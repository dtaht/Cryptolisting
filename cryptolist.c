/* Coprright 2010 by Dave Taht
 * based on greyfix, which was
 * Copyright 2007 by Kim Minh Kaplan
 *
 * cryptolist.c
 *
 * Postfix policy daemon designed to detect tls support
 *
 * Postfix: http://www.postfix.org/
 * Kim Minh Kaplan: http://www.kim-minh.com/
 *
 */
#ifdef HAVE_CONFIG_H
#include <config.h>
#endif
#include <assert.h>
#include <errno.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <unistd.h>
#include <syslog.h>
#include <sys/stat.h>
#include <arpa/inet.h>

#include <db.h>

#include "policy.h"

/**
 * This determines how many seconds we will block inbound mail that is
 * from a previously unknown (ip, from, to) triplet.  If it is set to
 * zero, incoming mail association will be learned, but no deliveries
 * will be tempfailed.  Use a setting of zero with caution, as it will
 * learn spammers as well as legitimate senders.
 **/
#define DELAY_MAIL_SECS (60*5)	/* 5 minutes */

/**
 * This determines how many seconds we will block inbound encrypted
 * mail that is
 * from a previously unknown (ip, from, to) triplet.  If it is set to
 * zero, incoming mail association will be learned, but no deliveries
 * will be tempfailed.  Use a setting of zero with caution, as it will
 * learn spammers as well as legitimate senders.
 **/

#define DELAY_CMAIL_SECS (20)	/* 20 seconds */

/**
 * This determines how many seconds of life are given to a record that
 * is created from a new mail [ip,from,to] triplet.  Note that the
 * window created by this setting for passing mails is reduced by the
 * amount set for DELAY_MAIL_SECS.  NOTE: See Also:
 * update_record_life and update_record_life_secs.
 */
#define AUTO_RECORD_LIFE_SECS (5 * 3600) /* 5 hours */
/**
 * How much life (in secs) to give to a record we are updating from an
 * allowed (passed) email.
 *
 * The default is 36 days, which should be enough to handle messages
 * that may only be sent once a month, or on things like the first
 * monday of the month (which sometimes means 5 weeks).  Plus, we add
 * a day for a delivery buffer.
 */
#define UPDATE_RECORD_LIFE_SECS (36 * 24 * 3600)

#define DEF_DB_HOME DATA_STATE_DIR"/"PACKAGE

#define DB_FILE_NAME_V0 "tls_triplets.db"
#define DB_FILE_NAME "tls_triplets-1.db"
#define SEP '\000'

/* First byte of the DB keys */
enum dbkey_type_enum {
    DBKEY_T_RAW = 0,
    DBKEY_T_IP4,
    DBKEY_T_IP6
};

#define IPV4_BITS (8 * sizeof(struct in_addr))
#define IPV6_BITS (8 * sizeof(struct in6_addr))

#define MAX(a,b) (((a)>(b))?(a):(b))
#define prefixp(s,p) (!strncmp((s),(p),sizeof(p)-1))

/*
  right now the crypto field has to be "discovered". I'd like, actually
  to track what crypto gets used. 
 */

#define TRANSPORT_NOTCRYPTED (0)
#define TRANSPORT_ENCRYPTED (1) /* Encypted but we don't know how */
#define TRANSPORT_TLS1 (2) 
#define TRANSPORT_TLS3 (3) 
#define TRANSPORT_SSL1 (4) 
#define TRANSPORT_SSL2 (5) 
#define TRANSPORT_SSL3 (6) 

struct triplet_data {
    time_t create_time;
    time_t access_time;
    unsigned long block_count;
    unsigned long pass_count;
    int crypted;
};

/* Filled in with a message when premature exit is requested from the
   signal handler */
void *exit_requested = NULL;
static int exit_requested_status = 0;

static const char *db_home = DEF_DB_HOME;

static DBT dbkey = { 0 };
static DBT dbdata = { 0 };
static struct triplet_data triplet_data;
static int deadlock_detect = 0;

static unsigned long greylist_delay = DELAY_MAIL_SECS;
static unsigned long cryptlist_delay = DELAY_CMAIL_SECS;
static unsigned long bloc_max_idle = AUTO_RECORD_LIFE_SECS;
static unsigned long pass_max_idle = UPDATE_RECORD_LIFE_SECS;
static block_unencrypted = 0;

/* The sequence "%d" is replaced by the number of seconds.  The
   sequence "%p" is replaced by the singular_string if the delay is
   one second, by plural_string otherwise.  The sequence "%s" is
   replaced by the single character " ".  The sequence "%m" is
   replaced by the receiving domain name.  The sequence "%%" is
   replaced by the single character "%".  Other sequences beginning
   with "%" are invalid. */

static const char *reject_action_fmt = 
  "451 Cryptolisted by "
   PACKAGE_STRING ", Thanks for using STARTTLS. Delayed: %d second%p."
    "  See http://cryptolist.taht.net.";
static const char *reject_unencrypted_action_fmt = 
  "451 Cryptolisted by "
   PACKAGE_STRING ", PLEASE enable STARTTLS on your email server. The bits you save may be your own. Delayed: %d second%p."
    "  See http://cryptolist.taht.net";
static const char *greylisted_action_fmt = "PREPEND X-Nocrypt: Non-encrypted transfer stalled by "
    PACKAGE_STRING " for %d second%p."
    "  See http://cryptolist.taht.net";
static const char *cryptlisted_action_fmt = "PREPEND X-Crypt: Encrypted transfer stalled by "
    PACKAGE_STRING " for %d second%p."
    "  See http://cryptolist.taht.net";

static const char *singular_string = "", *plural_string = "s";
static unsigned int ipv4_network_prefix = IPV4_BITS;
static unsigned int ipv6_network_prefix = IPV6_BITS;
/* --dump-triplets: dump the triplet database to stdout and exit */
static int dump_triplets;

/* Some Berkeley DB errors are not really error.  Keep them quiet. */
static int muffle_error = 0;

/* When Cryptolist detects a problem, let emails pass through and log. */
static jmp_buf defect_jmp_buf;
static const char *defect_msg = 0;

static int upgrade_from_v0(DB_ENV *);

/**********************************************************************
 * Berkeley DB routines
 */
static void
log_db_error(const char *msg, int error)
{
    if (muffle_error)
	syslog(LOG_NOTICE, "NOTICE (this is not an error): %s: %s",
	       msg, db_strerror(error));
    else
	syslog(LOG_ERR, "%s: %s", msg, db_strerror(error));
}

#if DB_VERSION_MAJOR == 4 && DB_VERSION_MINOR < 3 || DB_VERSION_MAJOR < 4
/* http://docs.oracle.com/cd/E17076_02/html/upgrading/upgrade_4_3_err.html */
static void
db_errcall_fcn(const char *errpfx, char *msg)
#else
static void
db_errcall_fcn(const DB_ENV *dbenv, const char *errpfx, const char *msg)
#endif
{
    syslog(LOG_ERR, "%s: %s", errpfx ? errpfx : "Berkeley DB", msg);
}

static int
call_db(int err, const char *msg)
{
    if (err)
	log_db_error(msg, err);
    return err;
}

static int
db_open(DB *db, const char *file, const char *database,
	DBTYPE type, u_int32_t flags, int mode)
{
    /* http://docs.oracle.com/cd/E17076_02/html/upgrading/upgrade_4_1_fop.html
       To upgrade, applications must add a DB_TXN parameter in the
       appropriate location for the DB->open method calls [...] the
       second argument */
#if DB_VERSION_MAJOR > 4 || DB_VERSION_MAJOR == 4 && DB_VERSION_MINOR >= 1
    return db->open(db, NULL, file, database, type, flags, mode);
#else
    return db->open(db, file, database, type, flags, mode);
#endif
}

/* Return the current Berkeley DB environment. If "force" is not zero
   then force creating the environment if it does not yet exist. Note
   that if "force" is zero then the function can not fail. */
static int
get_dbenv(DB_ENV **dbenv_ret, int force)
{
    static DB_ENV *dbenv = NULL;
    int rc = 0;
    if (dbenv == NULL && force) {
	rc = call_db(db_env_create(&dbenv, 0), "db_env_create");
	if (!rc) {
	    dbenv->set_errcall(dbenv, db_errcall_fcn);
	    rc = call_db(dbenv->set_lk_detect(dbenv, DB_LOCK_YOUNGEST),
			 "dbenv->set_lk_detect DB_LOCK_YOUNGEST, expired triplets will not be deleted");
	    if (!rc)
		deadlock_detect = 1;
	    rc = call_db(dbenv->open(dbenv, db_home,
#ifdef DB_REGISTER
				     /* DB_REGISTER appears in Berkeley DB 4.4 [#11511]
					http://docs.oracle.com/cd/E17076_02/html/upgrading/changelog_4_4_16.html#idp51982816 */
				     DB_REGISTER | DB_RECOVER |
#endif
				     DB_INIT_TXN | DB_INIT_LOCK | DB_INIT_LOG | DB_INIT_MPOOL | DB_CREATE, 0),
			 "dbenv->open");
	    if (rc) {
		dbenv->close(dbenv, 0);
		dbenv = 0;
	    }
	}
    }
    if (dbenv_ret)
	*dbenv_ret = dbenv;
    return rc;
}

static int
get_db(DB **db_ret, int force)
{
    static DB *db = NULL;
    int rc = 0;
    if (db == NULL && force) {
	DB_ENV *dbenv;
	rc = get_dbenv(&dbenv, force);
	if (rc)
	    return rc;
	rc = call_db(db_create(&db, dbenv, 0), "db_create");
	if (!rc) {
	    /* XXX do not use call_db: it is normal for this call to
	       fail with ENOENT if the database has to be upgraded or
	       created from scratch */
	    rc = db_open(db, DB_FILE_NAME, NULL,
			 DB_BTREE, DB_AUTO_COMMIT, 0644);
	    if (rc == ENOENT) {
		/* Try and upgrade from an old version */
		rc = call_db(upgrade_from_v0(dbenv), "upgrade_from_v0");
		if (!rc)
		    rc = call_db(db_open(db, DB_FILE_NAME, NULL, DB_BTREE, DB_AUTO_COMMIT | DB_CREATE, 0644),
				 "db->open 2");
	    }
	    else if (rc)
		call_db(rc, "db->open");
	    if (rc) {
		db->close(db, 0);
		db = 0;
	    }
	}
    }
    if (db_ret)
	*db_ret = db;
    return rc;
}

static void
initialize()
{
    char *version;
    int major, minor, patch;
    policy_initialize();
    version = db_version(&major, &minor, &patch);
    if (DB_VERSION_MAJOR != major || DB_VERSION_MINOR != minor) {
	syslog(LOG_ERR,
	       "This daemon was compiled with " DB_VERSION_STRING " (%d.%d.%d) definitions "
	       "but it is using %s (%d.%d.%d).  This will not work!  "
	       "Check that the version of the developpement files for Berkeley DB "
	       "match the version that used.",
	       DB_VERSION_MAJOR, DB_VERSION_MINOR, DB_VERSION_PATCH,
	       version, major, minor, patch);
	abort();
    }
    if (DB_VERSION_PATCH != patch && (opt_verbose || debug_me))
	syslog(LOG_INFO,
	       "Compiled with " DB_VERSION_STRING " (%d.%d.%d) definitions.  "
	       "Running with %s (%d.%d.%d).",
	       DB_VERSION_MAJOR, DB_VERSION_MINOR, DB_VERSION_PATCH,
	       version, major, minor, patch);
    else if (debug_me)
	syslog(LOG_DEBUG,
	       "This daemon was compiled with " DB_VERSION_STRING " (%d.%d.%d) definitions.",
	       DB_VERSION_MAJOR, DB_VERSION_MINOR, DB_VERSION_PATCH);
    dbdata.data = &triplet_data;
    dbdata.size = sizeof triplet_data;
    dbdata.ulen = sizeof triplet_data;
    dbdata.flags = DB_DBT_USERMEM;
}

static void
cleanup()
{
    int rc;
    DB *db;
    DB_ENV *dbenv;
    rc = get_db(&db, 0);
    assert(! rc);
    rc = get_dbenv(&dbenv, 0);
    assert(! rc);
    if (dbkey.data)
	free(dbkey.data);
    if (db)
	call_db(db->close(db, 0), "DB close");
    if (dbenv) {
	rc = call_db(db_create(&db, dbenv, 0), "db_create");
	if (!rc)
	    if (! db->remove(db, "tls_stats.db", 0, 0))
		syslog(LOG_NOTICE, "Unused database tls_stats.db removed");
	call_db(dbenv->txn_checkpoint(dbenv, 100 * 1024, 24 * 60, 0),
		"txn_checkpoint");
	call_db(dbenv->log_archive(dbenv, NULL, DB_ARCH_REMOVE), "log_archive");
	call_db(dbenv->close(dbenv, 0), "DB_ENV close");
    }
    policy_cleanup();
}

static void
fatal(const char *msg)
{
    syslog(LOG_ERR, "fatal: %s", msg);
    abort();
}

/* Decode the client address from the dbkey into a static buffer */
static const char *
db_key_ntop(const char *data)
{
    static char buffer[MAX(INET_ADDRSTRLEN, INET6_ADDRSTRLEN)];
    switch ((enum dbkey_type_enum)*data) {
    case DBKEY_T_RAW:
	return data + 1;
    case DBKEY_T_IP4:
	if (!inet_ntop(AF_INET, data + 1, buffer, sizeof(buffer)))
	    fatal("inet_ntop AF_INET failed");
	return buffer;
    case DBKEY_T_IP6:
	if (!inet_ntop(AF_INET6, data + 1, buffer, sizeof(buffer)))
	    fatal("inet_ntop AF_INET6 failed");
	return buffer;
    }
    syslog(LOG_ERR, "inet_ntop unexpected type %hhd", *data);
    abort();
}

static void
run_expiry()
{
    DB_ENV *dbenv;
    DB *db;
    DB_TXN *txn;
    DBC *dbcp;
    int rc;
    time_t now;
    DBT key = { 0 };
    unsigned int count = 0;
    if (exit_requested)
	return;
    /* Cursor operations can hold several locks and therefore deadlock
       so don't run expiry if deadlock detection does not work
       http://docs.oracle.com/cd/E17076_02/html/programmer_reference/lock_notxn.html */
    rc = get_db(&db, 0);
    assert(! rc);
    if (db == 0 || deadlock_detect == 0)
	return;
    rc = get_dbenv(&dbenv, 0);
    assert(! rc && dbenv);
    if (time(&now) == (time_t)-1) {
	syslog(LOG_ERR, "time failed during run_expiry");
	return;
    }
    muffle_error++;
    rc = dbenv->txn_begin(dbenv, NULL, &txn, DB_TXN_NOWAIT);
    if (rc) {
	if (rc == DB_LOCK_DEADLOCK)
	    syslog(LOG_DEBUG, "skipping concurrent expiry avoids "
		   "deadlocks and unnecessary work");
	else
	    log_db_error("txn_begin failed during run_expiry", rc);
	goto out;
    }
#if DB_VERSION_MAJOR >= 5
    call_db(txn->set_priority(txn, 50), "TXN->set_priority");
#endif
    rc = call_db(db->cursor(db, txn, &dbcp, 0),
		 "db->cursor failed during expiry run");
    if (rc)
	goto txn_fail;
    while ((rc = dbcp->c_get(dbcp, &key, &dbdata, DB_NEXT | DB_RMW)) == 0) {
	time_t ref_time;
	double age_max, age;
	if (triplet_data.pass_count) {
	    ref_time = triplet_data.access_time;
	    age_max = pass_max_idle;
	}
	else {
	    ref_time = triplet_data.create_time;
	    age_max = bloc_max_idle;
	}
	age = difftime(now, ref_time);
	if (age > age_max) {
	    if (opt_verbose) {
		syslog(LOG_INFO, "Expiring %s %s after %.0f seconds idle",
		       db_key_ntop(key.data),
		       triplet_data.pass_count ? "pass" : "block", age);
	    }
	    rc = call_db(dbcp->c_del(dbcp, 0), "dbcp->c_del failed");
	    if (rc)
		goto cursor_fail;
	    count++;
	}
	if (exit_requested)
	    break;
    }
    if (rc && rc != DB_NOTFOUND) {
	if (rc == DB_LOCK_DEADLOCK)
	    syslog(LOG_NOTICE, "Aborting concurrent expiry due to deadlock");
	else
	    log_db_error("dbcp->c_get failed", rc);
	goto cursor_fail;
    }
    if (call_db(dbcp->c_close(dbcp), "dbcp->c_close failed"))
	goto txn_fail;
    call_db(txn->commit(txn, 0), "commit failed in run_expiry");
    if (count)
	syslog(LOG_NOTICE, "Expired %u triplets", count);
    goto out;

  cursor_fail:
    call_db(dbcp->c_close(dbcp), "dbcp->c_close failed");
  txn_fail:
    call_db(txn->abort(txn), "failed to abort");
  out:
    muffle_error--;
    return;
}

/* Write the result of calling ctime(3) on stdout without the trailing
   newline. */
static void
write_ctime(const time_t *time)
{
    const char *s, *t;
    s = ctime(time);
    t = strchr(s, '\n');
    if (t)
	fwrite(s, 1, t - s, stdout);
    else
	fputs(s, stdout);
}

/* FIXME should this be wrapped in an explicit transaction? */
static void
do_dump_triplets()
{
    DB *db;
    DBC *dbcp;
    int rc;
    DBT key = { 0 },
	data = { 0 };
    rc = get_db(&db, 1);
    if (rc) {
	fprintf(stderr, "DBD-%d: failed to open database\n", rc);
	return;
    }
    rc = db->cursor(db, 0, &dbcp, 0);
    if (rc)
	fprintf(stderr, "DBD-%d: db->cursor failed: %s\n",
		rc, db_strerror(rc));
    else {
	while (! exit_requested
	       && (rc = dbcp->c_get(dbcp, &key, &data, DB_NEXT)) == 0) {
	    const char *const start = key.data, *s = start;
	    const struct triplet_data *t = data.data;
	    printf("%d\t", t->crypted);
	    printf("%s\t", db_key_ntop(s));
	    switch ((enum dbkey_type_enum)*s++) {
	    case DBKEY_T_RAW:
		s += strlen(s) + 1;
		break;
	    case DBKEY_T_IP4:
		s += IPV4_BITS / 8;
		break;
	    case DBKEY_T_IP6:
		s += IPV6_BITS / 8;
		break;
	    }
	    printf("%s\t", s);
	    s += strlen(s) + 1;
	    fwrite(s, 1, key.size - (s - start), stdout);
	    putchar('\t');
	    write_ctime(&t->create_time);
	    putchar('\t');
	    write_ctime(&t->access_time);
	    printf("\t%lu\t%lu\n", t->block_count, t->pass_count);
	}
	if (rc && rc != DB_NOTFOUND)
	    fprintf(stderr, "DBD-%d: dbcp->c_get failed: %s\n",
		    rc, db_strerror(rc));
	rc = dbcp->c_close(dbcp);
	if (rc)
	    fprintf(stderr, "DBD-%d: dbcp->c_close failed: %s\n",
		    rc, db_strerror(rc));
    }
}

static void *
ensure_dbkey_reserve(size_t total)
{
    if (dbkey.ulen < total) {
	dbkey.data = xrealloc(dbkey.data, total);
	dbkey.ulen = total;
	dbkey.flags = DB_DBT_USERMEM;
    }
    return dbkey.data;
}

/* Upgrade the database from v0 format to the new format */
static int
upgrade_from_v0(DB_ENV *dbenv)
{
    DB *db0 = NULL, *db1 = NULL;
    DB_TXN *tid = NULL;
    DBC *cursor = NULL;
    DBT key = { 0 }, data = { 0 };
    int rc = call_db(dbenv->txn_begin(dbenv, NULL, &tid, 0),
		     "upgrade_from_v0 dbenv->txn_begin");
    if (!rc)
	rc = call_db(db_create(&db0, dbenv, 0), "upgrade_from_v0 db_create 0");
    if (!rc) {
	/* XXX do not use call_db: it is normal for this call to fail,
	   if there is no database to upgrade from. */
	rc = db0->open(db0, tid, DB_FILE_NAME_V0, NULL, DB_UNKNOWN, 0, 0644);
	if (rc == ENOENT) {
	    call_db(db0->close(db0, 0), "upgrade_from_v0 db0->close 0");
	    call_db(tid->commit(tid, 0), "upgrade_from_v0 tid->commit 0");
	    return 0;
	}
    }
    if (!rc) {
	syslog(LOG_WARNING, "Upgrading from database format v0");
	rc = call_db(db_create(&db1, dbenv, 0), "upgrade_from_v0 db_create 1");
    }
    if (!rc)
	rc = call_db(db1->open(db1, tid,
			       DB_FILE_NAME, NULL,
			       DB_BTREE, DB_CREATE | DB_EXCL, 0644),
		     "upgrade_from_v0 db1->open");
    if (!rc)
	rc = call_db(db0->cursor(db0, tid, &cursor, 0),
		     "upgrade_from_v0 db0->cursor");
    size_t buffer_size = 0;
    char *buffer = 0;
    while (!rc) {
	rc = cursor->get(cursor, &key, &data, DB_NEXT);
	if (rc == DB_NOTFOUND) {
	    /* this is expected result, do commit this transaction */
	    rc = 0;
	    break;
	}
	else if (rc) {
	    call_db(rc, "upgrade_from_v0 cursor->get");
	    break;
	}
	/* Convert this entry to new format */
	char *s, *ip, *from, *to;
	size_t iplen, fromlen, tolen;
	ip = key.data;
	iplen = strlen(ip);
	from = ip + iplen + 1;
	fromlen = strlen(from);
	to = from + fromlen + 1;
	tolen = key.size - fromlen - iplen - 2;
	int count = 0;
	for (s = strchr(ip, '.'); s != NULL; s = strchr(s + 1, '.'))
	    count++;
	s = ensure_dbkey_reserve(MAX(MAX(sizeof(struct in_addr),
					 sizeof(struct in6_addr)),
				     iplen + 1)
				 + fromlen + tolen + 2);
	if (count) {
	    /* This is supposedly an IPv4 address. Complete it with
	       trailing zeroes. A complete IPv4 address has 3 dots and
	       4 numbers. For each missing dot, add the dot and a 0. */
	    size_t needed = iplen + 2 * (3 - count) + 1;
	    if (buffer_size < needed) {
		buffer = xrealloc(buffer, needed);
		buffer_size = needed;
	    }
	    strcpy(buffer, ip);
	    while (count++ < 3)
		strcat(buffer, ".0");
	    *s++ = DBKEY_T_IP4;
	    rc = inet_pton(AF_INET, buffer, s);
	    s += sizeof(struct in_addr);
	    if (rc == -1)
		rc = errno;
	    else if (rc == 1)
		rc = 0;
	    else
		rc = EINVAL;
	    if (rc)
		break;		/* error */
	}
	else {
	    /* Try it as an IPv6 address. v0 format did not abbreviate
	       IPv6 addresses. */
	    *s++ = DBKEY_T_IP6;
	    if (inet_pton(AF_INET6, ip, s) == 1)
		s += sizeof(struct in6_addr);
	    else {
		/* Not IPv4 neither IPv6. Keep it in its raw form */
		*s++ = DBKEY_T_RAW;
		strcpy(s, ip);
		s += iplen + 1;
	    }
	}
	strcpy(s, from);
	s += fromlen + 1;
	memcpy(s, to, tolen);
	s += tolen;
	dbkey.size = s - (char*)dbkey.data;
	rc = call_db(db1->put(db1, tid, &dbkey, &data, DB_NOOVERWRITE),
		     "upgrade_from_v0 db1->put");
    }
    if (buffer != NULL)
	free(buffer);
    if (cursor != NULL)
	call_db(cursor->close(cursor), "upgrade_from_v0 cursor->close");
    if (db1 != NULL)
	call_db(db1->close(db1, 0), "upgrade_from_v0 db1->close");
    if (db0 != NULL)
	call_db(db0->close(db0, 0), "upgrade_from_v0 db0->close");
    if (!rc)
	rc = call_db(dbenv->dbremove(dbenv, tid, DB_FILE_NAME_V0, NULL, 0),
		     "upgrade_from_v0 dbenv->dbremove");
    if (tid != NULL) {
	if (rc)
	    call_db(tid->abort(tid), "upgrade_from_v0 tid->abort");
	else
	    call_db(tid->commit(tid, 0), "upgrade_from_v0 tid->commit");
    }
    return rc;
}

static void
build_triplet_key(const char *ip, const char *from, const char *to)
{
    /* New database format: the first byte specifies the format of the record.

       DBKEY_T_RAW, ip, \000, from, \000, to
       DBKEY_T_IP4, in_addr, from, \000, to
       DBKEY_T_IP6, in6_addr, from, \000, to
    */
    const char *endip = strchr(ip, '\n'),
	*endfrom = strchr(from, '\n'),
	*endto = strchr(to, '\n');
    size_t lenfrom = endfrom - from,
	lenip = endip - ip,
	lento = endto - to;
    size_t maxbuf = MAX(MAX(sizeof(struct in_addr), sizeof(struct in6_addr)),
			lenip + 1);
    char *buf = ensure_dbkey_reserve(maxbuf + lenfrom + lento + 2);
    /* XXX KLUDGE we restore *endip to \n after the inet_pton calls */
    char *endipx = (char *)endip;
    *endipx = 0;
    if (inet_pton(AF_INET, ip, buf + 1) > 0) {
	*buf++ = DBKEY_T_IP4;
	dbkey.size = sizeof(struct in_addr);
	unsigned int keep_bytes = ipv4_network_prefix / 8;
	if (keep_bytes < dbkey.size) {
	    buf[keep_bytes] &= 0xff << (8 - ipv4_network_prefix % 8);
	    memset(buf + keep_bytes + 1, 0, dbkey.size - keep_bytes - 1);
	}
    }
    else if (inet_pton(AF_INET6, ip, buf + 1) > 0) {
	*buf++ = DBKEY_T_IP6;
	dbkey.size = sizeof(struct in6_addr);
	unsigned int keep_bytes = ipv6_network_prefix / 8;
	if (keep_bytes < dbkey.size) {
	    buf[keep_bytes] &= 0xff << (8 - ipv6_network_prefix % 8);
	    memset(buf + keep_bytes + 1, 0, dbkey.size - keep_bytes - 1);
	}
    }
    else {
	/* inet_pton failed to parse the address. Fallback to the
	   raw address */
	*buf++ = DBKEY_T_RAW;
	dbkey.size = lenip + 1;
	memcpy(buf, ip, dbkey.size);
    }
    *endipx = '\n';

    buf += dbkey.size;
    memcpy(buf, from, lenfrom);
    buf += lenfrom;
    *buf++ = 0;
    memcpy(buf, to, lento);
    buf += lento;
    dbkey.size = buf - (char*)dbkey.data;
    assert(dbkey.size <= dbkey.ulen);

    if (debug_me)
	syslog(LOG_DEBUG, "triplet effective IP: %s", db_key_ntop(dbkey.data));
}

/* If there is an error while processing a SMTP request, log a warning
   in Postfix. */
static void
jmperr(const char *msg)
{
    defect_msg = msg;
    longjmp(defect_jmp_buf, 1);
}

static void
touch_data()
{
    if (time(&triplet_data.access_time) == (time_t)-1)
	jmperr("time failed");
}

static void
build_data()
{
    triplet_data.create_time = triplet_data.access_time;
    triplet_data.block_count = 0;
    triplet_data.pass_count = 0;
    triplet_data.crypted = 0;
}

static void
get_grey_data(DB *db, DB_TXN *txn)
{
    int rc;
    rc = db->get(db, txn, &dbkey, &dbdata, 0);
    if (rc == DB_NOTFOUND) {
	touch_data();
	build_data();
    }
    else if (rc) {
	log_db_error("get failed", rc);
	jmperr("get failed");
    }
    else {
	time_t ref_time;
	double age_max;
	if (triplet_data.pass_count) {
	    ref_time = triplet_data.access_time;
	    age_max = pass_max_idle;
	}
	else {
	    ref_time = triplet_data.create_time;
	    age_max = bloc_max_idle;
	}
	touch_data();
	/* Expire IDLE records */
	if (difftime(triplet_data.access_time, ref_time) > age_max)
	    build_data();
    }
}

static int
put_grey_data(DB *db, DB_TXN *txn)
{
    return call_db(db->put(db, txn, &dbkey, &dbdata, 0), "put");
}

static void
printf_action(const char *fmt, unsigned long delay)
{
    /* interpret the %x sequences */
    while (*fmt) {
	const char *t = strchr(fmt, '%');
	if (t) {
	    fwrite(fmt, sizeof *fmt, t - fmt, stdout);
	    fmt = t + 1;
	    switch (*fmt) {
	    case 'd':
		printf("%lu", delay);
		break;
	    case 'p':
		fputs(delay == 1 ? singular_string : plural_string, stdout);
		break;
	    case 's':
		putchar(' ');
		break;
	    case '%':
		putchar('%');
		break;
	    case 0:
		syslog(LOG_WARNING, "Invalid reject_action sequence %%");
		break;
	    default:
		syslog(LOG_WARNING,
		       "Invalid reject_action sequence %%%c", *fmt);
		break;
	    }
	    if (*fmt)
		fmt++;
	}
	else {
	    fputs(fmt, stdout);
	    break;
	}
    }
}

static int
process_smtp_rcpt(int crypted)
{
    double delay;
    int rc;
    DB_ENV *dbenv;
    DB *db;
    DB_TXN *txn = NULL;
    if (setjmp(defect_jmp_buf)) {
	if (defect_msg) {
	    printf(STR_ACTION "WARN %s\n", defect_msg);
	    defect_msg = 0;
	}
	else
	    puts(STR_ACTION "WARN " PACKAGE_STRING " is not working properly");
	if (txn)
	    call_db(txn->abort(txn), "Failed to abort transaction");
	return 1;
    }
    rc = get_dbenv(&dbenv, 1);
    if (rc)
	jmperr("get_dbenv failed");
    rc = get_db(&db, 1);
    if (rc)
	jmperr("get_db failed");
    rc = call_db(dbenv->txn_begin(dbenv, NULL, &txn, 0),
		 "txn_begin failed in process_smtp_rcpt");
    if (rc)
	jmperr("txn_begin failed");
    get_grey_data(db, txn);
    if (triplet_data.crypted != crypted) {
      triplet_data.crypted = crypted;
      if (debug_me) syslog(LOG_DEBUG,"crypted field changed for some reason");
    }
    delay = difftime(triplet_data.access_time, triplet_data.create_time);
    /* Block inbound mail that is from a previously unknown (ip, from, to) triplet */
    /* However we want different behavior for crypted stuff
     */

    if(crypted > 0) {
      if(delay < cryptlist_delay) {
	triplet_data.block_count++;
	fputs(STR_ACTION, stdout);
	printf_action(reject_action_fmt, greylist_delay - delay);
	putchar('\n');
    }
    else if (triplet_data.pass_count++)
	puts(STR_ACTION "DUNNO");
      else {
        fputs(STR_ACTION, stdout);
        printf_action(cryptlisted_action_fmt, delay);
        putchar('\n');
      }
    } else {
      if(delay < greylist_delay || block_unencrypted) {
        triplet_data.block_count++;
        fputs(STR_ACTION, stdout);
        if(block_unencrypted == 1) {
          printf_action(reject_unencrypted_action_fmt, (3600*24)); // block it for a day
        } else {
          printf_action(reject_unencrypted_action_fmt, greylist_delay - delay);
        }
        putchar('\n');
      }
      else if (triplet_data.pass_count++)
        puts(STR_ACTION "DUNNO");
      else {
        fputs(STR_ACTION, stdout);
        printf_action(greylisted_action_fmt, delay);
        putchar('\n');
      }
    }
    rc = put_grey_data(db, txn);
    if (rc)
	call_db(txn->abort(txn), "abort failed");
    else
	call_db(txn->commit(txn, 0), "commit failed");
    return rc;
}

static void
signal_handler(int signal)
{
    syslog(LOG_NOTICE, "Received signal %d", signal);
    exit_requested = "signal received";
    exit_requested_status = EXIT_FAILURE;
}

static int
loptp(const char *opt, const char *long_opt)
{
    return strcmp(opt, long_opt) == 0;
}

static int
optp(const char *opt, const char *short_opt, const char *long_opt)
{
    return strcmp(opt, short_opt) == 0 || loptp(opt, long_opt);
}

static void
print_usage(FILE *f, const char *progname)
{
    fprintf(f,
	    "Usage: %s [-V] [-v] [-d] [-h <Berkeley DB home directory>]\n" 
            "[-g <greylist delay>] [-G <greylisted action>] [-r <reject action>]\n"	    
            "[-c <cryptlist delay>] [-C <cryptlisted action>] [-R <reject action>]\n"	    
            "[-b <bloc maximum idle>] [-p <pass maximum idle>] \n"
	    "[-/ <network bits>] [--dump-triplets] [--help]\n"
	    "\n"
	    "    -b <seconds>, --bloc-max-idle <seconds>\n"
	    "\n"
	    "	This determines how many seconds of life are given to a record\n"
	    "	that is created from a new mail (ip, from, to) triplet.  Note\n"
	    "	that the window created by this setting for passing mails is\n"
	    "	reduced by the amount set for --greylist-delay.  NOTE: See\n"
	    "	also --pass-max-idle.  Defaults to %d.\n"
	    "\n"
	    "    -d, --debug\n"
	    "\n"
	    "	Debug logging\n"
	    "\n"
	    "    -g <seconds>, --greylist-delay <seconds>\n"
	    "\n"
	    "	This determines how many seconds we will block unencrypted \n"
	    "	inbound mail from a previously unknown (ip, from, to) triplet.  If\n"
	    "	it is set to zero, incoming mail association will be learned,\n"
	    "	but no deliveries will be tempfailed.  Use a setting of zero\n"
	    "	with caution, as it will learn spammers as well as legitimate\n"
	    "	senders.  Defaults to %d.\n"
	    "\n"
	    "    -c <seconds>, --cryptlist-delay <seconds>\n"
	    "\n"
	    "	This determines how many seconds we will block crypted inbound mail\n"
	    "	that is from a previously unknown (ip, from, to) triplet.  If\n"
	    "	it is set to zero, incoming mail association will be learned,\n"
	    "	but no deliveries will be tempfailed.  Use a setting of zero\n"
	    "	with caution, as it will learn spammers as well as legitimate\n"
	    "	senders.  Defaults to %d.\n"
	    "\n"
	    "    -h <Berkeley DB home directory>, --home <Berkeley DB home directory>\n"
	    "\n"
	    "	Location of the Berkeley DB environment home location (the\n"
	    "	default is " DEF_DB_HOME ".\n"
	    "\n"
	    "    --help\n"
	    "\n"
	    "        Show usage information.\n"
	    "\n"
	    "    -p <seconds>, --pass-max-idle <seconds>\n"
	    "\n"
	    "	How much life (in secs) to give to a record we are updating\n"
	    "	from an allowed (passed) email.\n"
	    "\n"
	    "	The default is %d, which should be enough to handle\n"
	    "	messages that may only be sent once a month, or on things like\n"
	    "	the first monday of the month (which sometimes means 5 weeks).\n"
	    "	Plus, we add a day for a delivery buffer.\n"
	    "\n"
	    "    -r <reject action>, --reject-action <reject action>\n"
	    "\n"
	    "        The reject action directive that will be used.  See access(5)\n"
	    "        for valid actions.  The string expands %%d to the number of\n"
	    "        seconds, %%p to the empty string if %%d expands to 1 or \"s\"\n"
	    "        otherwise, %%s to \" \" and %%%% to \"%%\".\n"
	    "\n"
	    "        The default is \"%s\".\n"
	    "\n"
	    "    -G <greylisted action>, --greylisted-action <greylisted action>\n"
	    "\n"
	    "        The action that will be used the first time a triplet passes\n"
	    "        greylisting.  Same expansion as for --reject-action.\n"
	    "\n"
	    "        The default is \"%s\"\n"
	    "\n"
	    "    -C <cryptlisted action>, --cryptlisted-action <cryptlisted action>\n"
	    "\n"
	    "        The action that will be used the first time a triplet passes\n"
	    "        greylisting for an encrypted transfer." 
            "        Same expansion as for --reject-action.\n"
	    "\n"
	    "        The default is \"%s\"\n"
	    "\n"
	    "    -v, --verbose\n"
	    "\n"
	    "	Verbose logging\n"
	    "\n"
	    "    -V, --version\n"
	    "\n"
	    "        Show version information.\n"
	    "\n"
	    "    -/ <nbits>, --network-prefix <nbits>\n"
	    "\n"
	    "	Only consider the first <nbits> bits of an IPv4 address.\n"
	    "	Defaults to %lu i.e. the whole adresse is significant.\n"
	    "\n"
	    "    -6 <nbits>, --network6-prefix <nbits>\n"
	    "\n"
	    "	Only consider the first <nbits> bits of an IPv6 address.\n"
	    "	Defaults to %lu i.e. the whole adresse is significant.\n"
	    "\n"
	    "    -B \n"
	    "\n"
	    "	Block unencrypted mail\n"
	    "\n"
	    "    --dump-triplets\n"
	    "\n"
	    "        Dump the triplets database to stdout.  Mostly for debugging\n"
	    "        purposes.\n",
	    progname, AUTO_RECORD_LIFE_SECS, DELAY_MAIL_SECS, DELAY_CMAIL_SECS,
	    UPDATE_RECORD_LIFE_SECS, reject_action_fmt, greylisted_action_fmt, cryptlisted_action_fmt,
	    IPV4_BITS, IPV6_BITS);
}

/* 
    Postfix version 2.1 and later:
    request=smtpd_access_policy
    protocol_state=RCPT
    protocol_name=SMTP
    helo_name=some.domain.tld
    queue_id=8045F2AB23
    sender=foo@bar.tld
    recipient=bar@foo.tld
    recipient_count=0
    client_address=1.2.3.4
    client_name=another.domain.tld
    reverse_client_name=another.domain.tld
    instance=123.456.7

    Postfix version 2.2 and later:
    sasl_method=plain
    sasl_username=you
    sasl_sender=
    size=12345
    ccert_subject=solaris9.porcupine.org
    ccert_issuer=Wietse+20Venema
    ccert_fingerprint=C2:9D:F4:87:71:73:73:D9:18:E7:C2:F3:C1:DA:6E:04

    Postfix version 2.3 and later:
    encryption_protocol=TLSv1/SSLv3
    encryption_cipher=DHE-RSA-AES256-SHA
    encryption_keysize=256
    etrn_domain=
    Postfix version 2.5 and later:
    stress=
    [empty line]

*/

int
main(int argc, const char **argv)
{
    char *p;
    unsigned int i;
    int opt_version = 0, opt_help = 0, opt_error = 0;
    progname = strrchr(argv[0], '/');
    if (progname)
	progname++;
    else
	progname = argv[0];
    openlog(progname, LOG_PID, LOG_MAIL);
    for (i = 1; i < argc; i++) {
	if (optp(argv[i], "-d", "--debug"))
	    debug_me = 1;
	else if (optp(argv[i], "-v", "--verbose"))
	    opt_verbose++;
	else if (optp(argv[i], "-V", "--version"))
	    opt_version = 1;
	else if (loptp(argv[i], "--help"))
	    opt_help = 1;
	else if (optp(argv[i], "-b", "--bloc-max-idle")) {
	    if (++i >= argc)
		fatal("Missing argument to --bloc-max-idle");
	    bloc_max_idle = strtoul(argv[i], &p, 10);
	    if (*p)
		fatal("Invalid argument to --bloc-max-idle.  "
		      "Integer value expected");
	}
	else if (optp(argv[i], "-g", "--greylist-delay")) {
	    if (++i >= argc)
		fatal("Missing argument to --greylist-delay");
	    greylist_delay = strtoul(argv[i], &p, 10);
	    if (*p)
		fatal("Invalid argument to --greylist-delay.  "
		      "Integer value expected");
	}
	else if (optp(argv[i], "-c", "--cryptlist-delay")) {
	    if (++i >= argc)
		fatal("Missing argument to --cryptlist-delay");
	    cryptlist_delay = strtoul(argv[i], &p, 10);
	    if (*p)
		fatal("Invalid argument to --cryptlist-delay.  "
		      "Integer value expected");
	}
	else if (optp(argv[i], "-h", "--home")) {
	    if (++i >= argc)
		fatal("Missing argument to --home");
	    db_home = argv[i];
	}
	else if (optp(argv[i], "-/", "--network-prefix")) {
	    if (++i >= argc)
		fatal("Missing argument to --network-prefix");
	    ipv4_network_prefix = strtoul(argv[i], &p, 10);
	    if (*p || ipv4_network_prefix > IPV4_BITS)
		fatal("Invalid argument to --network-prefix.  "
		      "Integer value between 0 and 32 expected");
	}
	else if (optp(argv[i], "-6", "--network6-prefix")) {
	    if (++i >= argc)
		fatal("Missing argument to --network6-prefix");
	    ipv6_network_prefix = strtoul(argv[i], &p, 10);
	    if (*p || ipv6_network_prefix > IPV6_BITS)
		fatal("Invalid argument to --network6-prefix.  "
		      "Integer value between 0 and 128 expected");
	}
	else if (optp(argv[i], "-p", "--pass-max-idle")) {
	    if (++i >= argc)
		fatal("Missing argument to --pass-max-idle");
	    pass_max_idle = strtoul(argv[i], &p, 10);
	    if (*p)
		fatal("Invalid argument to --pass-max-idle.  "
		      "Integer value expected");
	}
	else if (optp(argv[i], "-r", "--reject-action")) {
	    if (++i >= argc)
		fatal("Missing argument to --reject-action");
	    reject_action_fmt = argv[i];
	}
	else if (optp(argv[i], "-R", "--reject-unencrypted-action")) {
	    if (++i >= argc)
		fatal("Missing argument to --reject-unencrypted-action");
	    reject_unencrypted_action_fmt = argv[i];
	}
	else if (optp(argv[i], "-G", "--greylisted-action")) {
	    if (++i >= argc)
		fatal("Missing argument to --greylisted-action");
	    greylisted_action_fmt = argv[i];
	}
	else if (optp(argv[i], "-C", "--cryptlisted-action")) {
	    if (++i >= argc)
		fatal("Missing argument to --greylisted-action");
	    cryptlisted_action_fmt = argv[i];
	}
	else if (loptp(argv[i], "--dump-triplets")) {
	  dump_triplets = 1;
	}
	else if (optp(argv[i],"-B","--block-unencrypted")) {
	  block_unencrypted = 1;
	}
	else {
	    fprintf(stderr, "Unknown option \"%s\"\n", argv[i]);
	    opt_error = 1;
	}
    }
    if (opt_error) {
	print_usage(stderr, progname);
	exit(EXIT_FAILURE);
    }
    if (opt_version)
	puts(PACKAGE_STRING);
    if (opt_help) {
	print_usage(stdout, progname);
	exit(EXIT_SUCCESS);
    }

    struct sigaction act = { { 0 } };
    act.sa_handler = signal_handler;
    act.sa_flags = SA_RESETHAND; /* Avoid infinite loops */
    sigemptyset(&act.sa_mask);
#ifdef SIGHUP
    if (sigaction(SIGHUP, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGINT
    if (sigaction(SIGINT, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGQUIT
    if (sigaction(SIGQUIT, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGILL
    if (sigaction(SIGILL, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGABRT
    if (sigaction(SIGABRT, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGSEGV
    if (sigaction(SIGSEGV, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGALRM
    if (sigaction(SIGALRM, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif
#ifdef SIGTERM
    if (sigaction(SIGTERM, &act, NULL) < 0) {
	perror("sigaction failed");
	exit(1);
    }
#endif

    initialize();
    if (dump_triplets)
	do_dump_triplets();
    else while (! exit_requested && read_policy_request(0)) {
	const char *protocol = 0, *state = 0, *ip, *from, *to, 
	  *encryption_protocol = 0, *ccert_fingerprint = 0;
	int crypted = 0;

	if ((protocol = find_attribute("protocol_name"))
	    && (state = find_attribute("protocol_state"))
	    && (prefixp(protocol, STR_SMTP "\n")
		|| prefixp(protocol, STR_ESMTP "\n"))
	    && prefixp(state, STR_RCPT "\n")
	    && (ip = find_attribute("client_address"))
	    && (from = find_attribute("sender"))
	    && (to = find_attribute("recipient"))) {
	    encryption_protocol = find_attribute("encryption_protocol");
	    ccert_fingerprint = find_attribute("ccert_fingerprint");
	    if (encryption_protocol) {
	    // grumble - find_attribute returns a \n terminated string, not null
	      int i;
	      char actual_crypt[255];
	      char actual_fingerprint[255]; // FIXME
	      actual_crypt[0] = '\0';
	      actual_fingerprint[0] = '\0';
	      if(encryption_protocol[0] != '\n') {
          crypted = triplet_data.crypted = TRANSPORT_ENCRYPTED; // FIXME, figure out what it is
	      for(i = 0; i < 255 && encryption_protocol[i] != '\n'; i++) ;
	      if(i > 0) { 
          strncpy(actual_crypt,encryption_protocol,i); 
          actual_crypt[i] = '\0';
	      }

	      for(i = 0; i < 255 && ccert_fingerprint[i] != '\n'; i++) ;

	      if(i > 0) { 
          strncpy(actual_fingerprint,ccert_fingerprint,i); 
          actual_fingerprint[i] = '\0';
	      }
	      
	      syslog(LOG_DEBUG,"Encryption: %s Fingerprint: %s", 
          actual_crypt ? actual_crypt : "NA",
          actual_fingerprint ? actual_fingerprint : "NA");  
	    }
	    }

	    build_triplet_key(ip, from, to);
	    if (process_smtp_rcpt(crypted)) {
	      syslog(LOG_ERR, "error: cleaning up");
	      cleanup();
	      syslog(LOG_ERR, "error: exiting after cleanup");
	      return 1;
	    }
	}
	else {
	    puts(STR_ACTION "DUNNO");
	    if (debug_me) {
		char *p = 0, *s = 0;
		if (protocol) {
		    p = strchr(protocol, '\n');
		    *p = 0;
		}
		if (state) {
		    s = strchr(state, '\n');
		    *s = 0;
		}
		syslog(LOG_DEBUG,
		       "Ignoring protocol %s state %s",
		       protocol ? protocol : "(not defined)",
		       state ? state : "(not defined)");
		if (p)
		    *p = '\n';
		if (s)
		    *s = '\n';
	    }
	}
	putchar('\n');
	fflush(stdout);
    }
    run_expiry();
    cleanup();
    if (opt_verbose)
	syslog(LOG_NOTICE, "daemon stopped");
    closelog();
    return exit_requested_status;
}
