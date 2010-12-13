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
#include <db.h>

#include "policy.h"

/**
 * This determines how many seconds we will block inbound mail that is
 * from a previously unknown (ip, from, to) triplet.  If it is set to
 * zero, incoming mail association will be learned, but no deliveries
 * will be tempfailed.  Use a setting of zero with caution, as it will
 * learn spammers as well as legitimate senders.
 **/
#define DELAY_MAIL_SECS (60)	/* 1 minute */
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

#define DB_FILE_NAME "tls_triplets.db"
#define SEP '\000'

#define prefixp(s,p) (!strncmp((s),(p),sizeof(p)-1))

/*
  right now the crypto field has to be "discovered". I'd like, actually
  to track what crypto gets used. 

 */

#define TRANSPORT_NOTCRYPTED 0
#define TRANSPORT_ENCRYPTED 1

struct triplet_data {
    time_t create_time;
    time_t access_time;
    unsigned long block_count;
    unsigned long pass_count;
    int crypted;
};


static const char *db_home = DEF_DB_HOME;

static DB_ENV *dbenv = 0;
static DB *db = 0;

static DBT dbkey = { 0 };
static DBT dbdata = { 0 };
static struct triplet_data triplet_data;
static int deadlock_detect = 0;

static unsigned long greylist_delay = DELAY_MAIL_SECS;
static unsigned long bloc_max_idle = AUTO_RECORD_LIFE_SECS;
static unsigned long pass_max_idle = UPDATE_RECORD_LIFE_SECS;
/* The sequence "%d" is replaced by the number of seconds.  The
   sequence "%p" is replaced by the singular_string if the delay is
   one second, by plural_string otherwise.  The sequence "%s" is
   replaced by the single character " ".  The sequence "%m" is
   replaced by the receiving domain name.  The sequence "%%" is
   replaced by the single character "%".  Other sequences beginning
   with "%" are invalid. */
static const char *reject_action_fmt = "DEFER_IF_PERMIT Cryptolisted by "
    PACKAGE_STRING ", PLEASE enable STARTTLS on your email server. The bits you save may be your own. Delayed: %d second%p."
    "  See http://cryptolist.taht.net for more information.";
static const char *greylisted_action_fmt = "PREPEND X-CRYPTED: Non-encrypted transfer stalled by "
    PACKAGE_STRING " for %d second%p."
    "  See http://cryptolist.taht.net for more information.";
static const char *cryptolisted_action_fmt = "PREPEND X-CRYPTED: Encrypted transfer stalled by "
    PACKAGE_STRING " for %d second%p."
    "  See http://cryptolist.taht.net for more information.";
static const char *singular_string = "", *plural_string = "s";
/* As we store IP addresses in Postfix's format, to obtain the network
 address we first strip `ipv4_network_strip_bytes' numbers (between 0
 and 4) then we apply `ipv4_network_mask' on the last byte. */
static unsigned int ipv4_network_strip_bytes;
static unsigned int ipv4_network_mask;
/* --dump-triplets: dump the triplet database to stdout and exit */
static int dump_triplets;

/* Some Berkeley DB errors are not really error.  Keep them quiet. */
static int muffle_error = 0;

/* When Cryptolist detects a problem, let emails pass through and log. */
static jmp_buf defect_jmp_buf;
static const char *defect_msg = 0;

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
/* http://www.oracle.com/technology/documentation/berkeley-db/db/ref/upgrade.4.3/err.html */
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
db_open(DB *db, const char *file, const char *database,
	DBTYPE type, u_int32_t flags, int mode)
{
    /* http://www.oracle.com/technology/documentation/berkeley-db/db/ref/upgrade.4.1/fop.html
       To upgrade, applications must add a DB_TXN parameter in the
       appropriate location for the DB->open method calls [...] the
       second argument */
#if DB_VERSION_MAJOR > 4 || DB_VERSION_MAJOR == 4 && DB_VERSION_MINOR >= 1
    return db->open(db, NULL, file, database, type, flags, mode);
#else
    return db->open(db, file, database, type, flags, mode);
#endif
}

static int
prepare_env()
{
    int rc;
    rc = db_env_create(&dbenv, 0);
    if (rc)
	log_db_error("db_env_create", rc);
    else {
	dbenv->set_errcall(dbenv, db_errcall_fcn);
	rc = dbenv->set_lk_detect(dbenv, DB_LOCK_YOUNGEST);
	if (rc)
	    log_db_error("dbenv->set_lk_detect DB_LOCK_YOUNGEST, expired triplets will not be deleted", rc);
	else
	    deadlock_detect = 1;
	rc = dbenv->open(dbenv, db_home,
			 DB_INIT_LOCK | DB_INIT_MPOOL | DB_CREATE, 0);
	if (rc) {
	    log_db_error("dbenv->open", rc);
	    dbenv->close(dbenv, 0);
	    dbenv = 0;
	}
    }
    return rc;
}

static int
prepare_db()
{
    int rc;
    rc = db_create(&db, dbenv, 0);
    if (rc)
	log_db_error("db_create", rc);
    else {
	rc = db_open(db, DB_FILE_NAME, NULL, DB_BTREE, DB_CREATE, 0644);
	if (rc) {
	    log_db_error("db->open", rc);
	    db->close(db, 0);
	    db = 0;
	}
    }
    return rc;
}

static int
initialize()
{
    int rc;
    char *version;
    int major, minor, patch;
    rc = policy_initialize();
    if (rc)
	return rc;
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
    rc = prepare_env();
    if (!rc)
	rc = prepare_db();
    return rc;
}

static void
cleanup()
{
    int rc;
    if (dbkey.data)
	free(dbkey.data);
    if (db) {
	rc = db->close(db, 0);
	if (rc)
	    log_db_error("DB close", rc);
    }
    rc = db_create(&db, dbenv, 0);
    if (!rc)
	if (! db->remove(db, "tls_stats.db", 0, 0))
	    syslog(LOG_NOTICE, "Unused database tls_stats.db removed");
    db = 0;
    if (dbenv) {
	rc = dbenv->close(dbenv, 0);
	dbenv = 0;
	if (rc)
	    log_db_error("DB_ENV close", rc);
    }
    policy_cleanup();
}

static void
fatal(const char *msg)
{
    syslog(LOG_ERR, "fatal: %s", msg);
    abort();
}

static void
run_expiry()
{
    DBC *dbcp;
    int rc;
    time_t now;
    unsigned int count = 0;
    /* Cursor operations can hold several locks and therefore deadlock
       so don't run expiry if deadlock detection does not work
       http://www.oracle.com/technology/documentation/berkeley-db/db/ref/lock/notxn.html */
    if (db == 0 || deadlock_detect == 0)
	return;
    if (time(&now) == (time_t)-1) {
	syslog(LOG_ERR, "time failed during run_expiry");
	return;
    }
    muffle_error++;
    if (rc = db->cursor(db, 0, &dbcp, 0))
	log_db_error("db->cursor failed during expiry run", rc);
    else {
	DBT key = { 0 };
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
		if (opt_verbose)
		    syslog(LOG_INFO, "Expiring %s %s after %.0f seconds idle",
			   key.data,
			   triplet_data.pass_count ? "pass" : "block", age);
		if (rc = dbcp->c_del(dbcp, 0))
		    log_db_error("dbcp->c_del failed", rc);
		else
		    count++;
	    }
	}
	if (rc == DB_LOCK_DEADLOCK)
	    syslog(LOG_DEBUG, "skipping concurrent expiry avoids "
		   "deadlocks and unnecessary work");
	else if (rc != DB_NOTFOUND)
	    log_db_error("dbcp->c_get failed", rc);
	if (rc = dbcp->c_close(dbcp))
	    log_db_error("dbcp->c_close failed", rc);
    }
    muffle_error--;
    if (count)
	syslog(LOG_NOTICE, "Expired %u triplets", count);
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

static void
do_dump_triplets()
{
    DBC *dbcp;
    int rc;
    DBT key = { 0 },
	data = { 0 };
    rc = db->cursor(db, 0, &dbcp, 0);
    if (rc)
	fprintf(stderr, "DBD-%d: db->cursor failed: %s\n",
		rc, db_strerror(rc));
    else {
	while ((rc = dbcp->c_get(dbcp, &key, &data, DB_NEXT)) == 0) {
	    const char *s = key.data;
	    const struct triplet_data *t = data.data;
	    printf("%d\t", t->crypted);
	    printf("%s\t", s);
	    s += strlen(s) + 1;
	    printf("%s\t", s);
	    s += strlen(s) + 1;
	    fwrite(s, 1, key.size - (s - (char *)key.data), stdout);
	    putchar('\t');
	    write_ctime(&t->create_time);
	    putchar('\t');
	    write_ctime(&t->access_time);
	    printf("\t%lu\t%lu\n", t->block_count, t->pass_count);
	}
	if (rc != DB_NOTFOUND)
	    fprintf(stderr, "DBD-%d: dbcp->c_get failed: %s\n",
		    rc, db_strerror(rc));
	rc = dbcp->c_close(dbcp);
	if (rc)
	    fprintf(stderr, "DBD-%d: dbcp->c_close failed: %s\n",
		    rc, db_strerror(rc));
    }
}

static void
build_triplet_key(const char *ip, const char *from, const char *to)
{
    const char *endip = strchr(ip, '\n'),
	*endfrom = strchr(from, '\n'),
	*endto = strchr(to, '\n');
    size_t lenfrom = endfrom - from,
	lento = endto - to;
    int ipv4 = memchr(ip, '.', endip - ip) != 0;
    size_t lenip, total;
    char *buf;
    /* Mangle the IP address so that only the required prefix is used */
    if (ipv4 && ipv4_network_strip_bytes > 0) {
	const char *p = endip;
	unsigned int i = ipv4_network_strip_bytes;
	while (i && --p > ip)
	    if (*p == '.')
		i--;
	if (i <= 1)
	    endip = p;
	else {
	    ipv4 = 0;
	    syslog(LOG_ERR, "Could not apply network strip");
	}
    }
    lenip = endip - ip,
    total = lenip + lenfrom + lento + 2;
    if (dbkey.ulen < total) {
	dbkey.data = xrealloc(dbkey.data, total);
	dbkey.ulen = total;
	dbkey.flags = DB_DBT_USERMEM;
    }
    buf = (char*)dbkey.data;
    if (ipv4 && ipv4_network_mask != 0xffU) {
	/* Mask the last octet of the IP address */
	char *q;
	unsigned long byte;
	const char *p = endip;
	while (--p > ip)
	    if (*p == '.')
		break;
	if (*p == '.')
	    p++;
	byte = strtoul(p, &q, 10);
	if (p != q && q <= endip && byte < 256U) {
	    size_t n = p - ip;
	    memcpy(buf, ip, n);
	    buf += n;
	    /* XXX the byte we are subsituting can only be smaller
	       than the original so no additional memory is needed. */
	    n = sprintf(buf, "%lu", byte & ipv4_network_mask);
	    buf += n;
	    assert(buf - (char *)dbkey.data <= lenip);
	}
	else
	    ipv4 = 0;
    }
    if (! ipv4 || ipv4_network_mask == 0xffU) {
	memcpy(buf, ip, lenip);
	buf += lenip;
    }
    *buf++ = 0;
    if (debug_me)
	syslog(LOG_DEBUG, "triplet effective IP: %s", dbkey.data);
    memcpy(buf, from, lenfrom);
    buf += lenfrom;
    *buf++ = 0;
    memcpy(buf, to, lento);
    buf += lento;
    dbkey.size = buf - (char *)dbkey.data;
    assert(dbkey.size <= dbkey.ulen);
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
get_grey_data()
{
    int rc;
    if (!db)
	jmperr(PACKAGE_STRING " database not opened");
    rc = db->get(db, NULL, &dbkey, &dbdata, 0);
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
put_grey_data()
{
    int rc;
    rc = db->put(db, NULL, &dbkey, &dbdata, 0);
    if (rc)
	log_db_error("put", rc);
    return rc;
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
    if (setjmp(defect_jmp_buf)) {
	if (defect_msg) {
	    printf(STR_ACTION "WARN %s\n", defect_msg);
	    defect_msg = 0;
	}
	else
	    puts(STR_ACTION "WARN " PACKAGE_STRING " is not working properly");
	return 1;
    }
    // FIXME this could overwrite
    get_grey_data();
    if (triplet_data.crypted != crypted) {
      syslog(LOG_DEBUG,"crypted field changed for some reason");
      triplet_data.crypted = crypted;
    }
    delay = difftime(triplet_data.access_time, triplet_data.create_time);

    /* Block inbound mail that is from a previously unknown (ip, from, to) triplet */
    /* However we want different behavior for crypted stuff
     */

    if(crypted > 0) {
	fputs(STR_ACTION, stdout);
	printf_action(cryptolisted_action_fmt, delay);
	putchar('\n');
    } else {
      // IN the case of unecrypted data
      if(delay < greylist_delay) {
	triplet_data.block_count++;
	fputs(STR_ACTION, stdout);
	printf_action(reject_action_fmt, greylist_delay - delay);
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
    return put_grey_data();
}

static void
signal_handler(int signal)
{
    cleanup();
    syslog(LOG_NOTICE, "Received signal %d", signal);
    kill(getpid(), signal);
    exit(-1);
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
	    "Usage: %s [-V] [-v] [-d] [-h <Berkeley DB home directory>] [-g <greylist delay>]\n"
	    "    [-b <bloc maximum idle>] [-p <pass maximum idle>] [-r <reject action>]\n"
	    "    [-G <greylisted action>] [-/ <network bits>] [--dump-triplets] [--help]\n"
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
	    "	This determines how many seconds we will block inbound mail\n"
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
	    "	Defaults to 32 i.e. the whole adresse is significant.\n"
	    "\n"
	    "    --dump-triplets\n"
	    "\n"
	    "        Dump the triplets database to stdout.  Mostly for debugging\n"
	    "        purposes.\n",
	    progname, AUTO_RECORD_LIFE_SECS, DELAY_MAIL_SECS,
	    UPDATE_RECORD_LIFE_SECS, reject_action_fmt, greylisted_action_fmt);
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
    int rc;
    unsigned long network_prefix = 32;
    unsigned int suffix;
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
	else if (optp(argv[i], "-h", "--home")) {
	    if (++i >= argc)
		fatal("Missing argument to --home");
	    db_home = argv[i];
	}
	else if (optp(argv[i], "-/", "--network-prefix")) {
	    if (++i >= argc)
		fatal("Missing argument to --network-prefix");
	    network_prefix = strtoul(argv[i], &p, 10);
	    if (*p || network_prefix > 32U)
		fatal("Invalid argument to --network-prefix.  "
		      "Integer value between 0 and 32 expected");
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
	else if (optp(argv[i], "-G", "--greylisted-action")) {
	    if (++i >= argc)
		fatal("Missing argument to --greylisted-action");
	    greylisted_action_fmt = argv[i];
	}
	else if (loptp(argv[i], "--dump-triplets")) {
	  dump_triplets = 1;
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

    suffix = 32 - network_prefix;
    ipv4_network_strip_bytes = suffix >> 3;
    ipv4_network_mask = 0xffU & ~0U << (suffix & 0x7U);

#ifdef SIGHUP
    signal(SIGHUP, signal_handler);
#endif
#ifdef SIGINT
    signal(SIGINT, signal_handler);
#endif
#ifdef SIGQUIT
    signal(SIGQUIT, signal_handler);
#endif
#ifdef SIGILL
    signal(SIGILL, signal_handler);
#endif
#ifdef SIGABRT
    signal(SIGABRT, signal_handler);
#endif
#ifdef SIGSEGV
    signal(SIGSEGV, signal_handler);
#endif
#ifdef SIGALRM
    signal(SIGALRM, signal_handler);
#endif
#ifdef SIGTERM
    signal(SIGTERM, signal_handler);
#endif

    rc = initialize();
    if (rc) {
	cleanup();
	syslog(LOG_ERR, "error: initialization failure: %s", db_strerror(rc));
    }
    if (dump_triplets)
	do_dump_triplets();
    else while (read_policy_request(0)) {
	const char *protocol = 0, *state = 0, *ip, *from, *to, 
	  *encryption_protocol = 0, *ccert_fingerprint = 0;
	int crypted = 0;
	if ((protocol = find_attribute("protocol_name"))
	    && (state = find_attribute("protocol_state"))
	    && (prefixp(protocol, STR_SMTP) || prefixp(protocol, STR_ESMTP))
	    && prefixp(state, STR_RCPT)
	    && (ip = find_attribute("client_address"))
	    && (from = find_attribute("sender"))
	    && (to = find_attribute("recipient"))) {
	    encryption_protocol = find_attribute("encryption_protocol");
	    ccert_fingerprint = find_attribute("ccert_fingerprint");
	    if (encryption_protocol) {
	      triplet_data.crypted = TRANSPORT_ENCRYPTED; // FIXME, figure out what it is
	    }
	    syslog(LOG_DEBUG,"Encryption: %s Fingerprint: %s", 
		   encryption_protocol ? encryption_protocol : "NA",
		   ccert_fingerprint ? ccert_fingerprint : "NA");  

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
    return 0;
}
