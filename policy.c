/* Copyright 2007 by Kim Minh Kaplan
 *
 * policy.c
 *
 * Postfix policy daemon routines
 *
 * Postfix SMTP Access Policy Delegation:
 *     http://www.postfix.org/SMTPD_POLICY_README.html
 * Postfix: http://www.postfix.org/
 * Kim Minh Kaplan: http://www.kim-minh.com/
 */
/* XXX COMMON */
#ifdef HAVE_CONFIG_H
#include <config.h>
#endif
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>
#include <syslog.h>

#include "policy.h"

const char *progname = 0;
int opt_verbose = 0;
int debug_me = 0;

static char *policy_request = 0;
static size_t policy_request_size = 0;
static size_t policy_request_fill = 0;

void *
xrealloc(void *ptr, size_t size)
{
    void *newptr = realloc(ptr, size);
    if (newptr)
	return newptr;
    syslog(LOG_ERR, "fatal: out of memory in xrealloc: %s", strerror(errno));
    abort();
}

int
policy_initialize()
{
    if (opt_verbose)
	syslog(LOG_NOTICE, "Policy daemon");
    return 0;
}

void
policy_cleanup()
{
    if (policy_request)
	free(policy_request);
    if (debug_me)
	syslog(LOG_DEBUG, "Cleaned");
}

/* XXX Assumes there is an empty line marking the end of request */
char *
find_attribute(const char *name)
{
    char *p;
    size_t nlen;
    nlen = strlen(name);
    for (p = policy_request; *p != '\n'; p = strchr(p, '\n') + 1)
	if (strncmp(name, p, nlen) == 0 && p[nlen] == '=')
	    return p + nlen + 1;
    return NULL;
}

static char *
find_empty_line(const char *p, const char *const endp)
{
    while (p < endp && (p = memchr(p, '\n', endp - p))) {
	p++;
	if (p < endp && *p == '\n')
	    return (char *) p + 1;
    }
    return NULL;
}

/* Find the end of request marker */
static char *
find_eor()
{
    return find_empty_line(policy_request,
			   policy_request + policy_request_fill);
}

/* Forget the oldest policy request */
static void
forget_policy_request()
{
    const char *eor = find_eor();
    if (eor) {
	policy_request_fill -= eor - policy_request;
	memmove(policy_request, eor, policy_request_fill);
    }
    else
	policy_request_fill = 0;
}

/* Read in a new SMTPD access policy request */
const char *
read_policy_request(int in)
{
    forget_policy_request();
    while (! find_eor()) {
	size_t wanted;
	int n;
	/* Make sure there is some room to read data */
	if (policy_request_fill == policy_request_size) {
	    if (policy_request_size)
		policy_request_size *= 2;
	    else
		policy_request_size = BUFSIZ;
	    if (debug_me)
		syslog(LOG_DEBUG,
		       "allocate %u bytes for request buffer",
		       policy_request_size);
	    policy_request = xrealloc(policy_request, policy_request_size);
	}
	wanted = policy_request_size - policy_request_fill;
	n = read(in, policy_request + policy_request_fill, wanted);
	if (n < 0)
	    syslog(LOG_ERR, "read_policy_request failed: %s: %d",
		   strerror(errno), n);
	else if (n)
	    policy_request_fill += n;
	else
	    return NULL;
    }
    return policy_request;
}

