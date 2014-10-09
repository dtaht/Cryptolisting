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

#define prefixp(s,p) (!strncmp((s),(p),sizeof(p)-1))

#define STR_SMTP "SMTP"
#define STR_ESMTP "ESMTP"
#define STR_RCPT "RCPT"
#define STR_ACTION "action="

/* FIXME this should actually be part of greyfix.h */
extern void *exit_requested;

extern const char *progname;
extern int opt_verbose;
extern int debug_me;

extern void *xrealloc(void *, size_t);
extern void policy_initialize();
extern void policy_cleanup();
extern char *find_attribute(const char *);
extern const char *read_policy_request(int);
