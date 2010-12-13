AUTOMAKE_OPTIONS = foreign
datastatedir = $(localstatedir)/lib
sbin_PROGRAMS = cryptolist
cryptolist_SOURCES = cryptolist.c policy.c policy.h

install-data-local:
	test -d "$(DESTDIR)$(datastatedir)" || $(MKDIR_P) "$(DESTDIR)$(datastatedir)"
	$(mkinstalldirs) -o nobody -m 700 "$(DESTDIR)$(datastatedir)/$(PACKAGE)"
