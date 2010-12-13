AC_INIT([greyfix], [0.3.9])
AC_CONFIG_HEADERS([config.h])
AC_PREREQ(2.59)
AC_CONFIG_SRCDIR([greyfix.c])
AM_INIT_AUTOMAKE
AC_ARG_WITH(berkeleydb-includedir,
	AS_HELP_STRING([--with-berkeleydb-includedir],
		       [Specify location of Berkeley DB header files]),
	CPPFLAGS="-I$withval $CPPFLAGS")
AC_ARG_WITH(berkeleydb-libdir,
	AS_HELP_STRING([--with-berkeleydb-libdir],
		       [Specify location of the Berkeley DB library files]),
	LDFLAGS="-L$withval $LDFLAGS")
CPPFLAGS="$CPPFLAGS -DDATA_STATE_DIR=\"\\\"\$(datastatedir)\\\"\""
AC_CHECK_HEADER([db.h], ,
	AC_MSG_ERROR([Berkeley DB header file is missing]))
dnl XXX Berkeley DB version 4.2 and before used macros instead of functions
dnl rendering AC_CHECK_LIB unusable.
AC_CHECK_LIB(db, db_version)
AC_MSG_CHECKING(match between Berkeley DB header files and runtime)
AC_RUN_IFELSE([AC_LANG_PROGRAM([[#include <db.h>]],
			       [[int M, m; db_version(&M, &m, 0);
			       return DB_VERSION_MAJOR != M || DB_VERSION_MINOR != m;]])],
	,
	AC_MSG_ERROR([Berkeley DB header file does not match the library file]))
AC_MSG_RESULT(yes)
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
