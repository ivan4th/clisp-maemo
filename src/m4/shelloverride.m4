AC_DEFUN([CL_SHELL_OVERRIDE],
[AC_ARG_WITH(shell, [  --with-shell=SHELL      use SHELL as the system shell])
AC_MSG_CHECKING([for shell override])
if test ! -z "$with_shell" ; then
  AC_DEFINE_UNQUOTED([SHELL_OVERRIDE], "$with_shell", [System shell to use instead of /bin/sh])
  AC_MSG_RESULT(got \"$with_shell\")
else
  AC_MSG_RESULT(none)
fi
])
