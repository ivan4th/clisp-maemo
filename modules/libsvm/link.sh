file_list=''
mod_list=''
if test -f libsvm.c; then # if we use :library in ffi, no C file is created
  file_list="$file_list libsvm.o `pwd`/svm${SHREXT}"
  mod_list="$mod_list"' libsvm'
fi
${MAKE-make} clisp-module \
  CC="${CC}" CPPFLAGS="${CPPFLAGS}" CFLAGS="${CFLAGS}" \
  CLISP_LINKKIT="$absolute_linkkitdir" SHREXT=${SHREXT} CLISP="${CLISP}"
NEW_FILES="${file_list}"
NEW_LIBS="${file_list} -lm"
NEW_MODULES="${mod_list}"
TO_LOAD='libsvm'
TO_PRELOAD="preload.lisp"
