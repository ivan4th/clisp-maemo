/*
 * Pathnames for CLISP
 * Bruno Haible 1990-2003
 * Logical Pathnames: Marcus Daniels 16.9.1994
 * ANSI compliance, bugs: Sam Steingold 1998-2003
 * German comments translated into English: Stefan Kain 2002-01-03
 */

#include "lispbibl.c"
#ifdef WIN32_NATIVE
#include "w32shell.c"
#endif
#ifdef HAVE_DISASSEMBLER
  #include <string.h> /* declares strlen() */
#endif

# enable the following #define to debug pathname translations
# setting DEBUG_TRANSLATE_PATHNAME to a larger value results in more output
# WARNING: PRIN1 can trigger GC! BEWARE!
# define DEBUG_TRANSLATE_PATHNAME 1
#if DEBUG_TRANSLATE_PATHNAME
#define string_concat(x) (printf("[%d]string_concat(%d)\n",__LINE__,x),(string_concat)(x))
# define DOUT(l,o) printf("[%d] %s %s\n",__LINE__,l,#o);gar_col()
#define DOUT(label,obj)  OBJECT_OUT(obj,label)
#define SDOUT(label,obj) printf("%d %s %s",__LINE__,label,STRING(obj));nobject_out(stdout,obj)
#else
#define DOUT(l,o)
#define SDOUT(l,o)
#endif

# =============================================================================
#                       Low level functions

# UP: Tests whether a pathname is possibly a symlink.
# possible_symlink(path)
#ifdef UNIX_LINUX
local inline bool possible_symlink (const char* path) {
  # In Linux 2.0.35, /proc/<pid>/{cwd,exe,root} and /proc/<pid>/fd/<n>
  # are symlinks pointing to void. Treat them like non-symlinks, in order
  # to avoid errors.
  if (path[0]=='/'
      && path[1]=='p' && path[2]=='r' && path[3]=='o' && path[4]=='c'
      && path[5]=='/'
      && (path[6]>='0' && path[6]<='9'))
    return false;
  return true;
}
#else
  #define possible_symlink(path)  true
#endif

#ifdef UNIX_LINUX
# The Linux /proc filesystem has some symlinks whose readlink value is
# zero-terminated: /proc/self in Linux 2.0.35, /proc/<pid>/fd/<n> in
# Linux 2.2.2. Remove this extraneous trailing zero byte.
local inline int my_readlink (const char* path, char* buf, size_t bufsiz) {
  var int linklen = readlink(path,buf,bufsiz);
  if (linklen > 0 && buf[linklen-1] == '\0')
    linklen--;
  return linklen;
}
#define readlink  my_readlink
#endif

#ifdef UNIX
  # library-function realpath implementation:
  # [Copyright: SUN Microsystems, B. Haible]
  # TITLE
  #   REALPATH(3)
  # SYNOPSIS
  #   char* realpath (const char* path, char resolved_path[MAXPATHLEN]);
  # DESCRIPTION
  #   realpath() expands all symbolic links  and  resolves  refer-
  #   ences  to '/./', '/../' and extra '/' characters in the null
  #   terminated string named by path and stores the canonicalized
  #   absolute pathname in the buffer named by resolved_path.  The
  #   resulting path will have no symbolic links  components,  nor
  #   any '/./' or '/../' components.
  # RETURN VALUES
  #   realpath() returns a pointer to the  resolved_path  on  suc-
  #   cess.   On  failure, it returns NULL, sets errno to indicate
  #   the error, and places in resolved_path the absolute pathname
  #   of the path component which could not be resolved.
#define realpath my_realpath # avoid conflict with Consensys realpath declaration
local char* realpath (const char* path, char* resolved_path) {
  # Method: use getwd and readlink.
  var char mypath[MAXPATHLEN];
  var int symlinkcount = 0; # the number of symbolic links so far
  var char* resolved_limit = &resolved_path[MAXPATHLEN-1];
  # Valid pointers are those with resolved_path <= ptr <= resolved_limit.
  # in *resolved_limit at most one null byte.
  # (similarly with mypath.)
  var char* resolve_start;
  {
    var char* resolved_ptr = resolved_path; # always <= resolved_limit
    # poss. use Working-Directory:
    if (!(path[0]=='/')) { # not an absolute pathname?
      if (getwd(resolved_path) == NULL)
        return NULL;
      resolved_ptr = resolved_path;
      while (*resolved_ptr) {
        resolved_ptr++;
      }
      if (resolved_ptr < resolved_limit) {
        *resolved_ptr++ = '/';
      }
      resolve_start = resolved_ptr;
    } else {
      resolve_start = resolved_ptr = &resolved_path[0];
    }
    # copy the path:
    var const char* path_ptr = path;
    while ((resolved_ptr < resolved_limit) && *path_ptr) {
      *resolved_ptr++ = *path_ptr++;
    }
    # finish with '/' and a null:
    if (resolved_ptr < resolved_limit) {
      *resolved_ptr++ = '/';
    }
    *resolved_ptr = 0;
  }
  # Now start in resolved_path at resolve_start.
  var char* from_ptr = resolve_start;
  var char* to_ptr = resolve_start;
  while ((to_ptr < resolved_limit) && (*from_ptr)) {
    # so far the path in  resolved_path[0]...to_ptr[-1]
    # has the shape '/subdir1/subdir2/.../txt',
    # whereas 'txt' is poss. empty, but no subdir is empty.
    var char next = *from_ptr++; *to_ptr++ = next;
    if ((next == '/') && (to_ptr > resolved_path+1)) {
      # to_ptr[-1]='/'  ->  resolve Directory ...to_ptr[-2] :
      var char* last_subdir_end = &to_ptr[-2];
      switch (*last_subdir_end) {
        case '/':
          #ifdef PATHNAME_UNIX_UNC
          if (to_ptr > resolved_path+2)
          #endif
            # '//' is simplified to '/' :
            to_ptr--;
          break;
        case '.':
          {
            var char* last_subdir_ptr = &last_subdir_end[-1];
            if (to_ptr > resolved_path+2) {
              if (*last_subdir_ptr == '.') {
                if ((to_ptr > resolved_path+4)
                    && (*--last_subdir_ptr == '/')) {
                  # last subdir was '/../'
                  # Therefore remove the subdir in front of it:
                  while ((last_subdir_ptr > resolved_path)
                         && !(*--last_subdir_ptr == '/'));
                  to_ptr = last_subdir_ptr+1;
                }
              } else if (*last_subdir_ptr == '/') {
                # last subdir was '/./'
                # remove:
                to_ptr = last_subdir_end;
              }
            }
          }
          break;
        default:
          # after a normal subdir
          #ifdef HAVE_READLINK
          if (possible_symlink(resolved_path)) {
            # read symbolic link:
            to_ptr[-1]=0; # replace '/' with 0
            #ifdef UNIX_CYGWIN32
            # readlink() does not work right on NFS mounted directories
            # (it returns -1,ENOENT or -1,EIO).
            # So check for a directory first.
            var struct stat statbuf;
            if (lstat(resolved_path,&statbuf) < 0)
              return NULL; # error
            if (S_ISDIR(statbuf.st_mode)) {
              # directory, not a symbolic link
              to_ptr[-1] = '/'; # insert the '/' again
            } else if (!S_ISLNK(statbuf.st_mode)) {
              # something else, but not a directory or symbolic link.
              errno = ENOTDIR;
              return NULL;
            } else
            #endif
              {
                var int linklen =
                  readlink(resolved_path,mypath,sizeof(mypath)-1);
                if (linklen >=0) {
                  # was a symbolic link
                  if (++symlinkcount > MAXSYMLINKS) {
                    errno = ELOOP_VALUE; return NULL;
                  }
                  # append the still to be resolved part of path
                  # to the link-content:
                  {
                    var char* mypath_ptr = &mypath[linklen]; # here is room
                    var char* mypath_limit = &mypath[MAXPATHLEN-1]; # up to here
                    if (mypath_ptr < mypath_limit) { *mypath_ptr++ = '/'; } # first, append a '/'
                    # then the rest:
                    while ((mypath_ptr <= mypath_limit)
                           && (*mypath_ptr = *from_ptr++))
                      { mypath_ptr++; }
                    *mypath_ptr = 0; # and conclude wit 0
                  }
                  # this replaces resp. completes the path:
                  if (mypath[0] == '/') {
                    # replaces the path:
                    from_ptr = &mypath[0]; to_ptr = resolved_path;
                    while ((*to_ptr++ = *from_ptr++));
                    from_ptr = resolved_path;
                  } else {
                    # completes the path:
                    # disrcard link-name. Therefore search for the last '/':
                    {
                      var char* ptr = &to_ptr[-1];
                      while ((ptr > resolved_path) && !(ptr[-1] == '/')) { ptr--; }
                      from_ptr = ptr;
                    }
                    {
                      var char* mypath_ptr = &mypath[0]; to_ptr = from_ptr;
                      while ((to_ptr <= resolved_limit) && (*to_ptr++ = *mypath_ptr++));
                    }
                  }
                  to_ptr = from_ptr;
                } else {
                  #if defined(UNIX_IRIX)
                  if ((errno == EINVAL) || (errno == ENXIO))
                  #elif defined(UNIX_MINT)
                  if ((errno == EINVAL) || (errno == EACCESS))
                  #elif defined(UNIX_CYGWIN32)
                  if ((errno == EINVAL) || (errno == EACCES))
                  #else
                  if (errno == EINVAL)
                  #endif
                    # no symbolic link
                    to_ptr[-1] = '/'; # insert the '/' again
                  else
                    return NULL; # error
                }
              }
          }
          #endif
          break;
      }
    }
  } # go for the next subdir
  # discard a '/' at the tail:
  if ((to_ptr[-1] == '/')
      #ifdef PATHNAME_UNIX_UNC
      && (to_ptr > resolved_path+2)
      #else
      && (to_ptr > resolved_path+1)
      #endif
      )
    to_ptr--;
  to_ptr[0] = 0; # conclude with 0
  return resolved_path; # finished
}
#endif
#ifdef RISCOS
  # SYNOPSIS
  #   char* realpath (char* path, char resolved_path[MAXPATHLEN]);
  # RETURN VALUES
  #   realpath() returns a pointer to the resolved_path on success.
  #   On failure, it returns NULL and sets errno to indicate the error.
#define realpath my_realpath # there is no consensus on realpath declaration
#include <sys/os.h>
local char* realpath (char* path, char* resolved_path) {
  var int handle;
  var int r[10];
  #if 0 # Both of these implementations should work.
  if (os_fopen(0x40,path,&handle))
    return NULL;
  r[0] = 7; r[1] = handle; r[2] = (long)resolved_path; r[5] = MAXPATHLEN;
  os_swi(9,r);
  os_fclose(handle);
  #else
  var os_error* err;
  r[0] = 37; r[1] = (long)path; r[2] = (long)resolved_path;
  r[3] = 0; r[4] = 0; r[5] = MAXPATHLEN;
  err = os_swi(0x29,r);
  if (err) {
    __seterr(err); return NULL;
  }
  #endif
  if (r[5] <= 0) {
    errno = ENOMEM /* ENAMETOOLONG would be better, but does not yet exist */;
    return NULL;
  }
  return resolved_path;
}
#endif

# Creates a new subdirectory.
# make_directory(pathstring);
# > pathstring: result of shorter_directory(...)
# > STACK_0: pathname
local inline void make_directory (char* pathstring) {
 #ifdef AMIGAOS
  set_break_sem_4();
  begin_system_call();
  {
    var BPTR lock = CreateDir(pathstring); # create sub-directory
    if (lock==BPTR_NULL) {
      end_system_call(); OS_file_error(STACK_0);
    }
    UnLock(lock); # release lock
  }
  end_system_call();
  clr_break_sem_4();
 #endif
 #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
  begin_system_call();
  if (mkdir(pathstring,0777)) { # create sub-directory
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  if (! CreateDirectory(pathstring,NULL) ) { # create sub-directory
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
}

# Deletes a subdirectory.
# delete_directory(pathstring);
# > pathstring: result of shorter_directory(...)
# > STACK_0: pathname
local inline void delete_directory (char* pathstring) {
 #ifdef AMIGAOS
  # yet test, if it is really a directory and not a file??
  begin_system_call();
  if (! DeleteFile(pathstring) ) { # delete sub-directory
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
 #if defined(UNIX) || defined(EMUNIX)
  begin_system_call();
  if (rmdir(pathstring)) { # delete sub-directory
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
 #ifdef RISCOS
  begin_system_call();
  if (unlink(pathstring)) { # delete sub-directory
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  if (! RemoveDirectory(pathstring) ) { # delete sub-directory
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
}

#if defined(MSDOS) || defined(WIN32_NATIVE)
# Changes the operating system's current directory.
# change_directory(pathstring);
# > pathstring: directory, ASCIZ-String
# > STACK_0: pathname
local inline void change_current_directory (char* pathstring) {
  begin_system_call();
 #ifdef MSDOS
  if (!( chdir(pathstring) ==0)) {
    end_system_call(); OS_file_error(STACK_0);
  }
 #endif
 #ifdef WIN32_NATIVE
  if (!SetCurrentDirectory(pathstring)) {
    end_system_call(); OS_file_error(STACK_0);
  }
 #endif
  end_system_call();
}
#endif

# Delete a file.
# delete_existing_file(pathstring);
# It is known that the file exists.
# > pathstring: file name, ASCIZ-String
# > STACK_0: pathname
local inline void delete_existing_file (char* pathstring) {
 #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
  begin_system_call();
  if (!( unlink(pathstring) ==0)) {
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
 #if defined(AMIGAOS) || defined(WIN32_NATIVE)
  begin_system_call();
  if (! DeleteFile(pathstring) ) {
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
}

#ifdef WIN32_NATIVE
#define WIN32_ERROR_NOT_FOUND (GetLastError()==ERROR_FILE_NOT_FOUND || GetLastError()==ERROR_PATH_NOT_FOUND || GetLastError()==ERROR_BAD_NETPATH)
#endif

# Delete a file.
# delete_file_if_exists(pathstring);
# No error is signaled if the file does not exist.
# > pathstring: file name, ASCIZ-String
# > STACK_0: pathname
# < result: whether the file existed
local inline bool delete_file_if_exists (char* pathstring) {
  var bool exists = true;
 #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
  begin_system_call();
  if (!( unlink(pathstring) ==0)) {
    if (!(errno==ENOENT)) { # not found -> OK
      end_system_call(); OS_file_error(STACK_0); # report other error
    }
    exists = false;
  }
  end_system_call();
 #endif
 #ifdef AMIGAOS
  begin_system_call();
  if (! DeleteFile(pathstring) ) {
    if (!(IoErr()==ERROR_OBJECT_NOT_FOUND)) { # not found -> OK
      end_system_call(); OS_file_error(STACK_0); # report other error
    }
    exists = false;
  }
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  if (! DeleteFile(pathstring) ) {
    if (!WIN32_ERROR_NOT_FOUND) {
      end_system_call(); OS_file_error(STACK_0);
    }
    exists = false;
  }
  end_system_call();
 #endif
  return exists;
}

# Delete a file being the target of a subsequent rename.
# delete_file_before_rename(pathstring);
# No error is signaled if the file does not exist.
# > pathstring: file name, ASCIZ-String
# > STACK_0: pathname
local inline void delete_file_before_rename (char* pathstring) {
 #if !defined(UNIX) # rename() on Unix does it automatically
  delete_file_if_exists(pathstring);
 #endif
}

# Rename a file.
# rename_existing_file(old_pathstring,new_pathstring);
# It is known that the old_pathstring exists.
# On platforms except UNIX, it is known that new_pathstring does not exist.
# > old_pathstring: old file name, ASCIZ-String
# > new_pathstring: new file name, ASCIZ-String
# > STACK_0: pathname
local inline void rename_existing_file (char* old_pathstring,
                                        char* new_pathstring) {
 #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
  begin_system_call();
  if ( rename(old_pathstring,new_pathstring) <0) { # rename file
    end_system_call(); OS_file_error(STACK_0); # report error
  }
  end_system_call();
 #endif
 #ifdef AMIGAOS
  begin_system_call();
  if (! Rename(old_pathstring,new_pathstring) ) {
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  if (! MoveFile(old_pathstring,new_pathstring) ) {
    end_system_call(); OS_file_error(STACK_0);
  }
  end_system_call();
 #endif
}

# Rename a file.
# rename_file_to_nonexisting(old_pathstring,new_pathstring);
# It is known that new_pathstring does not exist.
# > old_pathstring: old file name, ASCIZ-String
# > new_pathstring: new file name, ASCIZ-String
# > STACK_3: old pathname
# > STACK_1: new pathname
local inline void rename_file_to_nonexisting (char* old_pathstring,
                                              char* new_pathstring) {
 #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
  begin_system_call();
  if ( rename(old_pathstring,new_pathstring) <0) { # rename file
    if (errno==ENOENT) {
      end_system_call(); OS_file_error(STACK_3);
    } else {
      end_system_call(); OS_file_error(STACK_1);
    }
  }
  end_system_call();
 #endif
 #ifdef AMIGAOS
  begin_system_call();
  if (! Rename(old_pathstring,new_pathstring) ) {
    if (IoErr()==ERROR_OBJECT_NOT_FOUND) {
      end_system_call(); OS_file_error(STACK_3);
    } else {
      end_system_call(); OS_file_error(STACK_1);
    }
  }
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  if (! MoveFile(old_pathstring,new_pathstring) ) {
    if (WIN32_ERROR_NOT_FOUND) {
      end_system_call(); OS_file_error(STACK_3);
    } else {
      end_system_call(); OS_file_error(STACK_1);
    }
  }
  end_system_call();
 #endif
}

# =============================================================================
#                         P A T H N A M E S

# All simple-strings occurring in pathnames are in fact normal-simple-strings.

#ifdef PATHNAME_AMIGAOS
# components:
# HOST          always NIL
# DEVICE        NIL or Simple-String
# DIRECTORY     (Startpoint . Subdirs) with
#                Startpoint = :RELATIVE | :ABSOLUTE
#                Subdirs = () | (subdir . Subdirs)
#                subdir = :WILD-INFERIORS (means "**" or "...", all subdirectories) or
#                subdir = :PARENT (means "/" instead of "subdir/") or
#                subdir = Simple-String, poss. with Wildcard-Character ? and *
# NAME          NIL or
#               Simple-String, poss. wit Wildcard-Character ? and *
#               (also :WILD on input)
# TYPE          NIL or
#               Simple-String, poss. with Wildcard-Character ? and *
#               (also :WILD on input)
# VERSION       always NIL (also :WILD or :NEWEST on input)
# Constraint: Startpoint = :RELATIVE only, if Device = NIL;
#             for a specified device there are only absolute Pathnames!
# An AMIGAOS-Filename is split in Name and Type as follows:
#   if there is no '.' in filename: Name = everything, Type = NIL,
#   if there is a '.' in filename: Name = everything in front, Type = everything behind the last '.' .
# capital-/small letters within the Strings are ignored for comparison,
# but apart from that no conversion between capital and small letters takes place.
# If a pathname must be completely specified (no wildcards),
# :WILD, :WILD-INFERIORS is not permitted; no wildcard-characters in the
# Strings, no NIL at NAME poss. too.
# External Notation:  device:sub1.typ/sub2.typ/name.typ
# with Defaults:             sub1.typ/sub2.typ/name.typ
# or                                           name.typ
# or                         sub1.typ/ ** /sub3.typ/x*.lisp  (without Spaces!)
# or similar.
# Formal:
#   ch ::= any Character except ':','/' and '*','?'
#   name ::= {ch}+
#   device ::= [ <empty> | ':' | name ':' ]
#              ; empty = current device, relative from the current directory
#              ; ':'  = current device, absolute (from root for disks)
#              ; name ':' = specified device, absolute (from root for disks)
#   subdir ::= [ <empty> | name ]                ; empty = '..'
#   pathname ::= device { subdir '/' }* name
# Examples:
#   String        Device    Directory                unser Pathname
#   ------        ------    ---------                --------------
#   'c:foo'       'C',     device->foo               "c" (:ABSOLUTE "foo")
#   'c:foo/'      'C',     device->foo               "c" (:ABSOLUTE "foo")
#   'c:foo/bar'   'C',     device->foo->bar          "c" (:ABSOLUTE "foo" "bar")
#   'c:/foo'      'C',     device->up->foo           "c" (:ABSOLUTE :PARENT "foo")
#   'c:'          'C',     device                    "c" (:ABSOLUTE)
#   ':foo'        current, device->root->foo         NIL (:ABSOLUTE "foo")
#   'foo'         current, device->foo               NIL (:RELATIVE "foo")
#   '/foo'        current, device->up->foo           NIL (:RELATIVE :PARENT "foo")
#   '//foo/bar'   current, device->up->up->foo->bar  NIL (:RELATIVE :PARENT :PARENT "foo" "bar")
#   ''            current, device                    NIL (:RELATIVE)
# A '/' can be appended to a pathstring, that is non-empty and that does
#  not end with ':' or '/', without changing its semantics.
# This '/' must be appended, before a further non-empty
# component can be appended.
# Appending a '/' to a pathstring, that is empty or that ends with ':' or '/' ,
# means to ascend to the Parent Directory!
# We interprete each pathstring, that is empty or that ends with ':' or '/' ,
# as directory-pathname (with Name=NIL and Type=NIL) .
#endif

#ifdef PATHNAME_UNIX
# Components:
# HOST          always NIL
# DEVICE        always NIL
# DIRECTORY     (Startpoint . Subdirs) whereas
#                Startpoint = :RELATIVE | :ABSOLUTE
#                Subdirs = () | (subdir . Subdirs)
#                subdir = :WILD-INFERIORS (means "**" or "...", all subdirectories) or
#                subdir = Simple-String, poss. with wildcard-character ? and *
# NAME          NIL or
#               Simple-String, poss. with wildcard-character ? and *
#               (also :WILD on input)
# TYPE          NIL or
#               Simple-String, poss. with wildcard-character ? and *
#               (also :WILD on input)
# VERSION       always NIL (also :WILD or :NEWEST on input)
# A UNIX-filename is split in Name and Type as follows:
#   if there is no '.' in Filename: Name = everything, Type = NIL,
#   if there is '.' in Filename: Name = everything in front of it, Type = everything behind the last '.' .
# If a pathname must be completely specified (no wildcards),
#  :WILD, :WILD-INFERIORS are not allowed, no wildcard-characters in the
# Strings, at NAME poss. also not NIL.
# External Notation:  server:/sub1.typ/sub2.typ/name.typ
# with Defaults:             /sub1.typ/sub2.typ/name.typ
# or                                            name.typ
# or                         /sub1.typ/ ** /sub3.typ/x*.lisp  (without Spaces!)
# or similar.
# If NAME starts with a dot, (parse-namestring (namestring pathname)) will not
# be the same as pathname.
#endif

#ifdef PATHNAME_OS2
# Components:
# HOST          always NIL
# DEVICE        NIL or :WILD or "A"|...|"Z"
# DIRECTORY     (Startpoint . Subdirs) whereas
#                Startpoint = :RELATIVE | :ABSOLUTE
#                Subdirs = () | (subdir . Subdirs)
#                subdir = :WILD-INFERIORS (means "**" or "...", all Subdirectories) or
#                subdir = Simple-String, poss. with Wildcard-Characters ? and *
# NAME          NIL or
#               Simple-String, poss. with Wildcard-Character ? and *
#               (also :WILD on input)
# TYPE          NIL or
#               Simple-String, poss. with Wildcard-Character ? and *
#               (also :WILD on input)
# VERSION       always NIL (also :WILD or :NEWEST on input)
# An OS/2-Filename is split into Name and Type as follows:
#   if there is no '.' in filename: Name = everything, Type = NIL,
#   if there is a '.' in filename: Name = everything in front of, Type = everything behind the last '.' .
# If a Pathname must be completely specified (no Wildcards),
# then :WILD, :WILD-INFERIORS are not allowed, no Wildcard-Characters in the
# Strings, at NAME poss. also not NIL.
# External notation:       A:\sub1.typ\sub2.typ\name.typ
# with Defaults:             \sub1.typ\sub2.typ\name.typ
# or                                            name.typ
# or                       *:\sub1.typ\**\sub3.typ\x*.lisp
# or similar.
# Instead of '\'  - traditionally on DOS - also '/' is allowed.
#endif

#ifdef PATHNAME_WIN32
# Components:
# HOST          NIL or Simple-String (Wildcard-Characters are without meaning)
# DEVICE        NIL or :WILD or "A"|...|"Z"
# DIRECTORY     (Startpoint . Subdirs) whereas
#                Startpoint = :RELATIVE | :ABSOLUTE
#                Subdirs = () | (subdir . Subdirs)
#                subdir = :WILD-INFERIORS (means "**" or "...", all Subdirectories) or
#                subdir = Simple-String, poss. with Wildcard-Character ? and *
# NAME          NIL or
#               Simple-String, poss. with Wildcard-Character ? and *
#               (also :WILD on input)
# TYPE          NIL or
#               Simple-String, poss. with Wildcard-Character ? and *
#               (also :WILD on input)
# VERSION       always NIL (also :WILD or :NEWEST on input)
# If HOST is non-NIL, DEVICE must be NIL.
# A WIN32-Filename is split into Name and Type as follows:
#   if there is no '.' in Filename: Name = everything, Type = NIL,
#   if there is a '.' in Filename: Name = everything in front of, Type = everything behind the last '.' .
# If a Pathname must be completely specified (no Wildcards),
# then :WILD, :WILD-INFERIORS are not allowed, no Wildcard-Characters in the
# Strings, at NAME poss. also not NIL.
# External notation:       A:\sub1.typ\sub2.typ\name.typ
# with Defaults:             \sub1.typ\sub2.typ\name.typ
# or                                            name.typ
# or                       *:\sub1.typ\**\sub3.typ\x*.lisp
# or similar.
# Instead of '\'  - traditionally on DOS - also '/' is allowed.
# If HOST is non-NIL and the DIRECTORY's Startpoint is not :ABSOLUTE,
# (parse-namestring (namestring pathname)) will not be the same as pathname.
#endif

#ifdef PATHNAME_RISCOS
#
# Peter Burwood <clisp@arcangel.demon.co.uk> writes:
#
# RISC OS provides several filing systems as standard (ADFS, IDEFS, NetFS,
# RamFS, NetPrint) and support for extra filing systems (DOSFS, ResourceFS and
# DeviceFS).
#
# A module called FileSwitch is at the centre of all filing system operation
# in RISC OS. FileSwitch provides a common core of functions used by all
# filing systems. It only provides the parts of these services that are device
# independent. The device dependant services that control the hardware are
# provided by separate modules, which are the actual filing systems.
# FileSwitch keeps track of active filing systems and switches betwen them as
# necessary.
#
# One of the filing system modules that RISC OS provides is FileCore. It takes
# the normal calls that FileSwitch sends to a filing system module, and
# converts them to a simpler set of calls to modules that control the
# hardware. Unlike FileSwitch it creates a fresh instantiation of itself for
# each module that it supports. Using FileCore to build filing system modules
# imposes a more rigid structure on it, as more of the filing system is
# predefined.
#
# As well as standard filing systems, FileSwitch supports image filing
# systems. These provide facilities for RISC OS to handle media in foreign
# formats, and to support `image files' (or partitions) in those formats.
# Rather than accessing the hardware directly they rely on standard RISC OS
# filing systems to do so. DOSFS is an example of an image filing system used
# to handle DOS format discs.
#
# Terminology
#
# A pathname may include a filing system name, a special field, a media name
# (e.g., a disc name), directory name(s), and the name of the object itself;
# each of these parts of a pathname is known as an `element' of the pathname.
#
# Filenames
#
# Filename `elements' may be up to ten characters in length on FileCore-based
# filing systems and on NetFS. These characters may be digits or letters.
# FileSwitch makes no distinction between upper and lower case, although
# filing systems can do so. As a general rule, you should not use top-bit-set
# characters in filenames, although some filing systems (such as
# FileCore-based ones) support them. Other characters may be used provided
# they do not have a special significance. Those that do are listed below :
#
#    .   Separates directory specifications, e.g., $.fred
#    :   Introduces a drive or disc specification, e.g., :0, :bigdisc. It also
#        marks the end of a filing system name, e.g., adfs:
#    *   Acts as a `wildcard' to match zero or more characters.
#    #   Acts as a `wildcard' to match any single character.
#    $   is the name of the root directory of the disc.
#    &   is the user root directory (URD)
#    @   is the currently selected directory (CSD)
#    ^   is the `parent' directory
#    %   is the currently selected library (CSL)
#    \   is the previously selected directory (PSD)
#
# Directories
#
# The root directory, $, forms the top of the directory hierarchy
# of the media which contains the CSD. $ does not have a parent directory,
# trying to access its parent will just access $. Each directory name is
# separated by a '.' character. For example:
#
#    $.Documents.Memos
#    %.cc
#
# Filing Systems
#
# Files may also be accessed on filing systems other than the current one by
# prefixing the filename with a filing system specification. A filing system
# name may appear between '-' characters, or suffixed by a ':', though the
# latter is advised since '-' can also be used to introduce a parameter on a
# command line, or as part of a file name. For example:
#
#    -net-$.SystemMesg
#    adfs:%.aasm
#
# Special Fields
#
# Special fields are used to supply more information to the filing system than
# you can using standard path names; for example NetFS and NetPrint use them
# to specify server addresses or names. They are introduced by a '#'
# character; a variety of syntaxes are possible:
#
#    net#MJHardy::disc1.mike
#       #MJHardy::disc1.mike
#   -net#MJHardy-:disc1.mike
#      -#MJHardy-:disc1.mike
#
# The special fields here are all MJHardy, and give the name of the fileserver
# to use. Special fields may use any character except for control characters,
# double quote '"', solidus '|' and space. If a special field contains a hypen
# you may only use the first two syntaxes given above.
#
# File$Path and Run$Path
#
# These two special variables control exactly where a file will be looked for,
# according to the operation being performed on it.
#
#    File$Path   for read operations
#    Run$Path    for execute operations
#
# The contents of each variable should expand to a list or prefixes, separated
# by commas. When a read operation is performed then the prefixes in File$Path
# are used in the order in which they are listed. The first object that
# matches is used, whether it be a file or directory. Similarly any execute
# operation uses the prefixes in Run$Path. These search paths are only used
# when the pathname does not contain an explicit filing system reference,
# e.g., executing adfs:file will not use Run$Path.
#
# Other path variables
#
# You can set up other path variables and use them as pseudo filing systems.
# For example if you typed:
#
#    *Set Source$Path adfs:$.src.,adfs:$.public.src.
#
# you could then refer to the pseudo filing system as Source: or (less
# preferable) as -Source-. These path variables work in the same was as
# File$Path and Run$Path.
#
# NOTE: Path variables are not implemented in this version of CLISP. A
# workaround for this is to use "<Foo$Path>" instead of "Foo:" until they are
# made available.
#
#
# from Lisp-string notation to internal representation
# ----------------------------------------------------
# NO swapping. "foo.lisp" means file type "lisp" and file name "foo".
# This is pseudo-BNF:
#
# legal character ::= any ISO latin-1 graphic character >= ' ' except
#                     '.' ':' '*' '#' '$' '&' '@' '^' '%' '\' '?'
#
# extended legal character ::= any ISO latin-1 graphic character >= ' ' except
#                              ':' '"' '|'
#
# legal-wild char ::= legal char | '*' | '#' | '?'
#
# host ::=   '-' { extended legal char except '-' }+ '-'
#          | { extended legal char except '-' } { extended legal char }* ':'
#          | empty
#
# device ::=   ':' { legal char }+ '.'
#            | empty
#
# directory ::=   { '$' | '&' | '@' | '%' | '\' } '.' { subdirectory }*
#               | { subdirectory }+
#               | empty
#
# '$' -> :ABSOLUTE :ROOT, '&' -> :ABSOLUTE :HOME, '@' -> :ABSOLUTE :CURRENT,
# '%' -> :ABSOLUTE :LIBRARY, '\' -> :ABSOLUTE :PREVIOUS, else :RELATIVE.
#
# subdirectory ::= { '^' | { legal-wild char }+ } '.'
#                  '^' -> :PARENT
#
# filename ::= { { legal-wild char }+ | empty }
#
# filetype ::= { '.' { legal-wild char }+ | empty }
#
# pathname ::= host device directory filename filetype
#
# Examples:
# String                          Hostname Device  Directory            Name         Type
# -net-$.SystemMesg                "net"   NIL     (:ABSOLUTE :ROOT)    "SystemMesg" NIL
# net#MJHardy::disc1.mike    "net#MJHardy" "disc1" (:ABSOLUTE :ROOT)    "mike"       NIL
# #MJHardy::disc1.mike          "#MJHardy" "disc1" (:ABSOLUTE :ROOT)    "mike"       NIL
# -net#MJHardy-:disc1.mike   "net#MJHardy" "disc1" (:ABSOLUTE :ROOT)    "mike"       NIL
# -#MJHardy-:disc1.mike         "#MJHardy" "disc1" (:ABSOLUTE :ROOT)    "mike"       NIL
# @.foo                            NIL     NIL     (:ABSOLUTE :CURRENT) "foo"        NIL
# foo                              NIL     NIL     (:RELATIVE)          "foo"        NIL
# ^.                               NIL     NIL     (:RELATIVE :PARENT)  NIL          NIL
# @.^.                             NIL     NIL     (:ABSOLUTE :CURRENT :PARENT) NIL  NIL
# foo.bar                          NIL     NIL     (:RELATIVE)          "foo"        "bar"
# foo.bar.baz                      NIL     NIL     (:RELATIVE "foo")    "bar"        "baz"
# foo.bar.                         NIL     NIL     (:RELATIVE "foo" "bar") NIL       NIL
# foo.@.                       illegal
#
# from internal representation to RISCOS string
# ---------------------------------------------
#
# with swapping _only_ of name/type components.
#
# Hostname    Device  Directory                   Name    Type      RISCOS String
#
# "net"       "disc1" (:ABSOLUTE :ROOT)           "foo"   NIL       "net::disc1.$.foo"
# "net#MJ"    "disc1" (:ABSOLUTE :ROOT "foo")     "bar"   "baz"     "net#MJ::disc1.$.foo.baz.bar"
# "adfs"      "4"     (:ABSOLUTE :ROOT "foo" "bar") NIL   NIL       "adfs::4.$.foo.bar"
# NIL         "disc1" (:ABSOLUTE :ROOT "foo")     "bar"   NIL       ":disc1.$.foo.bar"
# NIL         "disc1" (:ABSOLUTE :CURRENT)        NIL     NIL       illegal here
# NIL         "disc1" (:RELATIVE)                 NIL     NIL       ":disc1."
# NIL         "disc1" NIL                         NIL     NIL       ":disc1."
# NIL         NIL     (:ABSOLUTE :ROOT)           "foo"   NIL       "$.foo"
# NIL         NIL     (:ABSOLUTE :CURRENT)        "foo"   NIL       "@.foo"
# NIL         NIL     (:RELATIVE)                 "foo"   "bar"     "bar.foo"
# NIL         NIL     (:RELATIVE "foo")           "bar"   "baz"     "foo.baz.bar"
# NIL         NIL     (:ABSOLUTE :LIBRARY)        "bar"   NIL       "%.bar"
# NIL         NIL     (:ABSOLUTE :LIBRARY "foo")  "bar"   NIL       "%.foo.bar"
# NIL         NIL     (:RELATIVE)                 "foo"   "bar"     "bar.foo"
# NIL         NIL     (:RELATIVE "foo")           "bar"   NIL       "foo.bar"
# NIL         NIL     (:RELATIVE "foo")           NIL     "bar"     illegal here
#
# That is, the RISCOS string is the flattenation-concatenation of
#   (append
#     (if (null hostname) "" (append hostname ":"))
#     (if (null device) "" (append ":" device "."))
#     (case (pop directory)
#       (:ABSOLUTE (case (pop directory)
#                          (:ROOT "$.")
#                          (:HOME "&.")
#                          (:CURRENT "@.")
#                          (:LIBRARY "%.")
#                          (:PREVIOUS "\\.")
#       )          )
#       (:RELATIVE "")
#     )
#     (mapcar (lambda (subdir) (append subdir ".")) directory)
#     (if (null name)
#       (if (null type) "" (error "type with name illegal here"))
#       (if (null type)
#         name
#         (append type "." name)
#   ) ) )
#
# internal representation
# -----------------------
#
# Pathname components:
# HOST          Simple-String or NIL
# DEVICE        Simple-String or NIL
# DIRECTORY     (Startpoint . Subdirs) where
#                Startpoint = :RELATIVE | :ABSOLUTE anchor
#                anchor = :ROOT | :HOME | :CURRENT | :LIBRARY | :PREVIOUS
#                Subdirs = () | (subdir . Subdirs)
#                subdir = :PARENT or
#                subdir = simple string, may contain wildcard characters ?,# and *
# NAME          NIL or
#               simple string, may contain wildcard characters ?,# and *
#               (may also be specified as :WILD)
# TYPE          NIL or
#               simple string, may contain wildcard characters ?,# and *
#               (may also be specified as :WILD)
# VERSION       always NIL (may also be specified as :WILD or :NEWEST)
#
# Constraint: startpoint /= :ABSOLUTE :ROOT only if device = NIL. If the device
# is specified, the pathname must be :ABSOLUTE :ROOT.
#
# Components:
# HOST          Simple-String or NIL
# DEVICE        Simple-String or NIL
# DIRECTORY     (Startpoint . Subdirs) whereas
#                Startpoint = :RELATIVE | :ABSOLUTE Anker
#                Anker = :ROOT | :HOME | :CURRENT | :LIBRARY | :PREVIOUS
#                Subdirs = () | (subdir . Subdirs)
#                subdir = :PARENT oder
#                subdir = Simple-String, poss. with Wildcard-Character ?,# and *
# NAME          NIL or
#               Simple-String, poss. with Wildcard-Character ?,# and *
#               (also :WILD on input)
# TYPE          NIL or
#               Simple-String, poss. with Wildcard-Character ?,# and *
#               (also :WILD on input)
# VERSION       always NIL (also :WILD or :NEWEST on input)
#
#endif

#ifdef LOGICAL_PATHNAMES
# Components of Logical Pathnames:
# HOST          Simple-String or NIL
# DEVICE        always NIL
# DIRECTORY     (Startpoint . Subdirs) whereas
#                Startpoint = :RELATIVE | :ABSOLUTE
#                Subdirs = () | (subdir . Subdirs)
#               subdir = :WILD-INFERIORS (means "**", all Subdirectories) or
#               subdir = :WILD (means "*") or
#               subdir = Simple-String, poss. with Wildcard-Character *
# NAME          NIL or
#               :WILD (means "*") or
#               Simple-String, poss. with Wildcard-Character *
# TYPE          NIL or
#               :WILD (means "*") or
#               Simple-String, poss. with Wildcard-Character *
# VERSION       NIL or :NEWEST or :WILD or Integer
# External Notation: see CLtl2 p. 628-629.
#endif

# access functions without case transforms:
# xpathname_host(logical,pathname)
# xpathname_device(logical,pathname)
# xpathname_directory(logical,pathname)
# xpathname_name(logical,pathname)
# xpathname_type(logical,pathname)
# xpathname_version(logical,pathname)
# > pathname: pathname or logical pathname
# > logical: flag = logpathnamep(pathname)
# < result: the value of the requested component
#if HAS_HOST
#define pathname_host_maybe(obj) (object)ThePathname(obj)->pathname_host
#else
#define pathname_host_maybe(obj) (unused(obj), NIL)
#endif
#if HAS_DEVICE
#define pathname_device_maybe(obj) (object)ThePathname(obj)->pathname_device
#else
#define pathname_device_maybe(obj) (unused(obj), NIL)
#endif
#if HAS_VERSION
#define pathname_version_maybe(obj) (object)ThePathname(obj)->pathname_version
#else
#define pathname_version_maybe(obj) (unused(obj), NIL)
#endif

#ifdef LOGICAL_PATHNAMES
#define xpathname_host(logical,pathname)                       \
  (logical ? (object)TheLogpathname(pathname)->pathname_host : \
             pathname_host_maybe(pathname))
#define xpathname_device(logical,pathname)  \
  (logical ? NIL : pathname_device_maybe(pathname))
#define xpathname_directory(logical,pathname)                       \
  (logical ? (object)TheLogpathname(pathname)->pathname_directory : \
                (object)ThePathname(pathname)->pathname_directory)
#define xpathname_name(logical,pathname)                       \
  (logical ? (object)TheLogpathname(pathname)->pathname_name : \
                (object)ThePathname(pathname)->pathname_name)
#define xpathname_type(logical,pathname)                       \
  (logical ? (object)TheLogpathname(pathname)->pathname_type : \
                (object)ThePathname(pathname)->pathname_type)
#define xpathname_version(logical,pathname)                       \
  (logical ? (object)TheLogpathname(pathname)->pathname_version : \
             pathname_version_maybe(pathname))
#else # no logical pathnames
#define xpathname_host(logical,pathname) \
  pathname_host_maybe(pathname)
#define xpathname_device(logical,pathname) \
  pathname_device_maybe(pathname)
#define xpathname_directory(logical,pathname) \
  ThePathname(pathname)->pathname_directory
#define xpathname_name(logical,pathname) \
  ThePathname(pathname)->pathname_name
#define xpathname_type(logical,pathname) \
  ThePathname(pathname)->pathname_type
#define xpathname_version(logical,pathname) \
  pathname_version_maybe(pathname)
#endif

#define SUBST_RECURSE(atom_form,self_call)                      \
  if (atomp(obj)) return atom_form;                             \
  check_STACK(); check_SP();                                    \
  pushSTACK(obj);                                               \
  { /* recursive call for CAR: */                               \
    object new_car = self_call(Car(obj));                       \
    pushSTACK(new_car);                                         \
  }                                                             \
  { /* recursive call for CDR: */                               \
    object new_cdr = self_call(Cdr(STACK_1));                   \
    if (eq(new_cdr,Cdr(STACK_1)) && eq(STACK_0,Car(STACK_1))) { \
      obj = STACK_1; skipSTACK(2); return obj;                  \
    } else { /* (CONS new_car new_cdr) */                       \
      STACK_1 = new_cdr;                                        \
     {object new_cons = allocate_cons();                        \
      Car(new_cons) = popSTACK(); Cdr(new_cons) = popSTACK();   \
      return new_cons;                                          \
    }}                                                          \
  }

# Converts capital-/small letters between :LOCAL and :COMMON .
# common_case(string)
# > string: Normal-Simple-String or Symbol/Number
# < result: converted Normal-Simple-String or the same Symbol/Number
# can trigger GC
# Operating System with preference for small letters or Capitalize
local object common_case (object string) {
  if (!simple_string_p(string))
    return string;
  var uintL len = Sstring_length(string);
  # Search, if capital- or small letters (or both) occur:
  var bool all_upper = true;
  var bool all_lower = true;
  if (len > 0) {
    var object storage = string; simple_array_to_storage(storage);
    SstringDispatch(storage,X, {
      var const cintX* ptr = &((SstringX)TheVarobject(storage))->data[0];
      var uintL count;
      dotimespL(count,len, {
        var chart ch = as_chart(*ptr++);
        if (!chareq(ch,up_case(ch)))
          all_upper = false;
        if (!chareq(ch,down_case(ch)))
          all_lower = false;
        if (!all_upper && !all_lower)
          break;
      });
    });
  }
  if (all_upper == all_lower)
    # all_upper = all_lower = true: Nothing to convert.
    # all_upper = all_lower = false: "Mixed case represents itself."
    return string;
  if (all_upper)
    # all_upper = true, all_lower = false: STRING-DOWNCASE
    return string_downcase(string);
  else
    # all_upper = false, all_lower = true: STRING-UPCASE
    return string_upcase(string);
}
# the same, recursive like with SUBST:
local object subst_common_case (object obj) {
  SUBST_RECURSE(common_case(obj),subst_common_case);
}

#ifdef LOGICAL_PATHNAMES

local bool legal_logical_word_char (chart ch) {
  ch = up_case(ch);
  var cint c = as_cint(ch);
  if (((c >= 'A') && (c <= 'Z'))
      || ((c >= '0') && (c <= '9'))
      || (c == '-'))
    return true;
  else
    return false;
}

#endif

#if HAS_HOST

# UP: Determines, if a character is allowed as character in the host-part
# of a namestring.
# legal_hostchar(ch)
# > chart ch: Character-Code
# < result: true if allowed, else false
# NB: legal_logical_word_char(ch) implies legal_hostchar(ch).
local bool legal_hostchar (chart ch) {
 #if defined(PATHNAME_RISCOS)
  return (graphic_char_p(ch)
          && !chareq(ch,ascii(':'))
          && !chareq(ch,ascii('"'))
          && !chareq(ch,ascii('|')));
 #elif defined(PATHNAME_WIN32)
  # This is just a guess. I do not know which characters are allowed in
  # Windows host names.
  var cint c = as_cint(ch);
  if ((c >= ' ') && (c <= '~')
      && (c != '"') && (c != '/') && (c != ':') && (c != '<') && (c != '>')
      && (c != '\\'))
    return true;
  else
    return false;
 #else
  return alphanumericp(ch) || chareq(ch,ascii('-'));
 #endif
}

# UP: check an optional HOST argument
# test_optional_host(host,convert)
# > host: Host-Argument
# > convert: Flag, if case-conversion is undesired
# < result: valid host-component
# can trigger GC
local object test_optional_host (object host, bool convert) {
  if (!boundp(host))
    return NIL;
  if (nullp(host))
    goto OK; # NIL is OK
  # Else, host must be a String, whose characters are alphanumeric:
  if (!stringp(host)) {
    pushSTACK(host);         # TYPE-ERROR slot DATUM
    pushSTACK(O(type_host)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(host);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: host should be NIL or a string, not ~"));
  }
  host = coerce_normal_ss(host); # as Normal-Simple-String
  if (convert)
    host = common_case(host);
  {
    var uintL len = Sstring_length(host);
    if (len > 0) {
      var const chart* charptr = &TheSstring(host)->data[0];
      dotimespL(len,len, {
        var chart ch = *charptr++;
        if (!legal_hostchar(ch))
          goto badhost;
      });
    }
  }
 OK: return host;
 badhost:
  pushSTACK(host);
  pushSTACK(TheSubr(subr_self)->name);
  fehler(parse_error,GETTEXT("~: illegal hostname ~"));
}

#else

#ifdef LOGICAL_PATHNAMES

# UP: check an optional HOST argument
# test_optional_host(host)
# > host: Host-Argument
# < result: valid host-component
# can trigger GC
local object test_optional_host (object host) {
  if (!boundp(host))
    return NIL; # not specified -> NIL
  if (nullp(host))
    goto OK; # NIL is OK
  # Else, host must be a String, whose characters are alphanumeric:
  if (!stringp(host)) {
    pushSTACK(host);         # TYPE-ERROR slot DATUM
    pushSTACK(O(type_host)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(host);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: host should be NIL or a string, not ~"));
  }
  host = coerce_normal_ss(host); # as Normal-Simple-String
  {
    var uintL len = Sstring_length(host);
    if (len > 0) {
      var object storage = host; simple_array_to_storage(storage);
      SstringDispatch(storage,X, {
        var const cintX* ptr = &((SstringX)TheVarobject(storage))->data[0];
        dotimespL(len,len, {
          var chart ch = as_chart(*ptr++);
          if (!legal_logical_word_char(ch))
            goto badhost;
        });
      });
    }
  }
 OK: return host;
 badhost:
  pushSTACK(host);
  pushSTACK(TheSubr(subr_self)->name);
  fehler(parse_error,GETTEXT("~: illegal hostname ~"));
}

#else

# UP: check an optional HOST argument
# test_optional_host(host);
# > host: Host-Argument
# < result: valid host-component
local object test_optional_host (object host) {
  if (boundp(host)) { # not specified -> OK
    if (!nullp(host)) { # specified -> should be =NIL
      pushSTACK(host);    # TYPE-ERROR slot DATUM
      pushSTACK(S(null)); # TYPE-ERROR slot EXPECTED-TYPE
      pushSTACK(host);
      pushSTACK(TheSubr(subr_self)->name);
      fehler(type_error,GETTEXT("~: host should be NIL, not ~"));
    }
  }
  return NIL;
}

#endif

#endif

# Determines, if two characters count as equal characters in pathnames.
# equal_pathchar(ch1,ch2)
# > chart ch1,ch2: Character-Codes
# < result: true if equal, else false
  #if !(defined(PATHNAME_AMIGAOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32))
    #define equal_pathchar(ch1,ch2)  chareq(ch1,ch2)
  #else # defined(PATHNAME_AMIGAOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
    # Case-insensitive, but normally without conversion
    #define equal_pathchar(ch1,ch2)  chareq(up_case(ch1),up_case(ch2))
  #endif

# UP: check whether the character is a valid element of NAME or TYPE
# component in a Namestring
# legal_namechar(ch)
# > chart ch: character-code
# < return: true if legal, else false
local bool legal_namechar (chart ch) {
  var uintB c;
 #ifdef UNICODE
  # Check whether ch fits into a single byte in O(pathname_encoding).
  if (!(cslen(O(pathname_encoding),&ch,1) == 1)) return false;
  cstombs(O(pathname_encoding),&ch,1,&c,1); # causes error message if it does not fit
 #else
  c = as_cint(ch);
 #endif
 #ifdef VALID_FILENAME_CHAR # defined in unixconf.h
  #define ch c
  return VALID_FILENAME_CHAR || (ch=='*') || (ch=='?');
  #undef ch
 #else
  #ifdef PATHNAME_AMIGAOS
  return (graphic_char_p(ch) && !(c=='/') && !(c==':'));
  #endif
  #ifdef PATHNAME_UNIX
  return ((c>=' ') && (c<='~') && !(c=='/'));
  #endif
  #ifdef PATHNAME_OS2
  return (graphic_char_p(ch) && !(c=='\\') && !(c=='/') && !(c==':'));
  #endif
  #ifdef PATHNAME_WIN32
  return ((c >= 1) && (c <= 127)
          && (c != '"') /*&& (c != '*')*/
          && (c != '/') && (c != ':')
          && (c != '<') && (c != '>') /*&& (c != '?')*/
          && (c != '\\'))
         || (c == 131)
         || (c >= 160);
  #endif
  #ifdef PATHNAME_RISCOS
  return (graphic_char_p(ch) && !(c==':') && !(c=='.')
          && !(c=='$') && !(c=='&') && !(c=='@')
          && !(c=='^') && !(c=='%') && !(c=='\\')
          # Wild Characters '*' '#' '?' are allowed here.
          );
  #endif
 #endif
}

# Determines, if a character is a wildcard for a single
# character.
# singlewild_char_p(ch)
# > chart ch: Character-Code
# < result: true if yes, else false
#if !defined(PATHNAME_RISCOS)
  #define singlewild_char_p(ch)  chareq(ch,ascii('?'))
#else # defined(PATHNAME_RISCOS)
  #define singlewild_char_p(ch)  (chareq(ch,ascii('?')) || chareq(ch,ascii('#')))
#endif
#define multiwild_char_p(ch)  chareq(ch,ascii('*'))
#define wild_char_p(ch)   (multiwild_char_p(ch) || singlewild_char_p(ch))

# Converts an object into a pathname.
local object coerce_xpathname (object obj); # later

# Converts an object into a non-logical pathname.
local object coerce_pathname (object obj); # later
#if !defined(LOGICAL_PATHNAMES)
#define coerce_pathname(obj)  coerce_xpathname(obj)
#endif

# Returns a default-pathname.
local object defaults_pathname (void); # later

# checks a default-pathname.
# test_default_pathname(defaults)
# > defaults: defaults-argument
# < result: value of the defaults-argument, a pathname
# can trigger GC
local object test_default_pathname (object defaults) {
  if (missingp(defaults))
    # not specified -> take value of *DEFAULT-PATHNAME-DEFAULTS* :
    return defaults_pathname();
  else
    # specified -> turn into a pathname:
    return coerce_xpathname(defaults);
}

# error-message because of illegal pathname-argument.
# fehler_pathname_designator(thing); ( fehler_... = error_... )
# > thing: (erroneous) argument
nonreturning_function(global, fehler_pathname_designator, (object thing)) {
  pushSTACK(thing);                       # TYPE-ERROR slot DATUM
  pushSTACK(O(type_designator_pathname)); # TYPE-ERROR slot EXPECTED-TYPE
  pushSTACK(O(type_designator_pathname));
  pushSTACK(thing);
  pushSTACK(TheSubr(subr_self)->name);
  fehler(type_error,
         GETTEXT("~: argument ~ should be a pathname designator ~"));
}

# Tracks a chain of Synonym-Streams, so long as a File-Stream
# is reached.
# as_file_stream(stream)
# > stream: Builtin-Stream
# < stream: File-Stream
local object as_file_stream (object stream) {
  var object s = stream;
  loop {
    if (TheStream(s)->strmtype == strmtype_file)
      return s;
    if (!(TheStream(s)->strmtype == strmtype_synonym))
      break;
    s = Symbol_value(TheStream(stream)->strm_synonym_symbol);
    if (!builtin_stream_p(s))
      break;
  }
  fehler_pathname_designator(stream);
}

# Signal an error if a file-stream does not have
# a file-name associated with it.
# test_file_stream_named(stream)
# > stream: File-Stream
#define test_file_stream_named(stream)  \
  do { if (nullp(TheStream(stream)->strm_file_truename)) \
         fehler_file_stream_unnamed(stream);             \
  } while(0)
nonreturning_function(local, fehler_file_stream_unnamed, (object stream)) {
  pushSTACK(stream); # FILE-ERROR slot PATHNAME
  pushSTACK(stream);
  pushSTACK(TheSubr(subr_self)->name);
  fehler(file_error,GETTEXT("~: filename for ~ is unknown"));
}

#if defined(UNIX) || defined(MSDOS) || defined(RISCOS) || defined(WIN32_NATIVE)

#if defined(UNIX) || defined(MSDOS)
  #define slash  '/'
#endif
#ifdef WIN32_NATIVE
  #define slash  '\\'
#endif
#ifdef RISCOS
  #define slash  '.'
#endif
# physical slash
#if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
 #define pslashp(c)  (chareq(c,ascii('\\')) || chareq(c,ascii('/')))
 #define cpslashp(c) ((c) == '\\' || (c) == '/')
#else /* PATHNAME_UNIX PATHNAME_AMIGAOS PATHNAME_RISCOS */
 #define pslashp(c)  chareq(c,ascii(slash))
 #define cpslashp(c) ((c) == slash)
#endif
#define colonp(c)    chareq(c,ascii(':'))
#ifndef LOGICAL_PATHNAMES
#define lslashp(c)   pslashp(c)
#endif

# UP: add a character to an ASCII string and return as a Lisp string
# can trigger GC
#ifdef UNICODE
local object asciz_add_char (const char* chars, uintL len, char ch,
                             object encoding)
#else
#define asciz_add_char(chars,len,ch,encoding)  asciz_add_char_(chars,len,ch)
local object asciz_add_char_ (const char* chars, uintL len, char ch)
#endif
{
  var DYNAMIC_ARRAY(buf,char,len+1);
  begin_system_call(); memcpy(buf,chars,len); end_system_call();
  buf[len] = ch;
  var object s = n_char_to_string(buf,len+1,encoding);
  FREE_DYNAMIC_ARRAY(buf);
  return s;
}

# UP: Converts a Unix-Directory-Specification into a pathname.
# asciz_dir_to_pathname(path,encoding)
# > const char* path: path as ASCIZ-String
# > encoding: Encoding
# < result: as a pathname without name and type
# can trigger GC
#ifdef UNICODE
local object asciz_dir_to_pathname(const char* path, object encoding)
#else
#define asciz_dir_to_pathname(path,encoding)  asciz_dir_to_pathname_(path)
local object asciz_dir_to_pathname_(const char* path)
#endif
{
  var object pathname;
  var uintL len = asciz_length(path); /* string length */
  /* if the String does not end with a '/' already, a '/' is added: */
  if ((len>0) && cpslashp(path[len-1]))
    pathname = n_char_to_string(path,len,encoding);
  else
    pathname = asciz_add_char(path,len,slash,encoding);
  # and convert into a pathname:
  return coerce_pathname(pathname);
}

#endif

# Type for PARSE-NAMESTRING:
# State while the string is being parsed character by character.
typedef struct {
  uintL index;    # index (incl. offset)
  object FNindex; # index as a fixnum
  uintL count;    # number of the remaining characters
} zustand;        # "state"

# Skip s characters.
#define Z_SHIFT(z,s) \
 do { (z).index += (s); (z).FNindex = fixnum_inc((z).FNindex,(s)); (z).count -= (s); } while(0)

# Tests whether the current character at Z satisfies pred.
#define Z_AT_SLASH(z,pred,st) \
  (((z).count != 0) && pred(schar(st,(z).index)))

# Replace this string with a substring.
#define Z_SUB(z,s) ((s) = subsstring((s),(z).index,(z).index+(z).count), (z).index = 0)

#ifdef LOGICAL_PATHNAMES

# Parsing of logical pathnames.

# separator between subdirs
#define semicolonp(c)  (chareq(c,ascii(';')))
#define lslashp(c)     semicolonp(c)

/* copy LEN characters in string ORIG starting at ORIG_OFFSET to string DEST,
   starting at DEST_OFFSET, up-casing all characters */
local void copy_upcase (object dest, uintL dest_offset,
                        object orig, uintL orig_offset, uintL len) {
  simple_array_to_storage(orig);
  SstringDispatch(orig,X1, {
    var cintX1* ptr1 = &((SstringX1)TheVarobject(orig))->data[orig_offset];
    simple_array_to_storage(dest);
    SstringDispatch(dest,X2, {
      var cintX2* ptr2 = &((SstringX2)TheVarobject(dest))->data[dest_offset];
      dotimespL(len,len, { *ptr2++ = as_cint(up_case(as_chart(*ptr1++))); });
    });
  });
}

# Parses the name/type/version part (if subdirp=false) or a subdir part
# (if subdirp=true) of a logical pathname.
# parse_logical_word(&z,subdirp)
# > STACK_2: storage vector, a normal-simple-string
# > zustand z: start state
# < zustand z: updated
# < result: a normal-simple-string or :WILD or :WILD-INFERIORS or NIL
# can trigger GC
local object parse_logical_word (zustand* z, bool subdirp) {
  ASSERT(sstring_normal_p(STACK_2));
  var zustand startz = *z; # start-state
  var chart ch;
  # Is there a sequence of alphanumeric characters or '*',
  # no two '*' adjacent (except "**", if subdirp),
  # and, if subdirp, a ';' ?
  var bool last_was_star = false;
  var bool seen_starstar = false;
  while (z->count) {
    ch = schar(STACK_2,z->index); # next character
    if (!legal_logical_word_char(ch)) {
      if (chareq(ch,ascii('*'))) {
        if (last_was_star) {
          if (subdirp && (z->index - startz.index == 1))
            seen_starstar = true;
          else
            break; # adjacent '*' are forbidden
        } else
          last_was_star = true;
      } else
        break;
    }
    # skip character:
    Z_SHIFT(*z,1);
  }
  var uintL len = z->index - startz.index;
  if (subdirp) {
    if ((z->count == 0) || !lslashp(ch)) {
      *z = startz; return NIL; # no ';' -> no subdir
    }
    # skip character ';' :
    Z_SHIFT(*z,1);
  }
  if (len==0)
    return NIL;
  else if ((len==1) && chareq(schar(STACK_2,startz.index),ascii('*')))
    return S(Kwild);
  else if ((len==2) && seen_starstar)
    return S(Kwild_inferiors);
  else {
    var object result = allocate_string(len);
    copy_upcase(result,0,STACK_2,startz.index,len);
    return result;
  }
}

# Test whether a string is a digit sequence.
# all_digits(string)
# > string: a normal-simple-string
# < true if the string consists entirely of digits, else false
local bool all_digits (object string) {
  var uintL len = Sstring_length(string);
  if (len > 0) {
    var object storage = string; simple_array_to_storage(storage);
    SstringDispatch(storage,X, {
      var const cintX* ptr = &((SstringX)TheVarobject(storage))->data[0];
      dotimespL(len,len, {
        var cintX c = *ptr++;
        if (!((c >= '0') && (c <= '9')))
          return false;
      });
    });
  }
  return true;
}

# test whether the string contains semicolons,
# thus appearing to be a logical pathname
# > string: storage vector, a normal-simple-string
# < result: true if the string contains semicolons
local bool looks_logical_p (object string) {
  var uintL len = Sstring_length(string);
  if (len > 0) {
    SstringDispatch(string,X, {
      var const cintX* charptr = &((SstringX)TheVarobject(string))->data[0];
      dotimespL(len,len, {
        var chart ch = as_chart(*charptr++);
        if (semicolonp(ch))
          return true;
      });
    });
  }
  return false;
}

# Attempt to parse a logical host name string, starting at a given state.
# parse_logical_host_prefix(&z,string)
# > string: storage vector, a normal-simple-string
# > state z: start state
# < state z: updated to point past the colon after the logical host
# < result: logical host, or NIL
# can trigger GC
local object parse_logical_host_prefix (zustand* zp, object string) {
  ASSERT(sstring_normal_p(string));
  var object host;
  var uintL startindex = zp->index;
  var chart ch;
  # a sequence of alphanumeric characters and then ':'
  loop {
    if (zp->count==0)
      return NIL; # string already ended -> no host
    ch = schar(string,zp->index); # next character
    if (!legal_logical_word_char(ch))
      break;
    # go past alphanumeric character:
    Z_SHIFT(*zp,1);
  }
  if (!colonp(ch))
    return NIL; # no ':' -> no host
  { # make host-string:
    var uintL len = zp->index - startindex;
    pushSTACK(string);
    host = allocate_string(len);
    # and fill it:
    if (len > 0)
      copy_upcase(host,0,popSTACK()/* ==string */,startindex,len);
  }
  # skip ':'
  Z_SHIFT(*zp,1);
  return host;
}

# CLHS for MAKE-PATHNAME: "Whenever a pathname is constructed the
# components may be canonicalized if appropriate."
# simplify the subdirectory list
# strings are coerced to normal simple strings
# the list should start with a valid startpoint (not checked!)
# > dir : pathname directory list
# < dir : the same list, destructively modified:
#         ".." or :back         ==> :up
#         ... x "foo" :up y ... ==> ... x y ...
#         ... x     "."   y ... ==> ... x y ...
#         :absolute :up   y ... ==> :absolute y ...
# can trigger GC
local object simplify_directory (object dir) {
  if (!consp(dir)) return dir;
  DOUT("simplify_directory:< ",dir);
  pushSTACK(dir);
  { # kill ".", ".."->:up, coerce to normal simple strings
    var object curr = dir;
    while (consp(curr) && consp(Cdr(curr))) {
      var object next = Cdr(curr);
      if (stringp(Car(next))) {
        if (string_equal(Car(next),O(dot_string))) {
          Cdr(curr) = Cdr(next); # drop "."
          continue;
        } else if (string_equal(Car(next),O(wild_string))) {
          Car(next) = S(Kwild);
          curr = next;
          continue;
        } else if (string_equal(Car(next),O(wildwild_string))) {
          Car(next) = S(Kwild_inferiors);
          curr = next;
          continue;
        } else if (!consp(next))
          break;
        if (string_equal(Car(next),O(dotdot_string)))
          Car(next) = S(Kup); # ".." --> :UP
        else {
          # coerce to normal
          pushSTACK(next);
          var object element = coerce_normal_ss(Car(next));
          next = popSTACK();
          Car(next) = element;
        }
      } else if (eq(Car(next),S(Kback)))
        Car(next) = S(Kup); # :BACK --> :UP (ANSI)
      curr = next;
    }
  }
  dir = popSTACK();
  # collapse "foo/../" (quadratic algorithm)
  var bool changed_p;
  do {
    changed_p = false;
    var object curr = dir;
    while (consp(curr) && consp(Cdr(curr))) {
      var object next = Cdr(curr);
      if (consp(Cdr(next))
          && !eq(Car(next),S(Kup)) && !eq(Car(next),S(Kwild_inferiors))
          && eq(Car(Cdr(next)),S(Kup))) {
        changed_p = true;
        Cdr(curr) = Cdr(Cdr(next)); # collapse "foo/../"
      } else
        curr = next;
    }
  } while (changed_p);
  if (eq(Car(dir),S(Kabsolute))) { # drop initial :up after :absolute
    while (consp(Cdr(dir)) && eq(Car(Cdr(dir)),S(Kup)))
      Cdr(dir) = Cdr(Cdr(dir));
  }
  DOUT("simplify_directory:> ",dir);
  return dir;
}

# Parses a logical pathname.
# parse_logical_pathnamestring(z)
# > STACK_1: storage vector, a normal-simple-string
# > STACK_0: freshly allocated logical pathname
# > state z: start state
# < STACK_0: same logical pathname, filled
# < result: number of remaining characters
# can trigger GC
local uintL parse_logical_pathnamestring (zustand z) {
  DOUT("parse_logical_pathnamestring:<0",STACK_0);
  DOUT("parse_logical_pathnamestring:<1",STACK_1);
  { # parse Host-Specification:
    var zustand startz = z;
    var object host = parse_logical_host_prefix(&z,STACK_1);
    if (nullp(host)) {
      z = startz; # back to the start
      host = STACK_(3+2); # Default-Host
    } else { # enter host:
      TheLogpathname(STACK_0)->pathname_host = host;
    }
  }
  { # enter Directory-Start:
    var object new_cons = allocate_cons(); # new Cons for Startpoint
    TheLogpathname(STACK_0)->pathname_directory = new_cons;
    pushSTACK(new_cons); # new (last (pathname-directory Pathname))
  }
  # stack layout:
  # data-vector, pathname, (last (pathname-directory Pathname)).
  # parse subdirectories:
  # If ";" is the first char, it is turned into :RELATIVE
  # (otherwise :ABSOLUTE) as the first subdir
  # for a reason that escapes me, ANSI CL specifies that
  # "foo:;bar;baz.zot" is a  :RELATIVE logical pathname while
  # "foo:/bar/baz.zot" is an :ABSOLUTE physical pathname.
  # see "19.3.1.1.3 The Directory part of a Logical Pathname Namestring"
  # http://www.lisp.org/HyperSpec/Body/sec_19-3-1-1-3.html
  if (Z_AT_SLASH(z,lslashp,STACK_2)) {
    Z_SHIFT(z,1);
    Car(STACK_0) = S(Krelative);
  } else {
    Car(STACK_0) = S(Kabsolute);
  }
  loop {
    # try to parse the next subdir
    var object subdir = parse_logical_word(&z,true);
    if (nullp(subdir))
      break;
    # lengthen (pathname-directory pathname) by Subdir:
    pushSTACK(subdir);
    var object new_cons = allocate_cons(); # new Cons
    Car(new_cons) = popSTACK(); # = (cons subdir NIL)
    Cdr(STACK_0) = new_cons; # lengthens (pathname-directory Pathname)
    STACK_0 = new_cons; # new (last (pathname-directory Pathname))
  }
  { # parse Name:
    var object name = parse_logical_word(&z,false);
    TheLogpathname(STACK_1)->pathname_name = name;
    if ((z.count > 0) && chareq(schar(STACK_2,z.index),ascii('.'))) {
      var zustand z_name = z;
      # skip Character '.' :
      Z_SHIFT(z,1);
      # parse Typ:
      var object type = parse_logical_word(&z,false);
      TheLogpathname(STACK_1)->pathname_type = type;
      if (!nullp(type)) {
        if ((z.count > 0) && chareq(schar(STACK_2,z.index),ascii('.'))) {
          var zustand z_type = z;
          # skip Character '.' :
          Z_SHIFT(z,1);
          # parse Version:
          var object version = parse_logical_word(&z,false);
          if (eq(version,S(Kwild))) {
          } else if (equal(version,Symbol_name(S(Knewest)))) {
            version = S(Knewest);
          } else if (all_digits(version)) { # convert version into Integer
            pushSTACK(version); funcall(L(parse_integer),1);
            version = value1;
          } else {
            version = NIL;
          }
          TheLogpathname(STACK_1)->pathname_version = version;
          if (nullp(version))
            z = z_type; # restore character '.'
        } else {
          TheLogpathname(STACK_1)->pathname_version = NIL;
        }
      } else {
        z = z_name; # restore character '.'
        TheLogpathname(STACK_1)->pathname_version = NIL;
      }
    } else {
      TheLogpathname(STACK_1)->pathname_type = NIL;
      TheLogpathname(STACK_1)->pathname_version = NIL;
    }
  }
  skipSTACK(1);
  TheLogpathname(STACK_0)->pathname_directory =
    simplify_directory(TheLogpathname(STACK_0)->pathname_directory);
  DOUT("parse_logical_pathnamestring:>0",STACK_0);
  DOUT("parse_logical_pathnamestring:>1",STACK_1);
  return z.count;
}

# recognition of a logical host, cf. CLtL2 p. 631
# (defun logical-host-p (host)
#   (and (simple-string-p host)
#        (gethash host sys::*logical-pathname-translations*) ; :test #'equalp !
#        t
# ) )
local bool logical_host_p (object host) {
  return (simple_string_p(host)
          # No need to string-upcase host, because it's tested via EQUALP.
          && !eq(gethash(host,Symbol_value(S(logpathname_translations))),
                 nullobj));
}

#endif

#define string2wild(str)  (equal(str,O(wild_string)) ? S(Kwild) : (object)(str))
#define wild2string(obj)  (eq(obj,S(Kwild)) ? (object)O(wild_string) : (obj))

#ifdef PATHNAME_NOEXT
# auxiliary function for PARSE-NAMESTRING:
# splits a string (at the last dot) into Name and Type.
# split_name_type(skip);
# > STACK_0: Normal-Simple-String
# > skip: 1 if a dot at the beginning should not trigger the splitting, else 0
# < STACK_1: Name
# < STACK_0: Type
# decrements STACK by 1
# can trigger GC
local void split_name_type (uintL skip) {
  if (skip == 0) {
    if (eq(Symbol_value(S(parse_namestring_dot_file)),S(Ktype))) { # OK
    } else if (eq(Symbol_value(S(parse_namestring_dot_file)),S(Kname))) {
      skip = 1; # always have a name!
    } else {
      Symbol_value(S(parse_namestring_dot_file)) = S(Ktype); # CLISP default
      pushSTACK(NIL);
      pushSTACK(S(parse_namestring_dot_file));
      pushSTACK(S(parse_namestring_dot_file));
      pushSTACK(Symbol_value(S(parse_namestring_dot_file)));
      STACK_3 = CLSTEXT("The variable ~S had an illegal value." NLstring
                        "~S has been reset to ~S.");
      funcall(S(warn),4);
    }
  }
  var object string = STACK_0;
  var uintL length = Sstring_length(string);
  # Search for the last dot:
  var uintL index = length;
  SstringDispatch(string,X, {
    var const cintX* ptr = &((SstringX)TheVarobject(string))->data[index];
    while (index > skip) {
      if (*--ptr == '.') goto punkt;
      index--;
    }
  });
  # no dot found -> Type := NIL
  pushSTACK(NIL);
  goto name_type_ok;
 punkt: # dot found at index
  # type := (substring string index)
  pushSTACK(subsstring(string,index,length));
  # name := (substring string 0 (1- index))
  STACK_1 = subsstring(STACK_1,0,index-1);
 name_type_ok:
  STACK_0 = string2wild(STACK_0);
  STACK_1 = string2wild(STACK_1);
}
#endif

# (PARSE-NAMESTRING thing [host [defaults [:start] [:end] [:junk-allowed]]]),
# CLTL p. 414
LISPFUN(parse_namestring,seclass_read,1,2,norest,key,3,
        (kw(start),kw(end),kw(junk_allowed)) ) {
  # stack layout: thing, host, defaults, start, end, junk-allowed.
  var bool junk_allowed;
  var bool parse_logical = false;
  DOUT("parse-namestring:[thng]",STACK_5);
  DOUT("parse-namestring:[host]",STACK_4);
  DOUT("parse-namestring:[dflt]",STACK_3);
  DOUT("parse-namestring:[beg]",STACK_2);
  DOUT("parse-namestring:[end]",STACK_1);
  DOUT("parse-namestring:[junk]",STACK_0);
  { # 1. check junk-allowed:
    var object obj = popSTACK(); # junk-allowed-Argument
    junk_allowed = !missingp(obj);
  }
  # stack layout: thing, host, defaults, start, end.
  # 2. default-value for start is 0:
  if (!boundp(STACK_1))
    STACK_1 = Fixnum_0;
  # 3. check host:
 #if HAS_HOST || defined(LOGICAL_PATHNAMES)
  {
    var object host = STACK_3;
   #if HAS_HOST
    host = test_optional_host(host,false);
   #else
    host = test_optional_host(host);
   #endif
    if (nullp(host)) {
      # host := (PATHNAME-HOST defaults)
      var object defaults = test_default_pathname(STACK_2);
     #ifdef LOGICAL_PATHNAMES
      if (logpathnamep(defaults))
        parse_logical = true;
     #endif
      host = xpathname_host(parse_logical,defaults);
    } else {
     #ifdef LOGICAL_PATHNAMES
      if (logical_host_p(host)) {
        parse_logical = true; host = string_upcase(host);
      }
     #endif
    }
    STACK_3 = host;
  }
 #else
  test_optional_host(STACK_3);
 #endif
  # 4. thing must be a String:
  DOUT("parse-namestring:[thng]",STACK_4);
  DOUT("parse-namestring:[host]",STACK_3);
  DOUT("parse-namestring:[dflt]",STACK_2);
  var object thing = STACK_4;
  if (xpathnamep(thing)) { # Pathname?
    value1 = thing; # 1. value thing
  fertig:
    DOUT("parse-namestring:[fertig]",value1);
    value2 = STACK_1; mv_count=2; # 2. value start
    skipSTACK(5); return;
  }
  if (builtin_stream_p(thing)) { # Stream?
    thing = as_file_stream(thing);
    test_file_stream_named(thing);
    value1 = TheStream(thing)->strm_file_name; # 1. value: Filename
    goto fertig; # 2. value like above
  }
  # thing should now be at least a String or a Symbol:
  var bool thing_symbol = false;
  if (!stringp(thing)) {
    if (!symbolp(thing) || !nullpSv(parse_namestring_ansi))
      fehler_pathname_designator(thing);
    thing = Symbol_name(thing); # Symbol -> use symbol name
    thing_symbol = true;
    STACK_4 = thing; # and write back into the Stack
  }
  # thing = STACK_4 is now a String.
  # it will be traversed.
  var zustand z; # running state
 #ifdef PATHNAME_RISCOS
  # auxiliary variables for the conversion of a new_thing-relative FNindex
  # into a thing-relative FNindex.
  var object FNindex_limit = Fixnum_0;
  var sintL FNindex_offset = 0;
  var object FNindex_fallback;
 #endif
  {
    var object string; # String thing
    { /* check boundaries, with thing, start, end as arguments: */
      var stringarg arg;
      pushSTACK(thing); pushSTACK(STACK_(1+1)); pushSTACK(STACK_(0+2));
      test_string_limits_ro(&arg);
      string = arg.string;
      z.index = arg.offset+arg.index; /* z.index = start-argument, */
      z.count = arg.len;           # z.count = number of characters.
      z.FNindex = fixnum(z.index); # z.FNindex = start-Index as Fixnum.
    }
   #ifdef LOGICAL_PATHNAMES
    if (!parse_logical) {
      # Check whether *PARSE-NAMESTRING-ANSI* is true and the string
      # starts with a logical hostname.
      if (!nullpSv(parse_namestring_ansi)) {
        # Coerce string to be a normal-simple-string.
        #ifdef HAVE_SMALL_SSTRING
        SstringCase(string,{ Z_SUB(z,string); },{ Z_SUB(z,string); },{});
        #endif
        var zustand tmp = z;
        var object host = parse_logical_host_prefix(&tmp,string);
        DOUT("parse-namestring:",string);
        DOUT("parse-namestring:",host);
        if (!nullp(host)
            # Test whether the given hostname is valid. This is not
            # strictly what ANSI specifies, but is better than giving
            # an error for Win32 pathnames like "C:\\FOOBAR".
            && logical_host_p(host))
          parse_logical = true;
        else
          # ANSI CL specifies that we should look at the entire string, using
          # parse_logical_pathnamestring, not only parse_logical_host_prefix.
          parse_logical = looks_logical_p(string);
      }
    }
   #endif
    if (thing_symbol && !parse_logical) {
     #if defined(PATHNAME_UNIX) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32) || defined(PATHNAME_RISCOS)
      # operating system with preference for small letters
      Z_SUB(z,string); # yes -> convert with STRING-DOWNCASE
      pushSTACK(string);
      nstring_downcase(string,0,Sstring_length(string));
      string = popSTACK();
      simple_array_to_storage(string);
     #endif
     #ifdef PATHNAME_AMIGAOS
      # operating system with preference for Capitalize
      Z_SUB(z,string); # yes -> convert with STRING-CAPITALIZE
      pushSTACK(string);
      nstring_capitalize(string,0,Sstring_length(string));
      string = popSTACK();
      simple_array_to_storage(string);
     #endif
    }
    # Coerce string to be a normal-simple-string.
    #ifdef HAVE_SMALL_SSTRING
    SstringCase(string,{ Z_SUB(z,string); },{ Z_SUB(z,string); },{});
    #endif
    pushSTACK(string);
  }
 #ifdef LOGICAL_PATHNAMES
  if (parse_logical) {
    pushSTACK(allocate_logpathname());
    # stack layout: ..., data-vector, pathname.
    var uintL remaining = parse_logical_pathnamestring(z);
    z.index += z.count-remaining; z.FNindex = fixnum_inc(z.FNindex,z.count-remaining); z.count = remaining;
  } else
 #endif
  {
   #ifdef PATHNAME_RISCOS
    # If the string starts with a system variable in <...> syntax,
    # then perform the substitution
    # (string-concat "<" var ">" tail) -->
    # (string-concat (sys::getenv var) tail).
    if ((z.count != 0)
        && chareq(TheSstring(STACK_0)->data[z.index],ascii('<'))) {
      var zustand startz = z; # Start-Zustand
      var chart ch;
      # skip character '<' :
      Z_SHIFT(z,1);
      loop {
        if (z.count==0)
          goto no_envvar;
        ch = TheSstring(STACK_0)->data[z.index]; # next character
        if (chareq(ch,ascii('>')))
          break;
        if (!(graphic_char_p(ch) && !chareq(ch,ascii('*'))
              && !chareq(ch,ascii('#'))))
          goto no_envvar;
        # skip valid character:
        Z_SHIFT(z,1);
      }
      FNindex_fallback = z.FNindex;
      # skip character '>' :
      Z_SHIFT(z,1);
      # build environment-variable as Simple-String:
      if (z.index - startz.index - 2 == 0)
        goto no_envvar;
      {
        var object envvar = subsstring(STACK_0,startz.index+1,z.index-1);
        # fetch its value:
        with_sstring_0(envvar,O(misc_encoding),envvar_asciz, {
          begin_system_call();
          var const char* envval = getenv(envvar_asciz);
          end_system_call();
          if (envval==NULL) {
            pushSTACK(envvar);
            pushSTACK(S(parse_namestring));
            fehler(parse_error,
                   GETTEXT("~: there is no environment variable ~"));
          }
          pushSTACK(asciz_to_string(envval,O(misc_encoding))); # value of the variable as String
        });
      }
      # build rest-piece:
      pushSTACK(subsstring(STACK_1,z.index,z.index+z.count));
      { /* merge both, replace thing: */
        var uintL envval_len = Sstring_length(STACK_1);
        var object new_thing = string_concat(2);
        STACK_(4+1) = STACK_0 = new_thing;
        # the 2. value FNindex must still be modified later.
        FNindex_limit = fixnum(envval_len);
        FNindex_offset = (sintL)posfixnum_to_L(z.FNindex) - (sintL)envval_len;
        z.index = 0; z.count = Sstring_length(new_thing); z.FNindex = Fixnum_0;
      }
      goto envvar_ok;
    no_envvar: # no environment-variable
      z = startz; # go back to the start
    }
    envvar_ok: ;
   #endif
    pushSTACK(allocate_pathname());
    # stack layout: ..., data-vector, pathname.
    # separator between subdirs is on MSDOS both '\' and '/':
   #if HAS_HOST
    { # parse Host-Specification:
      var object host;
      {
        var zustand startz = z; # start-state
        var chart ch;
       #if defined(PATHNAME_RISCOS)
        # Is it a sequence of characters, embedded in '-',
        # or a sequence of characters and then a ':' ?
        if (z.count==0) goto no_hostspec; # string already through -> no host
        ch = TheSstring(STACK_1)->data[z.index]; # next character
        if (chareq(ch,ascii('-'))) {
          # skip '-' :
          Z_SHIFT(z,1);
          loop {
            if (z.count==0)
              goto no_hostspec; # string already through -> no host
            ch = TheSstring(STACK_1)->data[z.index]; # next character
            if (chareq(ch,ascii('-')))
              break;
            if (!legal_hostchar(ch))
              goto no_hostspec;
            # skip valid character:
            Z_SHIFT(z,1);
          }
          # build host-string:
          if (z.index - startz.index - 1 == 0)
            goto no_hostspec;
          host = subsstring(STACK_1,startz.index+1,z.index);
        } else {
          loop {
            if (!legal_hostchar(ch))
              goto no_hostspec;
            # skip valid character:
            Z_SHIFT(z,1);
            if (z.count==0)
              goto no_hostspec; # string already through -> no host
            ch = TheSstring(STACK_1)->data[z.index]; # next character
            if (colonp(ch))
              break;
          }
          # build host-string:
          host = subsstring(STACK_1,startz.index,z.index);
        }
        # skip character '-' resp. ':' :
        Z_SHIFT(z,1);
        goto hostspec_ok;
       #elif defined(PATHNAME_WIN32)
        # Look for two slashes, then a sequence of characters.
        if (z.count==0) goto no_hostspec;
        ch = TheSstring(STACK_1)->data[z.index];
        if (!pslashp(ch)) goto no_hostspec;
        Z_SHIFT(z,1);
        if (z.count==0) goto no_hostspec;
        ch = TheSstring(STACK_1)->data[z.index];
        if (!pslashp(ch)) goto no_hostspec;
        Z_SHIFT(z,1);
        while (z.count) {
          ch = TheSstring(STACK_1)->data[z.index];
          if (!legal_hostchar(ch))
            break;
          # Skip past valid host char.
          Z_SHIFT(z,1);
        }
        # Create host string.
        if (z.index - startz.index - 2 == 0)
          goto no_hostspec;
        host = subsstring(STACK_1,startz.index+2,z.index);
        # Note: The next character in the string is not a letter or '*';
        # therefore the device of the resulting pathname will be NIL.
        goto hostspec_ok;
       #else
        # is it a sequence of alphanumeric characters and then a ':' resp. '::' ?
        loop {
          if (z.count==0)
            goto no_hostspec; # string already through -> no Host
          ch = TheSstring(STACK_1)->data[z.index]; # next character
          if (!alphanumericp(ch))
            break;
          # skip alphanumeric character:
          Z_SHIFT(z,1);
        }
        if (!colonp(ch))
          goto no_hostspec; # no ':' -> no host
        # build host-string:
        host = subsstring(STACK_1,startz.index,z.index);
        # skip character ':' :
        Z_SHIFT(z,1);
        goto hostspec_ok;
       #endif
      no_hostspec: # no host-specification
        z = startz; # back to start
        host = STACK_(3+2); # Default-Host
      }
    hostspec_ok: # enter host:
      ThePathname(STACK_0)->pathname_host = host;
    }
   #endif /* HAS_HOST */
   #if HAS_DEVICE
    #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
    { # parse one-letter Device-Specification:
      var object device = NIL; # Device := NIL
      # parse Drive-Specification:
      # Is there a letter ('*','A'-'Z','a'-'z') and then a ':' ?
      {
        var zustand startz = z; # start-state
        var chart ch;
        if (z.count==0)
          goto no_drivespec; # string already through ?
        ch = TheSstring(STACK_1)->data[z.index]; # next character
        ch = up_case(ch); # as capital letter
        if (chareq(ch,ascii('*'))) {
          # ch = '*' -> Device := :WILD
          device = S(Kwild);
        } else if ((as_cint(ch) >= 'A') && (as_cint(ch) <= 'Z')) {
          # 'A' <= ch <= 'Z' -> Device := "ch"
          var object string = allocate_string(1); # String of length 1
          TheSstring(string)->data[0] = ch; # with ch as sole letter
          device = string;
        } else
          goto no_device;
        # Device OK, skip character:
        Z_SHIFT(z,1);
        if (z.count==0)
          goto no_drivespec; # string already through ?
        ch = TheSstring(STACK_1)->data[z.index]; # next character
        ch = up_case(ch); # as capital letter
      no_device:
        # concluded with colon?
        if (!colonp(ch))
          goto no_drivespec;
        # skip character:
        Z_SHIFT(z,1);
        goto drivespec_ok;
      no_drivespec:
        # parsing a Drive-Specification did not succeed.
        z = startz; # restore start-state
        device = NIL; # Device := NIL
      }
    drivespec_ok: # enter Device
      ThePathname(STACK_0)->pathname_device = device;
    }
    #endif /* PATHNAME_OS2 || PATHNAME_WIN32 */
    #ifdef PATHNAME_AMIGAOS
    { # parse Device-Specification:
      var object device;
      # Is it a non-empty sequence of alphanumeric characters and then a ':'?
      {
        var zustand startz = z; # start-state
        var chart ch;
        loop {
          if (z.count==0)
            goto no_devicespec; # string already through -> no Device
          ch = TheSstring(STACK_1)->data[z.index]; # next character
          if (!legal_namechar(ch))
            break;
          # skip alphanumeric character:
          Z_SHIFT(z,1);
        }
        if (!colonp(ch))
          goto no_devicespec; # no ':' -> no Device
        if (z.index==startz.index)
          goto no_devicespec; # ':' at the start is no Device
        # build Device-String:
        device = subsstring(STACK_1,startz.index,z.index);
        # do not skip character ':' ; it will then result in :ABSOLUTE.
        goto devicespec_ok;
      no_devicespec: # no Device-Specification
        z = startz; # back to the start
        device = NIL; # Device NIL
      }
    devicespec_ok: # enter Device:
      ThePathname(STACK_0)->pathname_device = device;
    }
   #endif /* PATHNAME_AMIGAOS */
   #ifdef PATHNAME_RISCOS
    { # parse Device-Specification:
      var object device;
      # Is there a ':', a non-empty sequence of characters and then a '.' ?
      {
        var zustand startz = z; # start-state
        var chart ch;
        if (!Z_AT_SLASH(z,colonp,STACK_1))
          goto no_devicespec;
        # skip character ':' :
        Z_SHIFT(z,1);
        loop {
          if (z.count==0)
            goto no_devicespec; # string already through -> no Device
          ch = TheSstring(STACK_1)->data[z.index]; # next character
          if (!(legal_namechar(ch) && !wild_char_p(ch)))
            break;
          # skip valid character:
          Z_SHIFT(z,1);
        }
        if (!chareq(ch,ascii('.')))
          goto no_devicespec; # no '.' -> no Device
        # build Device-String:
        if (z.index - startz.index - 1 == 0)
          goto no_devicespec;
        device = subsstring(STACK_1,startz.index+1,z.index);
        # skip character '.' :
        Z_SHIFT(z,1);
        goto devicespec_ok;
      no_devicespec: # no Device-Specification
        z = startz; # back to the start
        device = NIL; # Device NIL
      }
    devicespec_ok: # enter Device:
      ThePathname(STACK_0)->pathname_device = device;
    }
    #endif /* PATHNAME_RISCOS */
   #endif /* HAS_DEVICE */
    # enter Directory-Start:
    {
      var object new_cons = allocate_cons(); # new Cons for Startpoint
      ThePathname(STACK_0)->pathname_directory = new_cons;
      pushSTACK(new_cons); # new (last (pathname-directory Pathname))
    }
    # stack layout:
    # ..., Datenvektor, Pathname, (last (pathname-directory Pathname)).
    # parse subdirectories:
    {
     #if defined(USER_HOMEDIR) && defined(PATHNAME_UNIX)
      # if there is a '~' immediately, a username is read up to the next '/'
      # or string-end and the Home-Directory of this user is inserted:
      if ((z.count != 0) && chareq(schar(STACK_2,z.index),ascii('~'))) {
        # there is a '~' immediately.
        # skip character:
        Z_SHIFT(z,1);
        var object userhomedir; # Pathname of the User-Homedir
        # search next '/' :
        var uintL charcount = 0;
        SstringDispatch(STACK_2,X, {
          var const cintX* charptr =
            &((SstringX)TheVarobject(STACK_2))->data[z.index];
          var uintL count;
          dotimesL(count,z.count, {
            if (*charptr++ == '/') break;
            charcount++;
          });
        });
        # Username has charcount characters
        if (charcount==0) {
          userhomedir = O(user_homedir); # only '~' -> User-Homedir
        } else { # build username:
          var object username =
            subsstring(STACK_2,z.index,z.index+charcount);
          # fetch his/her Home-Directory from the password-file:
          with_sstring_0(username,O(misc_encoding),username_asciz, {
            begin_system_call();
            errno = 0;
            var struct passwd * userpasswd = getpwnam(username_asciz);
            if (userpasswd == (struct passwd *)NULL) { # unsuccessful?
              if (!(errno==0)) { OS_error(); } # report error
              end_system_call();
              # else: error
              pushSTACK(username);
              pushSTACK(S(parse_namestring));
              fehler(parse_error,GETTEXT("~: there is no user named ~"));
            }
            end_system_call();
            userhomedir = # homedir as pathname
              asciz_dir_to_pathname(userpasswd->pw_dir,O(misc_encoding));
          });
        }
        # copy directory from the pathname userhomedir:
        # (copy-list dir) = (nreconc (reverse dir) nil),
        # after it memorize its last Cons.
        userhomedir = reverse(ThePathname(userhomedir)->pathname_directory);
        userhomedir = nreconc(userhomedir,NIL);
        ThePathname(STACK_1)->pathname_directory = userhomedir;
        while (mconsp(Cdr(userhomedir))) { userhomedir = Cdr(userhomedir); }
        STACK_0 = userhomedir;
        # skip username-characters:
        Z_SHIFT(z,charcount);
        # if the string is through: finished,
        # otherwise a '/' follows immediately , it will be skipped:
        if (z.count==0) { # Name and Type := NIL
          pushSTACK(NIL); pushSTACK(NIL); goto after_name_type;
        }
        # skip character:
        Z_SHIFT(z,1);
      } else
     #endif /* USER_HOMEDIR & PATHNAME_UNIX */
     #if defined(PATHNAME_UNIX) && 0
        # What is this needed for, except for $HOME ?
        # If a '$' follows immediately, an Environment-Variable is read up
        # to the next '/' or string-end and its value is inserted:
        if ((z.count != 0)
            && chareq(TheSstring(STACK_2)->data[z.index],ascii('$'))) {
          # A '$' follows immediately.
          # skip character:
          Z_SHIFT(z,1);
          var object envval_dir;
          # search next '/' :
          var uintL charcount = 0;
          {
            var const chart* charptr = &TheSstring(STACK_2)->data[z.index];
            var uintL count;
            dotimesL(count,z.count, {
              if (chareq(*charptr++,ascii('/')))
                break;
              charcount++;
            });
          }
          { # Environment-Variable has charcount characters.
            var object envvar =
              subsstring(STACK_2,z.index,z.index+charcount);
            # fetch its value:
            with_sstring_0(envvar,O(misc_encoding),envvar_asciz, {
              begin_system_call();
              var const char* envval = getenv(envvar_asciz);
              end_system_call();
              if (envval==NULL) {
                pushSTACK(envvar);
                pushSTACK(S(parse_namestring));
                fehler(parse_error,
                       GETTEXT("~: there is no environment variable ~"));
              }
              envval_dir = # value of the variable as pathname
                asciz_dir_to_pathname(envval,O(misc_encoding));
            });
          }
          # copy directory from the pathname envval_dir:
          # (copy-list dir) = (nreconc (reverse dir) nil),
          # afterwards memorize its last Cons.
          envval_dir = reverse(ThePathname(envval_dir)->pathname_directory);
          envval_dir = nreconc(envval_dir,NIL);
          ThePathname(STACK_1)->pathname_directory = envval_dir;
          while (mconsp(Cdr(envval_dir))) { envval_dir = Cdr(envval_dir); }
          STACK_0 = envval_dir;
          # skip envvar-characters:
          Z_SHIFT(z,charcount);
          # if the string is through: finished,
          # otherwise a '/' follows immediately , it will be skipped:
          if (z.count==0) { # Name and Type := NIL
            pushSTACK(NIL); pushSTACK(NIL); goto after_name_type;
          }
          # skip character:
          Z_SHIFT(z,1);
        } else
     #endif /* PATHNAME_UNIX & 0 */
     #if defined(PATHNAME_UNIX) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
      #if defined(UNIX_CYGWIN32)
        if (z.count > 1 && !nullpSv(device_prefix)
            && chareq(schar(STACK_2,z.index+1),ascii(':'))) {
          /* if string starts with 'x:', treat it as a device */
          var chart ch = down_case(schar(STACK_2,z.index));
          if ((as_cint(ch) >= 'a') && (as_cint(ch) <= 'z')) {
            Car(STACK_0) = allocate_string(1);
            TheSstring(Car(STACK_0))->data[0] = ch;
            Z_SHIFT(z,2);
            if (Z_AT_SLASH(z,pslashp,STACK_2)) Z_SHIFT(z,1);
          } else goto continue_parsing_despite_semicolon;
        } else
        continue_parsing_despite_semicolon:
      #endif
        # if 1st char is a slash, start with :ABSOLUTE (otherwise :RELATIVE):
        if (Z_AT_SLASH(z,pslashp,STACK_2)) {
          Z_SHIFT(z,1);
          Car(STACK_0) = S(Kabsolute);
        } else {
          Car(STACK_0) = S(Krelative);
        }
     #endif
     #ifdef PATHNAME_AMIGAOS
      # if 1st char is a ':', start with :ABSOLUTE (otherwise :RELATIVE):
      if (Z_AT_SLASH(z,colonp,STACK_2)) {
        Z_SHIFT(z,1);
        Car(STACK_0) = S(Kabsolute);
      } else {
        Car(STACK_0) = S(Krelative);
      }
     #endif
     #ifdef PATHNAME_RISCOS
      # parse prefix '$.' or '&.' or '@.' or '%.' or '\.' .
      if ((z.count >= 2)
          && chareq(TheSstring(STACK_2)->data[z.index+1],ascii('.'))) {
        switch (as_cint(TheSstring(STACK_2)->data[z.index])) {
          case '$': # directory = (:ABSOLUTE :ROOT)
            Car(STACK_0) = S(Kroot); break;
          case '&': # directory = (:ABSOLUTE :HOME)
            Car(STACK_0) = S(Khome); break;
          case '@': # directory = (:ABSOLUTE :CURRENT)
            Car(STACK_0) = S(Kcurrent); break;
          case '%': # directory = (:ABSOLUTE :LIBRARY)
            Car(STACK_0) = S(Klibrary); break;
          case '\\':  # directory = (:ABSOLUTE :PREVIOUS)
            Car(STACK_0) = S(Kprevious); break;
          default: goto prefix_relative;
        }
        # skip prefix:
        Z_SHIFT(z,2);
        # lengthen (pathname-directory pathname) by a Cons (:ABSOLUTE) :
        var object new_cons = allocate_cons(); # new Cons
        Car(new_cons) = S(Kabsolute); Cdr(new_cons) = STACK_0;
        ThePathname(STACK_1)->pathname_directory = new_cons;
      } else {
      prefix_relative:
        Car(STACK_0) = S(Krelative); # directory = (:RELATIVE)
      }
     #endif
     #if !defined(PATHNAME_RISCOS)
      loop {
        # try to parse another subdirectory.
       #ifdef PATHNAME_NOEXT
        {
          var uintL z_start_index = z.index; # index at the start
          loop {
            var chart ch;
            if (z.count == 0)
              break;
            ch = schar(STACK_2,z.index); # next character
            if (!legal_namechar(ch)) # valid character ?
              break;
            # yes -> part of the name
            # skip character:
            Z_SHIFT(z,1);
          }
          # reached end of the name.
          # Name := substring of STACK_2 from z_start_index (inclusive)
          #                                to z.index (exclusive).
          var object string = subsstring(STACK_2,z_start_index,z.index);
          # name finished.
          pushSTACK(string);
        }
        # if a '/' resp. '\' follows immediately, then it was a subdirectory,
        # else the pathname is finished:
        if (!Z_AT_SLASH(z,pslashp,STACK_3))
          # no -> it was the name and no subdir.
          break;
        # a '/' resp. '\' follows. skip character:
        Z_SHIFT(z,1);
        # stack layout: ...,
        #   data-vector, pathname, (last (pathname-directory Pathname)),
        #   subdir.
        #ifdef PATHNAME_AMIGAOS
        # was it '' ?
        if (equal(STACK_0,O(empty_string))) {
          STACK_0 = S(Kparent); # replace with :PARENT
        } else
        #endif
          # was it '**' or '...' ?
          if (equal(STACK_0,O(wildwild_string))
              || equal(STACK_0,O(dotdotdot_string))) {
            STACK_0 = S(Kwild_inferiors); # replace with :WILD-INFERIORS
          }
       #endif /* PATHNAME_NOEXT */
        # lengthen (pathname-directory pathname) by subdir STACK_0:
        var object new_cons = allocate_cons(); # new Cons
        Car(new_cons) = popSTACK(); # = (cons subdir NIL)
        Cdr(STACK_0) = new_cons; # lengthened (pathname-directory Pathname)
        STACK_0 = new_cons; # new (last (pathname-directory Pathname))
      }
     #else # defined(PATHNAME_RISCOS)
      pushSTACK(unbound); # maybe-name
      # stack layout: ..., data-vector, pathname,
      #             (last (pathname-directory Pathname)), maybe-name.
      loop {
        # Try to parse another subdirectory.
        # Maybe-Name = the last read component in
        # { { legal-wild char }+ | empty } '.'  Syntax.
        # If it is another subdir or the name, will only be decided
        # later.
        # is there a '^.' ?
        if (!nullp(STACK_0)
            && (z.count >= 2)
            && chareq(TheSstring(STACK_3)->data[z.index],ascii('^'))
            && pslashp(TheSstring(STACK_3)->data[z.index+1])) {
          # skip both characters:
          Z_SHIFT(z,2);
          pushSTACK(S(Kparent)); # :PARENT
        } else {
          # Try to parse the normal  { legal-wild char }+  Syntax:
          var uintL z_start_index = z.index; # index at the start of the name
          loop {
            var chart ch;
            if (z.count == 0)
              break;
            ch = TheSstring(STACK_3)->data[z.index]; # next character
            if (!legal_namechar(ch)) # valid character ?
              break;
            # yes -> part of the name
            # skip character:
            Z_SHIFT(z,1);
          }
          # reached end of the name.
          # Name := substring of STACK_3 from z_start_index (inclusive)
          #                                to z.index (exclusive).
          var object string;
          if (z.index - z_start_index == 0)
            string = NIL; # "" will become NIL
          else
            string = subsstring(STACK_3,z_start_index,z.index);
          # Name finished.
          if (nullp(STACK_0) || (!Z_AT_SLASH(z,pslashp,STACK_3))) {
            pushSTACK(string); break;
          }
          # skip character '.' :
          Z_SHIFT(z,1);
          pushSTACK(string);
        }
        if (boundp(STACK_1)) {
          # lengthen (pathname-directory pathname) by subdir STACK_1:
          var object new_cons = allocate_cons(); # new Cons
          Car(new_cons) = STACK_1; # = (cons subdir NIL)
          Cdr(STACK_2) = new_cons; # lengthens (pathname-directory Pathname)
          STACK_2 = new_cons; # new (last (pathname-directory Pathname))
        }
        STACK_1 = STACK_0; skipSTACK(1); # maybe-name := subdir
      }
      if (!boundp(STACK_1)) {
        STACK_1 = STACK_0; STACK_0 = NIL;
      }
      # stack layout: ..., data-vector, pathname,
      #              (last (pathname-directory Pathname)), name, type.
      # In certain cases the Directory-Specification does not stop after the
      # second last dot, but after the last dot:
      else if (eq(STACK_1,S(Kparent)) # e.g. "bar.^.foo"
               || (nullp(STACK_0) && !nullp(STACK_1))) { # e.g. "foo.bar."
        # lengthen (pathname-directory pathname) by subdir STACK_1:
        var object new_cons = allocate_cons(); # new Cons
        Car(new_cons) = STACK_1; # = (cons subdir NIL)
        Cdr(STACK_2) = new_cons; # lengthens (pathname-directory Pathname)
        STACK_2 = new_cons; # new (last (pathname-directory Pathname))
        STACK_1 = STACK_0; # name := type
        STACK_0 = NIL;     # type := NIL
      }
     #endif /* PATHNAME_RISCOS */
     #if defined(PATHNAME_RISCOS)
      # stack layout: ...,
      #   data-vector, pathname, (last (pathname-directory Pathname)),
      #   name, type.
      { # enter name and type in pathname:
        var object type = popSTACK();
        var object name = popSTACK();
        skipSTACK(1); # directory is already entered
        var object pathname = STACK_0;
        ThePathname(pathname)->pathname_name = name;
        ThePathname(pathname)->pathname_type = type;
      }
     #endif
     #ifdef PATHNAME_NOEXT
      # stack layout: ..., data-vector, pathname,
      #             (last (pathname-directory Pathname)), string.
      split_name_type(0); # split string STACK_0 in name and type
    after_name_type:
      # stack layout: ..., data-vector, pathname,
      #             (last (pathname-directory Pathname)), name, type.
      { # enter name and type in pathname:
        var object type = popSTACK();
        var object name = popSTACK();
        skipSTACK(1); # directory is already entered
        # replace name="" with name=NIL:
        if (equal(name,O(empty_string)))
          name = NIL;
        var object pathname = STACK_0;
        ThePathname(pathname)->pathname_name = name;
        ThePathname(pathname)->pathname_type = type;
      }
     #endif
     #ifdef WIN32_NATIVE
      var object pathname = STACK_0;
      var object dir = ThePathname(pathname)->pathname_directory;
      var object dev = Symbol_value(S(device_prefix));
      if (nullp(ThePathname(pathname)->pathname_device)
          # actually, we already know that dir is a cons
          && consp(dir) && eq(Car(dir),S(Kabsolute))
          # Cdr(dir) might not be a cons, e.g., "/foo" ==
          # #S(pathname :directory (:absolute) :name "foo")
          && consp(Cdr(dir)) && consp(Cdr(Cdr(dir)))
          && stringp(dev)
          && string_eqcomp_ci(Car(Cdr(dir)),0,dev,0,vector_length(dev))) {
        # path = (:ABSOLUTE "cygdrive" "drive" "dir1" ...) ===>
          # path = (:ABSOLUTE "dir1" ...); device = "DRIVE"
        var object device = Car(Cdr(Cdr(dir)));
        Cdr(dir) = Cdr(Cdr(Cdr(dir)));
        device = string_upcase(device);
        ThePathname(STACK_0)->pathname_device = device;
      }
     #endif
     #ifdef UNIX_CYGWIN32
      var object dir = ThePathname(STACK_0)->pathname_directory;
      if (consp(dir) && stringp(Car(dir))) {
        /* dir = ("c" ...) --> (:absolute *device-prefix* "c" ...)*/
        pushSTACK(S(Kabsolute));
        pushSTACK(Symbol_value(S(device_prefix)));
        dir = listof(2);
        Cdr(Cdr(dir)) = ThePathname(STACK_0)->pathname_directory;
        ThePathname(STACK_0)->pathname_directory = dir;
      }
     #endif
      ThePathname(STACK_0)->pathname_directory =
        simplify_directory(ThePathname(STACK_0)->pathname_directory);
    }
  }
  # Pathname is finished.
  # stack layout: ..., data-vector, pathname.
  if (!junk_allowed)
    # Check whether no more characters remain
    if (!(z.count == 0)) {
      pushSTACK(z.FNindex); # last index
      pushSTACK(STACK_(4+2+1)); # thing
      pushSTACK(S(parse_namestring));
      fehler(parse_error,
             GETTEXT("~: syntax error in filename ~ at position ~"));
    }
 #if HAS_HOST || defined(LOGICAL_PATHNAMES)
  # Check that if a :host argument (or :host component of the :defaults
  # argument) was present and the parsed pathname has a host component,
  # they agree; and set the :host component of the result otherwise
  if (!missingp(STACK_(3+2))) {
   #ifdef LOGICAL_PATHNAMES
    if (parse_logical) {
      var object parsed_host = TheLogpathname(STACK_0)->pathname_host;
      if (!nullp(parsed_host)) {
        if (!equal(STACK_(3+2),parsed_host)) {
          pushSTACK(STACK_0);
          pushSTACK(parsed_host);
          pushSTACK(STACK_(3+2+2));
          pushSTACK(S(parse_namestring));
          fehler(error,GETTEXT("~: hosts ~ and ~ of ~ should coincide"));
        }
      } else
        TheLogpathname(STACK_0)->pathname_host = STACK_(3+2);
    } else
   #endif
    {
     #if HAS_HOST
      var object parsed_host = ThePathname(STACK_0)->pathname_host;
      if (!nullp(parsed_host)) {
        if (!equal(STACK_(3+2),parsed_host)) {
          pushSTACK(STACK_0);
          pushSTACK(parsed_host);
          pushSTACK(STACK_(3+2+2));
          pushSTACK(S(parse_namestring));
          fehler(error,GETTEXT("~: hosts ~ and ~ of ~ should coincide"));
        }
      } else
        ThePathname(STACK_0)->pathname_host = STACK_(3+2);
     #endif
    }
  }
 #endif /* HAS_HOST || LOGICAL_PATHNAMES */
  value1 = STACK_0; # pathname as 1. value
 #ifdef PATHNAME_RISCOS
  if (as_oint(z.FNindex) >= as_oint(FNindex_limit)) {
    # transfrom FNindex from new_thing to thing:
    value2 = fixnum_inc(z.FNindex,FNindex_offset);
  } else {
    # FNindex points into the replaced (!) String envval. What else
    # remains for us as index other than the start-index?
    # (not quite correct, sure enough: If the parsing really stopped
    # there, value1 would look different!)
    # For example an index into the inside of the <...>-construct.
    # (This is not all correct, but comes closer.)
    value2 = FNindex_fallback;
  }
 #else
  value2 = z.FNindex; # index as 2. value
 #endif
  mv_count=2; # 2 values
  DOUT("parse-namestring:[end ret]",value1);
  skipSTACK(5+2); return;
}
#undef colonp
#undef Z_SUB
#undef Z_AT_SLASH
#undef Z_SHIFT

# UP: Converts an object into a pathname.
# coerce_xpathname(object)
# > object: object
# < result: (PATHNAME Objekt)
# can trigger GC
local object coerce_xpathname (object obj) {
  if (xpathnamep(obj)) {
    # nothing to do for pathnames.
    return obj;
  } else {
    # else: call PARSE-NAMESTRING:
    pushSTACK(obj); funcall(L(parse_namestring),1);
    return value1;
  }
}

LISPFUNNR(pathname,1) { /* (PATHNAME pathname), CLTL p. 413 */
  VALUES1(coerce_xpathname(popSTACK()));
}

# (PATHNAME-HOST pathname [:case]), CLTL p. 417, CLtL2 p. 644
LISPFUN(pathnamehost,seclass_read,1,0,norest,key,1, (kw(case))) {
  var object pathname = coerce_xpathname(STACK_1);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    VALUES1(TheLogpathname(pathname)->pathname_host);
  } else
 #endif
  {
   #if HAS_HOST
    var object erg = ThePathname(pathname)->pathname_host;
    VALUES1(eq(STACK_0,S(Kcommon)) ? common_case(erg) : erg); /* host as value */
   #else
    VALUES1(NIL);
   #endif
  }
  skipSTACK(2);
}

# (PATHNAME-DEVICE pathname [:case]), CLTL p. 417, CLtL2 p. 644
LISPFUN(pathnamedevice,seclass_read,1,0,norest,key,1, (kw(case))) {
  var object pathname = coerce_xpathname(STACK_1);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    VALUES1(NIL);
  } else
 #endif
  {
   #if HAS_DEVICE
    var object erg = ThePathname(pathname)->pathname_device; # device as value
    VALUES1(eq(STACK_0,S(Kcommon)) ? common_case(erg) : erg);
   #else
    VALUES1(NIL);
   #endif
  }
  skipSTACK(2);
}

# (PATHNAME-DIRECTORY pathname [:case]), CLTL p. 417, CLtL2 p. 644
LISPFUN(pathnamedirectory,seclass_read,1,0,norest,key,1, (kw(case))) {
  var object pathname = coerce_xpathname(STACK_1);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    VALUES1(TheLogpathname(pathname)->pathname_directory);
  } else
 #endif
  {
    var object erg = ThePathname(pathname)->pathname_directory;
    VALUES1(eq(STACK_0,S(Kcommon)) ? subst_common_case(erg) : erg);
  }
  skipSTACK(2);
}

# (PATHNAME-NAME pathname [:case]), CLTL p. 417, CLtL2 p. 644
LISPFUN(pathnamename,seclass_read,1,0,norest,key,1, (kw(case))) {
  var object pathname = coerce_xpathname(STACK_1);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    value1 = TheLogpathname(pathname)->pathname_name;
  } else
 #endif
  {
    var object erg = ThePathname(pathname)->pathname_name;
    value1 = (eq(STACK_0,S(Kcommon)) ? common_case(erg) : erg);
  }
  mv_count=1; # name as value
  skipSTACK(2);
}

# (PATHNAME-TYPE pathname [:case]), CLTL p. 417, CLtL2 p. 644
LISPFUN(pathnametype,seclass_read,1,0,norest,key,1, (kw(case))) {
  var object pathname = coerce_xpathname(STACK_1);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    value1 = TheLogpathname(pathname)->pathname_type;
  } else
 #endif
  {
    var object erg = ThePathname(pathname)->pathname_type;
    value1 = (eq(STACK_0,S(Kcommon)) ? common_case(erg) : erg);
  }
  mv_count=1; # type as value
  skipSTACK(2);
}

# (PATHNAME-VERSION pathname), CLTL p. 417, CLtL2 p. 644
LISPFUNNR(pathnameversion,1) {
  var object pathname = coerce_xpathname(popSTACK());
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    value1 = TheLogpathname(pathname)->pathname_version;
  } else
 #endif
    value1 = pathname_version_maybe(pathname); # version as value
  mv_count=1;
}

#ifdef LOGICAL_PATHNAMES

local object parse_as_logical (object obj) {
  # the value of (PARSE-NAMESTRING obj nil empty-logical-pathname)
  # is always a logical pathname.
  pushSTACK(obj); pushSTACK(NIL);
  pushSTACK(O(empty_logical_pathname));
  funcall(L(parse_namestring),3);
  return value1;
}

LISPFUNNR(logical_pathname,1)
{ /* (LOGICAL-PATHNAME thing), CLtL2 p. 631 */
  var object thing = popSTACK();
  if (logpathnamep(thing)) {
    # nothing to do for logical pathnames.
    VALUES1(thing);
  } else if (pathnamep(thing)) {
    # normal pathnames cannot be converted into logical pathnames.
    pushSTACK(thing);                    # TYPE-ERROR slot DATUM
    pushSTACK(O(type_logical_pathname)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(thing);
    pushSTACK(S(logical_pathname));
    fehler(type_error,GETTEXT("~: argument ~ is not a logical pathname, string, stream or symbol"));
  } else {
    VALUES1(parse_as_logical(thing));
  }
}

# (TRANSLATE-LOGICAL-PATHNAME pathname &key), CLtL2 p. 631
LISPFUN(translate_logical_pathname,seclass_default,1,0,norest,key,0,_EMA_) {
  var object pathname;
  # It is not clear from the ANSI CL spec how the argument shall be coerced
  # to a pathname. But the examples in the spec indicate that if the
  # argument is a string, it should be converted to a logical pathname,
  # by calling LOGICAL-PATHNAME, not by calling PATHNAME.
  if (stringp(STACK_0)) {
    funcall(L(logical_pathname),1); pathname = value1;
  } else {
    pathname = coerce_xpathname(popSTACK());
  }
  if (logpathnamep(pathname)) {
    # Conversion of a logical into a normal pathname:
    # (let ((ht (make-hash-table :test #'equal)))
    #   (loop
    #     (when (gethash pathname ht) (error "Translation loop"))
    #     (setf (gethash pathname ht) t)
    #     (let ((host (or (pathname-host pathname) "SYS")))
    #       (unless (logical-host-p host) (error "No translation for host"))
    #       (let* ((translations (gethash host sys::*logical-pathname-translations*))
    #              (translation (assoc pathname translations :test #'pathname-match-p)))
    #         (unless (and translation (consp translation) (consp (cdr translation)))
    #           (error "No translation for pathname")
    #         )
    #         (setq pathname (translate-pathname pathname (first translation) (second translation)))
    #     ) )
    #     (unless (sys::logical-pathname-p pathname) (return))
    #   )
    #   pathname
    # )
    pushSTACK(pathname);
    DOUT("translate-logical-pathname: <",pathname);
    pushSTACK(S(Ktest)); pushSTACK(L(equal)); funcall(L(make_hash_table),2);
    pushSTACK(value1);
    # stack layout: pathname, ht.
    loop {
      if (!nullp(shifthash(STACK_0,STACK_1,T))) {
        # STACK_1 = pathname; # FILE-ERROR slot PATHNAME
        STACK_0 = STACK_1;
        pushSTACK(S(translate_logical_pathname));
        fehler(file_error,GETTEXT("~: endless loop while resolving ~"));
      }
      if (nullp(TheLogpathname(STACK_1)->pathname_host)) {
        # replace host NIL with default-host:
        var object newp = allocate_logpathname();
        var object oldp = STACK_1;
        TheLogpathname(newp)->pathname_host
          = O(default_logical_pathname_host); # Default "SYS"
        TheLogpathname(newp)->pathname_directory
          = TheLogpathname(oldp)->pathname_directory;
        TheLogpathname(newp)->pathname_name
          = TheLogpathname(oldp)->pathname_name;
        TheLogpathname(newp)->pathname_type
          = TheLogpathname(oldp)->pathname_type;
        TheLogpathname(newp)->pathname_version
          = TheLogpathname(oldp)->pathname_version;
        STACK_1 = newp;
      }
      var object host = TheLogpathname(STACK_1)->pathname_host;
      DOUT("translate-logical-pathname:",host);
      var object translations
        = gethash(host,Symbol_value(S(logpathname_translations)));
      if (eq(translations,nullobj)) {
        # STACK_1 = pathname; # FILE-ERROR slot PATHNAME
        STACK_0 = STACK_1;
        pushSTACK(host);
        pushSTACK(S(translate_logical_pathname));
        fehler(file_error,GETTEXT("~: unknown logical host ~ in ~"));
      }
      # (ASSOC pathname translations :test #'pathname-match-p):
      pushSTACK(STACK_1); pushSTACK(translations);
      DOUT("translate-logical-pathname:[path_name_s1]",STACK_1);
      DOUT("translate-logical-pathname:",translations);
      pushSTACK(S(Ktest)); pushSTACK(L(pathname_match_p));
      funcall(L(assoc),4);
      if (atomp(value1) || matomp(Cdr(value1))) {
        # STACK_1 = pathname; # FILE-ERROR slot PATHNAME
        STACK_0 = STACK_1;
        pushSTACK(S(translate_logical_pathname));
        fehler(file_error,GETTEXT("~: No replacement rule for ~ is known."));
      }
      # (TRANSLATE-PATHNAME pathname (first rule) (second rule) :MERGE NIL):
      pushSTACK(STACK_1); pushSTACK(Car(value1)); pushSTACK(Car(Cdr(value1)));
      pushSTACK(S(Kmerge)); pushSTACK(NIL);
      funcall(L(translate_pathname),5);
      STACK_1 = pathname = value1;
      DOUT("translate-logical-pathname:",pathname);
      if (!logpathnamep(pathname))
        break;
    }
    DOUT("translate-logical-pathname: >",pathname);
    skipSTACK(2);
  }
  VALUES1(pathname);
}

# UP: Change an object into a non-logical pathname.
# coerce_pathname(object)
# > object: object
# < return: (TRANSLATE-LOGICAL-PATHNAME (PATHNAME Objekt))
# can trigger GC
local object coerce_pathname (object obj) {
  obj = coerce_xpathname(obj);
  if (pathnamep(obj)) {
    return obj;
  } else if (logpathnamep(obj)) {
    # call TRANSLATE-LOGICAL-PATHNAME:
    pushSTACK(obj); funcall(L(translate_logical_pathname),1);
    return value1;
  } else
    NOTREACHED;
}

#endif

# UP: Pushes substrings for STRING_CONCAT on the STACK, that together yield
# the string for a subdirectory (car path) .
# subdir_namestring_parts(path,logicalp)
# > path: a Cons
# > logicalp: boolean
# < result: number of strings pushed on the stack
# changes STACK

#define SUBDIR_PUSHSTACK(subdir)                                         \
  do { if (eq(subdir,S(Kwild_inferiors))) pushSTACK(O(wildwild_string)); \
       else if (eq(subdir,S(Kwild))) pushSTACK(O(wild_string));          \
       else if (eq(subdir,S(Kup)) || eq(subdir,S(Kback)))                \
         pushSTACK(O(dotdot_string));                                    \
       else if (stringp(subdir)) pushSTACK(subdir);                      \
       else NOTREACHED;                                                  \
  } while(0)

local uintC subdir_namestring_parts (object path,bool logp) {
  var object subdir = Car(path);
 #if defined(LOGICAL_PATHNAMES) && (defined(PATHNAME_AMIGAOS) || defined(PATHNAME_RISCOS))
  if (logp) { # same as UNIX/Win32/OS2
    SUBDIR_PUSHSTACK(subdir); return 1;
  }
 #endif
 #ifdef PATHNAME_AMIGAOS
  if (eq(subdir,S(Kparent))) { # :PARENT ?
    return 0; # empty string
  } else { SUBDIR_PUSHSTACK(subdir); return 1; }
 #endif
 #if defined(PATHNAME_UNIX) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  SUBDIR_PUSHSTACK(subdir); return 1;
 #endif
 #ifdef PATHNAME_RISCOS
  if (eq(subdir,S(Kparent))) { # :PARENT ?
    pushSTACK(O(parent_string)); return 1;
  } else { SUBDIR_PUSHSTACK(subdir); return 1; }
 #endif
}

# UP: Pushes substrings for STRING_CONCAT on the STACK, that together yield
# the String for the host of the Pathname pathname.
# host_namestring_parts(pathname)
# > pathname: non-logical pathname
# < result: number of strings pushed on the stack
# changes STACK
#if HAS_HOST || defined(LOGICAL_PATHNAMES)
local uintC host_namestring_parts (object pathname) {
  var bool logp = logpathnamep(pathname);
  var object host = xpathname_host(logp,pathname);
  if (nullp(host)) {
    return 0; # no String
  } else {
   #ifdef PATHNAME_WIN32
    if (!logp) {
      pushSTACK(O(backslashbackslash_string));
      pushSTACK(host);
      return 2;
    }
   #endif
    pushSTACK(host);
    pushSTACK(O(colon_string)); # ":"
    return 2;
  }
}
#else
  #define host_namestring_parts(pathname)  (unused (pathname), 0)  # no strings
#endif

# UP: Pushes substrings for STRING_CONCAT on the STACK, that together yield the
# String for the Device and Directory of the Pathname pathname.
# directory_namestring_parts(pathname)
# > pathname: non-logical pathname
# < result: number of strings pushed on the stack
# changes STACK
local uintC directory_namestring_parts (object pathname) {
  var uintC stringcount = 0; # number of strings so far = 0
  var bool logp = logpathnamep(pathname);
 #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  { # Device:
    var object device = xpathname_device(logp,pathname);
    if (!(nullp(device))) { # NIL -> no string
      var object string = wild2string(device);
      pushSTACK(string);
      stringcount++; # and count
      pushSTACK(O(colon_string));
      stringcount++; # ":"
    }
  }
 #endif
 #if defined(PATHNAME_WIN32) || defined(PATHNAME_UNIX)
  if (stringcount == 0) /* only if there's no device already */
    /* no check for both host and device being present:
       this can never happen in CLISP */
    stringcount += host_namestring_parts(pathname);
 #endif
 #ifdef PATHNAME_AMIGAOS
  { # Device:
    var object device = xpathname_device(logp,pathname);
    if (!(nullp(device))) { # NIL -> no string
      pushSTACK(device); # Device on the stack
      stringcount += 1; # and count
      # Because of :ABSOLUTE there is a ":" immediately on the stack.
    }
  }
 #endif
 #ifdef PATHNAME_RISCOS
  { # Device:
    var object device = xpathname_device(logp,pathname);
    if (!(nullp(device))) { # NIL -> no string
      pushSTACK(O(colon_string)); # ":"
      pushSTACK(device); # Device on the stack
      pushSTACK(O(dot_string)); # "."
      stringcount += 3; # and count
    }
  }
 #endif
  { # Directory:
    var object directory = xpathname_directory(logp,pathname);
   #if defined(LOGICAL_PATHNAMES)
    if (logp) {
      if (eq(Car(directory),S(Krelative))) {
        pushSTACK(O(semicolon_string)); stringcount++; # ";" on the Stack
      }
    } else
   #endif
   {
    if (!mconsp(directory)) return stringcount; # just in case
    # is the first subdir = :ABSOLUTE or = :RELATIVE ?
    if (eq(Car(directory),S(Kabsolute))) {
     #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
      pushSTACK(O(backslash_string)); stringcount++; # "\\"
     #endif
     #ifdef PATHNAME_AMIGAOS
      pushSTACK(O(colon_string)); stringcount++; # ":"
     #endif
     #ifdef PATHNAME_UNIX
      pushSTACK(O(slash_string)); stringcount++; # "/"
     #endif
     #ifdef PATHNAME_RISCOS
      directory = Cdr(directory); # skip
      var object firstdir = Car(directory);
      if (eq(firstdir,S(Kroot))) {
        pushSTACK(O(root_string)); stringcount++; # "$."
      } else if (eq(firstdir,S(Khome))) {
        pushSTACK(O(home_string)); stringcount++; # "&."
      } else if (eq(firstdir,S(Kcurrent))) {
        pushSTACK(O(current_string)); stringcount++; # "@."
      } else if (eq(firstdir,S(Klibrary))) {
        pushSTACK(O(library_string)); stringcount++; # "%."
      } else if (eq(firstdir,S(Kprevious))) {
        pushSTACK(O(previous_string)); stringcount++; # "\\."
      } else
        NOTREACHED;
     #endif
   }}
    directory = Cdr(directory); # skip
    # other subdirs on the stack:
    while (consp(directory)) {
      stringcount += subdir_namestring_parts(directory,logp);
     #if defined(LOGICAL_PATHNAMES)
      if (logp) {
        pushSTACK(O(semicolon_string)); stringcount++; # ";"
      } else
     #endif
      {
       #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
        pushSTACK(O(backslash_string)); stringcount++; # "\\"
       #endif
       #if defined(PATHNAME_UNIX) || defined(PATHNAME_AMIGAOS)
        pushSTACK(O(slash_string)); stringcount++; # "/"
       #endif
       #ifdef PATHNAME_RISCOS
        pushSTACK(O(dot_string)); stringcount++; # "."
       #endif
      }
    directory = Cdr(directory);
    }
  }
  return stringcount;
}

# UP: Pushes substrings for STRING_CONCAT on the STACK, that together yield
# the string for Name and Type of the pathname.
# nametype_namestring_parts(name,type,version)
# > name, type, poss. version: components of the pathname
# < result: number of the strings pushed on the stack
# can trigger GC
# changes STACK
#if HAS_VERSION || defined(LOGICAL_PATHNAMES)
local uintC nametype_namestring_parts (object name, object type,
                                       object version)
#else
local uintC nametype_namestring_parts_ (object name, object type)
#define nametype_namestring_parts(n,t,v)  nametype_namestring_parts_(n,t)
#endif
{
  var uintC stringcount = 0;
  # Name:
  if (!nullp(name)) { # name=NIL -> do not print
    var object string = wild2string(name);
    pushSTACK(string);
    stringcount++; # and count
  }
  # Type:
  if (!nullp(type)) { # type=NIL -> do not print
    pushSTACK(O(dot_string)); # "."
    stringcount++; # and count
    var object string = wild2string(type);
    pushSTACK(string);
    stringcount++; # and count
  }
 #if HAS_VERSION || defined(LOGICAL_PATHNAMES)
  if (!nullp(version)) { # version=NIL -> do not print
    pushSTACK(O(dot_string)); # "."
    stringcount++; # and count
    if (eq(version,S(Knewest)))
      pushSTACK(O(zero_string)); # :NEWEST -> String "0"
    else if (eq(version,S(Kwild)))
      pushSTACK(O(wild_string));
    else
      # version (integer >0) ==> string: (sys::decimal-string version)
      pushSTACK(decimal_string(version));
    stringcount++; # and count
  }
 #endif
  return stringcount;
}

# UP: Pushes substrings for STRING_CONCAT on the STACK, that together yield
# the string for name and type of the pathname.
# file_namestring_parts(pathname)
# > pathname: non-logical pathname
# < result: number of the strings pushed on the stack
# can trigger GC
# changes STACK
local uintC file_namestring_parts (object pathname) {
 #if defined(LOGICAL_PATHNAMES)
  if (logpathnamep(pathname))
    return nametype_namestring_parts
      (TheLogpathname(pathname)->pathname_name,
       TheLogpathname(pathname)->pathname_type,
       TheLogpathname(pathname)->pathname_version);
  else
 #endif
    return nametype_namestring_parts(ThePathname(pathname)->pathname_name,
                                     ThePathname(pathname)->pathname_type,
                                     pathname_version_maybe(pathname));
}

# UP: Converts pathname into string.
# whole_namestring(pathname)
# > pathname: non-logical pathname
# < result: Normal-Simple-String
# can trigger GC
local object whole_namestring (object pathname) {
  var uintC stringcount = 0;
#if !defined(PATHNAME_WIN32) && !defined(PATHNAME_UNIX)
/* though it seems to make sense only on RISCOS */
  stringcount += host_namestring_parts(pathname);
#endif
  stringcount += directory_namestring_parts(pathname);
  stringcount += file_namestring_parts(pathname);
  return string_concat(stringcount);
}

# UP: Returns the string for the directory of a pathname.
# directory_namestring(pathname)
# > pathname: non-logical pathname
# < result: Normal-Simple-String
# can trigger GC
local object directory_namestring (object pathname) {
  # The function DIRECTORY-NAMESTRING is totally underspecified.
  # It could return
  # a. just the string for the directory portion,
  # b. the string for the device + directory portions,
  # c. the string for the host + device + directory portions.
  # Before we used hosts, we have traditionally returned (b).
  # Now, with hosts, we still return (b) since HOST-NAMESTRING returns
  # the host part, while there is no way to return just the device
  # This makes most sense, given that CLHS says that programs
  # should not attempt to concatenate the resulting string with anything.
  return string_concat(directory_namestring_parts(pathname));
}

# UP: Returns the string identifying a file in its directory.
# file_namestring(pathname)
# > pathname: non-logical pathname
# < result: normal-simple-string
# can trigger GC
local inline object file_namestring (object pathname) {
  return string_concat(file_namestring_parts(pathname));
}

LISPFUNNR(file_namestring,1)
{ /* (FILE-NAMESTRING pathname), CLTL p. 417 */
  var object pathname = coerce_xpathname(popSTACK());
  VALUES1(file_namestring(pathname));
}

LISPFUNNR(directory_namestring,1)
{ /* (DIRECTORY-NAMESTRING pathname), CLTL p. 417 */
  var object pathname = coerce_xpathname(popSTACK());
  VALUES1(directory_namestring(pathname));
}

LISPFUNNR(host_namestring,1)
{ /* (HOST-NAMESTRING pathname), CLTL p. 417 */
  var object pathname = coerce_xpathname(popSTACK());
  VALUES1(xpathname_host(logpathnamep(pathname),pathname));
}

#if HAS_VERSION || defined(LOGICAL_PATHNAMES)
# UP: check an optional VERSION argument.
# test_optional_version(def);
# > STACK_0: VERSION-Argument
# > def: default value for it
# < result: valid version-component
local object test_optional_version (object def) {
  var object version = STACK_0;
  if (!boundp(version)) {
    STACK_0 = def; # not specified -> Default
  } else if (nullp(version)) { # NIL is OK
  } else if (eq(version,S(Kwild))) { # :WILD is OK
  } else if (eq(version,S(Knewest))) { # :NEWEST is OK
  } else if (posfixnump(version) && !eq(version,Fixnum_0)) { # Fixnum >0 is OK
  } else if (pathnamep(version)) { # Pathname -> its Version
    STACK_0 = xpathname_version(false,version);
  }
#ifdef LOGICAL_PATHNAMES
  else if (logpathnamep(version)) { # Logical Pathname -> its Version
    STACK_0 = TheLogpathname(version)->pathname_version;
  }
#endif
  else { # None of the desired cases -> error:
    pushSTACK(version);         # TYPE-ERROR slot DATUM
    pushSTACK(O(type_version)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(version);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: :VERSION-argument should be NIL or a positive fixnum or :WILD or :NEWEST, not ~"));
  }
  return STACK_0;
}
#else
# UP: check an optional VERSION argument.
# test_optional_version();
# > STACK_0: VERSION-Argument
#define test_optional_version(def)  test_optional_version_()
local void test_optional_version_ (void) {
  var object version = STACK_0;
  if (missingp(version)
      || eq(version,S(Kwild))   # or :WILD ?
      || eq(version,S(Knewest))) # or :NEWEST ?
    return; # yes -> OK
  else {
    pushSTACK(version);         # TYPE-ERROR slot DATUM
    pushSTACK(O(type_version)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(version);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: :VERSION-argument should be NIL or :WILD or :NEWEST, not ~"));
  }
}
#endif

#if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)

# the operating system manages a default-drive.
# the operating system manages a default-directory on each drive. This
# can change, if another floppy disk is inserted.

# a default-drive is kept: DEFAULT_DRIVE = O(default_drive).

# the variable *DEFAULT-PATHNAME-DEFAULTS* contains (as pathname) the
# default value for each MERGE-operation. It is the one, which the system
# "interpretes into" the pathnames entered by the user.
# It is kept up to date with the DEFAULT_DRIVE: On
# initialization the current device (in terms of DOS), on
# change of DEFAULT_DRIVE via CD.

#endif # PATHNAME_OS2 || PATHNAME_WIN32

#if defined(PATHNAME_UNIX) || defined(PATHNAME_AMIGAOS)

# The variable *DEFAULT-PATHNAME-DEFAULTS* contains (as pathname) the
# default value for each MERGE-operation. It is the one, which the system
# "interpretes into" the pathnames entered by the user.

#endif

#ifdef UNIX

# the operating system manages a default-directory ("working directory")
# for this process. It can be changed with chdir and queried with getwd.
# See CHDIR(2) and GETWD(3).

#endif

#ifdef AMIGAOS

# the operating system manages a default-directory ("current directory")
# for this process. It can be changed with CurrentDir and queried with a
# combination of Examine and ParentDir.

#endif

# UP: Re-calculation of *DEFAULT-PATHNAME-DEFAULTS*
#if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
# from DEFAULT_DRIVE
#endif
# recalc_defaults_pathname();
# < result: value of *DEFAULT-PATHNAME-DEFAULTS*, a pathname
# can trigger GC
local object recalc_defaults_pathname (void) {
 #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  # execute (MAKE-PATHNAME :DEVICE default-drive) :
  pushSTACK(S(Kdevice)); pushSTACK(O(default_drive));
  funcall(L(make_pathname),2);
 #endif
 #if defined(PATHNAME_UNIX) || defined(PATHNAME_AMIGAOS) || defined(PATHNAME_RISCOS)
  # execute (MAKE-PATHNAME) :
  funcall(L(make_pathname),0);
 #endif
  # and assign *DEFAULT-PATHNAME-DEFAULTS* :
  return Symbol_value(S(default_pathname_defaults)) = value1;
}

# UP: Returns the default-pathname.
# defaults_pathname()
# < result: value of *DEFAULT-PATHNAME-DEFAULTS*, a pathname
# can trigger GC
local object defaults_pathname (void) {
  var object pathname = Symbol_value(S(default_pathname_defaults)); # value of *DEFAULT-PATHNAME-DEFAULTS*
  if (xpathnamep(pathname)) { # is a pathname -> OK
    return pathname;
  } else { # else warning:
    pushSTACK(CLSTEXT("The value of ~S was not a pathname. ~:*~S is being reset."));
    pushSTACK(S(default_pathname_defaults));
    funcall(S(warn),2);
    # and re-calculate:
    return recalc_defaults_pathname();
  }
}

# merge two directories
# > p_directory: pathname directory list
# > d_directory: defaults directory list
# > p_log: flag, whether pathname is logical
# > wildp: flag, from MERGE-PATHNAMES
# > called_from_make_pathname: flag, from MERGE-PATHNAMES
# < result: merges directory list
# can trigger GC
local object merge_dirs (object p_directory, object d_directory, bool p_log,
                         bool wildp, bool called_from_make_pathname) {
  var object new_subdirs = p_directory;
 #if DEBUG_TRANSLATE_PATHNAME
  printf("[%d] merge_dirs: log: %d; wild: %d; cfmp: %d\n",
         __LINE__,p_log,wildp,called_from_make_pathname);
 #endif
  SDOUT("merge_dirs:",p_directory);
  SDOUT("merge_dirs:",d_directory);
  if (called_from_make_pathname) {
    if (!boundp(p_directory)) /* pathname-subdirs not given? */
      new_subdirs = d_directory; # use defaults-subdirs
  } else if (!wildp) {
    # is pathname-subdirs trivial?
    if (eq(Car(p_directory),p_log ? S(Kabsolute) : S(Krelative))
        && matomp(Cdr(p_directory))) {
      new_subdirs = d_directory; # use defaults-subdirs:
    } else if (eq(Car(p_directory),S(Krelative))
               # PATHNAME = :ABSOLUTE ==> merge is not needed
               && (eq(Car(d_directory),S(Kabsolute))
                   || !nullpSv(merge_pathnames_ansi))) {
      # (append defaults-subdirs (cdr pathname-subdirs)) =
      # (nreconc (reverse defaults-subdirs) (cdr pathname-subdirs)) :
      pushSTACK(Cdr(p_directory));
      var object temp = reverse(d_directory);
      new_subdirs = simplify_directory(nreconc(temp,popSTACK()));
    }
  }
  return new_subdirs;
}

# (MERGE-PATHNAMES pathname [defaults [default-version]] [:wild]), CLTL p. 415
# Definition assuming that HAS_HOST and HAS_DEVICE are exclusive:
# (defun merge-pathnames (pathname &optional (defaults *default-pathname-defaults*) default-version)
#   (setq pathname (pathname pathname))
#   (setq defaults (pathname defaults))
#   (multiple-value-call #'make-pathname
#if HAS_HOST
#     (if (or (equal (pathname-host pathname) (pathname-host defaults))
#             (null (pathname-host pathname))
#         )
#       (values
#         :host (or (pathname-host pathname) (pathname-host defaults))
#endif
#if HAS_DEVICE
#     (if (or (equal (pathname-device pathname) (pathname-device defaults))
#             (null (pathname-device pathname))
#         )
#       (values
#         :device (or (pathname-device pathname) (pathname-device defaults))
#endif
#         :directory
#           (let ((pathname-dir (pathname-directory pathname))
#                 (defaults-dir (pathname-directory defaults)))
#             (if (eq (car pathname-dir) ':RELATIVE)
#               (cond ((null (cdr pathname-dir)) defaults-dir)
#                     ((or *merge-pathnames-ansi*
#                          (not (eq (car defaults-dir) ':RELATIVE)) ; <----
#                      )
#                      (append defaults-dir (cdr pathname-dir))
#                     )
#                     (t pathname-dir)
#               )
#               pathname-dir
#           ) )
#       )
#       (values
#if HAS_HOST
#         :host (pathname-host pathname)
#endif
#if HAS_DEVICE
#         :device (pathname-device pathname)
#endif
#         :directory (pathname-directory pathname)
#     ) )
#     :name (or (pathname-name pathname) (pathname-name defaults))
#     :type (or (pathname-type pathname) (pathname-type defaults))
# ) )
#
# If HAS_HOST and HAS_DEVICE are both true, the semantics are more
# complicated; see CLHS for details.
#
# If the :WILD argument is specified, :WILD components are replaced,
# instead of missing components.
#
# Explanation of the "<----" line:
#
# Roger Kehr <kehr@iti.informatik.th-darmstadt.de> asks why in CLISP
#
# (merge-pathnames (make-pathname :directory '(:relative "x"))
#                  (make-pathname :directory '(:relative "y")))
# => #"x/"
#
# where he expects to get #"y/x/".
#
# Bruno: There are two reasons for this behaviour:
#
# 1. An informal one: I found the latter behaviour confusing and changed
#    CLISP to do it the former way. It seems to work better this way.
#
# 2. A formal one: MERGE-PATHNAMES is used to specify default components
#    for pathnames, so there is some analogy between (MERGE-PATHNAMES a b)
#    and (or a b). Obviously putting in the same default a second time
#    should do the same as putting it in once:
#
#      (or a b b) is the same as (or a b), so
#
#      (MERGE-PATHNAMES (MERGE-PATHNAMES a b) b) should be the same as
#      (MERGE-PATHNAMES a b).
#
#    (This question actually matters because in Common Lisp there is
#    no distinction between "pathnames with defaults merged-in" and
#    "pathnames with defaults not yet applied". For example, you do not
#    know whether COMPILE-FILE will merge in some defaults.)
#
#    Now, (MERGE-PATHNAMES (MERGE-PATHNAMES '#"x/" '#"y/") '#"y/")
#    and  (MERGE-PATHNAMES '#"x/" '#"y/")
#    are equal in CLISP's implementation, but not in implementations
#    that strictly follow the Common Lisp spec. In fact, the above
#    twice-default = once-default rule holds for all pathnames in CLISP.
LISPFUN(merge_pathnames,seclass_read,1,2,norest,key,1, (kw(wild))) {
  # :wild #'make-pathname causes NIL components to be considered specified,
  # only #<unbound> components are considered unspecified.
  var bool called_from_make_pathname = eq(STACK_0,L(make_pathname));
  # :wild t causes only wild components to be considered unspecified.
  var bool wildp = !missingp(STACK_0);
  skipSTACK(1);

#define SPECIFIED(obj)                                  \
    !(called_from_make_pathname ? !boundp(obj) :     \
      (wildp ? eq(obj,S(Kwild)) : nullp(obj)))
#define NAMETYPE_MATCH(acc,slot)                                           \
    { var object tmp = x##slot(p_log,p);                                   \
      acc(newp)->slot = (SPECIFIED(tmp) ? tmp : (object)x##slot(d_log,d)); \
    }

  # check pathname (STACK_2) and defaults (STACK_1):
  # (coerce defaults 'pathname):
  STACK_1 = test_default_pathname(STACK_1);
  # (coerce pathname 'pathname):
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(STACK_1)) {
    if (!xpathnamep(STACK_2)) { # pathname
      STACK_2 = parse_as_logical(STACK_2);
      DOUT("merge-pathnames:[log_pathname]",STACK_2);
    }
  } else
  #endif
  STACK_2 = coerce_xpathname(STACK_2); # pathname
  var bool d_log = logpathnamep(STACK_1);
  var bool p_log = logpathnamep(STACK_2);

 #if HAS_VERSION || defined(LOGICAL_PATHNAMES)
  { # check default-version (STACK_0):
    var object v = test_optional_version(unbound);
    var object p_version = xpathname_version(p_log,STACK_2);
    if (!boundp(v)) {
      var object p_name    = xpathname_name   (p_log,STACK_2);
      var object d_version = xpathname_version(d_log,STACK_1);
      v = (SPECIFIED(p_version) ? p_version :
           (SPECIFIED(d_version) && !SPECIFIED(p_name) ? d_version :
            S(Knewest)));
    } else if (nullp(v)) v = p_version;
    if (!boundp(v)) v = S(Knewest);
    STACK_0 = STACK_1; STACK_1 = STACK_2; STACK_2 = v;
    DOUT("merge-pathnames:",v);
  }
  # stack layout: default-version, pathname, defaults.
 #else
  test_optional_version(S(Knewest)); skipSTACK(1);
  # stack layout: pathname, defaults.
 #endif

  # do the merge
 #ifdef LOGICAL_PATHNAMES
  DOUT("merge-pathnames:[defaults]",STACK_0);
  DOUT("merge-pathnames:[pathname]",STACK_1);
  if (d_log || p_log) {
    # MERGE-PATHNAMES for logical pathnames
    var object newp = allocate_logpathname(); # fetch new pathname
    var object d = popSTACK(); # defaults
    var object p = popSTACK(); # pathname
    { # match hosts:
      var object p_host = xpathname_host(p_log,p);
      var object d_host = xpathname_host(d_log,d);
      TheLogpathname(newp)->pathname_host = p_host; # initially, new-host := pathname-host
      if (equal(p_host,d_host))
        goto lmatch_directories;
      if (wildp ? !boundp(p_host) : nullp(p_host)) {
        # pathname-host not specified, but defaults-host specified:
        TheLogpathname(newp)->pathname_host = d_host; # new-host := defaults-host
        goto lmatch_directories;
      }
    }
    { # directories do not match: new-directory := pathname-directory
      var object dir = xpathname_directory(p_log,p);
      TheLogpathname(newp)->pathname_directory =
        (!boundp(dir) ? xpathname_directory(d_log,d) : dir);
      goto ldirectories_OK;
    }
  lmatch_directories:
    { # match directories:
      pushSTACK(p); pushSTACK(d); pushSTACK(newp);
      TheLogpathname(STACK_0)->pathname_directory =
        merge_dirs(xpathname_directory(p_log,p),
                   xpathname_directory(d_log,d),
                   p_log,wildp,called_from_make_pathname);
      newp = popSTACK(); d = popSTACK(); p = popSTACK();
    }
  ldirectories_OK:
    # the directories are OK now
    NAMETYPE_MATCH(TheLogpathname,pathname_name);
    NAMETYPE_MATCH(TheLogpathname,pathname_type);
    TheLogpathname(newp)->pathname_version = popSTACK();
    DOUT("merge-pathnames:[ret]",newp);
    VALUES1(newp);
    return;
  }
  # not both are logical pathnames -> first, convert into normal pathnames:
  STACK_1 = coerce_pathname(STACK_1);
  STACK_0 = coerce_pathname(STACK_0);
 #endif
  var object newp = allocate_pathname(); # fetch new pathname
  var object d = popSTACK(); # defaults
  var object p = popSTACK(); # pathname
 #if HAS_HOST
  { # match hosts:
    var object p_host = ThePathname(p)->pathname_host;
    var object d_host = ThePathname(d)->pathname_host;
    ThePathname(newp)->pathname_host = p_host; # initially, new-host := pathname-host
    # both hosts equal -> match devices:
    if (equal(p_host,d_host))
      goto match_devices;
    if (!(wildp ? false : nullp(p_host)))
      goto notmatch_devices;
   #ifdef PATHNAME_WIN32
    var object p_device = ThePathname(p)->pathname_device;
    # On Win32, a non-null p_device implicitly designates p_host as the
    # local machine. It must not be overridden by d_host.
    if (SPECIFIED(p_device))
      goto notmatch_devices;
   #endif
    # pathname-host not specified, but defaults-host specified:
    ThePathname(newp)->pathname_host = d_host; # new-host := defaults-host
    goto match_devices;
  }
 #endif /* HAS_HOST */
 match_devices:
 #if HAS_DEVICE
  { # match devices:
    var object p_device = ThePathname(p)->pathname_device;
    var object d_device = ThePathname(d)->pathname_device;
    ThePathname(newp)->pathname_device = p_device; # initially, new-device := pathname-device
    # both devices equal -> match directories:
    if (equal(p_device,d_device))
      goto match_directories;
    if (!SPECIFIED(p_device)) {
      # pathname-device not given, but defaults-device is given:
      ThePathname(newp)->pathname_device = d_device; # new-device := defaults-device
      goto match_directories;
    }
    goto notmatch_directories;
  }
 #endif /* HAS_DEVICE */
 match_directories: { /* match directories: */
    var object tmp;
    pushSTACK(p); pushSTACK(d); pushSTACK(newp);
    tmp = merge_dirs(ThePathname(p)->pathname_directory,
                     ThePathname(d)->pathname_directory,
                     false,wildp,called_from_make_pathname);
    newp = popSTACK(); d = popSTACK(); p = popSTACK();
    ThePathname(newp)->pathname_directory = tmp;
  }
  goto directories_OK;
  # do not match devices:
 notmatch_devices:
 #if HAS_DEVICE
  { # new-device := pathname-device :
    ThePathname(newp)->pathname_device = ThePathname(p)->pathname_device;
  }
 #endif
 notmatch_directories:
  { # directories do not match: new-directory := pathname-directory
    var object dir = xpathname_directory(p_log,p);
    ThePathname(newp)->pathname_directory =
      (!boundp(dir) ? xpathname_directory(d_log,d) : dir);
  }
 directories_OK:
  # the directories are OK now
  NAMETYPE_MATCH(ThePathname,pathname_name);
  NAMETYPE_MATCH(ThePathname,pathname_type);
 #if HAS_VERSION
  ThePathname(newp)->pathname_version = popSTACK();
 #elif defined(LOGICAL_PATHNAMES)
  skipSTACK(1);
 #endif
  DOUT("merge-pathnames:[ret]",newp);
  VALUES1(newp);
}
#undef SPECIFIED
#undef NAMETYPE_MATCH

# (ENOUGH-NAMESTRING pathname [defaults]), CLTL p. 417
# Definition assuming that HAS_HOST and HAS_DEVICE are exclusive:
# (defun enough-namestring (pathname &optional (defaults *default-pathname-defaults*))
#   (setq pathname (pathname pathname))
#   (setq defaults (pathname defaults))
#   (namestring
#     (multiple-value-call #'make-pathname
#if HAS_HOST
#       (if (equal (pathname-host pathname) (pathname-host defaults))
#         (values
#           :host nil
#endif
#if HAS_DEVICE
#       (if (equal (pathname-device pathname) (pathname-device defaults))
#         (values
#           :device nil
#endif
#           :directory
#             (let ((pathname-dir (pathname-directory pathname))
#                   (defaults-dir (pathname-directory defaults)))
#               (if (equal pathname-dir defaults-dir)
#                 (list ':RELATIVE)
#                 (if (and (not (eq (car pathname-dir) ':RELATIVE))
#                          (not (eq (car defaults-dir) ':RELATIVE))
#                          (equal (subseq pathname-dir 0 (min (length pathname-dir) (length defaults-dir)))
#                                 defaults-dir
#                     )    )
#                   (cons ':RELATIVE (nthcdr (length defaults-dir) pathname-dir))
#                   pathname-dir
#             ) ) )
#         )
#         (values
#if HAS_HOST
#           :host (pathname-host pathname)
#endif
#if HAS_DEVICE
#           :device (pathname-device pathname)
#endif
#           :directory (pathname-directory pathname)
#       ) )
#       :name (if (equal (pathname-name pathname) (pathname-name defaults))
#               nil
#               (pathname-name pathname)
#             )
#       :type (if (equal (pathname-type pathname) (pathname-type defaults))
#               nil
#               (pathname-type pathname)
#             )
# ) ) )
#
# If HAS_HOST and HAS_DEVICE are both true, the semantics are more
# complicated; see CLHS for details.
#define SET_NEWP(slot,value)                            \
      if (log2) TheLogpathname(newp)->slot = value;     \
      else ThePathname(newp)->slot = value;
LISPFUN(enough_namestring,seclass_read,1,1,norest,nokey,0,NIL) {
  # check pathname and defaults:
  # turn pathname into a Pathname:
  STACK_1 = coerce_xpathname(STACK_1);
  var bool log2 = logpathnamep(STACK_1);
  # turn defaults into a Pathname:
  STACK_0 = test_default_pathname(STACK_0);
  var bool log1 = logpathnamep(STACK_0);
  # fetch new Pathname:
  var object newp = (log2 ? allocate_logpathname() : allocate_pathname());
  pushSTACK(newp);
  # stack layout: pathname, defaults, new.
 #if HAS_HOST
  { # compare hosts:
    var object p_host = xpathname_host(log2,STACK_2); # pathname-host
    var object d_host = xpathname_host(log1,STACK_1); # defaults-host
    if (equal(p_host,d_host)) { # both hosts equal?
      SET_NEWP(pathname_host,NIL); # new-host := NIL
 #endif
 #if HAS_DEVICE
    { # compare devices:
      var object p_device = xpathname_device(log2,STACK_2); # pathname-device
      var object d_device = xpathname_device(log1,STACK_1); # defaults-device
      if (equal(p_device,d_device)) { # both devices equal?
        if (!log2) ThePathname(newp)->pathname_device = NIL;
 #endif
        {
          var object p_directory = xpathname_directory(log2,STACK_2); # pathname-directory
          var object d_directory = xpathname_directory(log1,STACK_1); # defaults-directory
          var object new_subdirs;
          # compare pathname-subdirs and defaults-subdirs:
          if (equal(p_directory,d_directory)) {
            # equal -> use (cons :RELATIVE nil) :
            new_subdirs = NIL; goto insert_RELATIVE;
          } else {
            # Does neither pathname-subdirs nor defaults-subdirs
            # start with :RELATIVE ?
            if (   (!eq(Car(p_directory),S(Krelative)))
                && (!eq(Car(d_directory),S(Krelative)))) {
              # yes -> test, if defaults-subdirs is a starting piece
              # of the list pathname-subdirs:
              var object Lp = p_directory;
              var object Ld = d_directory;
              # Is Ld a starting piece of Lp ?
              loop {
                if (atomp(Ld)) { # Ld finished -> yes
                  new_subdirs = Lp; goto insert_RELATIVE;
                }
                if (atomp(Lp))
                  break; # Lp finished -> no
                if (!equal(Car(Ld),Car(Lp))) # different list-elements?
                  break; # -> no
                Ld = Cdr(Ld); Lp = Cdr(Lp); # advance lists
              }
            }
            new_subdirs = p_directory; # new-subdirs := pathname-subdirs
            goto subdirs_ok;
          }
         insert_RELATIVE:
          { /* new-subdirs := (cons :RELATIVE new-subdirs) : */
            pushSTACK(new_subdirs);
            new_subdirs = allocate_cons();
            Cdr(new_subdirs) = popSTACK(); Car(new_subdirs) = S(Krelative);
          }
         subdirs_ok: # new-subdirs is the new subdir-list.
          # new-directory := new-subdirs :
          newp = STACK_0;
          SET_NEWP(pathname_directory,new_subdirs);
        }
    #if HAS_DEVICE
      } else {
        # different devices
        # (Note for PATHNAME_WIN32: If we have different devices, the common
        # host must have been NIL.)
        # new-device := pathname-device
        # new-directory := pathname-directory
        if (log2) {
          TheLogpathname(newp)->pathname_directory =
            TheLogpathname(STACK_2)->pathname_directory;
        } else {
          ThePathname(newp)->pathname_device = p_device;
          ThePathname(newp)->pathname_directory =
            ThePathname(STACK_2)->pathname_directory;
        }
      }
    }
    #endif
    #if HAS_HOST
    } else { # different hosts
      # new-host := pathname-host
      # new-device := pathname-device
      # new-directory := pathname-directory
      if (log2) {
        TheLogpathname(newp)->pathname_host = p_host;
        TheLogpathname(newp)->pathname_directory =
          TheLogpathname(STACK_2)->pathname_directory;
      } else {
        ThePathname(newp)->pathname_host = p_host;
       #if HAS_DEVICE
        ThePathname(newp)->pathname_device =
          ThePathname(STACK_2)->pathname_device;
       #endif
        ThePathname(newp)->pathname_directory =
          ThePathname(STACK_2)->pathname_directory;
      }
    }
  }
 #endif
  { # fill in name:
    var object p_name = xpathname_name(log2,STACK_2); # pathname-name
    var object d_name = xpathname_name(log1,STACK_1); # defaults-name
    var object r_name = (equal(p_name,d_name) ? NIL : p_name);
    SET_NEWP(pathname_name,r_name);
  }
  { # fill in type:
    var object p_type = xpathname_type(log2,STACK_2); # pathname-type
    var object d_type = xpathname_type(log1,STACK_1); # defaults-type
    var object r_type = (equal(p_type,d_type) ? NIL : p_type);
    SET_NEWP(pathname_type,r_type);
  }
  skipSTACK(3);
  # build (namestring new) :
  with_saved_back_trace(L(namestring),-1,VALUES1(whole_namestring(newp)));
}
#undef SET_NEWP

#ifdef LOGICAL_PATHNAMES

# UP: checks, if object is an admissible name:
# :WILD or a Simple-String made of valid characters, without adjacent '*'.
# legal_logical_word(object)
# > object: if a simple-string, a normal-simple-string
local bool legal_logical_word (object obj) {
  if (eq(obj,S(Kwild)))
    return true;
  if (!simple_string_p(obj))
    return false;
  ASSERT(sstring_normal_p(obj));
  var uintL len = Sstring_length(obj);
  if (len==0)
    return false; # empty word is forbidden
  SstringDispatch(obj,X, {
    var const cintX* charptr = &((SstringX)TheVarobject(obj))->data[0];
    var bool last_was_star = false;
    dotimespL(len,len, {
      var chart cc = as_chart(*charptr++);
      if (!(legal_logical_word_char(cc) || chareq(cc,ascii('*'))))
        return false;
      if (chareq(cc,ascii('*'))) {
        if (last_was_star)
          return false; # adjacent '*' are forbidden
        last_was_star = true;
      } else {
        last_was_star = false;
      }
    });
  });
  return true;
}

#endif

#if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)

# UP: checks, if object is an admissible name:
# a Simple-String made of valid characters
# legal_name(object)
# > object: any object
local bool legal_name (object obj) {
  if (!stringp(obj)) return false;
  var uintL len, offset;
  obj = unpack_string_ro(obj,&len,&offset);
  if (len > 0) {
    SstringDispatch(obj,X, {
      var const cintX* charptr = &((SstringX)TheVarobject(obj))->data[offset];
      dotimespL(len,len, {
        if (!legal_namechar(as_chart(*charptr++)))
          return false;
      });
    });
  }
  return true;
}

# UP: checks, if object is an admissible name:
# ein Simple-String made of valid characters, without '.'
# legal_type(object)
# > object: if a simple-string, a normal-simple-string
local bool legal_type (object obj);
#ifdef PATHNAME_NOEXT
local bool legal_type (object obj) {
  if (!simple_string_p(obj))
    return false;
  ASSERT(sstring_normal_p(obj));
  var uintL len = Sstring_length(obj);
  if (len > 0) {
    SstringDispatch(obj,X, {
      var const cintX* charptr = &((SstringX)TheVarobject(obj))->data[0];
      dotimespL(len,len, {
        var chart cc = as_chart(*charptr++);
        if (chareq(cc,ascii('.')) || !legal_namechar(cc))
          return false;
      });
    });
  }
  return true;
}
#endif
#ifdef PATHNAME_RISCOS
  #define legal_type(obj)  legal_name(obj)
#endif

#endif # PATHNAME_NOEXT || PATHNAME_RISCOS

local object copy_pathname (object pathname);

# check whether the list is a valid directory list
local bool directory_list_valid_p (bool logical, object dirlist) {
  { # CAR must be either :RELATIVE or :ABSOLUTE ?
    var object startpoint = Car(dirlist);
    if (!(eq(startpoint,S(Krelative)) || eq(startpoint,S(Kabsolute))))
      return false;
   #ifdef PATHNAME_RISCOS
    if (!logical && eq(startpoint,S(Kabsolute))) {
      dirlist = Cdr(dirlist);
      startpoint = Car(dirlist);
      if (!(   eq(startpoint,S(Kroot))
               || eq(startpoint,S(Khome))
               || eq(startpoint,S(Kcurrent))
               || eq(startpoint,S(Klibrary))
               || eq(startpoint,S(Kprevious))) )
        return false;
    }
   #endif
  }
  dirlist = Cdr(dirlist);
  # check subdir list:
  while (consp(dirlist)) {
    # check the next subdir = POP(dirlist);
    var object subdir = Car(dirlist); dirlist = Cdr(dirlist);
   #ifdef LOGICAL_PATHNAMES
    if (logical) {
      if (!(eq(subdir,S(Kwild_inferiors)) || eq(subdir,S(Kwild))
            || legal_logical_word(subdir) || eq(subdir,S(Kup))))
        return false;
    } else
   #endif
    {
     #ifdef PATHNAME_NOEXT
      #ifdef PATHNAME_AMIGAOS
      if (!(eq(subdir,S(Kwild_inferiors)) || eq(subdir,S(Kparent))
            || legal_name(subdir) || eq(subdir,S(Kup))))
        return false;
      #endif
      #if defined(PATHNAME_UNIX) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
      if (!(eq(subdir,S(Kwild_inferiors)) || eq(subdir,S(Kwild))
            || legal_name(subdir) || eq(subdir,S(Kup))))
        return false;
      #endif
     #endif
      #ifdef PATHNAME_RISCOS
      if (!(eq(subdir,S(Kparent)) || legal_name(subdir) || eq(subdir,S(Kup))))
        return false;
      #endif
    }
  }
  return true;
}

#ifdef LOGICAL_PATHNAMES
 #define COERCE_PATHNAME_SLOT(slot,obj,stack_res)       \
   stack_res = ThePathname(coerce_pathname(obj))->pathname_##slot
#else
 #define COERCE_PATHNAME_SLOT(slot,obj,stack_res)       \
   stack_res = ThePathname(obj)->pathname_##slot
#endif

# (MAKE-PATHNAME [:host] [:device] [:directory] [:name] [:type] [:version]
#                [:defaults] [:case]),
# CLTL p. 416, CLtL2 p. 643
LISPFUN(make_pathname,seclass_read,0,0,norest,key,8,
        (kw(defaults),kw(case),kw(host),kw(device),kw(directory),
         kw(name),kw(type),kw(version)) ) {
  # stack layout: defaults, case, host, device, directory, name, type, version.
  var bool logical = false;
  var bool convert = eq(STACK_6,S(Kcommon));
  # 0. check defaults (STACK_7):
  if (boundp(STACK_7)) {
   #ifdef LOGICAL_PATHNAMES
    if (!nullpSv(parse_namestring_ansi)
        && stringp(STACK_7) && looks_logical_p(STACK_7))
      STACK_7 = parse_as_logical(STACK_7);
    else
   #endif
      STACK_7 = coerce_xpathname(STACK_7);
  }
  # 1. check host:
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(STACK_5)) {
    STACK_5 = TheLogpathname(STACK_5)->pathname_host;
    logical = true;
  }
 #endif
  if (!boundp(STACK_5)) {
    var object d_path = defaults_pathname();
    STACK_5 = (!boundp(STACK_7) ?
               xpathname_host(logpathnamep(d_path),d_path) :
               xpathname_host(logpathnamep(STACK_7),STACK_7));
  } else {
   #if HAS_HOST
    STACK_5 = test_optional_host(STACK_5,convert);
   #else
    STACK_5 = test_optional_host(STACK_5);
   #endif
  }
 #ifdef LOGICAL_PATHNAMES
  if (!nullp(STACK_5) && logical_host_p(STACK_5)) {
    logical = true; STACK_5 = string_upcase(STACK_5);
  }
 #endif
  DOUT("make-pathname:[version]",STACK_0);
  DOUT("make-pathname:[type]",STACK_1);
  DOUT("make-pathname:[name]",STACK_2);
  DOUT("make-pathname:[directory]",STACK_3);
  DOUT("make-pathname:[device]",STACK_4);
  DOUT("make-pathname:[host]",STACK_5);
  DOUT("make-pathname:[case]",STACK_6);
  DOUT("make-pathname:[defaults]",STACK_7);
 #if HAS_DEVICE
  { # 2. check device:
    var object device = STACK_4;
    if (!boundp(device)) {
      if (!boundp(STACK_7)) /* no defaults? */
        STACK_4 = NIL; # -> use NIL
    } else {
      if (stringp(device))
        STACK_4 = device = coerce_normal_ss(device);
      if (convert)
        STACK_4 = device = common_case(device);
      if (nullp(device)) # = NIL ?
        goto device_ok;
     #ifdef LOGICAL_PATHNAMES
      else if (logical) {
        if (logpathnamep(device)) { # Pathname -> its device
          STACK_4 = NIL; goto device_ok;
        }
      }
     #endif
     #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
      else if (eq(device,S(Kwild))) # = :WILD ?
        goto device_ok;
      else if (simple_string_p(device)) { # Simple-String ?
        if (Sstring_length(device) == 1) { # of length 1 ?
          var chart ch = TheSstring(device)->data[0];
          if ((as_cint(ch) >= 'A') && (as_cint(ch) <= 'Z')) # with letters >='A' and <='Z' ?
            goto device_ok;
        }
      }
     #endif
     #ifdef PATHNAME_AMIGAOS
      else if (simple_string_p(device)) { # Simple-String ?
        var uintL count = Sstring_length(device);
        if (count > 0) {
          var const chart* ptr = &TheSstring(device)->data[0];
          dotimespL(count,count, {
            if (!legal_namechar(*ptr++)) goto device_not_ok;
          });
        }
        goto device_ok;
      device_not_ok: ;
      }
     #endif
     #ifdef PATHNAME_RISCOS
      else if (simple_string_p(device)) { # Simple-String ?
        var uintL count = Sstring_length(device);
        if (count > 0) {
          var const chart* ptr = &TheSstring(device)->data[0];
          dotimespL(count,count, {
            var chart ch = *ptr++;
            if (!(legal_namechar(ch) && !wild_char_p(ch)))
              goto device_not_ok;
          });
        }
        goto device_ok;
      device_not_ok: ;
      }
     #endif
      else if (xpathnamep(device)) { # Pathname -> its Device
        COERCE_PATHNAME_SLOT(device,device,STACK_4);
        goto device_ok;
      }
      # None of the desired cases -> error:
      pushSTACK(STACK_4); pushSTACK(S(Kdevice)); goto fehler_arg;
       device_ok: ;
     #ifdef PATHNAME_WIN32
      if (!nullp(STACK_5) && !nullp(STACK_4)) {
        pushSTACK(STACK_4);
        pushSTACK(STACK_(5+1));
        pushSTACK(TheSubr(subr_self)->name);
        fehler(error,
               GETTEXT("~: on host ~, device ~ is invalid, should be NIL"));
      }
     #endif
    }
  }
 #else /* HAS_DEVICE */
  {
    var object device = STACK_4;
    if (boundp(device)) /* specified ? */
      if (!(nullp(device) || xpathnamep(device))) { # NIL or Pathname -> OK
        # None of the desired cases -> error:
        pushSTACK(STACK_4); pushSTACK(S(Kdevice)); goto fehler_arg;
      }
  }
 #endif
  { # 3. check directory:
    DOUT("make-pathname:[directory]",STACK_3);
    var object directory = STACK_3;
    if (!boundp(directory) && boundp(STACK_7)) {
      # not specified but defaults is supplied
      goto directory_ok;
    } else if (missingp(directory)) {
      # not specified or NIL
     #ifdef PATHNAME_AMIGAOS
      if (!nullp(STACK_4)) # Device specified (with non-logical pathname)?
        STACK_3 = O(directory_absolute); # Default is (:ABSOLUTE)
      else
     #endif
        STACK_3 = O(directory_default); # Default is (:RELATIVE)
      goto directory_ok;
    } else if (eq(directory,S(Kwild)) || eq(directory,S(Kwild_inferiors))) {
      directory = S(Kwild_inferiors);
      goto directory_add_absolute;
    } else if (stringp(directory)) {
      if (!legal_name(directory)) goto directory_bad;
      STACK_3 = directory = coerce_normal_ss(directory);
    directory_add_absolute:
      pushSTACK(S(Kabsolute));
      pushSTACK(directory);
      directory = listof(2); STACK_3 = directory;
      goto directory_ok;
    } else if (consp(directory)) { # a Cons?
      STACK_3 = directory = simplify_directory(copy_list(directory));
      if (convert)
        STACK_3 = directory = subst_common_case(directory);
      if (!directory_list_valid_p(logical,directory))
        goto directory_bad;
      else
        goto directory_ok;
    }
   #ifdef LOGICAL_PATHNAMES
    else if (logical) {
      if (logpathnamep(directory)) { # Pathname -> its Directory
        STACK_3 = TheLogpathname(directory)->pathname_directory;
        goto directory_ok;
      }
    }
   #endif
    else if (xpathnamep(directory)) { # Pathname -> its Directory
      COERCE_PATHNAME_SLOT(directory,directory,STACK_3);
      goto directory_ok;
    }
    # None of the desired cases -> error:
  directory_bad:
    pushSTACK(STACK_3); pushSTACK(S(Kdirectory)); goto fehler_arg;
  directory_ok: ;
   #ifdef PATHNAME_AMIGAOS
    # For device /= NIL the directory must begin with :ABSOLUTE :
    if (!nullp(STACK_4) && !eq(Car(STACK_3),S(Kabsolute)))
      goto directory_bad;
   #endif
  }
  { # 4. check name:
    DOUT("make-pathname:[name]",STACK_2);
    var object name = STACK_2;
    if (stringp(name))
      STACK_2 = name = coerce_normal_ss(name);
    if (convert)
      STACK_2 = name = common_case(name);
    if (!boundp(name)) { /* not specified */
        if (!boundp(STACK_7)) /* no defaults? */
          STACK_2 = NIL; # -> use NIL
    } else if (equal(name,O(empty_string))) { # name = "" ?
      STACK_2 = NIL; # -> use NIL
    } else if (nullp(name)) { # NIL is OK
    }
   #ifdef LOGICAL_PATHNAMES
    else if (logical) {
      if (legal_logical_word(name)) { # OK
      } else if (logpathnamep(name)) { # Pathname -> its Name
        STACK_2 = TheLogpathname(name)->pathname_name;
      } else { # None of the desired cases -> error:
        pushSTACK(STACK_2); pushSTACK(S(Kname)); goto fehler_arg;
      }
    }
   #endif
   #if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
    else if (eq(name,S(Kwild))) { # :WILD is OK
    }
   #endif
    else if (legal_name(name)) { # admissible Name ist OK
      STACK_2 = name = coerce_normal_ss(name);
    } else if (xpathnamep(name)) { # Pathname -> its Name
      COERCE_PATHNAME_SLOT(name,name,STACK_2);
    } else { # None of the desired cases -> error:
      pushSTACK(STACK_2); pushSTACK(S(Kname)); goto fehler_arg;
    }
  }
  { # 5. check type:
    DOUT("make-pathname:[type]",STACK_1);
    var object type = STACK_1;
    if (stringp(type))
      STACK_1 = type = coerce_normal_ss(type);
    if (convert)
      STACK_1 = type = common_case(type);
    if (!boundp(type)) {
      if (!boundp(STACK_7)) /* no Defaults ? */
        STACK_1 = NIL; # -> use NIL
    } else if (nullp(type)) { # NIL is OK
    }
   #ifdef LOGICAL_PATHNAMES
    else if (logical) {
      if (legal_logical_word(type)) { # OK
      } else if (logpathnamep(type)) { # Pathname -> its Type
        STACK_1 = TheLogpathname(type)->pathname_type;
      } else { # None of the desired cases -> error:
        pushSTACK(STACK_1); pushSTACK(S(Ktype)); goto fehler_arg;
      }
    }
   #endif
   #if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
    else if (eq(type,S(Kwild))) { # :WILD is OK
    }
   #endif
    else if (legal_type(type)) {
    } else if (xpathnamep(type)) { # Pathname -> its Type
      COERCE_PATHNAME_SLOT(type,type,STACK_1);
    } else { # None of the desired cases -> error:
      pushSTACK(STACK_1); pushSTACK(S(Ktype)); goto fehler_arg;
    }
  }
  # 6. check version:
 #if HAS_VERSION || defined(LOGICAL_PATHNAMES)
  STACK_0 = test_optional_version(!boundp(STACK_7) ? NIL : unbound);
  DOUT("make-pathname:[ver]",STACK_0);
  DOUT("make-pathname:[ver]",STACK_7);
 #else
  test_optional_version(NIL);
 #endif
  { # 7. build Pathname:
    var object pathname;
   #ifdef LOGICAL_PATHNAMES
    if (logical) {
      pathname = allocate_logpathname(); # new Logical Pathname
      TheLogpathname(pathname)->pathname_version   = popSTACK();
      TheLogpathname(pathname)->pathname_type      = popSTACK();
      TheLogpathname(pathname)->pathname_name      = popSTACK();
      TheLogpathname(pathname)->pathname_directory = popSTACK();
      skipSTACK(1);
      TheLogpathname(pathname)->pathname_host      = popSTACK();
    } else
   #endif
    {
      pathname = allocate_pathname(); # new Pathname
     #if HAS_VERSION
      ThePathname(pathname)->pathname_version   = popSTACK();
     #else
      skipSTACK(1);
     #endif
      ThePathname(pathname)->pathname_type      = popSTACK();
      ThePathname(pathname)->pathname_name      = popSTACK();
      ThePathname(pathname)->pathname_directory = popSTACK();
     #if HAS_DEVICE
      ThePathname(pathname)->pathname_device    = popSTACK();
     #else
      skipSTACK(1);
     #endif
     #if HAS_HOST
      ThePathname(pathname)->pathname_host      = popSTACK();
     #else
      skipSTACK(1);
     #endif
    }
    STACK_0 = pathname; # forget case
    DOUT("make-pathname:[pathname]",STACK_0);
    DOUT("make-pathname:[defaults]",STACK_1);
    pathname = popSTACK();
    # 8. poss. merge in Defaults:
    var object defaults = popSTACK();
    if (!boundp(defaults)) { /* no defaults given -> pathname is the value */
      value1 = pathname;
    } else { # (MERGE-PATHNAMES pathname defaults [nil] :wild #'make-pathname)
      pushSTACK(pathname); pushSTACK(defaults);
      pushSTACK(unbound); pushSTACK(S(Kwild)); pushSTACK(L(make_pathname));
      funcall(L(merge_pathnames),5);
    }
    mv_count=1;
    DOUT("make-pathname:[ret]",value1);
    return;
  }
 fehler_arg: # error-message:
  pushSTACK(TheSubr(subr_self)->name);
  fehler(error,GETTEXT("~: illegal ~ argument ~"));
}
#undef COERCE_PATHNAME_SLOT

#ifdef LOGICAL_PATHNAMES

# (MAKE-LOGICAL-PATHNAME [:host] [:device] [:directory] [:name]
#                        [:type] [:version] [:defaults] [:case]),
# like MAKE-PATHNAME, except that a Logical Pathname is built.
LISPFUN(make_logical_pathname,seclass_read,0,0,norest,key,8,
        (kw(defaults),kw(case),kw(host),kw(device),
         kw(directory),kw(name),kw(type),kw(version)) ) {
  # A logical pathname as :HOST-Argument for MAKE-PATHNAME
  # enforces a logical pathname as result.
  var object obj = allocate_logpathname();
  TheLogpathname(obj)->pathname_host =
    (boundp(STACK_5) ? (object)STACK_5 : NIL);
  STACK_5 = obj;
  # continue at MAKE-PATHNAME.
  C_make_pathname();
}

#endif

#ifdef USER_HOMEDIR
# (USER-HOMEDIR-PATHNAME [host]), CLTL p. 418
LISPFUN(user_homedir_pathname,seclass_default,0,1,norest,nokey,0,NIL) {
  DOUT("user-homedir-pathname:[host]",STACK_0);
 #if HAS_HOST
  STACK_0 = test_optional_host(STACK_0,false); # check Host
  if (!nullp(STACK_0)) {
   #if defined(PATHNAME_RISCOS)
    {
      var object pathname = allocate_pathname(); # new Pathname
      ThePathname(pathname)->pathname_host      = popSTACK();
     #if HAS_DEVICE
      ThePathname(pathname)->pathname_device    = NIL;
     #endif
      ThePathname(pathname)->pathname_directory = O(directory_homedir);
      ThePathname(pathname)->pathname_name      = NIL;
      ThePathname(pathname)->pathname_type      = NIL;
     #if HAS_VERSION
      ThePathname(pathname)->pathname_version   = NIL;
     #endif
      VALUES1(pathname);
    }
   #elif defined(PATHNAME_WIN32)
    # This is very primitive. Does Windows have the notion of homedirs on
    # remote hosts??
    {
      var object pathname = allocate_pathname(); # new Pathname
      ThePathname(pathname)->pathname_host      = popSTACK();
     #if HAS_DEVICE
      ThePathname(pathname)->pathname_device    = NIL;
     #endif
      ThePathname(pathname)->pathname_directory = O(directory_absolute);
      ThePathname(pathname)->pathname_name      = NIL;
      ThePathname(pathname)->pathname_type      = NIL;
     #if HAS_VERSION
      ThePathname(pathname)->pathname_version   = NIL;
     #endif
      VALUES1(pathname);
    }
   #else
      ??; /* FIXME for HAS_HOST & not WIN32 & not RISCOS */
   #endif
  } else { # no host given
    skipSTACK(1);
    VALUES1(O(user_homedir)); /* User-Homedir-Pathname */
  }
 #else /* HAS_HOST */
  test_optional_host(popSTACK()); # check Host and ignore
  VALUES1(O(user_homedir)); /* User-Homedir-Pathname */
 #endif
  DOUT("user-homedir-pathname:[ret]",value1);
}
#endif

# UP: copies a pathname.
# copy_pathname(pathname)
# > pathname: non-logical pathname
# < result: copy of the pathname, with the same components
# can trigger GC
local object copy_pathname (object pathname) {
  pushSTACK(pathname);
  var object newp = allocate_pathname();
  pathname = popSTACK();
 #if HAS_HOST
  ThePathname(newp)->pathname_host
    = ThePathname(pathname)->pathname_host;
 #endif
 #if HAS_DEVICE
  ThePathname(newp)->pathname_device
    = ThePathname(pathname)->pathname_device;
 #endif
  ThePathname(newp)->pathname_directory
    = ThePathname(pathname)->pathname_directory;
  ThePathname(newp)->pathname_name
    = ThePathname(pathname)->pathname_name;
  ThePathname(newp)->pathname_type
    = ThePathname(pathname)->pathname_type;
 #if HAS_VERSION
  ThePathname(newp)->pathname_version
    = ThePathname(pathname)->pathname_version;
 #endif
  return newp;
}

# Wildcards
# =========

#if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
# UP: check whether the object is wild
# wild_p(object)
# > object: normal simple-string or symbol
# < return: true when the object is wild
local bool wild_p (object obj, bool dirp) {
  if (simple_string_p(obj)) {
    var uintL len = Sstring_length(obj);
    if (len > 0) {
      SstringDispatch(obj,X, {
        var const cintX* charptr = &((SstringX)TheVarobject(obj))->data[0];
        dotimespL(len,len, {
          var chart ch = as_chart(*charptr++);
          if (wild_char_p(ch))
            return true;
        });
      });
    }
    return false;
  } else
    return eq(obj,S(Kwild)) || (dirp && eq(obj,S(Kwild_inferiors)));
}
#endif

#ifdef LOGICAL_PATHNAMES
# UP: check whether the obj is a string with '*' or a :WILD
# word_wild_p(object)
# > object: normal simple-string or symbol
# < return: true when the object is word-wild
local bool word_wild_p (object obj, bool dirp) {
  if (simple_string_p(obj)) {
    var uintL len = Sstring_length(obj);
    if (len > 0) {
      SstringDispatch(obj,X, {
        var const cintX* charptr = &((SstringX)TheVarobject(obj))->data[0];
        dotimespL(len,len, {
          if (chareq(as_chart(*charptr++),ascii('*')))
            return true;
        });
      });
    }
    return false;
  } else
    return eq(obj,S(Kwild)) || (dirp && eq(obj,S(Kwild_inferiors)));
}
#endif

# UP: checks, if the host-component of a pathname contains wildcards.
# has_host_wildcards(pathname)
# > pathname: pathname
# < result: true if (PATHNAME-HOST pathname) contains wildcards.
local bool has_host_wildcards (object pathname);
  # host can not contain wildcards.
#define has_host_wildcards(pathname)  (unused (pathname), false)

# UP: checks, if the device-component of a pathname contains wildcards.
# has_device_wildcards(pathname)
# > pathname: pathname
# < result: true if (PATHNAME-DEVICE pathname) contains wildcards.
local bool has_device_wildcards (object pathname) {
 #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname))
    return false;
 #endif
  # check device: = :WILD ?
  return eq(ThePathname(pathname)->pathname_device,S(Kwild));
 #else
  return false;
 #endif
}

# UP: checks, if the directory-component of a pathname contains wildcards.
# has_directory_wildcards(pathname)
# > pathname: pathname
# < result: true if (PATHNAME-DIRECTORY pathname) contains wildcards.
local bool has_directory_wildcards (object pathname) {
  # check directory:
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    var object directory = TheLogpathname(pathname)->pathname_directory;
    while (consp(directory = Cdr(directory)))
      if (word_wild_p(Car(directory),true))
        return true;
    return false;
  }
 #endif
  var object directory = ThePathname(pathname)->pathname_directory;
  while (consp(directory = Cdr(directory)))
    if (wild_p(Car(directory),true))
      return true;
  return false;
}

# UP: checks, if the name-component of a pathname contains wildcards.
# has_name_wildcards(pathname)
# > pathname: pathname
# < result: true if (PATHNAME-NAME pathname) contains wildcards.
local bool has_name_wildcards (object pathname) {
  # check name:
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname))
    return word_wild_p(TheLogpathname(pathname)->pathname_name,false);
 #endif
 #if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
  return wild_p(ThePathname(pathname)->pathname_name,false);
 #endif
  return false;
}

# UP: checks, if the type-component of a pathname contains wildcards.
# has_type_wildcards(pathname)
# > pathname: pathname
# < result: true if (PATHNAME-TYPE pathname) contains wildcards.
local bool has_type_wildcards (object pathname) {
  # check type:
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname))
    return word_wild_p(TheLogpathname(pathname)->pathname_type,false);
 #endif
 #if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
  return wild_p(ThePathname(pathname)->pathname_type,false);
 #endif
  return false;
}

# UP: checks, if the version-component of a pathname contains wildcards.
# has_version_wildcards(pathname)
# > pathname: pathname
# < result: true if (PATHNAME-VERSION pathname) contains wildcards.
local bool has_version_wildcards (object pathname) {
  # check version:
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pathname)) {
    if (eq(TheLogpathname(pathname)->pathname_version,S(Kwild)))
      return true;
    return false;
  }
 #endif
  return false;
}

# UP: checks, if any component of a pathname contains wildcards.
# has_some_wildcards(pathname)
# > pathname: pathname
# < result: true if pathname contains wildcards.
local bool has_some_wildcards (object pathname) {
  if (has_host_wildcards(pathname)) return true;
  if (has_device_wildcards(pathname)) return true;
  if (has_directory_wildcards(pathname)) return true;
  if (has_name_wildcards(pathname)) return true;
  if (has_type_wildcards(pathname)) return true;
  if (has_version_wildcards(pathname)) return true;
  return false;
}

# UP: checks, if a pathname contains no wildcards.
# check_no_wildcards(pathname);
# > pathname: pathname
local void check_no_wildcards (object pathname) {
  if (!has_some_wildcards(pathname)) # no wildcards found.
    return;
  # error-message, if the pathname contains wildcards:
  pushSTACK(pathname); # FILE-ERROR slot PATHNAME
  pushSTACK(pathname);
  fehler(file_error,GETTEXT("wildcards are not allowed here: ~"));
}

LISPFUN(wild_pathname_p,seclass_read,1,1,norest,nokey,0,NIL)
{ /* (WILD-PATHNAME-P pathname [field-key]), CLtL2 p. 623 */
  var object pathname = coerce_xpathname(STACK_1);
  var object key = STACK_0;
  var bool erg;
  if (missingp(key)) {
    erg = has_some_wildcards(pathname);
  } else if (eq(key,S(Khost))) {
    erg = has_host_wildcards(pathname);
  } else if (eq(key,S(Kdevice))) {
    erg = has_device_wildcards(pathname);
  } else if (eq(key,S(Kdirectory))) {
    erg = has_directory_wildcards(pathname);
  } else if (eq(key,S(Kname))) {
    erg = has_name_wildcards(pathname);
  } else if (eq(key,S(Ktype))) {
    erg = has_type_wildcards(pathname);
  } else if (eq(key,S(Kversion))) {
    erg = has_version_wildcards(pathname);
  } else {
    pushSTACK(key);                        # TYPE-ERROR slot DATUM
    pushSTACK(O(type_pathname_field_key)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(NIL);
    pushSTACK(S(Kversion));
    pushSTACK(S(Ktype));
    pushSTACK(S(Kname));
    pushSTACK(S(Kdirectory));
    pushSTACK(S(Kdevice));
    pushSTACK(S(Khost));
    pushSTACK(key);
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,
           GETTEXT("~: argument ~ should be ~, ~, ~, ~, ~, ~ or ~"));
  }
  VALUES_IF(erg); /* boolean value */
  skipSTACK(2);
}

# Wildcard Matching
# =================

# For the purposes of wildcard matching, according to CLHS, non-present
# components (i.e. NIL or a directory = (:RELATIVE)) are treated as wild.

#if defined(PATHNAME_NOEXT) || defined(LOGICAL_PATHNAMES)

  # UP: Matches a Wildcard-String ("Pattern") with a "Sample".
  # > pattern : Normal-Simple-String, with wildcards
  #           '?' for exactly 1 character
  #           '*' for arbitrary many characters
  # > sample  : Normal-Simple-String, that has to be matched
  # recursive implementation because of backtracking:
local bool wildcard_match_ab (uintL m_count, const chart* m_ptr,
                              uintL b_count, const chart* b_ptr);
local bool wildcard_match (object pattern, object sample) {
  if (eq(pattern,S(Kwild)) || eq(pattern,S(Kwild_inferiors)))
    return true;
  if (eq(pattern,S(Kup)) || eq(pattern,S(Kback)))
    return false;
  ASSERT(sstring_normal_p(pattern));
  ASSERT(sstring_normal_p(sample));
  return wildcard_match_ab(
                           /* m_count = */ Sstring_length(pattern),
                           /* m_ptr   = */ &TheSstring(pattern)->data[0],
                           /* b_count = */ Sstring_length(sample),
                           /* b_ptr   = */ &TheSstring(sample)->data[0]
                                           );
}
local bool wildcard_match_ab (uintL m_count, const chart* m_ptr,
                              uintL b_count, const chart* b_ptr) {
  var chart c;
  loop {
    if (m_count==0)
      return (b_count==0); # "" matches only ""
    m_count--;
    c = *m_ptr++; # next match-character
    if (chareq(c,ascii('?'))) { # wildcard '?'
      if (b_count==0) return false; # at least one character still has to come
      b_count--; b_ptr++; # it will be ignored
    } else if (chareq(c,ascii('*')))
      break; # wildcard '*' later
    else { # everything else must match exactly:
      if (b_count==0) return false;
      b_count--; if (!equal_pathchar(*b_ptr++,c)) return false;
    }
  }
  # Wildcard '*': Search next non-wildcard-character and also count the '?'
  # (because a sequence '*??*???***?' matches everything, that is as least as
  # long as the sequence of question marks). The '?' can also be utilized
  # immediately, because '*??*???***?' is equivalent to '??????*' .
  loop {
    if (m_count==0) return true; # wildcard at the end matches the rest.
    m_count--;
    c = *m_ptr++; # next match-character
    if (chareq(c,ascii('?'))) { # question mark: move forward, process instantly
      if (b_count==0) return false;
      b_count--; b_ptr++;
    }
    else if (!chareq(c,ascii('*')))
      break;
  }
  # c = next non-wildcard-character. Search it.
  loop {
    if (b_count==0) return false; # c not found
    b_count--;
    if (equal_pathchar(*b_ptr++,c)) {
      if (wildcard_match_ab(m_count,m_ptr,b_count,b_ptr))
        return true;
    }
  }
}

#endif

# UPs: matches a pathname-component ("Sample") and
# a pathname-component ("Pattern") at a time.
local bool host_match (object pattern, object sample, bool logical);
local bool device_match (object pattern, object sample, bool logical);
local bool directory_match (object pattern, object sample, bool logical);
local bool nametype_match (object pattern, object sample, bool logical);
local bool version_match (object pattern, object sample, bool logical);
local bool host_match (object pattern, object sample, bool logical) {
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (nullp(pattern)) return true;
    return equal(pattern,sample);
  }
 #endif
 #if HAS_HOST
  if (nullp(pattern)) return true;
  return equal(pattern,sample);
 #else
  return true;
 #endif
}
local bool device_match (object pattern, object sample, bool logical) {
 #if HAS_DEVICE
  #ifdef LOGICAL_PATHNAMES
  if (logical) {
    return true;
  }
  #endif
  if (nullp(pattern)) return true;
  #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  if (eq(pattern,S(Kwild))) return true;
  if (eq(sample,S(Kwild))) return false;
  #endif
  #if defined(PATHNAME_AMIGAOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  return equalp(pattern,sample);
  #else
  return equal(pattern,sample);
  #endif
 #else
  return true;
 #endif
}
local bool nametype_match_aux (object pattern, object sample, bool logical) {
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (eq(pattern,S(Kwild))) return true;
    if (eq(sample,S(Kwild))) return false;
    if (nullp(pattern)) {
      if (nullp(sample))
        return true;
      else
        return false;
    }
    if (nullp(sample)) {
      return false;
    }
    return wildcard_match(pattern,sample);
  }
 #endif
 #ifdef PATHNAME_NOEXT
  if (nullp(pattern)) {
    if (nullp(sample))
      return true;
    else
      return false;
  }
  if (nullp(sample)) {
    return false;
  }
  return wildcard_match(pattern,sample);
 #endif
}
local bool subdir_match (object pattern, object sample, bool logical) {
  if (eq(pattern,sample)) return true;
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (eq(pattern,S(Kwild))) return true;
    if (!simple_string_p(pattern) || !simple_string_p(sample)) return false;
    return wildcard_match(pattern,sample);
  }
 #endif
 #ifdef PATHNAME_NOEXT
  if (!simple_string_p(pattern) || !simple_string_p(sample)) return false;
  return wildcard_match(pattern,sample);
 #endif
}
# recursive implementation because of backtracking:
local bool directory_match_ab (object m_list, object b_list, bool logical);
local bool directory_match_ab (object m_list, object b_list, bool logical) {
  # Algorithm analogous to wildcard_match_ab.
  var object item;
  loop {
    if (atomp(m_list)) { return atomp(b_list); }
    item = Car(m_list); m_list = Cdr(m_list);
    if (eq(item,S(Kwild_inferiors))) break;
    if (atomp(b_list)) return false;
    if (!subdir_match(item,Car(b_list),logical)) return false;
    b_list = Cdr(b_list);
  }
  loop {
    if (atomp(m_list)) return true;
    item = Car(m_list); m_list = Cdr(m_list);
    if (!eq(item,S(Kwild_inferiors))) break;
  }
  loop {
    if (atomp(b_list)) return false;
    if (subdir_match(item,Car(b_list),logical)) {
      b_list = Cdr(b_list);
      if (directory_match_ab(m_list,b_list,logical)) return true;
    } else {
      b_list = Cdr(b_list);
    }
  }
}
local bool directory_match (object pattern, object sample, bool logical) {
  # compare pattern with O(directory_default):
  if (eq(Car(pattern),S(Krelative)) && nullp(Cdr(pattern)))
    return true;
  if (!boundp(sample)) return true;
  # match startpoint:
  if (!eq(Car(pattern),Car(sample)))
    return false;
  pattern = Cdr(pattern); sample = Cdr(sample);
  # match subdirs:
  return directory_match_ab(pattern,sample,logical);
}
local bool nametype_match (object pattern, object sample, bool logical) {
  if (missingp(pattern)) return true;
  return nametype_match_aux(pattern,sample,logical);
}
local bool version_match (object pattern, object sample, bool logical) {
  SDOUT("version_match:",pattern);
  SDOUT("version_match:",sample);
  if (!boundp(sample)) return true;
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (nullp(pattern) || eq(pattern,S(Kwild))) return true;
    return eql(pattern,sample);
  }
 #endif
 #if HAS_VERSION
  if (nullp(pattern) || eq(pattern,S(Kwild))) return true;
  if (eq(sample,S(Kwild))) return false;
  return eql(pattern,sample);
 #else
  return true;
 #endif
}

LISPFUNNR(pathname_match_p,2)
{ /* (PATHNAME-MATCH-P pathname wildname), CLtL2 p. 623 */
  # stack layout: pathname, wildname.
  var bool logical = false;
  STACK_1 = coerce_xpathname(STACK_1);
  STACK_0 = coerce_xpathname(STACK_0);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(STACK_1) && logpathnamep(STACK_0)) {
    logical = true;
  } else { # not both logical pathnames -> first convert into normal pathnames:
    STACK_1 = coerce_pathname(STACK_1);
    STACK_0 = coerce_pathname(STACK_0);
  }
 #endif
  DOUT("pathname-match-p:[s0]",STACK_0);
  DOUT("pathname-match-p:[s1]",STACK_1);
  var object wildname = popSTACK();
  var object pathname = popSTACK();
  if (!host_match(xpathname_host(logical,wildname),
                  xpathname_host(logical,pathname),
                  logical))
    goto no;
  if (!device_match(xpathname_device(logical,wildname),
                    xpathname_device(logical,pathname),
                    logical))
    goto no;
  if (!directory_match(xpathname_directory(logical,wildname),
                       xpathname_directory(logical,pathname),
                       logical))
    goto no;
  if (!nametype_match(xpathname_name(logical,wildname),
                      xpathname_name(logical,pathname),
                      logical))
    goto no;
  if (!nametype_match(xpathname_type(logical,wildname),
                      xpathname_type(logical,pathname),
                      logical))
    goto no;
  if (!version_match(xpathname_version(logical,wildname),
                     xpathname_version(logical,pathname),
                     logical))
    goto no;
 yes:
  VALUES1(T); return;
 no:
  VALUES1(NIL); return;
}

# (TRANSLATE-PATHNAME sample pattern1 pattern2) implemented as follows:
# 1. (PATHNAME-MATCH-P sample pattern1) while checking, extract
#    text items from the substitution pattern (:WILD -> "*").
# 2. Put the text items into pattern2 until pattern2 is full or all the
#    text items are used up
# 3. finally, (MERGE-PATHNAMES modified_pattern2 sample).

  # UP: Compare a wildcard string ("Pattern") with "Sample".
  # wildcard_diff(pattern,sample,previous,solutions);
  # > pattern: normal simple string, with substitution characters
  #           '?' for exactly 1 character
  #           '*' for as many characters as desired
  # > sample: normal simple string, to compare with
  # > previous: the already known result of comparison
  #             (reversed list of normal simple strings, NILs and lists)
  # > solutions: address of a list in the STACK, onto which the results of
  #              the comparisons (reversed list of normal simple strings
  #              and lists) have to be consed
  # can trigger GC

  # Here you need not Lisp or C, but PROLOG!
  # (PUSH previous solutions)
  #define push_solution()   do {                \
      var object new_cons = allocate_cons();    \
      Car(new_cons) = *previous;                \
      Cdr(new_cons) = *solutions;               \
      *solutions = new_cons;                    \
    } while(0)
  # (PUSH (CONS new_piece previous) solutions)
  #define push_solution_with(new_piece)   do {                  \
      pushSTACK(new_piece);                                     \
     {var object new_cons = allocate_cons();                    \
      Car(new_cons) = STACK_0; Cdr(new_cons) = *previous;       \
      STACK_0 = new_cons;                                       \
      new_cons = allocate_cons();                               \
      Car(new_cons) = popSTACK(); Cdr(new_cons) = *solutions;   \
      *solutions = new_cons;                                    \
    }} while(0)

#if defined(PATHNAME_NOEXT) || defined(LOGICAL_PATHNAMES)

# recursive implementation because of backtracking:
local void wildcard_diff_ab (object pattern, object sample,
                             uintL m_index, uintL b_index,
                             const gcv_object_t* previous,
                             gcv_object_t* solutions) {
  var chart cc;
  loop {
    if (m_index == Sstring_length(pattern)) {
      if (b_index == Sstring_length(sample))
        push_solution();
      return;
    }
    cc = schar(pattern,m_index++);
    if (chareq(cc,ascii('*')))
      break;
    if (b_index == Sstring_length(sample))
      return;
    if (chareq(cc,ascii('?'))) {
      # recursive call to wildcard_diff_ab(), with extended previous:
      cc = schar(sample,b_index++);
      pushSTACK(pattern); pushSTACK(sample);
      {
        var object new_string = allocate_string(1);
        TheS32string(new_string)->data[0] = as_cint(cc);
        pushSTACK(new_string);
      }
      {
        var object new_cons = allocate_cons();
        Car(new_cons) = STACK_0; Cdr(new_cons) = *previous;
        STACK_0 = new_cons; # (CONS ... previous)
      }
      wildcard_diff_ab(STACK_2,STACK_1,m_index,b_index,&STACK_0,solutions);
      skipSTACK(3);
      return;
    } else {
      if (!equal_pathchar(schar(sample,b_index++),cc))
        return;
    }
  }
  var uintL b_start_index = b_index;
  loop {
    # to reduce consing, intercept cases when wildcard_diff_ab() does nothing
    if (m_index == Sstring_length(pattern)
        ? b_index == Sstring_length(sample)
        : (cc = schar(pattern,m_index),
           chareq(cc,ascii('*')) || chareq(cc,ascii('?'))
           || (b_index < Sstring_length(sample)
               && equal_pathchar(schar(sample,b_index),cc)))) {
      # wildcard_diff_ab() recursive call, with extended previous:
      pushSTACK(pattern); pushSTACK(sample);
      # (SUBSTRING sample b_start_index b_index)
      pushSTACK(subsstring(sample,b_start_index,b_index));
      var object new_cons = allocate_cons();
      Car(new_cons) = STACK_0; Cdr(new_cons) = *previous;
      STACK_0 = new_cons; # (CONS ... previous)
      wildcard_diff_ab(STACK_2,STACK_1,m_index,b_index,&STACK_0,solutions);
      skipSTACK(1);
      sample = popSTACK(); pattern = popSTACK();
    }
    if (b_index == Sstring_length(sample))
      break;
    b_index++;
  }
}

local void wildcard_diff (object pattern, object sample,
                          const gcv_object_t* previous,
                          gcv_object_t* solutions) {
  ASSERT(sstring_normal_p(pattern));
  ASSERT(sstring_normal_p(sample));
  wildcard_diff_ab(pattern,sample,0,0,previous,solutions);
}

#endif

#if DEBUG_TRANSLATE_PATHNAME>1
# all arguments to *_diff are on stack - this should be safe
#define DEBUG_DIFF(f)                                         \
  printf("\n* " #f " [logical: %d]\n",logical);               \
  DOUT("",pattern); DOUT("",sample); DOUT("",*previous); DOUT("",*solutions)
#else
#define DEBUG_DIFF(f)
#endif
# UPs: compares a pathname-component ("Sample") and
# a pathname-component ("Pattern") at a time.
# can trigger GC
local void host_diff      (object pattern, object sample, bool logical,
                           const gcv_object_t* previous, gcv_object_t* solutions);
local void device_diff    (object pattern, object sample, bool logical,
                           const gcv_object_t* previous, gcv_object_t* solutions);
local void directory_diff (object pattern, object sample, bool logical,
                           const gcv_object_t* previous, gcv_object_t* solutions);
local void nametype_diff  (object pattern, object sample, bool logical,
                           const gcv_object_t* previous, gcv_object_t* solutions);
local void version_diff   (object pattern, object sample, bool logical,
                           const gcv_object_t* previous, gcv_object_t* solutions);
local void host_diff (object pattern, object sample, bool logical,
                      const gcv_object_t* previous, gcv_object_t* solutions) {
  DEBUG_DIFF(host_diff);
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (nullp(pattern)) {
      push_solution_with(sample); return;
    }
    if (!equal(pattern,sample)) return;
  } else
 #endif
  {
 #if HAS_HOST
    if (nullp(pattern)) {
      push_solution_with(sample); return;
    }
    if (!equal(pattern,sample)) return;
 #endif
  }
 #if HAS_HOST
  push_solution_with(S(Khost));
 #else
  push_solution();
 #endif
}
local void device_diff (object pattern, object sample, bool logical,
                        const gcv_object_t* previous, gcv_object_t* solutions) {
  DEBUG_DIFF(device_diff);
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
   #if HAS_DEVICE
    push_solution_with(S(Kdevice));
   #else
    push_solution();
   #endif
    return;
  }
 #endif
 #if HAS_DEVICE
  #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  if (nullp(pattern) || eq(pattern,S(Kwild))) {
    var object string = wild2string(sample);
    push_solution_with(string);
    return;
  }
  if (eq(sample,S(Kwild))) return;
  #endif
  #if defined(PATHNAME_AMIGAOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  if (nullp(pattern)) {
    var object string =
  #if defined(PATHNAME_AMIGAOS)
      sample;
  #endif
  #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
    wild2string(sample);
  #endif
    push_solution_with(string);
    return;
  }
  if (!equalp(pattern,sample)) return;
  #else
  if (!equal(pattern,sample)) return;
  #endif
  push_solution_with(S(Kdevice));
 #else /* HAS_DEVICE */
  push_solution();
 #endif
}
local void nametype_diff_aux (object pattern, object sample, bool logical,
                              const gcv_object_t* previous,
                              gcv_object_t* solutions) {
 #if defined(LOGICAL_PATHNAMES) || defined(PATHNAME_NOEXT)
  unused(logical);
  if (eq(pattern,S(Kwild))) {
    var object string = wild2string(sample);
    push_solution_with(string);
    return;
    }
  if (eq(sample,S(Kwild))) return;
  if (nullp(pattern)) {
    if (nullp(sample))
      push_solution();
    return;
  }
  if (nullp(sample))
    return;
  wildcard_diff(pattern,sample,previous,solutions);
 #endif
}
local void subdir_diff (object pattern, object sample, bool logical,
                        const gcv_object_t* previous, gcv_object_t* solutions)
{
  DEBUG_DIFF(subdir_diff);
  if (eq(pattern,sample)) {
    if (eq(sample,S(Kwild)))
      push_solution_with(O(wild_string));
    else
      push_solution();
    return;
  }
 #if defined(LOGICAL_PATHNAMES) || defined(PATHNAME_NOEXT)
  unused(logical);
  if (eq(pattern,S(Kwild))) {
    var object string = wild2string(sample);
    push_solution_with(string);
    return;
  }
  if (eq(sample,S(Kwild))) return;
  if (!simple_string_p(pattern) || !simple_string_p(sample)) return;
  wildcard_diff(pattern,sample,previous,solutions);
 #endif
}
# recursive implementation because of backtracking:
local void directory_diff_ab (object m_list, object b_list, bool logical,
                              const gcv_object_t* previous,
                              gcv_object_t* solutions) {
  # algorithm analogous to wildcard_diff_ab.
  var object item;
  if (atomp(m_list)) {
    if (atomp(b_list))
      push_solution();
    return;
  }
  item = Car(m_list); m_list = Cdr(m_list);
  if (!eq(item,S(Kwild_inferiors))) {
    if (atomp(b_list)) return;
    pushSTACK(NIL); pushSTACK(m_list); pushSTACK(Cdr(b_list));
    subdir_diff(item,Car(b_list),logical,previous,&STACK_2);
    # call directory_diff_ab() recursively, with extended previous:
    while (mconsp(STACK_2)) {
      pushSTACK(Car(STACK_2));
      directory_diff_ab(STACK_(1+1),STACK_(0+1),logical,&STACK_0,solutions);
      skipSTACK(1);
      STACK_2 = Cdr(STACK_2);
    }
    skipSTACK(3);
  } else {
    pushSTACK(b_list); # b_start_list := b_list
    loop {
      # to reduce consing, intercept cases when directory_diff_ab()
      # does nothing:
      if (atomp(m_list)
          ? atomp(b_list)
          : (eq(Car(m_list),S(Kwild_inferiors)) || !atomp(b_list))) {
        # call directory_diff_ab() recursively, with extended previous:
        pushSTACK(m_list); pushSTACK(b_list);
        pushSTACK(STACK_2); pushSTACK(b_list);
        funcall(L(ldiff),2); # (LDIFF b_start_list b_list)
        pushSTACK(value1);
        {
          var object new_piece = allocate_cons(); # (:DIRECTORY subdir1 ... subdirn)
          Car(new_piece) = S(Kdirectory); Cdr(new_piece) = STACK_0;
          STACK_0 = new_piece;
        }
        {
          var object new_cons = allocate_cons();
          Car(new_cons) = STACK_0; Cdr(new_cons) = *previous;
          STACK_0 = new_cons; # (CONS ... previous)
          directory_diff_ab(STACK_2,STACK_1,logical,&STACK_0,solutions);
          skipSTACK(1);
          b_list = popSTACK(); m_list = popSTACK();
        }
      }
      if (atomp(b_list))
        break;
      b_list = Cdr(b_list);
    }
    skipSTACK(1);
  }
}
#define SAMPLE_UNBOUND_CHECK \
  if (!boundp(sample)) { push_solution_with(pattern); return; }
local void directory_diff (object pattern, object sample, bool logical,
                           const gcv_object_t* previous,
                           gcv_object_t* solutions) {
  DEBUG_DIFF(directory_diff);
  SAMPLE_UNBOUND_CHECK;
  # compare pattern with O(directory_default) :
  if (eq(Car(pattern),S(Krelative)) && nullp(Cdr(pattern))) {
    # Augment the solution with the sample list - starting
    # with :ABSOLUTE or :RELATIVE, it will not fit for "**".
    push_solution_with(sample);
    return;
  }
  # compare startpoint:
  if (!eq(Car(pattern),Car(sample)))
    return;
  pattern = Cdr(pattern); sample = Cdr(sample);
  # compare subdirs:
  directory_diff_ab(pattern,sample,logical,previous,solutions);
}
local void nametype_diff (object pattern, object sample, bool logical,
                          const gcv_object_t* previous,
                          gcv_object_t* solutions) {
  DEBUG_DIFF(nametype_diff);
  SAMPLE_UNBOUND_CHECK;
  if (nullp(pattern)) {
    var object string = wild2string(sample);
    push_solution_with(string);
    return;
  }
  nametype_diff_aux(pattern,sample,logical,previous,solutions);
}
local void version_diff (object pattern, object sample, bool logical,
                         const gcv_object_t* previous, gcv_object_t* solutions)
{
  DEBUG_DIFF(version_diff);
  SAMPLE_UNBOUND_CHECK;
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (nullp(pattern) || eq(pattern,S(Kwild))) {
      var object string =
        (eq(sample,S(Kwild)) ? (object)O(wild_string) :
         integerp(sample) ? decimal_string(sample) # (SYS::DECIMAL-STRING sample)
         : NIL);
      push_solution_with(string);
      return;
    }
    if (eq(sample,S(Kwild))) return;
    if (!eql(pattern,sample)) return;
    push_solution();
    return;
  }
 #endif
 #if HAS_VERSION
  if (nullp(pattern) || eq(pattern,S(Kwild))) {
    var object string =
      (eq(sample,S(Kwild)) ? O(wild_string) :
       integerp(sample) ? decimal_string(sample) # (SYS::DECIMAL-STRING sample)
       : NIL);
    push_solution_with(string);
    return;
  }
  if (eq(sample,S(Kwild))) return;
  if (!eql(pattern,sample)) return;
  push_solution();
 #else
  push_solution_with(NIL);
 #endif
}

#undef push_solution_with
#undef push_solution
#undef DEBUG_DIFF
#undef SAMPLE_UNBOUND_CHECK

# Each substitution is a list of Normal-Simple-Strings or Lists.
# (The Lists come into being with :WILD-INFERIORS in directory_diff().)
# A Normal-Simple-String fits only with '?' or '*' or :WILD,
# A List fits only with :WILD-INFERIORS.

#ifdef LOGICAL_PATHNAMES

# On insertion of pieces of normal pathnames in logical pathnames:
# Conversion to capital letters.
# logical_case(string)
# > string: Normal-Simple-String or Symbol/Number
# < result: converted Normal-Simple-String or the same Symbol/Number
# can trigger GC
local object logical_case (object string) {
  if (!simple_string_p(string))
    return string;
  return string_upcase(string);
}
# The same, recursive like with SUBST:
local object subst_logical_case (object obj);
local object subst_logical_case (object obj) {
  SUBST_RECURSE(logical_case(obj),subst_logical_case);
}

# On insertion of pieces of logical pathnames in normal pathnames:
# Conversion to capital letters.
# customary_case(string)
# > string: Normal-Simple-String or Symbol/Number
# < result: converted Normal-Simple-String or the same Symbol/Number
# can trigger GC
local object customary_case (object string) {
  if (!simple_string_p(string))
    return string;
 #if defined(PATHNAME_UNIX) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32) || defined(PATHNAME_RISCOS)
  # operating system with preference for lowercase letters
  return string_downcase(string);
 #endif
 #ifdef PATHNAME_AMIGAOS
  # operating system with preference for Capitalize
  string = copy_string(string);
  pushSTACK(string);
  nstring_capitalize(&TheSstring(string)->data[0],Sstring_length(string));
  string = popSTACK();
  simple_array_to_storage(string);
  return string;
 #endif
}
# The same, recursive like with SUBST:
local object subst_customary_case (object obj) {
  SUBST_RECURSE(customary_case(obj),subst_customary_case);
}

#endif

#undef SUBST_RECURSE

# Apply substitution SUBST to the PATTERN.
# translate_pathname(&subst,pattern)
local object translate_pathname (object* subst, object pattern);
# Pop the CAR of *subst and return it.
#define RET_POP(subst)  \
  { var object ret = Car(*subst); *subst = Cdr(*subst); return ret; }
# is the value trivial enough to ensure a trivial action?
#define TRIVIAL_P(val) (simple_string_p(val)||nullp(val))
# is the value simple enough to ensure a simple action?
#define SIMPLE_P(val) (TRIVIAL_P(val)||eq(val,S(Kwild)))
# translate_host(&subst,pattern,logical) etc.
# returns the appropriate replacement for host etc.; shortens subst;
# returns nullobj on failure
# may trigger GC
local object translate_host (gcv_object_t* subst, object pattern, bool logical);
local object translate_device (gcv_object_t* subst, object pattern, bool logical);
local object translate_subdir (gcv_object_t* subst, object pattern, bool logical);
local object translate_directory (gcv_object_t* subst, object pattern, bool logical);
local object translate_nametype (gcv_object_t* subst, object pattern, bool logical);
local object translate_version (gcv_object_t* subst, object pattern, bool logical);
#if DEBUG_TRANSLATE_PATHNAME
# all arguments to translate_* should be on stack - this should be safe
#define DEBUG_TRAN(f)                                         \
  printf("\n* " #f " [logical: %d]\n",logical);               \
  DOUT("",*subst); DOUT("",pattern)
#else
#define DEBUG_TRAN(f)
#endif
local object translate_host (gcv_object_t* subst, object pattern, bool logical) {
  DEBUG_TRAN(translate_host);
#define TRAN_HOST(subst,pattern)                        \
        if (nullp(pattern) && mconsp(*subst)) {         \
          if (TRIVIAL_P(Car(*subst))) {                 \
            RET_POP(subst);                             \
          } else if (eq(Car(*subst),S(Khost))) {        \
            *subst = Cdr(*subst);                       \
            return pattern;                             \
          } else                                        \
            return nullobj;                             \
        }
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    TRAN_HOST(subst,pattern);
  } else
 #endif
  {
 #if HAS_HOST
    TRAN_HOST(subst,pattern);
 #endif
  }
 #if HAS_HOST
  if (eq(Car(*subst),S(Khost)))
    *subst = Cdr(*subst);
 #endif
  return pattern;
 #undef TRAN_HOST
}
local object translate_device (gcv_object_t* subst, object pattern, bool logical) {
  DEBUG_TRAN(translate_device);
 #if HAS_DEVICE
  #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if (eq(Car(*subst),S(Kdevice)))
      { *subst = Cdr(*subst); }
    return pattern;
  }
  #endif
  #if defined(PATHNAME_AMIGAOS) || defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  if (nullp(pattern) && mconsp(*subst))
  #else
  if ((nullp(pattern) || eq(pattern,S(Kwild))) && mconsp(*subst))
  #endif
    {
      if (TRIVIAL_P(Car(*subst))) {
        RET_POP(subst);
      } else if (eq(Car(*subst),S(Kdevice))) {
        *subst = Cdr(*subst);
        return pattern;
      } else
        return nullobj;
    }
  if (eq(Car(*subst),S(Kdevice)))
    *subst = Cdr(*subst);
 #endif
  return pattern;
}
local object translate_nametype_aux (gcv_object_t* subst, object pattern,
                                     bool logical) {
  DEBUG_TRAN(translate_nametype_aux);
  if (eq(pattern,S(Kwild)) && mconsp(*subst)) {
    if (TRIVIAL_P(Car(*subst))) {
      var object erg = Car(*subst); *subst = Cdr(*subst);
      return (nullp(erg) ? (object)O(empty_string) : erg);
    } else
      return nullobj;
  }
  if (simple_string_p(pattern)) {
    pushSTACK(pattern); # save pattern
    var gcv_object_t* pattern_ = &STACK_0;
    var uintL len = Sstring_length(pattern);
    var uintL index = 0;
    var uintL stringcount = 0; # number of strings on the stack
    loop {
      var uintL last_index = index;
      var chart cc;
      # search next wildcard-character:
      pattern = *pattern_;
      while (index != len) {
        cc = schar(pattern,index);
        if ((chareq(cc,ascii('*')) # wildcard for arbitrary many characters
             || (!logical && singlewild_char_p(cc))) # wildcard for exactly one character
            && mconsp(*subst))
          break;
        index++;
      }
      # Next substring on the stack:
      pushSTACK(subsstring(pattern,last_index,index)); # (SUBSTRING pattern last_index index)
      stringcount++;
      # finished?
      if (index == len)
        break;
      # replace wildcard:
      if (TRIVIAL_P(Car(*subst))) {
        var object s = Car(*subst);
        pushSTACK(nullp(s) ? (object)O(empty_string) : s);
        *subst = Cdr(*subst); stringcount++;
      } else {
        skipSTACK(stringcount+1); return nullobj;
      }
      index++;
    }
    value1 = string_concat(stringcount);
    skipSTACK(1); # skip pattern
    return value1;
  }
  return pattern;
}
local object translate_subdir (gcv_object_t* subst, object pattern, bool logical) {
  DEBUG_TRAN(translate_subdir);
 #ifdef LOGICAL_PATHNAMES
  if (logical)
    return translate_nametype_aux(subst,pattern,logical);
 #endif
 #ifdef PATHNAME_NOEXT
  return translate_nametype_aux(subst,pattern,false);
 #endif
}
local object translate_directory (gcv_object_t* subst, object pattern,
                                  bool logical) {
  DEBUG_TRAN(translate_directory);
  # compare pattern with O(directory_default):
  if (eq(Car(pattern),S(Krelative)) && nullp(Cdr(pattern))
      && mconsp(*subst) && mconsp(Car(*subst))) {
    var object list = Car(*subst); *subst = Cdr(*subst);
    if (eq(Car(list),S(Kabsolute)) || eq(Car(list),S(Krelative)))
      return copy_list(list);
    else
      return nullobj;
  }
  # if subst is :relative while pattern is :absolute, nothing is to be done
  if (eq(Car(pattern),S(Kabsolute)) && mconsp(*subst)
      && mconsp(Car(*subst)) && eq(Car(Car(*subst)),S(Krelative))) {
    *subst = Cdr(*subst);
    return copy_list(pattern);
  }
  var uintL itemcount = 0; # number of items on the stack
  # Startpoint:
  pushSTACK(Car(pattern)); pattern = Cdr(pattern); itemcount++;
  # subdirs:
  while (consp(pattern)) {
    var object item = Car(pattern);
    pattern = Cdr(pattern);
    if (eq(item,S(Kwild_inferiors))) {
      if (mconsp(*subst)) {
        if (consp(Car(*subst)) && eq(Car(Car(*subst)),S(Kdirectory))) {
          var object list = Cdr(Car(*subst)); *subst = Cdr(*subst);
          while (consp(list)) {
            pushSTACK(Car(list)); list = Cdr(list); itemcount++;
          }
        } else {
          skipSTACK(itemcount); return nullobj;
        }
      } else {
        pushSTACK(item); itemcount++;
      }
    } else {
      pushSTACK(pattern); # save pattern
      item = translate_subdir(subst,item,logical);
      if (eq(item,nullobj)) { skipSTACK(itemcount+1); return nullobj; }
      pattern = STACK_0; STACK_0 = item; itemcount++;
    }
  }
  return listof(itemcount);
}
local object translate_nametype (gcv_object_t* subst, object pattern, bool logical) {
  DEBUG_TRAN(translate_nametype);
  if (nullp(pattern) && mconsp(*subst)) {
    if (SIMPLE_P(Car(*subst))) {
      RET_POP(subst);
    } else
      return nullobj;
  }
  return translate_nametype_aux(subst,pattern,logical);
}
local object translate_version (gcv_object_t* subst, object pattern, bool logical) {
  DEBUG_TRAN(translate_version);
 #ifdef LOGICAL_PATHNAMES
  if (logical) {
    if ((nullp(pattern) || eq(pattern,S(Kwild))) && mconsp(*subst)) {
      if (SIMPLE_P(Car(*subst))) {
        var object erg = Car(*subst); *subst = Cdr(*subst);
        if (nullp(erg))
          return erg;
        pushSTACK(erg); funcall(L(parse_integer),1);
        return value1;
      } else
        return nullobj;
    }
    return pattern;
  }
 #endif
 #if HAS_VERSION
  if ((nullp(pattern) || eq(pattern,S(Kwild))) && mconsp(*subst)) {
    if (SIMPLE_P(Car(*subst))) {
      var object erg = Car(*subst); *subst = Cdr(*subst);
      if (nullp(erg))
        return erg;
      pushSTACK(erg); funcall(L(parse_integer),1);
      return value1;
    } else
      return nullobj;
      }
  return pattern;
 #else
  if (mconsp(*subst)) {
    if (SIMPLE_P(Car(*subst))) {
      *subst = Cdr(*subst); return NIL;
    } else
      return nullobj;
  }
  return NIL;
 #endif
}
#undef SIMPLE_P
#undef TRIVIAL_P
#undef RET_POP
#undef DEBUG_TRAN
local object translate_pathname (gcv_object_t* subst, object pattern) {
  var bool logical = false;
  var object item;
  pushSTACK(*subst); # save subst for the error message
  pushSTACK(pattern);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(pattern))
    logical = true;
 #endif
#define GET_ITEM(what,xwhat,where,skip)                                     \
   item = translate_##what(subst,xpathname_##xwhat(logical,where),logical); \
   if (eq(item,nullobj)) { skipSTACK(skip); goto subst_error; }             \
   DOUT(#what " > ",item); pushSTACK(S(K##xwhat)); pushSTACK(item)
#define GET_ITEM_S(y,x,w) GET_ITEM(y,x,STACK_(w),w)
  # build together arguments for MAKE-PATHNAME:
  GET_ITEM(host,host,pattern,0);
 #if HAS_DEVICE
  GET_ITEM_S(device,device,2);
 #endif
  GET_ITEM_S(directory,directory,2+2*HAS_DEVICE);
  GET_ITEM_S(nametype,name,2+2*HAS_DEVICE+2);
  GET_ITEM_S(nametype,type,2+2*HAS_DEVICE+4);
  GET_ITEM_S(version,version,2+2*HAS_DEVICE+6);
  # All replacement pieces must be consumed!
  if (mconsp(*subst)) { skipSTACK(2+2*HAS_DEVICE+8); goto subst_error; }
  # call (MAKE-PATHNAME ...) resp. (SYS::MAKE-LOGICAL-PATHNAME ...) :
 #ifdef LOGICAL_PATHNAMES
  if (logical)
    funcall(L(make_logical_pathname),2+2*HAS_DEVICE+8);
  else
 #endif
        funcall(L(make_pathname),2+2*HAS_DEVICE+8);
  skipSTACK(2);
  return value1;
 subst_error: # Error because of nullobj.
  # stack layout: subst, pattern.
  pushSTACK(STACK_1);
  pushSTACK(S(translate_pathname));
  fehler(error,GETTEXT("~: replacement pieces ~ do not fit into ~"));
}
#undef GET_ITEM
#undef GET_ITEM_S

# (TRANSLATE-PATHNAME sample pattern1 pattern2 [:all] [:merge]), CLtL2 p. 624
# :all = T --> return a list of all fitting pathnames
# :all = NIL --> Error, if more than one pathname fits
# :merge = NIL --> skip last MERGE-PATHNAMES step
LISPFUN(translate_pathname,seclass_default,3,0,norest,key,2,
        (kw(all),kw(merge))) {
  # stack layout: sample, pattern1, pattern2, all, merge.
  var bool logical = false; # Flag, if sample and pattern are logical pathnames
  var bool logical2 = false; # Flag, if pattern2 is a logical pathname
  STACK_4 = coerce_xpathname(STACK_4);
  STACK_3 = coerce_xpathname(STACK_3);
  STACK_2 = coerce_xpathname(STACK_2);
 #ifdef LOGICAL_PATHNAMES
  if (logpathnamep(STACK_4) && logpathnamep(STACK_3)) {
    logical = true;
  } else { # not both logical pathnames -> first convert into normal pathnames:
    STACK_4 = coerce_pathname(STACK_4);
    STACK_3 = coerce_pathname(STACK_3);
  }
  if (logpathnamep(STACK_2))
    logical2 = true;
 #endif
  # 1. step: construct list of all fitting substitutions.
  pushSTACK(NIL); pushSTACK(NIL);
  host_diff(xpathname_host(logical,STACK_(3+2)),
            xpathname_host(logical,STACK_(4+2)),
            logical,&STACK_1,&STACK_0);
  while (mconsp(STACK_0)) {
    pushSTACK(Car(STACK_0)); pushSTACK(NIL);
    device_diff(xpathname_device(logical,STACK_(3+4)),
                xpathname_device(logical,STACK_(4+4)),
                logical,&STACK_1,&STACK_0);
    while (mconsp(STACK_0)) {
      pushSTACK(Car(STACK_0)); pushSTACK(NIL);
      directory_diff(xpathname_directory(logical,STACK_(3+6)),
                     xpathname_directory(logical,STACK_(4+6)),
                     logical,&STACK_1,&STACK_0);
      while (mconsp(STACK_0)) {
        pushSTACK(Car(STACK_0)); pushSTACK(NIL);
        nametype_diff(xpathname_name(logical,STACK_(3+8)),
                      xpathname_name(logical,STACK_(4+8)),
                      logical,&STACK_1,&STACK_0);
        while (mconsp(STACK_0)) {
          pushSTACK(Car(STACK_0)); pushSTACK(NIL);
          nametype_diff(xpathname_type(logical,STACK_(3+10)),
                        xpathname_type(logical,STACK_(4+10)),
                        logical,&STACK_1,&STACK_0);
          while (mconsp(STACK_0)) {
            pushSTACK(Car(STACK_0));
            version_diff(xpathname_version(logical,STACK_(3+11)),
                         xpathname_version(logical,STACK_(4+11)),
                         logical,&STACK_0,&STACK_10);
            skipSTACK(1);
            STACK_0 = Cdr(STACK_0);
          }
          skipSTACK(2);
          STACK_0 = Cdr(STACK_0);
        }
        skipSTACK(2);
        STACK_0 = Cdr(STACK_0);
      }
      skipSTACK(2);
      STACK_0 = Cdr(STACK_0);
    }
    skipSTACK(2);
    STACK_0 = Cdr(STACK_0);
  }
  skipSTACK(1);
  # stack layout: ..., solutions.
  if (matomp(STACK_0)) {
    pushSTACK(STACK_(3+1));
    pushSTACK(STACK_(4+1+1));
    pushSTACK(S(translate_pathname));
    fehler(error,GETTEXT("~: ~ is not a specialization of ~"));
  }
  # 2.,3. step:
  pushSTACK(NIL); # pathnames := '()
  while (mconsp(STACK_1)) { # traverse solutions
    var object solutions = STACK_1;
    STACK_1 = Cdr(solutions);
    {
      var object solution = reverse(Car(solutions)); # reverse list solution
      # 2. step: insert substitution in pattern2.
     #ifdef LOGICAL_PATHNAMES
      # convert capital-/small letters suitably:
      if (!logical) {
        if (logical2)
          solution = subst_logical_case(solution);
      } else {
        if (!logical2)
          solution = subst_customary_case(solution);
      }
     #endif
      pushSTACK(solution);
      STACK_0 = translate_pathname(&STACK_0,STACK_(2+1+2));
    }
    # 3. step: (MERGE-PATHNAMES modified_pattern2 sample :WILD T)
    if (!nullp(STACK_(0+1+2))) # query :MERGE-Argument
      if (has_some_wildcards(STACK_0)) { # MERGE-PATHNAMES may be unnecessary
        pushSTACK(STACK_(4+1+2)); pushSTACK(unbound);
        pushSTACK(S(Kwild)); pushSTACK(T);
        funcall(L(merge_pathnames),5);
        pushSTACK(value1);
      }
    { # (PUSH pathname pathnames)
      var object new_cons = allocate_cons();
      Car(new_cons) = popSTACK(); Cdr(new_cons) = STACK_0;
      STACK_0 = new_cons;
    }
  }
  # 4. step: (DELETE-DUPLICATES pathnames :TEST #'EQUAL)
  pushSTACK(S(Ktest)); pushSTACK(L(equal));
  funcall(L(delete_duplicates),3);
  # stack layout: ..., nil.
  if (missingp(STACK_(1+1))) { /* query :ALL-Argument */
    if (mconsp(Cdr(value1))) {
      pushSTACK(value1);
      pushSTACK(STACK_(2+2));
      pushSTACK(STACK_(3+3));
      pushSTACK(STACK_(4+4));
      pushSTACK(S(translate_pathname));
      fehler(error,GETTEXT("(~ ~ ~ ~) is ambiguous: ~"));
    }
    value1 = Car(value1);
  }
  mv_count=1;
  skipSTACK(5+1);
}

# UP: tests, if the name of a pathname is =NIL.
# namenullp(pathname)
# > pathname: non-logical pathname
  # local bool namenullp (object pathname);
  # local bool namenullp(pathname)
  #   { return nullp(ThePathname(pathname)->pathname_name); }
  #define namenullp(path)  (nullp(ThePathname(path)->pathname_name))

# error, if directory does not exist
# > obj: pathname or (better) erroneous component
nonreturning_function(local, fehler_dir_not_exists, (object obj)) {
  pushSTACK(obj); # FILE-ERROR slot PATHNAME
  pushSTACK(obj);
  fehler(file_error,GETTEXT("nonexistent directory: ~"));
}

# error, if a file already exits
# > STACK_0: pathname
nonreturning_function(local, fehler_file_exists, (void)) {
  # STACK_0 = FILE-ERROR slot PATHNAME
  pushSTACK(STACK_0); # pathname
  pushSTACK(TheSubr(subr_self)->name);
  fehler(file_error,GETTEXT("~: file ~ already exists"));
}

#ifdef LOGICAL_PATHNAMES
# An "absolute pathname" is always a non-logical pathname, poss.
# with further restrictions.
#endif

#if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)

# An "absolute pathname" is a pathname, whose device is a checked
# String and directory does not contain :RELATIVE, :CURRENT, :PARENT.

# UP: returns a namestring of a pathname for the operating system.
# OSnamestring(dir_namestring)
# > STACK_0: non-logical pathname
# > dir_namestring: directory-namestring (for DOS)
# < result: namestring (for DOS)
# can trigger GC
local object OSnamestring (object dir_namestring) {
  var uintC stringcount;
  pushSTACK(dir_namestring); # Directory-Namestring as 1. String
  stringcount = file_namestring_parts(STACK_(0+1)); # Strings for the filename
  return string_concat(1+stringcount); # concatenate
}

#ifdef EMUNIX

# query working directory on a given drive:
# getwdof(&buf,drive)
# > uintB* &buf: addresse of a path-buffer
# > uintB drive: drive (0=A, 1=B, ...)
# < result: <0 if error
#define getwdof(buf,drive)  _getcwd(buf,drive)

# returns the current directory of a drive.
# getwd_of(path,drive)
# > uintB drive: drive-(capital-)letter
# > uintB* path: room for the current directory
# < path: path of the current directory, with '/' as separator and as beginning
# < result: <0 if error
#define getwd_of(path,drive)  _getcwd1(path,drive)

#endif # EMUNIX

# UP: tests, if a drive exists.
# > uintB drive: drive-(capital-)letter
# < bool result: if this drive exists and is responsive
local bool good_drive (uintB drive);
#ifdef EMUNIX
local bool good_drive (uintB drive) {
  # Method (see HELPPC/misc.txt):
  # 1. save current drive  (INT 0x21,0x19)
  # 2. set current drive  (INT 0x21,0xE)
  # 3. get current drive  (INT 0x21,0x19)
  # 4. if current drive == drive requested
  #       then drive exists
  #       else drive does not exist
  # 5. reset original drive  (INT 0x21,0xE)
  var bool result;
  begin_system_call();
  {
    var uintB orig_drive = _getdrive();
    _chdrive(drive);
    result = (_getdrive() == drive);
    _chdrive(orig_drive);
  }
  end_system_call();
  return result;
  # Alternative:
  # {
  #   var uintB drv[3];
  #   var uintB fsys[16];
  #   drv[0] = drive; drv[1] = ':'; drv[2] = '\0';
  #   begin_system_call();
  #   var int result = _filesys(drv,&fsys,sizeof(fsys));
  #   end_system_call();
  #   return (result==0);
  # }
}
#endif
#ifdef WIN32_NATIVE
local bool good_drive (uintB drive) {
  var char rootpath[4];
  var DWORD result;
  rootpath[0] = drive;
  rootpath[1] = ':';
  rootpath[2] = '\\';
  rootpath[3] = '\0';
  begin_system_call();
  result = GetDriveType(rootpath);
  switch (result) {
    case DRIVE_UNKNOWN:
      end_system_call();
      return false;
    case DRIVE_NO_ROOT_DIR:
      # Distinguish NFS mounts from nonassigned drive letters:
      result = GetFileAttributes(rootpath);
      end_system_call();
      return !(result==0xFFFFFFFF);
    default:
      end_system_call();
      return true;
  }
}
#if 0
# The following fails to recognize some (but not all) NFS mounts on WinNT.
local bool good_drive_notsogood (uintB drive) {
  var DWORD drives_bitmask;
  begin_system_call();
  drives_bitmask = GetLogicalDrives();
  end_system_call();
  return ((drives_bitmask & ((DWORD)1 << (drive-'A'))) != 0);
}
#endif
#endif /* EMUNIX */

# UP: returns the current drive.
# < char drive: drive-(capital-)letter
local char default_drive (void);
#ifdef EMUNIX
local char default_drive (void) {
  var uintB result;
  begin_system_call();
  result = _getdrive();
  end_system_call();
  return result;
}
#endif
#ifdef WIN32_NATIVE
local char default_drive (void) {
  var DWORD path_buflen = _MAX_PATH;
  var char* path_buffer = (char*)alloca(path_buflen);
  var DWORD result;
  begin_system_call();
  result = GetCurrentDirectory(path_buflen,path_buffer);
  if (!result) { OS_error(); }
  if (result >= path_buflen) {
    path_buflen = result; path_buffer = (char*)alloca(path_buflen);
    result = GetCurrentDirectory(path_buflen,path_buffer);
    if (!result) { OS_error(); }
  }
  end_system_call();
  ASSERT(path_buffer[1]==':');
  ASSERT(path_buffer[2]=='\\');
  return as_cint(up_case(as_chart(path_buffer[0])));
}
#endif

# UP: returns the current directory on the given drive.
# > uintB drive: drive-(capital-)letter
# > object pathname: pathname (for error-reporting purposes)
# < result: current directory (as pathname)
# can trigger GC
local object default_directory_of (uintB drive, object pathname) {
# working directory (of DOS) is the current directory:
 #if defined(WIN32_NATIVE)
  var char currpath[4];
  var DWORD path_buflen = _MAX_PATH;
  var char* path_buffer = (char*)alloca(path_buflen+1);
  var char* dummy;
  var DWORD result;
  currpath[0] = drive;
  currpath[1] = ':';
  currpath[2] = '.'; # this dot is actually not needed
  currpath[3] = '\0';
  begin_system_call();
  result = GetFullPathName(currpath,path_buflen,path_buffer,&dummy);
  if (!result) { end_system_call(); OS_file_error(pathname); }
  if (result >= path_buflen) {
    path_buflen = result; path_buffer = (char*)alloca(path_buflen+1);
    result = GetFullPathName(currpath,path_buflen,path_buffer,&dummy);
    if (!result) { end_system_call(); OS_file_error(pathname); }
  }
  end_system_call();
  { # poss. add a '\' at the end:
    var char* path_end = &path_buffer[asciz_length(path_buffer)];
    if (!(path_end[-1]=='\\')) { path_end[0] = '\\'; path_end[1] = '\0'; }
  }
 #else
  var char path_buffer[3+MAXPATHLEN]; # cf. GETWD(3)
  path_buffer[0] = drive; path_buffer[1] = ':';
  # file working directory in path_buffer:
  begin_system_call();
  getwd_of(&path_buffer[2],drive);
  end_system_call();
 #endif
  # Hack by DJ (see GO32/EXPHDLR.C) and EM (see LIB/MISC/_GETCWD1.C):
  # converts all '\' to '/' and all captial- to small letters (only cosmetics,
  # because DOS and our PARSE-NAMESTRING also understand filenames with '/'
  # instead of '\').
  # convert to pathname:
  return asciz_dir_to_pathname(&path_buffer[0],O(pathname_encoding));
}

# UP: Fills default-drive and default-directory into a pathname.
# use_default_dir(pathname)
# > pathname: non-logical pathname with Device /= :WILD
# < result: new absolute pathname
# can trigger GC
local object use_default_dir (object pathname) {
  # first copy the pathname:
  pathname = copy_pathname(pathname);
  pushSTACK(pathname);
  # stack layout: pathname.
  # default for the device:
 #if HAS_HOST # PATHNAME_WIN32
  if (nullp(ThePathname(pathname)->pathname_host))
 #endif
    if (nullp(ThePathname(pathname)->pathname_device)) { # no device specified?
      # take the default-drive instead:
      ThePathname(pathname)->pathname_device = O(default_drive);
    }
  { # Default for the directory:
    var object subdirs = ThePathname(pathname)->pathname_directory;
    # Does pathname-directory start with :RELATIVE ?
    if (eq(Car(subdirs),S(Krelative))) {
      # yes -> replace :RELATIVE with the default-directory:
      pushSTACK(Cdr(subdirs));
     #if HAS_HOST # PATHNAME_WIN32
      if (!nullp(ThePathname(pathname)->pathname_host)) {
        # We do not have the concept of a current directory on a
        # remote host. Simply use :ABSOLUTE instead of :RELATIVE.
        subdirs = allocate_cons();
        Car(subdirs) = S(Kabsolute);
        Cdr(subdirs) = popSTACK();
      } else
     #endif
      {
        var uintB drive = as_cint(TheSstring(ThePathname(pathname)->pathname_device)->data[0]);
        var object default_dir = default_directory_of(drive,pathname);
        # default_dir (ein Pathname) is finished.
        # Replace :RELATIVE with default-subdirs, i.e.
        # form  (append default-subdirs (cdr subdirs))
        #      = (nreconc (reverse default-subdirs) (cdr subdirs))
        var object temp = ThePathname(default_dir)->pathname_directory;
        temp = reverse(temp);
        subdirs = nreconc(temp,popSTACK());
      }
    }
    # traverse list and freshly cons up, thereby process '.\' and '..\'
    # and '...\'  (do not leave it to DOS):
    pushSTACK(subdirs);
    pushSTACK(NIL);
    # stack layout: pathname, subdir-oldlist, subdir-newlist.
    while (mconsp(STACK_1)) { # until oldlist is finished:
      var object subdir = Car(STACK_1); # next subdir
      if (equal(subdir,O(dot_string))) {
        # = :CURRENT -> leave newlist unchanged
      } else if (equal(subdir,O(dotdot_string))) {
        # = :PARENT -> shorten newlist by one:
        if (matomp(Cdr(STACK_0))) { # newlist (except for :ABSOLUTE) empty ?
          # :PARENT from "\" returns Error
          pushSTACK(STACK_2); # FILE-ERROR slot PATHNAME
          pushSTACK(O(backslash_string)); # "\\"
          pushSTACK(directory_namestring(STACK_(2+2))); # directory of pathname
          fehler(file_error,GETTEXT("no directory ~ above ~"));
        }
        if (eq(Car(STACK_0),S(Kwild_inferiors))) { # newlist starts with '...\' ?
          # :PARENT from "...\" returns Error
          pushSTACK(STACK_2); # FILE-ERROR slot PATHNAME
          pushSTACK(directory_namestring(STACK_(2+1))); # directory of pathname
          fehler(file_error, # '"..\\" after "...\\" is inadmissible: ~'
                 GETTEXT("\"..\\\\\" after \"...\\\\\" is invalid: ~"));
        }
        STACK_0 = Cdr(STACK_0);
      } else { # (also if :ABSOLUTE !)
        # lengthen newlist by one:
        pushSTACK(subdir);
        var object new_cons = allocate_cons();
        Car(new_cons) = popSTACK();
        Cdr(new_cons) = STACK_0;
        STACK_0 = new_cons;
      }
      STACK_1 = Cdr(STACK_1);
    }
    subdirs = nreverse(popSTACK()); # newlist, reverse again
    skipSTACK(1);
    # stack layout: pathname.
    pathname = popSTACK();
    ThePathname(pathname)->pathname_directory =
      simplify_directory(subdirs); # enter into the pathname
  }
  return pathname;
}

#ifdef WIN32_NATIVE

/* UP: translates short name to full name
 > shortname: old DOS 8.3 pathname
 < fullname: buffer should be not less than MAX_PATH
 < result: true on success */
bool FullName (LPCSTR shortname, LPSTR fullname) {
  var WIN32_FIND_DATA wfd;
  var char drive[_MAX_DRIVE];
  var char dir[_MAX_DIR];
  var char fname[_MAX_FNAME];
  var char ext[_MAX_EXT];
  var char current[_MAX_PATH];
  var HANDLE h = NULL;
  var *fullname = 0; /* also first loop flag */
  var char savedslash[2];savedslash[0] = 0;savedslash[1] = 0;
  strcpy(current,shortname);
  do {
    var int l = strlen(current);
    if (l>0 && cpslashp(current[l-1])) {
      if (!*fullname) *savedslash = current[l-1];
      current[l-1] = 0; /* remove trailing slash */
    }
    _splitpath(current,drive,dir,fname,ext);
    h = FindFirstFile(current,&wfd);
    if (h != INVALID_HANDLE_VALUE) {
      if (*fullname) strcat(fullname,"\\");
      strrev(wfd.cFileName);
      strcat(fullname,wfd.cFileName);
      FindClose(h);
    } else return false;
    _makepath(current,drive,dir,NULL,NULL);
  } while (strcmp(dir,"\\")!=0);
  strrev(drive);
  strcat(fullname,"\\");
  strcat(fullname,drive);
  strrev(fullname);
  if (*savedslash) strcat(fullname,savedslash);
  return true;
}

#endif

/* UP: guarantees that the Directory of the Pathname exists
 (signals an error if it does not)
 assure_dir_exists(links_resolved,tolerantp)
 > STACK_0: absolute pathname without wildcards in directory
 > links_resolved: Flag, whether all links in the directory
                   of the pathname are already resolved
 > tolerantp: Flag, whether an error should be avoided
 < returns:
     if Name=NIL: Directory-Namestring (for DOS)
     if Name/=NIL: Namestring (for DOS)
     if tolerantp, maybe: nullobj
 can trigger GC */
#ifdef MSDOS
local object assure_dir_exists (bool links_resolved, bool tolerantp) {
  var object dir_namestring = directory_namestring(STACK_0);
  if (!links_resolved) { # test for existence:
    # 1. subdir-list empty -> OK
    #    (must be intercepted, because stat() on rootdir returns error.)
    # 2. OS/2: subdir-list = ("PIPE") -> OK
    #    (this special directory "\\PIPE\\" is none, actually.)
    # 3. Elso try stat() .
    if (!(nullp(Cdr(ThePathname(STACK_0)->pathname_directory))
         #ifdef PATHNAME_OS2
          || equal(Cdr(ThePathname(STACK_0)->pathname_directory),O(pipe_subdirs))
         #endif
          ) ) {
      var struct stat statbuf;
      with_sstring(dir_namestring,O(pathname_encoding),path,len, {
        ASSERT((len > 0) && (path[len-1] == '\\'));
        path[len-1] = '\0'; # replace '\' at the end with nullbyte
        begin_system_call();
        if (stat(path,&statbuf) < 0) {
          if (!(tolerantp && (errno==ENOENT))) {
            end_system_call(); OS_file_error(STACK_0);
          }
          end_system_call();
          FREE_DYNAMIC_ARRAY(path);
          return nullobj;
        }
        end_system_call();
      });
      if (!S_ISDIR(statbuf.st_mode)) { # found file no subdirectory ?
        if (tolerantp) return nullobj;
        fehler_dir_not_exists(dir_namestring);
      }
    }
  }
  if (namenullp(STACK_0))
    return dir_namestring;
  else
    return OSnamestring(dir_namestring);
}
#endif


#ifdef WIN32_NATIVE
local object assure_dir_exists (bool links_resolved, bool tolerantp) {
  var bool nnullp = namenullp(STACK_0);
  if (nnullp && links_resolved) return directory_namestring(STACK_0);
  with_sstring_0(whole_namestring(STACK_0),O(pathname_encoding),path, {
    var char resolved[MAX_PATH];
    var bool substitute = false;
    var bool error = false;
    begin_system_call();
    if (links_resolved) { # use light function
      shell_shortcut_target_t rresolve = resolve_shell_symlink(path,resolved);
      if (rresolve != shell_shortcut_notresolved) {
        if (rresolve == shell_shortcut_notexists)
          error = true;
        else
          substitute = true;
      }
    } else {
      if (real_path(path,resolved))
        substitute = true;
      else { # A file doesn't exist. Maybe dir does ?
        error = true; # let's be pessimistic
        if (!nnullp) {
          var uintL lastslashpos = strlen(path) - 1;
          while (lastslashpos > 0 && path[lastslashpos]!=slash) lastslashpos--;
          if (path[lastslashpos]==slash) {
            path[lastslashpos + 1] = '\0'; /* leave only path without name */
            if (real_path(path,resolved)) {
              # substitute only directory part
              var DWORD fileattr = GetFileAttributes(resolved);
              # resolved to a file ? Only directories allowed - nonmaskable error
              if (fileattr == 0xFFFFFFFF
                  || !(fileattr & FILE_ATTRIBUTE_DIRECTORY)) {
                SetLastError(ERROR_DIRECTORY);
                end_system_call(); OS_file_error(STACK_0);
              }
              pushSTACK(asciz_to_string(resolved,O(pathname_encoding)));
              # substitute immediately - w/o substitute flag
              # turn it into a pathname and use it with old name:
              pushSTACK(coerce_pathname(STACK_0));
              /* save old pathname name and type components */
              pushSTACK(ThePathname(STACK_2)->pathname_name);
              pushSTACK(ThePathname(STACK_3)->pathname_type);
              STACK_4 = STACK_2;
              ThePathname(STACK_4)->pathname_name = STACK_1;
              ThePathname(STACK_4)->pathname_type = STACK_0;
              skipSTACK(4);
              error = false;
            }
          }
        }
      }
    }
    end_system_call();
    if (error) {
      if (tolerantp) return nullobj;
      pushSTACK(copy_pathname(STACK_0));
      ThePathname(STACK_0)->pathname_name = NIL;
      ThePathname(STACK_0)->pathname_type = NIL;
      fehler_dir_not_exists(popSTACK());
    }
    if (substitute) {
      var object resolved_string = asciz_to_string(resolved,O(pathname_encoding));
      STACK_0 = coerce_pathname(resolved_string);
      nnullp = namenullp(STACK_0);
    }
    { var object dns = directory_namestring(STACK_0);
      return nnullp?dns:OSnamestring(dns); }
  });
}
#endif

# UP: returns the directory-namestring of a pathname under the assumption,
#     that the directory of this pathname exists.
# assume_dir_exists()
# > STACK_0: absolute pathname without wildcards in the directory
# < result:
#     if Name=NIL: directory-namestring (for DOS)
#     if Name/=NIL: namestring (for DOS)
# can trigger GC
global object assume_dir_exists (void) {
  return assure_dir_exists(true,false);
}

#endif

#ifdef PATHNAME_AMIGAOS

# UP: returns the truename of a directory-locks.
# > set_break_sem_4(): already executed
# > lock: Directory-Lock, will be released
# < result: Directory (as Pathname)
# can trigger GC
local object directory_truename (BPTR lock) {
  # move up from here:
  pushSTACK(NIL); # subdir-liste := NIL
  {
    var LONGALIGNTYPE(struct FileInfoBlock) fib;
    var struct FileInfoBlock * fibptr = LONGALIGN(&fib);
    loop { # look at directory itself:
      begin_system_call();
      {
        var LONG ergebnis = Examine(lock,fibptr);
        if (!ergebnis) { UnLock(lock); OS_error(); }
        end_system_call();
      }
      # use its name:
      var object name =
        asciz_to_string(&fibptr->fib_FileName[0],O(pathname_encoding));
      # step up to the parent-directory:
      var BPTR parentlock;
      begin_system_call();
      parentlock = ParentDir(lock);
      UnLock(lock);
      end_system_call();
      if (!(parentlock==BPTR_NULL)) {
        # name is the name of a subdirectory
        # push in front of the subdir-list:
        pushSTACK(name);
        {
          var object new_cons = allocate_cons();
          Car(new_cons) = popSTACK();
          Cdr(new_cons) = STACK_0;
          STACK_0 = new_cons;
        }
        lock = parentlock; # continue, starting from the parent directory
      } else {
        begin_system_call();
        if (IoErr()) { OS_error(); } # Error occurred?
        end_system_call();
        # name is the name of a DOS-Volume.
        pushSTACK(name);
        break;
      }
    }
  }
  clr_break_sem_4(); # allow breaks again
  # stack layout: subdirs, devicename.
  { # let subdirs start with :ABSOLUTE :
    var object new_cons = allocate_cons();
    Car(new_cons) = S(Kabsolute); Cdr(new_cons) = STACK_1;
    STACK_1 = new_cons;
  }
  var object default_dir = allocate_pathname(); # new pathname with Name=NIL and Type=NIL
  ThePathname(default_dir)->pathname_device = popSTACK();
  ThePathname(default_dir)->pathname_directory = popSTACK();
  return default_dir;
}

# UP: returns the current directory.
# < result: current directory (as pathname)
# can trigger GC
local object default_directory (void) {
  # acquire lock for the current directory:
  set_break_sem_4(); # impede breaks in the meantime
  begin_system_call();
  var BPTR lock = Lock("",ACCESS_READ);
  if (lock==BPTR_NULL) {
    if (!(IoErr()==ERROR_OBJECT_NOT_FOUND)) { clr_break_sem_4(); OS_error(); }
    end_system_call(); clr_break_sem_4();
    pushSTACK(unbound); # FILE-ERROR slot PATHNAME
    fehler(file_error,GETTEXT("Could not access current directory"));
  }
  end_system_call();
  return directory_truename(lock); # executes clr_break_sem_4(); and UnLock(lock);
}

# UP: Fills default-directory into a pathname.
# use_default_dir(pathname)
# > pathname: non-logical pathname
# < result: new absolute pathname
# can trigger GC
local object use_default_dir (object pathname) {
  # copy the pathname first:
  pathname = copy_pathname(pathname);
  { # then build the default-directory into the pathname:
    var object subdirs = ThePathname(pathname)->pathname_directory;
    # does pathname-directory start with :RELATIVE?
    if (eq(Car(subdirs),S(Krelative))) {
      # yes -> replace :RELATIVE with default-subdirs, i.e.
      # form  (append default-subdirs (cdr subdirs))
      #      = (nreconc (reverse default-subdirs) (cdr subdirs))
      pushSTACK(pathname);
      pushSTACK(Cdr(subdirs));
      var object temp = default_directory();
      temp = ThePathname(temp)->pathname_directory;
      temp = reverse(temp);
      subdirs = nreconc(temp,popSTACK());
      pathname = popSTACK();
      ThePathname(pathname)->pathname_directory =
        simplify_directory(subdirs); # enter into the pathname:
    }
  }
  return pathname;
}

# UP: Turns a directory-namestring into one that is appropriate for AMIGAOS.
# OSdirnamestring(namestring)
# > namestring: newly created directory-namestring, wit '/' or ':' at the
#               end, a Normal-Simple-String
# < result: Namestring for this Directory, in AmigaOS-Format: last '/'
#             discarded, if redundant, a Normal-Simple-String
# can trigger GC
local object OSdirnamestring (object namestring) {
  var uintL len = Sstring_length(namestring);
  if (len==0) goto ok; # empty string -> do not discard anything
  var chart ch = TheSstring(namestring)->data[len-1];
  if (!chareq(ch,ascii('/'))) # no '/' at the end -> do not discard anything
    goto ok;
  if (len==1) goto ok; # "/" means Parent -> do not discard
  ch = TheSstring(namestring)->data[len-2];
  if (chareq(ch,ascii('/')) || chareq(ch,ascii(':'))) # before it a '/' or ':'
    goto ok; # -> means Parent -> do not discard
  # discard '/' at the end:
  namestring = subsstring(namestring,0,len-1);
 ok: # do not discard anything
  return namestring;
}

# UP: ensures, that the directory of a pathname exists.
# assure_dir_exists(tolerantp)
# > STACK_0: non-logical pathname, whose directory does not contain :RELATIVE.
# > links_resolved: Flag, if all links in the directory of the pathname are
#     already resolved and if it is known as existing
# > tolerantp: Flag, if an error is to be avoided
# < STACK_0: (poss. the same) pathname, but resolved.
# < result:
#     if Name=NIL: Directory-Namestring (for AMIGAOS, wit '/' at the end)
#     if Name/=NIL: Namestring (for AMIGAOS)
#     if tolerantp poss.: nullobj
# < filestatus: if Name/=NIL: NULL if the File does not exist,
#                                else a pointer to STAT-information.
# can trigger GC
local var struct FileInfoBlock * filestatus;
local object assure_dir_exists (bool links_resolved, bool tolerantp) {
  if (!links_resolved) {
    # For resolution of :PARENTs, that step beyond Root,
    # the operating system has to be asked. So:
    var object dir_namestring = directory_namestring(STACK_0);
    pushSTACK(dir_namestring);
    dir_namestring = OSdirnamestring(dir_namestring); # without redundant '/' at the end
    with_sstring_0(dir_namestring,O(pathname_encoding),dir_namestring_asciz, {
      # acquire lock for this directory:
      set_break_sem_4(); # impede breaks in the meantime
      begin_system_call();
      var BPTR lock = Lock(dir_namestring_asciz,ACCESS_READ);
      if (lock==BPTR_NULL) {
        var LONG errcode = IoErr();
        end_system_call();
        FREE_DYNAMIC_ARRAY(dir_namestring_asciz);
        switch (errcode) {
          case ERROR_OBJECT_NOT_FOUND:
            clr_break_sem_4();
            if (tolerantp) { skipSTACK(1); return nullobj; }
            fehler_dir_not_exists(STACK_0);
          case ERROR_ACTION_NOT_KNOWN:
            # A device, for which no locks for subdirectories can be
            # acquired! It must be a special device
            # (PIPE, CON, AUX, etc.).
            # We stop the subdirectory-checks. We even do not call
            # Examine() . On the contrary, we assume that
            # the file does not exist (yet) in the usual sense.
            clr_break_sem_4(); # allow breaks, as we have not occupied a lock after all.
            if (namenullp(STACK_(0+1))) { # no file addressed?
              return popSTACK(); # yes -> finished
            } else {
              var uintC stringcount = 1; # directory_namestring already on the STACK
              stringcount += file_namestring_parts(STACK_(0+1)); # Strings for the Filename
              var object namestring = string_concat(stringcount); # concatenate
              filestatus = (struct FileInfoBlock *)NULL; # we say, the file does not exist
              return namestring;
            }
          default:
            OS_file_error(STACK_(0+1));
        }
      }
      end_system_call();
      dir_namestring = popSTACK();
      { # and check whether it is a directory:
        var LONGALIGNTYPE(struct FileInfoBlock) fib;
        var struct FileInfoBlock * fibptr = LONGALIGN(&fib);
        begin_system_call();
        var LONG ergebnis = Examine(lock,fibptr);
        if (!ergebnis) {
          UnLock(lock);
          end_system_call(); clr_break_sem_4();
          FREE_DYNAMIC_ARRAY(dir_namestring_asciz);
          OS_file_error(STACK_0);
        }
        if (!(fibptr->fib_DirEntryType >= 0)) { # it is not a directory?
          UnLock(lock);
          end_system_call(); clr_break_sem_4();
          FREE_DYNAMIC_ARRAY(dir_namestring_asciz);
          if (tolerantp) { return nullobj; }
          # STACK_0 = FILE-ERROR slot PATHNAME
          pushSTACK(dir_namestring);
          pushSTACK(TheSubr(subr_self)->name);
          fehler(file_error,GETTEXT("~: ~ names a file, not a directory"));
        }
        end_system_call();
      }
      # create lock for Truename:
      var object new_pathname = directory_truename(lock); # does clr_break_sem_4();
      var object old_pathname = STACK_0;
      ThePathname(new_pathname)->pathname_name
        = ThePathname(old_pathname)->pathname_name;
      ThePathname(new_pathname)->pathname_type
        = ThePathname(old_pathname)->pathname_type;
      STACK_0 = new_pathname;
    });
  }
  var object pathname = STACK_0;
  # get information concerning the addressed file:
  if (namenullp(pathname)) # no file addressed?
    return directory_namestring(pathname); # yes -> finished
  var object namestring = whole_namestring(pathname);
  with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
    # create lock for this file:
    set_break_sem_4(); # impede breaks in the meantime
    begin_system_call();
    var BPTR lock = Lock(namestring_asciz,ACCESS_READ);
    if (lock==BPTR_NULL) {
      if (!(IoErr()==ERROR_OBJECT_NOT_FOUND)) {
        end_system_call(); clr_break_sem_4(); OS_file_error(STACK_0);
      }
      end_system_call(); clr_break_sem_4();
      # file does not exist.
      filestatus = (struct FileInfoBlock *)NULL; return namestring;
    }
    end_system_call();
    # file exists.
    # get information:
    var local LONGALIGNTYPE(struct FileInfoBlock) status;
    var struct FileInfoBlock * statusptr = LONGALIGN(&status);
    begin_system_call();
    if (! Examine(lock,statusptr) ) {
      UnLock(lock); end_system_call(); clr_break_sem_4();
      OS_file_error(STACK_0);
    }
    UnLock(lock);
    end_system_call();
    clr_break_sem_4();
    if (statusptr->fib_DirEntryType >= 0) { # Is it a directory?
      # STACK_0 = FILE-ERROR slot PATHNAME
      pushSTACK(whole_namestring(STACK_0));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(file_error,GETTEXT("~: ~ names a directory, not a file"));
    } else {
      # normal file
      pushSTACK(namestring);
      # the capitalization/(use of small letters) of the truename is determined
      # by the already existing file.
      pushSTACK(asciz_to_string(&statusptr->fib_FileName[0],O(pathname_encoding)));
      split_name_type(1);
      var object pathname = STACK_(0+3); # the copied pathname
      ThePathname(pathname)->pathname_type = popSTACK();
      ThePathname(pathname)->pathname_name = popSTACK();
      # finished.
      filestatus = statusptr;
      return popSTACK(); # namestring
    }
  });
}

# the same, under the assumption that the directory already exists.
# (No simplification, because we have to determine the truename.??)
global object assume_dir_exists (void) {
  var object ret;
  with_saved_back_trace(L(open),-1,ret=assure_dir_exists(true,false));
  return ret;
}

#endif

#ifdef PATHNAME_UNIX

# UP: Return the current Directory.
# < result: current Directory (as Pathname)
# can trigger GC
local object default_directory (void) {
  var char path_buffer[MAXPATHLEN]; # cf. GETWD(3)
  # store Working Directory in path_buffer:
  begin_system_call();
  if ( getwd(&path_buffer[0]) ==NULL) {
    end_system_call();
    pushSTACK(O(dot_string)); # FILE-ERROR slot PATHNAME
    pushSTACK(asciz_to_string(&path_buffer[0],O(pathname_encoding))); # message
    fehler(file_error,GETTEXT("UNIX error while GETWD: ~"));
  }
  end_system_call();
  # It must start with '/' :
  if (!(path_buffer[0] == '/')) {
    pushSTACK(O(dot_string)); # FILE-ERROR slot PATHNAME
    pushSTACK(asciz_to_string(&path_buffer[0],O(pathname_encoding)));
    fehler(file_error,GETTEXT("UNIX GETWD returned ~"));
  }
  # convert to pathname:
  return asciz_dir_to_pathname(&path_buffer[0],O(pathname_encoding));
}

# UP: Fills Default-Directory into a pathname.
# use_default_dir(pathname)
# > pathname: non-logical pathname
# < result: new pathname, whose directory contains no :RELATIVE .
#             (short: "absolute pathname")
# can trigger GC
local object use_default_dir (object pathname) {
  # copy the pathname first:
  pathname = copy_pathname(pathname);
  { # then build the default-directory into the pathname:
    var object subdirs = ThePathname(pathname)->pathname_directory;
    # does pathname-directory start with :RELATIVE?
    if (eq(Car(subdirs),S(Krelative))) {
      # yes -> replace :RELATIVE with default-subdirs, i.e.
      # form  (append default-subdirs (cdr subdirs))
      #      = (nreconc (reverse default-subdirs) (cdr subdirs))
      pushSTACK(pathname);
      pushSTACK(Cdr(subdirs));
      var object temp = default_directory();
      temp = ThePathname(temp)->pathname_directory;
      temp = reverse(temp);
      subdirs = nreconc(temp,popSTACK());
      pathname = popSTACK();
      ThePathname(pathname)->pathname_directory =
        simplify_directory(subdirs); # enter into the pathname:
    }
  }
  return pathname;
}

# UP: Assures, that the directory of a pathname exists, and thereby resolves
# symbolic links.
# assure_dir_exists(tolerantp)
# > STACK_0: non-logical pathname, whose directory does not contain :RELATIVE.
# > links_resolved: Flag, if all links in the directory of the pathname
#     are already resolved and if it is known to exist
# > tolerantp: flag, if an error is to be avoided
# < STACK_0: (poss. the same) pathname, whereas neither for the directory nor
#            for the Filename a symbolic link is to be tracked.
# < result:
#     if Name=NIL: directory-namestring (for UNIX, with '/' at the end)
#     if Name/=NIL: namestring (for UNIX)
#     if tolerantp poss.: nullobj
# < filestatus: if Name/=NIL: NULL if the file does not exist,
#                                  else a pointer to a STAT-information.
# can trigger GC

# this has to be done this ugly way since C does not allow conditionals
# (like #ifdef HAVE_LSTAT) inside macros (like with_sstring_0)
#ifdef HAVE_LSTAT
  #define if_HAVE_LSTAT(statement)  statement
#else
  #define if_HAVE_LSTAT(statement)
#endif

local var struct stat * filestatus;
local object assure_dir_exists (bool links_resolved, bool tolerantp) {
  var uintC allowed_links = MAXSYMLINKS; # number of allowed symbolic links
  if (links_resolved)
    goto dir_exists;
  loop { # loop over the symbolic links to be resolved
    { # determine Truepath of the directory:
      var char path_buffer[MAXPATHLEN]; # cf. REALPATH(3)
      {
        var object pathname = STACK_0;
        var uintC stringcount =
          directory_namestring_parts(pathname); /* host and directory strings */
        pushSTACK(O(dot_string)); # and "."
        var object string = string_concat(stringcount+1); # concatenate
        /* resolve symbolic links therein: */
        with_sstring_0(string,O(pathname_encoding),string_asciz, {
          begin_system_call();
          if ( realpath(string_asciz,&path_buffer[0]) ==NULL) {
            if (errno!=ENOENT) { end_system_call(); OS_file_error(STACK_0); }
            end_system_call();
            if (!tolerantp)
              fehler_dir_not_exists(asciz_dir_to_pathname(&path_buffer[0],O(pathname_encoding))); # erroneous component
            end_system_call();
            FREE_DYNAMIC_ARRAY(string_asciz);
            return nullobj;
          }
          end_system_call();
        });
      }
      /* new Directory-Path must start with '/' : */
      if (!(path_buffer[0] == '/')) {
        /* STACK_0 = FILE-ERROR slot PATHNAME */
        pushSTACK(asciz_to_string(&path_buffer[0],O(pathname_encoding)));
        fehler(file_error,GETTEXT("UNIX REALPATH returned ~"));
      }
      /* possibly add a '/' at the end: */
      var char* pathptr = &path_buffer[0];
      var uintL len = 0; # string-length
      until (*pathptr == 0) { pathptr++; len++; } # search ASCIZ-string-end
      if (!((len>0) && (pathptr[-1]=='/'))) {
        *pathptr = '/'; len++; # add a '/'
      }
      /* and convert to a string: */
      var object new_string = n_char_to_string(&path_buffer[0],len,O(pathname_encoding));
      /* turn it into a pathname and use its Directory: */
      var object new_pathname = coerce_pathname(new_string);
      ThePathname(STACK_0)->pathname_directory
        = ThePathname(new_pathname)->pathname_directory;
    }
  dir_exists:
    /* get information for the addressed file: */
    if (namenullp(STACK_0)) # no file addressed?
      return directory_namestring(STACK_0); # yes -> finished
    var object namestring = whole_namestring(STACK_0); # concatenate
    /* get information: */
    var local struct stat status;
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      begin_system_call();
      if (!( lstat(namestring_asciz,&status) ==0)) {
        if (!(errno==ENOENT))
          { end_system_call(); OS_file_error(STACK_0); }
        /* file does not exist. */
        end_system_call();
        FREE_DYNAMIC_ARRAY(namestring_asciz);
        filestatus = (struct stat *)NULL; return namestring;
      }
      end_system_call();
      /* file exists. */
      if (S_ISDIR(status.st_mode)) { # is it a directory?
        /* STACK_0 = FILE-ERROR slot PATHNAME */
        pushSTACK(whole_namestring(STACK_0));
        pushSTACK(TheSubr(subr_self)->name);
        fehler(file_error,GETTEXT("~: ~ names a directory, not a file"));
      }
     if_HAVE_LSTAT(
      else if (possible_symlink(namestring_asciz) && S_ISLNK(status.st_mode)) {
        /* is it a symbolic link?
           yes -> continue resolving: */
        if (allowed_links==0) { # no more links allowed?
          /* yes -> simulate UNIX-Error ELOOP */
          begin_system_call();
          errno = ELOOP_VALUE;
          end_system_call();
          OS_file_error(STACK_0);
        }
        allowed_links--; # after that, one link less is allowed
        var uintL linklen = status.st_size; # presumed length of the link-content
      retry_readlink:
        {
          var DYNAMIC_ARRAY(linkbuf,char,linklen+1); # buffer for the Link-content
          /* read link-content: */
          begin_system_call();
          {
            var int result = readlink(namestring_asciz,linkbuf,linklen);
            end_system_call();
            if (result<0)
              OS_file_error(STACK_0);
            if (!(result == (int)linklen)) { # sometimes (AIX, NFS) status.st_size is incorrect
              FREE_DYNAMIC_ARRAY(linkbuf); linklen = result; goto retry_readlink;
            }
          }
          /* turn it into a pathname:
             (MERGE-PATHNAMES (PARSE-NAMESTRING linkbuf) pathname-without-name&type) */
          pushSTACK(n_char_to_string(linkbuf,linklen,O(pathname_encoding)));
          FREE_DYNAMIC_ARRAY(linkbuf);
        }
        funcall(L(parse_namestring),1);
        pushSTACK(value1);
        var object pathname = copy_pathname(STACK_(0+1));
        ThePathname(pathname)->pathname_name = NIL;
        ThePathname(pathname)->pathname_type = NIL;
        pushSTACK(pathname);
        funcall(L(merge_pathnames),2);
        STACK_0 = value1;
      }
     ) # HAVE_LSTAT
      else { # normal file
        filestatus = &status; return namestring;
      }
    });
  }
}

/* the same under the assumption, that the directory already exists.
   (only a little simplification, as the file can be a symbolic link into a
   different directory, and this must be tested to exist.) */
global object assume_dir_exists (void) {
  var object ret;
  with_saved_back_trace(L(open),-1,ret=assure_dir_exists(true,false));
  return ret;
}

#endif

#ifdef PATHNAME_RISCOS

# an "absolute pathname" is a pathname, whose Directory starts with
# (:ABSOLUTE :ROOT ...) .

# UP: returns the current directory.
# < result: current directory (as pathname)
# can trigger GC
local object default_directory (void) {
  # Working Directory (of RISCOS) is the resolved "@":
  var char path_buffer[MAXPATHLEN];
  # store working directory in path_buffer:
  begin_system_call();
  if ( realpath("@",&path_buffer[0]) ==NULL) { OS_error(); }
  end_system_call();
  # convert to pathname:
  return asciz_dir_to_pathname(&path_buffer[0],O(pathname_encoding));
}

#if 0 # unused
# UP: Convert a valid RISCOS file namestring to an absolute pathname.
# canonicalise_filename(filename)
# > filename: Simple-Asciz-String
# < result: absolute pathname
local object canonicalise_filename (object filename) {
  var char path_buffer[MAXPATHLEN];
  with_string_0(filename,O(pathname_encoding),filename_asciz, {
    begin_system_call();
    if ( realpath(filename_asciz,&path_buffer[0]) ==NULL) { OS_error(); }
    end_system_call();
  });
  # convert to pathname:
  return coerce_pathname(asciz_to_string(path_buffer,O(pathname_encoding)));
}
#endif

# UP: Convert a valid RISCOS directory namestring to an absolute pathname.
# canonicalise_dirname(pathname,dirname)
# > pathname: Pathname whose host name and device is to be used
# > dirname: Normal-Simple-String, ends with '.'
# < result: absolute pathname
local object canonicalise_dirname (object pathname, object dirname) {
  pushSTACK(pathname);
  var uintC stringcount = host_namestring_parts(pathname); # Strings for the host
  # Device, cf. directory_namestring_parts():
  {
    var object device = ThePathname(pathname)->pathname_device;
    if (!(nullp(device))) { # NIL -> no string
      pushSTACK(O(colon_string)); # ":"
      pushSTACK(device); # Device on the stack
      pushSTACK(O(dot_string)); # "."
      stringcount += 3; # and count
    }
  }
  pushSTACK(dirname);
  var object dir_string = string_concat(stringcount+1);
  with_sstring(dir_string,O(pathname_encoding),dir_path,len, {
    # replace dot at the end with Nullbyte:
    ASSERT((len > 0) && (dir_path[len-1] == '.'));
    dir_path[len-1] = '\0';
    # make absolute:
    var char path_buffer[MAXPATHLEN];
    begin_system_call();
    if ( realpath(dir_path,&path_buffer[0]) ==NULL) {
      end_system_call(); OS_file_error(STACK_0);
    }
    end_system_call();
    skipSTACK(1);
    # concert to pathname:
    dir_string = asciz_dir_to_pathname(&path_buffer[0],O(pathname_encoding));
  });
  return dir_string;
}

# UP: Fills the default-directory into the pathname.
# use_default_dir(pathname)
# > pathname: non-logical pathname
# < ergebnis: new pathname, whose directory contains no :RELATIVE or similar.
#             (short: "absolute pathname")
# can trigger GC
local object use_default_dir (object pathname) {
  var bool resolved_root = false;
 retry:
  # copy the pathname, first:
  pathname = copy_pathname(pathname);
  {
    var object subdirs = ThePathname(pathname)->pathname_directory;
    # if the device is specified, then directory must start with (:ABSOLUTE :ROOT ...)
    # (or with (:RELATIVE ...) - that will be replaced).
    if (!nullp(ThePathname(pathname)->pathname_device)) {
      if (eq(Car(subdirs),S(Krelative))) {
        pushSTACK(pathname); # save pathname
        pushSTACK(allocate_cons());
        var object new_cons = allocate_cons();
        subdirs = popSTACK();
        pathname = popSTACK(); # restore pathname
        Car(subdirs) = S(Kabsolute); Cdr(subdirs) = new_cons;
        Car(new_cons) = S(Kroot);
        Cdr(new_cons) = Cdr(ThePathname(pathname)->pathname_directory);
        ThePathname(pathname)->pathname_directory = subdirs;
      } else if (!(eq(Car(subdirs),S(Kabsolute))
                   && eq(Car(Cdr(subdirs)),S(Kroot)))) {
        pushSTACK(pathname); # FILE-ERROR slot PATHNAME
        pushSTACK(pathname);
        pushSTACK(O(root_string));
        pushSTACK(TheSubr(subr_self)->name);
        fehler(file_error,GETTEXT("~: If a device is specified, the directory must begin with ~: ~"));
      }
    }
    pushSTACK(pathname); # save pathname
    var object defaults;
    if (eq(Car(subdirs),S(Krelative))) {
      pushSTACK(Cdr(subdirs)); defaults = default_directory();
    } else { # (eq(Car(subdirs),S(Kabsolute)))
      var object next = Car(Cdr(subdirs));
      pushSTACK(Cdr(Cdr(subdirs)));
      if (eq(next,S(Kroot))) { # :ROOT -> "$." resolve or we are done
        # "$." is only resolved, if Host or Device are still
        # unknown, but only once (in order to avoid infinite loop.)
        # If Host or Device =NIL, is not
        # that important.
        if (!resolved_root
            && (nullp(ThePathname(pathname)->pathname_host)
                || nullp(ThePathname(pathname)->pathname_device))) {
          defaults = canonicalise_dirname(pathname,O(root_string));
          resolved_root = true;
        } else
          goto resolved;
      } else if (eq(next,S(Khome))) { # :HOME -> "&."
        defaults = canonicalise_dirname(pathname,O(home_string));
      } else if (eq(next,S(Kcurrent))) { # :CURRENT -> "@."
        defaults = canonicalise_dirname(pathname,O(current_string));
      } else if (eq(next,S(Klibrary))) { # :LIBRARY -> "%."
        defaults = canonicalise_dirname(pathname,O(library_string));
      } else if (eq(next,S(Kprevious))) { # :PREVIOUS -> "\\."
        defaults = canonicalise_dirname(pathname,O(previous_string));
      } else
        NOTREACHED;
    }
    # stack layout: pathname, rest-subdirs.
    # procedure not quite the same as with MERGE-PATHNAMES:
    # form  (append default-subdirs rest-subdirs)
    #      = (nreconc (reverse default-subdirs) rest-subdirs)
    pathname = STACK_1;
    ThePathname(pathname)->pathname_host
      = ThePathname(defaults)->pathname_host;
    ThePathname(pathname)->pathname_device
      = ThePathname(defaults)->pathname_device;
    defaults = ThePathname(defaults)->pathname_directory;
    defaults = reverse(defaults); subdirs = nreconc(defaults,popSTACK());
    pathname = popSTACK();
    ThePathname(pathname)->pathname_directory = subdirs;
    # it might be, that even now not everything is resolved.
    goto retry;
  }
 resolved: # stack layout: pathname, subdir-oldlist.
  # traverse list and freshly cons up, thereby process "^."
  # (Otherwise assure_dir_exists() would have to do this.)
  pushSTACK(S(Kroot)); pushSTACK(S(Kabsolute));
  { var object newlist = listof(2); pushSTACK(newlist); }
  # stack layout: pathname, subdir-oldlist, subdir-newlist.
  while (mconsp(STACK_1)) { # until oldlist is finished:
    var object subdir = Car(STACK_1); # next subdir
    if (eq(subdir,S(Kparent))) {
      # = :PARENT -> shorten newlist by one:
      if (matomp(Cdr(Cdr(STACK_0)))) { # newlist (except for :ABSOLUTE and :ROOT) empty ?
        # :PARENT from "$."  returns Error
        pushSTACK(STACK_2); # FILE-ERROR slot PATHNAME
        pushSTACK(O(root_string)); # "$."
        pushSTACK(directory_namestring(STACK_(2+2))); # directory of pathname
        fehler(file_error,GETTEXT("no directory ~ above ~"));
      }
      STACK_0 = Cdr(STACK_0);
    } else { # lengthen newlist by one:
      pushSTACK(subdir);
      var object new_cons = allocate_cons();
      Car(new_cons) = popSTACK();
      Cdr(new_cons) = STACK_0;
      STACK_0 = new_cons;
    }
    STACK_1 = Cdr(STACK_1);
  }
  var object subdirs = nreverse(popSTACK()); # newlist, reverse again
  skipSTACK(1);
  pathname = popSTACK();
  ThePathname(pathname)->pathname_directory =
    simplify_directory(subdirs); # enter into the pathname
  return pathname;
}

# UP: returns the namestring of a pathname for the operating system.
# OSnamestring(dir_namestring)
# > STACK_0: non-logical pathname
# > dir_namestring: directory-namestring
# < result: namestring (for RISCOS, swapped with Name/Type)
# can trigger GC
local object OSnamestring (object dir_namestring) {
  var object pathname = STACK_0;
  var uintC stringcount;
  pushSTACK(dir_namestring); # directory-namestring as 1st string
  stringcount = # and strings for the filename
    (nullp(ThePathname(pathname)->pathname_type)
     ? nametype_namestring_parts(ThePathname(pathname)->pathname_name,
                                 ThePathname(pathname)->pathname_type,
                                 pathname_version_maybe(pathname))
     # swap name and type (the type becomes a subdirectory-name):
     : nametype_namestring_parts(ThePathname(pathname)->pathname_type,
                                 ThePathname(pathname)->pathname_name,
                                 pathname_version_maybe(pathname)));
  return string_concat(1+stringcount); # concatenate
}

# UP: Assures, that the directory of a pathname exists.
# else error-message.
# assure_dir_exists(links_resolved,tolerantp)
# assure_dir_exists_(links_resolved,tolerantp,allowdir)
# > STACK_0: absolute pathname without wildcards in the directory
# > links_resolved: Flag, if all links in the directory of the pathname
#     are already resolved and if it is known to exist
# > tolerantp: flag, if an error is to be avoided
# > allowdir: Flag, if for Name/=NIL a directory instead of a file is allowed
# < result:
#     if Name=NIL: Directory-Namestring (for RISCOS, with '.' at the end)
#     if Name/=NIL: Namestring (for RISCOS)
#     if tolerantp poss.: nullobj
# < filestatus: if Name/=NIL: NULL if the file does not exist,
#                                else a pointer to a STAT-information.
# can trigger GC
local var struct stat * filestatus;
#define assure_dir_exists(links_resolved,tolerantp)  \
     assure_dir_exists_(links_resolved,tolerantp,false)
local object assure_dir_exists_ (bool links_resolved, bool tolerantp,
                                 bool allowdir) {
  var object dir_namestring = directory_namestring(STACK_0);
  if (!links_resolved) { # existence-test:
    var struct stat statbuf;
    with_sstring(dir_namestring,O(pathname_encoding),dir_namestring_asciz,len, {
      ASSERT((len > 0) && (dir_namestring_asciz[len-1]=='.'));
      dir_namestring_asciz[len-1] = '\0'; # replace '.' at the end with nullbyte
      begin_system_call();
      if (stat(dir_namestring_asciz,&statbuf) < 0) {
        if (!(tolerantp && (errno==ENOENT))) {
          end_system_call(); OS_file_error(STACK_0);
        }
        end_system_call();
        FREE_DYNAMIC_ARRAY(dir_namestring_asciz);
        return nullobj;
      }
      end_system_call();
    });
    if (!S_ISDIR(statbuf.st_mode)) { # found file not a subdirectory ?
      if (tolerantp) return nullobj;
      fehler_dir_not_exists(dir_namestring);
    }
  }
  # get information for the addressed file:
  if (namenullp(STACK_0)) { # no file addressed?
    return dir_namestring; # yes -> finished
  } else {
    var object namestring = OSnamestring(dir_namestring);
    # get information:
    var local struct stat status;
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      begin_system_call();
      if (stat(namestring_asciz,&status) < 0) {
        if (!(errno==ENOENT)) { end_system_call(); OS_file_error(STACK_0); }
        # File does not exist.
        end_system_call();
        FREE_DYNAMIC_ARRAY(namestring_asciz);
        filestatus = (struct stat *)NULL; return namestring;
      }
      end_system_call();
    });
    # file exists.
    if (!allowdir && S_ISDIR(status.st_mode)) { # Ist es ein Directory?
      # STACK_0 = FILE-ERROR slot PATHNAME
      pushSTACK(whole_namestring(STACK_0));
      pushSTACK(TheSubr(subr_self)->name);
      fehler(file_error,GETTEXT("~: ~ names a directory, not a file"));
    } else { # normal file or (allowed) directory
      filestatus = &status; return namestring;
    }
  }
}

# the same under the assumption, that the directory already exists.
# (No simplification, because we have to determine the truename.??)
global object assume_dir_exists (void) {
  var object ret;
  with_saved_back_trace(L(open),-1,ret=assure_dir_exists(true,false));
  return ret;
}

# A file "name.type" is conciliated to RISCOS as "type.name" , thereby "type"
# is the name of a subdirectory! If a file "name.type" is to be
# created, the subdirectory "type" has to be created first.
# prepare_create(pathname);
# > pathname: a pathname
# can trigger GC
local object pathname_add_subdir (void);
local void prepare_create (object pathname) {
  if (!nullp(ThePathname(pathname)->pathname_type)) {
    # call pathname_add_subdir:
    pushSTACK(pathname); pushSTACK(ThePathname(pathname)->pathname_type);
    pathname = pathname_add_subdir();
    ThePathname(pathname)->pathname_name = NIL;
    ThePathname(pathname)->pathname_type = NIL;
    # call MAKE-DIR if the directory does not exist:
    pushSTACK(pathname);
    if (eq(assure_dir_exists(false,true),nullobj)) {
      funcall(L(make_dir),1);
    } else {
      skipSTACK(1);
    }
  }
}

#else

# Normally nothing special to do before creating a file.
  #define prepare_create(pathname)

#endif

#if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
#if 0 # unused
# UP: Turns a directory-namestring into one, that is suitably for DOS.
# OSdirnamestring(namestring)
# > namestring: newly created directory-namestring, with '\' at the end,
#               a normal-simple-string
# < result: namestring for this directory, in DOS-Format: last '\'
#             discarded, if superfluous, a normal-simple-string
# can trigger GC
local object OSdirnamestring (object namestring) {
  var uintL len = Sstring_length(namestring);
  if (len==0) goto ok; # empty string -> do not discard anything
  var chart ch = TheSstring(namestring)->data[len-1];
  if (!chareq(ch,ascii('\\'))) # no '\' at the end -> do not discard
    goto ok;
  if (len==1) goto ok; # "\" means Root -> do not discard
  ch = TheSstring(namestring)->data[len-2];
  if (chareq(ch,ascii('\\')) || chareq(ch,ascii(':'))) # '\' or ':' before it
    goto ok; # -> means parent -> do not discard
  # discard '\' at the end:
  namestring = subsstring(namestring,0,len-1);
 ok: # do not discard anything
  return namestring;
}
#endif
# UP: Changes the default-drive and its default-directory.
# change_default();
# > STACK_0: absolute pathname, whose device is a string and directory
#     contains no :RELATIVE, :CURRENT, :PARENT, and name and type are =NIL.
# can trigger GC
local void change_default (void) {
  { /* change default-directory for this drive: */
    var object pathname = STACK_0;
    var uintC stringcount =
      directory_namestring_parts(pathname); # strings for the directory
    # no redundant '\' at the end
    if (mconsp(Cdr(ThePathname(pathname)->pathname_directory))) {
      skipSTACK(1); stringcount--;
    }
    var object string = string_concat(stringcount); # concatenate
    with_sstring_0(string,O(pathname_encoding),asciz, {
      # change default-directory:
      change_current_directory(asciz);
    });
  }
  # change default-drive:
  O(default_drive) = ThePathname(STACK_0)->pathname_device;
  # set *DEFAULT-PATHNAME-DEFAULTS* :
  recalc_defaults_pathname();
}
#endif
#ifdef PATHNAME_AMIGAOS
# UP: changes the default-directory.
# change_default();
# > STACK_0: absolute pathname, whose directory contains no :RELATIVE, :CURRENT,
#     :PARENT , and name and type are =NIL.
# can trigger GC
extern BPTR orig_dir_lock; # lock for the original directory
                           # (this does not belong to us, do not release!)
local void change_default (void) {
  var object dir_namestring = directory_namestring(STACK_0);
  dir_namestring = OSdirnamestring(dir_namestring); # without redundant '/' at the end
  with_sstring_0(dir_namestring,O(pathname_encoding),dir_namestring_asciz, {
    # change default-directory:
    set_break_sem_4();
    begin_system_call();
    var BPTR lock = Lock(dir_namestring_asciz,ACCESS_READ);
    if (lock==BPTR_NULL) { end_system_call(); OS_file_error(STACK_0); }
    lock = CurrentDir(lock); # newly set current directory
    # memorize resp. release lock of the old current directory:
    if (orig_dir_lock == BPTR_NONE)
      orig_dir_lock = lock;
    else
      UnLock(lock);
    end_system_call();
    clr_break_sem_4();
  });
}
#endif
#ifdef PATHNAME_UNIX
# UP: changes the default-directory.
# change_default();
# > STACK_0: absolute pathname, whose directory contains no :RELATIVE,
#      :CURRENT, :PARENT , and name and Type are =NIL.
# can trigger GC
local void change_default (void) {
  var object string = directory_namestring(STACK_0);
  with_sstring_0(string,O(pathname_encoding),asciz, {
    # change default-directory:
    begin_system_call();
    if (!( chdir(asciz) ==0)) { end_system_call(); OS_file_error(STACK_0); }
    end_system_call();
  });
}
#endif
#ifdef PATHNAME_RISCOS
# UP: changes the default-directory.
# change_default();
# > STACK_0: absolute pathname, whose name and type are =NIL.
# can trigger GC
local void change_default (void) {
  var object dir_namestring = directory_namestring(STACK_0);
  with_sstring(dir_namestring,O(pathname_encoding),dir_namestring_asciz,len, {
    ASSERT((len > 0) && (dir_namestring_asciz[len-1]=='.'));
    dir_namestring_asciz[len-1] = '\0'; # replace '.' at the end with nullbyte
    begin_system_call();
    if (chdir(dir_namestring_asciz))
      { end_system_call(); OS_file_error(STACK_0); }
    end_system_call();
  });
}
#endif

# (NAMESTRING pathname), CLTL p. 417
# (NAMESTRING pathname t) -> namestring in external format
#   Unix: with default-directory
LISPFUN(namestring,seclass_read,1,1,norest,nokey,0,NIL) {
  var object flag = popSTACK(); # optional argument flag
  var object pathname = coerce_xpathname(popSTACK());
 #if defined(PATHNAME_UNIX) || defined(PATHNAME_AMIGAOS) || defined(PATHNAME_RISCOS) || defined(PATHNAME_WIN32)
  if (!missingp(flag)) {
    # flag /= NIL -> for the operating system:
    pathname = coerce_pathname(pathname);
    check_no_wildcards(pathname); # with wildcards -> error
    pathname = use_default_dir(pathname); # insert default-directory
    # (because Unix/AMIGAOS does not know the default-directory of LISP
    # and Win32 is multitasking)
  }
 #endif
  VALUES1(whole_namestring(pathname));
}

# error-message because of missing file name
# fehler_noname(pathname);
# > pathname: pathname
nonreturning_function(local, fehler_noname, (object pathname)) {
  pushSTACK(pathname); # FILE-ERROR slot PATHNAME
  pushSTACK(pathname);
  fehler(file_error,GETTEXT("no file name given: ~"));
}
#define check_noname(pathname)                                          \
  do { if (namenullp(pathname)) { fehler_noname(pathname); } } while(0)

# error-message because of illegal Name/Type-specification
# fehler_notdir(pathname);
# > pathname: pathname
nonreturning_function(local, fehler_notdir, (object pathname)) {
  pushSTACK(pathname); # FILE-ERROR slot PATHNAME
  pushSTACK(pathname);
  fehler(file_error,GETTEXT("not a directory: ~"));
}
#define check_notdir(pathname)                                  \
  do { if (!(nullp(ThePathname(pathname)->pathname_name)        \
             && nullp(ThePathname(pathname)->pathname_type)))   \
         fehler_notdir(pathname); } while(0)

# test, if a file exists:
# file_exists(namestring)
# > led the way: assure_dir_exists()
# > STACK_0: pathname, the same as after execution of assure_dir_exists(), Name/=NIL
# > namestring: its namestring for the operating system
#if defined(MSDOS) || defined(WIN32_NATIVE)
  #ifdef MSDOS
    local inline int access0 (CONST char* path) {
      begin_system_call();
      var int erg = access(path,0);
      end_system_call();
      return erg;
    }
  #endif
  #ifdef WIN32_NATIVE
    local inline int access0 (const char* path) {
      begin_system_call();
      var DWORD fileattr = GetFileAttributes(path);
      if (fileattr == 0xFFFFFFFF) {
        if (WIN32_ERROR_NOT_FOUND) {
          end_system_call(); return -1;
        }
        end_system_call(); OS_file_error(STACK_0);
      }
      end_system_call();
      return 0;
    }
  #endif
  local bool file_exists (object namestring) {
    var bool exists;
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      exists = (access0(namestring_asciz)==0);
    });
    return exists;
  }
#endif
#ifdef AMIGAOS
  #define file_exists(namestring)  (!(filestatus == (struct FileInfoBlock *)NULL))
  #define FILE_EXISTS_TRIVIAL
#endif
#if defined(UNIX) || defined(RISCOS)
  #define file_exists(namestring)  (!(filestatus == (struct stat *)NULL))
  #define FILE_EXISTS_TRIVIAL
#endif

# error-message because of non-existent file
# fehler_file_not_exists();
# > STACK_0: pathname
nonreturning_function(local, fehler_file_not_exists, (void)) {
  # STACK_0 = FILE-ERROR slot PATHNAME
  pushSTACK(STACK_0); # pathname
  pushSTACK(TheSubr(subr_self)->name);
  fehler(file_error,GETTEXT("~: file ~ does not exist"));
}

/* TRUENAME for a pathname
   pushes pathname on the stack and
   returns the truename (filename for the operating system) or nullobj
   can trigger GC */
local object true_namestring (object pathname, bool noname_p, bool tolerantp) {
  check_no_wildcards(pathname); /* with wildcards -> error */
  pathname = use_default_dir(pathname); /* insert default-directory */
  if (noname_p) check_noname(pathname);
  pushSTACK(pathname); /* directory must exist: */
  return assure_dir_exists(false,tolerantp);
}

LISPFUNNR(truename,1)
{ /* (TRUENAME pathname), CLTL p. 413 */
  var object pathname = popSTACK(); # pathname-argument
  if (builtin_stream_p(pathname)) { # stream -> treat extra:
    # must be file-stream:
    pathname = as_file_stream(pathname);
    test_file_stream_named(pathname);
    # Streamtype File-Stream
    VALUES1(TheStream(pathname)->strm_file_truename);
  } else {
    var object namestring = true_namestring(coerce_pathname(pathname),
                                            false,false);
    if (namenullp(STACK_0)) {
      # no name specified
      if (!nullp(ThePathname(STACK_0)->pathname_type)) {
        # STACK_0 = FILE-ERROR slot PATHNAME
        pushSTACK(STACK_0); # pathname
        pushSTACK(TheSubr(subr_self)->name);
        fehler(file_error,GETTEXT("~: pathname with type but without name makes no sense: ~"));
      }
      # no name and no type specified -> pathname as result
    } else {
      # name specified.
      # check, if the file exists:
      if (!file_exists(namestring)) { fehler_file_not_exists(); }
      # file exists -> pathname as value
    }
    VALUES1(popSTACK());
  }
}

LISPFUNNR(probe_file,1)
{ /* (PROBE-FILE filename), CLTL p. 424 */
  var object pathname = popSTACK(); # pathname-argument
  if (builtin_stream_p(pathname)) { # stream -> treat extra:
    # must be file-stream:
    pathname = as_file_stream(pathname);
    test_file_stream_named(pathname);
    # streamtype file-stream -> take truename:
    var uintB flags = TheStream(pathname)->strmflags;
    pathname = TheStream(pathname)->strm_file_truename;
    if (flags & strmflags_open_B) { # file opened?
      # yes -> truename instantly as result:
      VALUES1(pathname); return;
    }
    # no -> yet to test, if the file for the truename exists.
  } else {
    pathname = coerce_pathname(pathname); # turn into a pathname
  }
  # pathname is now a Pathname.
  var object namestring = true_namestring(pathname,true,true);
  if (eq(namestring,nullobj)) {
    # path to the file does not exist -> NIL as value:
    skipSTACK(1); VALUES1(NIL); return;
  }
  # check, if the file exists:
  if (file_exists(namestring)) {
    VALUES1(popSTACK()); /* file exists -> pathname as value */
  } else {
    skipSTACK(1); VALUES1(NIL); return; /* else NIL as value */
  }
}

# tests, if a directory exists.
# directory_exists(pathname)
# > pathname: an absolute pathname without wildcards, with Name=NIL and Type=NIL
# < result: true, if it denotes an existing directory
# can trigger GC
local bool directory_exists (object pathname) {
  pushSTACK(pathname); # save pathname
  var object dir_namestring = directory_namestring(pathname);
  # existence test, see assure_dir_exists():
  var bool exists = true;
 #ifdef MSDOS
  if (!(nullp(Cdr(ThePathname(STACK_0)->pathname_directory))
       #ifdef PATHNAME_OS2
        || equal(Cdr(ThePathname(STACK_0)->pathname_directory),O(pipe_subdirs))
       #endif
        ) ) {
    with_sstring(dir_namestring,O(pathname_encoding),dir_namestring_asciz,len, {
      ASSERT((len > 0) && (dir_namestring_asciz[len-1] == '\\'));
      dir_namestring_asciz[len-1] = '\0'; # replace '\' at the end with nullbyte
      var struct stat statbuf;
      begin_system_call();
      if (stat(dir_namestring_asciz,&statbuf) < 0) {
        if (!(errno==ENOENT)) { end_system_call(); OS_file_error(STACK_0); }
        exists = false;
      } else {
        if (!S_ISDIR(statbuf.st_mode)) # found file is no subdirectory ?
          exists = false;
      }
      end_system_call();
    });
  }
 #endif
 #ifdef WIN32_NATIVE
  with_sstring_0(dir_namestring,O(pathname_encoding),dir_namestring_asciz, {
    if (!nullp(Cdr(ThePathname(STACK_0)->pathname_directory))) {
      var uintL len = Sstring_length(dir_namestring);
      ASSERT((len > 0) && cpslashp(dir_namestring_asciz[len-1]));
      dir_namestring_asciz[len-1] = '\0'; # replace '\' at the end with nullbyte
    }
    begin_system_call();
    var DWORD fileattr = GetFileAttributes(dir_namestring_asciz);
    if (fileattr == 0xFFFFFFFF) {
      if (!WIN32_ERROR_NOT_FOUND) {
        end_system_call(); OS_file_error(STACK_0);
      }
      exists = false;
    } else {
      if (!(fileattr & FILE_ATTRIBUTE_DIRECTORY)) # found file is no subdirectory ?
        exists = false;
    }
    end_system_call();
  });
 #endif
 #ifdef PATHNAME_AMIGAOS
  dir_namestring = OSdirnamestring(dir_namestring); # without redundant '/' at the end
  with_sstring_0(dir_namestring,O(pathname_encoding),dir_namestring_asciz, {
    # get lock for this directory:
    set_break_sem_4(); # impede breaks in the meantime
    begin_system_call();
    var BPTR lock = Lock(dir_namestring_asciz,ACCESS_READ);
    if (lock==BPTR_NULL) {
      var LONG errcode = IoErr();
      switch (errcode) {
        case ERROR_OBJECT_NOT_FOUND:
        case ERROR_ACTION_NOT_KNOWN:
          exists = false;
          break;
        default:
          end_system_call(); OS_file_error(STACK_0);
      }
    } else {
      var LONGALIGNTYPE(struct FileInfoBlock) fib;
      var struct FileInfoBlock * fibptr = LONGALIGN(&fib);
      var LONG ergebnis = Examine(lock,fibptr);
      if (!ergebnis || !(fibptr->fib_DirEntryType >= 0))
        exists = false;
      UnLock(lock);
    }
    end_system_call();
    clr_break_sem_4();
  });
 #endif
 #ifdef PATHNAME_UNIX
  pushSTACK(dir_namestring);
  pushSTACK(O(dot_string)); # and "."
  dir_namestring = string_concat(2); # concatenate
  with_sstring_0(dir_namestring,O(pathname_encoding),dir_namestring_asciz, {
    var struct stat statbuf;
    begin_system_call();
    if (stat(dir_namestring_asciz,&statbuf) < 0) {
      if (!(errno==ENOENT)) { end_system_call(); OS_file_error(STACK_0); }
      exists = false;
    } else {
      if (!S_ISDIR(statbuf.st_mode)) # found file is no subdirectory ?
        exists = false;
    }
    end_system_call();
  });
 #endif
 #ifdef PATHNAME_RISCOS
  with_sstring(dir_namestring,O(pathname_encoding),dir_namestring_asciz,len, {
    ASSERT((len > 0) && (dir_namestring_asciz[len-1]=='.'));
    dir_namestring_asciz[len-1] = '\0'; # replace '.' at the end with nullbyte
    var struct stat statbuf;
    begin_system_call();
    if (stat(dir_namestring_asciz,&statbuf) < 0) {
      if (!(errno==ENOENT)) { end_system_call(); OS_file_error(STACK_0); }
      exists = false;
    } else {
      if (!S_ISDIR(statbuf.st_mode)) # found file is no subdirectory ?
        exists = false;
    }
    end_system_call();
  });
 #endif
  skipSTACK(1);
  return exists;
}

LISPFUNNR(probe_directory,1)
{ /* (PROBE-DIRECTORY filename) tests, if a directory exists. */
  var object pathname = popSTACK(); # pathname-argument
  pathname = coerce_pathname(pathname); # turn into a pathname
  check_no_wildcards(pathname); # with wildcards -> error
  pathname = use_default_dir(pathname); # insert default-directory
  check_notdir(pathname); # ensure that Name=NIL and Type=NIL
  VALUES_IF(directory_exists(pathname));
}

# Converts a directory pathname to an OS directory specification.
# > pathname: an object
# > use_default: whether to use the current default directory
# < result: a simple-bit-vector containing an ASCIZ string in OS format
# can trigger GC
global object pathname_to_OSdir (object pathname, bool use_default) {
  pathname = coerce_pathname(pathname); # convert to pathname
  check_no_wildcards(pathname); # if it has wildcards -> error
  if (use_default)
    pathname = use_default_dir(pathname); # insert default directory
  check_notdir(pathname); # ensure that Name=NIL and Type=NIL
  pushSTACK(pathname); # save pathname
  var object dir_namestring = directory_namestring(pathname);
  #ifdef PATHNAME_AMIGAOS
  dir_namestring = OSdirnamestring(dir_namestring);
  #endif
  var object dir_namestring_asciz =
    string_to_asciz(dir_namestring,O(pathname_encoding));
  var char* asciz = TheAsciz(dir_namestring_asciz);
  var uintL len = asciz_length(asciz);
  #ifdef MSDOS
    if (!(nullp(Cdr(ThePathname(STACK_0)->pathname_directory))
          #ifdef PATHNAME_OS2
          || equal(Cdr(ThePathname(STACK_0)->pathname_directory),O(pipe_subdirs))
          #endif
       ) ) {
      ASSERT((len > 0) && (asciz[len-1] == '\\'));
      asciz[len-1] = '\0';
    }
  #endif
  #if defined(WIN32_NATIVE) || defined(UNIX)
    if (!nullp(Cdr(ThePathname(STACK_0)->pathname_directory))) {
      ASSERT((len > 0) && cpslashp(asciz[len-1]));
      asciz[len-1] = '\0';
    }
  #endif
  #ifdef PATHNAME_RISCOS
    ASSERT((len > 0) && cpslashp(asciz[len-1]));
    asciz[len-1] = '\0';
  #endif
  skipSTACK(1); # forget pathname
  return dir_namestring_asciz;
}

# Converts an OS directory specification to a directory pathname.
# > path: a pathname referring to a directory
# < result: a pathname without name and type
# can trigger GC
global object OSdir_to_pathname (const char* path) {
  return asciz_dir_to_pathname(path,O(pathname_encoding));
}

# UP: determines, if a file is opened.
# openp(pathname)
#if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
# > pathname: absolute pathname, without wildcards.
#endif
#ifdef PATHNAME_AMIGAOS
# > pathname: absolute pathname, without wildcards, without :PARENT
#endif
#ifdef PATHNAME_UNIX
# > pathname: absolute pathname, without wildcards, after resolution
#             of symbolic links
#endif
# < result: true, if an opened file-stream exits for this file.
local bool openp (object pathname) {
  var object flist = O(open_files); # traverse list of all open files
  while (consp(flist)) {
    var object f = Car(flist); # next open stream
    if (TheStream(f)->strmtype == strmtype_file) { # file-stream ?
      if (equal(TheStream(f)->strm_file_truename,pathname))
        return true;
    }
    flist = Cdr(flist);
  }
  return false;
}

# error-message because of deletion attempt on opened file
# fehler_delete_open(pathname);
# > pathname: truename of the file
nonreturning_function(local, fehler_delete_open, (object pathname)) {
  pushSTACK(pathname); # FILE-ERROR slot PATHNAME
  pushSTACK(pathname);
  fehler(file_error,GETTEXT("cannot delete file ~ since there is file stream open to it"));
}
#define check_delete_open(pathname)                                     \
 do { if (openp(pathname)) { fehler_delete_open(pathname); } } while(0)

# (DELETE-FILE filename), CLTL p. 424
LISPFUNN(delete_file,1) {
  var object pathname = popSTACK(); # pathname-argument
  if (builtin_stream_p(pathname)) { # stream -> treat extra:
    var object stream = as_file_stream(pathname); # must be file-stream
    test_file_stream_named(stream);
    # Streamtype file-stream.
    # if file is opened, close file first:
    if (TheStream(stream)->strmflags & strmflags_open_B) { # file opened ?
      pushSTACK(stream); builtin_stream_close(&STACK_0); stream = popSTACK();
    }
    # then take the truename as file to be deleted:
    pathname = TheStream(stream)->strm_file_truename;
  } else {
    pathname = coerce_pathname(pathname); # turn into a pathname
  }
  # pathname is now a pathname.
  check_no_wildcards(pathname); /* with wildcards -> error */
  pathname = use_default_dir(pathname); /* insert default-directory */
  check_noname(pathname);
  pushSTACK(pathname); pushSTACK(pathname);
  var object namestring = assure_dir_exists(false,true);
  if (eq(namestring,nullobj)) {
    # path to the file does not exist ==> return NIL
    skipSTACK(1); VALUES1(NIL); return;
  }
  check_delete_open(STACK_0);
  /* delete the original filename - not the truename */
  namestring = whole_namestring(STACK_1);
  with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
    if (!delete_file_if_exists(namestring_asciz)) {
      # file does not exist -> value NIL
      FREE_DYNAMIC_ARRAY(namestring_asciz); skipSTACK(2);
      VALUES1(NIL); return;
    }
  });
  # file existed, was deleted -> pathname (/=NIL) as value
  VALUES1(STACK_1); skipSTACK(2);
}

# error-message because of renaming attempt of an opened file
# fehler_rename_open(pathname);
# > pathname: truename of the file
nonreturning_function(local, fehler_rename_open, (object pathname)) {
  pushSTACK(pathname); # FILE-ERROR slot PATHNAME
  pushSTACK(pathname);
  fehler(file_error,GETTEXT("cannot rename file ~ since there is file stream open to it"));
}

# UP: Renames a file.
# rename_file();
# > stack layout: filename, newname, oldpathname.
# < stack layout: filename, newname, oldpathname, newpathname,
#                oldtruename, oldnamestring, newtruename, newnamestring.
local void rename_file (void) {
  { # 1. newpathname := (MERGE-PATHNAMES newname oldpathname)
    pushSTACK(STACK_1); # newname as 1. argument
    pushSTACK(STACK_(0+1)); # oldpathname as 2. argument
    funcall(L(merge_pathnames),2);
    pushSTACK(value1);
  }
  # stack layout: filename, newname, oldpathname, newpathname.
  { # 2. check oldpathname:
    var object oldpathname = STACK_1;
    var object old_namestring = true_namestring(oldpathname,true,false);
    if (openp(STACK_0)) # do not rename open files!
      { fehler_rename_open(STACK_0); }
    pushSTACK(old_namestring);
  }
  # stack layout: filename, newname, oldpathname, newpathname,
  #              oldtruename, oldnamestring.
  { # 3. check newpathname:
    var object newpathname = coerce_pathname(STACK_2);
    var object new_namestring = true_namestring(newpathname,true,false);
    # stack layout: filename, newname, oldpathname, newpathname,
    #              oldtruename, oldnamestring, newtruename.
    # 4. rename file:
    if (file_exists(new_namestring)) {
      # file already exists -> do not delete without forewarn
      fehler_file_exists();
    }
    pushSTACK(new_namestring);
  }
  # stack layout: filename, newname, oldpathname, newpathname,
  #              oldtruename, oldnamestring, newtruename, newnamestring.
  # now it can be renamed without risk:
  prepare_create(STACK_4);
  with_sstring_0(STACK_2,O(pathname_encoding),oldnamestring_asciz, {
    with_sstring_0(STACK_0,O(pathname_encoding),newnamestring_asciz, {
      rename_file_to_nonexisting(oldnamestring_asciz,newnamestring_asciz);
    });
  });
}

# (RENAME-FILE filename newname), CLTL p. 423
LISPFUNN(rename_file,2) {
  var object filename = STACK_1; # filename-argument
  if (builtin_stream_p(filename)) { # stream -> treat extra:
    # must be file-stream:
    filename = as_file_stream(filename);
    test_file_stream_named(filename);
    # streamtype file-stream -> use truename:
    filename = TheStream(filename)->strm_file_truename;
    pushSTACK(filename);
    # rename:
    rename_file();
    # update stream:
    filename = STACK_7;
    TheStream(filename)->strm_file_name = STACK_4; # newpathname as new name
    TheStream(filename)->strm_file_truename = STACK_1; # newtruename as new truename
    # leave handle etc. untouched
  } else {
    filename = coerce_pathname(filename); # turn into a pathname
    pushSTACK(filename);
    # rename:
    rename_file();
  }
  VALUES3(STACK_4, /* newpathname as 1st value */
          STACK_3, /* oldtruename as 2nd value */
          STACK_1); /* newtruename as 3rd value */
  skipSTACK(8);
}

# Create a file.
# create_new_file(pathstring);
# It is known that the file does not already exist.
# > pathstring: file name, ASCIZ-String
# > STACK_0: pathname
local inline void create_new_file (char* pathstring) {
 #ifdef AMIGAOS
  begin_system_call();
  var Handle handle = Open(pathstring,MODE_NEWFILE);
  if (handle == Handle_NULL) { end_system_call(); OS_file_error(STACK_0); } # report error
  # file was created, handle is the Handle.
  # close file again:
  (void) Close(handle);
  end_system_call();
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  var Handle handle = CreateFile(pathstring, 0, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
  if (handle==INVALID_HANDLE_VALUE)
    { end_system_call(); OS_file_error(STACK_0); }
  # file was created, handle is the Handle.
  # close file again:
  if (!CloseHandle(handle)) { end_system_call(); OS_file_error(STACK_0); }
  end_system_call();
 #endif
 #ifdef EMUNIX
  begin_system_call();
  var int result = creat(pathstring,my_open_mask);
  if (result<0) { end_system_call(); OS_file_error(STACK_0); } # report error
  setmode(ergebnis,O_BINARY);
  # file was created, result is the Handle.
  # close file again:
  if (!(CLOSE(result)==0)) { end_system_call(); OS_file_error(STACK_0); } # report error
  end_system_call();
 #endif
 #if defined(UNIX) || defined(RISCOS)
  begin_system_call();
  var int result = OPEN(pathstring, O_WRONLY | O_BINARY | O_CREAT | O_TRUNC, my_open_mask);
  if (result<0) { end_system_call(); OS_file_error(STACK_0); } # report error
  # file was created, result is the Handle.
  # close file again:
  if (!(CLOSE(result)==0)) { end_system_call(); OS_file_error(STACK_0); } # report error
  end_system_call();
 #endif
}

# Open a file for input.
# open_input_file(pathstring,create_if_not_exists,&handle)
# > led the way: assure_dir_exists()
# > pathstring: file name, ASCIZ-String
# > create_if_not_exists: if true, the file must be created
# > STACK_0: pathname
# < handle: open file handle
# < result: whether the file could be opened (necessarily true if create_if_not_exists)
local inline bool open_input_file (char* pathstring, bool create_if_not_exists,
                                   Handle* handle_) {
 #ifdef EMUNIX
  var sintW result;
  # try to open file:
  #ifdef FILE_EXISTS_TRIVIAL
  if (file_exists(_EMA_)) {
    begin_system_call();
    result = open(pathstring,O_RDONLY);
  } else { # file does not exist
    if (!create_if_not_exists) return false;
    # create file with creat:
    begin_system_call();
    result = creat(pathstring,my_open_mask);
  }
  if (result<0) {
    end_system_call(); OS_file_error(STACK_0);
  }
  #else
  # first find out with open, if the file exists:
  begin_system_call();
  result = open(pathstring,O_RDONLY);
  if (result<0) {
    if (errno == ENOENT) { # not found?
      # file does not exist
      if (!create_if_not_exists) { end_system_call(); return false; }
      # create file with creat:
      result = creat(pathstring,my_open_mask);
      if (result<0) { end_system_call(); OS_file_error(STACK_0); }
    } else {
      end_system_call(); OS_file_error(STACK_0); # report error
    }
  }
  #endif
  setmode(result,O_BINARY);
  end_system_call();
  *handle_ = result; return true;
 #endif
 #ifdef AMIGAOS
  var Handle handle;
  #ifdef FILE_EXISTS_TRIVIAL
  if (file_exists(_EMA_)) {
    begin_system_call();
    handle = Open(pathstring,MODE_OLDFILE);
  } else { # file does not exist
    if (!create_if_not_exists) return false;
    # create file with Open:
    begin_system_call();
    handle = Open(pathstring,MODE_READWRITE);
  }
  #else
  # first find out with Open, if the file exists:
  begin_system_call();
  handle = Open(pathstring,MODE_OLDFILE);
  if (handle==Handle_NULL) {
    if (IoErr()==ERROR_OBJECT_NOT_FOUND) {
      # file does not exist
      if (!create_if_not_exists) { end_system_call(); return false; }
      # create file with Open:
      handle = Open(pathstring,MODE_READWRITE);
    }
  }
  #endif
  end_system_call();
  if (handle==Handle_NULL) { OS_file_error(STACK_0); }
  *handle_ = handle; return true;
 #endif
 #if defined(UNIX) || defined(RISCOS)
  var int result;
  #ifdef FILE_EXISTS_TRIVIAL
  var int oflags = O_RDONLY | O_BINARY;
  if (!file_exists(_EMA_)) {
    # file does not exist
    if (!create_if_not_exists) return false;
    # create file with open:
    oflags |= O_CREAT;
  }
  begin_system_call();
  result = OPEN(pathstring,oflags,my_open_mask);
  end_system_call();
  if (result<0) { OS_file_error(STACK_0); }
  #else
  var int oflags = O_RDONLY | O_BINARY;
  if (create_if_not_exists) { oflags |= O_CREAT; }
  begin_system_call();
  result = OPEN(pathstring,oflags,my_open_mask);
  if (result<0) {
    if (errno == ENOENT) { # not found?
      # file does not exist
      if (!create_if_not_exists) { end_system_call(); return false; }
    }
    end_system_call(); OS_file_error(STACK_0); # report error
  }
  end_system_call();
  #endif
  *handle_ = result; return true;
 #endif
 #ifdef WIN32_NATIVE
  var Handle handle;
  #ifdef FILE_EXISTS_TRIVIAL
  var DWORD flag = OPEN_EXISTING;
  if (!file_exists(_EMA_)) { # file does not exist
    if (!create_if_not_exists) return false;
    # create file with CreateFile:
    flag = OPEN_ALWAYS;
  }
  begin_system_call();
  handle = CreateFile(pathstring, GENERIC_READ,
                      FILE_SHARE_READ | FILE_SHARE_WRITE,
                      NULL, flag, FILE_ATTRIBUTE_NORMAL, NULL);
  end_system_call();
  if (handle==INVALID_HANDLE_VALUE) { OS_file_error(STACK_0); }
  #else
  var DWORD flag = OPEN_EXISTING;
  if (create_if_not_exists) { flag = OPEN_ALWAYS; }
  begin_system_call();
  handle = CreateFile(pathstring, GENERIC_READ,
                      FILE_SHARE_READ | FILE_SHARE_WRITE,
                      NULL, flag, FILE_ATTRIBUTE_NORMAL, NULL);
  if (handle==INVALID_HANDLE_VALUE) {
    if (WIN32_ERROR_NOT_FOUND) { # not found?
      # file does not exist
      if (!create_if_not_exists) { end_system_call(); return false; }
    }
    end_system_call(); OS_file_error(STACK_0); # report Error
  }
  end_system_call();
  #endif
  *handle_ = handle; return true;
 #endif
}

#if defined(UNIX) || defined(AMIGAOS) || defined(RISCOS) || defined(WIN32_NATIVE)
# Open a file for output.
# open_output_file(pathstring,truncate_if_exists)
# > pathstring: file name, ASCIZ-String
# > truncate_if_exists: if true, the file is truncated to zero size
# > STACK_0: pathname
# < result: open file handle
local inline Handle open_output_file (char* pathstring,
                                      bool truncate_if_exists) {
 #ifdef AMIGAOS
  begin_system_call();
  var Handle handle = Open(pathstring, (truncate_if_exists ? MODE_NEWFILE : MODE_READWRITE));
  end_system_call();
  if (handle==Handle_NULL) { OS_file_error(STACK_0); } # report error
  return handle;
 #endif
 #if defined(UNIX) || defined(RISCOS)
  begin_system_call();
  var int result =
    OPEN(pathstring,
         (truncate_if_exists ? O_RDWR | O_BINARY | O_CREAT | O_TRUNC
          : O_RDWR | O_BINARY | O_CREAT),
         my_open_mask);
  end_system_call();
  if (result<0) { OS_file_error(STACK_0); } # report error
  return result;
 #endif
 #ifdef WIN32_NATIVE
  begin_system_call();
  var Handle handle = CreateFile(pathstring, GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE,
                                 NULL, (truncate_if_exists ? CREATE_ALWAYS : OPEN_ALWAYS), FILE_ATTRIBUTE_NORMAL, NULL);
  end_system_call();
  if (handle==INVALID_HANDLE_VALUE) { OS_file_error(STACK_0); }
  return handle;
 #endif
}
#endif

/* Create a backup file before opening a file for output.
 create_backup_file(pathstring,delete_backup_file);
 > led the way: assure_dir_exists()
 > pathstring: file name, ASCIZ-String
 > delete_backup_file: if true, delete the backup file
 > STACK_0: pathname
Can trigger GC */
local inline void create_backup_file (char* pathstring,
                                      bool delete_backup_file) {
  var object filename = STACK_0;
  if (openp(filename))
    fehler_rename_open(filename); # do not rename open files!
  var object new_namestring;
 #ifdef EMUNIX
  # extend truename with ".bak" :
  # filename := (merge-pathnames ".bak" filename) :
  filename = copy_pathname(filename); # copy
  ThePathname(filename)->pathname_type = O(backuptype_string); # with Extension "BAK"
  check_delete_open(filename);
  pushSTACK(filename);
  # directory already exists.
  new_namestring = assume_dir_exists(); # filename for the operating system
 #endif
 #if defined(UNIX) || defined(AMIGAOS) || defined(WIN32_NATIVE)
  # extend truename with "%" resp. ".bak" resp. "~" :
  # filename := (parse-namestring (concatenate 'string (namestring filename) "%")) :
  filename = whole_namestring(filename); # as String
  pushSTACK(filename); pushSTACK(O(backupextend_string)); # "%"
  filename = string_concat(2); # concatenate
  pushSTACK(filename); # save
  pushSTACK(filename); # save
  filename = coerce_pathname(filename); # again as filename
  check_delete_open(filename);
  STACK_1 = filename;
  # directory already exists. Do not resolve further links here.
  new_namestring = popSTACK(); # filename for the operating system
 #endif
 #ifdef RISCOS
  # prepend a "~" in front of the name:
  filename = copy_pathname(filename);
  pushSTACK(filename);
  pushSTACK(O(backupprepend_string)); pushSTACK(ThePathname(filename)->pathname_name);
  {
    var object new_name = string_concat(2);
    filename = STACK_0;
    ThePathname(filename)->pathname_name = new_name;
  }
  check_delete_open(filename);
  new_namestring = assure_dir_exists(false,false); # filename for the operating system
 #endif
  with_sstring_0(new_namestring,O(pathname_encoding),new_namestring_asciz, {
    # delete file (or link) with this name, if existing:
    delete_file_before_rename(new_namestring_asciz);
    # rename file from the old name to this name:
    rename_existing_file(pathstring,new_namestring_asciz);
    if (delete_backup_file) { delete_existing_file(new_namestring_asciz); }
  });
  skipSTACK(1);
}

# check the :DIRECTION argument
global direction_t check_direction (object dir) {
  if (!boundp(dir) || eq(dir,S(Kinput)))
    return DIRECTION_INPUT;
  else if (eq(dir,S(Kinput_immutable)))
    return DIRECTION_INPUT_IMMUTABLE;
  else if (eq(dir,S(Koutput)))
    return DIRECTION_OUTPUT;
  else if (eq(dir,S(Kio)))
    return DIRECTION_IO;
  else if (eq(dir,S(Kprobe)))
    return DIRECTION_PROBE;
  else {
    pushSTACK(dir);               # TYPE-ERROR slot DATUM
    pushSTACK(O(type_direction)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(dir); pushSTACK(S(Kdirection));
    pushSTACK(TheSubr(subr_self)->name);
    fehler(type_error,GETTEXT("~: illegal ~ argument ~"));
  }
}

# check the :IF-DOES-NOT-EXIST argument
global if_does_not_exist_t check_if_does_not_exist (object if_not_exist) {
  if (!boundp(if_not_exist))
    return IF_DOES_NOT_EXIST_UNBOUND;
  else if (eq(if_not_exist,S(Kerror)))
    return IF_DOES_NOT_EXIST_ERROR;
  else if (nullp(if_not_exist))
    return IF_DOES_NOT_EXIST_NIL;
  else if (eq(if_not_exist,S(Kcreate)))
    return IF_DOES_NOT_EXIST_CREATE;
  else {
    pushSTACK(if_not_exist);              # TYPE-ERROR slot DATUM
    pushSTACK(O(type_if_does_not_exist)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(if_not_exist); pushSTACK(S(Kif_does_not_exist));
    pushSTACK(S(open));
    fehler(type_error,GETTEXT("~: illegal ~ argument ~"));
  }
}
global object if_does_not_exist_symbol (if_does_not_exist_t if_not_exist) {
  switch (if_not_exist) {
    case IF_DOES_NOT_EXIST_UNBOUND: return unbound;
    case IF_DOES_NOT_EXIST_ERROR: return S(Kerror);
    case IF_DOES_NOT_EXIST_NIL: return NIL;
    case IF_DOES_NOT_EXIST_CREATE: return S(Kcreate);
  }
  NOTREACHED;
}

# check the :IF-EXISTS argument
global if_exists_t check_if_exists (object if_exists) {
  if (!boundp(if_exists))
    return IF_EXISTS_UNBOUND;
  else if (eq(if_exists,S(Kerror)))
    return IF_EXISTS_ERROR;
  else if (nullp(if_exists))
    return IF_EXISTS_NIL;
  else if (eq(if_exists,S(Krename)))
    return IF_EXISTS_RENAME;
  else if (eq(if_exists,S(Krename_and_delete)))
    return IF_EXISTS_RENAME_AND_DELETE;
  else if (eq(if_exists,S(Knew_version)) || eq(if_exists,S(Ksupersede)))
    return IF_EXISTS_SUPERSEDE;
  else if (eq(if_exists,S(Kappend)))
    return IF_EXISTS_APPEND;
  else if (eq(if_exists,S(Koverwrite)))
    return IF_EXISTS_OVERWRITE;
  else {
    pushSTACK(if_exists);         # TYPE-ERROR slot DATUM
    pushSTACK(O(type_if_exists)); # TYPE-ERROR slot EXPECTED-TYPE
    pushSTACK(if_exists); pushSTACK(S(Kif_exists)); pushSTACK(S(open));
    fehler(type_error,GETTEXT("~: illegal ~ argument ~"));
  }
}
global object if_exists_symbol (if_exists_t if_exists) {
  switch (if_exists) {          /* :IF-EXISTS */
    case IF_EXISTS_UNBOUND: return unbound;
    case IF_EXISTS_ERROR: return S(Kerror);
    case IF_EXISTS_NIL: return NIL;
    case IF_EXISTS_RENAME: return S(Krename);
    case IF_EXISTS_RENAME_AND_DELETE: return S(Krename_and_delete);
    case IF_EXISTS_SUPERSEDE: return S(Ksupersede);
    case IF_EXISTS_APPEND: return S(Kappend);
    case IF_EXISTS_OVERWRITE: return S(Koverwrite);
  }
  NOTREACHED;
}

# UP: create a file-stream
# open_file(filename,direction,if_exists,if_not_exists)
# > STACK_3: original filename (may be logical)
# > STACK_2: :BUFFERED argument
# > STACK_1: :EXTERNAL-FORMAT argument
# > STACK_0: :ELEMENT-TYPE argument
# > filename: filename, a pathname
# > direction: direction_t (see lispbibl.d)
# > if_exists: :IF-EXISTS argument if_exists_t (see lispbibl.d)
# > if_not_exists: :IF-DOES-NOT-EXIST argument (see lispbibl.d)
# < result: Stream or NIL
# < STACK: cleaned up
# can trigger GC
local object open_file (object filename, direction_t direction,
                        if_exists_t if_exists,
                        if_does_not_exist_t if_not_exists) {
  pushSTACK(STACK_3); # save filename
  # Directory must exist:
  var object namestring = # File name for the operating system
    # tolerant only if :PROBE and if_not_exists = UNBOUND or NIL
    true_namestring(filename,true,
                    ((direction == DIRECTION_PROBE)
                     && (if_not_exists == IF_DOES_NOT_EXIST_UNBOUND))
                    || (if_not_exists == IF_DOES_NOT_EXIST_NIL));
  if (eq(namestring,nullobj))
    # path to the file does not exist,
    # and :IF-DOES-NOT-EXIST = unbound or NIL
    goto ergebnis_NIL;
  # stack layout: Pathname, Truename.
  # check filename and get the handle:
  var object handle;
 {var bool append_flag = false;
 {switch (direction) {
    case DIRECTION_PROBE:
      if (!file_exists(namestring)) { # file does not exist
        # :IF-DOES-NOT-EXIST decides:
        if (if_not_exists==IF_DOES_NOT_EXIST_ERROR)
          goto fehler_notfound;
        if (if_not_exists==IF_DOES_NOT_EXIST_UNBOUND
            || if_not_exists==IF_DOES_NOT_EXIST_NIL)
          goto ergebnis_NIL;
        # :CREATE -> create the file using open and close:
        with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
          prepare_create(STACK_0);
          create_new_file(namestring_asciz);
        });
      }
      handle = NIL; # Handle := NIL
      break;
    case DIRECTION_INPUT: case DIRECTION_INPUT_IMMUTABLE: { # == :INPUT
      var Handle handl;
      var bool result;
      #ifdef PATHNAME_RISCOS
      if (!file_exists(namestring)) {
        pushSTACK(namestring); prepare_create(STACK_1);
        namestring = popSTACK();
      }
      #endif
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        result = open_input_file(namestring_asciz,
                                 if_not_exists==IF_DOES_NOT_EXIST_CREATE,
                                 &handl);
      });
      if (!result) {
        # :IF-DOES-NOT-EXIST decides:
        if (if_not_exists==IF_DOES_NOT_EXIST_NIL)
          goto ergebnis_NIL;
        else # UNBOUND or :ERROR -> Error
          goto fehler_notfound;
      }
      handle = allocate_handle(handl);
    }
      break;
    default: # DIRECTION is :OUTPUT or :IO
      # default for if_not_exists depends on if_exists:
      if (if_not_exists==IF_DOES_NOT_EXIST_UNBOUND) {
        if (if_exists!=IF_EXISTS_APPEND && if_exists!=IF_EXISTS_OVERWRITE)
          # (if_exists<IF_EXISTS_APPEND)
          # if_exists = :APPEND or :OVERWRITE -> if_not_exists unchanged,
          # otherwise :CREATE is the default
          if_not_exists = IF_DOES_NOT_EXIST_CREATE;
      }
      # default for if_exists is :SUPERSEDE (= :NEW-VERSION) :
      if (if_exists==IF_EXISTS_UNBOUND)
        if_exists = IF_EXISTS_SUPERSEDE;
      #ifdef EMUNIX
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        # when if_exists=IF_EXISTS_SUPERSEDE and
        # if_not_exists=IF_DOES_NOT_EXIST_CREATE we can go for
        # CREATE right away, otherwise must first try OPEN:
        if (!((if_exists==IF_EXISTS_SUPERSEDE)
              && (if_not_exists==IF_DOES_NOT_EXIST_CREATE))) {
          begin_system_call(); # try to open file
          var sintW ergebnis = open(namestring_asciz,O_RDWR);
          if (ergebnis<0) {
            if (errno == ENOENT) { # not found?
              # file does not exist
              end_system_call();
              # :IF-DOES-NOT-EXIST decides:
              if (if_not_exists==IF_DOES_NOT_EXIST_UNBOUND
                  || if_not_exists==IF_DOES_NOT_EXIST_ERROR)
                goto fehler_notfound;
              if (if_not_exists==IF_DOES_NOT_EXIST_NIL)
                goto ergebnis_NIL;
              # :CREATE
            } else { # report error
              end_system_call(); OS_file_error(STACK_0);
            }
          } else {
            # file exists, return the handle
            # :IF-EXISTS decides:
            switch (if_exists) {
              case IF_EXISTS_ERROR: # close and error
                if (CLOSE(ergebnis) < 0) {
                  end_system_call(); OS_file_error(STACK_0);
                }
                end_system_call();
                goto fehler_exists;
              case IF_EXISTS_NIL: # close and NIL
                if (CLOSE(ergebnis) < 0) {
                  end_system_call(); OS_file_error(STACK_0);
                }
                end_system_call();
                goto ergebnis_NIL;
              case IF_EXISTS_APPEND:
                append_flag = true; # position at the end
              case IF_EXISTS_OVERWRITE: # use the existing file
                setmode(ergebnis,O_BINARY);
                end_system_call();
                handle = allocate_handle(ergebnis);
                goto handle_ok;
              default: ;
                # :RENAME :RENAME-AND-DELETE -> rename file; open again
                # :NEW-VERSION, :SUPERSEDE -> truncate file to 0 length
            }
            # in both cases - close the file
            if (CLOSE(ergebnis) < 0) {
              end_system_call(); OS_file_error(STACK_0);
            }
            end_system_call();
            if ((if_exists==IF_EXISTS_RENAME)
                || (if_exists==IF_EXISTS_RENAME_AND_DELETE)) {
              # :RENAME or :RENAME-AND-DELETE -> rename:
              create_backup_file(namestring_asciz,
                                 if_exists==IF_EXISTS_RENAME_AND_DELETE);
            }
          }
        }
        # create file
        begin_system_call();
        var sintW ergebnis = creat(namestring_asciz,my_open_mask);
        if (ergebnis<0) {
          end_system_call(); OS_file_error(STACK_0);
        }
        setmode(ergebnis,O_BINARY);
        end_system_call();
        # new file created, return the handle
        handle = allocate_handle(ergebnis);
      });
      #endif
      #if defined(UNIX) || defined(AMIGAOS) || defined(RISCOS) || defined(WIN32_NATIVE)
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        if (file_exists(namestring)) {
          # file exists
          # :IF-EXISTS decides:
          switch (if_exists) {
            case IF_EXISTS_ERROR:
              goto fehler_exists;
            case IF_EXISTS_NIL:
              goto ergebnis_NIL;
            case IF_EXISTS_RENAME: case IF_EXISTS_RENAME_AND_DELETE:
              create_backup_file(namestring_asciz,
                                 if_exists==IF_EXISTS_RENAME_AND_DELETE);
              break;
            case IF_EXISTS_APPEND:
              append_flag = true; # position at the end
            default: ;
              # :OVERWRITE -> use the existing file
              # :NEW-VERSION, :SUPERSEDE -> truncate the file at 0 length
          }
        } else {
          # file does not exist
          # :IF-DOES-NOT-EXIST decides:
          if (if_not_exists==IF_DOES_NOT_EXIST_UNBOUND
              || if_not_exists==IF_DOES_NOT_EXIST_ERROR)
            goto fehler_notfound;
          if (if_not_exists==IF_DOES_NOT_EXIST_NIL)
            goto ergebnis_NIL;
          # :CREATE
        }
        prepare_create(STACK_0);
        # open file:
        # if-exists: if if_exists<IF_EXISTS_APPEND delete contents;
        # othersise (with :APPEND, :OVERWRITE) preserve contents.
        # if-not-exists: create new file.
        var Handle handl =
          open_output_file(namestring_asciz,# if_exists<IF_EXISTS_APPEND
                           (if_exists!=IF_EXISTS_APPEND
                            && if_exists!=IF_EXISTS_OVERWRITE));
        handle = allocate_handle(handl);
      });
      #endif
      break;
      # STACK_0 = Truename, FILE-ERROR slot PATHNAME
  fehler_notfound: # error: file not found
      fehler_file_not_exists();
  fehler_exists: # error: file already exists
      fehler_file_exists();
 }}
 handle_ok:
  # handle and append_flag are done with.
  # make the Stream:
  pushSTACK(STACK_4); # :BUFFERED argument
  pushSTACK(STACK_4); # :EXTERNAL-FORMAT argument
  pushSTACK(STACK_4); # :ELEMENT-TYPE argument
  pushSTACK(handle);
  {var object stream = make_file_stream(direction,append_flag,true);
   skipSTACK(4);
   return stream;
 }}
 ergebnis_NIL: # return NIL
  skipSTACK(6); # forget both Pathnames and three arguments
  return NIL;
}

# (OPEN filename :direction :element-type :if-exists :if-does-not-exist
#                :external-format :buffered)
LISPFUN(open,seclass_default,1,0,norest,key,6,
        (kw(direction),kw(element_type),kw(if_exists),
         kw(if_does_not_exist),kw(external_format),kw(buffered)) ) {
  var object filename = STACK_6; # filename
  if (builtin_stream_p(filename)) {
    # must be file-stream:
    filename = as_file_stream(filename);
    test_file_stream_named(filename);
    # streamtype file-stream -> use truename:
    filename = TheStream(filename)->strm_file_truename;
    pushSTACK(filename);
  } else {
    filename = coerce_xpathname(filename); # turn into a pathname
    pushSTACK(filename);
   #ifdef LOGICAL_PATHNAMES
    # Convert from logical to physical pathname:
    if (logpathnamep(filename))
      filename = coerce_pathname(filename);
   #endif
  }
  # Stack layout: filename-arg, direction, element-type, if-exists,
  #               if-does-not-exist, external-format, buffered, origpathname.
  # filename is now a pathname.
  var direction_t direction = check_direction(STACK_(5+1));
  var if_exists_t if_exists = check_if_exists(STACK_(3+1));
  var if_does_not_exist_t if_not_exists=check_if_does_not_exist(STACK_(2+1));
  # :element-type is checked later.
  # :external-format is checked later.
  # :buffered is checked later.
  # open file:
  STACK_4 = STACK_5; STACK_5 = STACK_2; STACK_6 = STACK_1; STACK_7 = STACK_0;
  skipSTACK(4);
  VALUES1(open_file(filename,direction,if_exists,if_not_exists));
}

/* UP: Returns a list of all matching pathnames.
 directory_search(pathname,dir_search_param)
 > pathname: pathname with device /= :WILD
 > dir_search_param: :if-does-not-exist, :circle flag, :full flag
 < result:
     if name=NIL and type=NIL:     list of all matching directories,
     else (name=NIL -> name=:WILD):  list of all matching files.
     as absolute pathname without wildcards at a time,
     resp. for files and Full-Flag /=NIL as list
          (Pathname Write-Date Length)
          with Pathname without :WILD/:WILD-INFERIORS-components,
               Write-Date = Date of file creation (ss mm hh dd mm yy),
                 as Decoded-Time suitable for ENCODE-UNIVERSAL-TIME,
               Length = Length of the file (in Bytes).
 Method: Breadth-first-search (=> only one search operation runs at a time)
 can trigger GC */
typedef enum {
  DIR_IF_NONE_DISCARD, DIR_IF_NONE_ERROR, DIR_IF_NONE_KEEP, DIR_IF_NONE_IGNORE
} dir_search_if_none_t;
typedef struct {
  dir_search_if_none_t if_none;
  bool full_p;
  bool circle_p;
} dir_search_param_t;
local object directory_search (object pathname, dir_search_param_t *dsp);

#if defined(MSDOS) || defined(WIN32_NATIVE)
  # Common set of macros for directory search.
  #ifdef MSDOS
    #define READDIR_wildnametype_suffix  O(wild_wild_string) # "*.*"
    #define READDIR_var_declarations  \
      var struct ffblk DTA_buffer; \
      set_break_sem_4(); # impede breaks because of DTA-Buffer
    #define READDIR_end_declarations  \
      clr_break_sem_4();
    #define READDIR_findfirst(pathstring,error_statement,done_statement)  \
      if (findfirst(pathstring,&DTA_buffer,FA_DIREC|FA_ARCH|FA_RDONLY) <0) \
        { if (!((errno==ENOENT) || (errno==ENOMORE)))                      \
            { error_statement }                                            \
          else                                                             \
            { done_statement }                                             \
        }
    #define READDIR_findnext(error_statement,done_statement)  \
      if (findnext(&DTA_buffer) <0)                                        \
        { if (!((errno==ENOENT) || (errno==ENOMORE)))                      \
            { error_statement }                                            \
          else                                                             \
            { done_statement }                                             \
        }
    #define READDIR_entry_name()  (&DTA_buffer.ff_name[0])
    #define READDIR_entry_ISDIR()  (DTA_buffer.ff_attrib & FA_DIREC)
    #define READDIR_entry_timedate(timepointp)  \
      convert_timedate((uintW)DTA_buffer.ff_ftime,(uintW)DTA_buffer.ff_fdate,timepointp);
    #define READDIR_entry_size()  (*(uintL*)(&DTA_buffer.ff_fsize))
  #endif
  #ifdef WIN32_NATIVE
    #define READDIR_wildnametype_suffix  O(wild_string) # "*"
    #define READDIR_var_declarations  \
      var WIN32_FIND_DATA filedata; \
      var HANDLE search_handle;
    #define READDIR_end_declarations
    #define READDIR_findfirst(pathstring,error_statement,done_statement) \
      if ((search_handle = FindFirstFile(pathstring,&filedata))          \
          == INVALID_HANDLE_VALUE) {                                     \
        if (!WIN32_ERROR_NOT_FOUND) { error_statement }                  \
        else { done_statement }                                          \
      }
    #define READDIR_findnext(error_statement,done_statement)    \
      if (!FindNextFile(search_handle,&filedata)) {             \
        if (!(GetLastError()==ERROR_NO_MORE_FILES)              \
              || !FindClose(search_handle))                     \
            { error_statement }                                 \
          else { done_statement }                               \
      }
    #define READDIR_entry_name()  (&filedata.cFileName[0])
    #define READDIR_entry_ISDIR()  (filedata.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
    #define READDIR_entry_timedate(timepointp)  \
      { var FILETIME* pftimepoint = &filedata.ftLastWriteTime;               \
        if (pftimepoint->dwLowDateTime==0 && pftimepoint->dwHighDateTime==0) \
          pftimepoint = &filedata.ftCreationTime;                            \
        convert_time(pftimepoint,timepointp);                                \
      }
    #define READDIR_entry_size()  filedata.nFileSizeLow
  #endif
#endif

#if defined(UNIX) || defined(RISCOS)
# Just like stat(), except that directories or files which would lead
# to problems are silently hidden.
local inline int stat_for_search (char* pathstring, struct stat * statbuf) {
 #ifdef UNIX_LINUX
  # Avoid searching /proc: It is a zoo containing strange animals:
  # directories which go away constantly, pseudo-regular files which
  # are really pipes, etc.
  if (asciz_equal(pathstring,"/proc")) { errno = ENOENT; return -1; }
 #endif
  var int result = stat(pathstring,statbuf);
 #ifdef UNIX_CYGWIN32
  if ((result < 0) && (errno == EACCES)) { errno = ENOENT; }
 #endif
  return result;
}
#endif

#if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
#
# UP: Extends the directory of a pathname by one component.
# > STACK_1: a pathname
# > STACK_0: new Subdir-component, a Simple-String
# < result: new pathname with by subdir lengthened directory
# increases STACK by 2
# can trigger GC
local object pathname_add_subdir (void) {
  # copy pathname and lengthen its directory according to
  # (append x (list y)) = (nreverse (cons y (reverse x))) :
  var object pathname = copy_pathname(STACK_1);
  STACK_1 = pathname;
  pushSTACK(reverse(ThePathname(pathname)->pathname_directory));
  var object new_cons = allocate_cons();
  Cdr(new_cons) = popSTACK();
  Car(new_cons) = popSTACK();
  new_cons = nreverse(new_cons);
  pathname = popSTACK();
  ThePathname(pathname)->pathname_directory = new_cons;
  return pathname;
}

#if defined(UNIX) || defined(AMIGAOS) || defined(RISCOS)
# UP: extends a pathname by the file-information.
# > STACK_1: absolute pathname
# > STACK_0: absolute pathname, links resolved
# > *filestatus: its stat-info
# < STACK_0: list (Pathname Truename Write-Date Length [Comment])
#            in :FULL-Format
local void with_stat_info (void) {
  var object newlist;
 #if defined(UNIX) || defined(RISCOS)
  var uintL size = filestatus->st_size;
 #endif
 #ifdef AMIGAOS
  var uintL size = filestatus->fib_Size;
 #endif
  # Pathname already in STACK_1, as 1. list element
  # Truename already in STACK_0, as 2. list element
  {
    var decoded_time_t timepoint; # Write-Date in decoded form
   #if defined(UNIX) || defined(RISCOS)
    convert_time(&filestatus->st_mtime,&timepoint);
   #endif
   #ifdef AMIGAOS
    convert_time(&filestatus->fib_Date,&timepoint);
   #endif
    pushSTACK(timepoint.Sekunden);
    pushSTACK(timepoint.Minuten);
    pushSTACK(timepoint.Stunden);
    pushSTACK(timepoint.Tag);
    pushSTACK(timepoint.Monat);
    pushSTACK(timepoint.Jahr);
    newlist = listof(6); # build 6-element list
  }
  pushSTACK(newlist); # as 3. list element
  pushSTACK(UL_to_I(size)); # length as 4. list element
 #if defined(UNIX) || defined(RISCOS)
  newlist = listof(4); # build 4-element list
 #endif
 #ifdef AMIGAOS
  pushSTACK(asciz_to_string(&filestatus->fib_Comment[0],O(pathname_encoding))); # comment as 5. list element
  newlist = listof(5); # build 5-element list
 #endif
  pushSTACK(Car(newlist)); # pathname again in the stack
  pushSTACK(newlist); # list in the stack
}
#endif

# Check whether a directory exists.
# check_stat_directory(namestring_asciz,error_statement,exists_statement);
# If the directory does not exist or is a file, does nothing.
#if defined(UNIX) || defined(RISCOS)
  #define check_stat_directory(namestring_asciz,error_statement,exists_statement)  \
    { var struct stat status;                                  \
      begin_system_call();                                     \
      if (!( stat(namestring_asciz,&status) ==0))              \
        { if (!(errno==ENOENT))                                \
            { end_system_call(); error_statement }             \
            else                                               \
            # subdirectory does not exist -> OK.               \
            { end_system_call(); }                             \
        }                                                      \
        else                                                   \
        # file exists.                                         \
        { end_system_call();                                   \
          if (S_ISDIR(status.st_mode)) # is it a directory?    \
            { exists_statement }                               \
    }   }
#endif
#ifdef AMIGAOS
  #define check_stat_directory(namestring_asciz,error_statement,exists_statement)  \
    { var LONGALIGNTYPE(struct FileInfoBlock) fib;                       \
      var struct FileInfoBlock * fibptr = LONGALIGN(&fib);               \
      set_break_sem_4();                                                 \
      begin_system_call();                                               \
     {var BPTR lock = Lock(namestring_asciz,ACCESS_READ);                \
      if (lock==BPTR_NULL)                                               \
        { if (!(IoErr()==ERROR_OBJECT_NOT_FOUND))                        \
            { end_system_call(); clr_break_sem_4(); error_statement }    \
            else                                                         \
            # subdirectory does not exist -> OK.                         \
            { end_system_call(); clr_break_sem_4(); }                    \
        }                                                                \
        else                                                             \
        # file exists.                                                   \
        { if (! Examine(lock,fibptr) )                                   \
            { UnLock(lock);                                              \
              end_system_call(); clr_break_sem_4();                      \
              error_statement                                            \
            }                                                            \
            else                                                         \
            { UnLock(lock);                                              \
              end_system_call(); clr_break_sem_4();                      \
              if (fibptr->fib_DirEntryType >= 0) # is it a directory?    \
                { exists_statement }                                     \
    }}  }   }
#endif
#ifdef WIN32_NATIVE
  #define check_stat_directory(namestring_asciz,error_statement,exists_statement)  \
    { var DWORD fileattr;                                                  \
      begin_system_call();                                                 \
      fileattr = GetFileAttributes(namestring_asciz);                      \
      if (fileattr == 0xFFFFFFFF)                                          \
        { if (!WIN32_ERROR_NOT_FOUND) \
            { end_system_call(); error_statement }                         \
            else                                                           \
            # subdirectory does not exist -> OK.                           \
            { end_system_call(); }                                         \
        }                                                                  \
        else                                                               \
        # File existiert.                                                  \
        { end_system_call();                                               \
          if (fileattr & FILE_ATTRIBUTE_DIRECTORY) # is it a directory?    \
            { exists_statement }                                           \
    }   }
#endif

#if !defined(MSDOS)
# Search for a subdirectory with a given name.
# directory_search_1subdir(subdir,namestring);
# > STACK_0 = pathname
# > STACK_(3+1) = new-pathname-list
# > subdir: the new directory component to add to the pathname, if it exists
# > namestring: the namestring (for the OS)
# < STACK_0: replaced
# < STACK_(3+1): augmented
# can trigger GC

#if !defined(WIN32_NATIVE)
local void directory_search_1subdir (object subdir, object namestring) {
  with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
    check_stat_directory(namestring_asciz,
    { OS_file_error(STACK_0); },
    { # copy pathname and lengthen its directory by subdir:
      pushSTACK(subdir);
      {
        var object pathname = pathname_add_subdir();
        pushSTACK(pathname);
      }
      { # push this new pathname in front of new-pathname-list:
        var object new_cons = allocate_cons();
        Car(new_cons) = STACK_0;
        Cdr(new_cons) = STACK_(3+1);
        STACK_(3+1) = new_cons;
      }
    });
  });
}
#else
local void directory_search_1subdir (object subdir, object namestring) {
  with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
    char resolved[MAX_PATH];
    if (real_path(namestring_asciz,resolved)) {
      # copy pathname and lengthen its directory by subdir:
      pushSTACK(subdir);
      {
        var object pathname = pathname_add_subdir();
        pushSTACK(pathname);
      }
      { # push this new pathname in front of new-pathname-list:
        var object new_cons = allocate_cons();
        Car(new_cons) = STACK_0;
        Cdr(new_cons) = STACK_(3+1);
        STACK_(3+1) = new_cons;
      }
    }
  });
}
#endif
#endif

#if defined(UNIX) || defined(WIN32_NATIVE)
# Returns a truename dependent hash code for a directory.
# directory_search_hashcode()
# STACK_0 = dir_namestring
# STACK_1 = pathname
# < result: a hash code, or nullobj if the directory does not exist
# can trigger GC

#ifdef UNIX
# return (cons drive inode)
local object directory_search_hashcode (void) {
  pushSTACK(STACK_0); # Directory-Name
  pushSTACK(O(dot_string)); # and "."
  var object namestring = string_concat(2); # concatenate
  var struct stat status;
  with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
    begin_system_call();
    if (!( stat(namestring_asciz,&status) ==0)) { # get information
      end_system_call();
      FREE_DYNAMIC_ARRAY(namestring_asciz);
      return nullobj;
    }
    end_system_call();
  });
  # entry exists (oh miracle...)
  pushSTACK(UL_to_I(status.st_dev)); # Device-Number and
  pushSTACK(UL_to_I(status.st_ino)); # Inode-Number
  var object new_cons = allocate_cons(); # cons them together
  Cdr(new_cons) = popSTACK(); Car(new_cons) = popSTACK();
  return new_cons;
}
#else
# win32 - there is stat but no inodes
# using directory truenames as hashcodes
local object directory_search_hashcode (void) {
  return STACK_0;
}
#endif
#endif

#if defined(UNIX) || defined(RISCOS)
# Tests whether a directory entry actually exists.
# (It could be a link pointing to nowhere, or an undesired directory.)
# directory_search_direntry_ok(namestring,&statbuf)
# STACK_2 = pathname
# < result: true and statbuf filled, or false.
local bool directory_search_direntry_ok (object namestring,
                                         struct stat * statbuf) {
  var bool exists = true;
  with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
    begin_system_call();
    if (!( stat_for_search(namestring_asciz,statbuf) ==0)) {
      if (!((errno==ENOENT) || (errno==ELOOP_VALUE))) {
        end_system_call(); OS_file_error(STACK_2);
      }
      end_system_call();
      exists = false;
    }
    end_system_call();
  });
  return exists;
}
#endif

# Scans an entire directory.
# directory_search_scandir(recursively,next_task);
# stack layout: result-list, pathname, name&type, subdir-list, pathname-list,
#              new-pathname-list, ht, pathname-list-rest, pathnames-to-insert,
#              pathname, dir_namestring.
local void directory_search_scandir (bool recursively, signean next_task,
                                     dir_search_param_t *dsp) {
 #if defined(UNIX) || defined(RISCOS)
  {
    var object namestring;
   #ifdef UNIX
    pushSTACK(STACK_0); # directory-name
    pushSTACK(O(dot_string)); # and "."
    namestring = string_concat(2); # concatenate
   #endif
   #ifdef RISCOS
    var object wildcard_mask;
    namestring = STACK_0; # directory-name
    namestring = subsstring(namestring,0,Sstring_length(namestring)-1); # directory-name without '.' at the end
    # instead of calling wildcard_match() ourselves, we leave this to the operating system:
    wildcard_mask = (next_task<0 ? Car(STACK_(1+4+3)) : STACK_(2+4+3));
   #endif
    # scan directory:
    var DIR* dirp;
    set_break_sem_4();
   #ifdef UNIX
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      begin_system_call();
      dirp = opendir(namestring_asciz); # open directory
      end_system_call();
    });
   #endif
   #ifdef RISCOS
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      with_sstring_0(wildcard_mask,O(pathname_encoding),wildcard_mask_asciz, {
        # In wildcard_mask_asciz, turn the Wildchar-Characters '?' into synonyms '#' :
        {
          var uintB* ptr = wildcard_mask_asciz;
          while (*ptr != '\0') { if (*ptr == '?') { *ptr = '#'; } ptr++; }
        }
        begin_system_call();
        dirp = opendir(namestring_asciz,wildcard_mask_asciz); # open directory for search
        end_system_call();
      });
    });
   #endif
    if (dirp == (DIR*)NULL) {
      if (dsp->if_none == DIR_IF_NONE_IGNORE) return;
      else OS_file_error(STACK_1);
    }
    loop {
      var SDIRENT* dp;
      begin_system_call();
      errno = 0;
      dp = readdir(dirp); # fetch next directory-entry
      if (dp == (SDIRENT*)NULL) { # error or directory finished
        if (!(errno==0)) { end_system_call(); OS_file_error(STACK_1); }
        end_system_call();
        break;
      }
      end_system_call();
      # convert directory-entry into string:
      var object direntry;
      {
        var uintL direntry_len;
       #if defined(UNIX_CYGWIN32)
        # Neither d_reclen nor d_namlen present in DIR structure.
        direntry_len = asciz_length(dp->d_name);
       #elif defined(HAVE_STRUCT_DIRENT_D_NAMLEN) || defined(__USE_GNU)
        # On UNIX_LINUX direntry_len := dp->d_reclen was sufficient, but in
        # general direntry_len := min(dp->d_reclen,asciz_length(dp->d_name))
        # is necessary. The GNU libc is buggy: it does "#define d_namlen d_reclen",
        # just as the Linux libc-5.0.9.
        {
          var const uintB* ptr = (const uintB*)(&dp->d_name[0]);
          var uintL count;
          direntry_len = 0;
          dotimesL(count,dp->d_reclen, {
            if (*ptr == '\0') break;
            ptr++; direntry_len++;
          });
        }
       #else
        direntry_len = dp->d_namlen;
       #endif
        direntry = n_char_to_string(&dp->d_name[0],direntry_len,O(pathname_encoding));
      }
     #ifndef RISCOS
      # skip "." and ".." :
      if (!(equal(direntry,O(dot_string))
            || equal(direntry,O(dotdot_string))))
     #endif
        {
          pushSTACK(direntry);
          # stack layout: ..., pathname, dir_namestring, direntry.
          # determine, if it is a directory or a file:
          pushSTACK(STACK_1); # Directory-Namestring
          SUBDIR_PUSHSTACK(direntry); # direntry
          var object namestring = string_concat(2); # concatenate
          # get information:
          var struct stat status;
         #if 1 # just an optimization
          if (!recursively) {
            # Try to avoid calling directory_search_direntry_ok(),
            # since it is an expensive operation (it calls stat()).
            if (next_task < 0) {
             #ifndef RISCOS
              # match (car subdir-list) with direntry:
              if (wildcard_match(Car(STACK_(1+4+3)),STACK_0))
             #endif
              if (directory_search_direntry_ok(namestring,&status)) {
                if (S_ISDIR(status.st_mode))
                  goto push_matching_subdir;
              } else
                switch (dsp->if_none) {
                  case DIR_IF_NONE_IGNORE: case DIR_IF_NONE_DISCARD: break;
                  case DIR_IF_NONE_ERROR:
                    pushSTACK(namestring);
                    fehler_file_not_exists();
                  case DIR_IF_NONE_KEEP:
                    goto push_matching_file;
                  default: NOTREACHED;
                }
            } else if (next_task > 0) {
             #ifndef RISCOS
              # match name&type with direntry:
              if (wildcard_match(STACK_(2+4+3),STACK_0))
             #endif
              if (directory_search_direntry_ok(namestring,&status)) {
                if (!S_ISDIR(status.st_mode))
                  goto push_matching_file;
              } else
                switch (dsp->if_none) {
                  case DIR_IF_NONE_IGNORE: case DIR_IF_NONE_DISCARD: break;
                  case DIR_IF_NONE_ERROR:
                    pushSTACK(namestring);
                    fehler_file_not_exists();
                  case DIR_IF_NONE_KEEP:
                    goto push_matching_file;
                  default: NOTREACHED;
                }
            }
            goto done_direntry;
          }
         #endif
          if (directory_search_direntry_ok(namestring,&status)) {
            # entry exists and is not unwanted.
            if (S_ISDIR(status.st_mode)) { # is it a directory?
              # entry is a directory.
              if (recursively) { # all recursive subdirectories wanted?
                # yes -> turn into a pathname and push to
                # pathnames-to-insert (is later insertet in front
                # of pathname-list-rest):
                pushSTACK(STACK_2); pushSTACK(STACK_(0+1)); # pathname and direntry
                {
                  var object pathname = pathname_add_subdir();
                  pushSTACK(pathname);
                }
                { # push this new pathname in front of pathname-to-insert:
                  var object new_cons = allocate_cons();
                  Car(new_cons) = popSTACK();
                  Cdr(new_cons) = STACK_(0+3);
                  STACK_(0+3) = new_cons;
                }
              }
              if (next_task<0) {
               #ifndef RISCOS
                # match (car subdir-list) with direntry:
                if (wildcard_match(Car(STACK_(1+4+3)),STACK_0))
               #endif
                  {
                  push_matching_subdir:
                    # subdirectory matches -> turn into a pathname
                    # and push onto new-pathname-list:
                    pushSTACK(STACK_2); pushSTACK(STACK_(0+1)); # pathname and direntry
                    {
                      var object pathname = pathname_add_subdir();
                      pushSTACK(pathname);
                    }
                    # push this new pathname in front of new-pathname-list:
                    {
                      var object new_cons = allocate_cons();
                      Car(new_cons) = popSTACK();
                      Cdr(new_cons) = STACK_(3+3);
                      STACK_(3+3) = new_cons;
                    }
                  }
              }
            } else {
              # entry is a (halfway) normal File.
              if (next_task>0) {
               #ifndef RISCOS
                # match name&type with direntry:
                if (wildcard_match(STACK_(2+4+3),STACK_0))
               #endif
                  {
                  push_matching_file:
                    # File matches -> turn into a pathname
                    # and push onto result-list:
                   #ifndef PATHNAME_RISCOS
                    pushSTACK(STACK_0); # direntry
                    split_name_type(1); # split into Name and Type
                    {
                      var object pathname = copy_pathname(STACK_(2+2));
                      ThePathname(pathname)->pathname_type = popSTACK(); # insert type
                      ThePathname(pathname)->pathname_name = popSTACK(); # insert name
                      pushSTACK(pathname);
                      pushSTACK(pathname);
                    }
                   #else # PATHNAME_RISCOS
                    {
                      var object pathname = copy_pathname(STACK_2);
                      pushSTACK(pathname);
                      if (name_and_type && nullp(ThePathname(pathname)->pathname_type)) {
                        # Move the last subdir into the type slot of the pathname.
                        # subdirs := (butlast subdirs) = (nreverse (cdr (reverse subdirs)))
                        var object subdirs = reverse(ThePathname(pathname)->pathname_directory);
                        pathname = STACK_0;
                        ThePathname(pathname)->pathname_type = Car(subdirs);
                        ThePathname(pathname)->pathname_directory = nreverse(Cdr(subdirs));
                      }
                      ThePathname(pathname)->pathname_name = STACK_1; # direntry
                      pushSTACK(pathname);
                    }
                   #endif
                    # form truename (resolve symbolic links):
                    if (!eq(nullobj,assure_dir_exists(true,true))
                        && file_exists(_EMA_)) {
                      /* if file (still...) exists */
                      if (dsp->full_p) /* :FULL wanted? */
                        with_stat_info(); # yes -> extend STACK_0
                      { /* and push STACK_0 in front of result-list: */
                        var object new_cons = allocate_cons();
                        Car(new_cons) = STACK_0;
                        Cdr(new_cons) = STACK_(4+4+3+2);
                        STACK_(4+4+3+2) = new_cons;
                      }
                    } else if (dsp->if_none == DIR_IF_NONE_KEEP) {
                      var object new_cons = allocate_cons();
                      Car(new_cons) = STACK_1; /* unresolved pathname */
                      Cdr(new_cons) = STACK_(4+4+3+2);
                      STACK_(4+4+3+2) = new_cons;
                    }
                    skipSTACK(2);
                  }
              }
            }
          } else
            switch (dsp->if_none) {
              case DIR_IF_NONE_IGNORE: case DIR_IF_NONE_DISCARD: break;
              case DIR_IF_NONE_ERROR:
                pushSTACK(namestring);
                fehler_file_not_exists();
              case DIR_IF_NONE_KEEP:
                goto push_matching_file;
              default: NOTREACHED;
            }
         done_direntry:
          skipSTACK(1); # forget direntry
        }
    }
    begin_system_call();
    if (CLOSEDIR(dirp)) { end_system_call(); OS_file_error(STACK_1); }
    end_system_call();
    clr_break_sem_4();
  }
 #endif
 #ifdef AMIGAOS
  { # search through directory:
    var object namestring = OSdirnamestring(STACK_0);
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      set_break_sem_4();
      begin_system_call();
      var BPTR lock = Lock(namestring_asciz,ACCESS_READ);
      var LONGALIGNTYPE(struct FileInfoBlock) fib;
      var struct FileInfoBlock * fibptr = LONGALIGN(&fib);
      if (lock==BPTR_NULL) {
        end_system_call();
        if (dsp->if_none == DIR_IF_NONE_IGNORE) {
          FREE_DYNAMIC_ARRAY(namestring_asciz); return;
        } else OS_file_error(STACK_1);
      }
      if (! Examine(lock,fibptr) ) {
        UnLock(lock); end_system_call();
        if (dsp->if_none == DIR_IF_NONE_IGNORE) {
          FREE_DYNAMIC_ARRAY(namestring_asciz); return;
        } else OS_file_error(STACK_1);
      }
      while (ExNext(lock,fibptr)) { /* no error and directory not finished? */
        end_system_call();
        # convert directory-entry into string:
        var object direntry = asciz_to_string(&fibptr->fib_FileName[0],O(pathname_encoding));
        pushSTACK(direntry);
        # stack layout: ..., pathname, dir_namestring, direntry.
        # determine, if it is a directory or a file:
        {
          var bool isdir;
          if (fibptr->fib_DirEntryType == ST_SOFTLINK) {
            # get a lock on the target and execute Examine:
            # this works, because Lock() resolves links (resp. it tries)
            SUBDIR_PUSHSTACK(STACK_1); SUBDIR_PUSHSTACK(STACK_(0+1));
            var object direntry_namestring = string_concat(2);
            with_sstring_0(direntry_namestring,O(pathname_encoding),direntry_namestring_asciz, {
              begin_system_call();
              # TODO olddir = CurrentDir(lock); ... CurrentDir(olddir)
              var BPTR direntry_lock = Lock(direntry_namestring_asciz,ACCESS_READ);
              if (direntry_lock==BPTR_NULL)
                switch (IoErr()) {
                  case ERROR_OBJECT_NOT_FOUND:
                  case ERROR_DEVICE_NOT_MOUNTED: # user canceled requester
                    end_system_call();
                    FREE_DYNAMIC_ARRAY(direntry_namestring_asciz);
                    goto skip_direntry; # forget direntry and ignore
                  default:
                    end_system_call(); OS_file_error(STACK_2);
                }
              var LONGALIGNTYPE(struct FileInfoBlock) direntry_status;
              var struct FileInfoBlock * statusptr = LONGALIGN(&direntry_status);
              if (! Examine(direntry_lock,statusptr) ) {
                UnLock(direntry_lock); end_system_call(); OS_file_error(STACK_2);
              }
              UnLock(direntry_lock);
              end_system_call();
              isdir = (statusptr->fib_DirEntryType >= 0);
            });
          } else {
            isdir = (fibptr->fib_DirEntryType >= 0);
          }
          if (isdir) {
            # entry is a directory.
            if (recursively) { # all recursive subdirectories wanted?
              # yes -> turn into a pathname and push
              # onto pathnames-to-insert (is inserted in
              # front of pathname-list-rest afterwards):
              pushSTACK(STACK_2); pushSTACK(STACK_(0+1)); # pathname and direntry
              {
                var object pathname = pathname_add_subdir();
                pushSTACK(pathname);
              }
              { # push this new pathname in front of pathname-to-insert:
                var object new_cons = allocate_cons();
                Car(new_cons) = popSTACK();
                Cdr(new_cons) = STACK_(0+3);
                STACK_(0+3) = new_cons;
              }
            }
            if (next_task<0) {
              # match (car subdir-list) with direntry:
              if (wildcard_match(Car(STACK_(1+4+3)),STACK_0)) {
                # subdirectory matches -> turn into a pathname
                # and push onto new-pathname-list:
                pushSTACK(STACK_2); pushSTACK(STACK_(0+1)); # pathname and direntry
                {
                  var object pathname = pathname_add_subdir();
                  pushSTACK(pathname);
                }
                # push this new pathname in front of new-pathname-list:
                {
                  var object new_cons = allocate_cons();
                  Car(new_cons) = popSTACK();
                  Cdr(new_cons) = STACK_(3+3);
                  STACK_(3+3) = new_cons;
                }
              }
            }
          } else {
            # entry is a (halfway) normal file.
            if (next_task>0) {
              # match name&type with direntry:
              if (wildcard_match(STACK_(2+4+3),STACK_0)) {
                # File matches -> turn into a pathname
                # and push onto result-list:
                pushSTACK(STACK_0); # direntry
                split_name_type(1); # split up in Name and Type
                {
                  var object pathname = copy_pathname(STACK_(2+2));
                  ThePathname(pathname)->pathname_type = popSTACK(); # insert type
                  ThePathname(pathname)->pathname_name = popSTACK(); # insert name
                  pushSTACK(pathname);
                  pushSTACK(pathname);
                }
                assure_dir_exists(true,false); # build truename (resolve symbolic links)
                if (dsp->full_p) /* :FULL wanted? */
                  with_stat_info(); # yes -> extend STACK_0
                # and push STACK_0 on front of result-list:
                {
                  var object new_cons = allocate_cons();
                  Car(new_cons) = STACK_0;
                  Cdr(new_cons) = STACK_(4+4+3+2);
                  STACK_(4+4+3+2) = new_cons;
                }
                skipSTACK(2);
              }
            }
          }
        }
      skip_direntry:
        skipSTACK(1); # forget direntry
        begin_system_call();
      }
      UnLock(lock);
      if (!(IoErr()==ERROR_NO_MORE_ENTRIES)) {
        end_system_call(); OS_file_error(STACK_1);
      }
      end_system_call();
      clr_break_sem_4();
    });
  }
 #endif
 #if defined(MSDOS) || defined(WIN32_NATIVE)
  {
    SUBDIR_PUSHSTACK(STACK_0); # Directory-Name
    pushSTACK(READDIR_wildnametype_suffix); # and concatenate
    var object namestring = string_concat(2); # "*.*" resp. "*"
    with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
      # scan directory, according to DOS-convention resp. Win32-convention:
      READDIR_var_declarations;
      # start of search, search for folders and normal files:
      begin_system_call();
      do {
        # readdir in resolved directory. directory was resolved earlier
        READDIR_findfirst(namestring_asciz,{
          end_system_call();
          if (dsp->if_none == DIR_IF_NONE_IGNORE) {
            FREE_DYNAMIC_ARRAY(namestring_asciz); return;
          } else OS_file_error(STACK_1);
        }, break; );
        loop {
          end_system_call();
          # convert directory-entry into string:
          var object direntry = asciz_to_string(READDIR_entry_name(),O(pathname_encoding));
          # skip "." and "..":
          if (!(equal(direntry,O(dot_string))
                || equal(direntry,O(dotdot_string)))) {
            var shell_shortcut_target_t rresolved = shell_shortcut_notresolved;
            pushSTACK(direntry);
            # stack layout: ..., pathname, dir_namestring, direntry.
            pushSTACK(NIL);       # will become found file full pathname,
                                  # changed with symbolic name for resolved (maybe nonfound) links
            pushSTACK(NIL);       # true pathname of it or whatever result to return
            pushSTACK(direntry);  # here will come filename to wildcard match
            split_name_type(1);
            # stack layout: ..., pathname, dir_namestring, direntry, NIL, NIL, direntry-name, direntry-type.

            # make full name of found file - dir + direntry
            # TODO: optimize to not do it when it not needed
            if (READDIR_entry_ISDIR()) {
              pushSTACK(STACK_(6)); pushSTACK(STACK_(4+1)); # pathname and direntry
              STACK_(3) = pathname_add_subdir();
            } else {
              STACK_(3) = copy_pathname(STACK_(6));
              ThePathname(STACK_(3))->pathname_type = STACK_0; # insert type
              ThePathname(STACK_(3))->pathname_name = STACK_1; # insert name
            }

            # try to resolve .lnk files
            if (!READDIR_entry_ISDIR() && !nullp(STACK_0)
                && string_equal(STACK_0,O(lnk_string)))
            {
              var char resolved[MAX_PATH];
              var char * full_resolved = resolved;
              with_sstring_0(whole_namestring(STACK_(3)),O(pathname_encoding),linkfile_asciiz, {
                rresolved =
                  resolve_shell_shortcut_more(linkfile_asciiz,resolved);
                if (rresolved != shell_shortcut_notresolved) {
                  var char resolved_f[MAX_PATH];
                  if (FullName(resolved,resolved_f))
                    full_resolved = resolved_f;
                  # hack direntry-pathname to make it a symbolic name
                  # symbolic link names are direntry-pathnames w/o ".lnk"
                  # so split the name again
                  # hack it in-place since lnk filename is not need anymore
                  pushSTACK(STACK_1);
                  split_name_type(1);
                  ThePathname(STACK_(3+2))->pathname_name = STACK_1;
                  ThePathname(STACK_(3+2))->pathname_type = STACK_0;
                  skipSTACK(2);
                  # what to use as a result
                  if (rresolved == shell_shortcut_notexists)
                    STACK_(2) = STACK_(3); # use symbolic names as a result when target is not found
                  else
                    STACK_(2) = coerce_pathname(asciz_to_string(full_resolved,O(pathname_encoding)));
                }
              });
            }

            if (rresolved == shell_shortcut_notresolved) {
              # truename is the pathname itself
              STACK_(2) = STACK_(3);
              # nametomatch is direntry
              STACK_(1) = STACK_(4);
            }

            skipSTACK(1); # drop direntry-type
            # stack layout: ..., pathname, dir_namestring, direntry,
            #       direntry-pathname, true-pathname, direntry-name-to-check.

            if (rresolved == shell_shortcut_notexists
                && dsp->if_none == DIR_IF_NONE_ERROR)
                  fehler_file_not_exists();

            if (rresolved != shell_shortcut_notexists
                || (dsp->if_none != DIR_IF_NONE_DISCARD &&
                    dsp->if_none != DIR_IF_NONE_IGNORE)) {
              if (READDIR_entry_ISDIR() || rresolved == shell_shortcut_directory) {
                # nonfound shortcuts are threated as shortcuts to files
                if (recursively) { # all recursive subdirectories wanted?
                  # yes -> push truename onto
                  # pathnames-to-insert (is inserted in front of
                  # pathname-list-rest later):
                  var object new_cons = allocate_cons();
                  Car(new_cons) = STACK_(1);
                  Cdr(new_cons) = STACK_(0+6);
                  STACK_(0+6) = new_cons;
                }
                if (next_task<0) {
                  # match (car subdir-list) with direntry:
                  if (wildcard_match(Car(STACK_(1+4+6)),STACK_0)) {
                    # Subdirectory matches -> push truename onto new-pathname-list:
                    var object new_cons = allocate_cons();
                    Car(new_cons) = STACK_(1);
                    Cdr(new_cons) = STACK_(3+6);
                    STACK_(3+6) = new_cons;
                  }
                }
              } else {
                # entry is a (halfway) normal file.
                if (next_task>0) {
                  if (wildcard_match(STACK_(2+4+6),STACK_0)) {
                    # stack layout: ..., pathname, dir_namestring, direntry,
                    #       direntry-maybhacked-pathname, true-pathname, direntry-name-to-check.
                    # test Full-Flag and poss. get more information:

                    if (dsp->full_p      /* :FULL wanted? */
                         && rresolved != shell_shortcut_notexists) { /* treat nonexisting as :FULL NIL */
                      var decoded_time_t timepoint;
                      var uintL entry_size = 0;
                      # get file attributes into these vars
                      if (rresolved == shell_shortcut_file) { # need another readdir here
                        READDIR_var_declarations;
                        with_sstring_0(whole_namestring(STACK_1),O(pathname_encoding),resolved_asciz, {
                          var bool notfound = false;
                          begin_system_call();
                          READDIR_findfirst(resolved_asciz, notfound = true; , notfound = true; );
                          end_system_call();
                          if (notfound || READDIR_entry_ISDIR()) {
                            # just to be paranoid
                            OS_file_error(STACK_1);
                          }
                          READDIR_entry_timedate(&timepoint);
                          entry_size = READDIR_entry_size();
                        });
                        READDIR_end_declarations;
                      } else {         # easy way
                        READDIR_entry_timedate(&timepoint);
                        entry_size = READDIR_entry_size();
                      }
                      pushSTACK(STACK_(2)); # newpathname as 1st list element
                      pushSTACK(STACK_(1+1)); # resolved pathname as 2nd list element
                      # convert time and date from DOS-format to decoded-time:
                      pushSTACK(timepoint.Sekunden);
                      pushSTACK(timepoint.Minuten);
                      pushSTACK(timepoint.Stunden);
                      pushSTACK(timepoint.Tag);
                      pushSTACK(timepoint.Monat);
                      pushSTACK(timepoint.Jahr);
                      { /* 6-element timestamp ==> the 3rd element */
                        object timestamp = listof(6); pushSTACK(timestamp); }
                      pushSTACK(UL_to_I(entry_size)); /* length ==> 4th */
                      { object fullinfo = listof(4); STACK_1 = fullinfo; }
                    }
                    # now STACK_1 can contain either truename or
                    # list-of-file-information (both for insertion to result-list)
                    # stack layout: ..., pathname, dir_namestring, direntry,
                    #       direntry-maybhacked-pathname, true-pathname-or-list-of-info, direntry-name-to-check.
                    { # push STACK_1 in front of result-list:
                      var object new_cons = allocate_cons();
                      Car(new_cons) = STACK_1;
                      Cdr(new_cons) = STACK_(4+4+6);
                      STACK_(4+4+6) = new_cons;
                    }
                  }
                }
              }
            }
            skipSTACK(4); # forget all up to dir_namestring
          }
          # next file:
          begin_system_call();
          READDIR_findnext({ end_system_call(); OS_file_error(STACK_1); }, break; );
        }
      } while (false);
      end_system_call();
      READDIR_end_declarations;
    });
  }
 #endif
}

local object directory_search (object pathname, dir_search_param_t *dsp) {
 #ifdef PATHNAME_RISCOS
  # If we search for a file with type /= NIL, we have to interpret the last
  # subdir as the type.
  var bool name_and_type = false;
  # We need to remember if the type is wild, since this controls whether
  # found files are legal.
  var bool type_is_wild = false;
 #endif
  pathname = use_default_dir(pathname); # insert default-directory
  # pathname is now new and an absolute pathname.
  pushSTACK(NIL); # result-list := NIL
  pushSTACK(pathname);
  # if name=NIL and type/=NIL: set name := "*".
  if (nullp(ThePathname(pathname)->pathname_name)
      && !nullp(ThePathname(pathname)->pathname_type))
    ThePathname(pathname)->pathname_name = S(Kwild);
 #ifdef PATHNAME_RISCOS
  # If the name and type are both set, then make the type part of
  # the directory specification and set the new type to NIL.
  if (!nullp(ThePathname(pathname)->pathname_name)
      && !nullp(ThePathname(pathname)->pathname_type)) {
    name_and_type = true;
    type_is_wild = wild_p(ThePathname(pathname)->pathname_type,false);
    pushSTACK(pathname); pushSTACK(ThePathname(pathname)->pathname_type);
    STACK_0 = pathname = pathname_add_subdir();
    ThePathname(pathname)->pathname_type = NIL;
  }
 #endif
  # for matching: collect name and type into a string:
  if (nullp(ThePathname(pathname)->pathname_name)) {
    pushSTACK(NIL); # name=NIL -> also type=NIL -> do not search files
  } else {
    var object nametype_string = file_namestring(pathname);
    pathname = STACK_0;
    pushSTACK(nametype_string);
  }
  pushSTACK(ThePathname(pathname)->pathname_directory); # subdir-list
 #ifdef PATHNAME_RISCOS
  STACK_0 = Cdr(STACK_0); # list starts with (:ABSOLUTE :ROOT ...) , shorten it
 #endif
  # copy pathname and thereby discard name and type and
  # shorten directory to (:ABSOLUTE) resp. (:ABSOLUTE :ROOT) :
  pathname = copy_pathname(pathname);
  ThePathname(pathname)->pathname_name = NIL;
  ThePathname(pathname)->pathname_type = NIL;
  ThePathname(pathname)->pathname_directory = O(directory_absolute);
  pushSTACK(pathname);
  { # pack into one-element list:
    var object new_cons = allocate_cons();
    Car(new_cons) = STACK_0;
    STACK_0 = new_cons;
  }
  var bool recursively = # Flag, if the next operation has to be applied
    false;                  # to all subdirectories.
  loop {
    # stack layout: result-list, pathname, name&type, subdir-list,
    #               pathname-list.
    # result-list = list of finished pathnames/lists, reversed.
    # name&type = NIL or Normal-Simple-String,
    #   against which the filenames have to be matched.
    # pathname-list = list of directories to be processed.
    # the pathnames from pathname-list contain the directory
    # only so deep, that afterwards work continues with (cdr subdir-list) .
    # process next subdir-level:
    STACK_1 = Cdr(STACK_1); # shorten subdir-list
    var signean next_task; # what has to be done with the Dirs from pathname-list:
    # 0: nothing, finished
    # 1: look for a file of given namen/type
    # -1: look for a subdirectory of given name
    # 2: look for all files, that match the given name/type
    # -2: look for all subdirectories, that match the given name
    if (matomp(STACK_1)) { # subdir-list finished?
      var object nametype = STACK_2;
      if (nullp(nametype)) # name=NIL and type=NIL -> do not search files
        next_task = 0;
     #if !(defined(MSDOS) || defined(WIN32_NATIVE))
      else if (!wild_p(nametype,false) && (dsp->if_none != DIR_IF_NONE_IGNORE))
        # === !(wild_p(name) || ((!nullp(type)) && wild_p(type)))
        next_task = 1; # search file
     #endif
      else
        next_task = 2; # search files with wildcards
    } else {
      var object next_subdir = Car(STACK_1);
      if (eq(next_subdir,S(Kwild_inferiors))) { # '...' ?
        # will be treated at the next run
        recursively = true; goto passed_subdir;
      }
     #ifndef MSDOS
      if (
       #ifdef PATHNAME_AMIGAOS
          eq(next_subdir,S(Kparent)) ||
       #endif
       #ifdef PATHNAME_RISCOS
          !simple_string_p(next_subdir) ||
       #endif
          !wild_p(next_subdir,false))
        next_task = -1; # search subdir
      else
     #endif
        next_task = -2; # search subdirs with wildcards
    }
    # traverse pathname-list and construct new list:
    pushSTACK(NIL);
   #if defined(UNIX) || defined(WIN32_NATIVE)
    if (dsp->circle_p) { /* query :CIRCLE-Flag */
      # maintain hash-table of all scanned directories so far (as
      # cons (dev . ino)) :
      pushSTACK(S(Ktest)); pushSTACK(S(equal));
      funcall(L(make_hash_table),2); # (MAKE-HASH-TABLE :TEST 'EQUAL)
      pushSTACK(value1);
    } else
   #endif
      pushSTACK(NIL);
    pushSTACK(STACK_(0+2));
    loop {
      # stack layout: ..., new-pathname-list, ht, pathname-list-rest.
      var object pathname_list_rest = STACK_0;
      if (atomp(pathname_list_rest))
        break;
      STACK_0 = Cdr(pathname_list_rest); # shorten list
      pushSTACK(NIL); # pathnames-to-insert := NIL
      # stack layout: ..., new-pathname-list, ht, pathname-list-rest,
      #               pathnames-to-insert.
      {
        var object pathname = Car(pathname_list_rest); # next directory
        pushSTACK(pathname); # into the stack
        # try to shorten the task a little:
        if (!recursively) {
          switch (next_task) {
            case 0: # return this pathname
             #if defined(UNIX) || defined(WIN32_NATIVE)
              assure_dir_exists(false,false); # first resolve links
             #endif
              { # and push STACK_0 in front of result-list:
                var object new_cons = allocate_cons();
                Car(new_cons) = popSTACK();
                Cdr(new_cons) = STACK_(4+4);
                STACK_(4+4) = new_cons;
              }
              goto next_pathname;
           #if !(defined(MSDOS) || defined(WIN32_NATIVE))
            case 1: # look in this pathname for a file
              ThePathname(pathname)->pathname_name = # insert name (/=NIL)
                ThePathname(STACK_(3+4+1))->pathname_name;
              ThePathname(pathname)->pathname_type = # insert type
                ThePathname(STACK_(3+4+1))->pathname_type;
              pushSTACK(pathname);
             #ifdef PATHNAME_RISCOS
              if (name_and_type && nullp(ThePathname(pathname)->pathname_type)) {
                # Move the last subdir into the type slot of the pathname.
                # subdirs := (butlast subdirs) = (nreverse (cdr (reverse subdirs)))
                var object subdirs = reverse(ThePathname(pathname)->pathname_directory);
                pathname = STACK_0;
                ThePathname(pathname)->pathname_type = Car(subdirs);
                ThePathname(pathname)->pathname_directory = nreverse(Cdr(subdirs));
              }
              assure_dir_exists_(true,false,type_is_wild); # resolve links, search file
              if (file_exists(_EMA_) && !S_ISDIR(filestatus->st_mode)) # if file exists and is no directory
             #else
              assure_dir_exists(true,false); # resolve links, search file
              if (file_exists(_EMA_)) # if file exists
             #endif
                {
                  # extend result-list:
                  if (dsp->full_p) /* :FULL wanted? */
                    with_stat_info(); # yes -> extend STACK_0
                  # and push STACK_0 in front of result-list:
                  var object new_cons = allocate_cons();
                  Car(new_cons) = STACK_0;
                  Cdr(new_cons) = STACK_(4+4+2);
                  STACK_(4+4+2) = new_cons;
                }
              skipSTACK(2);
              goto next_pathname;
           #endif
           #ifndef MSDOS
            case -1: # search for a subdirectory in this pathname
              {
                var object namestring = assure_dir_exists(true,false); # resolve links, directory-namestring
                pushSTACK(namestring); # directory-namestring

                {
                  var object subdir = Car(STACK_(1+4+1+1)); # (car subdir-list)
                 #if defined(PATHNAME_AMIGAOS) || defined(PATHNAME_RISCOS)
                  if (eq(subdir,S(Kparent))) { # for parent-directory
                   #ifdef PATHNAME_AMIGAOS
                    pushSTACK(O(slash_string)); # additional "/" at the end
                   #endif
                   #ifdef PATHNAME_RISCOS
                    pushSTACK(O(parent_string)); # additional "^" at the end
                   #endif
                  } else
                 #endif
                    SUBDIR_PUSHSTACK(subdir);
                }
               #if defined(WIN32_NATIVE)
                pushSTACK(O(backslash_string));
                namestring = string_concat(3); /* concatenate */
               #else
                namestring = string_concat(2);
               #endif
                # get information:
                directory_search_1subdir(Car(STACK_(1+4+1)),namestring);
              }
              skipSTACK(1);
              goto next_pathname;
           #endif
          }
        }
        # in order to finish the task, all entries in this directory
        # have to be scanned:
        {
          var object dir_namestring = assure_dir_exists(true,false); # resolve links, form directory-name
          pushSTACK(dir_namestring); # save
        }
        # stack layout: ..., pathname, dir_namestring.
       #if defined(UNIX) || defined(WIN32_NATIVE)
        if (dsp->circle_p) { /* query :CIRCLE flag */
          # search pathname in the hash-table:
          var object hashcode = directory_search_hashcode();
          if (eq(hashcode,nullobj)) {
            # entry does not exist, however (this can happen to us
            # only for symbolic links)
            # -> will be skipped
            skipSTACK(2); goto next_pathname;
          }
          # and locate in the hash-table and store:
          if (!nullp(shifthash(STACK_(2+2),hashcode,T))) {
            # was already inside -> will be skipped
            skipSTACK(2); goto next_pathname;
          }
        }
       #endif
        if (next_task==0) {
          # push pathname STACK_1 in front of result-list:
          var object new_cons = allocate_cons();
          Car(new_cons) = STACK_1;
          Cdr(new_cons) = STACK_(4+4+2);
          STACK_(4+4+2) = new_cons;
        }
        directory_search_scandir(recursively,next_task,dsp);
        skipSTACK(2); # forget pathname and dir_namestring
      next_pathname: ;
      }
      # stack layout: ..., new-pathname-list, ht, pathname-list-rest, pathnames-to-insert.
      # Before advancing with pathname-list-rest :
      # pathname-list-rest := (nreconc pathnames-to-insert pathname-list-rest):
      var object pathnames_to_insert = popSTACK();
      STACK_0 = nreconc(pathnames_to_insert,STACK_0);
    }
    skipSTACK(2); # forget empty pathname-list-rest and hash-table
    { # reverse new-pathname-list, replaces the emptied pathname-list:
      var object new_pathname_list = popSTACK();
      STACK_0 = nreverse(new_pathname_list); # new pathname-list
    }
    # we are finished with this subdir-stage.
    if (matomp(STACK_1))
      break; # (atom subdir-list) -> finished.
    recursively = false; # the next (preliminarily) non-recursive
  passed_subdir: ;
  }
  # stack layout: result-list, pathname, name&type, subdir-list, pathname-list.
  # subdir-list became =NIL , also pathname-list = NIL (because at the last
  # loop iteration next_task is always =0,1,2, so nothing
  # was pushed on new-pathname-list).
  skipSTACK(4);
  return popSTACK(); # result-list as result
}
#endif # PATHNAME_NOEXT

/* (DIRECTORY [pathname [:circle] [:full] [:if-does-not-exist]]),
   CLTL p. 427 */
LISPFUN(directory,seclass_read,0,1,norest,key,3,
        ( kw(if_does_not_exist),kw(circle),kw(full) ))
{ /* stack layout: pathname, if-does-not-exist, circle, full. */
  var dir_search_param_t dsp;
  if (!boundp(STACK_2) || eq(STACK_2,S(Kdiscard)))
    /* :IF-DOES-NOT-EXIST defaults to :DISCARD */
    dsp.if_none = DIR_IF_NONE_DISCARD;
  else if (eq(STACK_2,S(Kerror)))
    dsp.if_none = DIR_IF_NONE_ERROR;
  else if (eq(STACK_2,S(Kkeep)))
    dsp.if_none = DIR_IF_NONE_KEEP;
  else if (eq(STACK_2,S(Kignore)))
    dsp.if_none = DIR_IF_NONE_IGNORE;
  else {
    pushSTACK(STACK_2); /* TYPE-ERROR slot DATUM */
    pushSTACK(O(type_directory_not_exist)); /* TYPE-ERROR slot EXPECTED-TYPE */
    pushSTACK(STACK_(2+2)); /* :IF-DOES-NOT-EXIST argument */
    pushSTACK(S(Kif_does_not_exist)); pushSTACK(S(directory));
    fehler(type_error,GETTEXT("~: illegal ~ argument ~"));
  }
  dsp.circle_p = !missingp(STACK_1); /* :CIRCLE argument defaults to NIL */
  dsp.full_p = !missingp(STACK_0); /* :FULL argument defaults to NIL */
  skipSTACK(3);
  /* check pathname-argument: */
  var object pathname = STACK_0;
  if (!boundp(pathname)) {
   #if defined(PATHNAME_NOEXT) || defined(PATHNAME_RISCOS)
    pathname = O(wild_string); # Default is "*"
   #endif
  }
  pathname = coerce_pathname(pathname); # turn into a pathname
  # let's go:
 #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  if (eq(ThePathname(pathname)->pathname_device,S(Kwild))) { # Device = :WILD ?
    # scan all devices
    STACK_0 = pathname;
    pushSTACK(NIL); # pathname-list := NIL
    { /* stack layout: pathname, pathname-list. */
      var char drive;
      for (drive='A'; drive<='Z'; drive++) # traverse all drives
        if (good_drive(drive)) {
          var object newpathname = copy_pathname(STACK_1);
          ThePathname(newpathname)->pathname_device =
            /* take over the device = one-element drive string */
            n_char_to_string(&drive,1,O(pathname_encoding));
          # search within a drive:
          var object newpathnames = directory_search(newpathname,&dsp);
          # and attach pathname-list in front of STACK_0:
          STACK_0 = nreconc(newpathnames,STACK_0);
        }
    }
    VALUES1(nreverse(STACK_0)); /* reverse pathname-list again */
    skipSTACK(2);
  } else
    # only one device to scan
 #endif
  {
    VALUES1(directory_search(pathname,&dsp)); /* form matching pathnames */
    skipSTACK(1);
  }
}

# UP: make sure that the supposed directory namestring ends with a slash
# returns a new string with a slash appended or the same stirng
# can trigger GC
local object ensure_last_slash (object dir_string) {
  ASSERT(stringp(dir_string));
  var uintL len, offset;
  var object str = unpack_string_ro(dir_string,&len,&offset);
  var chart ch = schar(str,len+offset-1);
  if (!pslashp(ch) && !lslashp(ch)) {
    var char sl = (looks_logical_p(dir_string) ? ';' : slash);
    with_sstring_0(str,O(pathname_encoding),asciz, {
      dir_string = asciz_add_char(asciz,len,sl,O(pathname_encoding));
    });
  }
  return dir_string;
}

# (CD [pathname]) sets the current drive and the current directory.
LISPFUN(cd,seclass_default,0,1,norest,nokey,0,NIL) {
  var object pathname = popSTACK();
  if (!boundp(pathname)) { pathname = O(empty_string); } /* "" */
  else if (stringp(pathname)) # make sure it ends with a slash
    pathname = ensure_last_slash(pathname);
  pathname = coerce_pathname(pathname); # turn into a pathname
  # copy and set name and type to NIL:
  pathname = copy_pathname(pathname);
  ThePathname(pathname)->pathname_name = NIL;
  ThePathname(pathname)->pathname_type = NIL;
  true_namestring(pathname,false,false); # the directory must exist
 #if HAS_HOST # necessary at least for PATHNAME_WIN32
  if (!nullp(ThePathname(STACK_0)->pathname_host)) {
    pushSTACK(STACK_0); # value for slot PATHNAME of FILE-ERROR
    pushSTACK(STACK_(0+1));
    pushSTACK(TheSubr(subr_self)->name);
    fehler(file_error,
           GETTEXT("~: cannot change default directory on remote host: ~"));
  }
 #endif
  change_default(); # set default drive and default directory
  VALUES1(popSTACK()); /* new pathname as the value */
}
#undef lslashp
#undef pslashp

# UP: checks a pathname, if both name and type are =NIL ,
# and if the directory "almost" exists.
# shorter_directory(pathname,resolve_links)
# > pathname : Pathname-Argument
# > resolve_links : flag, if links have to be resolved (usually yes)
# < -(STACK) : absolute pathname
#if defined(MSDOS) || defined(WIN32_NATIVE)
# < result: Directory-Namestring (for the OS, without '\' at the end, Normal-Simple-String)
#endif
#if defined(UNIX) || defined(AMIGAOS)
# < result: Directory-Namestring (for the OS, without '/' at the end, Normal-Simple-String)
#endif
#if defined(RISCOS)
# < result: Directory-Namestring (for the OS, without '.' at the end, Normal-Simple-String)
#endif
# decrements STACK by 1.
# can trigger GC
local object shorter_directory (object pathname, bool resolve_links) {
  pathname = coerce_pathname(pathname); # turn argument into a pathname
  check_no_wildcards(pathname); # with wildcards -> error
  pathname = use_default_dir(pathname); # insert default-directory
  check_notdir(pathname); # ensure that Name=NIL and Type=NIL
  pushSTACK(pathname); # save new pathname
  # shorten the directory:
  var object subdirs = ThePathname(pathname)->pathname_directory;
  if (nullp(Cdr(subdirs))) { # root-directory ?
  baddir:
    # STACK_0 = pathname, FILE-ERROR slot PATHNAME
    pushSTACK(STACK_0);
    fehler(file_error,GETTEXT("root directory not allowed here: ~"));
  }
  subdirs = reverse(subdirs); # copy list and reverse
 #if defined(PATHNAME_AMIGAOS) || defined(PATHNAME_RISCOS)
  if (eq(Car(subdirs),S(Kparent))) # last subdir must be /= :PARENT
    goto baddir;
 #endif
  pushSTACK(subdirs); # save cons with last subdir as CAR
  subdirs = Cdr(subdirs); # all subdirs except for the last
  subdirs = nreverse(subdirs); # bring into right order again
  pathname = STACK_1;
  ThePathname(pathname)->pathname_directory = subdirs; # and store in the pathname
  # this directory must exist:
  pushSTACK(pathname);
  # stack layout: pathname, subdircons, pathname.
  var object dir_namestring =
    (resolve_links ? assure_dir_exists(false,false) : assume_dir_exists());
  # build subdir-string for the operating system:
  STACK_0 = dir_namestring; # directory-namestring so far as 1. String
  var uintC stringcount =  # the strings in the last subdir
    subdir_namestring_parts(STACK_1,false);
  # and no '\' at the end (for the OS)
  # and no '/' at the end (for the OS)
  var object dirstring = string_concat(1+stringcount); # concatenate
  skipSTACK(1);
  return dirstring;
}

# (MAKE-DIR pathname) makes a new subdirectory pathname.
LISPFUNN(make_dir,1) {
  var object pathstring = shorter_directory(STACK_0,true);
  with_sstring_0(pathstring,O(pathname_encoding),pathstring_asciz, {
    make_directory(pathstring_asciz);
  });
  skipSTACK(2);
  VALUES1(T);
}

# (DELETE-DIR pathname) removes the subdirectory pathname.
LISPFUNN(delete_dir,1) {
  var object pathstring = shorter_directory(STACK_0,true);
  with_sstring_0(pathstring,O(pathname_encoding),pathstring_asciz, {
    delete_directory(pathstring_asciz);
  });
  skipSTACK(2);
  VALUES1(T);
}

# (defun ensure-directories-exist (pathspec &key verbose)
#   (let* ((dir (pathname-directory pathspec))
#          (path (make-pathname :host (pathname-host pathspec)
#                               :device (pathname-device pathspec)
#                               :directory dir)))
#     (when (wild-pathname-p path)
#       (error (make-condition 'file-error :pathname pathspec)))
#     (if (directory path)
#       (values pathspec nil)
#       (progn
#         (loop
#           for i from 1 upto (length dir)
#           do (let ((newpath
#                      (make-pathname :host (pathname-host pathspec)
#                                     :device (pathname-device pathspec)
#                                     :directory (subseq dir 0 i))))
#                (unless (directory newpath)
#                  (let ((namestring (namestring newpath)))
#                    (when verbose
#                      (format *standard-output* "~&Creating directory: ~A~%"
#                              namestring))
#                    (ignore-errors (lisp:make-dir namestring))
#                    (unless (directory newpath)
#                      (error (make-condition 'file-error :pathname pathspec))
#              ) ) ) )
#         )
#         (values pathspec t)
# ) ) ) )
LISPFUN(ensure_directories_exist,seclass_default,1,0,norest,key,1,
        (kw(verbose))) {
  var object pathname = coerce_pathname(STACK_1); # turn argument into a pathname
  pathname = copy_pathname(pathname); # copy and discard name, type
  ThePathname(pathname)->pathname_name = NIL;
  ThePathname(pathname)->pathname_type = NIL;
  check_no_wildcards(pathname); # with wildcards -> error
  pathname = use_default_dir(pathname); # insert default-directory
  pushSTACK(pathname); # save new pathname
  # stack layout: pathspec, verbose, pathname.
  if (directory_exists(pathname)) {
    skipSTACK(2); value2 = NIL; # pathspec, NIL as values
  } else {
    var object subdirs = copy_list(ThePathname(STACK_0)->pathname_directory);
    pushSTACK(subdirs); pushSTACK(Cdr(subdirs));
    Cdr(subdirs) = NIL;
    ThePathname(STACK_2)->pathname_directory = subdirs;
    # stack layout: pathspec, verbose, pathname, (car (last subdirs)), remaining_subdirs.
    while (mconsp(STACK_0)) {
      subdirs = STACK_0;
      Cdr(STACK_1) = subdirs; STACK_1 = subdirs; STACK_0 = Cdr(subdirs); Cdr(subdirs) = NIL;
      if (!directory_exists(STACK_2)) {
        if (!missingp(STACK_3)) { /* Verbose? */
          funcall(L(fresh_line),0); # (FRESH-LINE [*standard-output*])
          pushSTACK(CLSTEXT("Creating directory: ")); funcall(L(write_string),1); # (WRITE-STRING "..." [*standard-output*])
          pushSTACK(STACK_2); funcall(L(princ),1); # (PRINC pathname [*standard-output*])
          funcall(L(terpri),0); # (TERPRI [*standard-output*])
        }
        # side remark: Do not need to resolve links here, because here we
        # proceed step by step starting at the root, anyway.
        var object pathstring = shorter_directory(STACK_2,false);
        with_sstring_0(pathstring,O(pathname_encoding),pathstring_asciz, {
          make_directory(pathstring_asciz);
        });
        skipSTACK(1);
      }
    }
    skipSTACK(4); value2 = T; # pathspec, T as values
  }
  value1 = popSTACK(); mv_count=2;
}

#ifdef UNIX
# Returns the struct passwd entry for the current user.
# The return value points to static data, or is NULL upon failure.
local struct passwd * unix_user_pwd (void) {
  var const char* username;
  var struct passwd * userpasswd = NULL;
  # The manpage for GETLOGIN(3V) recommends
  # first getpwnam(getlogin()), then getpwuid(getuid()).
  begin_system_call();
  # 1. attempt: getpwnam(getenv("USER"))
  username = getenv("USER");
  if (username != NULL) {
    errno = 0; userpasswd = getpwnam(username);
    if (userpasswd != NULL) goto ok;
    if (errno != 0) { OS_error(); }
  }
  # 2. attempt: getpwnam(getlogin())
  username = getlogin();
  if (username != NULL) {
    errno = 0; userpasswd = getpwnam(username);
    if (userpasswd != NULL) goto ok;
    if (errno != 0) { OS_error(); }
  }
  # 3. attempt: getpwuid(getuid())
  errno = 0; userpasswd = getpwuid(getuid());
  if (userpasswd != NULL) goto ok;
  if (errno != 0) { OS_error(); }
  # Everything fails, userpasswd == NULL.
 ok:
  end_system_call();
  return userpasswd;
}
#endif

# UP: Initializes the pathname-system.
# init_pathnames();
# can trigger GC
global void init_pathnames (void) {
 #if defined(PATHNAME_OS2) || defined(PATHNAME_WIN32)
  { # initialize default-drive:
    var char drive = default_drive();
    O(default_drive) = n_char_to_string(&drive,1,O(pathname_encoding));
  }
 #endif
  # initialize *DEFAULT-PATHNAME-DEFAULTS* :
  recalc_defaults_pathname();
 #ifdef USER_HOMEDIR
  #ifdef UNIX
  # we retrieve the home-directory and the usable shell from the
  # environment. It contains (almost) always at least the following variables:
  #   LOGNAME = Username at the first login ("true" identity of the user)
  #   USER    = current username
  #   HOME    = current home-directory, fetched from /etc/passwd
  #   SHELL   = current standard-shell, fetched from /etc/passwd
  #   PATH    = search path for program call
  #   TERM    = terminal emulation
  # we retrieve HOME (for "~" - translation) and SHELL (for EXECUTE).
  # For "~username" we must scan the /etc/passwd - file.
  { # search in the environment for variable HOME:
    begin_system_call();
    var const char* homedir = getenv("HOME");
    end_system_call();
    if (homedir != NULL) { # found?
      O(user_homedir) = asciz_dir_to_pathname(homedir,O(misc_encoding)); # yes -> enter
    } else { # no -> get home-directory from the passwort-file:
      var struct passwd * userpasswd = unix_user_pwd();
      if (userpasswd != NULL) { # no -> enter homedir as pathname
        O(user_homedir) = asciz_dir_to_pathname(userpasswd->pw_dir,O(misc_encoding));
      } else { # no -> take current directory:
        O(user_homedir) = default_directory();
      }
    }
  }
  #endif
  #ifdef WIN32
  # WinNT defines HOMEDRIVE and HOMEPATH. Win95 (which is actually not a
  # multiuser OS) lets the user set HOME himself.
  # In any case, we give preference to HOME, because the user can change
  # this.
  {
    var const char * home;
    begin_system_call();
    home = getenv("HOME");
    if (home != NULL) {
      end_system_call();
      O(user_homedir) = asciz_dir_to_pathname(home,O(misc_encoding));
    } else {
      var const char * homedrive = getenv("HOMEDRIVE");
      var const char * homepath = getenv("HOMEPATH");
      end_system_call();
      if (homedrive!=NULL && homepath!=NULL) {
        var char* homeall = (char*)alloca(asciz_length(homedrive)+asciz_length(homepath)+1);
        var char* ptr = homeall;
        while ((*ptr = *homedrive) != '\0') { homedrive++; ptr++; }
        while ((*ptr = *homepath) != '\0') { homepath++; ptr++; }
        *ptr = '\0';
        O(user_homedir) = asciz_dir_to_pathname(homeall,O(misc_encoding));
      } else {
        O(user_homedir) = use_default_dir(asciz_dir_to_pathname(".",Symbol_value(S(ascii))));
      }
    }
  }
  #endif
 #endif
 #ifdef HAVE_SHELL
  #ifdef UNIX
  # the command-shell O(command_shell) remains unchanged, otherwise
  # we get too many portability problems.
  { # search the environment for variable SHELL:
    begin_system_call();
    var const char* shell = getenv("SHELL");
    end_system_call();
    if (shell != NULL) { # found?
      O(user_shell) = asciz_to_string(shell,O(misc_encoding)); # yes -> enter
    }
    # else O(user_shell) remains on the default value "/bin/csh".
  }
  #endif
  #ifdef MSDOS
  { /* search the environment for variable COMSPEC: */
    begin_system_call();
    var const char* shell = getenv("COMSPEC");
    end_system_call();
    if (!(shell==NULL)) { # found?
      O(command_shell) = asciz_to_string(shell,O(misc_encoding)); # yes -> enter
    }
    # else O(command_shell) remains on the default value "\\COMMAND.COM".
  }
  #endif
  #ifdef WIN32_NATIVE
  { # search in the environment for variable COMSPEC:
    begin_system_call();
    var const char* shell = getenv("COMSPEC");
    if (!(shell==NULL)) {
      end_system_call();
      O(command_shell) = asciz_to_string(shell,O(misc_encoding)); # enter
    } else {
      var OSVERSIONINFO v;
      v.dwOSVersionInfoSize = sizeof(OSVERSIONINFO);
      if (!GetVersionEx(&v)) { OS_error(); }
      if (v.dwPlatformId == VER_PLATFORM_WIN32_NT) { # Windows NT
        shell = "cmd.exe";
      } else { # Windows 95 or else
        shell = "command.com";
      }
      end_system_call();
      O(command_shell) = ascii_to_string(shell); # enter
    }
  }
  #endif
 #endif
}

# (FILE-WRITE-DATE file), CLTL p. 424
LISPFUNNR(file_write_date,1) {
 #ifdef AMIGAOS
  var struct DateStamp file_datetime; # buffer for date/time of a file
 #endif
 #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
  var time_t file_datetime; # buffer for date/time of a file
 #endif
 #ifdef WIN32_NATIVE
  var WIN32_FIND_DATA filedata;
 #endif
  var object pathname = popSTACK(); # pathname-argument
  if (builtin_stream_p(pathname)) { # stream -> treat extra:
    # must be file-stream:
    pathname = as_file_stream(pathname);
    # streamtype file-stream
   #if !defined(AMIGAOS)
    if ((TheStream(pathname)->strmflags & strmflags_open_B)
        && (!nullp(TheStream(pathname)->strm_buffered_channel))) {
      # open file-stream
      # work with the handle directly:
     #if defined(UNIX) || defined(EMUNIX) || defined(RISCOS)
      var struct stat status;
      begin_system_call();
      if (!( fstat(TheHandle(TheStream(pathname)->strm_buffered_channel),&status) ==0)) {
        end_system_call(); OS_filestream_error(pathname);
      }
      end_system_call();
      file_datetime = status.st_mtime;
     #endif
     #ifdef WIN32_NATIVE
      var BY_HANDLE_FILE_INFORMATION fileinfo;
      var BOOL result;
      begin_system_call();
      result = GetFileInformationByHandle(TheHandle(TheStream(pathname)->strm_buffered_channel),&fileinfo);
      end_system_call();
      if (result) {
        filedata.ftCreationTime   = fileinfo.ftCreationTime;
        filedata.ftLastAccessTime = fileinfo.ftLastAccessTime;
        filedata.ftLastWriteTime  = fileinfo.ftLastWriteTime;
      } else { # If that failed, try the full pathname.
        test_file_stream_named(pathname);
        pathname = TheStream(pathname)->strm_file_truename;
        goto is_pathname;
      }
     #endif
    } else
   #endif
    { # closed file-stream -> use truename as pathname
      test_file_stream_named(pathname);
      pathname = TheStream(pathname)->strm_file_truename;
      goto is_pathname;
    }
  } else {
    pathname = coerce_pathname(pathname); # turn into a pathname
   is_pathname: { /* pathname is now really a pathname */
      var object namestring = true_namestring(pathname,true,false);
     #ifdef EMUNIX
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        var struct stat statbuf;
        begin_system_call();
        if (stat(namestring_asciz,&statbuf) < 0) {
          end_system_call(); OS_file_error(STACK_0);
        }
        end_system_call();
        if (!S_ISREG(statbuf.st_mode)) { fehler_file_not_exists(); } # file must exist
        file_datetime = statbuf.st_mtime;
      });
     #endif
     #ifdef AMIGAOS
      if (!file_exists(namestring)) { fehler_file_not_exists(); } # file must exist
      file_datetime = filestatus->fib_Date;
     #endif
     #if defined(UNIX) || defined(RISCOS)
      if (!file_exists(namestring)) { fehler_file_not_exists(); } # file must exist
      file_datetime = filestatus->st_mtime;
     #endif
     #ifdef WIN32_NATIVE
      # Only a directory search gives us the times.
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        var HANDLE search_handle;
        begin_system_call();
        search_handle = FindFirstFile(namestring_asciz,&filedata);
        if (search_handle==INVALID_HANDLE_VALUE) {
          if (WIN32_ERROR_NOT_FOUND) {
            end_system_call(); fehler_file_not_exists();
          }
          end_system_call(); OS_file_error(STACK_0);
        } else if (!FindClose(search_handle)) {
          end_system_call(); OS_file_error(STACK_0);
        }
        end_system_call();
      });
     #endif
      skipSTACK(1);
    }
  }
  # date/time no is in the buffer file_datetime.
  # convert into Universal-Time-Format:
 #if defined(UNIX) || defined(EMUNIX) || defined(AMIGAOS) || defined(RISCOS)
  VALUES1(convert_time_to_universal(&file_datetime));
 #endif
 #ifdef WIN32_NATIVE
  var FILETIME* pftimepoint = &filedata.ftLastWriteTime;
  if (pftimepoint->dwLowDateTime==0 && pftimepoint->dwHighDateTime==0)
    pftimepoint = &filedata.ftCreationTime;
  VALUES1(convert_time_to_universal(pftimepoint));
 #endif
}

# (FILE-AUTHOR file), CLTL p. 424
LISPFUNNR(file_author,1) {
  var object pathname = popSTACK(); # pathname-argument
  if (builtin_stream_p(pathname)) { # stream -> treat extra:
    # must be file-stream:
    pathname = as_file_stream(pathname);
    # streamtype file-stream
    if (TheStream(pathname)->strmflags & strmflags_open_B) {
      # open file-stream -> OK
    } else { # closed file-stream -> use truename as pathname
      test_file_stream_named(pathname);
      pathname = TheStream(pathname)->strm_file_truename;
      goto is_pathname;
    }
  } else {
    pathname = coerce_pathname(pathname); # turn into a pathname
   is_pathname: { # pathname is now really a pathname
      var object namestring = true_namestring(pathname,true,false);
    #ifdef MSDOS
     #if 1
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        # open file:
        begin_system_call();
        var sintW result = # try to open file
          open(namestring_asciz,O_RDONLY);
        if (result < 0) {
          end_system_call(); OS_file_error(STACK_0); # report error
        }
        # now result contains the handle of the opened files.
        if (CLOSE(result) < 0) { # close file instantly again
          end_system_call(); OS_file_error(STACK_0);
        }
        end_system_call();
      });
     #else
      with_sstring_0(namestring,O(pathname_encoding),namestring_asciz, {
        var struct stat statbuf;
        begin_system_call();
        if (stat(namestring_asciz,&statbuf) < 0) {
          end_system_call(); OS_file_error(STACK_0);
        }
        end_system_call();
        if (!S_ISREG(statbuf.st_mode)) { fehler_file_not_exists(); } # file must exist
      });
     #endif
    #endif
     #if defined(UNIX) || defined(AMIGAOS) || defined(RISCOS) || defined(WIN32_NATIVE)
      if (!file_exists(namestring)) { fehler_file_not_exists(); } # file must exist
     #endif
      skipSTACK(1);
    }
  }
  /* file exists -> NIL as value */
  VALUES1(NIL);
}

#if defined(UNIX) || defined(MSDOS) || defined(RISCOS)

# (EXECUTE file arg1 arg2 ...) calls a file with the given arguments.
LISPFUN(execute,seclass_default,1,0,rest,nokey,0,NIL) {
  var gcv_object_t* args_pointer = rest_args_pointer STACKop 1;
  {
    var gcv_object_t* argptr = args_pointer; # Pointer to the arguments
    { # check file:
      var gcv_object_t* file_ = &NEXT(argptr);
      var object namestring = true_namestring(coerce_pathname(*file_),
                                              true,false);
      # check, if the file exists:
      if (!file_exists(namestring)) { fehler_file_not_exists(); }
      *file_ = string_to_asciz(namestring,O(pathname_encoding)); # save
      skipSTACK(1);
    }
    { # check the other arguments:
      var uintC count;
      dotimesC(count,argcount, {
        var gcv_object_t* arg_ = &NEXT(argptr);
        pushSTACK(*arg_); funcall(L(string),1); # convert next argument into a string
        *arg_ = string_to_asciz(value1,O(misc_encoding)); # and convert ASCIZ-string
      });
    }
  }
 #ifdef EMUNIX
  # (On OS/2 system() seems to be safer than spawnv(). Why?)
  # concatenate all arguments (now ASCIZ-strings) , with spaces in between:
  {
    var uintL argvdata_length = 0;
    {
      var gcv_object_t* argptr = args_pointer;
      var uintC count;
      dotimespC(count,argcount+1, {
        var object arg = NEXT(argptr); # next argument, ASCIZ-string
        argvdata_length += Sbvector_length(arg);
      });
    }
    var DYNAMIC_ARRAY(argvdata,char,argvdata_length);
    {
      var gcv_object_t* argptr = args_pointer;
      var char* argvdataptr = &argvdata[0];
      var uintC count;
      dotimespC(count,argcount+1, {
        var object arg = NEXT(argptr); # next argument, ASCIZ-string
        var char* ptr = TheAsciz(arg);
        var uintL len = Sbvector_length(arg);
        dotimesL(len,len-1, { *argvdataptr++ = *ptr++; } ); # and copy
        *argvdataptr++ = ' ';
      });
      argvdataptr[-1] = '\0';
    }
    # call program:
    begin_system_call();
    var int ergebnis = system(&argvdata[0]);
    end_system_call();
    # finished.
    set_args_end_pointer(args_pointer); # clean up STACK
    # utilize return value: =0 (OK) -> T, >0 (nicht OK) -> NIL :
    VALUES_IF(ergebnis==0);
    FREE_DYNAMIC_ARRAY(argvdata);
  }
 #endif
 #if defined(UNIX) || defined(RISCOS)
  { # build up argv-Array in stack and copy strings in the stack:
    var uintL argvdata_length = 0;
    {
      var gcv_object_t* argptr = args_pointer;
      var uintC count;
      dotimespC(count,argcount+1, {
        var object arg = NEXT(argptr); # next argument, ASCIZ-string
        argvdata_length += Sbvector_length(arg);
      });
    }
    var DYNAMIC_ARRAY(argv,char*,1+(uintL)argcount+1);
    var DYNAMIC_ARRAY(argvdata,char,argvdata_length);
    {
      var gcv_object_t* argptr = args_pointer;
      var char** argvptr = &argv[0];
      var char* argvdataptr = &argvdata[0];
      var uintC count;
      dotimespC(count,argcount+1, {
        var object arg = NEXT(argptr); # next argument, ASCIZ-string
        var char* ptr = TheAsciz(arg);
        var uintL len = Sbvector_length(arg);
        *argvptr++ = argvdataptr; # fill into argv
        dotimespL(len,len, { *argvdataptr++ = *ptr++; } ); # and copy
      });
      *argvptr = NULL; # and conclude with nullpointer
    }
    { # start a new process:
      var int child;
      begin_system_call();
      begin_want_sigcld();
      if ((child = vfork()) ==0) {
        # this program part is executed by the child-process:
        execv(argv[0],argv); # call program
        _exit(-1); # if this fails, end the child-process
      }
      # this program part is executed by the caller:
      if (child==-1) {
        # something. failed, either on vfork or on execv.
        # in both cases errno was set.
        end_want_sigcld(); OS_error();
      }
      # wait, until the child-process is finished:
      var int status = wait2(child);
      # cf. WAIT(2V) and #include <sys/wait.h> :
      #   WIFSTOPPED(status)  ==  ((status & 0xFF) == 0177)
      #   WEXITSTATUS(status)  == ((status & 0xFF00) >> 8)
      end_want_sigcld();
      end_system_call();
      # finished.
      set_args_end_pointer(args_pointer); # clean up STACK
      VALUES1(((status & 0xFF) == 0000) /* process ended normally (without signal, without core-dump) ? */
             ? fixnum((status & 0xFF00) >> 8) /* yes -> exit-status as value: */
             : NIL); /* no -> NIL as value */
    }
    FREE_DYNAMIC_ARRAY(argvdata);
    FREE_DYNAMIC_ARRAY(argv);
  }
 #endif
}

#endif

#ifdef AMIGAOS

# (EXECUTE command-string) sends a string to the operating system.
# in this case this is synonymous with (SHELL command-string).
LISPFUN(execute,seclass_default,1,0,norest,nokey,0,NIL) {
  C_shell(); # call SHELL, same stack layout
}

#endif

/* duplicate the handle (maybe into new_handle)
 must be surrounded with begin_system_call()/end_system_call() */
global Handle handle_dup (Handle old_handle, Handle new_handle) {
 #if defined(UNIX)
  new_handle = (new_handle == (Handle)-1 ? dup(old_handle)
                : dup2(old_handle,new_handle));
 #elif defined(WIN32_NATIVE)
  if (!DuplicateHandle(GetCurrentProcess(),old_handle,
                       GetCurrentProcess(),&new_handle,
                       0, true, DUPLICATE_SAME_ACCESS))
    OS_error();
 #else
  NOTREACHED;
 #endif
  if (new_handle == (Handle)-1)
    OS_error();
  return new_handle;
}

#ifdef HAVE_SHELL

# (SHELL) calls a shell.
# (SHELL command) calls a shell and lets it execute a command.

#if defined(AMIGAOS)
#include <dos/dostags.h>         # for SystemTags()

LISPFUN(shell,seclass_default,0,1,norest,nokey,0,NIL) {
  var object command = popSTACK();
  # As I/O is on the terminal and we obviously keep a handle on it,
  # we will also get ^C^D^E^F signals from it during command execution.
  # We choose to restore the initial signal state to avoid a double
  # interruption, even though that implies that signals sent to us
  # explicitly (Break command) in this time will be ignored.
  if (missingp(command)) {
    # call command interpreter:
    run_time_stop();
    begin_system_call();
    var BOOL ergebnis = false;
   #if 0 # ok, it is not that simple
    ergebnis = Execute("",stdin_handle,stdout_handle);
   #else
    var Handle terminal = Open("*",MODE_READWRITE);
    if (!(terminal==Handle_NULL)) {
      var ULONG signals = SetSignal(0L,0L);
      ergebnis = Execute("",terminal,Handle_NULL);
      # Restore state of break signals
      SetSignal(signals,(SIGBREAKF_CTRL_C|SIGBREAKF_CTRL_D|
                         SIGBREAKF_CTRL_E|SIGBREAKF_CTRL_F));
      Write(terminal,NLstring,1);
      Close(terminal);
    }
   #endif
    end_system_call();
    run_time_restart();
    # utilize return value: executed -> T, not found -> NIL :
    VALUES_IF(ergebnis);
  } else {
    # execute single command:
    command = check_string(command);
    with_string_0(command,O(misc_encoding),command_asciz, {
      # execute command:
      run_time_stop();
      begin_system_call();
      var ULONG signals = SetSignal(0L,0L);
      # Using SystemTags() instead of Execute() sends console signals to
      # the command and it gives us the command's exit code.
      var LONG ergebnis =
        SystemTags(command_asciz,
                   SYS_Input, stdin_handle,
                   # Work around bug in Emacs-18 subshell where Input() and Output()
                   # are forbiddenly the same by having Input() cloned.
                   SYS_Output, (stdin_handle == stdout_handle) ? Handle_NULL : stdout_handle,
                   SYS_UserShell, 1L,
                   TAG_DONE);
      # Restore state of break signals
      SetSignal(signals,(SIGBREAKF_CTRL_C|SIGBREAKF_CTRL_D|
                         SIGBREAKF_CTRL_E|SIGBREAKF_CTRL_F));
      end_system_call();
      run_time_restart();
      # utilize return value
      VALUES1(L_to_I(ergebnis));
    });
  }
}

#elif defined(WIN32_NATIVE)

# (SYSTEM::SHELL-NAME) returns the name of the command shell.
LISPFUNN(shell_name,0) {
  VALUES1(O(command_shell));
}

LISPFUN(shell,seclass_default,0,1,norest,nokey,0,NIL) {
  var object command = popSTACK();
  if (missingp(command))
    command = O(command_shell);
  command = check_string(command);
  var HANDLE prochandle;
  with_string_0(command,O(misc_encoding),command_asciz, {
    # Start new process.
    var HANDLE stdinput;
    var HANDLE stdoutput;
    var HANDLE stderror;
    var PROCESS_INFORMATION pinfo;
    begin_system_call();
    stdinput = GetStdHandle(STD_INPUT_HANDLE);
    if (stdinput == INVALID_HANDLE_VALUE) { OS_error(); }
    stdoutput = GetStdHandle(STD_OUTPUT_HANDLE);
    if (stdoutput == INVALID_HANDLE_VALUE) { OS_error(); }
    stderror = GetStdHandle(STD_ERROR_HANDLE);
    if (stderror == INVALID_HANDLE_VALUE) { OS_error(); }
    if (!MyCreateProcess(command_asciz,stdinput,stdoutput,stderror,&pinfo))
      { OS_error(); }
    if (pinfo.hThread && !CloseHandle(pinfo.hThread)) { OS_error(); }
    prochandle = pinfo.hProcess;
  });
  # Wait until it terminates, get its exit status code.
  var DWORD exitcode;
  switch (WaitForSingleObject(prochandle,INFINITE)) {
    case WAIT_FAILED:
      OS_error();
    case WAIT_OBJECT_0:
      break;
    default: NOTREACHED;
  }
  if (!GetExitCodeProcess(prochandle,&exitcode)) { OS_error(); }
  if (!CloseHandle(prochandle)) { OS_error(); }
  end_system_call();
  # utilize return value: =0 (OK) -> T, >0 (not OK) -> NIL :
  VALUES_IF(exitcode == 0);
}

#else # UNIX || MSDOS || ...

LISPFUN(shell,seclass_default,0,1,norest,nokey,0,NIL) {
  var object command = popSTACK();
  if (missingp(command)) {
    # execute (EXECUTE shell) :
   #ifdef UNIX
    pushSTACK(O(user_shell)); # Shell-Name
   #else # MSDOS
    pushSTACK(O(command_shell)); # Shell-Name
   #endif
    funcall(L(execute),1);
  } else {
   #if defined(MSDOS) || defined(RISCOS)
    # the command has to be passed already split into single parts at
    # the white spaces to the DOS command-interpreter. The function
    # system() does this job for us, fortunately.
    command = check_string(command);
    with_string_0(command,O(misc_encoding),command_asciz, {
      begin_system_call();
      # call program:
      var int ergebnis = system(command_asciz);
      end_system_call();
      # utilize return value: =0 (OK) -> T, >0 (not OK) -> NIL :
      VALUES_IF(ergebnis == 0);
    });
   #else
    # call (EXECUTE shell "-c" command):
    pushSTACK(O(command_shell)); # shell name
    pushSTACK(O(command_shell_option)); # shell option "-c"
    #ifdef EMUNIX
    # On DOS 2.x, 3.x the options-character can be a different one!
    if ((_osmode == DOS_MODE) && (_osmajor < 4)) {
      var uintB swchar = _swchar();
      if (swchar) # pss. replace "/C" with something else
        sstring_store(STACK_0,0,ascii(swchar)); # (destructive)
    }
    #endif
    pushSTACK(command);
    funcall(L(execute),3);
   #endif
  }
}

#endif

#endif

/* stringlist_to_asciizlist (stringlist, encoding)
 convert a stringlist to list of asciz strings
 and places it on the stack.
 returns total length of all asciiz strings including zeros
   and listlength (if the pointer is not NULL)
 adds one element to STACK
 can trigger GC */
#if !defined(UNICODE)
#define stringlist_to_asciizlist(s,e,l) stringlist_to_asciizlist_(s,l)
local int stringlist_to_asciizlist_ (object stringlist,uintL *listlength)
#else
local int stringlist_to_asciizlist (object stringlist,
                                    gcv_object_t *encoding_,
                                    uintL *listlength)
#endif
{
  var int length = 0;
  var int listlen = 0;
  pushSTACK(NIL)/*result head*/; pushSTACK(NIL)/*result tail*/;
  pushSTACK(stringlist);
  while (consp(STACK_0/*stringlist tail*/)) {
    var object tmp = allocate_cons();
    if (nullp(STACK_2/*result*/)) STACK_1 = STACK_2 = tmp;
    else { Cdr(STACK_1/*result tail*/) = tmp; STACK_1 = tmp; }
    tmp = check_string(Car(STACK_0));
    tmp = string_to_asciz(tmp,*encoding_);
    length += Sbvector_length(tmp) + 1;
    Car(STACK_1) = tmp;
    STACK_0 = Cdr(STACK_0);
    listlen++;
  }
  if (listlength) *listlength = listlen;
  skipSTACK(2); /* drop stringlist and result tail */
  return length;
}

#ifdef WIN32_NATIVE

/* (LAUNCH executable [:arguments] [:wait] [:input] [:output] [:error] [:priority])
 Launches a program.
 :arguments : a list of strings
 :wait - nullp/not nullp - whether to wait for process to finish (default T)
 :input, :output, :error - i/o/e streams for process. basically file-streams
   or terminal-streams. see stream_lend_handle() in stream.d for full list
   of supported streams
 :priority : on windows : HIGH/LOW/NORMAL on UNIX : fixnum - see nice(2)
 returns: if wait exit code, child PID otherwise */
LISPFUN(launch,seclass_default,1,0,norest,key,6,
        (kw(arguments),kw(wait),kw(input),kw(output),kw(error),kw(priority))) {
  STACK_6 = check_string(STACK_6); /* command_arg */
  if (!boundp(STACK_5)) STACK_5 = NIL; /* arguments_arg */
  else STACK_5 = check_list(STACK_5);
  var bool wait_p = !nullp(STACK_4); /* default: do wait! */
  var int handletype; # TODO: check it
  var DWORD pry = NORMAL_PRIORITY_CLASS;
  if (boundp(STACK_0)) {        /* priority_arg */
    var object priority_arg = STACK_0;
   restart_priority:
    if (eq(priority_arg,S(Khigh))) pry = HIGH_PRIORITY_CLASS;
    else if (eq(priority_arg,S(Klow))) pry = IDLE_PRIORITY_CLASS;
    else if (!eq(priority_arg,S(Knormal))) {
      pushSTACK(NIL);              /* no PLACE */
      pushSTACK(priority_arg);     /* TYPE-ERROR slot DATUM */
      pushSTACK(O(type_priority)); /* TYPE-ERROR slot EXPECTED-TYPE */
      pushSTACK(priority_arg);
      pushSTACK(S(Kpriority));
      pushSTACK(TheSubr(subr_self)->name);
      check_value(type_error,GETTEXT("~: illegal ~ argument ~"));
      priority_arg = value1;
      goto restart_priority;
    }
  }
  var Handle hinput = /* STACK_3 == input_stream_arg */
    handle_dup1((boundp(STACK_3) && !eq(STACK_3,S(Kterminal)))
                ? stream_lend_handle(STACK_3,true,&handletype)
                : stdin_handle);
  var Handle houtput = /* STACK_2 == output_stream_arg */
    handle_dup1((boundp(STACK_2) && !eq(STACK_2,S(Kterminal)))
                ? stream_lend_handle(STACK_2,false,&handletype)
                : stdout_handle);
  var Handle herror = /* STACK_1 == error_stream_arg */
    handle_dup1((boundp(STACK_1) && !eq(STACK_1,S(Kterminal)))
                ? stream_lend_handle(STACK_1,false,&handletype)
                : stderr_handle);
  var HANDLE prochandle;
  var object cmdlist_cons = allocate_cons();
  Car(cmdlist_cons) = STACK_6; /* command_arg */
  Cdr(cmdlist_cons) = STACK_5; /* arguments_arg */
  pushSTACK(cmdlist_cons);
  var int command_len =
    stringlist_to_asciizlist(STACK_0,&O(misc_encoding),NULL);
  /* STACK: cmdlist, ascizcmdlist */
  var DYNAMIC_ARRAY(command_data,char,command_len*2);
  /* command_len is multiplied by 2 for quoting sake */
  var int command_pos = 0;
  while (!nullp(STACK_0)) {
    if (command_pos > 0) command_data[command_pos++] = ' ';
    command_pos += shell_quote(command_data+command_pos,
                               TheAsciz(Car(STACK_0)));
    ASSERT(command_pos < command_len*2);
    STACK_0 = Cdr(STACK_0);
  }
  skipSTACK(2);
  /* STACK: -- */

  /* Start new process. */
  var PROCESS_INFORMATION pinfo;
  var STARTUPINFO sinfo;
  sinfo.cb = sizeof(STARTUPINFO);
  sinfo.lpReserved = NULL;
  sinfo.lpDesktop = NULL;
  sinfo.lpTitle = NULL;
  sinfo.cbReserved2 = 0;
  sinfo.lpReserved2 = NULL;
  sinfo.dwFlags = STARTF_USESTDHANDLES;
  sinfo.hStdInput = hinput;
  sinfo.hStdOutput = houtput;
  sinfo.hStdError = herror;
  begin_system_call();
  if (!CreateProcess(NULL, command_data, NULL, NULL, true, pry,
                     NULL, NULL, &sinfo, &pinfo))
    { end_system_call(); OS_error(); }
  if (pinfo.hThread /* zero for 16 bit programs in NT */
       && !CloseHandle(pinfo.hThread))
    { end_system_call(); OS_error(); }
  prochandle = pinfo.hProcess;
  FREE_DYNAMIC_ARRAY(command_data);
  var DWORD exitcode = 0;
  if (wait_p) {
    /* Wait until it terminates, get its exit status code. */
    switch (WaitForSingleObject(prochandle,INFINITE)) {
      case WAIT_FAILED:
        end_system_call(); OS_error();
      case WAIT_OBJECT_0:
        break;
      default: NOTREACHED;
    }
    if (!GetExitCodeProcess(prochandle,&exitcode))
      { end_system_call(); OS_error(); }
  }

  /* we can safely close handle of a running process - no problem */
  if (!CloseHandle(prochandle)) { end_system_call(); OS_error(); }

  /* so with our copy of the child's handles */
  if (hinput!=stdin_handle && !CloseHandle(hinput))
    { end_system_call(); OS_error(); }
  if (houtput!=stdout_handle && !CloseHandle(houtput))
    { end_system_call(); OS_error(); }
  if (houtput!=stderr_handle && !CloseHandle(herror))
    { end_system_call(); OS_error(); }

  end_system_call();
  if (wait_p) VALUES1(fixnum(exitcode));
  else VALUES1(sfixnum(prochandle));
  skipSTACK(7);
}

/* (SHELL-EXECUTE verb filename parameters defaultdir)
   ShellExecute wrapper
   See ShellExecute description at
   http://msdn.microsoft.com/library/default.asp?url=/library/en-us/shellcc/
     platform/Shell/reference/functions/shellexecute.asp
   verb: usually nil (for default),
         "edit", "explore", "open", "print", "properties"
   filename: filename or url to open
   parameters: list of arguments
   defaultdir: default directory for application (can be nil)
   returns: nil, but can signal an OS error*/
LISPFUN(shell_execute,seclass_default,0,4,norest,nokey,0,NIL) {
  var object verb_arg = STACK_3;
  var object filename_arg = check_string(STACK_2);
  var object parameters_arg = STACK_1;
  var object defaultdir_arg = STACK_0;
  var int verb_len = 0;
  if (nullp(verb_arg)) pushSTACK(S(nil));
  else {
    pushSTACK(string_to_asciz(check_string(verb_arg),O(misc_encoding)));
    verb_len = Sbvector_length(STACK_0);
  }
  var int filename_len = 0;
  pushSTACK(string_to_asciz(check_string(filename_arg),
      O(misc_encoding)));
  filename_len = Sbvector_length(STACK_0);
  var int parameters_len =
    stringlist_to_asciizlist(parameters_arg,&O(misc_encoding),NULL);
  /* list of asciiz strings is in the STACK */
  var DYNAMIC_ARRAY(parameters,char,parameters_len*2);
  var int parameter_pos = 0;
  while (!nullp(STACK_0)) {
    if (parameter_pos > 0) parameters[parameter_pos++] = ' ';
    parameter_pos +=
      shell_quote(parameters+parameter_pos,TheAsciz(Car(STACK_0)));
    ASSERT(parameter_pos < parameters_len*2);
    STACK_0 = Cdr(STACK_0);
  }
  skipSTACK(1);
  var int defaultdir_len = 0;
  if (nullp(defaultdir_arg)) pushSTACK(S(nil));
  else {
    pushSTACK(string_to_asciz(check_string(defaultdir_arg),
                              O(misc_encoding)));
    defaultdir_len = Sbvector_length(STACK_0);
  }
  /* STACK: verb/nil, filename, defaultdir/nil */
  var DYNAMIC_ARRAY(verb,char,1+verb_len);
  var DYNAMIC_ARRAY(filename,char,1+filename_len);
  var DYNAMIC_ARRAY(defaultdir,char,1+defaultdir_len);
  var char *sp, *dp;
  if (!nullp(STACK_2))
    for (sp=TheAsciz(STACK_2),dp=verb;(*dp = *sp);sp++,dp++);
  for (sp=TheAsciz(STACK_1),dp=filename;(*dp = *sp);sp++,dp++);
  if (!nullp(STACK_0))
    for (sp=TheAsciz(STACK_0),dp=defaultdir;(*dp = *sp);sp++,dp++);
  begin_system_call();
  var DWORD result = (DWORD) ShellExecute(NULL,
                                          nullp(STACK_2)?NULL:verb,
                                          filename,
                                          parameters_len?parameters:NULL,
                                          nullp(STACK_0)?NULL:defaultdir,
                                          SW_SHOWNORMAL);
  end_system_call();
  if (result <= 32) OS_error();
  FREE_DYNAMIC_ARRAY(defaultdir);
  FREE_DYNAMIC_ARRAY(filename);
  FREE_DYNAMIC_ARRAY(verb);
  FREE_DYNAMIC_ARRAY(parameters);
  skipSTACK(3+4);
  VALUES1(S(nil));
}

#endif

#if defined(UNIX) || defined(RISCOS)

LISPFUN(launch,seclass_default,1,0,norest,key,6,
        (kw(arguments),kw(wait),kw(input),kw(output),kw(error),kw(priority))) {
  STACK_6 = check_string(STACK_6); /* command_arg */
  var long priority = (integerp(STACK_0) ? I_to_L(STACK_0)
                       : (fehler_posfixnum(STACK_0), 0));
  var bool wait_p = !nullp(STACK_4); /* default: do wait! */
  var int handletype;
  var Handle hinput = /* STACK_3 == input_stream_arg */
    handle_dup1((boundp(STACK_3) && !eq(STACK_3,S(Kterminal)))
                ? stream_lend_handle(STACK_3,true,&handletype)
                : stdin_handle);
  var Handle houtput = /* STACK_2 == output_stream_arg */
    handle_dup1((boundp(STACK_2) && !eq(STACK_2,S(Kterminal)))
                ? stream_lend_handle(STACK_2,false,&handletype)
                : stdout_handle);
  var Handle herror = /* STACK_1 == error_stream_arg */
    handle_dup1((boundp(STACK_1) && !eq(STACK_1,S(Kterminal)))
                ? stream_lend_handle(STACK_1,false,&handletype)
                : stderr_handle);
  var int exit_code = 0;
  pushSTACK(allocate_cons());
  Car(STACK_0) = string_to_asciz(STACK_(6+1)/*command_arg*/,
                                 O(pathname_encoding));
  var uintL command_arg_len = Sbvector_length(Car(STACK_0));
  var uintL argbuf_len = 0, arglist_count = 0;
  { /* argument list */
    var object arg_arg = STACK_(5+1);
    if (boundp(arg_arg))
      arg_arg = check_list(STACK_(5+1));
    if (!nullp(arg_arg))
      argbuf_len = command_arg_len + 1 +
        stringlist_to_asciizlist(arg_arg,&O(misc_encoding),&arglist_count);
  }
  /* STACK: (list asciiz-command), asciiz-arg-list */
  Cdr(STACK_1) = STACK_0;
  skipSTACK(1);
  /* STACK: (cons asciiz-command asciiz-arg-list) */
  var DYNAMIC_ARRAY(argv,char*,1+(uintL)arglist_count+1);
  var DYNAMIC_ARRAY(argvdata,char,argbuf_len);
  var object curcons = STACK_0;
  var char** argvptr = &argv[0];
  var char* argvdataptr = &argvdata[0];
  while (consp(curcons)) {
    var uintL len = Sbvector_length(Car(curcons));
    var char* ptr = TheAsciz(Car(curcons));
    *argvptr++ = argvdataptr; /* fill into argv */
    dotimespL(len,len, { *argvdataptr++ = *ptr++; } ); /* and copy */
    curcons = Cdr(curcons);
  };
  *argvptr = NULL; /* and conclude with null */
  skipSTACK(1);
  /* STACK: -- */
  begin_system_call();
  begin_want_sigcld();
  var int child = vfork();
  if (child == 0) {/* What ?! I am the clone ?! */
   #define CHILD_DUP(from,to)                                           \
    if (handle_dup(from,to) == (Handle)-1) {                            \
        fprintf(stderr,"clisp/child: cannot duplicate %d to %d: %s\n",  \
                from,to,strerror(errno));                               \
        _exit(-1);                                                      \
      }                                                                 \
      if (from>2) close(from)
    CHILD_DUP(hinput,0);
    CHILD_DUP(houtput,1);
    CHILD_DUP(herror,2);
   #undef CHILD_DUP
   #ifdef HAVE_NICE
    errno = 0; nice(priority);
    if (errno) {
      fprintf(stderr,"clisp/child: cannot set priority to %d: %s\n",
              priority,strerror(errno));
      _exit(-1);
    }
   #endif
    execvp(*argv,argv);
    fprintf(stderr,"clisp/child: execvp failed: %s\n",strerror(errno));
    _exit(-1);
  } else if (child < 0) {
    /* TODO: FIXME: no easy way to be aware of dup2 or exec failures */
    end_want_sigcld();
    end_system_call();
    OS_error();
  }
  if (wait_p) {
    var int status = wait2(child);
    exit_code = WEXITSTATUS(status);
  }
  end_want_sigcld();
  end_system_call();
  FREE_DYNAMIC_ARRAY(argv);
  FREE_DYNAMIC_ARRAY(argvdata);
  if (wait_p) VALUES1(sfixnum(exit_code));
  else VALUES1(sfixnum(child));
  skipSTACK(7);
}

#endif

# (SAVEMEM pathname) stores the memory image at pathname.
LISPFUNN(savemem,1) {
  # execute (OPEN pathname :direction :output) :
  # pathname as 1. argument
  pushSTACK(S(Kdirection)); # :DIRECTION as 2. Argument
  pushSTACK(S(Koutput)); # :OUTPUT as 3. Argument
 #ifdef UNIX
  # On Unix with mmap() existing .mem-Files may not be simply
  # overwritten, because running Lisp-processes would crash due to this.
  # So therefore :if-exists :rename-and-delete.
  #if defined(UNIX_LINUX) && defined(SINGLEMAP_MEMORY)
  # Under Linux 1.3.20, when the mem file to be saved is on an NFS volume
  # and has the same filename as the mem file we started with, the GC
  # done by savemem (once the new mem file has been created and still has
  # size 0) will crash. Looks like a bug in the Linux NFS client, which
  # causes random pages to be mapped in instead of pages from the renamed
  # old mem file. Workaround: Do a full GC, forcing all the old mem file's
  # contents into memory immediately.
  gar_col();
  #endif
  pushSTACK(S(Kif_exists)); # :IF-EXISTS as 4. Argument
  pushSTACK(S(Krename_and_delete)); # :RENAME-AND-DELETE as 5. Argument
  funcall(L(open),5);
 #else
  #ifdef SELFMADE_MMAP
  # With selfmade_mmap the existing .mem-file has to be completely loaded
  # into memory first. Other running Lisp-processes will crash, however.
  gar_col();
  #endif
  funcall(L(open),3);
 #endif
  # write memory image into the file:
  # (the stream has to be closed by function savemem(),
  # also in case of an error.)
  savemem(value1);
  VALUES1(T);
}

#ifdef DYNAMIC_MODULES

# (SYSTEM::DYNLOAD-MODULES pathname stringlist)
# loads a shared library, containing a number of modules.
LISPFUNN(dynload_modules,2) {
  # convert pathname into string:
  pushSTACK(STACK_1); pushSTACK(T); funcall(L(namestring),2); # (NAMESTRING pathname T)
  STACK_1 = value1;
  # check strings and store in the stack:
  var uintL stringcount = llength(STACK_0);
  var gcv_object_t* arg_ = &STACK_0;
  {
    var uintL count;
    dotimesL(count,stringcount, {
      Car(*arg_) = check_string(Car(*arg_));
      pushSTACK(string_to_asciz(Car(*arg_),Symbol_value(S(ascii))));
      *arg_ = Cdr(*arg_);
    });
    endp(*arg_); # test for true list
  }
  {
    var const char * libpath = TheAsciz(string_to_asciz(*(arg_ STACKop 1),O(pathname_encoding)));
    var DYNAMIC_ARRAY(modnames,const char *,stringcount);
    if (stringcount > 0) {
      var uintL count;
      var gcv_object_t* ptr1 = STACK STACKop stringcount;
      var const char * * ptr2 = modnames;
      dotimespL(count,stringcount, { *ptr2++ = TheAsciz(NEXT(ptr1)); });
    }
    dynload_modules(libpath,stringcount,modnames);
    FREE_DYNAMIC_ARRAY(modnames);
  }
  skipSTACK(stringcount+1);
  VALUES1(popSTACK()); # Library-Name as value
}

#endif

# =============================================================================

#ifdef HAVE_DISASSEMBLER

# Finding the full path of the executable.
# Bruno Haible 20.12.1994

# This assumes that the executable is not removed or renamed while running.

# file name of the executable
local char* executable_name = NULL;
#ifdef UNIX_CYGWIN32
/* note that up and including win2000, detaching from a process kills it
 <http://article.gmane.org/gmane.os.cygwin/32245>
 <http://article.gmane.org/gmane.os.cygwin/32246>
 <http://article.gmane.org/gmane.os.cygwin/32250> */
#define default_executable_name  "lisp.exe"
#else
#define default_executable_name  "lisp.run"
#endif

# file descriptor of the executable
# (Only used to verify that we find the correct executable.)
local int executable_fd = -1;

# maybe_executable(pathname)
# checks whether a given pathname may belong to the executable.
local bool maybe_executable (const char * filename) {
  var struct stat statexe;
  var struct stat statfile;
  if (access(filename,R_OK|X_OK) < 0)
    return false;
  if (executable_fd < 0)
    return true;
  # If we already have an executable_fd, check that filename points to
  # the same inode.
  if (fstat(executable_fd,&statexe) < 0)
    return true;
  if (stat(filename,&statfile) < 0)
    return false;
  if (statfile.st_dev
      && statfile.st_dev == statexe.st_dev
      && statfile.st_ino == statexe.st_ino)
    return true;
  return false;
}

# find_executable(program_name)
# is to be called immediately after the program starts,
# with program_name = argv[0],
# before any chdir() operation and before any setenv("PATH",...).
# It determines the full program path and opens a file descriptor to
# the executable, for later use.
# Return value is 0 if successful, -1 and errno set if not.
global int find_executable (const char * program_name) {
  # Do not need to execute this more than once.
  if (executable_name != NULL) return 0;
 #if defined(WIN32_NATIVE)
  { /* try WIN32 API - this is not used because HAVE_DISASSEMBLER is UNIX-only,
       but this is an illustration that win32 API can be sometimes useful */
    LPTSTR cmdl = GetCommandLine();
    /* cmdl is now the full command line and the first word is the
       full correct executable path, quoted with "" if it contains spaces */
    if (cmdl[0] == '"') {
      int pos_end = strchr(cmdl+1,'"') - cmdl - 1;
      strncpy(executable_name,cmdl+1,pos_end);
      executable_name[pos_end] = 0;
    } else {
      int pos_end = strchr(cmdl,' ') - cmdl;
      strncpy(executable_name,cmdl,pos_end);
      executable_name[pos_end] = 0;
    }
    return 0;
  }
 #endif
 #ifdef UNIX_LINUX
  # The executable is accessible as /proc/<pid>/exe. We try this first
  # because it is safer: no race condition w.r.t. the file system. It may
  # fail, however, if the user has not compiled /proc support into his
  # kernel.
  {
    var char buf[6+10+5];
    var int fd;
    sprintf(buf,"/proc/%d/exe",getpid());
    fd = OPEN(buf,O_RDONLY,my_open_mask);
    if (fd >= 0)
      executable_fd = fd;
  }
 #endif
  # Now we guess the executable's full path. We assume the executable
  # has been called via execlp() or execvp() with properly set up argv[0].
  # The login(1) convention to add a '-' prefix to argv[0] is not supported.
  var bool has_slash = false;
  {
    var const char * p;
    for (p = program_name; *p; p++)
      if (*p == '/') {
        has_slash = true; break;
      }
  }
  if (!has_slash) {
    # exec searches paths without slashes in the directory list given
    # by $PATH.
    var const char * path = getenv("PATH");
    if (!(path==NULL)) {
      var const char * p;
      var const char * p_next;
      for (p = path; *p; p = p_next) {
        var const char * q;
        var uintL p_len;
        for (q = p; *q; q++) { if (*q == ':') break; }
        p_len = q-p; p_next = (*q=='\0' ? q : q+1);
        # We have a path item at p, of length p_len.
        # Now concatenate the path item and program_name.
        var char * concat_name = (char*) malloc(p_len + strlen(program_name) + 2);
        if (concat_name == NULL) { errno = ENOMEM; goto notfound; }
        if (p_len == 0) {
          # empty PATH element designates the current directory
          strcpy(concat_name,program_name);
        } else {
          memcpy(concat_name, p, p_len);
          concat_name[p_len] = '/';
          strcpy(concat_name+p_len+1, program_name);
        }
        if (maybe_executable(concat_name)) {
          # Assume we have found the executable
          program_name = concat_name; goto resolve;
        }
        free(concat_name);
      }
    }
    # Not found in the PATH, assume the current directory.
  }
  # exec treats paths containing slashes as relative to the current directory.
  if (maybe_executable(program_name)) {
  resolve:
    # resolve program_name:
    executable_name = (char*) malloc(MAXPATHLEN);
    if (executable_name == NULL) { errno = ENOMEM; goto notfound; }
    if (realpath(program_name,executable_name) == NULL) {
      free(executable_name); goto notfound;
    }
    return 0;
  }
  errno = ENOENT;
 notfound:
  executable_name = default_executable_name; return -1;
}

# (SYS::PROGRAM-NAME) returns the executable's name.
LISPFUNN(program_name,0) {
  VALUES1(asciz_to_string(executable_name,O(pathname_encoding)));
}

#endif

# (SYS::LIB-DIRECTORY) returns CLISP's private library directory
# (called $(lisplibdir) in the Makefile).
LISPFUNN(lib_directory,0) {
  if (!nullp(O(lib_dir))) {
    VALUES1(O(lib_dir));
  } else {
    pushSTACK(TheSubr(subr_self)->name);
    fehler(error,GETTEXT("~: library directory is not known, use a command line option to specify it"));
  }
}

# (SYS::SET-LIB-DIRECTORY path) sets the CLISP's private library directory
LISPFUNN(set_lib_directory,1) {
  var object path = popSTACK();
  if (stringp(path)) path = ensure_last_slash(path);
  VALUES1(O(lib_dir) = coerce_xpathname(path));
}

# =============================================================================

#ifdef EMUNIX

# Bypass an annoying ENAMETOOLONG Error when using long
# filenames on FAT-Drives on OS/2:

#undef chdir
#undef access
#undef stat
#undef unlink
#undef rename
#undef __findfirst
#undef mkdir
#undef open
#undef creat
#undef spawnv

# path2 := shortened copy of path1
local void shorten_path (const char* path1, char* path2) {
  var const uintB* p1 = path1;
  var uintB* p2 = path2;
  var uintB c;
  var uintC wordlength = 0; # former length in name or type
  var uintC maxwordlength = 8; # = 8 in name, = 3 in type
  loop {
    c = *p1++;
    if (c=='\0') {
      *p2++ = c; break;
    }
    if ((c=='\\') || (c=='/') || (c==':')) {
      *p2++ = c; wordlength = 0; maxwordlength = 8;
    } else if (c=='.') {
      *p2++ = c; wordlength = 0; maxwordlength = 3;
    } else {
      if (++wordlength <= maxwordlength)
        *p2++ = c;
    }
  }
}

global int my_chdir (const char* path) {
  var int erg = chdir(path);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = chdir(shorter_path);
  }
  return erg;
}

global int my_access (const char* path, int amode) {
  var int erg = access(path,amode);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = access(shorter_path,amode);
  }
  return erg;
}

global int my_stat (const char* path, struct stat* buf) {
  var int erg = stat(path,buf);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = stat(shorter_path,buf);
  }
  return erg;
}

global int my_unlink (const char* path) {
  var int erg = unlink(path);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = unlink(shorter_path);
  }
  return erg;
}

global int my_rename (const char* oldpath, const char* newpath) {
  var int erg = rename(oldpath,newpath);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_oldpath = alloca(asciz_length(oldpath)+1);
    shorten_path(oldpath,shorter_oldpath);
    erg = rename(shorter_oldpath,newpath);
    if ((erg<0) && (errno==ENAMETOOLONG)) {
      var char* shorter_newpath = alloca(asciz_length(newpath)+1);
      shorten_path(newpath,shorter_newpath);
      erg = rename(shorter_oldpath,shorter_newpath);
    }
  }
  return erg;
}

global int my___findfirst (const char* path, int attrib, struct ffblk* ffblk) {
  var int erg = __findfirst(path,attrib,ffblk);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = __findfirst(shorter_path,attrib,ffblk);
  }
  return erg;
}

global int my_mkdir (const char* path, long attrib) {
  var int erg = mkdir(path,attrib);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = mkdir(shorter_path,attrib);
  }
  return erg;
}

global int my_open (const char* path, int flags) {
  var int erg = open(path,flags);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = open(shorter_path,flags);
  }
  return erg;
}

#define creat(path,mode)  open(path,O_RDWR|O_TRUNC|O_CREAT,mode)
global int my_creat (const char* path, int pmode) {
  var int erg = creat(path,pmode);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = creat(shorter_path,pmode);
  }
  return erg;
}

global int my_spawnv (int pmode, CONST char* path, const char* const * argv) {
  var int erg = spawnv(pmode,path,argv);
  if ((erg<0) && (errno==ENAMETOOLONG)) {
    var char* shorter_path = alloca(asciz_length(path)+1);
    shorten_path(path,shorter_path);
    erg = spawnv(pmode,shorter_path,argv);
  }
  return erg;
}

#endif

# ============================================================================

#ifdef DEBUG_TRANSLATE_PATHNAME
#undef DEBUG_TRANSLATE_PATHNAME
#undef DOUT
#endif
