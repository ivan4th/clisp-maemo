/* orafns.c

   "C" functions for simplified interface to Oracle OCI client
   library.

   Copyright (C) 2002 Alma Mater Software, Inc.
   Author: "John Kelley Hinsdale" <hin@alma.com>

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License version 2 as
   published by the Free Software Foundation; see file GNU-GPL.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software Foundation,
   Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.

   $Id$

*/

/* Oracle OCI library */
#include <oci.h>

/* Unix calls (e.g., sprintf) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Our exported functions and types */
#include "oiface.h"

/* Constants */

/* Default no. of bytes for row prefetch */
#define DEFAULT_PREFETCH_BYTES  65536
/* Size of per-connection error buffer */
#define ERRBUF_BYTES            100000

/* Local routines, w/ wrappers passed to external interface */
static struct db_conn * connect(char *, char *, char *, char *, int, int);
static int              disconnect(struct db_conn *);
static int              exec_sql(struct db_conn *, char *, struct sqlparam **, int);
static int              fetch_row(struct db_conn *);
static int              ncol(struct db_conn *);
static int              eof(struct db_conn *);
static int              success(struct db_conn *);
static struct sqlcol ** column_info(struct db_conn *);
static struct sqlval ** row_values(struct db_conn *);
static int              rows_affected(struct db_conn *);
static int              commit(struct db_conn *);
static int              rollback(struct db_conn *);
static int              set_auto_commit(struct db_conn *, int);

/* Purely local routines */
static void      append_oci_error(char *, OCIError *);
static int       init_session(struct db_conn *, char *, char *, char *, char*, int);
static int       get_cols(struct db_conn *);
static int       get_param_attr(CONST dvoid *, int, struct db_conn *, dvoid *, ub4 *, char *, ub4);
static char *    decode_data_type(int);
static int       fetch_data_len(int, int);
static void      free_columns(struct db_conn *);
static void      free_column(struct column *);
static void      free_if_non_null(void *);
static void      reset_db_conn(struct db_conn *);
static int       check_active_statement(struct db_conn *, char *);
static int       check_active_select(struct db_conn *, char *);
static int       empty(char *);
static char *    valid_string(char *);

/* Static indicator variables for input data */
static sb4      null_indicator = -1;
static sb4      non_null_indicator = 0;

/* ------------------------------------------------------------------------------------------------------------- */

/* Main driver */
#if 0
int main(int argc, char **argv) {

  struct db_conn *  db = 0;

  int           success = 0;
  char *        sql     = 0;
  
  int               nrow            = 0;
  int               n               = 0;
  ub4               ncol            = 0;
  struct column *   col             = 0;

  int               is_command      = 0;

  /* Check usage */
  if ( argc != 7 ) {
    printf("Usage: %s <user> <schema> <pass> <sid> <cmdflag> <sql>\n", argv[0]);
    exit(1);
  }

  /* Connect to server */
  db = connect(argv[1], argv[2], argv[3], argv[4],
                      -1,   /* Prefetch bytes */
                      1);   /* Auto-commit? */
  if ( ! db ) {
    /* Should never really get this */
    printf("Error initting connection\n");
    return 0;
  }
  else if ( ! db->success ) {
    printf("%s", db->errmsg);
    return 0;
  }

  /* Execute SQL query or command */
  is_command = atoi(argv[5]);
  success = exec_sql(db, argv[6], is_command);
  if ( ! success ) {
    printf("Error: %s\n", db->errmsg);
    return 0;
  }

  /* Fetch data rows - data will show up in the "column" structs above */
  while ( 1 ) {

    int eof = 0;
    
    success = fetch_row(db);
    if ( ! success ) {
      strcat(db->errmsg, "A row-fetch error occured.\n");
      return 0;
    }
    else if ( success == 2 ) /* EOF */
      break;

    /* Successful fetch.  Extract column data */
    printf("-------  ROW ----------\n");
    nrow++;
  
    if ( nrow % 5000 == 0 )
      printf("Fetched %d rows ...\n", nrow);

    for ( n=0; n < db->ncol; n++ ) {
    
      col = &db->columns[n];
      
      printf("%-30s %4d %4d ", col->name, col->indicator, strlen(col->data));
      
      /* First check if null */
      if ( col->indicator == -1 ) {
        printf("<NULL>\n");
        continue;
      }
      /* Should never really get the other two cases (-2 = really huge, or positive truncation) */
      else if ( col->indicator != 0 ) {
        sprintf(db->errmsg, "Got unexpected indicator value %d in column '%s'\n", col->indicator, col->name);
        return 0;
      }
    
      /* Should have the result as a null-terminated string */
      printf("'%s'\n", (char *) col->data);
    }
  }

  printf("Fetched %d rows\n", nrow);

  /* Success */ 
  return 0;
}
#endif

/* ------------------------------------------------------------------------------------------------------------- */

/* Init a new connection, given user, schema, password and SID */

static struct db_conn * connect(char * user, char * schema, char * password, char * sid, int prefetch_bytes, int auto_commit)
{
  sb4       status  = OCI_SUCCESS;

  /* Set up the Oracle environment */
  struct db_conn * db = (struct db_conn *) malloc(sizeof (struct db_conn));
  if ( ! db )
    return 0;

  /* Init everything to sane values */
  reset_db_conn(db);

  /* First alloc the error message */
  db->errmsg = (char *) malloc(ERRBUF_BYTES);
  if ( ! db->errmsg )
    return 0;

  /* Connect to database */
  db->success = init_session(db, user, schema, password, sid, 0);
  if ( ! db->success )
    return db;

  /* Copy buffer size and auto-commit */
  db->prefetch_bytes = prefetch_bytes;
  db->auto_commit = auto_commit;

  /* Success */
  db->success = 1;
  return db;
};

/* ------------------------------------------------------------------------------------------------------------- */

  
/* Fetch a row of data.  Data will be placed in the structures pointed
   to by columns[] array.  Return 0 for failure, 1 for fetch, 2 for EOF
   Once EOF is returned, it is an error to fetch again.
*/
static int fetch_row(struct db_conn * db)
{

  int               null            = 0,    /* Flag: null column(s) exist in fetched row */
                    truncated       = 0;    /* Flag: truncated column(s) exist in fetched row */

  struct column *   col             = 0;
  int               n               = 0;
  sb4               fetch_status    = OCI_SUCCESS;
  
  /* Clear out results */
  *db->errmsg = '\0';
  db->success = 0;
  
  /* Make sure we have a connection, and active SELECT */
  if ( ! check_active_select(db, "fetch result row") )
    return db->success = 0;

  /* Reset fetch info for all columns (Oracle does not do it for us) */
  for ( n=0; n < db->ncol; n++ ) {
    col = &db->columns[n];
    *((char *) col->data) = '\0';
    col->indicator = 0;
    col->nfetched = 0;
  }
  
  /* Init row data if not already.  The presence of a non-NULL
     db->currow indicates the first fetch has been called.  Some
     functions are not valid until that time. */
  if ( ! db->currow ) {
    db->currow = (struct sqlval **) malloc((db->ncol + 1) * sizeof(struct sqlval *));
    for ( n=0; n < db->ncol; n++ ) {
      struct sqlval * r = (struct sqlval *) malloc(sizeof(struct sqlval));

      r->data     = db->columns[n].data;
      r->is_null      = 0;
      db->currow[n] = r;
    }
    /* Terminate pointer array */
    db->currow[n] = 0;
  }

  /* Make sure not already at EOF */
  if ( db->eof ) {
    sprintf(db->errmsg,"Fetch: already at EOF\n");
    return db->success = 0;
  }

  /* Get one row at a time */
  fetch_status = OCIStmtFetch(db->stmt, db->err, 1, OCI_FETCH_NEXT, OCI_DEFAULT);
  
  if ( fetch_status == OCI_NO_DATA ) {
    /* EOF */
    db->eof = 1;
    return db->success = 2;
  }
  
  if ( fetch_status != OCI_SUCCESS && fetch_status != OCI_SUCCESS_WITH_INFO ) {
    /* Error fetching */
    sprintf(db->errmsg, "Fetch error %d:\n", fetch_status);
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }
  
  /* If have success "with info" could mean null value, truncated
     data, or EOF.  Error codes are 01405 (null), 01406 (truncated
     data) and 01403 (EOF).  For null and truncated data, have to
     look at each column's "indicator variable" for what
     happened. */
  
  if ( fetch_status == OCI_SUCCESS_WITH_INFO ) {
    char * dummy = 0;
    sb4 errcode = 0;
    sb4 err_status = OCIErrorGet(db->err, 1, dummy, &errcode, 0, 0, OCI_HTYPE_ERROR);
    if ( err_status != OCI_SUCCESS ) {
      sprintf(db->errmsg, "Error getting error status checking for EOF\n");
      return db->success = 0;
    }
    
    /* Check for EOF */
    if ( errcode == 1403 ) {
      db->eof = 1;
      return db->success = 2; /* EOF */
    }
    /* Null value(s) */
    else if ( errcode == 1405 )
      null = 1;
    /* Truncated value(s) */
    else if ( errcode == 1406 )
      truncated = 1;
    /* Null OR truncated */
    else if ( errcode == 24345 ) {
      truncated = 1;
      null = 1;
    }
    else {
      sprintf(db->errmsg, "Unknown Oracle warning %d\n", errcode);
      append_oci_error(db->errmsg, db->err);
      return db->success = 0;
    }
  }
  
  /* Copy is-null indicator status to external structures.  */
  for ( n=0; n < db->ncol; n++ ) {
    struct sqlval * r = db->currow[n];
    col = &db->columns[n];
    if ( col->indicator == 0 )
      r->is_null = 0;
    else if ( col->indicator == -1 )
      r->is_null = 1;
    else {
      sprintf(db->errmsg, "Bad indicator value %d for column %d\n", col->indicator, n);
      append_oci_error(db->errmsg, db->err);
    }
  }
  
  /* Maintain row count */
  db->rows_affected++;

  /* Success */
  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Get column info for a SELECT query just executed by stmt handle.
   Get column type info and number of columns.   */

static int get_cols(struct db_conn * db)
{
  sb4               attr_status         = OCI_SUCCESS;
  sb4               param_status        = OCI_SUCCESS;
  OCIParam *        param               = 0;
  ub4               param_count         = 0;
  ub4               ncol                = 0;
  struct column *   col                 = 0;
  text *            colnamep            = 0;
  ub4               colname_len         = 0;
  char              colname[10000];
  int               fetch_buflen        = 0;
  int               success             = 0;
  sb4               define_status       = OCI_SUCCESS;

  /* Clear out previous results */
  free_columns(db);
  db->ncol = 0;
  *db->errmsg = '\0';

  /* Get the number of columns in the output.  We also will calculate
     this as we retreive parameter info below, but having its value
     now is useful for allocating buffers. */
  attr_status = OCIAttrGet((dvoid *) db->stmt, OCI_HTYPE_STMT, &param_count, 0, OCI_ATTR_PARAM_COUNT, db->err);
  if ( attr_status != OCI_SUCCESS ) {
    /* Error getting param info */
    sprintf(db->errmsg, "Error getting param count:\n");
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  /* Allocate buffers for column info */
  db->ncol = param_count;
  db->columns = (struct column *) malloc(db->ncol * sizeof(struct column));
  
  /* Successfully parsed: now get the names, types and lengths of the result columns */
  ncol = 0;

  do {

    ncol++;
    param_status = OCIParamGet(db->stmt, OCI_HTYPE_STMT, db->err, (dvoid **) &param, ncol);

    /* See if done -- the Oracle docs say that OCIParamGet() will
       return OCI_NO_DATA (== 100) when at the end of the parameters.
       However by observation, it seems to really return status of
       OCI_ERROR, with an error context of "ORA-24334: no descriptor
       for this position".  So we have to check the error code in the
       error handle rather than the return status of OCIParamGet().
       What a pain in the ass.  */

    /* This is what should normally happend according to Oracle docs */
    if ( param_status == OCI_NO_DATA )
      break;
    else if ( param_status != OCI_SUCCESS ) {

      /* Error getting param info -- might not be an error if the
         error code is 24334 ("no descriptor for this position").
         Check if that is the case and break normally. */

      char * dummy = 0;
      sb4 errcode = 0;
      sb4 err_status = OCIErrorGet(db->err, 1, dummy, &errcode, 0, 0, OCI_HTYPE_ERROR);
      if ( err_status != OCI_SUCCESS ) {
        sprintf(db->errmsg, "Error getting error status checking OCI_NO_DATA on col %d\n", ncol);
        return db->success = 0;
      }
      else if ( errcode == 24334 ) {
        /* OK, really a "no more data" situation */
        break;
      }
      else {
        /* A real error */
        sprintf(db->errmsg, "Error getting param col %d:\n", ncol);
        append_oci_error(db->errmsg, db->err);
        return db->success = 0;
      }
    }
      
    /* Set up for a new column */

    /* Make sure we are not overflowing our buffer (i.e., that Oracle
     is giving us more columns than it said before it has) */
    if ( ncol > param_count ) {
      sprintf(db->errmsg, "Error: more than expected count of %d columns returned", param_count);
      return db->success = 0;
    }
    
    col = &db->columns[ncol-1];

    /* Get param attributes */
    success = 1;
    success = success && get_param_attr(param, ncol, db, &colnamep,       &colname_len, "name",      OCI_ATTR_NAME);
    success = success && get_param_attr(param, ncol, db, &col->dtype,     0,            "data type", OCI_ATTR_DATA_TYPE);
    success = success && get_param_attr(param, ncol, db, &col->dsize,     0,            "size",      OCI_ATTR_DATA_SIZE);
    success = success && get_param_attr(param, ncol, db, &col->precision, 0,            "precision", OCI_ATTR_PRECISION);
    success = success && get_param_attr(param, ncol, db, &col->scale,     0,            "scale",     OCI_ATTR_SCALE);
    success = success && get_param_attr(param, ncol, db, &col->null_ok,   0,            "is-null",   OCI_ATTR_IS_NULL);
    if ( ! success )
      return db->success = 0;

    /* Copy column name to our buffer */
    memcpy(colname, colnamep, colname_len);
    colname[colname_len] = '\0';
    col->name = (char *) strdup(colname);

    /*
      printf("Col %2d: type is %-10s name = %-20s size = %4d precision = %2d scale = %2d null-ok=%d\n",
             ncol, decode_data_type(col->dtype), col->name, col->dsize, col->precision, col->scale, col->null_ok);
    */

    /* Set up a define variable for this col to get its fetched value.
       Note that we ask Oracle to convert everything to
       null-terminated string, SQLT_STR. */
    fetch_buflen = fetch_data_len(col->dtype, col->dsize);
    col->data = malloc(fetch_buflen);
    *((char *) col->data) = '\0';
    col->indicator = 0;
    col->nfetched = 0;
    col->rcode = 0;
    define_status = OCIDefineByPos(db->stmt, &col->def, db->err, ncol, col->data, fetch_buflen, SQLT_STR,
                                   &col->indicator, &col->nfetched, &col->rcode, OCI_DEFAULT);
    if ( define_status != OCI_SUCCESS ) {
      sprintf(db->errmsg, "Error setting up define for column '%s':\n", col->name);
      append_oci_error(db->errmsg, db->err);
      return db->success = 0;
    }
  }
  while ( param_status == OCI_SUCCESS );

  /* Make sure the no. of params we extracted is the same as what Oracle thinks it has */
  if ( ncol - 1 != param_count ) {
    sprintf(db->errmsg, "Column count mismatch - we have %d and Oracle had %d\n", ncol - 1, param_count);
    return db->success = 0;
  }
  
  /* Copy column info to structures suitable for returning to external
     interface.  Allocate ncol+1 struct pointers, and terminate w/ a
     zero pointer. */
  db->sqlcols = (struct sqlcol **) malloc((db->ncol + 1) * sizeof(struct sqlcol *));
  for ( ncol=0; ncol < db->ncol; ncol++ ) {
    struct sqlcol * e = (struct sqlcol *) malloc(sizeof(struct sqlcol));
    struct column * c = &db->columns[ncol];

    e->name         = c->name;
    e->type         = decode_data_type(c->dtype);
    e->size         = c->dsize;
    e->scale        = c->scale;
    e->precision    = c->precision;
    e->null_ok      = c->null_ok;

    db->sqlcols[ncol] = e;
  }
  /* Terminate pointer array */
  db->sqlcols[ncol] = 0;
            
  /* Success */
  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Commit the current transaction */

static int commit(struct db_conn * db)
{
  sword status  = OCI_SUCCESS;

  *db->errmsg = '\0';
  db->success = 0;
 
  status = OCITransCommit(db->svc, db->err, OCI_DEFAULT);
  if ( status != OCI_SUCCESS ) {
    sprintf(db->errmsg, "Error commiting transaction:\n");
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Rollback (abort) the current transaction */

static int rollback(struct db_conn * db)
{
  sword status  = OCI_SUCCESS;

  *db->errmsg = '\0';
  db->success = 0;
  
  /* Make sure we are not in "auto-commit" mode */
  if ( db->auto_commit ) {
    sprintf(db->errmsg, "Rollback called while autocommit turned on.");
    return db->success = 0;
  }

  status = OCITransRollback(db->svc, db->err, OCI_DEFAULT);
  if ( status != OCI_SUCCESS ) {
    sprintf(db->errmsg, "Error rolling back transaction:\n");
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Prepare and execute a SQL command.  Return a new statment handle,
   which MUST be eventually OCIHandleFree()'s by the caller.
*/
static int exec_sql(struct db_conn * db, char * sql, struct sqlparam ** params, int is_command)
{
  sword                 status  = 0;
  ub4                   iters   = 0;
  int                   nparam  = 0;
  struct sqlparam **    params_save = params;
  
  /* Clear out results */
  *db->errmsg = '\0';
  db->success = 0;

  /* Reset EOF indicator  and row count */
  db->eof = 0;
  db->rows_affected = 0;
  
  /* Make sure we are connected */
  if ( ! db->svc ) {
    sprintf(db->errmsg, "Attempt to run SQL statement when not connected");
    return db->success = 0;
  }

  /* For SELECT's do zero iters (just parse), for destructive commands, do one */
  iters = is_command ? 1 : 0;

  /* Parse the SQL query or command */
  if ( empty(sql) ) {
    sprintf(db->errmsg, "Null SQL query or command given");
    return db->success = 0;
  }

  /* Save the SQL away for later reporting */
  if ( db->sql )
    free(db->sql);
  db->sql = (char *) strdup(sql);
  db->is_command = is_command;
  
  /* Get a new statement handle - ISSUE: will Oracle roll back an
     active transaction currently in progress with the old handle?  It
     probably should.  */
  if ( db->stmt ) {
	/* Note - freeing the statement handle recursively frees its
	   children "define" handles, and since we may have kept around
	   copies of those handles, we need to clear out our copies
	   first. */
	free_columns(db);
    OCIHandleFree(db->stmt, OCI_HTYPE_STMT);
    db->stmt = 0;
  }
  if ( OCI_SUCCESS !=  OCIHandleAlloc(db->env, (dvoid **) &db->stmt, OCI_HTYPE_STMT, 0, 0) ) {
    sprintf(db->errmsg, "Error allocating statement handle\n");
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  /* "Prepare" the statement - this rarely returns an error */
  status = OCIStmtPrepare(db->stmt, db->err, sql, strlen(sql), OCI_V8_SYNTAX, OCI_DEFAULT);
  if ( status != OCI_SUCCESS ) {
    sprintf(db->errmsg, "Error parsing SQL text:\n%s\n", sql);
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  /* Bind the input parameters - need to do this after the "prepare"
     so Oracle knows what vars there are */
  while ( params && *params ) {

    OCIBind *           dummy   = 0;
    dvoid *             indp    = 0;
    struct sqlparam *   p       = (struct sqlparam *) *params;
    char *              pname   = p->name;
    struct sqlval *     val     = &p->value;
    dvoid *             data    = 0;
    
    if ( empty(pname) ) {
      sprintf(db->errmsg, "Null bind-parameter name given\n");
      return db->success = 0;
    }
    
    if ( ! val->data || val->is_null ) {
      indp = (dvoid *) &null_indicator;
      data = (dvoid * ) "";     /* Shouldn't really need this */
    }
    else {
      indp = (dvoid *) &non_null_indicator;
      data = val->data;
    }
    
    status = OCIBindByName(db->stmt,                /* Statment handle */
                           &dummy,                  /* Output bind handle (Oracle will free it with db->stmt) */
                           db->err,                 /* Error handle */
                           (text *) pname,          /* Param name */
                           (sb4) strlen(pname),     /* Param len */
                           (dvoid *) data,          /* Data value */
                           (sb4) strlen(data) + 1,  /* Data len */
                           SQLT_STR,                /* Data type */
                           indp,                    /* Null indicator */
                           0, 0, 0, 0,              /* alenp, rcodep, maxarra_len, curelep */
                           OCI_DEFAULT);            /* Mode */

    if ( status != OCI_SUCCESS ) {
      sprintf(db->errmsg, "Error binding SQL input parameter '%s' to value '%s' in query:\n---\n%s\n---\n",
              pname, data, sql);
      append_oci_error(db->errmsg, db->err);
      return db->success = 0;
    }

    nparam++;
    params++;
  }

  /* "Execute" the statement - here is where an error is signalled if there is a SQL syntax error */
  status = OCIStmtExecute(db->svc, db->stmt, db->err, iters,
                          0,        /* Row offset */
                          0, 0,     /* Snapshot in/out */
                          OCI_DEFAULT);

  if ( OCI_SUCCESS != status ) {

    ub4 err_offset = 0;

    sprintf(db->errmsg, "Error executing SQL %s:\n---\n%s\n---\n", is_command ? "command" : "query", sql);

    /* Also show what params were given */
    if ( nparam ) {
      int i;
      char buf[50000], buf2[10000];

      sprintf(buf, "SQL bind parameters (%d) given:\n", nparam);
      strcat(db->errmsg, buf);
      params = params_save;
      for (i=0; i < nparam; i++) {
        sprintf(buf, "'%s' -> '%s'\n", params[i]->name, params[i]->value.data);
        strcat(db->errmsg, buf);
      }
      strcat(db->errmsg, "---\n");
    }
    
    append_oci_error(db->errmsg, db->err);

    /* Get the parse error offset so we can print an indicator as to
       where the error occurred */
    status = OCIAttrGet(db->stmt, OCI_HTYPE_STMT, (dvoid *) &err_offset, (ub4 *) 0, OCI_ATTR_PARSE_ERROR_OFFSET, db->err);
    if ( OCI_SUCCESS != status ) {
      strcat(db->errmsg, "Could not get parse error offset:\n");
      append_oci_error(db->errmsg, db->err);
    }
    else {
      char p[100];
      sprintf(p, "At character %d, near ==> indicator in:\n----\n", err_offset);
      strcat(db->errmsg, p);

      strncat(db->errmsg, sql, err_offset);
      strcat(db->errmsg, "\n==> ");
      strcat(db->errmsg, sql + err_offset);
      strcat(db->errmsg, "\n----\n");
    }
    return db->success = 0;
  }

  /* For query, get column info and set up for fetching */
  if ( ! is_command ) {
    if ( ! get_cols(db) ) {
      strcat(db->errmsg, "An error occurred getting column info.\n");
      return db->success = 0;
    }
  }
  /* For command, commit (if auto-commit is on) and get rows affected */
  else {
    sb4 attr_status = OCI_SUCCESS;

    /* Commit */
    if ( db->auto_commit && ! commit(db) ) {
      strcat(db->errmsg, "Error auto-commiting transaction.\n");
      return db->success = 0;
    }

    /* Get rows affected */
    db->rows_affected = 0;
    attr_status = OCIAttrGet((dvoid *) db->stmt, OCI_HTYPE_STMT, &db->rows_affected, 0, OCI_ATTR_ROW_COUNT, db->err);
    if ( attr_status != OCI_SUCCESS ) {
      sprintf(db->errmsg, "Error getting row count for command:\n");
      append_oci_error(db->errmsg, db->err);
      return db->success = 0;
    }
  }

  /* Success */
  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Connect to Oracle, setting up the handles.  Return true for
   success, false for error.  On success, result handles are set.
   On error, the error message is filled in saying what went wrong.
*/
static int init_session(struct db_conn * db, char *user, char * schema, char *password, char *sid, int prefetch_bytes)
{

  sword         status  = 0;        /* Error status return from OCI calls */
  int           success = 0;
  ub4           attval  = 0;

  char sqlbuf[1000];
  
  /* Clear out results */
  db->success = 0;

  /* If already connected, drop and re-connect */
  if ( db->env )
    disconnect(db);

  /* Clear out results */
  *db->errmsg = '\0';
  db->env = 0;
  db->err = 0;
  db->svc = 0;
  
  /* VALIDATE INPUTS */
  /* Default schema to userid */
  if ( empty(schema) )
    schema = user;

  /* Check user, passwd and SID are non-null */
  sid = valid_string(sid);
  password = valid_string(password);
  if ( empty(user) ) {
    sprintf(db->errmsg, "Null user ID given connecting to Oracle server '%s'", sid);
    return db->success = 0;
  }
  
  /* Init Oracle library */
  /* TODO: use mode OCI_OBJECT so that we can describe tables w/ BLOB cols */
  status = OCIInitialize(OCI_OBJECT,
                         0,         /* Context for mode OCI_OBJECT */
                         0,         /* Our malloc() func */
                         0,         /* Our realloc() func */
                         0);        /* Our free() func */

  /* Init an Oracle "environment handle" */
  status = OCIEnvInit(&db->env,     /* Returned: new handle */
                      OCI_DEFAULT,  /* Use mutexes */
                      0,            /* Our memory size */
                      0);           /* Returned: alloc'ed memory */
  if ( OCI_SUCCESS != status ) {
    sprintf(db->errmsg, "Error initializing OCI library: OCIEnvInit() returned %s", status);
    return db->success = 0;
  }

  /* Get an error handle */
  status = OCIHandleAlloc(db->env, (dvoid **) &db->err, OCI_HTYPE_ERROR, 0, 0);
  if ( OCI_SUCCESS != status ) {
    sprintf(db->errmsg, "Error initializing OCI error handle: OCIHandleAlloc(OCI_HTYPE_ERROR) returned %s", status);
    OCIHandleFree(db->env, OCI_HTYPE_ENV);
    db->env = 0;
    return db->success = 0;
  }

  /* Connect to the database */
  status = OCILogon(db->env, db->err, &db->svc,
                    user, strlen(user), password, strlen(password), sid, strlen(sid));
  if ( OCI_SUCCESS != status ) {
    sprintf(db->errmsg, "Error logging on to Oracle service '%s' as user '%s':\n", sid, user);
    append_oci_error(db->errmsg, db->err);
    OCIHandleFree(db->env, OCI_HTYPE_ENV);
    db->env = 0;
    return db->success = 0;
  }

  /* Save login params for later error reporting */
  db->user      = (char *) strdup(user);
  db->schema    = (char *) strdup(schema);
  db->sid       = (char *) strdup(sid);
  
  /* Set up for ANSI date formatting. */
  success = exec_sql(db, "ALTER SESSION SET NLS_DATE_FORMAT = 'YYYY-MM-DD HH24:MI:SS'", 0, 1);
  if ( ! success ) {
    strcat(db->errmsg, "Error setting date format\n");
    return db->success = 0;
  }

  /* Switch to given schema, if given */
  if ( schema && *schema ) {
    sprintf(sqlbuf, "ALTER SESSION SET CURRENT_SCHEMA = %s", schema);
    success = exec_sql(db, sqlbuf, 0, 1);
    if ( ! success ) {
      strcat(db->errmsg, "Error setting current schema\n");
      return db->success = 0;
    }
  }

  /* Set pre-fetch memory and row count for SELECT queries */
  if ( prefetch_bytes < 0 )
    attval = DEFAULT_PREFETCH_BYTES;
  else
    attval = prefetch_bytes;

  status = OCIAttrSet(db->stmt, OCI_HTYPE_STMT, &attval, 0, OCI_ATTR_PREFETCH_MEMORY, db->err);
  if ( status != OCI_SUCCESS ) {
    sprintf(db->errmsg, "Error %d setting prefetch memory:\n", status);
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }
    
  /* Set pre-fetch rows to some very large value.  Oracle will clamp
     this down automatically to what will fit in PREFETCH_MEMORY.
     It's not documented if that would be what happens if we set
     PREFETCH_MEMORY to some buffer size, but left PREFETCH_ROWS at,
     say, zero -- a reasonable convenction for "use as much as in
     PREFETCH_MEMORY".  Oracle seems to behave that way, but don't
     rely on it.  The "clamp down" behavior is documented.  */
  attval = 1000000;
  status = OCIAttrSet(db->stmt, OCI_HTYPE_STMT, &attval, 0, OCI_ATTR_PREFETCH_ROWS, db->err);
  if ( status != OCI_SUCCESS ) {
    sprintf(db->errmsg, "Error settgin prefetch row count:\n");
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  /* Connected successfully */
  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Get a parameter attribute, checking errors */
static int get_param_attr(CONST dvoid * param, int ncol, struct db_conn * db, dvoid * attrib, ub4 * sizep, char *prompt, ub4 attrtype)
{
  sb4           attr_status         = OCI_SUCCESS;

  attr_status = OCIAttrGet((dvoid *) param, OCI_DTYPE_PARAM, attrib, sizep, attrtype, db->err);
  if ( attr_status != OCI_SUCCESS ) {
    /* Error getting param info */
    sprintf(db->errmsg, "Error getting column %s for col %d:\n", prompt, ncol);
    append_oci_error(db->errmsg, db->err);
    return db->success = 0;
  }

  /* Success */
  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Append Oracle error to our specific error */
static void append_oci_error(char *errbuf, OCIError * err)
{
  sword status      = 0;
  char *dummy = 0;
  sb4 errcode = 0;
  char buf[50000];

  /* If Oracle message begins with this, it means we cannot locate
     error messages.  Probably issue with ORACLE_HOME */
    
  /* Hack: this is highly language dependent */
  char * leading = "Error while trying to retrieve text for error";
    
  status = OCIErrorGet(err, 1, dummy, &errcode, buf, sizeof buf, OCI_HTYPE_ERROR);
  if ( status )
    return;

  /* Append Oracle error */
  strcat(errbuf, buf);
  
  /* See if having trouble getting error text */
  if ( 0 == strncmp(buf, leading, strlen(leading)) ) {
    char reason[1000];
    char * home = getenv("ORACLE_HOME");
    if ( ! home )
      strcpy(reason, "ORACLE_HOME is not set.");
    else if ( ! *home )
      strcpy(reason, "ORACLE_HOME is set to the empty string.");
    else 
      sprintf(reason, "ORACLE_HOME value '%s' is possibly not valid.", home);

    strcat(errbuf, "Cannot get Oracle error message text.  Check ORACLE_HOME environment variable.\n");
    strcat(errbuf, reason);
  }

}

/* ------------------------------------------------------------------------------------------------------------- */

/* Decode data type code */
static char * decode_data_type(int dtype) 
{
  static char buf[100];
  switch (dtype) {
  case 1:   return "VARCHAR2";
  case 2:   return "NUMBER";
  case 3:   return "INTEGER";
  case 4:   return "FLOAT";
  case 8:   return "LONG";
  case 11:  return "ROWID";
  case 12:  return "DATE";
  case 23:  return "RAW";
  case 24:  return "LONG RAW";
  case 96:  return "CHAR";
  case 104: return "ROWID DESC";
  case 105: return "MLSLABEL";
  case 108: return "User defined";
  case 111: return "REF";
  case 112: return "CLOB";
  case 113: return "BLOB";
  }
  sprintf("<Unknown type %d>", buf);
  return buf;
}

/* Get appropriate length for fetch into on output define variable */
static int fetch_data_len(int dtype, int dlen)
{
  static char buf[100];

  /* We get everything as a string (SQLT_STR).  So for numbers, use
     the largest buffer that would ever be used by an Oracle number,
     for dates a reasonable limit for formatted dates (e.g.,
     "Wednesday, November 23, 2005") and for chars, just that length,
     plus one for the null terminator.

     With all this, we should not be getting Oracle truncation due to
     deficiencies in our buffer size (i.e., our buffer should always
     accomodate the Oracle data).  */

  switch (dtype) {
  case 1:   /* VARCHAR2 */
  case 96:  /* CHAR */
    return dlen + 1;
    
  case 2:   /* NUMBER */
  case 3:   /* INTEGER */
  case 4:   /* FLOAT */
    return 50;
    
  case 8:   /* LONG */
    return 70000;
    
  case 12:  /* DATE */
    return 50;
  }
  return SQLT_STR;
}

/* ------------------------------------------------------------------------------------------------------------- */
/* Free contents of a column */
static void free_column(struct column * c)
{
  free_if_non_null(c->name);
  free_if_non_null(c->data);

  if ( c->def )
    OCIHandleFree(c->def, OCI_HTYPE_DEFINE);
}

/* ------------------------------------------------------------------------------------------------------------- */

static void free_if_non_null(void *p) { if ( p ) free(p); }

/* ------------------------------------------------------------------------------------------------------------- */
static int disconnect(struct db_conn * db)
{
  if ( ! db )
    return 0;

  free_columns(db);
  
  /* This should cause Oracle to free up all other handles created under it */
  if ( db->env )
    OCIHandleFree(db->env, OCI_HTYPE_ENV);

  free_if_non_null(db->user);
  free_if_non_null(db->schema);
  free_if_non_null(db->sid);
  free_if_non_null(db->sql);
  free_if_non_null(db->errmsg);

  reset_db_conn(db);

  return db->success = 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Free column info */
static void free_columns(struct db_conn * db)
{
  int i;
  
  /* Clear out internal column struct */
  if ( db->columns ) {
    for ( i=0; i < db->ncol; i++ )
      free_column(&db->columns[i]);
    free(db->columns);
    db->columns = 0;
  }

  /* Free externally visible row and column structures */
  if ( db->sqlcols ) {
    for ( i=0; i < db->ncol; i++ )
      free_if_non_null(db->sqlcols[i]);
    free(db->sqlcols);
    db->sqlcols = 0;
  }
  if ( db->currow ) {
    for ( i=0; i < db->ncol; i++ )
      free_if_non_null(db->currow[i]);
    free(db->currow);
    db->currow = 0;
  }
}

/* Reset a db_conn struct */
static void reset_db_conn(struct db_conn * db)
{
  db->env               = 0;
  db->err               = 0;
  db->svc               = 0;
  db->prefetch_bytes    = -1;
  db->auto_commit       = 1;
  db->stmt              = 0;

  db->sql               = 0;
  db->is_command        = 0;
  db->params            = 0;
  db->nparam            = 0;
  db->columns           = 0;
  db->sqlcols           = 0;
  db->currow            = 0;
  db->ncol              = 0;
  db->rows_affected     = 0;
  db->eof               = 0;
  db->success           = 0;
  db->errmsg            = 0;
}

/* ------------------------------------------------------------------------------------------------------------- */
/* Do checks prior to operations that are relevant only for an active SQL statement */
static int check_active_statement(struct db_conn * db, char * action)
{
  /* Clear out results */
  *db->errmsg = '\0';
  db->success = 0;
  
  /* Make sure we have a connection, and an active SQL statement */
  if ( ! db->env || ! db->svc ) {
    sprintf(db->errmsg, "Attempt to %s while not connected.\n", action);
    return 0;
  }
  else if ( ! db->stmt ) {
    sprintf(db->errmsg, "Attempt to %s before SQL statement executed.\n", action);
    return 0;
  }
  return 1;
}

/* Do checks prior to operations that are relevant only for SELECT query */
static int check_active_select(struct db_conn * db, char * action)
{
  /* First check active SQL */
  if ( ! check_active_statement(db, action) )
       return 0;
  else if ( db->is_command ) {
    sprintf(db->errmsg, "Attempt to %s on non-SELECT SQL statement:\n%s\n", action, db->sql);
    return 0;
  }
  /* If have statement, but not column info, probably had an invalid
     statement or other error. */
  else if ( ! db->sqlcols ) {
    sprintf(db->errmsg, "Attempt to %s on invalid SQL statement:\n%s\n", action, db->sql);
    return 0;
  }
  return 1;
}

/* ------------------------------------------------------------------------------------------------------------- */

/* Get number of columns in SELECT query, or zero if error. */
static int ncol(struct db_conn * db)
{
  if ( ! check_active_select(db, "get number of SELECT columns") )
    return 0;
  return db->ncol;
}

/* Get EOF status of SELECT query */
static int eof(struct db_conn * db)
{
  /* Make sure have an active SELECT */
  if ( ! check_active_select(db, "get fetch EOF status") )
    return db->success = 0;

  /* Make sure did a fetch and have db->currow */
  if ( ! db->currow ) {
    sprintf(db->errmsg, "Attempt to get EOF status before first fetch.\n");
    return db->success = 0;
  }
  db->success = 1;
  return db->eof;
}

/* Get success status of last operation */
static int success(struct db_conn * db)
{
  return db->success;
}

/* Get column info for SELECT result */
static struct sqlcol ** column_info(struct db_conn * db)
{
  if ( ! check_active_select(db, "get column info for SELECT results") )
    return 0;
  db->success = 1;
  return db->sqlcols;
}

/* Get row values for most recent fetch */
static struct sqlval ** row_values(struct db_conn * db)
{
  int n;
  
  /* Make sure have an active SELECT */
  if ( ! check_active_select(db, "get row values for SELECT results") ) {
    db->success = 0;
    return 0;
  }

  /* Make sure did a fetch and have db->currow */
  if ( ! db->currow ) {
    sprintf(db->errmsg, "Attempt to get row values before first fetch.\n");
    db->success = 0;
    return 0;
  }

  /* Make sure not at EOF */
  if ( db->eof ) {
    sprintf(db->errmsg, "Attempt to get row values at EOF.\n");
    db->success = 0;
    return 0;
  }

  /*
  printf("\n");
  for (n=0; n < db->ncol; n++) {
    if ( db->currow[n]->is_null )
      printf("sqlval[%d]->data is NULL\n", n);
    else
      printf("sqlval[%d]->data is '%s'\n", n, db->currow[n]->data);
  }
  printf("terminator is '%d'\n", db->currow[n]);
  */
  
  db->success = 1;
  return db->currow;
}

/* Get no. of rows affected (no. insert/update/delete, or no. fetched so far) */
static int rows_affected(struct db_conn * db)
{
  /* Make sure have an active SELECT */
  if ( ! check_active_statement(db, "get number of affected rows") )
    return db->success = 0;
  db->success = 1;
  return db->rows_affected;
}

/* Set auto_commit flag (returns what it was before) */
static int set_auto_commit(struct db_conn * db, int auto_commit)
{
  int old_value = db->auto_commit;
  db->auto_commit = auto_commit;
  return old_value;
}

/* Is string NULL empty? */
static int empty(char * s) { return !s || !*s; }
/* Map NULL to empty string */
static char * valid_string(char * s) { return s ? s : ""; }

/* ------------------------------------------------------------------------------------------------------------- */

/* Wrapper routines - these are part of the "void *" based interface
   that are straight-through calls to the equivalent routines in this
   module.  More functions (e.g., to get column info and data) are
   implemented in the interface module.
*/

void * oracle_connect(char * user, char * schema, char * password, char * sid, int prefetch_bytes, int auto_commit)
{ return (void *) connect(user, schema, password, sid, prefetch_bytes, auto_commit); }

int oracle_disconnect(void * db)
{ return disconnect((struct db_conn *) db); }

int oracle_exec_sql(void * db, char * sql, struct sqlparam ** params, int is_command)
{ return exec_sql((struct db_conn *) db, sql, params, is_command); }

int oracle_fetch_row(void * db)
{ return fetch_row((struct db_conn *) db); }

int oracle_ncol(void * db)
{ return ncol((struct db_conn *) db); }

int oracle_eof(void * db)
{ return eof((struct db_conn *) db); }

int oracle_success(void * db)
{ return success((struct db_conn *) db); }

struct sqlcol ** oracle_column_info(void * db)
{ return column_info((struct db_conn *) db); }

struct sqlval ** oracle_row_values(void * db)
{ return row_values((struct db_conn *) db); }

int oracle_rows_affected(void * db)
{ return rows_affected((struct db_conn *) db); }

int oracle_commit(void * db)
{ return commit((struct db_conn *) db); }

int oracle_rollback(void * db)
{ return rollback((struct db_conn *) db); }

int oracle_set_auto_commit(void * db, int auto_commit)
{ return set_auto_commit((struct db_conn *) db, auto_commit); }

/* ------------------------------------------------------------------------------------------------------------- */
