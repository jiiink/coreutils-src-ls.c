/* 'dir', 'vdir' and 'ls' directory listing programs for GNU.
   Copyright (C) 1985-2025 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* If ls_mode is LS_MULTI_COL,
   the multi-column format is the default regardless
   of the type of output device.
   This is for the 'dir' program.

   If ls_mode is LS_LONG_FORMAT,
   the long format is the default regardless of the
   type of output device.
   This is for the 'vdir' program.

   If ls_mode is LS_LS,
   the output format depends on whether the output
   device is a terminal.
   This is for the 'ls' program.  */

/* Written by Richard Stallman and David MacKenzie.  */

/* Color support by Peter Anvin <Peter.Anvin@linux.org> and Dennis
   Flaherty <dennisf@denix.elk.miles.com> based on original patches by
   Greg Lee <lee@uhunix.uhcc.hawaii.edu>.  */

#include <config.h>
#include <ctype.h>
#include <sys/types.h>

#include <termios.h>
#if HAVE_STROPTS_H
# include <stropts.h>
#endif
#include <sys/ioctl.h>

#ifdef WINSIZE_IN_PTEM
# include <sys/stream.h>
# include <sys/ptem.h>
#endif

#include <stdio.h>
#include <setjmp.h>
#include <pwd.h>
#include <getopt.h>
#include <signal.h>

#if HAVE_LANGINFO_CODESET
# include <langinfo.h>
#endif

/* Use SA_NOCLDSTOP as a proxy for whether the sigaction machinery is
   present.  */
#ifndef SA_NOCLDSTOP
# define SA_NOCLDSTOP 0
# define sigprocmask(How, Set, Oset) /* empty */
# define sigset_t int
# if ! HAVE_SIGINTERRUPT
#  define siginterrupt(sig, flag) /* empty */
# endif
#endif

/* NonStop circa 2011 lacks both SA_RESTART and siginterrupt, so don't
   restart syscalls after a signal handler fires.  This may cause
   colors to get messed up on the screen if 'ls' is interrupted, but
   that's the best we can do on such a platform.  */
#ifndef SA_RESTART
# define SA_RESTART 0
#endif

#include <fnmatch.h>

#include "acl.h"
#include "argmatch.h"
#include "system.h"
#include "assure.h"
#include "c-strcase.h"
#include "dev-ino.h"
#include "filenamecat.h"
#include "hard-locale.h"
#include "hash.h"
#include "human.h"
#include "filemode.h"
#include "filevercmp.h"
#include "idcache.h"
#include "ls.h"
#include "mbswidth.h"
#include "mpsort.h"
#include "obstack.h"
#include "quote.h"
#include "stat-size.h"
#include "stat-time.h"
#include "strftime.h"
#include "xdectoint.h"
#include "xstrtol.h"
#include "xstrtol-error.h"
#include "areadlink.h"
#include "dircolors.h"
#include "xgethostname.h"
#include "c-ctype.h"
#include "canonicalize.h"
#include "statx.h"

/* Include <sys/capability.h> last to avoid a clash of <sys/types.h>
   include guards with some premature versions of libcap.
   For more details, see <https://bugzilla.redhat.com/483548>.  */
#ifdef HAVE_CAP
# include <sys/capability.h>
#endif

#if HAVE_LINUX_XATTR_H
# include <linux/xattr.h>
# ifndef XATTR_NAME_CAPS
#  define XATTR_NAME_CAPS "security.capability"
# endif
#endif

#define PROGRAM_NAME (ls_mode == LS_LS ? "ls" \
                      : (ls_mode == LS_MULTI_COL \
                         ? "dir" : "vdir"))

#define AUTHORS \
  proper_name ("Richard M. Stallman"), \
  proper_name ("David MacKenzie")

#define obstack_chunk_alloc malloc
#define obstack_chunk_free free

/* Unix-based readdir implementations have historically returned a dirent.d_ino
   value that is sometimes not equal to the stat-obtained st_ino value for
   that same entry.  This error occurs for a readdir entry that refers
   to a mount point.  readdir's error is to return the inode number of
   the underlying directory -- one that typically cannot be stat'ed, as
   long as a file system is mounted on that directory.  RELIABLE_D_INO
   encapsulates whether we can use the more efficient approach of relying
   on readdir-supplied d_ino values, or whether we must incur the cost of
   calling stat or lstat to obtain each guaranteed-valid inode number.  */

#ifndef READDIR_LIES_ABOUT_MOUNTPOINT_D_INO
# define READDIR_LIES_ABOUT_MOUNTPOINT_D_INO 1
#endif

#if READDIR_LIES_ABOUT_MOUNTPOINT_D_INO
# define RELIABLE_D_INO(dp) NOT_AN_INODE_NUMBER
#else
# define RELIABLE_D_INO(dp) D_INO (dp)
#endif

#if ! HAVE_STRUCT_STAT_ST_AUTHOR
# define st_author st_uid
#endif

enum filetype
  {
    unknown,
    fifo,
    chardev,
    directory,
    blockdev,
    normal,
    symbolic_link,
    sock,
    whiteout,
    arg_directory
  };
enum { filetype_cardinality = arg_directory + 1 };

/* Display letters and indicators for each filetype.
   Keep these in sync with enum filetype.  */
static char const filetype_letter[] =
  {'?', 'p', 'c', 'd', 'b', '-', 'l', 's', 'w', 'd'};
static_assert (ARRAY_CARDINALITY (filetype_letter) == filetype_cardinality);

/* Map enum filetype to <dirent.h> d_type values.  */
static unsigned char const filetype_d_type[] =
  {
    DT_UNKNOWN, DT_FIFO, DT_CHR, DT_DIR, DT_BLK, DT_REG, DT_LNK, DT_SOCK,
    DT_WHT, DT_DIR
  };
static_assert (ARRAY_CARDINALITY (filetype_d_type) == filetype_cardinality);

/* Map d_type values to enum filetype.  */
static char const d_type_filetype[UCHAR_MAX + 1] =
  {
    [DT_BLK] = blockdev, [DT_CHR] = chardev, [DT_DIR] = directory,
    [DT_FIFO] = fifo, [DT_LNK] = symbolic_link, [DT_REG] = normal,
    [DT_SOCK] = sock, [DT_WHT] = whiteout
  };

enum acl_type
  {
    ACL_T_NONE,
    ACL_T_UNKNOWN,
    ACL_T_LSM_CONTEXT_ONLY,
    ACL_T_YES
  };

struct fileinfo
  {
    /* The file name.  */
    char *name;

    /* For symbolic link, name of the file linked to, otherwise zero.  */
    char *linkname;

    /* For terminal hyperlinks. */
    char *absolute_name;

    struct stat stat;

    enum filetype filetype;

    /* For symbolic link and long listing, st_mode of file linked to, otherwise
       zero.  */
    mode_t linkmode;

    /* security context.  */
    char *scontext;

    bool stat_ok;

    /* For symbolic link and color printing, true if linked-to file
       exists, otherwise false.  */
    bool linkok;

    /* For long listings, true if the file has an access control list,
       or a security context.  */
    enum acl_type acl_type;

    /* For color listings, true if a regular file has capability info.  */
    bool has_capability;

    /* Whether file name needs quoting. tri-state with -1 == unknown.  */
    int quoted;

    /* Cached screen width (including quoting).  */
    size_t width;
  };

/* Null is a valid character in a color indicator (think about Epson
   printers, for example) so we have to use a length/buffer string
   type.  */

struct bin_str
  {
    size_t len;			/* Number of bytes */
    char const *string;		/* Pointer to the same */
  };

#if ! HAVE_TCGETPGRP
# define tcgetpgrp(Fd) 0
#endif

static size_t quote_name (char const *name,
                          struct quoting_options const *options,
                          int needs_general_quoting,
                          const struct bin_str *color,
                          bool allow_pad, struct obstack *stack,
                          char const *absolute_name);
static size_t quote_name_buf (char **inbuf, size_t bufsize, char *name,
                              struct quoting_options const *options,
                              int needs_general_quoting, size_t *width,
                              bool *pad);
static int decode_switches (int argc, char **argv);
static bool file_ignored (char const *name);
static uintmax_t gobble_file (char const *name, enum filetype type,
                              ino_t inode, bool command_line_arg,
                              char const *dirname);
static const struct bin_str * get_color_indicator (const struct fileinfo *f,
                                                   bool symlink_target);
static bool print_color_indicator (const struct bin_str *ind);
static void put_indicator (const struct bin_str *ind);
static void add_ignore_pattern (char const *pattern);
static void attach (char *dest, char const *dirname, char const *name);
static void clear_files (void);
static void extract_dirs_from_files (char const *dirname,
                                     bool command_line_arg);
static void get_link_name (char const *filename, struct fileinfo *f,
                           bool command_line_arg);
static void indent (size_t from, size_t to);
static idx_t calculate_columns (bool by_columns);
static void print_current_files (void);
static void print_dir (char const *name, char const *realname,
                       bool command_line_arg);
static size_t print_file_name_and_frills (const struct fileinfo *f,
                                          size_t start_col);
static void print_horizontal (void);
static int format_user_width (uid_t u);
static int format_group_width (gid_t g);
static void print_long_format (const struct fileinfo *f);
static void print_many_per_line (void);
static size_t print_name_with_quoting (const struct fileinfo *f,
                                       bool symlink_target,
                                       struct obstack *stack,
                                       size_t start_col);
static void prep_non_filename_text (void);
static bool print_type_indicator (bool stat_ok, mode_t mode,
                                  enum filetype type);
static void print_with_separator (char sep);
static void queue_directory (char const *name, char const *realname,
                             bool command_line_arg);
static void sort_files (void);
static void parse_ls_color (void);

static int getenv_quoting_style (void);

static size_t quote_name_width (char const *name,
                                struct quoting_options const *options,
                                int needs_general_quoting);

/* Initial size of hash table.
   Most hierarchies are likely to be shallower than this.  */
enum { INITIAL_TABLE_SIZE = 30 };

/* The set of 'active' directories, from the current command-line argument
   to the level in the hierarchy at which files are being listed.
   A directory is represented by its device and inode numbers (struct dev_ino).
   A directory is added to this set when ls begins listing it or its
   entries, and it is removed from the set just after ls has finished
   processing it.  This set is used solely to detect loops, e.g., with
   mkdir loop; cd loop; ln -s ../loop sub; ls -RL  */
static Hash_table *active_dir_set;

#define LOOP_DETECT (!!active_dir_set)

/* The table of files in the current directory:

   'cwd_file' points to a vector of 'struct fileinfo', one per file.
   'cwd_n_alloc' is the number of elements space has been allocated for.
   'cwd_n_used' is the number actually in use.  */

/* Address of block containing the files that are described.  */
static struct fileinfo *cwd_file;

/* Length of block that 'cwd_file' points to, measured in files.  */
static idx_t cwd_n_alloc;

/* Index of first unused slot in 'cwd_file'.  */
static idx_t cwd_n_used;

/* Whether files needs may need padding due to quoting.  */
static bool cwd_some_quoted;

/* Whether quoting style _may_ add outer quotes,
   and whether aligning those is useful.  */
static bool align_variable_outer_quotes;

/* Vector of pointers to files, in proper sorted order, and the number
   of entries allocated for it.  */
static void **sorted_file;
static size_t sorted_file_alloc;

/* When true, in a color listing, color each symlink name according to the
   type of file it points to.  Otherwise, color them according to the 'ln'
   directive in LS_COLORS.  Dangling (orphan) symlinks are treated specially,
   regardless.  This is set when 'ln=target' appears in LS_COLORS.  */

static bool color_symlink_as_referent;

static char const *hostname;

/* Mode of appropriate file for coloring.  */
static mode_t
file_or_link_mode (struct fileinfo const *file)
{
  if (color_symlink_as_referent && file->linkok)
    {
      return file->linkmode;
    }
  else
    {
      return file->stat.st_mode;
    }
}


/* Record of one pending directory waiting to be listed.  */

struct pending
  {
    char *name;
    /* If the directory is actually the file pointed to by a symbolic link we
       were told to list, 'realname' will contain the name of the symbolic
       link, otherwise zero.  */
    char *realname;
    bool command_line_arg;
    struct pending *next;
  };

static struct pending *pending_dirs;

/* Current time in seconds and nanoseconds since 1970, updated as
   needed when deciding whether a file is recent.  */

static struct timespec current_time;

static bool print_scontext;
static char UNKNOWN_SECURITY_CONTEXT[] = "?";

/* Whether any of the files has an ACL.  This affects the width of the
   mode column.  */

static bool any_has_acl;

/* The number of columns to use for columns containing inode numbers,
   block sizes, link counts, owners, groups, authors, major device
   numbers, minor device numbers, and file sizes, respectively.  */

static int inode_number_width;
static int block_size_width;
static int nlink_width;
static int scontext_width;
static int owner_width;
static int group_width;
static int author_width;
static int major_device_number_width;
static int minor_device_number_width;
static int file_size_width;

/* Option flags */

/* long_format for lots of info, one per line.
   one_per_line for just names, one per line.
   many_per_line for just names, many per line, sorted vertically.
   horizontal for just names, many per line, sorted horizontally.
   with_commas for just names, many per line, separated by commas.

   -l (and other options that imply -l), -1, -C, -x and -m control
   this parameter.  */

enum format
  {
    long_format,		/* -l and other options that imply -l */
    one_per_line,		/* -1 */
    many_per_line,		/* -C */
    horizontal,			/* -x */
    with_commas			/* -m */
  };

static enum format format;

/* 'full-iso' uses full ISO-style dates and times.  'long-iso' uses longer
   ISO-style timestamps, though shorter than 'full-iso'.  'iso' uses shorter
   ISO-style timestamps.  'locale' uses locale-dependent timestamps.  */
enum time_style
  {
    full_iso_time_style,	/* --time-style=full-iso */
    long_iso_time_style,	/* --time-style=long-iso */
    iso_time_style,		/* --time-style=iso */
    locale_time_style		/* --time-style=locale */
  };

static char const *const time_style_args[] =
{
  "full-iso", "long-iso", "iso", "locale", nullptr
};
static enum time_style const time_style_types[] =
{
  full_iso_time_style, long_iso_time_style, iso_time_style,
  locale_time_style
};
ARGMATCH_VERIFY (time_style_args, time_style_types);

/* Type of time to print or sort by.  Controlled by -c and -u.
   The values of each item of this enum are important since they are
   used as indices in the sort functions array (see sort_files()).  */

enum time_type
  {
    time_mtime = 0,		/* default */
    time_ctime,			/* -c */
    time_atime,			/* -u */
    time_btime,                 /* birth time */
    time_numtypes		/* the number of elements of this enum */
  };

static enum time_type time_type;
static bool explicit_time;

/* The file characteristic to sort by.  Controlled by -t, -S, -U, -X, -v.
   The values of each item of this enum are important since they are
   used as indices in the sort functions array (see sort_files()).  */

enum sort_type
  {
    sort_name = 0,		/* default */
    sort_extension,		/* -X */
    sort_width,
    sort_size,			/* -S */
    sort_version,		/* -v */
    sort_time,			/* -t; must be second to last */
    sort_none,			/* -U; must be last */
    sort_numtypes		/* the number of elements of this enum */
  };

static enum sort_type sort_type;

/* Direction of sort.
   false means highest first if numeric,
   lowest first if alphabetic;
   these are the defaults.
   true means the opposite order in each case.  -r  */

static bool sort_reverse;

/* True means to display owner information.  -g turns this off.  */

static bool print_owner = true;

/* True means to display author information.  */

static bool print_author;

/* True means to display group information.  -G and -o turn this off.  */

static bool print_group = true;

/* True means print the user and group id's as numbers rather
   than as names.  -n  */

static bool numeric_ids;

/* True means mention the size in blocks of each file.  -s  */

static bool print_block_size;

/* Human-readable options for output, when printing block counts.  */
static int human_output_opts;

/* The units to use when printing block counts.  */
static uintmax_t output_block_size;

/* Likewise, but for file sizes.  */
static int file_human_output_opts;
static uintmax_t file_output_block_size = 1;

/* Follow the output with a special string.  Using this format,
   Emacs' dired mode starts up twice as fast, and can handle all
   strange characters in file names.  */
static bool dired;

/* 'none' means don't mention the type of files.
   'slash' means mention directories only, with a '/'.
   'file_type' means mention file types.
   'classify' means mention file types and mark executables.

   Controlled by -F, -p, and --indicator-style.  */

enum indicator_style
  {
    none = 0,	/*     --indicator-style=none (default) */
    slash,	/* -p, --indicator-style=slash */
    file_type,	/*     --indicator-style=file-type */
    classify	/* -F, --indicator-style=classify */
  };

static enum indicator_style indicator_style;

/* Names of indicator styles.  */
static char const *const indicator_style_args[] =
{
  "none", "slash", "file-type", "classify", nullptr
};
static enum indicator_style const indicator_style_types[] =
{
  none, slash, file_type, classify
};
ARGMATCH_VERIFY (indicator_style_args, indicator_style_types);

/* True means use colors to mark types.  Also define the different
   colors as well as the stuff for the LS_COLORS environment variable.
   The LS_COLORS variable is now in a termcap-like format.  */

static bool print_with_color;

static bool print_hyperlink;

/* Whether we used any colors in the output so far.  If so, we will
   need to restore the default color later.  If not, we will need to
   call prep_non_filename_text before using color for the first time. */

static bool used_color = false;

enum when_type
  {
    when_never,		/* 0: default or --color=never */
    when_always,	/* 1: --color=always */
    when_if_tty		/* 2: --color=tty */
  };

enum Dereference_symlink
  {
    DEREF_UNDEFINED = 0,		/* default */
    DEREF_NEVER,
    DEREF_COMMAND_LINE_ARGUMENTS,	/* -H */
    DEREF_COMMAND_LINE_SYMLINK_TO_DIR,	/* the default, in certain cases */
    DEREF_ALWAYS			/* -L */
  };

enum indicator_no
  {
    C_LEFT, C_RIGHT, C_END, C_RESET, C_NORM, C_FILE, C_DIR, C_LINK,
    C_FIFO, C_SOCK,
    C_BLK, C_CHR, C_MISSING, C_ORPHAN, C_EXEC, C_DOOR, C_SETUID, C_SETGID,
    C_STICKY, C_OTHER_WRITABLE, C_STICKY_OTHER_WRITABLE, C_CAP, C_MULTIHARDLINK,
    C_CLR_TO_EOL
  };

static char const indicator_name[][2]=
  {
    {'l','c'}, {'r','c'}, {'e','c'}, {'r','s'}, {'n','o'},
    {'f','i'}, {'d','i'}, {'l','n'},
    {'p','i'}, {'s','o'},
    {'b','d'}, {'c','d'}, {'m','i'}, {'o','r'}, {'e','x'},
    {'d','o'}, {'s','u'}, {'s','g'},
    {'s','t'}, {'o','w'}, {'t','w'}, {'c','a'}, {'m','h'},
    {'c','l'}
  };

struct color_ext_type
  {
    struct bin_str ext;		/* The extension we're looking for */
    struct bin_str seq;		/* The sequence to output when we do */
    bool   exact_match;		/* Whether to compare case insensitively */
    struct color_ext_type *next;	/* Next in list */
  };

static struct bin_str color_indicator[] =
  {
    { 2, (char const []) {'\033','['} },/* lc: Left of color sequence */
    { 1, (char const []) {'m'} },	/* rc: Right of color sequence */
    { 0, nullptr },			/* ec: End color (replaces lc+rs+rc) */
    { 1, (char const []) {'0'} },	/* rs: Reset to ordinary colors */
    { 0, nullptr },			/* no: Normal */
    { 0, nullptr },			/* fi: File: default */
    { 5, ((char const [])
          {'0','1',';','3','4'}) },	/* di: Directory: bright blue */
    { 5, ((char const [])
          {'0','1',';','3','6'}) },	/* ln: Symlink: bright cyan */
    { 2, (char const []) {'3','3'} },		/* pi: Pipe: yellow/brown */
    { 5, ((char const [])
          {'0','1',';','3','5'}) },	/* so: Socket: bright magenta */
    { 5, ((char const [])
          {'0','1',';','3','3'}) },	/* bd: Block device: bright yellow */
    { 5, ((char const [])
          {'0','1',';','3','3'}) },	/* cd: Char device: bright yellow */
    { 0, nullptr },			/* mi: Missing file: undefined */
    { 0, nullptr },			/* or: Orphaned symlink: undefined */
    { 5, ((char const [])
          {'0','1',';','3','2'}) },	/* ex: Executable: bright green */
    { 5, ((char const [])
          {'0','1',';','3','5'}) },	/* do: Door: bright magenta */
    { 5, ((char const [])
          {'3','7',';','4','1'}) },	/* su: setuid: white on red */
    { 5, ((char const [])
          {'3','0',';','4','3'}) },	/* sg: setgid: black on yellow */
    { 5, ((char const [])
          {'3','7',';','4','4'}) },	/* st: sticky: black on blue */
    { 5, ((char const [])
          {'3','4',';','4','2'}) },	/* ow: other-writable: blue on green */
    { 5, ((char const [])
          {'3','0',';','4','2'}) },	/* tw: ow w/ sticky: black on green */
    { 0, nullptr },			/* ca: disabled by default */
    { 0, nullptr },			/* mh: disabled by default */
    { 3, ((char const [])
          {'\033','[','K'}) },		/* cl: clear to end of line */
  };

/* A list mapping file extensions to corresponding display sequence.  */
static struct color_ext_type *color_ext_list = nullptr;

/* Buffer for color sequences */
static char *color_buf;

/* True means to check for orphaned symbolic link, for displaying
   colors, or to group symlink to directories with other dirs.  */

static bool check_symlink_mode;

/* True means mention the inode number of each file.  -i  */

static bool print_inode;

/* What to do with symbolic links.  Affected by -d, -F, -H, -l (and
   other options that imply -l), and -L.  */

static enum Dereference_symlink dereference;

/* True means when a directory is found, display info on its
   contents.  -R  */

static bool recursive;

/* True means when an argument is a directory name, display info
   on it itself.  -d  */

static bool immediate_dirs;

/* True means that directories are grouped before files. */

static bool directories_first;

/* Which files to ignore.  */

static enum
{
  /* Ignore files whose names start with '.', and files specified by
     --hide and --ignore.  */
  IGNORE_DEFAULT = 0,

  /* Ignore '.', '..', and files specified by --ignore.  */
  IGNORE_DOT_AND_DOTDOT,

  /* Ignore only files specified by --ignore.  */
  IGNORE_MINIMAL
} ignore_mode;

/* A linked list of shell-style globbing patterns.  If a non-argument
   file name matches any of these patterns, it is ignored.
   Controlled by -I.  Multiple -I options accumulate.
   The -B option adds '*~' and '.*~' to this list.  */

struct ignore_pattern
  {
    char const *pattern;
    struct ignore_pattern *next;
  };

static struct ignore_pattern *ignore_patterns;

/* Similar to IGNORE_PATTERNS, except that -a or -A causes this
   variable itself to be ignored.  */
static struct ignore_pattern *hide_patterns;

/* True means output nongraphic chars in file names as '?'.
   (-q, --hide-control-chars)
   qmark_funny_chars and the quoting style (-Q, --quoting-style=WORD) are
   independent.  The algorithm is: first, obey the quoting style to get a
   string representing the file name;  then, if qmark_funny_chars is set,
   replace all nonprintable chars in that string with '?'.  It's necessary
   to replace nonprintable chars even in quoted strings, because we don't
   want to mess up the terminal if control chars get sent to it, and some
   quoting methods pass through control chars as-is.  */
static bool qmark_funny_chars;

/* Quoting options for file and dir name output.  */

static struct quoting_options *filename_quoting_options;
static struct quoting_options *dirname_quoting_options;

/* The number of chars per hardware tab stop.  Setting this to zero
   inhibits the use of TAB characters for separating columns.  -T */
static size_t tabsize;

/* True means print each directory name before listing it.  */

static bool print_dir_name;

/* The line length to use for breaking lines in many-per-line format.
   Can be set with -w.  If zero, there is no limit.  */

static size_t line_length;

/* The local time zone rules, as per the TZ environment variable.  */

static timezone_t localtz;

/* If true, the file listing format requires that stat be called on
   each file.  */

static bool format_needs_stat;

/* Similar to 'format_needs_stat', but set if only the file type is
   needed.  */

static bool format_needs_type;

/* Like 'format_needs_stat', but set only if capability colors are needed.  */

static bool format_needs_capability;

/* An arbitrary limit on the number of bytes in a printed timestamp.
   This is set to a relatively small value to avoid the need to worry
   about denial-of-service attacks on servers that run "ls" on behalf
   of remote clients.  1000 bytes should be enough for any practical
   timestamp format.  */

enum { TIME_STAMP_LEN_MAXIMUM = MAX (1000, INT_STRLEN_BOUND (time_t)) };

/* strftime formats for non-recent and recent files, respectively, in
   -l output.  */

static char const *long_time_format[2] =
  {
    /* strftime format for non-recent files (older than 6 months), in
       -l output.  This should contain the year, month and day (at
       least), in an order that is understood by people in your
       locale's territory.  Please try to keep the number of used
       screen columns small, because many people work in windows with
       only 80 columns.  But make this as wide as the other string
       below, for recent files.  */
    /* TRANSLATORS: ls output needs to be aligned for ease of reading,
       so be wary of using variable width fields from the locale.
       Note %b is handled specially by ls and aligned correctly.
       Note also that specifying a width as in %5b is erroneous as strftime
       will count bytes rather than characters in multibyte locales.  */
    N_("%b %e  %Y"),
    /* strftime format for recent files (younger than 6 months), in -l
       output.  This should contain the month, day and time (at
       least), in an order that is understood by people in your
       locale's territory.  Please try to keep the number of used
       screen columns small, because many people work in windows with
       only 80 columns.  But make this as wide as the other string
       above, for non-recent files.  */
    /* TRANSLATORS: ls output needs to be aligned for ease of reading,
       so be wary of using variable width fields from the locale.
       Note %b is handled specially by ls and aligned correctly.
       Note also that specifying a width as in %5b is erroneous as strftime
       will count bytes rather than characters in multibyte locales.  */
    N_("%b %e %H:%M")
  };

/* The set of signals that are caught.  */

static sigset_t caught_signals;

/* If nonzero, the value of the pending fatal signal.  */

static sig_atomic_t volatile interrupt_signal;

/* A count of the number of pending stop signals that have been received.  */

static sig_atomic_t volatile stop_signal_count;

/* Desired exit status.  */

static int exit_status;

/* Exit statuses.  */
enum
  {
    /* "ls" had a minor problem.  E.g., while processing a directory,
       ls obtained the name of an entry via readdir, yet was later
       unable to stat that name.  This happens when listing a directory
       in which entries are actively being removed or renamed.  */
    LS_MINOR_PROBLEM = 1,

    /* "ls" had more serious trouble (e.g., memory exhausted, invalid
       option or failure to stat a command line argument.  */
    LS_FAILURE = 2
  };

/* For long options that have no equivalent short option, use a
   non-character as a pseudo short option, starting with CHAR_MAX + 1.  */
enum
{
  AUTHOR_OPTION = CHAR_MAX + 1,
  BLOCK_SIZE_OPTION,
  COLOR_OPTION,
  DEREFERENCE_COMMAND_LINE_SYMLINK_TO_DIR_OPTION,
  FILE_TYPE_INDICATOR_OPTION,
  FORMAT_OPTION,
  FULL_TIME_OPTION,
  GROUP_DIRECTORIES_FIRST_OPTION,
  HIDE_OPTION,
  HYPERLINK_OPTION,
  INDICATOR_STYLE_OPTION,
  QUOTING_STYLE_OPTION,
  SHOW_CONTROL_CHARS_OPTION,
  SI_OPTION,
  SORT_OPTION,
  TIME_OPTION,
  TIME_STYLE_OPTION,
  ZERO_OPTION,
};

static struct option const long_options[] =
{
  {"all", no_argument, nullptr, 'a'},
  {"escape", no_argument, nullptr, 'b'},
  {"directory", no_argument, nullptr, 'd'},
  {"dired", no_argument, nullptr, 'D'},
  {"full-time", no_argument, nullptr, FULL_TIME_OPTION},
  {"group-directories-first", no_argument, nullptr,
   GROUP_DIRECTORIES_FIRST_OPTION},
  {"human-readable", no_argument, nullptr, 'h'},
  {"inode", no_argument, nullptr, 'i'},
  {"kibibytes", no_argument, nullptr, 'k'},
  {"numeric-uid-gid", no_argument, nullptr, 'n'},
  {"no-group", no_argument, nullptr, 'G'},
  {"hide-control-chars", no_argument, nullptr, 'q'},
  {"reverse", no_argument, nullptr, 'r'},
  {"size", no_argument, nullptr, 's'},
  {"width", required_argument, nullptr, 'w'},
  {"almost-all", no_argument, nullptr, 'A'},
  {"ignore-backups", no_argument, nullptr, 'B'},
  {"classify", optional_argument, nullptr, 'F'},
  {"file-type", no_argument, nullptr, FILE_TYPE_INDICATOR_OPTION},
  {"si", no_argument, nullptr, SI_OPTION},
  {"dereference-command-line", no_argument, nullptr, 'H'},
  {"dereference-command-line-symlink-to-dir", no_argument, nullptr,
   DEREFERENCE_COMMAND_LINE_SYMLINK_TO_DIR_OPTION},
  {"hide", required_argument, nullptr, HIDE_OPTION},
  {"ignore", required_argument, nullptr, 'I'},
  {"indicator-style", required_argument, nullptr, INDICATOR_STYLE_OPTION},
  {"dereference", no_argument, nullptr, 'L'},
  {"literal", no_argument, nullptr, 'N'},
  {"quote-name", no_argument, nullptr, 'Q'},
  {"quoting-style", required_argument, nullptr, QUOTING_STYLE_OPTION},
  {"recursive", no_argument, nullptr, 'R'},
  {"format", required_argument, nullptr, FORMAT_OPTION},
  {"show-control-chars", no_argument, nullptr, SHOW_CONTROL_CHARS_OPTION},
  {"sort", required_argument, nullptr, SORT_OPTION},
  {"tabsize", required_argument, nullptr, 'T'},
  {"time", required_argument, nullptr, TIME_OPTION},
  {"time-style", required_argument, nullptr, TIME_STYLE_OPTION},
  {"zero", no_argument, nullptr, ZERO_OPTION},
  {"color", optional_argument, nullptr, COLOR_OPTION},
  {"hyperlink", optional_argument, nullptr, HYPERLINK_OPTION},
  {"block-size", required_argument, nullptr, BLOCK_SIZE_OPTION},
  {"context", no_argument, 0, 'Z'},
  {"author", no_argument, nullptr, AUTHOR_OPTION},
  {GETOPT_HELP_OPTION_DECL},
  {GETOPT_VERSION_OPTION_DECL},
  {nullptr, 0, nullptr, 0}
};

static char const *const format_args[] =
{
  "verbose", "long", "commas", "horizontal", "across",
  "vertical", "single-column", nullptr
};
static enum format const format_types[] =
{
  long_format, long_format, with_commas, horizontal, horizontal,
  many_per_line, one_per_line
};
ARGMATCH_VERIFY (format_args, format_types);

static char const *const sort_args[] =
{
  "none", "size", "time", "version", "extension",
  "name", "width", nullptr
};
static enum sort_type const sort_types[] =
{
  sort_none, sort_size, sort_time, sort_version, sort_extension,
  sort_name, sort_width
};
ARGMATCH_VERIFY (sort_args, sort_types);

static char const *const time_args[] =
{
  "atime", "access", "use",
  "ctime", "status",
  "mtime", "modification",
  "birth", "creation",
  nullptr
};
static enum time_type const time_types[] =
{
  time_atime, time_atime, time_atime,
  time_ctime, time_ctime,
  time_mtime, time_mtime,
  time_btime, time_btime,
};
ARGMATCH_VERIFY (time_args, time_types);

static char const *const when_args[] =
{
  /* force and none are for compatibility with another color-ls version */
  "always", "yes", "force",
  "never", "no", "none",
  "auto", "tty", "if-tty", nullptr
};
static enum when_type const when_types[] =
{
  when_always, when_always, when_always,
  when_never, when_never, when_never,
  when_if_tty, when_if_tty, when_if_tty
};
ARGMATCH_VERIFY (when_args, when_types);

/* Information about filling a column.  */
struct column_info
{
  bool valid_len;
  size_t line_len;
  size_t *col_arr;
};

/* Array with information about column fullness.  */
static struct column_info *column_info;

/* Maximum number of columns ever possible for this display.  */
static size_t max_idx;

/* The minimum width of a column is 3: 1 character for the name and 2
   for the separating white space.  */
enum { MIN_COLUMN_WIDTH = 3 };


/* This zero-based index is for the --dired option.  It is incremented
   for each byte of output generated by this program so that the beginning
   and ending indices (in that output) of every file name can be recorded
   and later output themselves.  */
static off_t dired_pos;

static int
dired_outbyte (char c)
{
  if (putchar(c) == EOF)
    {
      return EOF;
    }
  dired_pos++;
  return 0;
}

/* Output the buffer S, of length S_LEN, and increment DIRED_POS by S_LEN.  */
static void
dired_outbuf (char const *s, size_t s_len)
{
  dired_pos += s_len;

  size_t items_written = fwrite(s, 1, s_len, stdout);

  if (items_written != s_len)
    {
      fprintf(stderr, "dired_outbuf: Failed to write all %zu bytes to stdout.\n", s_len);
      perror("fwrite error");
      exit(EXIT_FAILURE);
    }
}

/* Output the string S, and increment DIRED_POS by its length.  */
static void
dired_outstring (char const *s)
{
  if (s == NULL)
    {
      /* Handle NULL input gracefully by treating it as an empty string.
         This prevents a NULL pointer dereference with strlen() and
         ensures dired_outbuf() receives valid arguments. */
      dired_outbuf ("", 0);
      return;
    }
  dired_outbuf (s, strlen (s));
}

static void
dired_indent (int is_dired_mode_active)
{
  if (is_dired_mode_active)
    dired_outstring ("  ");
}

/* With --dired, store pairs of beginning and ending indices of file names.  */
static struct obstack dired_obstack;

/* With --dired, store pairs of beginning and ending indices of any
   directory names that appear as headers (just before 'total' line)
   for lists of directory entries.  Such directory names are seen when
   listing hierarchies using -R and when a directory is listed with at
   least one other command line argument.  */
static struct obstack subdired_obstack;

/* Save the current index on the specified obstack, OBS.  */
#include <stdbool.h>
#include <stddef.h>

static void
push_current_dired_pos (struct obstack *obs, bool dired_active, const void *pos_data, size_t pos_size)
{
  if (obs == NULL)
    {
      return;
    }

  if (dired_active)
    {
      if (pos_data == NULL)
        {
          return;
        }
      if (pos_size == 0)
        {
          return;
        }

      obstack_grow (obs, (void *)pos_data, pos_size);
    }
}

/* With -R, this stack is used to help detect directory cycles.
   The device/inode pairs on this stack mirror the pairs in the
   active_dir_set hash table.  */
static struct obstack dev_ino_obstack;

/* Push a pair onto the device/inode stack.  */
static void
dev_ino_push (dev_t dev, ino_t ino)
{
  struct dev_ino *di;
  di = (struct dev_ino *) obstack_alloc (&dev_ino_obstack, sizeof(struct dev_ino));
  di->st_dev = dev;
  di->st_ino = ino;
}

/* Pop a dev/ino struct off the global dev_ino_obstack
   and return that struct.  */
static struct dev_ino
dev_ino_pop (void)
{
  struct dev_ino *popped_dev_ino_ptr;
  const int dev_ino_size = sizeof(struct dev_ino);

  affirm (dev_ino_size <= obstack_object_size (&dev_ino_obstack));

  obstack_blank_fast (&dev_ino_obstack, -dev_ino_size);

  popped_dev_ino_ptr = (struct dev_ino *)obstack_next_free (&dev_ino_obstack);

  return *popped_dev_ino_ptr;
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>

/* Assume struct dev_ino is defined in an existing header, e.g.:
 * typedef struct {
 *   dev_t st_dev;
 *   ino_t st_ino;
 * } struct dev_ino;
 */

/*
 * Helper function for assertion failures.
 * This function provides detailed error information (file, line, message,
 * and errno details if applicable) and then terminates the program.
 * It replaces the generic 'assure' macro with a more robust and informative
 * error handling mechanism, improving reliability and maintainability.
 * Made static to limit its scope to this compilation unit.
 */
static void
_assert_fail_and_exit (char const *file, int line, char const *message, char const *context)
{
  fprintf (stderr, "FATAL: %s:%d: Assertion failed: %s", file, line, message);
  if (context && *context)
    fprintf (stderr, " (Context: '%s')", context);
  if (errno != 0)
    fprintf (stderr, ": %s", strerror (errno));
  fprintf (stderr, "\n");
  exit (EXIT_FAILURE);
}

static void
assert_matching_dev_ino (char const *name, struct dev_ino di)
{
  struct stat sb;

  /*
   * Check the return value of stat explicitly.
   * If stat fails, 'sb' is uninitialized. Accessing its members (sb.st_dev, sb.st_ino)
   * would lead to undefined behavior. This explicit check prevents that,
   * improving security and reliability.
   * Replaces 'assure(0 <= stat(...))' with a more detailed error report.
   */
  if (stat (name, &sb) != 0)
    {
      _assert_fail_and_exit (__FILE__, __LINE__, "Failed to stat file", name);
    }

  /*
   * Verify device numbers.
   * Replaces 'assure(sb.st_dev == di.st_dev)' with an explicit check
   * and a clear error message.
   */
  if (sb.st_dev != di.st_dev)
    {
      _assert_fail_and_exit (__FILE__, __LINE__, "Device numbers do not match", name);
    }

  /*
   * Verify inode numbers.
   * Replaces 'assure(sb.st_ino == di.st_ino)' with an explicit check
   * and a clear error message.
   */
  if (sb.st_ino != di.st_ino)
    {
      _assert_fail_and_exit (__FILE__, __LINE__, "Inode numbers do not match", name);
    }
}

static char eolbyte = '\n';

/* Write to standard output PREFIX, followed by the quoting style and
   a space-separated list of the integers stored in OS all on one line.  */

static int
dired_dump_obstack (char const *prefix, struct obstack *os)
{
  size_t n_pos;

  n_pos = obstack_object_size (os) / sizeof (off_t);

  if (n_pos > 0)
    {
      off_t *pos = obstack_finish (os);

      if (fputs (prefix, stdout) == EOF)
        {
          return EOF;
        }

      for (size_t i = 0; i < n_pos; i++)
        {
          intmax_t p = pos[i];
          if (printf (" %jd", p) < 0)
            {
              return EOF;
            }
        }

      if (putchar ('\n') == EOF)
        {
          return EOF;
        }
    }

  return 0;
}

/* Return the platform birthtime member of the stat structure,
   or fallback to the mtime member, which we have populated
   from the statx structure or reset to an invalid timestamp
   where birth time is not supported.  */
static struct timespec
get_stat_btime (struct stat const *st)
{
#if HAVE_STATX && defined STATX_INO
  return get_stat_mtime (st);
#else
  return get_stat_birthtime (st);
#endif
}

#if HAVE_STATX && defined STATX_INO
ATTRIBUTE_PURE
static unsigned int
time_type_to_statx (void)
{
  switch (time_type)
    {
    case time_ctime:
      return STATX_CTIME;
    case time_mtime:
      return STATX_MTIME;
    case time_atime:
      return STATX_ATIME;
    case time_btime:
      return STATX_BTIME;
    case time_numtypes: default:
      unreachable ();
    }
    return 0;
}

ATTRIBUTE_PURE
static unsigned int
calc_req_mask (void)
{
  unsigned int mask = STATX_MODE;

  if (print_inode)
    mask |= STATX_INO;

  if (print_block_size)
    mask |= STATX_BLOCKS;

  if (format == long_format) {
    mask |= STATX_NLINK | STATX_SIZE | time_type_to_statx ();
    if (print_owner || print_author)
      mask |= STATX_UID;
    if (print_group)
      mask |= STATX_GID;
  }

  switch (sort_type)
    {
    case sort_none:
    case sort_name:
    case sort_version:
    case sort_extension:
    case sort_width:
      break;
    case sort_time:
      mask |= time_type_to_statx ();
      break;
    case sort_size:
      mask |= STATX_SIZE;
      break;
    case sort_numtypes: default:
      unreachable ();
    }

  return mask;
}

static int
do_statx (int fd, char const *name, struct stat *st, int flags,
          unsigned int mask)
{
  struct statx stx;
  bool want_btime = mask & STATX_BTIME;
  int ret = statx (fd, name, flags | AT_NO_AUTOMOUNT, mask, &stx);
  if (ret >= 0)
    {
      statx_to_stat (&stx, st);
      /* Since we only need one timestamp type,
         store birth time in st_mtim.  */
      if (want_btime)
        {
          if (stx.stx_mask & STATX_BTIME)
            st->st_mtim = statx_timestamp_to_timespec (stx.stx_btime);
          else
            st->st_mtim.tv_sec = st->st_mtim.tv_nsec = -1;
        }
    }

  return ret;
}

static int
do_stat (char const *name, struct stat *st)
{
  return do_statx (AT_FDCWD, name, st, 0, calc_req_mask ());
}

static int
do_lstat (char const *name, struct stat *st)
{
  return do_statx (AT_FDCWD, name, st, AT_SYMLINK_NOFOLLOW, calc_req_mask ());
}

static int
stat_for_mode (char const *name, struct stat *st)
{
  return do_statx (AT_FDCWD, name, st, 0, STATX_MODE);
}

/* dev+ino should be static, so no need to sync with backing store */
static int
stat_for_ino (char const *name, struct stat *st)
{
  return do_statx (AT_FDCWD, name, st, 0, STATX_INO);
}

static int
fstat_for_ino (int fd, struct stat *st)
{
  return do_statx (fd, "", st, AT_EMPTY_PATH, STATX_INO);
}
#else
static int
do_stat (char const * restrict name, struct stat * restrict st)
{
  return stat (name, st);
}

#include <sys/stat.h> // For lstat, struct stat
#include <stdio.h>    // For fprintf, stderr
#include <errno.h>    // For errno
#include <string.h>   // For strerror

static int
do_lstat (char const *name, struct stat *st)
{
  if (name == NULL) {
    errno = EFAULT;
    fprintf(stderr, "Error: do_lstat received NULL 'name' argument.\n");
    return -1;
  }
  if (st == NULL) {
    errno = EFAULT;
    fprintf(stderr, "Error: do_lstat received NULL 'st' argument.\n");
    return -1;
  }

  int result = lstat (name, st);
  if (result == -1)
    {
      fprintf(stderr, "Error calling lstat on '%s': %s\n", name, strerror(errno));
    }
  return result;
}

#include <sys/stat.h> // For struct stat and stat()
#include <errno.h>    // For errno and EFAULT

static int
stat_for_mode (char const *name, struct stat *st)
{
  if (name == NULL || st == NULL)
    {
      errno = EFAULT;
      return -1;
    }

  return stat (name, st);
}

static int
stat_for_ino (char const *name, struct stat *st)
{
  if (name == NULL || st == NULL)
    {
      errno = EFAULT;
      return -1;
    }

  return stat (name, st);
}

static int
fstat_for_ino (int fd, struct stat *st)
{
  if (st == NULL) {
    errno = EFAULT;
    return -1;
  }
  return fstat (fd, st);
}
#endif

/* Return the address of the first plain %b spec in FMT, or nullptr if
   there is no such spec.  %5b etc. do not match, so that user
   widths/flags are honored.  */

ATTRIBUTE_PURE
static char const *
first_percent_b (char const *fmt)
{
  if (fmt == nullptr)
    return nullptr;

  for (; *fmt; fmt++)
    if (fmt[0] == '%')
      {
        if (fmt[1] == '\0')
          // Reached end of string with a lone '%'. No '%b' or '%%' possible.
          // The loop will terminate naturally after this iteration.
          break;

        switch (fmt[1])
          {
          case 'b': return fmt;
          case '%': fmt++; break;
          // For any other sequence like '%d', '%s', etc., the loop's fmt++
          // will correctly advance past the first '%' without special handling here.
          }
      }
  return nullptr;
}

static char RFC3986[256];
static void
file_escape_init (void)
{
  const unsigned char RFC3986_UNRESERVED_FLAG = 1;

  for (int i = 0; i < 256; i++)
    {
      if (c_isalnum (i) || i == '~' || i == '-' || i == '.' || i == '_')
        {
          RFC3986[i] |= RFC3986_UNRESERVED_FLAG;
        }
    }
}

enum { MBSWIDTH_FLAGS = MBSW_REJECT_INVALID | MBSW_REJECT_UNPRINTABLE };

/* Read the abbreviated month names from the locale, to align them
   and to determine the max width of the field and to truncate names
   greater than our max allowed.
   Note even though this handles multibyte locales correctly
   it's not restricted to them as single byte locales can have
   variable width abbreviated months and also precomputing/caching
   the names was seen to increase the performance of ls significantly.  */

/* abformat[RECENT][MON] is the format to use for timestamps with
   recentness RECENT and month MON.  */
enum { ABFORMAT_SIZE = 128 };
static char abformat[2][12][ABFORMAT_SIZE];
/* True if precomputed formats should be used.  This can be false if
   nl_langinfo fails, if a format or month abbreviation is unusually
   long, or if a month abbreviation contains '%'.  */
static bool use_abformat;

/* Store into ABMON the abbreviated month names, suitably aligned.
   Return true if successful.  */

static bool
abmon_init (char abmon[12][ABFORMAT_SIZE])
{
#ifndef HAVE_NL_LANGINFO
  return false;
#else
  int max_mon_width = 0;
  int mon_width[12];
  int mon_len[12];
  char const *raw_abbrs[12];

  for (int i = 0; i < 12; i++)
    {
      char const *abbr = nl_langinfo (ABMON_1 + i);
      if (abbr == NULL)
        {
          return false;
        }
      raw_abbrs[i] = abbr;

      mon_len[i] = strnlen (abbr, ABFORMAT_SIZE);
      if (mon_len[i] >= ABFORMAT_SIZE)
        {
          return false;
        }

      if (strchr (abbr, '%') != NULL)
        {
          return false;
        }

      int snp_res = snprintf(abmon[i], ABFORMAT_SIZE, "%s", abbr);
      if (snp_res < 0 || snp_res >= ABFORMAT_SIZE)
        {
          return false;
        }

      mon_width[i] = mbswidth (abmon[i], MBSWIDTH_FLAGS);
      if (mon_width[i] < 0)
        {
          return false;
        }

      max_mon_width = MAX (max_mon_width, mon_width[i]);
    }

  static char const padding_spaces[] =
    "                                                                " // 64 spaces
    "                                                                " // 128 spaces
    "                                                                " // 192 spaces
    "                                                                " // 256 spaces
    "                                                                " // 320 spaces
    "                                                                " // 384 spaces
    "                                                                " // 448 spaces
    "                                                                " // 512 spaces
    "                                                                " // 576 spaces
    "                                                                " // 640 spaces
    "                                                                " // 704 spaces
    "                                                                " // 768 spaces
    "                                                                " // 832 spaces
    "                                                                " // 896 spaces
    "                                                                " // 960 spaces
    "                                                                " // 1024 spaces
    "                                                                " // 1088 spaces
    "                                                                " // 1152 spaces
    "                                                                " // 1216 spaces
    "                                                                " // 1280 spaces
    "                                                                " // 1344 spaces
    "                                                                " // 1408 spaces
    "                                                                " // 1472 spaces
    "                                                                " // 1536 spaces
    "                                                                " // 1600 spaces
    "                                                                " // 1664 spaces
    "                                                                " // 1728 spaces
    "                                                                " // 1792 spaces
    "                                                                " // 1856 spaces
    "                                                                " // 1920 spaces
    "                                                                " // 1984 spaces
    "                                                                " // 2048 spaces
    "                                                                " // 2112 spaces
    "                                                                " // 2176 spaces
    "                                                                " // 2240 spaces
    "                                                                " // 2304 spaces
    "                                                                " // 2368 spaces
    "                                                                " // 2432 spaces
    "                                                                " // 2496 spaces
    "                                                                " // 2560 spaces
    "                                                                " // 2624 spaces
    "                                                                " // 2688 spaces
    "                                                                " // 2752 spaces
    "                                                                " // 2816 spaces
    "                                                                " // 2880 spaces
    "                                                                " // 2944 spaces
    "                                                                " // 3008 spaces
    "                                                                " // 3072 spaces
    "                                                                " // 3136 spaces
    "                                                                " // 3200 spaces
    "                                                                " // 3264 spaces
    "                                                                " // 3328 spaces
    "                                                                " // 3392 spaces
    "                                                                " // 3456 spaces
    "                                                                " // 3520 spaces
    "                                                                " // 3584 spaces
    "                                                                " // 3648 spaces
    "                                                                " // 3712 spaces
    "                                                                " // 3776 spaces
    "                                                                " // 3840 spaces
    "                                                                " // 3904 spaces
    "                                                                " // 3968 spaces
    "                                                                "; // 4032 spaces

  for (int i = 0; i < 12; i++)
    {
      int fill = max_mon_width - mon_width[i];
      char const *original_abbr = raw_abbrs[i];
      int current_orig_len = mon_len[i];

      if (current_orig_len + fill + 1 > ABFORMAT_SIZE)
        {
          return false;
        }

      bool align_left = !c_isdigit (original_abbr[0]);

      int snp_res;
      if (align_left)
        {
          snp_res = snprintf(abmon[i], ABFORMAT_SIZE, "%s%.*s",
                             original_abbr,
                             fill,
                             padding_spaces);
        }
      else
        {
          snp_res = snprintf(abmon[i], ABFORMAT_SIZE, "%.*s%s",
                             fill,
                             padding_spaces,
                             original_abbr);
        }

      if (snp_res < 0 || snp_res >= ABFORMAT_SIZE)
        {
          return false;
        }
    }

  return true;
#endif
}

/* Initialize ABFORMAT and USE_ABFORMAT.  */

static void
abformat_init (void)
{
  char const *pb[2];
  bool any_percent_b_found = false;

  for (int recent_idx = 0; recent_idx < 2; ++recent_idx)
    {
      pb[recent_idx] = first_percent_b (long_time_format[recent_idx]);
      if (pb[recent_idx] != NULL)
        {
          any_percent_b_found = true;
        }
    }

  if (!any_percent_b_found)
    {
      return;
    }

  char abmon[12][ABFORMAT_SIZE];
  if (! abmon_init (abmon))
    {
      return;
    }

  for (int recent_idx = 0; recent_idx < 2; ++recent_idx)
    {
      char const *fmt = long_time_format[recent_idx];

      for (int month_idx = 0; month_idx < 12; ++month_idx)
        {
          char *dest_nfmt = abformat[recent_idx][month_idx];
          int nbytes;

          if (pb[recent_idx] == NULL)
            {
              nbytes = snprintf (dest_nfmt, ABFORMAT_SIZE, "%s", fmt);
            }
          else
            {
              ptrdiff_t prefix_len_diff = pb[recent_idx] - fmt;

              if (prefix_len_diff < 0 || (size_t)prefix_len_diff >= ABFORMAT_SIZE)
                {
                  return;
                }

              int prefix_len = (int)prefix_len_diff;

              nbytes = snprintf (dest_nfmt, ABFORMAT_SIZE, "%.*s%s%s",
                                 prefix_len, fmt, abmon[month_idx], pb[recent_idx] + 2);
            }

          if (nbytes < 0 || (size_t)nbytes >= ABFORMAT_SIZE)
            {
              return;
            }
        }
    }

  use_abformat = true;
}

static size_t
dev_ino_hash (void const *x, size_t table_size)
{
  if (table_size == 0)
    {
      return 0;
    }

  if (x == NULL)
    {
      return 0;
    }

  struct dev_ino const *p = (struct dev_ino const *)x;
  return (uintmax_t) p->st_ino % table_size;
}

static bool
dev_ino_compare (void const *x, void const *y)
{
  if (!x || !y) {
    return false;
  }

  struct dev_ino const *a = x;
  struct dev_ino const *b = y;

  return a->st_dev == b->st_dev && a->st_ino == b->st_ino;
}

static inline void
dev_ino_free (void *x)
{
  free (x);
}

/* Add the device/inode pair (P->st_dev/P->st_ino) to the set of
   active directories.  Return true if there is already a matching
   entry in the table.  */

static bool
visit_dir (dev_t dev, ino_t ino)
{
  struct dev_ino *new_entry_candidate;
  struct dev_ino *returned_entry;

  new_entry_candidate = xmalloc (sizeof *new_entry_candidate);
  new_entry_candidate->st_ino = ino;
  new_entry_candidate->st_dev = dev;

  returned_entry = hash_insert (active_dir_set, new_entry_candidate);

  if (returned_entry == nullptr)
    {
      xalloc_die ();
    }

  if (returned_entry == new_entry_candidate)
    {
      return false;
    }
  else
    {
      free (new_entry_candidate);
      return true;
    }
}

static void
free_pending_ent (struct pending *p)
{
  if (p == NULL) {
    return;
  }

  free(p->name);
  free(p->realname);
  free(p);
}

static bool
is_colored (enum indicator_no type)
{
  size_t len = color_indicator[type].len;
  char const *s = color_indicator[type].string;

  if (len == 0)
    {
      return false;
    }

  if (s == NULL)
    {
      return false;
    }

  if (len > 2)
    {
      return true;
    }

  return (s[0] != '0') || (s[len - 1] != '0');
}

static void
restore_default_color (void)
{
  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (&color_indicator[C_RIGHT]);
}

static void
set_normal_color (void)
{
  if (!print_with_color || !is_colored (C_NORM))
    {
      return;
    }

  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (&color_indicator[C_NORM]);
  put_indicator (&color_indicator[C_RIGHT]);
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void
sighandler (int sig)
{
  if (!interrupt_signal)
    interrupt_signal = sig;
}

/* A SIGTSTP was received; arrange for the program to suspend itself.  */

static void
stophandler (int sig)
{
  (void)sig;
  if (! interrupt_signal)
    stop_signal_count++;
}

/* Process any pending signals.  If signals are caught, this function
   should be called periodically.  Ideally there should never be an
   unbounded amount of time when signals are not being processed.
   Signal handling can restore the default colors, so callers must
   immediately change colors after invoking this function.  */

static void
process_signals (void)
{
  while (interrupt_signal || stop_signal_count)
    {
      int current_signal_to_handle;
      int current_stop_count;
      sigset_t old_signal_mask;

      if (used_color)
        restore_default_color ();
      fflush (stdout);

      (void) sigprocmask (SIG_BLOCK, &caught_signals, &old_signal_mask);

      current_signal_to_handle = interrupt_signal;
      current_stop_count = stop_signal_count;

      if (current_stop_count > 0)
        {
          stop_signal_count = current_stop_count - 1;
          current_signal_to_handle = SIGSTOP;
        }
      else
        {
          signal (current_signal_to_handle, SIG_DFL);
        }

      raise (current_signal_to_handle);
      (void) sigprocmask (SIG_SETMASK, &old_signal_mask, NULL);
    }
}

/* Setup signal handlers if INIT is true,
   otherwise restore to the default.  */

#ifdef SA_NOCLDSTOP
static sigset_t caught_signals;
#endif

static void
signal_setup (bool init)
{
  static int const sig[] =
    {
      SIGTSTP,
      SIGALRM, SIGHUP, SIGINT, SIGPIPE, SIGQUIT, SIGTERM,
#ifdef SIGPOLL
      SIGPOLL,
#endif
#ifdef SIGPROF
      SIGPROF,
#endif
#ifdef SIGVTALRM
      SIGVTALRM,
#endif
#ifdef SIGXCPU
      SIGXCPU,
#endif
#ifdef SIGXFSZ
      SIGXFSZ,
#endif
    };
  enum { nsigs = sizeof(sig) / sizeof(sig[0]) };

#if ! SA_NOCLDSTOP
  static bool caught_sig[nsigs];
#endif

  if (init)
    {
#ifdef SA_NOCLDSTOP
      struct sigaction act;
      sigset_t current_signals_to_handle;

      if (sigemptyset(&current_signals_to_handle) == -1) {
          return;
      }

      for (int j = 0; j < nsigs; j++)
        {
          struct sigaction old_act;
          if (sigaction(sig[j], NULL, &old_act) == -1) {
              continue;
          }
          if (old_act.sa_handler != SIG_IGN)
            {
              if (sigaddset(&current_signals_to_handle, sig[j]) == -1) {
                  continue;
              }
            }
        }

      caught_signals = current_signals_to_handle;

      if (sigemptyset(&act.sa_mask) == -1) {
          return;
      }
      act.sa_mask = caught_signals;
      act.sa_flags = SA_RESTART;

      for (int j = 0; j < nsigs; j++)
        {
          if (sigismember(&current_signals_to_handle, sig[j]))
            {
              act.sa_handler = (sig[j] == SIGTSTP) ? stophandler : sighandler;
              if (sigaction(sig[j], &act, NULL) == -1) {
                  continue;
              }
            }
        }
#else
      for (int j = 0; j < nsigs; j++)
        {
          void (*old_handler)(int);
          old_handler = signal(sig[j], SIG_IGN);
          if (old_handler == SIG_ERR) {
              continue;
          }

          if (old_handler != SIG_IGN)
            {
              caught_sig[j] = true;
              void (*new_handler)(int) = (sig[j] == SIGTSTP) ? stophandler : sighandler;
              if (signal(sig[j], new_handler) == SIG_ERR) {
                  caught_sig[j] = false;
                  continue;
              }
              if (siginterrupt(sig[j], 0) == -1) {
                  caught_sig[j] = false;
                  continue;
              }
            }
          else
            {
              caught_sig[j] = false;
            }
        }
#endif
    }
  else
    {
      for (int j = 0; j < nsigs; j++)
        {
#ifdef SA_NOCLDSTOP
          if (sigismember(&caught_signals, sig[j]))
#else
          if (caught_sig[j])
#endif
            {
              if (signal(sig[j], SIG_DFL) == SIG_ERR) {
                  continue;
              }
            }
        }
    }
}

#include <stdio.h> // Required for fprintf, stderr

#define SIGNAL_HANDLING_ENABLED true // Use a named constant for clarity

static void
signal_init (void)
{
  // Improve reliability by checking the return value of signal_setup.
  // It is assumed that signal_setup returns 0 on success and a non-zero value on failure.
  if (signal_setup(SIGNAL_HANDLING_ENABLED) != 0) {
    // Log an error to stderr. As signal_init is void, it cannot return an error status
    // to its caller. Logging provides critical diagnostic information without
    // altering the external interface of signal_init.
    fprintf(stderr, "ERROR: Failed to initialize signal handling. Application might not respond correctly to signals.\n");
  }
}

static void
signal_restore (void)
{
  signal_setup (0);
}

static void setup_program_environment(int argc, char **argv);
static void configure_color_and_tabsize(void);
static void configure_symlink_and_dereference_modes(void);
static void initialize_recursive_and_timezone(void);
static void calculate_formatting_requirements(void);
static void initialize_dired_and_hyperlink_features(void);
static void initialize_cwd_file_buffer(void);
static void process_command_line_arguments(int start_idx, int argc, char **argv);
static void prepare_initial_output(int n_files_arg);
static void process_pending_directories_queue(void);
static void perform_final_cleanup(void);

#define INITIAL_CWD_FILE_ALLOC 100
#define COLOR_LEFT_ESC_LEN 2
#define COLOR_LEFT_ESC_STR "\033["
#define COLOR_RIGHT_ESC_CHAR 'm'
#define COLOR_RIGHT_ESC_LEN 1

int
main (int argc, char **argv)
{
  int i;
  int n_files;

  setup_program_environment(argc, argv);

  i = decode_switches (argc, argv);

  configure_color_and_tabsize();
  configure_symlink_and_dereference_modes();
  initialize_recursive_and_timezone();
  calculate_formatting_requirements();
  initialize_dired_and_hyperlink_features();
  initialize_cwd_file_buffer();

  clear_files ();

  n_files = argc - i;
  process_command_line_arguments(i, argc, argv);

  if (cwd_n_used)
    {
      sort_files ();
      if (!immediate_dirs)
        extract_dirs_from_files (nullptr, true);
    }

  prepare_initial_output(n_files);

  process_pending_directories_queue();

  perform_final_cleanup();

  return exit_status;
}

static void
setup_program_environment(int argc, char **argv)
{
  initialize_main (&argc, &argv);
  set_program_name (argv[0]);
  setlocale (LC_ALL, "");
  bindtextdomain (PACKAGE, LOCALEDIR);
  textdomain (PACKAGE);

  initialize_exit_failure (LS_FAILURE);
  atexit (close_stdout);

  static_assert (ARRAY_CARDINALITY (color_indicator)
                 == ARRAY_CARDINALITY (indicator_name));

  exit_status = EXIT_SUCCESS;
  print_dir_name = true;
  pending_dirs = nullptr;

  current_time.tv_sec = TYPE_MINIMUM (time_t);
  current_time.tv_nsec = -1;
}

static void
configure_color_and_tabsize(void)
{
  if (print_with_color)
    parse_ls_color ();

  if (print_with_color)
    {
      tabsize = 0;
    }
}

static void
configure_symlink_and_dereference_modes(void)
{
  if (directories_first)
    check_symlink_mode = true;
  else if (print_with_color)
    {
      if (is_colored (C_ORPHAN)
          || (is_colored (C_EXEC) && color_symlink_as_referent)
          || (is_colored (C_MISSING) && format == long_format))
        check_symlink_mode = true;
    }

  if (dereference == DEREF_UNDEFINED)
    dereference = ((immediate_dirs
                    || indicator_style == classify
                    || format == long_format)
                   ? DEREF_NEVER
                   : DEREF_COMMAND_LINE_SYMLINK_TO_DIR);
}

static void
initialize_recursive_and_timezone(void)
{
  if (recursive)
    {
      active_dir_set = hash_initialize (INITIAL_TABLE_SIZE, nullptr,
                                        dev_ino_hash,
                                        dev_ino_compare,
                                        dev_ino_free);
      if (active_dir_set == nullptr)
        xalloc_die ();

      obstack_init (&dev_ino_obstack);
    }

  localtz = tzalloc (getenv ("TZ"));
}

static void
calculate_formatting_requirements(void)
{
  format_needs_stat = ((sort_type == sort_time) || (sort_type == sort_size)
                       || (format == long_format)
                       || print_block_size || print_hyperlink || print_scontext);
  format_needs_type = ((! format_needs_stat)
                       && (recursive || print_with_color || print_scontext
                           || directories_first
                           || (indicator_style != none)));
  format_needs_capability = print_with_color && is_colored (C_CAP);
}

static void
initialize_dired_and_hyperlink_features(void)
{
  if (dired)
    {
      obstack_init (&dired_obstack);
      obstack_init (&subdired_obstack);
    }

  if (print_hyperlink)
    {
      file_escape_init ();
      hostname = xgethostname ();
      if (! hostname)
        hostname = "";
    }
}

static void
initialize_cwd_file_buffer(void)
{
  cwd_n_alloc = INITIAL_CWD_FILE_ALLOC;
  cwd_file = xmalloc (cwd_n_alloc * sizeof *cwd_file);
  cwd_n_used = 0;
}

static void
process_command_line_arguments(int start_idx, int argc, char **argv)
{
  int current_arg_idx = start_idx;
  int n_files_arg = argc - current_arg_idx;

  if (n_files_arg <= 0)
    {
      if (immediate_dirs)
        gobble_file (".", directory, NOT_AN_INODE_NUMBER, true, nullptr);
      else
        queue_directory (".", nullptr, true);
    }
  else
    {
      do
        gobble_file (argv[current_arg_idx++], unknown, NOT_AN_INODE_NUMBER, true, nullptr);
      while (current_arg_idx < argc);
    }
}

static void
prepare_initial_output(int n_files_arg)
{
  if (cwd_n_used)
    {
      print_current_files ();
      if (pending_dirs)
        dired_outbyte ('\n');
    }
  else if (n_files_arg <= 1 && pending_dirs && pending_dirs->next == 0)
    print_dir_name = false;
}

static void
process_pending_directories_queue(void)
{
  struct pending *thispend;

  while (pending_dirs)
    {
      thispend = pending_dirs;
      pending_dirs = pending_dirs->next;

      if (LOOP_DETECT)
        {
          if (thispend->name == nullptr)
            {
              struct dev_ino di = dev_ino_pop ();
              struct dev_ino *found = hash_remove (active_dir_set, &di);
              if (false)
                assert_matching_dev_ino (thispend->realname, di);
              affirm (found);
              dev_ino_free (found);
              free_pending_ent (thispend);
              continue;
            }
        }

      print_dir (thispend->name, thispend->realname,
                 thispend->command_line_arg);

      free_pending_ent (thispend);
      print_dir_name = true;
    }
}

static void
perform_final_cleanup(void)
{
  if (print_with_color && used_color)
    {
      int j;

      if (!(color_indicator[C_LEFT].len == COLOR_LEFT_ESC_LEN
            && memcmp (color_indicator[C_LEFT].string, COLOR_LEFT_ESC_STR, COLOR_LEFT_ESC_LEN) == 0
            && color_indicator[C_RIGHT].len == COLOR_RIGHT_ESC_LEN
            && color_indicator[C_RIGHT].string[0] == COLOR_RIGHT_ESC_CHAR))
        restore_default_color ();

      fflush (stdout);

      signal_restore ();

      for (j = stop_signal_count; j; j--)
        raise (SIGSTOP);
      j = interrupt_signal;
      if (j)
        raise (j);
    }

  if (dired)
    {
      dired_dump_obstack ("//DIRED//", &dired_obstack);
      dired_dump_obstack ("//SUBDIRED//", &subdired_obstack);
      printf ("//DIRED-OPTIONS// --quoting-style=%s\n",
              quoting_style_args[get_quoting_style (filename_quoting_options)]);
    }

  if (LOOP_DETECT)
    {
      assure (hash_get_n_entries (active_dir_set) == 0);
      hash_free (active_dir_set);
    }
}

/* Return the line length indicated by the value given by SPEC, or -1
   if unsuccessful.  0 means no limit on line length.  */

static ptrdiff_t
decode_line_length (char const *spec)
{
  uintmax_t val;
  LongIntResult result = xstrtoumax (spec, nullptr, 0, &val, "");

  switch (result)
    {
    case LONGINT_OK:
      if (val <= MIN (PTRDIFF_MAX, SIZE_MAX))
        return val;
      [[fallthrough]];

    case LONGINT_OVERFLOW:
      return 0;

    case LONGINT_INVALID:
    case LONGINT_INVALID_SUFFIX_CHAR:
    case LONGINT_INVALID_SUFFIX_CHAR_WITH_OVERFLOW:
      return -1;

    default:
      unreachable ();
    }
}

/* Return true if standard output is a tty, caching the result.  */

static bool stdout_isatty_computed = false;
static bool stdout_isatty_result;

static bool
stdout_isatty (void)
{
  if (!stdout_isatty_computed)
    {
      int ret = isatty(STDOUT_FILENO);
      if (ret == 1)
        {
          stdout_isatty_result = true;
        }
      else
        {
          stdout_isatty_result = false;
        }
      stdout_isatty_computed = true;
    }
  return stdout_isatty_result;
}

/* Set all the option flags according to the switches specified.
   Return the index of the first non-option argument.  */

static int
decode_switches(int argc, char **argv)
{
  char const *time_style_option = nullptr;

  /* These variables are false or -1 unless a switch says otherwise.  */
  bool kibibytes_specified = false;
  int format_opt = -1;
  int hide_control_chars_opt = -1;
  int quoting_style_opt = -1;
  int sort_opt = -1;
  ptrdiff_t tabsize_opt = -1;
  ptrdiff_t width_opt = -1;

  while (true)
    {
      int oi = -1;
      int c = getopt_long(argc, argv,
                          "abcdfghiklmnopqrstuvw:xABCDFGHI:LNQRST:UXZ1",
                          long_options, &oi);
      if (c == -1)
        break;

      switch (c)
        {
        case 'a':
          ignore_mode = IGNORE_MINIMAL;
          break;

        case 'b':
          quoting_style_opt = escape_quoting_style;
          break;

        case 'c':
          time_type = time_ctime;
          explicit_time = true;
          break;

        case 'd':
          immediate_dirs = true;
          break;

        case 'f':
          ignore_mode = IGNORE_MINIMAL; /* enable -a */
          sort_opt = sort_none;         /* enable -U */
          break;

        case FILE_TYPE_INDICATOR_OPTION: /* --file-type */
          indicator_style = file_type;
          break;

        case 'g':
          format_opt = long_format;
          print_owner = false;
          break;

        case 'h':
          file_human_output_opts = human_output_opts =
            human_autoscale | human_SI | human_base_1024;
          file_output_block_size = output_block_size = 1;
          break;

        case 'i':
          print_inode = true;
          break;

        case 'k':
          kibibytes_specified = true;
          break;

        case 'l':
          format_opt = long_format;
          break;

        case 'm':
          format_opt = with_commas;
          break;

        case 'n':
          numeric_ids = true;
          format_opt = long_format;
          break;

        case 'o':  /* Just like -l, but don't display group info.  */
          format_opt = long_format;
          print_group = false;
          break;

        case 'p':
          indicator_style = slash;
          break;

        case 'q':
          hide_control_chars_opt = true;
          break;

        case 'r':
          sort_reverse = true;
          break;

        case 's':
          print_block_size = true;
          break;

        case 't':
          sort_opt = sort_time;
          break;

        case 'u':
          time_type = time_atime;
          explicit_time = true;
          break;

        case 'v':
          sort_opt = sort_version;
          break;

        case 'w':
          width_opt = decode_line_length(optarg);
          if (width_opt < 0)
            error(LS_FAILURE, 0, "%s: %s", _("invalid line width"),
                  quote(optarg));
          break;

        case 'x':
          format_opt = horizontal;
          break;

        case 'A':
          ignore_mode = IGNORE_DOT_AND_DOTDOT;
          break;

        case 'B':
          add_ignore_pattern("*~");
          add_ignore_pattern(".*~");
          break;

        case 'C':
          format_opt = many_per_line;
          break;

        case 'D':
          format_opt = long_format;
          print_hyperlink = false;
          dired = true;
          break;

        case 'F':
          {
            int i = optarg ? XARGMATCH("--classify", optarg, when_args, when_types) : when_always;
            if (i == when_always || (i == when_if_tty && stdout_isatty()))
              indicator_style = classify;
          }
          break;

        case 'G':		/* inhibit display of group info */
          print_group = false;
          break;

        case 'H':
          dereference = DEREF_COMMAND_LINE_ARGUMENTS;
          break;

        case DEREFERENCE_COMMAND_LINE_SYMLINK_TO_DIR_OPTION:
          dereference = DEREF_COMMAND_LINE_SYMLINK_TO_DIR;
          break;

        case 'I':
          add_ignore_pattern(optarg);
          break;

        case 'L':
          dereference = DEREF_ALWAYS;
          break;

        case 'N':
          quoting_style_opt = literal_quoting_style;
          break;

        case 'Q':
          quoting_style_opt = c_quoting_style;
          break;

        case 'R':
          recursive = true;
          break;

        case 'S':
          sort_opt = sort_size;
          break;

        case 'T':
          tabsize_opt = xnumtoumax(optarg, 0, 0, MIN(PTRDIFF_MAX, SIZE_MAX),
                                   "", _("invalid tab size"), LS_FAILURE, 0);
          break;

        case 'U':
          sort_opt = sort_none;
          break;

        case 'X':
          sort_opt = sort_extension;
          break;

        case '1':
          /* -1 has no effect after -l.  */
          if (format_opt != long_format)
            format_opt = one_per_line;
          break;

        case AUTHOR_OPTION:
          print_author = true;
          break;

        case HIDE_OPTION:
          {
            struct ignore_pattern *hide = xmalloc(sizeof *hide);
            hide->pattern = optarg;
            hide->next = hide_patterns;
            hide_patterns = hide;
          }
          break;

        case SORT_OPTION:
          sort_opt = XARGMATCH("--sort", optarg, sort_args, sort_types);
          break;

        case GROUP_DIRECTORIES_FIRST_OPTION:
          directories_first = true;
          break;

        case TIME_OPTION:
          time_type = XARGMATCH("--time", optarg, time_args, time_types);
          explicit_time = true;
          break;

        case FORMAT_OPTION:
          format_opt = XARGMATCH("--format", optarg, format_args,
                                 format_types);
          break;

        case FULL_TIME_OPTION:
          format_opt = long_format;
          time_style_option = "full-iso";
          break;

        case COLOR_OPTION:
          {
            int i = optarg ? XARGMATCH("--color", optarg, when_args, when_types) : when_always;
            print_with_color = (i == when_always || (i == when_if_tty && stdout_isatty()));
          }
          break;

        case HYPERLINK_OPTION:
          {
            int i = optarg ? XARGMATCH("--hyperlink", optarg, when_args, when_types) : when_always;
            print_hyperlink = (i == when_always || (i == when_if_tty && stdout_isatty()));
          }
          break;

        case INDICATOR_STYLE_OPTION:
          indicator_style = XARGMATCH("--indicator-style", optarg,
                                      indicator_style_args,
                                      indicator_style_types);
          break;

        case QUOTING_STYLE_OPTION:
          quoting_style_opt = XARGMATCH("--quoting-style", optarg,
                                        quoting_style_args,
                                        quoting_style_vals);
          break;

        case TIME_STYLE_OPTION:
          time_style_option = optarg;
          break;

        case SHOW_CONTROL_CHARS_OPTION:
          hide_control_chars_opt = false;
          break;

        case BLOCK_SIZE_OPTION:
          {
            enum strtol_error e = human_options(optarg, &human_output_opts,
                                                &output_block_size);
            if (e != LONGINT_OK)
              xstrtol_fatal(e, oi, 0, long_options, optarg);
            file_human_output_opts = human_output_opts;
            file_output_block_size = output_block_size;
          }
          break;

        case SI_OPTION:
          file_human_output_opts = human_output_opts =
            human_autoscale | human_SI;
          file_output_block_size = output_block_size = 1;
          break;

        case 'Z':
          print_scontext = true;
          break;

        case ZERO_OPTION:
          eolbyte = 0;
          hide_control_chars_opt = false;
          if (format_opt != long_format)
            format_opt = one_per_line;
          print_with_color = false;
          quoting_style_opt = literal_quoting_style;
          break;

        case_GETOPT_HELP_CHAR;

        case_GETOPT_VERSION_CHAR (PROGRAM_NAME, AUTHORS);

        default:
          usage(LS_FAILURE);
        }
    }

  if (! output_block_size)
    {
      char const *ls_block_size = getenv("LS_BLOCK_SIZE");
      human_options(ls_block_size,
                    &human_output_opts, &output_block_size);
      if (ls_block_size || getenv("BLOCK_SIZE"))
        {
          file_human_output_opts = human_output_opts;
          file_output_block_size = output_block_size;
        }
      if (kibibytes_specified)
        {
          human_output_opts = 0;
          output_block_size = 1024;
        }
    }

  format = (0 <= format_opt ? format_opt
            : ls_mode == LS_LS ? (stdout_isatty() ? many_per_line : one_per_line)
            : ls_mode == LS_MULTI_COL ? many_per_line
            : /* ls_mode == LS_LONG_FORMAT */ long_format);

  /* If the line length was not set by a switch but is needed to determine
     output, go to the work of obtaining it from the environment.  */
  ptrdiff_t linelen = width_opt;
  if (format == many_per_line || format == horizontal || format == with_commas
      || print_with_color)
    {
#ifdef TIOCGWINSZ
      if (linelen < 0)
        {
          struct winsize ws;
          if (stdout_isatty()
              && ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) >= 0
              && ws.ws_col > 0)
            linelen = ws.ws_col <= MIN(PTRDIFF_MAX, SIZE_MAX) ? ws.ws_col : 0;
        }
#endif
      if (linelen < 0)
        {
          char const *p = getenv("COLUMNS");
          if (p && *p)
            {
              linelen = decode_line_length(p);
              if (linelen < 0)
                error(0, 0,
                      _("ignoring invalid width"
                        " in environment variable COLUMNS: %s"),
                      quote(p));
            }
        }
    }

  line_length = linelen < 0 ? 80 : linelen;

  /* Determine the max possible number of display columns.  */
  max_idx = line_length / MIN_COLUMN_WIDTH;
  /* Account for first display column not having a separator,
     or line_lengths shorter than MIN_COLUMN_WIDTH.  */
  max_idx += (line_length % MIN_COLUMN_WIDTH != 0);

  if (format == many_per_line || format == horizontal || format == with_commas)
    {
      if (0 <= tabsize_opt)
        tabsize = tabsize_opt;
      else
        {
          tabsize = 8;
          char const *p = getenv("TABSIZE");
          if (p)
            {
              uintmax_t tmp;
              if (xstrtoumax(p, nullptr, 0, &tmp, "") == LONGINT_OK
                  && tmp <= SIZE_MAX)
                tabsize = tmp;
              else
                error(0, 0,
                      _("ignoring invalid tab size"
                        " in environment variable TABSIZE: %s"),
                      quote(p));
            }
        }
    }

  qmark_funny_chars = (hide_control_chars_opt < 0
                       ? ls_mode == LS_LS && stdout_isatty()
                       : hide_control_chars_opt);

  int qs = quoting_style_opt;
  if (qs < 0)
    qs = getenv_quoting_style();
  if (qs < 0)
    qs = (ls_mode == LS_LS
          ? (stdout_isatty() ? shell_escape_quoting_style : -1)
          : escape_quoting_style);
  if (0 <= qs)
    set_quoting_style(nullptr, qs);
  qs = get_quoting_style(nullptr);
  align_variable_outer_quotes
    = ((format == long_format
        || ((format == many_per_line || format == horizontal) && line_length))
       && (qs == shell_quoting_style
           || qs == shell_escape_quoting_style
           || qs == c_maybe_quoting_style));
  filename_quoting_options = clone_quoting_options(nullptr);
  if (qs == escape_quoting_style)
    set_char_quoting(filename_quoting_options, ' ', 1);
  if (file_type <= indicator_style)
    {
      char const *p;
      for (p = &"*=>@|"[indicator_style - file_type]; *p; p++)
        set_char_quoting(filename_quoting_options, *p, 1);
    }

  dirname_quoting_options = clone_quoting_options(nullptr);
  set_char_quoting(dirname_quoting_options, ':', 1);

  /* --dired implies --format=long (-l) and sans --hyperlink.
     So ignore it if those overridden.  */
  dired &= (format == long_format) & !print_hyperlink;

  if (eolbyte < dired)
    error(LS_FAILURE, 0, _("--dired and --zero are incompatible"));

  /* If a time type is explicitly specified (with -c, -u, or --time=)
     and we're not showing a time (-l not specified), then sort by that time,
     rather than by name.  Note this behavior is unspecified by POSIX.  */

  sort_type = (0 <= sort_opt ? sort_opt
               : (format != long_format && explicit_time)
               ? sort_time : sort_name);

  if (format == long_format)
    {
      char const *style = time_style_option;
      static char const posix_prefix[] = "posix-";

      if (! style)
        {
          style = getenv("TIME_STYLE");
          if (! style)
            style = "locale";
        }

      while (STREQ_LEN(style, posix_prefix, sizeof posix_prefix - 1))
        {
          if (! hard_locale(LC_TIME))
            return optind;
          style += sizeof posix_prefix - 1;
        }

      if (*style == '+')
        {
          char const *p0 = style + 1;
          char *p0nl = strchr(p0, '\n');
          char const *p1 = p0;
          if (p0nl)
            {
              if (strchr(p0nl + 1, '\n'))
                error(LS_FAILURE, 0, _("invalid time style format %s"),
                      quote(p0));
              *p0nl++ = '\0';
              p1 = p0nl;
            }
          long_time_format[0] = p0;
          long_time_format[1] = p1;
        }
      else
        {
          switch (x_timestyle_match(style, /*allow_posix=*/ true,
                                    time_style_args,
                                    (char const *) time_style_types,
                                    sizeof(*time_style_types), LS_FAILURE))
            {
            case full_iso_time_style:
              long_time_format[0] = long_time_format[1] =
                "%Y-%m-%d %H:%M:%S.%N %z";
              break;

            case long_iso_time_style:
              long_time_format[0] = long_time_format[1] = "%Y-%m-%d %H:%M";
              break;

            case iso_time_style:
              long_time_format[0] = "%Y-%m-%d ";
              long_time_format[1] = "%m-%d %H:%M";
              break;

            case locale_time_style:
              if (hard_locale(LC_TIME))
                {
                  for (int i = 0; i < 2; i++)
                    long_time_format[i] =
                      dcgettext(nullptr, long_time_format[i], LC_TIME);
                }
            }
        }

      abformat_init();
    }

  return optind;
}

/* Parse a string as part of the LS_COLORS variable; this may involve
   decoding all kinds of escape characters.  If equals_end is set an
   unescaped equal sign ends the string, otherwise only a : or \0
   does.  Set *OUTPUT_COUNT to the number of bytes output.  Return
   true if successful.

   The resulting string is *not* null-terminated, but may contain
   embedded nulls.

   Note that both dest and src are char **; on return they point to
   the first free byte after the array and the character that ended
   the input string, respectively.  */

static inline bool
is_hex_digit(char c)
{
    return (c >= '0' && c <= '9') ||
           (c >= 'a' && c <= 'f') ||
           (c >= 'A' && c <= 'F');
}

static inline int
hex_to_int(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return 0; /* Should not be reached with prior is_hex_digit check */
}

static bool
get_funky_string (char **dest, char const **src, bool equals_end,
                  size_t *output_count)
{
  int current_char_value; /* Use int for safety with escape sequences */
  size_t count = 0;
  enum {
    ST_GND, ST_BACKSLASH, ST_OCTAL_DIGIT, ST_HEX_DIGIT, ST_CARET, ST_END, ST_ERROR
  } state = ST_GND;

  char const *p = *src;
  char *q = *dest;

  while (state != ST_END && state != ST_ERROR)
    {
      char c = *p; /* Current character from source */

      switch (state)
        {
        case ST_GND:
          switch (c)
            {
            case ':':
            case '\0':
              state = ST_END;
              break;
            case '=':
              if (equals_end)
                {
                  state = ST_END;
                  break;
                }
              /* If equals_end is false, fall through to default case */
            case '\\':
              state = ST_BACKSLASH;
              p++; /* Advance past backslash */
              break;
            case '^':
              state = ST_CARET;
              p++; /* Advance past caret */
              break;
            default:
              *q++ = c;
              count++;
              p++; /* Advance past regular character */
              break;
            }
          break;

        case ST_BACKSLASH:
          switch (c)
            {
            case '0': case '1': case '2': case '3': case '4':
            case '5': case '6': case '7':
              state = ST_OCTAL_DIGIT;
              current_char_value = c - '0';
              p++;
              break;
            case 'x':
            case 'X':
              state = ST_HEX_DIGIT;
              current_char_value = 0; /* Initialize for hex accumulation */
              p++;
              break;
            case 'a': current_char_value = '\a'; break;
            case 'b': current_char_value = '\b'; break;
            case 'e': current_char_value = 27;   break; /* ESC */
            case 'f': current_char_value = '\f'; break;
            case 'n': current_char_value = '\n'; break;
            case 'r': current_char_value = '\r'; break;
            case 't': current_char_value = '\t'; break;
            case 'v': current_char_value = '\v'; break;
            case '?': current_char_value = 127;  break; /* DEL */
            case '_': current_char_value = ' ';   break;
            case '\0': /* Incomplete escape sequence */
              state = ST_ERROR;
              break;
            default: /* Escaped character itself */
              current_char_value = c;
              break;
            }
          /* After processing a single-char escape, emit and return to GND */
          if (state == ST_BACKSLASH) { /* Only if not transitioned to OCTAL/HEX */
            *q++ = (char)current_char_value;
            count++;
            p++; /* Advance past escaped character */
            state = ST_GND;
          }
          break;

        case ST_OCTAL_DIGIT:
          if (c >= '0' && c <= '7')
            {
              current_char_value = (current_char_value << 3) + (c - '0');
              p++;
            }
          else
            { /* Non-octal digit encountered or end of string */
              *q++ = (char)current_char_value;
              count++;
              state = ST_GND; /* Don't advance p, let it be re-evaluated in GND */
            }
          break;

        case ST_HEX_DIGIT:
          if (is_hex_digit(c))
            {
              current_char_value = (current_char_value << 4) + hex_to_int(c);
              p++;
            }
          else
            { /* Non-hex digit encountered or end of string */
              *q++ = (char)current_char_value;
              count++;
              state = ST_GND; /* Don't advance p */
            }
          break;

        case ST_CARET:
          if (c >= '@' && c <= '~')
            {
              *q++ = c & 0x1F; /* Control character */
              count++;
              p++;
              state = ST_GND;
            }
          else if (c == '?')
            {
              *q++ = 127; /* DEL */
              count++;
              p++;
              state = ST_GND;
            }
          else
            { /* Malformed caret escape */
              state = ST_ERROR;
            }
          break;

        case ST_END:
        case ST_ERROR:
        default:
          /* These states should terminate the loop and not be reached in the switch. */
          break;
        }
    }

  *dest = q;
  *src = p;
  *output_count = count;

  return state != ST_ERROR;
}

enum parse_state
  {
    PS_START = 1,
    PS_2,
    PS_3,
    PS_4,
    PS_DONE,
    PS_FAIL
  };


/* Check if the content of TERM is a valid name in dircolors.  */

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <fnmatch.h>

// G_line is assumed to be a globally declared char array, e.g.:
// extern char G_line[];
// For sizeof(G_line) to work correctly and yield the array's total size in bytes,
// G_line must be defined as an array in a scope where its definition is visible
// at compile time (e.g., in the same .c file or a header with a sized array declaration).
// This refactoring assumes `G_line` is indeed a `char` array and `sizeof(G_line)`
// correctly provides its total capacity.

static bool
known_term_type (void)
{
  char const *term = getenv ("TERM");
  if (! term || ! *term)
    {
      return false;
    }

  const char * const TERM_PREFIX = "TERM ";
  const size_t TERM_PREFIX_LEN = sizeof(TERM_PREFIX) - 1;

  const char * const g_line_start = G_line;
  const char * const g_line_end = G_line + sizeof (G_line);
  char const *current_line_ptr = g_line_start;

  while (current_line_ptr < g_line_end)
    {
      size_t remaining_buffer_len = g_line_end - current_line_ptr;

      // Check for an empty string terminator for the entire list or if no space remains.
      if (remaining_buffer_len == 0 || *current_line_ptr == '\0')
        {
          break;
        }

      // Determine the actual length of the current null-terminated string,
      // bounded by the remaining buffer size to prevent over-reading.
      size_t current_str_len = strnlen(current_line_ptr, remaining_buffer_len);

      // Check if the current string starts with the "TERM " prefix
      // and is long enough to contain both the prefix and at least one character for the pattern.
      if (current_str_len >= TERM_PREFIX_LEN && strncmp(current_line_ptr, TERM_PREFIX, TERM_PREFIX_LEN) == 0)
        {
          // Ensure there's a pattern part after "TERM " and that the pattern string
          // is properly null-terminated within the bounds of G_line.
          // current_str_len < remaining_buffer_len implies strnlen found a null terminator.
          if (current_str_len > TERM_PREFIX_LEN && current_str_len < remaining_buffer_len)
            {
              if (fnmatch (current_line_ptr + TERM_PREFIX_LEN, term, 0) == 0)
                {
                  return true;
                }
            }
          // If current_str_len == remaining_buffer_len, it means the string filled
          // the buffer without a null terminator. Such a malformed entry is implicitly skipped
          // as passing it to `fnmatch` would be unsafe.
        }

      // Advance to the next string.
      // If current_str_len is equal to remaining_buffer_len, it means the current string
      // consumed the rest of the buffer and might not be null-terminated. In this case,
      // there is no null terminator to skip, and we've reached the effective end of the data.
      if (current_str_len == remaining_buffer_len)
        {
          break;
        }

      // Move past the current string and its null terminator to the start of the next string.
      current_line_ptr += current_str_len + 1;
    }

  return false;
}

enum GetFunkyStringType {
    FUNKY_STRING_IS_EXTENSION_PATTERN,
    FUNKY_STRING_IS_COLOR_SEQUENCE
};

static void
parse_ls_color (void)
{
  char const *p;
  char *buf;
  char label0, label1;
  struct color_ext_type *ext;

  if ((p = getenv ("LS_COLORS")) == nullptr || *p == '\0')
    {
      char const *colorterm = getenv ("COLORTERM");
      if (! (colorterm && *colorterm) && ! known_term_type ())
        print_with_color = false;
      return;
    }

  ext = nullptr;
  buf = color_buf = xstrdup (p);

  enum parse_state state = PS_START;
  while (true)
    {
      switch (state)
        {
        case PS_START:
          switch (*p)
            {
            case ':':
              ++p;
              break;

            case '*':
              ext = xmalloc (sizeof *ext);
              ext->next = color_ext_list;
              color_ext_list = ext;
              ext->exact_match = false;

              ++p;
              ext->ext.string = buf;

              state = (get_funky_string (&buf, &p, FUNKY_STRING_IS_EXTENSION_PATTERN, &ext->ext.len)
                       ? PS_4 : PS_FAIL);
              break;

            case '\0':
              state = PS_DONE;
              goto done;

            default:
              label0 = *p++;
              state = PS_2;
              break;
            }
          break;

        case PS_2:
          if (*p)
            {
              label1 = *p++;
              state = PS_3;
            }
          else
            state = PS_FAIL;
          break;

        case PS_3:
          state = PS_FAIL;
          if (*(p++) == '=')
            {
              for (int i = 0; i < ARRAY_CARDINALITY (indicator_name); i++)
                {
                  if ((label0 == indicator_name[i][0])
                      && (label1 == indicator_name[i][1]))
                    {
                      color_indicator[i].string = buf;
                      state = (get_funky_string (&buf, &p, FUNKY_STRING_IS_COLOR_SEQUENCE,
                                                 &color_indicator[i].len)
                               ? PS_START : PS_FAIL);
                      break;
                    }
                }
              if (state == PS_FAIL)
                error (0, 0, _("unrecognized prefix: %s"),
                       quote ((char []) {label0, label1, '\0'}));
            }
          break;

        case PS_4:
          if (*(p++) == '=')
            {
              ext->seq.string = buf;
              state = (get_funky_string (&buf, &p, FUNKY_STRING_IS_COLOR_SEQUENCE, &ext->seq.len)
                       ? PS_START : PS_FAIL);
            }
          else
            state = PS_FAIL;
          break;

        case PS_FAIL:
          goto done;

        case PS_DONE: default:
          affirm (false);
        }
    }
 done:

  if (state == PS_FAIL)
    {
      struct color_ext_type *e;
      struct color_ext_type *e2;

      error (0, 0,
             _("unparsable value for LS_COLORS environment variable"));
      free (color_buf);
      for (e = color_ext_list; e != nullptr; /* empty */)
        {
          e2 = e;
          e = e->next;
          free (e2);
        }
      print_with_color = false;
    }
  else
    {
      struct color_ext_type *e1;

      for (e1 = color_ext_list; e1 != nullptr; e1 = e1->next)
        {
          struct color_ext_type *e2;
          bool case_ignored_for_e1 = false;

          for (e2 = e1->next; e2 != nullptr; e2 = e2->next)
            {
              if (e2->ext.len == SIZE_MAX || e1->ext.len != e2->ext.len)
                continue;

              if (memcmp (e1->ext.string, e2->ext.string, e1->ext.len) == 0)
                {
                  e2->ext.len = SIZE_MAX;
                }
              else if (c_strncasecmp (e1->ext.string, e2->ext.string,
                                     e1->ext.len) == 0)
                {
                  if (case_ignored_for_e1)
                    {
                      e2->ext.len = SIZE_MAX;
                    }
                  else if (e1->seq.len == e2->seq.len
                           && memcmp (e1->seq.string, e2->seq.string,
                                      e1->seq.len) == 0)
                    {
                      e2->ext.len = SIZE_MAX;
                      case_ignored_for_e1 = true;
                    }
                  else
                    {
                      e1->exact_match = true;
                      e2->exact_match = true;
                    }
                }
            }
        }
    }

  if (color_indicator[C_LINK].len == 6
      && !STRNCMP_LIT (color_indicator[C_LINK].string, "target"))
    color_symlink_as_referent = true;
}

/* Return the quoting style specified by the environment variable
   QUOTING_STYLE if set and valid, -1 otherwise.  */

static int
getenv_quoting_style (void)
{
  static const char ENV_VAR_QUOTING_STYLE_NAME[] = "QUOTING_STYLE";

  char const *quoting_style_value = getenv(ENV_VAR_QUOTING_STYLE_NAME);
  if (!quoting_style_value)
    {
      return -1; /* Environment variable not set */
    }

  int style_match_index = ARGMATCH(quoting_style_value, quoting_style_args, quoting_style_vals);
  if (style_match_index < 0)
    {
      error(0, 0,
            _("ignoring invalid value of environment variable QUOTING_STYLE: %s"),
            quote(quoting_style_value));
      return -1; /* Invalid value found */
    }

  return quoting_style_vals[style_match_index]; /* Valid style found */
}

/* Set the exit status to report a failure.  If SERIOUS, it is a
   serious failure; otherwise, it is merely a minor problem.  */

static void
set_exit_status (bool serious)
{
  if (serious) {
    exit_status = LS_FAILURE;
  } else if (exit_status == EXIT_SUCCESS) {
    exit_status = LS_MINOR_PROBLEM;
  }
}

/* Assuming a failure is serious if SERIOUS, use the printf-style
   MESSAGE to report the failure to access a file named FILE.  Assume
   errno is set appropriately for the failure.  */

static void
file_failure (bool serious, char const *message, char const *file)
{
  int saved_errno = errno;
  error (0, saved_errno, message, quoteaf (file));
  set_exit_status (serious);
}

/* Request that the directory named NAME have its contents listed later.
   If REALNAME is nonzero, it will be used instead of NAME when the
   directory name is printed.  This allows symbolic links to directories
   to be treated as regular directories but still be listed under their
   real names.  NAME == nullptr is used to insert a marker entry for the
   directory named in REALNAME.
   If NAME is non-null, we use its dev/ino information to save
   a call to stat -- when doing a recursive (-R) traversal.
   COMMAND_LINE_ARG means this directory was mentioned on the command line.  */

static void
queue_directory (char const *name, char const *realname, bool command_line_arg)
{
  struct pending *new_node = xmalloc (sizeof *new_node);
  new_node->realname = realname ? xstrdup (realname) : nullptr;
  new_node->name = name ? xstrdup (name) : nullptr;
  new_node->command_line_arg = command_line_arg;
  new_node->next = pending_dirs;
  pending_dirs = new_node;
}

/* Read directory NAME, and list the files in it.
   If REALNAME is nonzero, print its name instead of NAME;
   this is used for symbolic links to directories.
   COMMAND_LINE_ARG means this directory was mentioned on the command line.  */

static bool
check_and_register_dir(char const *name, DIR *dirp, bool command_line_arg)
{
  struct stat dir_stat;
  int fd = dirfd (dirp);

  if ((0 <= fd
       ? fstat_for_ino (fd, &dir_stat)
       : stat_for_ino (name, &dir_stat)) < 0)
    {
      file_failure (command_line_arg,
                    _("cannot determine device and inode of %s"), name);
      return true;
    }

  if (visit_dir (dir_stat.st_dev, dir_stat.st_ino))
    {
      error (0, 0, _("%s: not listing already-listed directory"),
             quotef (name));
      set_exit_status (true);
      return true;
    }

  dev_ino_push (dir_stat.st_dev, dir_stat.st_ino);
  return false;
}

static void
print_directory_name_header(char const *name, char const *realname, bool command_line_arg, bool *is_first_call_overall)
{
  if (recursive || print_dir_name)
    {
      if (!*is_first_call_overall)
        dired_outbyte ('\n');
      *is_first_call_overall = false;
      dired_indent ();

      char *absolute_name = nullptr;
      if (print_hyperlink)
        {
          absolute_name = canonicalize_filename_mode (name, CAN_MISSING);
          if (! absolute_name)
            file_failure (command_line_arg, _("error canonicalizing %s"), name);
        }
      quote_name (realname ? realname : name, dirname_quoting_options, -1,
                  nullptr, true, &subdired_obstack, absolute_name);

      free (absolute_name);

      dired_outstring (":\n");
    }
}

static void
print_total_blocks_summary(uintmax_t total_blocks)
{
  if (format == long_format || print_block_size)
    {
      char buf[LONGEST_HUMAN_READABLE + 3];
      char *p = human_readable (total_blocks, buf + 1, human_output_opts,
                                ST_NBLOCKSIZE, output_block_size);
      char *pend = p + strlen (p);
      *--p = ' ';
      *pend++ = eolbyte;
      dired_indent ();
      dired_outstring (_("total"));
      dired_outbuf (p, pend - p);
    }
}

static void
print_dir (char const *name, char const *realname, bool command_line_arg)
{
  DIR *dirp;
  uintmax_t total_blocks = 0;
  static bool first = true;

  errno = 0;
  dirp = opendir (name);
  if (!dirp)
    {
      file_failure (command_line_arg, _("cannot open directory %s"), name);
      return;
    }

  if (LOOP_DETECT)
    {
      if (check_and_register_dir(name, dirp, command_line_arg))
        {
          closedir (dirp);
          return;
        }
    }

  clear_files ();

  print_directory_name_header(name, realname, command_line_arg, &first);

  while (true)
    {
      struct dirent *next;
      errno = 0;
      next = readdir (dirp);

      if (next)
        {
          if (! file_ignored (next->d_name))
            {
              enum filetype type;
#if HAVE_STRUCT_DIRENT_D_TYPE
              type = d_type_filetype[next->d_type];
#else
              type = unknown;
#endif
              total_blocks += gobble_file (next->d_name, type,
                                           RELIABLE_D_INO (next),
                                           false, name);

              if (format == one_per_line && sort_type == sort_none
                      && !print_block_size && !recursive)
                {
                  sort_files ();
                  print_current_files ();
                  clear_files ();
                }
            }
        }
      else
        {
          int err = errno;
          if (err == 0)
            break;
#if ! (2 < __GLIBC__ + (3 <= __GLIBC_MINOR__))
          if (err == ENOENT)
            break;
#endif
          file_failure (command_line_arg, _("reading directory %s"), name);
          if (err != EOVERFLOW)
            break;
        }

      process_signals ();
    }

  if (closedir (dirp) != 0)
    {
      file_failure (command_line_arg, _("closing directory %s"), name);
    }

  sort_files ();

  if (recursive)
    extract_dirs_from_files (name, false);

  print_total_blocks_summary(total_blocks);

  if (cwd_n_used)
    print_current_files ();
}

/* Add 'pattern' to the list of patterns for which files that match are
   not listed.  */

static void
add_ignore_pattern (char const *pattern)
{
  struct ignore_pattern *new_node = xmalloc (sizeof *new_node);

  new_node->pattern = pattern;
  new_node->next = ignore_patterns;
  ignore_patterns = new_node;
}

/* Return true if one of the PATTERNS matches FILE.  */

static bool
patterns_match (struct ignore_pattern const *patterns, char const *file)
{
  if (file == NULL)
    {
      return false;
    }

  struct ignore_pattern const *p;
  for (p = patterns; p != NULL; p = p->next)
    {
      if (p->pattern == NULL)
        {
          continue;
        }

      if (fnmatch (p->pattern, file, FNM_PERIOD) == 0)
        {
          return true;
        }
    }
  return false;
}

/* Return true if FILE should be ignored.  */

static bool
file_ignored (char const *name)
{
  if (name[0] == '.') {
    if (ignore_mode == IGNORE_DEFAULT) {
      return true;
    }
    else if (ignore_mode != IGNORE_MINIMAL) {
      if (name[1] == '\0' || (name[1] == '.' && name[2] == '\0')) {
        return true;
      }
    }
  }

  if (ignore_mode == IGNORE_DEFAULT && patterns_match(hide_patterns, name)) {
    return true;
  }

  if (patterns_match(ignore_patterns, name)) {
    return true;
  }

  return false;
}

/* POSIX requires that a file size be printed without a sign, even
   when negative.  Assume the typical case where negative sizes are
   actually positive values that have wrapped around.  */

#include <limits.h>
#include <stdint.h>

static uintmax_t
unsigned_file_size (off_t size)
{
  if (size >= 0)
    {
      return (uintmax_t)size;
    }
  else
    {
      const uintmax_t off_t_range = (uintmax_t)1 << (sizeof(off_t) * CHAR_BIT);
      return (uintmax_t)size + off_t_range;
    }
}

#ifdef HAVE_CAP
/* Return true if NAME has a capability (see linux/capability.h) */
static bool
has_capability (char const *name)
{
  char *result;
  bool has_cap;

  cap_t cap_d = cap_get_file (name);
  if (cap_d == nullptr)
    return false;

  result = cap_to_text (cap_d, nullptr);
  cap_free (cap_d);
  if (!result)
    return false;

  /* check if human-readable capability string is empty */
  has_cap = !!*result;

  cap_free (result);
  return has_cap;
}
#else
static bool
has_capability (char const *name)
{
  (void)name;
  errno = ENOTSUP;
  return false;
}
#endif

/* Enter and remove entries in the table 'cwd_file'.  */

static void
free_ent (struct fileinfo *f)
{
  if (f == NULL) {
    return;
  }

  free (f->name);
  f->name = NULL;

  free (f->linkname);
  f->linkname = NULL;

  free (f->absolute_name);
  f->absolute_name = NULL;

  if (f->scontext != UNKNOWN_SECURITY_CONTEXT) {
    aclinfo_scontext_free (f->scontext);
    f->scontext = UNKNOWN_SECURITY_CONTEXT;
  }
}

/* Empty the table of files.  */
static void
clear_files (void)
{
  for (idx_t i = 0; i < cwd_n_used; ++i)
    {
      struct fileinfo *const f = sorted_file[i];
      free_ent (f);
    }

  cwd_n_used = 0;
  cwd_some_quoted = false;
  any_has_acl = false;

  inode_number_width = 0;
  block_size_width = 0;
  nlink_width = 0;
  owner_width = 0;
  group_width = 0;
  author_width = 0;
  scontext_width = 0;
  major_device_number_width = 0;
  minor_device_number_width = 0;
  file_size_width = 0;
}

/* Cache file_has_aclinfo failure, when it's trivial to do.
   Like file_has_aclinfo, but when F's st_dev says it's on a file
   system lacking ACL support, return 0 with ENOTSUP immediately.  */
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>

struct fileinfo {
  int stat_ok;
  struct stat stat;
};

struct aclinfo {
  void *buf;
  size_t size;
  union {
    char __gl_acl_ch[1];
  } u;
  char *scontext;
  int scontext_err;
};

#ifndef ACL_GET_SCONTEXT
#define ACL_GET_SCONTEXT (1 << 0)
#endif

extern int file_has_aclinfo(char const *file, struct aclinfo *ai, int flags);
extern int acl_errno_valid(int err);

static struct {
  int result;
  char *scontext;
  int scontext_err;
  dev_t device;
  int is_valid;
} s_unsupported_aclinfo_cache = {
  .result = 0,
  .scontext = NULL,
  .scontext_err = 0,
  .device = 0,
  .is_valid = 0
};

static void clear_cached_scontext(void) {
  if (s_unsupported_aclinfo_cache.scontext != NULL) {
    free(s_unsupported_aclinfo_cache.scontext);
    s_unsupported_aclinfo_cache.scontext = NULL;
  }
}

static int
file_has_aclinfo_cache (char const *file, struct fileinfo *f,
                        struct aclinfo *ai, int flags)
{
  if (s_unsupported_aclinfo_cache.is_valid &&
      f->stat_ok &&
      f->stat.st_dev == s_unsupported_aclinfo_cache.device)
    {
      ai->buf = NULL;
      ai->size = 0;
      ai->scontext = s_unsupported_aclinfo_cache.scontext;
      ai->scontext_err = s_unsupported_aclinfo_cache.scontext_err;
      errno = ENOTSUP;
      return s_unsupported_aclinfo_cache.result;
    }

  errno = 0;
  int result_code = file_has_aclinfo(file, ai, flags);
  int call_errno = errno;

  int is_unsupported_feature =
      f->stat_ok &&
      result_code <= 0 &&
      !acl_errno_valid(call_errno) &&
      (!(flags & ACL_GET_SCONTEXT) || !acl_errno_valid(ai->scontext_err));

  if (is_unsupported_feature)
    {
      clear_cached_scontext();

      s_unsupported_aclinfo_cache.result = result_code;

      s_unsupported_aclinfo_cache.scontext = (ai->scontext != NULL) ? strdup(ai->scontext) : NULL;

      s_unsupported_aclinfo_cache.scontext_err = ai->scontext_err;
      s_unsupported_aclinfo_cache.device = f->stat.st_dev;
      s_unsupported_aclinfo_cache.is_valid = 1;
    }

  return result_code;
}

/* Cache has_capability failure, when it's trivial to do.
   Like has_capability, but when F's st_dev says it's on a file
   system lacking capability support, return 0 with ENOTSUP immediately.  */
static bool
has_capability_cache (char const *file, struct fileinfo *f)
{
  static bool unsupported_cached;
  static dev_t unsupported_device;

  if (f->stat_ok && unsupported_cached && f->stat.st_dev == unsupported_device)
    {
      errno = ENOTSUP;
      return false;
    }

  bool result = has_capability (file);
  if (f->stat_ok && !result && !acl_errno_valid (errno))
    {
      unsupported_cached = true;
      unsupported_device = f->stat.st_dev;
    }
  return result;
}

static bool
needs_quoting (char const *name)
{
  char quoted_prefix_buf[2];
  size_t original_name_len = strlen(name);
  size_t quoted_name_full_len = quotearg_buffer(quoted_prefix_buf, sizeof quoted_prefix_buf, name, -1, filename_quoting_options);

  bool first_char_changed = (*name != *quoted_prefix_buf);
  bool total_length_changed = (original_name_len != quoted_name_full_len);

  return first_char_changed || total_length_changed;
}

/* Add a file to the current table of files.
   Verify that the file exists, and print an error message if it does not.
   Return the number of blocks that the file occupies.  */
static int
get_file_stat (char const *full_name, enum Dereference_mode dereference_mode,
               bool command_line_arg, struct stat *st, bool *do_deref_out)
{
  int err;
  *do_deref_out = false;

  switch (dereference_mode)
    {
    case DEREF_ALWAYS:
      err = do_stat (full_name, st);
      *do_deref_out = true;
      break;

    case DEREF_COMMAND_LINE_ARGUMENTS:
      if (command_line_arg)
        {
          err = do_stat (full_name, st);
          *do_deref_out = true;
        }
      else
        {
          err = do_lstat (full_name, st);
          *do_deref_out = false;
        }
      break;

    case DEREF_COMMAND_LINE_SYMLINK_TO_DIR:
      if (command_line_arg)
        {
          err = do_stat (full_name, st);
          *do_deref_out = true;

          bool need_lstat_for_symlink_to_dir = (err < 0
                                                 ? (errno == ENOENT || errno == ELOOP)
                                                 : !S_ISDIR(st->st_mode));
          if (need_lstat_for_symlink_to_dir)
            {
              err = do_lstat (full_name, st);
              *do_deref_out = false;
            }
        }
      else
        {
          err = do_lstat (full_name, st);
          *do_deref_out = false;
        }
      break;

    case DEREF_NEVER:
      err = do_lstat (full_name, st);
      *do_deref_out = false;
      break;

    case DEREF_UNDEFINED:
    default:
      unreachable ();
    }
  return err;
}


static uintmax_t
gobble_file (char const *name, enum filetype type, ino_t inode,
             bool command_line_arg, char const *dirname)
{
  uintmax_t blocks = 0;
  struct fileinfo *f;

  affirm (! command_line_arg || inode == NOT_AN_INODE_NUMBER);

  if (cwd_n_used == cwd_n_alloc)
    cwd_file = xpalloc (cwd_file, &cwd_n_alloc, 1, (size_t)-1, sizeof *cwd_file);

  f = &cwd_file[cwd_n_used];
  memset (f, '\0', sizeof *f);
  f->stat.st_ino = inode;
  f->filetype = type;
  f->scontext = UNKNOWN_SECURITY_CONTEXT;

  f->quoted = -1;
  if ((! cwd_some_quoted) && align_variable_outer_quotes)
    {
      f->quoted = needs_quoting (name);
      if (f->quoted)
        cwd_some_quoted = true;
    }

  bool needs_stat_by_default = command_line_arg || print_hyperlink || format_needs_stat;
  bool needs_stat_for_unknown_type = format_needs_type && type == unknown;
  bool needs_stat_for_colored_dir =
    (type == directory || type == unknown) && print_with_color
    && (is_colored (C_OTHER_WRITABLE)
        || is_colored (C_STICKY)
        || is_colored (C_STICKY_OTHER_WRITABLE));
  bool needs_stat_for_symlink_deref_or_inode =
    (print_inode || format_needs_type)
    && (type == symbolic_link || type == unknown)
    && (dereference == DEREF_ALWAYS
        || color_symlink_as_referent || check_symlink_mode);
  bool needs_stat_for_unknown_inode = print_inode && inode == NOT_AN_INODE_NUMBER;
  bool needs_stat_for_normal_file_checks =
    (type == normal || type == unknown)
    && (indicator_style == classify
        || (print_with_color && (is_colored (C_EXEC)
                                 || is_colored (C_SETUID)
                                 || is_colored (C_SETGID))));

  bool check_stat = needs_stat_by_default
                    || needs_stat_for_unknown_type
                    || needs_stat_for_colored_dir
                    || needs_stat_for_symlink_deref_or_inode
                    || needs_stat_for_unknown_inode
                    || needs_stat_for_normal_file_checks;

  char const *full_name = name;
  bool needs_full_path = (check_stat || print_scontext || format_needs_capability)
                         && name[0] != '/' && dirname;
  if (needs_full_path)
    {
      char *p = alloca (strlen (name) + strlen (dirname) + 2);
      attach (p, dirname, name);
      full_name = p;
    }

  bool do_deref;

  if (!check_stat)
    {
      do_deref = dereference == DEREF_ALWAYS;
    }
  else
    {
      if (print_hyperlink)
        {
          f->absolute_name = canonicalize_filename_mode (full_name, CAN_MISSING);
          if (! f->absolute_name)
            {
              file_failure (command_line_arg,
                            _("error canonicalizing %s"), full_name);
            }
        }

      int err = get_file_stat (full_name, dereference, command_line_arg, &f->stat, &do_deref);

      if (err != 0)
        {
          file_failure (command_line_arg,
                        _("cannot access %s"), full_name);

          f->name = xstrdup (name);
          cwd_n_used++;
          return 0;
        }

      f->stat_ok = true;
      f->filetype = type = d_type_filetype[IFTODT (f->stat.st_mode)];
    }

  if (type == directory && command_line_arg && !immediate_dirs)
    f->filetype = type = arg_directory;

  bool get_scontext = (format == long_format) || print_scontext;
  bool check_capability = format_needs_capability && (type == normal);

  if (get_scontext || check_capability)
    {
      struct aclinfo ai;
      memset(&ai, 0, sizeof(ai));
      int aclinfo_flags = ((do_deref ? ACL_SYMLINK_FOLLOW : 0)
                           | (get_scontext ? ACL_GET_SCONTEXT : 0)
                           | filetype_d_type[type]);
      int n = file_has_aclinfo_cache (full_name, f, &ai, aclinfo_flags);
      bool have_acl = 0 < n;
      bool have_scontext = !ai.scontext_err;

      bool cannot_access_acl = n < 0
           && (errno == EACCES || errno == ENOENT);

      f->acl_type = (!have_scontext && !have_acl
                     ? (cannot_access_acl ? ACL_T_UNKNOWN : ACL_T_NONE)
                     : (have_scontext && !have_acl
                        ? ACL_T_LSM_CONTEXT_ONLY
                        : ACL_T_YES));
      any_has_acl |= (f->acl_type != ACL_T_NONE);

      if (format == long_format && n < 0 && !cannot_access_acl)
        error (0, errno, "%s", quotef (full_name));
      else
        {
          if (print_scontext && ai.scontext_err
              && (! (is_ENOTSUP (ai.scontext_err)
                     || ai.scontext_err == ENODATA)))
            error (0, ai.scontext_err, "%s", quotef (full_name));
        }

      if (check_capability && aclinfo_has_xattr (&ai, XATTR_NAME_CAPS))
        f->has_capability = has_capability_cache (full_name, f);

      f->scontext = ai.scontext;
      ai.scontext = NULL;
      aclinfo_free (&ai);
    }

  if (type == symbolic_link && (format == long_format || check_symlink_mode))
    {
      struct stat linkstats;

      get_link_name (full_name, f, command_line_arg);

      if (f->linkname && f->quoted == 0 && needs_quoting (f->linkname))
        f->quoted = -1;

      if (f->linkname
          && (file_type <= indicator_style || check_symlink_mode)
          && stat_for_mode (full_name, &linkstats) == 0)
        {
          f->linkok = true;
          f->linkmode = linkstats.st_mode;
        }
    }

  blocks = STP_NBLOCKS (&f->stat);
  if (format == long_format || print_block_size)
    {
      char buf[LONGEST_HUMAN_READABLE + 1];
      int len = mbswidth (human_readable (blocks, buf, human_output_opts,
                                          ST_NBLOCKSIZE, output_block_size),
                          MBSWIDTH_FLAGS);
      if (block_size_width < len)
        block_size_width = len;
    }

  if (format == long_format)
    {
      if (print_owner)
        {
          int len = format_user_width (f->stat.st_uid);
          if (owner_width < len)
            owner_width = len;
        }

      if (print_group)
        {
          int len = format_group_width (f->stat.st_gid);
          if (group_width < len)
            group_width = len;
        }

      if (print_author)
        {
          int len = format_user_width (f->stat.st_author);
          if (author_width < len)
            author_width = len;
        }
    }

  if (print_scontext)
    {
      int len = strlen (f->scontext);
      if (scontext_width < len)
        scontext_width = len;
    }

  if (format == long_format)
    {
      char b[INT_BUFSIZE_BOUND (uintmax_t)];
      int b_len = strlen (umaxtostr (f->stat.st_nlink, b));
      if (nlink_width < b_len)
        nlink_width = b_len;

      if ((type == chardev) || (type == blockdev))
        {
          char buf[INT_BUFSIZE_BOUND (uintmax_t)];
          int len = strlen (umaxtostr (major (f->stat.st_rdev), buf));
          if (major_device_number_width < len)
            major_device_number_width = len;
          len = strlen (umaxtostr (minor (f->stat.st_rdev), buf));
          if (minor_device_number_width < len)
            minor_device_number_width = len;
          len = major_device_number_width + 2 + minor_device_number_width;
          if (file_size_width < len)
            file_size_width = len;
        }
      else
        {
          char buf[LONGEST_HUMAN_READABLE + 1];
          uintmax_t size = unsigned_file_size (f->stat.st_size);
          int len = mbswidth (human_readable (size, buf,
                                              file_human_output_opts,
                                              1, file_output_block_size),
                              MBSWIDTH_FLAGS);
          if (file_size_width < len)
            file_size_width = len;
        }
    }

  if (print_inode)
    {
      char buf[INT_BUFSIZE_BOUND (uintmax_t)];
      int len = strlen (umaxtostr (f->stat.st_ino, buf));
      if (inode_number_width < len)
        inode_number_width = len;
    }

  f->name = xstrdup (name);
  cwd_n_used++;

  return blocks;
}

/* Return true if F refers to a directory.  */
static bool
is_directory (const struct fileinfo *f)
{
  if (f == NULL)
    {
      return false;
    }
  return f->filetype == directory || f->filetype == arg_directory;
}

/* Return true if F refers to a (symlinked) directory.  */
static bool
is_linked_directory (const struct fileinfo *f)
{
  if (f == NULL)
    {
      /* A NULL fileinfo pointer cannot represent a linked directory.
       * Returning false prevents dereferencing a NULL pointer,
       * improving reliability and security. */
      return false;
    }

  return f->filetype == directory || f->filetype == arg_directory
         || S_ISDIR (f->linkmode);
}

/* Put the name of the file that FILENAME is a symbolic link to
   into the LINKNAME field of 'f'.  COMMAND_LINE_ARG indicates whether
   FILENAME is a command-line argument.  */

static void
get_link_name (char const *filename, struct fileinfo *f, bool command_line_arg)
{
  f->linkname = areadlink_with_size (filename, f->stat.st_size);
  if (f->linkname == NULL)
    file_failure (command_line_arg, _("cannot read symbolic link %s"),
                  filename);
}

/* Return true if the last component of NAME is '.' or '..'
   This is so we don't try to recurse on '././././. ...' */

static bool
basename_is_dot_or_dotdot (char const *name)
{
  if (name == NULL)
    {
      return false;
    }

  char const *base = last_component (name);

  if (base == NULL)
    {
      return false;
    }

  return dot_or_dotdot (base);
}

/* Remove any entries from CWD_FILE that are for directories,
   and queue them to be listed as directories instead.
   DIRNAME is the prefix to prepend to each dirname
   to make it correct relative to ls's working dir;
   if it is null, no prefix is needed and "." and ".." should not be ignored.
   If COMMAND_LINE_ARG is true, this directory was mentioned at the top level,
   This is desirable when processing directories recursively.  */

static void
extract_dirs_from_files(char const *dirname, bool command_line_arg)
{
  bool const ignore_dot_and_dot_dot = (dirname != NULL);

  if (dirname && LOOP_DETECT)
    {
      queue_directory(NULL, dirname, false);
    }

  for (idx_t i = cwd_n_used - 1; i >= 0; --i)
    {
      struct fileinfo *f = sorted_file[i];

      if (is_directory(f) && (!ignore_dot_and_dot_dot || !basename_is_dot_or_dotdot(f->name)))
        {
          char *path_to_free = NULL;
          char const *path_to_use;

          if (dirname == NULL || f->name[0] == '/')
            {
              path_to_use = f->name;
            }
          else
            {
              path_to_free = file_name_concat(dirname, f->name, NULL);
              if (path_to_free == NULL)
                {
                  continue;
                }
              path_to_use = path_to_free;
            }

          queue_directory(path_to_use, f->linkname, command_line_arg);

          if (path_to_free != NULL)
            {
              free(path_to_free);
            }

          if (f->filetype == arg_directory)
            {
              free_ent(f);
            }
        }
    }

  idx_t write_idx = 0;
  for (idx_t read_idx = 0; read_idx < cwd_n_used; ++read_idx)
    {
      struct fileinfo *f = sorted_file[read_idx];
      if (f->filetype != arg_directory)
        {
          sorted_file[write_idx] = f;
          write_idx++;
        }
    }
  cwd_n_used = write_idx;
}

/* Use strcoll to compare strings in this locale.  If an error occurs,
   report an error and longjmp to failed_strcoll.  */

static jmp_buf failed_strcoll;

static int
xstrcoll (char const *a, char const *b)
{
  int diff;
  errno = 0;
  diff = strcoll (a, b);
  if (errno)
    {
      error (0, errno, _("cannot compare file names %s and %s"),
             quote_n (0, a), quote_n (1, b));
      set_exit_status (false);
      exit (EXIT_FAILURE);
    }
  return diff;
}

/* Comparison routines for sorting the files.  */

typedef void const *V;
typedef int (*qsortFunc)(V a, V b);

/* Used below in DEFINE_SORT_FUNCTIONS for _df_ sort function variants.  */
static int
dirfirst_check (struct fileinfo const *a, struct fileinfo const *b,
                int (*cmp) (struct fileinfo const *, struct fileinfo const *))
{
  int diff = is_linked_directory (b) - is_linked_directory (a);
  return diff ? diff : cmp (a, b);
}

/* Define the 8 different sort function variants required for each sortkey.
   KEY_NAME is a token describing the sort key, e.g., ctime, atime, size.
   KEY_CMP_FUNC is a function to compare records based on that key, e.g.,
   ctime_cmp, atime_cmp, size_cmp.  Append KEY_NAME to the string,
   '[rev_][x]str{cmp|coll}[_df]_', to create each function name.  */
#define DEFINE_SORT_FUNCTIONS(key_name, key_cmp_func)			\
  /* direct, non-dirfirst versions */					\
  static int xstrcoll_##key_name (V a, V b)				\
  { return key_cmp_func (a, b, xstrcoll); }				\
  ATTRIBUTE_PURE static int strcmp_##key_name (V a, V b)		\
  { return key_cmp_func (a, b, strcmp); }				\
                                                                        \
  /* reverse, non-dirfirst versions */					\
  static int rev_xstrcoll_##key_name (V a, V b)				\
  { return key_cmp_func (b, a, xstrcoll); }				\
  ATTRIBUTE_PURE static int rev_strcmp_##key_name (V a, V b)	\
  { return key_cmp_func (b, a, strcmp); }				\
                                                                        \
  /* direct, dirfirst versions */					\
  static int xstrcoll_df_##key_name (V a, V b)				\
  { return dirfirst_check (a, b, xstrcoll_##key_name); }		\
  ATTRIBUTE_PURE static int strcmp_df_##key_name (V a, V b)		\
  { return dirfirst_check (a, b, strcmp_##key_name); }			\
                                                                        \
  /* reverse, dirfirst versions */					\
  static int rev_xstrcoll_df_##key_name (V a, V b)			\
  { return dirfirst_check (a, b, rev_xstrcoll_##key_name); }		\
  ATTRIBUTE_PURE static int rev_strcmp_df_##key_name (V a, V b)	\
  { return dirfirst_check (a, b, rev_strcmp_##key_name); }

static int
cmp_ctime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int diff = timespec_cmp (get_stat_ctime (&b->stat),
                           get_stat_ctime (&a->stat));

  if (diff != 0)
  {
    return diff;
  }
  else
  {
    if (cmp != NULL)
    {
      return cmp(a->name, b->name);
    }
    else
    {
      return 0;
    }
  }
}

static int
cmp_mtime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int diff = timespec_cmp(get_stat_mtime(&b->stat),
                          get_stat_mtime(&a->stat));

  if (diff != 0)
    {
      return diff;
    }

  if (cmp == NULL)
    {
      /*
       * If modification times are equal and no name comparison function is
       * provided (i.e., cmp is NULL), treat them as equal for tie-breaking.
       * This prevents a null function pointer dereference, improving
       * reliability and security, without altering the primary comparison logic.
       */
      return 0;
    }

  return cmp(a->name, b->name);
}

static int
cmp_atime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == NULL && b == NULL)
    return 0;
  if (a == NULL)
    return -1;
  if (b == NULL)
    return 1;

  int diff = timespec_cmp (get_stat_atime (&b->stat),
                           get_stat_atime (&a->stat));

  return diff ? diff : cmp (a->name, b->name);
}

static int
cmp_btime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == NULL && b == NULL)
    return 0;
  if (a == NULL)
    return -1;
  if (b == NULL)
    return 1;

  int diff = timespec_cmp (get_stat_btime (&b->stat),
                           get_stat_btime (&a->stat));

  if (diff != 0)
    {
      return diff;
    }
  else
    {
      if (cmp != NULL)
        {
          return cmp (a->name, b->name);
        }
      else
        {
          return 0;
        }
    }
}

static int
off_cmp (off_t a, off_t b)
{
  if (a < b)
    return -1;
  if (a > b)
    return 1;
  return 0;
}

static int
cmp_size (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  if (a == NULL) {
    return (b == NULL) ? 0 : -1;
  }
  if (b == NULL) {
    return 1;
  }

  int diff = off_cmp (b->stat.st_size, a->stat.st_size);

  if (diff != 0) {
    return diff;
  } else {
    return cmp (a->name, b->name);
  }
}

static int
cmp_name (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  if (cmp == NULL)
    {
      return 0;
    }

  if (a == NULL)
    {
      return (b == NULL) ? 0 : -1;
    }
  if (b == NULL)
    {
      return 1;
    }

  char const *name_a = a->name;
  char const *name_b = b->name;

  if (name_a == NULL)
    {
      return (name_b == NULL) ? 0 : -1;
    }
  if (name_b == NULL)
    {
      return 1;
    }

  return cmp (name_a, name_b);
}

/* Compare file extensions.  Files with no extension are 'smallest'.
   If extensions are the same, compare by file names instead.  */

static int
cmp_extension (struct fileinfo const *a, struct fileinfo const *b,
               int (*cmp) (char const *, char const *))
{
  char const *extension_ptr_a = strrchr(a->name, '.');
  char const *extension_ptr_b = strrchr(b->name, '.');

  // If strrchr returns NULL, it means no '.' was found.
  // In such cases, we treat the "extension" as an empty string for comparison purposes.
  char const *effective_extension_a = extension_ptr_a ? extension_ptr_a : "";
  char const *effective_extension_b = extension_ptr_b ? extension_ptr_b : "";

  int extension_comparison_result = cmp(effective_extension_a, effective_extension_b);

  if (extension_comparison_result != 0)
    {
      return extension_comparison_result;
    }
  else
    {
      // If extensions are identical (or both absent),
      // fall back to comparing the full names.
      return cmp(a->name, b->name);
    }
}

/* Return the (cached) screen width,
   for the NAME associated with the passed fileinfo F.  */

static size_t
fileinfo_name_width (struct fileinfo const *f)
{
  if (f == NULL)
    {
      return 0;
    }

  return f->width
         ? f->width
         : quote_name_width (f->name, filename_quoting_options, f->quoted);
}

static int
cmp_width (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  if (a == NULL) {
    return (b == NULL) ? 0 : -1;
  }
  if (b == NULL) {
    return 1;
  }

  int diff = fileinfo_name_width (a) - fileinfo_name_width (b);

  if (diff != 0) {
    return diff;
  }

  if (cmp == NULL) {
    return 0;
  }

  return cmp (a->name, b->name);
}

#include <stdlib.h>

typedef struct {
    long timestamp;
    int some_identifier;
} ctime;

static int cmp_ctime(const void *a, const void *b) {
    const ctime *ct_a = (const ctime *)a;
    const ctime *ct_b = (const ctime *)b;

    if (ct_a->timestamp < ct_b->timestamp) {
        return -1;
    }
    if (ct_a->timestamp > ct_b->timestamp) {
        return 1;
    }
    return 0;
}

#define DEFINE_SORT_FUNCTIONS(TYPE, COMPARATOR_FUNC) \
    void sort_ ## TYPE ## _array(TYPE *arr, size_t num_elements) { \
        if (arr == NULL) { \
            return; \
        } \
        if (num_elements <= 1) { \
            return; \
        } \
        qsort(arr, num_elements, sizeof(TYPE), (int (*)(const void *, const void *))COMPARATOR_FUNC); \
    }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#include <stdlib.h>
#include <time.h>

typedef time_t ctime;

int cmp_ctime(const void *a, const void *b) {
    const ctime *time_a = (const ctime *)a;
    const ctime *time_b = (const ctime *)b;

    if (*time_a < *time_b) {
        return -1;
    } else if (*time_a > *time_b) {
        return 1;
    }
    return 0;
}

void sort_ctime_array(ctime *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }

    qsort(array, count, sizeof(ctime), cmp_ctime);
}#include <time.h>
#include <stdlib.h>

static int cmp_ctime(const void *a, const void *b) {
    const time_t val_a = *(const time_t *)a;
    const time_t val_b = *(const time_t *)b;

    if (val_a < val_b) {
        return -1;
    } else if (val_a > val_b) {
        return 1;
    } else {
        return 0;
    }
}

void sort_time_array(time_t *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(time_t), cmp_ctime);
}static int qsort_compare_ctime_type(const void *a, const void *b) {
    const ctime *val_a = (const ctime *)a;
    const ctime *val_b = (const ctime *)b;
    return cmp_ctime(val_a, val_b);
}

void sort_ctime_array(ctime *array, size_t count) {
    if (array == NULL && count > 0) {
        return;
    }
    if (count <= 1) {
        return;
    }
    qsort(array, count, sizeof(ctime), qsort_compare_ctime_type);
}#include <stdlib.h>
#include <stddef.h>

typedef long long ctime_t;

int cmp_ctime(const void *a, const void *b) {
    const ctime_t *val_a = (const ctime_t *)a;
    const ctime_t *val_b = (const ctime_t *)b;
    if (*val_a < *val_b) {
        return -1;
    } else if (*val_a > *val_b) {
        return 1;
    }
    return 0;
}

void sort_ctime_array(ctime_t *array, size_t count) {
    if (array == NULL && count > 0) {
        return;
    }
    if (count <= 1) {
        return;
    }
    qsort(array, count, sizeof(ctime_t), cmp_ctime);
}#include <time.h>

int cmp_ctime(const void *a, const void *b) {
    const time_t *time_a = (const time_t *)a;
    const time_t *time_b = (const time_t *)b;

    if (time_a == NULL || time_b == NULL) {
        // Handle NULL pointers gracefully, or assert/error based on requirements.
        // For qsort, this scenario should ideally not occur with valid data.
        // Returning 0 for equality if both are NULL, otherwise non-zero.
        if (time_a == NULL && time_b == NULL) return 0;
        if (time_a == NULL) return -1; // NULL comes before non-NULL
        return 1; // non-NULL comes after NULL
    }

    if (*time_a < *time_b) {
        return -1;
    } else if (*time_a > *time_b) {
        return 1;
    } else {
        return 0;
    }
}#include <time.h>
#include <stdlib.h>

static int cmp_time_t(const void *a, const void *b) {
    const time_t *time_a = (const time_t *)a;
    const time_t *time_b = (const time_t *)b;

    if (*time_a < *time_b) {
        return -1;
    } else if (*time_a > *time_b) {
        return 1;
    } else {
        return 0;
    }
}

void sort_time_t_array(time_t *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }

    qsort(array, count, sizeof(time_t), cmp_time_t);
}#include <stdlib.h>
#include <time.h>
#include <stddef.h>

typedef struct {
    time_t timestamp;
    long id;
} TimestampData;

static int cmp_TimestampData(const void *ptr_a, const void *ptr_b) {
    const TimestampData *a = (const TimestampData *)ptr_a;
    const TimestampData *b = (const TimestampData *)ptr_b;

    if (a->timestamp < b->timestamp) {
        return -1;
    }
    if (a->timestamp > b->timestamp) {
        return 1;
    }

    if (a->id < b->id) {
        return -1;
    }
    if (a->id > b->id) {
        return 1;
    }

    return 0;
}

void sort_TimestampData_array(TimestampData *array, size_t count) {
    if (array == NULL) {
        return;
    }

    if (count <= 1) {
        return;
    }

    qsort(array, count, sizeof(TimestampData), cmp_TimestampData);
}
#include <stdlib.h> // For qsort
#include <time.h>   // For time_t

// This structure definition is assumed to exist in the legacy codebase
// and is provided here for the refactored code to be compilable and clear.
// Adjust the fields as per the actual structure being sorted.
typedef struct FileInfo {
    // Placeholder for other relevant fields in the structure.
    // The 'mtime' field is critical for the sorting functionality.
    time_t mtime; // Modification time, commonly used for sorting files by age.
} FileInfo;

// Comparison function for qsort to sort an array of FileInfo structures
// based on their 'mtime' field. This function is named 'cmp_mtime' as specified.
int cmp_mtime(const void *a, const void *b) {
    // Safely cast the generic void pointers to specific FileInfo pointers.
    const FileInfo *file_a = (const FileInfo *)a;
    const FileInfo *file_b = (const FileInfo *)b;

    // Perform a direct comparison of the 'mtime' values.
    // This approach is robust against potential integer overflows that could
    // occur with simple subtraction (e.g., file_a->mtime - file_b->mtime)
    // if 'time_t' were a signed type and the difference exceeded its range.
    if (file_a->mtime < file_b->mtime) {
        return -1; // 'file_a' comes before 'file_b'
    } else if (file_a->mtime > file_b->mtime) {
        return 1;  // 'file_a' comes after 'file_b'
    }
    return 0;      // 'mtime' values are equal
}

// A convenience function to perform the sorting of an array of FileInfo structures
// using the 'cmp_mtime' comparison function. This improves maintainability by
// encapsulating the qsort call and adding input validation.
void sort_fileinfo_by_mtime(FileInfo *array, size_t count) {
    // Reliability: Validate input parameters to prevent undefined behavior
    // and improve the robustness of the function.
    // qsort expects a non-NULL base pointer and a non-zero count for sorting actions.
    if (array == NULL || count == 0) {
        // If the array pointer is NULL or the count is zero, there is nothing to sort.
        // For a void function, simply returning is the appropriate action.
        // In contexts where this might indicate an error condition, logging a message
        // or returning a status code could be considered if the function signature allowed it.
        return;
    }

    // Security & Maintainability: Call qsort with the correct element size.
    // Using sizeof(FileInfo) ensures that the size is always accurate, even if
    // the FileInfo structure's definition changes in the future.
    qsort(array, count, sizeof(FileInfo), cmp_mtime);
}#include <time.h>

typedef struct {
    char name[256];
    long size;
    time_t mtime;
    int type;
} FileEntry;

static int cmp_mtime(const void *a, const void *b) {
    const FileEntry *entry_a = (const FileEntry *)a;
    const FileEntry *entry_b = (const FileEntry *)b;

    if (entry_a->mtime < entry_b->mtime) {
        return -1;
    } else if (entry_a->mtime > entry_b->mtime) {
        return 1;
    } else {
        return 0;
    }
}#include <stdlib.h>
#include <time.h>
#include <sys/types.h>

typedef struct FileEntry {
    char name[256];
    time_t mtime;
    off_t size;
} FileEntry;

int cmp_mtime(const void *a, const void *b) {
    const FileEntry *entry_a = (const FileEntry *)a;
    const FileEntry *entry_b = (const FileEntry *)b;

    if (entry_a->mtime < entry_b->mtime) {
        return -1;
    } else if (entry_a->mtime > entry_b->mtime) {
        return 1;
    } else {
        return 0;
    }
}

void sort_FileEntry_by_mtime(FileEntry *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(FileEntry), cmp_mtime);
}static int cmp_mtime(const void *a, const void *b) {
    const long val_a = *(const long *)a;
    const long val_b = *(const long *)b;
    if (val_a < val_b) {
        return -1;
    } else if (val_a > val_b) {
        return 1;
    } else {
        return 0;
    }
}#include <stdlib.h>
#include <time.h>

typedef struct {
    time_t mtime;
    int id;
    char name[256];
} MyDataStruct;

#define SORT_MACRO_STRUCT_TYPE MyDataStruct
#define SORT_MACRO_FIELD_TYPE  time_t

#define DEFINE_SORT_FUNCTIONS(FIELD_NAME, CMP_FUNC_NAME) \
    static int CMP_FUNC_NAME(const void *a, const void *b) { \
        const SORT_MACRO_STRUCT_TYPE *elem_a = (const SORT_MACRO_STRUCT_TYPE *)a; \
        const SORT_MACRO_STRUCT_TYPE *elem_b = (const SORT_MACRO_STRUCT_TYPE *)b; \
        \
        if (elem_a->FIELD_NAME < elem_b->FIELD_NAME) { \
            return -1; \
        } else if (elem_a->FIELD_NAME > elem_b->FIELD_NAME) { \
            return 1; \
        } else { \
            return 0; \
        } \
    } \
    \
    void sort_by_ ## FIELD_NAME (SORT_MACRO_STRUCT_TYPE *array, size_t count) { \
        if (array == NULL || count == 0) { \
            return; \
        } \
        qsort(array, count, sizeof(SORT_MACRO_STRUCT_TYPE), CMP_FUNC_NAME); \
    }#include <stddef.h>
#include <stdlib.h>
#include <time.h>
#include <errno.h>
#include <stdio.h>

typedef struct FileInfo {
    time_t mtime;
} FileInfo;

static int compare_file_info_mtime(const void *a, const void *b) {
    const FileInfo *file_a = (const FileInfo *)a;
    const FileInfo *file_b = (const FileInfo *)b;

    if (file_a->mtime < file_b->mtime) {
        return -1;
    } else if (file_a->mtime > file_b->mtime) {
        return 1;
    } else {
        return 0;
    }
}

int sort_file_infos_by_mtime(FileInfo *files, size_t count) {
    if (files == NULL) {
        fprintf(stderr, "Error: sort_file_infos_by_mtime received a NULL array pointer.\n");
        errno = EINVAL;
        return -1;
    }

    if (count <= 1) {
        return 0;
    }

    qsort(files, count, sizeof(FileInfo), compare_file_info_mtime);

    return 0;
}#include <time.h>
#include <stdlib.h>

typedef struct FileEntry {
    char name[256];
    time_t mtime;
    long size;
} FileEntry;

static inline int cmp_mtime(time_t t1, time_t t2) {
    if (t1 < t2) {
        return -1;
    }
    if (t1 > t2) {
        return 1;
    }
    return 0;
}

static int compare_by_mtime(const void *ptr_a, const void *ptr_b) {
    const FileEntry *entry_a = (const FileEntry *)ptr_a;
    const FileEntry *entry_b = (const FileEntry *)ptr_b;
    return cmp_mtime(entry_a->mtime, entry_b->mtime);
}

void sort_mtime(FileEntry *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(FileEntry), compare_by_mtime);
}#include <time.h>

struct FileInfo {
    time_t mtime;
};

int cmp_mtime(const void *a, const void *b) {
    const struct FileInfo *file_a = (const struct FileInfo *)a;
    const struct FileInfo *file_b = (const struct FileInfo *)b;

    if (file_a->mtime < file_b->mtime) {
        return -1;
    } else if (file_a->mtime > file_b->mtime) {
        return 1;
    } else {
        return 0;
    }
}
#include <stdlib.h>

void sort_by_atime(atime *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(atime), cmp_atime);
}#include <stddef.h>
#include <time.h>
#include <stdlib.h>

typedef struct entry {
    time_t atime;
} entry_t;

int cmp_atime(const void *a, const void *b) {
    const entry_t *entry_a = (const entry_t *)a;
    const entry_t *entry_b = (const entry_t *)b;
    if (entry_a->atime < entry_b->atime) {
        return -1;
    } else if (entry_a->atime > entry_b->atime) {
        return 1;
    }
    return 0;
}

void sort_by_atime(entry_t *array, size_t count) {
    if (array == NULL) {
        return;
    }
    if (count == 0) {
        return;
    }
    qsort(array, count, sizeof(entry_t), cmp_atime);
}static int compare_atime_qsort_wrapper(const void *element_a, const void *element_b) {
    const atime *item_a = (const atime *)element_a;
    const atime *item_b = (const atime *)element_b;
    return cmp_atime(item_a, item_b);
}

void sort_atime_array(atime *array, size_t count) {
    if (array == NULL) {
        if (count > 0) {
        }
        return;
    }

    if (count == 0) {
        return;
    }

    qsort(array, count, sizeof(atime), compare_atime_qsort_wrapper);
}typedef struct {
    long long atime;
} SortableItem_t;

int cmp_atime(const void *a, const void *b) {
    const SortableItem_t *item_a = (const SortableItem_t *)a;
    const SortableItem_t *item_b = (const SortableItem_t *)b;

    if (item_a->atime < item_b->atime) {
        return -1;
    } else if (item_a->atime > item_b->atime) {
        return 1;
    } else {
        return 0;
    }
}#include <stdlib.h>
#include <time.h>

typedef struct entry {
    int id;
    time_t atime;
    // Other members of the structure can be defined here
} entry_t;

static int cmp_atime(const void *a, const void *b) {
    const entry_t *entry_a = (const entry_t *)a;
    const entry_t *entry_b = (const entry_t *)b;

    if (entry_a->atime < entry_b->atime) {
        return -1;
    } else if (entry_a->atime > entry_b->atime) {
        return 1;
    } else {
        return 0;
    }
}

void sort_entries_by_atime(entry_t *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(entry_t), cmp_atime);
}#include <stddef.h>
#include <stdlib.h>
#include <time.h>

typedef struct LogEntry {
    int id;
    time_t atime;
} LogEntry;

static int compareLogEntryByAtime(const void *a, const void *b) {
    const LogEntry *entry_a = (const LogEntry *)a;
    const LogEntry *entry_b = (const LogEntry *)b;

    if (entry_a->atime < entry_b->atime) {
        return -1;
    } else if (entry_a->atime > entry_b->atime) {
        return 1;
    } else {
        return 0;
    }
}

void sortLogEntriesByAtime(LogEntry *array, size_t num_elements) {
    if (array == NULL && num_elements > 0) {
        return;
    }
    qsort(array, num_elements, sizeof(LogEntry), compareLogEntryByAtime);
}#include <stdlib.h>
#include <stddef.h>

struct atime {
    long timestamp;
};

int cmp_atime(const void *ptr_a, const void *ptr_b) {
    const struct atime *a = (const struct atime *)ptr_a;
    const struct atime *b = (const struct atime *)ptr_b;

    if (a->timestamp < b->timestamp) {
        return -1;
    } else if (a->timestamp > b->timestamp) {
        return 1;
    } else {
        return 0;
    }
}

void sort_atime_array(struct atime *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }

    qsort(array, count, sizeof(struct atime), cmp_atime);
}#include <time.h>
#include <stdlib.h>

typedef struct {
    int id;
    char name[256];
    time_t atime;
    long size;
} FileEntry;

int cmp_atime(const void *a, const void *b) {
    const FileEntry *entry_a = (const FileEntry *)a;
    const FileEntry *entry_b = (const FileEntry *)b;

    if (entry_a->atime < entry_b->atime) {
        return -1;
    } else if (entry_a->atime > entry_b->atime) {
        return 1;
    } else {
        return 0;
    }
}
#include <stdlib.h>

typedef struct {
    long btime;
} DataItem;

int cmp_btime(const void *a, const void *b) {
    const DataItem *item_a = (const DataItem *)a;
    const DataItem *item_b = (const DataItem *)b;

    if (item_a->btime < item_b->btime) {
        return -1;
    } else if (item_a->btime > item_b->btime) {
        return 1;
    }
    return 0;
}

void sort_data_items_by_btime(DataItem *array, size_t count) {
    if (array == NULL && count > 0) {
        return;
    }
    if (count <= 1) {
        return;
    }
    qsort(array, count, sizeof(DataItem), cmp_btime);
}#include <stdlib.h>
#include <stddef.h>

int cmp_btime(const void *a_ptr, const void *b_ptr) {
    const btime *a = (const btime *)a_ptr;
    const btime *b = (const btime *)b_ptr;
    if (*a < *b) {
        return -1;
    } else if (*a > *b) {
        return 1;
    } else {
        return 0;
    }
}

void sort_btime_array(btime *array, size_t count) {
    if (array == NULL) {
        return;
    }
    qsort(array, count, sizeof(btime), cmp_btime);
}void sort_btime_array(btime *arr, size_t count) {
    if (arr == NULL || count == 0) {
        return;
    }
    qsort(arr, count, sizeof(btime), cmp_btime);
}#include <stdlib.h>

typedef struct {
    long btime;
} Record;

int cmp_btime(const void *a, const void *b) {
    const Record *itemA = (const Record *)a;
    const Record *itemB = (const Record *)b;
    if (itemA->btime < itemB->btime) {
        return -1;
    } else if (itemA->btime > itemB->btime) {
        return 1;
    } else {
        return 0;
    }
}

void sort_records_by_btime(Record *records, size_t count) {
    if (records == NULL || count == 0) {
        return;
    }
    qsort(records, count, sizeof(Record), cmp_btime);
}#include <stddef.h>
#include <stdlib.h>

typedef long long btime_t;

int cmp_btime(const void *a, const void *b) {
    const btime_t *pa = (const btime_t *)a;
    const btime_t *pb = (const btime_t *)b;
    if (*pa < *pb) {
        return -1;
    } else if (*pa > *pb) {
        return 1;
    } else {
        return 0;
    }
}

void sort_btime_array(btime_t *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(btime_t), cmp_btime);
}typedef struct {
    long btime;
} record_t;

int cmp_btime(const void *ptr_a, const void *ptr_b) {
    const record_t *record_a = (const record_t *)ptr_a;
    const record_t *record_b = (const record_t *)ptr_b;

    long btime_a = record_a->btime;
    long btime_b = record_b->btime;

    if (btime_a < btime_b) {
        return -1;
    } else if (btime_a > btime_b) {
        return 1;
    } else {
        return 0;
    }
}#include <stdlib.h>
#include <stddef.h>

#define DEFINE_SORT_FUNCTIONS(TYPE, CMP_FUNC) \
static int qsort_compare_ ## TYPE (const void *a, const void *b) { \
    const TYPE *val_a = (const TYPE *)a; \
    const TYPE *val_b = (const TYPE *)b; \
    return CMP_FUNC(*val_a, *val_b); \
} \
\
void sort_ ## TYPE ## _array(TYPE *array, size_t count) { \
    if (array == NULL || count == 0) { \
        return; \
    } \
    qsort(array, count, sizeof(TYPE), qsort_compare_ ## TYPE); \
}typedef struct {
    long long btime;
} record_t;

int cmp_btime(const void *a, const void *b) {
    const record_t *elem_a = (const record_t *)a;
    const record_t *elem_b = (const record_t *)b;

    if (elem_a->btime < elem_b->btime) {
        return -1;
    } else if (elem_a->btime > elem_b->btime) {
        return 1;
    }
    return 0;
}

void sort_records_by_btime(record_t *records, size_t count) {
    if (records == NULL || count == 0) {
        return;
    }
    qsort(records, count, sizeof(record_t), cmp_btime);
}
#include <stdlib.h>
#include <stddef.h>

void safe_generic_sort(void *base, size_t num, size_t width, int (*compare)(const void *, const void *))
{
    if (base == NULL || compare == NULL || num == 0 || width == 0) {
        return;
    }
    qsort(base, num, width, compare);
}#include <stdlib.h>
#include <stddef.h>

void sort_generic_elements(void* base, size_t num_elements, size_t element_size,
                       int (*compare_func)(const void*, const void*)) {
    if (base == NULL || num_elements == 0 || element_size == 0 || compare_func == NULL) {
        return;
    }
    qsort(base, num_elements, element_size, compare_func);
}#include <stddef.h>
#include <stdlib.h>

static int internal_qsort_wrapper_for_size_t(const void *a, const void *b) {
    return cmp_size(*(const size_t *)a, *(const size_t *)b);
}

void sort_size(size_t *array, size_t count) {
    if (array == NULL && count > 0) {
        return;
    }

    if (count <= 1) {
        return;
    }

    qsort(array, count, sizeof(size_t), internal_qsort_wrapper_for_size_t);
}#include <stddef.h>
#include <stdlib.h>

typedef int (*comparison_fn_ptr)(const void *, const void *);

static void _swap_elements(char *a, char *b, size_t element_size) {
    if (a == b) {
        return;
    }
    for (size_t i = 0; i < element_size; ++i) {
        char temp = a[i];
        a[i] = b[i];
        b[i] = temp;
    }
}

static long _qsort_partition(char *base_ptr, long low, long high, size_t element_size, comparison_fn_ptr compar) {
    char *pivot_ptr = base_ptr + high * element_size;
    long i = low - 1;

    for (long j = low; j < high; j++) {
        char *current_ptr = base_ptr + j * element_size;
        if (compar(current_ptr, pivot_ptr) <= 0) {
            i++;
            char *i_ptr = base_ptr + i * element_size;
            _swap_elements(i_ptr, current_ptr, element_size);
        }
    }

    char *i_plus_1_ptr = base_ptr + (i + 1) * element_size;
    _swap_elements(i_plus_1_ptr, pivot_ptr, element_size);

    return i + 1;
}

static void _qsort_recursive(char *base_ptr, long low, long high, size_t element_size, comparison_fn_ptr compar) {
    if (low < high) {
        long pi = _qsort_partition(base_ptr, low, high, element_size, compar);
        _qsort_recursive(base_ptr, low, pi - 1, element_size, compar);
        _qsort_recursive(base_ptr, pi + 1, high, element_size, compar);
    }
}

void generic_qsort_improved(void *base, size_t num, size_t element_size, comparison_fn_ptr compar) {
    if (base == NULL || num <= 1 || element_size == 0 || compar == NULL) {
        return;
    }
    char *base_as_char = (char *)base;
    _qsort_recursive(base_as_char, 0, (long)num - 1, element_size, compar);
}#include <stdlib.h>
#include <stddef.h>

void generic_array_sort(void *base, size_t num_elements, size_t element_size,
                        int (*compare_func)(const void *, const void *)) {
    if (base == NULL || compare_func == NULL) {
        return;
    }
    if (num_elements == 0 || element_size == 0) {
        return;
    }
    qsort(base, num_elements, element_size, compare_func);
}#define DEFINE_SORT_FUNCTIONS(type, cmp_func) \
static int _qsort_helper_##type##_cmp(const void *a, const void *b) { \
    return cmp_func((const type *)a, (const type *)b); \
} \
void sort_##type##_array(type *arr, size_t count) { \
    if (arr == NULL && count > 0) { \
        return; \
    } \
    qsort(arr, count, sizeof(type), _qsort_helper_##type##_cmp); \
}#ifndef _GENERIC_SORT_H_
#define _GENERIC_SORT_H_

#include <stddef.h>
#include <string.h>

#ifndef QUICK_SORT_INSERTION_SORT_THRESHOLD
#define QUICK_SORT_INSERTION_SORT_THRESHOLD 16
#endif

typedef int (*_generic_sort_cmp_func_t)(const void *, const void *);

#define DEFINE_SORT_FUNCTIONS(size, cmp_size) \
                                                                \
static void _##size##_swap(char *a, char *b, size_t _element_size_internal) { \
    if (a == b) {                                               \
        return;                                                 \
    }                                                           \
    char temp[_element_size_internal];                          \
    memcpy(temp, a, _element_size_internal);                    \
    memcpy(a, b, _element_size_internal);                       \
    memcpy(b, temp, _element_size_internal);                    \
}                                                               \
                                                                \
static void _##size##_insertionsort(char *base, size_t num_elements, size_t _element_size_internal, _generic_sort_cmp_func_t _cmp_func_internal) { \
    if (num_elements < 2) {                                     \
        return;                                                 \
    }                                                           \
                                                                \
    for (size_t i = 1; i < num_elements; ++i) {                 \
        char *key_ptr = base + i * _element_size_internal;      \
        char temp_key[_element_size_internal];                  \
        memcpy(temp_key, key_ptr, _element_size_internal);      \
                                                                \
        size_t j = i;                                           \
        char *prev_ptr_pos = base + (j - 1) * _element_size_internal; \
                                                                \
        while (j > 0 && _cmp_func_internal(prev_ptr_pos, temp_key) > 0) { \
            memcpy(base + j * _element_size_internal, prev_ptr_pos, _element_size_internal); \
            j--;                                                \
            if (j > 0) {                                        \
                prev_ptr_pos = base + (j - 1) * _element_size_internal; \
            }                                                   \
        }                                                       \
        memcpy(base + j * _element_size_internal, temp_key, _element_size_internal); \
    }                                                           \
}                                                               \
                                                                \
static size_t _##size##_median_of_three_pivot_selection(char *base, size_t low, size_t high, size_t _element_size_internal, _generic_sort_cmp_func_t _cmp_func_internal) { \
    size_t mid = low + (high - low) / 2;                        \
                                                                \
    if (_cmp_func_internal(base + low * _element_size_internal, base + mid * _element_size_internal) > 0) { \
        _##size##_swap(base + low * _element_size_internal, base + mid * _element_size_internal, _element_size_internal); \
    }                                                           \
    if (_cmp_func_internal(base + low * _element_size_internal, base + high * _element_size_internal) > 0) { \
        _##size##_swap(base + low * _element_size_internal, base + high * _element_size_internal, _element_size_internal); \
    }                                                           \
    if (_cmp_func_internal(base + mid * _element_size_internal, base + high * _element_size_internal) > 0) { \
        _##size##_swap(base + mid * _element_size_internal, base + high * _element_size_internal, _element_size_internal); \
    }                                                           \
                                                                \
    _##size##_swap(base + mid * _element_size_internal, base + (high - 1) * _element_size_internal, _element_size_internal); \
    return high - 1;                                            \
}                                                               \
                                                                \
static size_t _##size##_partition(char *base, size_t low, size_t high, size_t _element_size_internal, _generic_sort_cmp_func_t _cmp_func_internal) { \
    size_t pivot_idx = _##size##_median_of_three_pivot_selection(base, low, high, _element_size_internal, _cmp_func_internal); \
                                                                \
    _##size##_swap(base + pivot_idx * _element_size_internal, base + high * _element_size_internal, _element_size_internal); \
    char *pivot_val_ptr = base + high * _element_size_internal; \
                                                                \
    size_t store_idx = low;                                     \
    for (size_t j = low; j < high; ++j) {                       \
        if (_cmp_func_internal(base + j * _element_size_internal, pivot_val_ptr) <= 0) { \
            _##size##_swap(base + store_idx * _element_size_internal, base + j * _element_size_internal, _element_size_internal); \
            store_idx++;                                        \
        }                                                       \
    }                                                           \
    _##size##_swap(base + store_idx * _element_size_internal, base + high * _element_size_internal, _element_size_internal); \
    return store_idx;                                           \
}                                                               \
                                                                \
static void _##size##_quicksort_recursive(char *base, size_t low, size_t high, size_t _element_size_internal, _generic_sort_cmp_func_t _cmp_func_internal) { \
    while (low < high) {                                        \
        if (high - low + 1 < QUICK_SORT_INSERTION_SORT_THRESHOLD) { \
            _##size##_insertionsort(base + low * _element_size_internal, high - low + 1, _element_size_internal, _cmp_func_internal); \
            return;                                             \
        }                                                       \
                                                                \
        size_t pi = _##size##_partition(base, low, high, _element_size_internal, _cmp_func_internal); \
                                                                \
        if (pi - low < high - pi) {                             \
            _##size##_quicksort_recursive(base, low, pi - 1, _element_size_internal, _cmp_func_internal); \
            low = pi + 1;                                       \
        } else {                                                \
            _##size##_quicksort_recursive(base, pi + 1, high, _element_size_internal, _cmp_func_internal); \
            high = pi - 1;                                      \
        }                                                       \
    }                                                           \
}                                                               \
                                                                \
void sort_##size(void *base, size_t nmemb, _generic_sort_cmp_func_t cmp_size) { \
    if (base == NULL || nmemb == 0) {                           \
        return;                                                 \
    }                                                           \
    if (size == 0) {                                            \
        return;                                                 \
    }                                                           \
                                                                \
    if (nmemb < QUICK_SORT_INSERTION_SORT_THRESHOLD) {          \
        _##size##_insertionsort((char *)base, nmemb, size, cmp_size); \
        return;                                                 \
    }                                                           \
                                                                \
    _##size##_quicksort_recursive((char *)base, 0, nmemb - 1, size, cmp_size); \
}

#endiftypedef unsigned long size_t;

extern void qsort(void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));

typedef int (*ComparisonFunction)(const void *, const void *);

void perform_generic_sort(void *array, size_t num_elements, size_t element_size, ComparisonFunction compare) {
    if (array == 0 || element_size == 0 || compare == 0) {
        return;
    }
    qsort(array, num_elements, element_size, compare);
}

int compare_integers_asc(const void *a, const void *b) {
    const int *val_a = (const int *)a;
    const int *val_b = (const int *)b;

    if (*val_a < *val_b) {
        return -1;
    } else if (*val_a > *val_b) {
        return 1;
    } else {
        return 0;
    }
}
#include <stdlib.h>
#include <stddef.h>

typedef struct {
    int id;
    const char *name;
} DataEntry;

static int compare_data_entries_by_id(const void *a, const void *b) {
    const DataEntry *entry_a = (const DataEntry *)a;
    const DataEntry *entry_b = (const DataEntry *)b;

    if (entry_a->id < entry_b->id) {
        return -1;
    } else if (entry_a->id > entry_b->id) {
        return 1;
    } else {
        return 0;
    }
}

void sort_data_entry_array(DataEntry *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }

    qsort(array, count, sizeof(DataEntry), compare_data_entries_by_id);
}#include <stddef.h>

typedef struct {
    int id;
    double value;
} Measurement;

int compare_measurements(const Measurement *a, const Measurement *b) {
    if (a->id < b->id) return -1;
    if (a->id > b->id) return 1;
    if (a->value < b->value) return -1;
    if (a->value > b->value) return 1;
    return 0;
}

static void swap_Measurement(Measurement *a, Measurement *b) {
    Measurement temp = *a;
    *a = *b;
    *b = temp;
}

static size_t partition_Measurement(Measurement *array, size_t low, size_t high) {
    const Measurement pivot_value = array[high];
    size_t i = low;

    for (size_t j = low; j < high; ++j) {
        if (compare_measurements(&array[j], &pivot_value) <= 0) {
            swap_Measurement(&array[i], &array[j]);
            i++;
        }
    }
    swap_Measurement(&array[i], &array[high]);
    return i;
}

static void quick_sort_recursive_Measurement(Measurement *array, size_t low, size_t high) {
    if (low < high) {
        size_t pi = partition_Measurement(array, low, high);

        if (pi > low) {
            quick_sort_recursive_Measurement(array, low, pi - 1);
        }
        quick_sort_recursive_Measurement(array, pi + 1, high);
    }
}

void sort_Measurement(Measurement *array, size_t count) {
    if (array == NULL || count < 2) {
        return;
    }
    quick_sort_recursive_Measurement(array, 0, count - 1);
}#include <stddef.h>
#include <stdlib.h>

typedef struct {
    int id;
    char name[128];
    float price;
} Product;

static int compare_Product_by_id(const void *a, const void *b) {
    const Product *productA = (const Product *)a;
    const Product *productB = (const Product *)b;

    if (productA->id < productB->id) {
        return -1;
    }
    if (productA->id > productB->id) {
        return 1;
    }
    return 0;
}

void sort_Product_array(Product *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(Product), compare_Product_by_id);
}#include <stdlib.h>

#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
    static inline void sort_array_of_##name(name *array, size_t count) { \
        if (array == NULL || count == 0) { \
            return; \
        } \
        qsort(array, count, sizeof(name), cmp_name); \
    }#include <stdlib.h>
#include <stddef.h>

void sort_DataStruct_array(DataStruct* array, size_t num_elements) {
    if (array == NULL && num_elements > 0) {
        return;
    }

    if (num_elements == 0) {
        return;
    }

    qsort(array, num_elements, sizeof(DataStruct), (int (*)(const void*, const void*))compareDataStructs);
}#include <stddef.h>
#include <stdlib.h>
#include <string.h>

struct MyRecord {
    int id;
    char *name_field;
};

int compare_myrecord_by_id(const void *a, const void *b) {
    const struct MyRecord *record_a = (const struct MyRecord *)a;
    const struct MyRecord *record_b = (const struct MyRecord *)b;
    return record_a->id - record_b->id;
}

int compare_myrecord_by_name_field(const void *a, const void *b) {
    const struct MyRecord *record_a = (const struct MyRecord *)a;
    const struct MyRecord *record_b = (const struct MyRecord *)b;

    if (record_a->name_field == NULL && record_b->name_field == NULL) {
        return 0;
    }
    if (record_a->name_field == NULL) {
        return -1;
    }
    if (record_b->name_field == NULL) {
        return 1;
    }
    return strcmp(record_a->name_field, record_b->name_field);
}

void sort_myrecords(struct MyRecord *array, size_t num_elements,
                    int (*comparator)(const void *, const void *)) {
    if (array == NULL || num_elements == 0 || comparator == NULL) {
        return;
    }
    qsort(array, num_elements, sizeof(struct MyRecord), comparator);
}#include <stdlib.h> // Required for qsort
#include <stddef.h> // Required for size_t
#include <stdbool.h> // Required for bool type

// To make the generated code compilable and illustrate refactoring principles,
// we'll define a placeholder type and a placeholder comparison function.
// In a real scenario, 'name' would be substituted with an actual type (e.g., 'struct Person'),
// and 'cmp_name' with a concrete comparison function (e.g., 'compare_persons_by_id').

// Placeholder for the type 'name' that the macro would operate on.
// This structure demonstrates common data types that might be sorted.
typedef struct {
    int id;
    const char *data;
} PlaceholderType;

// Placeholder for the comparison function 'cmp_name'.
// This function strictly adheres to the qsort comparison signature.
// It includes defensive checks and clear comparison logic.
static int placeholder_compare_func(const void *a, const void *b) {
    // Type casting with const for safety and clarity
    const PlaceholderType *elem_a = (const PlaceholderType *)a;
    const PlaceholderType *elem_b = (const PlaceholderType *)b;

    // Reliability: Defensive checks against unexpected NULL pointers.
    // While qsort generally ensures valid pointers, explicit checks improve robustness
    // if this comparison function were used outside qsort or with malformed inputs.
    // For sorting, a common approach is to place NULL elements at one end.
    if (elem_a == NULL && elem_b == NULL) {
        return 0; // Both are "equal" in terms of nullness
    }
    if (elem_a == NULL) {
        return -1; // Place NULL 'a' before non-NULL 'b'
    }
    if (elem_b == NULL) {
        return 1; // Place non-NULL 'a' after NULL 'b'
    }

    // Main comparison logic based on 'id' field
    if (elem_a->id < elem_b->id) {
        return -1;
    }
    if (elem_a->id > elem_b->id) {
        return 1;
    }

    // If IDs are equal, consider comparing 'data' for stable sort (optional)
    // For simplicity, we assume 'id' is sufficient for ordering.
    // return 0; // IDs are equal
    // int data_cmp = strcmp(elem_a->data, elem_b->data);
    // return data_cmp;

    return 0;
}

// Refactored sort function that the DEFINE_SORT_FUNCTIONS macro would generate.
// It now includes improved reliability and maintainability features.
// The function name is made explicit to reflect the type being sorted.
bool sort_placeholder_type_array_safe(PlaceholderType *array, size_t count) {
    // Reliability: Input validation for common error conditions.
    // Checking for NULL array pointer.
    if (array == NULL) {
        // In a real application, an error message would be logged here.
        // For sorting, a NULL array is an invalid input.
        return false; // Indicate failure to sort
    }

    // Reliability: Handle empty arrays gracefully.
    // Sorting an empty array is a no-op but not an error.
    if (count == 0) {
        return true; // Consider it a successful (empty) sort
    }

    // Security & Maintainability: Use standard library's qsort, which is robust
    // and efficient. Ensure correct parameters are passed.
    // The 'placeholder_compare_func' is cast to the expected type by qsort.
    qsort(array, count, sizeof(PlaceholderType), placeholder_compare_func);

    return true; // Indicate successful sorting
}#include <stdlib.h>
#include <stddef.h>

#define DEFINE_SORT_FUNCTIONS(TYPE, CMP_FUNC) \
    void sort_##TYPE##_array(TYPE *array, size_t count) { \
        if (array == NULL || count == 0) { \
            return; \
        } \
        qsort(array, count, sizeof(TYPE), CMP_FUNC); \
    }
#define DEFINE_SORT_FUNCTIONS(extension, cmp_extension) \
    typedef extension extension ## _t; \
    typedef extension ## _t* extension ## _array_t; \
\
    static int qsort_wrapper_ ## extension ## _cmp(const void *a, const void *b) { \
        const extension ## _t *pa = (const extension ## _t *)a; \
        const extension ## _t *pb = (const extension ## _t *)b; \
        return cmp_extension(pa, pb); \
    } \
\
    void sort_ ## extension ## _array(extension ## _array_t array, size_t count) { \
        if (array == NULL && count > 0) { \
            return; \
        } \
        qsort(array, count, sizeof(extension ## _t), qsort_wrapper_ ## extension ## _cmp); \
    }void sort_extension(extension *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(extension), cmp_extension);
}#include <stdlib.h>

// Define the 'extension' type explicitly.
// This is an example placeholder; in actual code, 'extension'
// would be an existing struct, typedef, or fundamental type.
typedef struct {
    int id;
    // Potentially other members that might be used for sorting
    // int value;
    // char name[64];
} extension;

// Comparison function for 'extension' types.
// This function implements the logic for ordering 'extension' objects,
// typically used by qsort. It must adhere to qsort's comparator signature.
int cmp_extension(const void *a, const void *b) {
    const extension *ext_a = (const extension *)a;
    const extension *ext_b = (const extension *)b;

    // Standard comparison logic. Avoids subtraction for robustness against
    // potential integer overflow if 'id' were a very large/small type.
    if (ext_a->id < ext_b->id) {
        return -1;
    } else if (ext_a->id > ext_b->id) {
        return 1;
    } else {
        return 0;
    }
}

// Sort function for an array of 'extension' types.
// This function provides a robust wrapper around qsort, including
// necessary input validation to prevent common errors and improve reliability.
void sort_extension_array(extension *array, size_t count) {
    // Validate inputs to ensure safety and prevent undefined behavior.
    // A NULL array or zero count indicates nothing to sort,
    // so the function can safely return without action.
    if (array == NULL || count == 0) {
        return;
    }

    // Call the standard library's quicksort function.
    // Parameters: base address of the array, number of elements,
    // size of each element, and the comparison function.
    qsort(array, count, sizeof(extension), cmp_extension);
}#include <stdlib.h>
#include <stddef.h>

static int internal_qsort_cmp_extension(const void *a, const void *b) {
    return cmp_extension((const extension *)a, (const extension *)b);
}

void sort_extension(extension *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(extension), internal_qsort_cmp_extension);
}static int cmp_extension_qsort_wrapper(const void *a, const void *b) {
    return cmp_extension((const extension *)a, (const extension *)b);
}

void sort_extension_array(extension *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }

    qsort(array, count, sizeof(extension), cmp_extension_qsort_wrapper);
}void sort_extension_array(extension *arr, size_t count) {
    if (arr == NULL || count <= 1) {
        return;
    }
    qsort(arr, count, sizeof(extension), (int (*)(const void *, const void *))cmp_extension);
}#define DEFINE_SORT_FUNCTIONS(TYPE, USER_COMPARISON_FUNCTION) \
    static int _internal_qsort_cmp_ ## TYPE (const void* ptr_a, const void* ptr_b) { \
        const TYPE* val_a = (const TYPE*)ptr_a; \
        const TYPE* val_b = (const TYPE*)ptr_b; \
        return USER_COMPARISON_FUNCTION(val_a, val_b); \
    } \
    void sort_ ## TYPE ## s (TYPE* array, size_t num_elements) { \
        if (array == NULL || num_elements == 0) { \
            return; \
        } \
        qsort(array, num_elements, sizeof(TYPE), _internal_qsort_cmp_ ## TYPE); \
    }#include <stdlib.h>

#define DEFINE_SORT_FUNCTIONS(extension, cmp_extension) \
    \
    static int cmp_ ## extension ## _qsort_wrapper(const void* a, const void* b) { \
        return cmp_extension((const extension*)a, (const extension*)b); \
    } \
    \
    int sort_ ## extension ## _array(extension* array, size_t count) { \
        if (array == NULL) { \
            return -1; \
        } \
        if (count <= 1) { \
            return 0; \
        } \
        qsort(array, count, sizeof(extension), cmp_ ## extension ## _qsort_wrapper); \
        return 0; \
    } \
    \
    int is_ ## extension ## _array_sorted(const extension* array, size_t count) { \
        if (array == NULL) { \
            return -1; \
        } \
        if (count <= 1) { \
            return 1; \
        } \
        for (size_t i = 0; i < count - 1; ++i) { \
            if (cmp_extension(&array[i], &array[i+1]) > 0) { \
                return 0; \
            } \
        } \
        return 1; \
    }
#include <stdlib.h>
#include <stddef.h>

void generic_sort(void *base, size_t num, size_t size, int (*compar)(const void *, const void *)) {
    if (base == NULL || compar == NULL || num == 0 || size == 0) {
        return;
    }
    qsort(base, num, size, compar);
}#include <stdlib.h>
#include <stddef.h>
#include <string.h>

void perform_generic_sort(void *base_ptr, size_t num_elements, size_t element_size,
                          int (*compare_func)(const void *, const void *)) {
    if (num_elements > 0 && base_ptr == NULL) {
        return;
    }
    qsort(base_ptr, num_elements, element_size, compare_func);
}

int compare_integers(const void *a, const void *b) {
    const int *ia = (const int *)a;
    const int *ib = (const int *)b;
    if (*ia < *ib) {
        return -1;
    }
    if (*ia > *ib) {
        return 1;
    }
    return 0;
}

typedef struct {
    int id;
    char name[64];
} Entry;

int compare_entries_by_id(const void *a, const void *b) {
    const Entry *ea = (const Entry *)a;
    const Entry *eb = (const Entry *)b;
    if (ea->id < eb->id) {
        return -1;
    }
    if (ea->id > eb->id) {
        return 1;
    }
    return 0;
}#include <stddef.h>
#include <stdlib.h>

void safe_generic_sort(void *base, size_t num_elements, size_t element_size,
                       int (*compare_func)(const void *, const void *))
{
    if (num_elements == 0 || element_size == 0 || compare_func == NULL) {
        return;
    }

    if (base == NULL) {
        return;
    }

    qsort(base, num_elements, element_size, compare_func);
}#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

void sort_elements(void* base, size_t num_elements, size_t element_size,
                   int (*compare_func)(const void*, const void*)) {
    if (compare_func == NULL) {
        fprintf(stderr, "Error: sort_elements called with NULL comparison function.\n");
        errno = EINVAL;
        return;
    }

    if (num_elements == 0) {
        return; // Nothing to sort
    }

    if (base == NULL) {
        fprintf(stderr, "Error: sort_elements called with NULL base pointer for %zu elements.\n", num_elements);
        errno = EINVAL;
        return;
    }
    
    if (element_size == 0) {
        fprintf(stderr, "Error: sort_elements called with element_size 0 for %zu elements.\n", num_elements);
        errno = EINVAL;
        return;
    }

    qsort(base, num_elements, element_size, compare_func);
}#include <stddef.h>
#include <string.h>

#define DEFINE_SORT_FUNCTIONS(width, cmp_width) \
\
static inline void INTERNAL_swap_elements_##width(char *a, char *b, size_t elem_size) { \
    if (a == b) { \
        return; \
    } \
    char temp[width]; \
    memcpy(temp, a, elem_size); \
    memcpy(a, b, elem_size); \
    memcpy(b, temp, elem_size); \
} \
\
static size_t INTERNAL_partition_##width(char *base, size_t low, size_t high, size_t elem_size, \
                                         int (*compare)(const void *, const void *)) { \
    char *pivot_ptr = base + high * elem_size; \
    size_t i = low; \
\
    for (size_t j = low; j < high; ++j) { \
        if (compare(base + j * elem_size, pivot_ptr) < 0) { \
            INTERNAL_swap_elements_##width(base + i * elem_size, base + j * elem_size, elem_size); \
            i++; \
        } \
    } \
    INTERNAL_swap_elements_##width(base + i * elem_size, pivot_ptr, elem_size); \
    return i; \
} \
\
static void INTERNAL_quick_sort_iterative_##width(void *base_ptr, size_t num_elements, size_t elem_size, \
                                                    int (*compare)(const void *, const void *)) { \
    char *base = (char *)base_ptr; \
\
    if (base == NULL || num_elements < 2 || compare == NULL) { \
        return; \
    } \
\
    struct { \
        size_t low; \
        size_t high; \
    } stack[128]; \
\
    int top = -1; \
\
    stack[++top].low = 0; \
    stack[top].high = num_elements - 1; \
\
    while (top >= 0) { \
        size_t low = stack[top].low; \
        size_t high = stack[top--].high; \
\
        if (low < high) { \
            if (high - low + 1 < 10) { \
                for (size_t i = low + 1; i <= high; ++i) { \
                    char *key_ptr = base + i * elem_size; \
                    size_t j = i; \
                    while (j > low && compare(base + (j - 1) * elem_size, key_ptr) > 0) { \
                        INTERNAL_swap_elements_##width(base + j * elem_size, base + (j - 1) * elem_size, elem_size); \
                        j--; \
                    } \
                } \
                continue; \
            } \
\
            size_t pivot_index = INTERNAL_partition_##width(base, low, high, elem_size, compare); \
\
            if (pivot_index > low && pivot_index - low > high - pivot_index) { \
                if (pivot_index < high) { \
                    stack[++top].low = pivot_index + 1; \
                    stack[top].high = high; \
                } \
                if (pivot_index > low) { \
                    stack[++top].low = low; \
                    stack[top].high = pivot_index - 1; \
                } \
            } else { \
                if (pivot_index > low) { \
                    stack[++top].low = low; \
                    stack[top].high = pivot_index - 1; \
                } \
                if (pivot_index < high) { \
                    stack[++top].low = pivot_index + 1; \
                    stack[top].high = high; \
                } \
            } \
        } \
    } \
} \
\
void sort_##width(void *base, size_t num_elements) { \
    if (base == NULL || num_elements < 2) { \
        return; \
    } \
    INTERNAL_quick_sort_iterative_##width(base, num_elements, width, cmp_width); \
}#include <stddef.h>
#include <string.h>

#define DEFINE_SORT_FUNCTIONS(ELEMENT_WIDTH_TOKEN, COMPARE_FUNC_TOKEN) \
\
static void _qsort_swap_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(char *a, char *b) { \
    char temp_buffer[ELEMENT_WIDTH_TOKEN]; \
    memcpy(temp_buffer, a, ELEMENT_WIDTH_TOKEN); \
    memcpy(a, b, ELEMENT_WIDTH_TOKEN); \
    memcpy(b, temp_buffer, ELEMENT_WIDTH_TOKEN); \
} \
\
static long _qsort_partition_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(char *base_ptr, long low_idx, long high_idx) { \
    char *pivot_element_ptr = base_ptr + high_idx * ELEMENT_WIDTH_TOKEN; \
    long i = (low_idx - 1); \
\
    for (long j = low_idx; j < high_idx; j++) { \
        char *current_element_ptr = base_ptr + j * ELEMENT_WIDTH_TOKEN; \
        if (COMPARE_FUNC_TOKEN(current_element_ptr, pivot_element_ptr) <= 0) { \
            i++; \
            if (i != j) { \
                _qsort_swap_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(base_ptr + i * ELEMENT_WIDTH_TOKEN, current_element_ptr); \
            } \
        } \
    } \
    long pivot_final_idx = i + 1; \
    if (pivot_final_idx != high_idx) { \
        _qsort_swap_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(base_ptr + pivot_final_idx * ELEMENT_WIDTH_TOKEN, base_ptr + high_idx * ELEMENT_WIDTH_TOKEN); \
    } \
    return pivot_final_idx; \
} \
\
static void _qsort_recursive_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(char *base_ptr, long low_idx, long high_idx) { \
    if (low_idx < high_idx) { \
        long partition_index = _qsort_partition_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(base_ptr, low_idx, high_idx); \
        _qsort_recursive_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(base_ptr, low_idx, partition_index - 1); \
        _qsort_recursive_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN(base_ptr, partition_index + 1, high_idx); \
    } \
} \
\
void sort_array_with_##ELEMENT_WIDTH_TOKEN##_and_##COMPARE_FUNC_TOKEN(void *base, size_t num_elements) { \
    if (base == NULL || num_elements == 0) { \
        return; \
    } \
    _qsort_recursive_##ELEMENT_WIDTH_TOKEN##_##COMPARE_FUNC_TOKEN((char *)base, 0, (long)num_elements - 1); \
}DEFINE_SORT_FUNCTIONS (width, cmp_width)#include <stddef.h>
#include <string.h>

static inline void _sonar_generic_swap(void *a, void *b, size_t size) {
    if (a == NULL || b == NULL || size == 0) {
        return;
    }
    if (a == b) {
        return;
    }
    unsigned char *ptr_a = (unsigned char *)a;
    unsigned char *ptr_b = (unsigned char *)b;
    for (size_t i = 0; i < size; ++i) {
        unsigned char temp = ptr_a[i];
        ptr_a[i] = ptr_b[i];
        ptr_b[i] = temp;
    }
}

static size_t _sonar_qsort_partition(
    void *base,
    size_t element_size,
    int (*compar)(const void *, const void *),
    size_t low_idx,
    size_t high_idx
) {
    unsigned char *arr = (unsigned char *)base;
    unsigned char pivot_buffer[element_size];
    memcpy(pivot_buffer, arr + high_idx * element_size, element_size);

    size_t i = low_idx;

    for (size_t j = low_idx; j < high_idx; ++j) {
        if (compar(arr + j * element_size, pivot_buffer) <= 0) {
            _sonar_generic_swap(arr + i * element_size, arr + j * element_size, element_size);
            i++;
        }
    }

    _sonar_generic_swap(arr + i * element_size, arr + high_idx * element_size, element_size);
    return i;
}

static void _sonar_qsort_recursive_impl(
    void *base,
    size_t element_size,
    int (*compar)(const void *, const void *),
    size_t low_idx,
    size_t high_idx
) {
    if (low_idx >= high_idx) {
        return;
    }

    size_t pivot_index = _sonar_qsort_partition(base, element_size, compar, low_idx, high_idx);

    if (pivot_index > low_idx) {
        _sonar_qsort_recursive_impl(base, element_size, compar, low_idx, pivot_index - 1);
    }
    if (pivot_index < high_idx) {
        _sonar_qsort_recursive_impl(base, element_size, compar, pivot_index + 1, high_idx);
    }
}

#define DEFINE_SORT_FUNCTIONS(element_size_arg, compare_func_arg) \
    void qsort_from_macro(void *base, size_t num) { \
        if (base == NULL || num == 0 || element_size_arg == 0 || compare_func_arg == NULL) { \
            return; \
        } \
        _sonar_qsort_recursive_impl(base, element_size_arg, compare_func_arg, 0, num - 1); \
    }

/* Compare file versions.
   Unlike the other compare functions, cmp_version does not fail
   because filevercmp and strcmp do not fail; cmp_version uses strcmp
   instead of xstrcoll because filevercmp is locale-independent so
   strcmp is its appropriate secondary.

   All the other sort options need xstrcoll and strcmp variants,
   because they all use xstrcoll (either as the primary or secondary
   sort key), and xstrcoll has the ability to do a longjmp if strcoll fails for
   locale reasons.  */
static int
cmp_version (struct fileinfo const *a, struct fileinfo const *b)
{
  if (a == NULL)
  {
    return (b == NULL) ? 0 : -1;
  }
  if (b == NULL)
  {
    return 1;
  }

  const char *name_a = a->name;
  const char *name_b = b->name;

  if (name_a == NULL)
  {
    return (name_b == NULL) ? 0 : -1;
  }
  if (name_b == NULL)
  {
    return 1;
  }

  int diff = filevercmp(name_a, name_b);
  if (diff != 0)
  {
    return diff;
  }
  return strcmp(name_a, name_b);
}

static int
xstrcoll_version (const void *a, const void *b)
{
  return cmp_version (a, b);
}
static int
rev_xstrcoll_version (const V a, const V b)
{
  return cmp_version (b, a);
}
static int
xstrcoll_df_version (const void *a, const void *b)
{
  return dirfirst_check (a, b, xstrcoll_version);
}
static int
rev_xstrcoll_df_version (V a, V b)
{
  return dirfirst_check (a, b, rev_xstrcoll_version);
}


/* We have 2^3 different variants for each sort-key function
   (for 3 independent sort modes).
   The function pointers stored in this array must be dereferenced as:

    sort_variants[sort_key][use_strcmp][reverse][dirs_first]

   Note that the order in which sort keys are listed in the function pointer
   array below is defined by the order of the elements in the time_type and
   sort_type enums!  */

#define LIST_SORTFUNCTION_VARIANTS(key_name)                        \
  {                                                                 \
    {                                                               \
      { xstrcoll_##key_name, xstrcoll_df_##key_name },              \
      { rev_xstrcoll_##key_name, rev_xstrcoll_df_##key_name },      \
    },                                                              \
    {                                                               \
      { strcmp_##key_name, strcmp_df_##key_name },                  \
      { rev_strcmp_##key_name, rev_strcmp_df_##key_name },          \
    }                                                               \
  }

static qsortFunc const sort_functions[][2][2][2] =
  {
    LIST_SORTFUNCTION_VARIANTS (name),
    LIST_SORTFUNCTION_VARIANTS (extension),
    LIST_SORTFUNCTION_VARIANTS (width),
    LIST_SORTFUNCTION_VARIANTS (size),

    {
      {
        { xstrcoll_version, xstrcoll_df_version },
        { rev_xstrcoll_version, rev_xstrcoll_df_version },
      },

      /* We use nullptr for the strcmp variants of version comparison
         since as explained in cmp_version definition, version comparison
         does not rely on xstrcoll, so it will never longjmp, and never
         need to try the strcmp fallback. */
      {
        { nullptr, nullptr },
        { nullptr, nullptr },
      }
    },

    /* last are time sort functions */
    LIST_SORTFUNCTION_VARIANTS (mtime),
    LIST_SORTFUNCTION_VARIANTS (ctime),
    LIST_SORTFUNCTION_VARIANTS (atime),
    LIST_SORTFUNCTION_VARIANTS (btime)
  };

/* The number of sort keys is calculated as the sum of
     the number of elements in the sort_type enum (i.e., sort_numtypes)
     -2 because neither sort_time nor sort_none use entries themselves
     the number of elements in the time_type enum (i.e., time_numtypes)
   This is because when sort_type==sort_time, we have up to
   time_numtypes possible sort keys.

   This line verifies at compile-time that the array of sort functions has been
   initialized for all possible sort keys. */
static_assert (ARRAY_CARDINALITY (sort_functions)
               == sort_numtypes - 2 + time_numtypes);

/* Set up SORTED_FILE to point to the in-use entries in CWD_FILE, in order.  */

static void
initialize_ordering_vector (void)
{
  const size_t sorted_file_capacity = sizeof(sorted_file) / sizeof(sorted_file[0]);
  const size_t cwd_file_capacity = sizeof(cwd_file) / sizeof(cwd_file[0]);

  size_t current_n_used;

  if (cwd_n_used < 0) {
    current_n_used = 0;
  } else {
    current_n_used = (size_t)cwd_n_used;
  }

  size_t limit = current_n_used;

  if (limit > sorted_file_capacity) {
    limit = sorted_file_capacity;
  }
  if (limit > cwd_file_capacity) {
    limit = cwd_file_capacity;
  }

  for (size_t i = 0; i < limit; i++) {
    sorted_file[i] = &cwd_file[i];
  }
}

/* Cache values based on attributes global to all files.  */

static void
update_current_files_info (void)
{
  if (sort_type == sort_width
      || (line_length && (format == many_per_line || format == horizontal)))
    {
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          struct fileinfo *f = sorted_file[i];
          if (f != NULL)
            {
              f->width = fileinfo_name_width (f);
            }
        }
    }
}

/* Sort the files now in the table.  */

static void
sort_files (void)
{
  if (sorted_file_alloc < cwd_n_used + (cwd_n_used >> 1))
    {
      free (sorted_file);
      size_t new_capacity = 3 * cwd_n_used;
      sorted_file = xinmalloc (new_capacity, sizeof *sorted_file);
      sorted_file_alloc = new_capacity;
    }

  initialize_ordering_vector ();

  update_current_files_info ();

  if (sort_type == sort_none)
    return;

  bool use_strcmp = false;

  if (setjmp (failed_strcoll) != 0)
    {
      use_strcmp = true;
      affirm (sort_type != sort_version);
      initialize_ordering_vector ();
    }

  int primary_sort_index = sort_type;
  if (sort_type == sort_time)
    {
      primary_sort_index += time_type;
    }

  int (*comparison_function)(void const *, void const *) =
    sort_functions[primary_sort_index][use_strcmp][sort_reverse][directories_first];

  mpsort ((void const **) sorted_file, cwd_n_used, comparison_function);
}

/* List all the files now in the table.  */

static void handle_line_printing_mode(void (*specific_printer)(void)) {
    if (line_length == 0) {
        print_with_separator(' ');
    } else {
        specific_printer();
    }
}

static void
print_current_files (void)
{
  if (cwd_n_used == 0) {
      return;
  }

  switch (format)
    {
    case one_per_line:
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          print_file_name_and_frills (sorted_file[i], 0);
          putchar (eolbyte);
        }
      break;

    case many_per_line:
      handle_line_printing_mode(print_many_per_line);
      break;

    case horizontal:
      handle_line_printing_mode(print_horizontal);
      break;

    case with_commas:
      print_with_separator (',');
      break;

    case long_format:
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          set_normal_color ();
          print_long_format (sorted_file[i]);
          dired_outbyte (eolbyte);
        }
      break;
    }
}

/* Replace the first %b with precomputed aligned month names.
   Note on glibc-2.7 at least, this speeds up the whole 'ls -lU'
   process by around 17%, compared to letting strftime() handle the %b.  */

static size_t
align_nstrftime (char *buf, size_t size, bool recent, struct tm const *tm,
                 timezone_t tz, int ns)
{
  char const *nfmt;

  /*
   * Defensive check for 'tm' to prevent potential null dereference (CWE-476).
   * Returning 0 (no characters written) is a common convention for
   * size-writing functions when input is invalid, improving reliability
   * without altering the function's behavior for valid 'tm' inputs.
   */
  if (tm == NULL)
    {
      return 0;
    }

  if (use_abformat)
    {
      nfmt = abformat[recent][tm->tm_mon];
    }
  else
    {
      nfmt = long_time_format[recent];
    }

  return nstrftime (buf, size, nfmt, tm, tz, ns);
}

/* Return the expected number of columns in a long-format timestamp,
   or zero if it cannot be calculated.  */

static int
long_time_expected_width (void)
{
  static int width = -1;

  if (width < 0)
    {
      int calculated_width = 0;

      time_t epoch = 0;
      struct tm tm;

      if (localtime_rz (localtz, &epoch, &tm) != NULL)
        {
          char buf[TIME_STAMP_LEN_MAXIMUM + 1];
          size_t len = align_nstrftime (buf, sizeof buf, false,
                                        &tm, localtz, 0);
          if (len != 0)
            {
              calculated_width = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
              if (calculated_width < 0)
                {
                  calculated_width = 0;
                }
            }
        }
      width = calculated_width;
    }

  return width;
}

/* Print the user or group name NAME, with numeric id ID, using a
   print width of WIDTH columns.  */

static void
format_user_or_group (char const *name, uintmax_t id, int width)
{
  if (name)
    {
      dired_outstring (name);

      int name_display_width = mbswidth (name, MBSWIDTH_FLAGS);
      int spaces_to_print;

      if (name_display_width < 0)
        {
          spaces_to_print = 1;
        }
      else
        {
          int padding_for_alignment = width - name_display_width;
          spaces_to_print = MAX (0, padding_for_alignment) + 1;
        }

      for (int i = 0; i < spaces_to_print; ++i)
        dired_outbyte (' ');
    }
  else
    dired_pos += printf ("%*ju ", width, id);
}

/* Print the name or id of the user with id U, using a print width of
   WIDTH.  */

static void
format_user (uid_t u, int width, bool stat_ok)
{
  const char *display_name;

  if (!stat_ok)
    {
      display_name = "?";
    }
  else
    {
      if (numeric_ids)
        {
          display_name = NULL;
        }
      else
        {
          display_name = getuser (u);
        }
    }

  format_user_or_group (display_name, u, width);
}

/* Likewise, for groups.  */

static void
format_group (gid_t g, int width, bool stat_ok)
{
  const char *group_name_to_display;

  if (!stat_ok)
    {
      group_name_to_display = "?";
    }
  else
    {
      if (numeric_ids)
        {
          group_name_to_display = NULL;
        }
      else
        {
          group_name_to_display = getgroup (g);
        }
    }

  format_user_or_group (group_name_to_display, g, width);
}

/* Return the number of columns that format_user_or_group will print,
   or -1 if unknown.  */

#include <stddef.h>
#include <stdio.h>
#include <inttypes.h>
#include <limits.h>

static int
format_user_or_group_width (char const *name, uintmax_t id)
{
  if (name != NULL)
    {
      size_t width = mbswidth(name, MBSWIDTH_FLAGS);
      if (width == (size_t)-1)
        {
          return -1;
        }
      if (width > (size_t)INT_MAX)
        {
          return -1;
        }
      return (int)width;
    }
  else
    {
      int required_width = snprintf(NULL, 0, "%ju", id);
      if (required_width < 0)
        {
          return -1;
        }
      return required_width;
    }
}

/* Return the number of columns that format_user will print,
   or -1 if unknown.  */

static int
format_user_width (uid_t u)
{
  const char *username = NULL;

  if (!numeric_ids)
    {
      username = getuser (u);
    }

  return format_user_or_group_width (username, u);
}

/* Likewise, for groups.  */

static int
format_group_width (gid_t g)
{
  const struct group *grp_ptr = NULL;

  if (!numeric_ids)
    {
      grp_ptr = getgroup (g);
    }

  return format_user_or_group_width (grp_ptr, g);
}

/* Return a pointer to a formatted version of F->stat.st_ino,
   possibly using buffer, which must be at least
   INT_BUFSIZE_BOUND (uintmax_t) bytes.  */
#include <stddef.h>

static char *
format_inode (char buf[INT_BUFSIZE_BOUND (uintmax_t)],
              const struct fileinfo *f)
{
  if (f == NULL)
    {
      return (char *) "?";
    }

  if (f->stat_ok && f->stat.st_ino != NOT_AN_INODE_NUMBER)
    {
      return umaxtostr (f->stat.st_ino, buf);
    }
  else
    {
      return (char *) "?";
    }
}

/* Print information about F in long format.  */
static char get_acl_indicator_char(bool any_acl_in_dir, enum acl_type type) {
  if (!any_acl_in_dir) {
    return '\0';
  }
  switch (type) {
    case ACL_T_LSM_CONTEXT_ONLY: return '.';
    case ACL_T_YES:              return '+';
    case ACL_T_UNKNOWN:          return '?';
    case ACL_T_NO:               return ' '; // No specific ACL but directory has ACLs
    default:                     return ' '; // Fallback to space
  }
}

// Helper for safely appending to buf and updating pointer.
// 'p_ptr' is the current write position, 'buf_start' is the start of the buffer.
// 'buf_capacity' is the total allocated size of the buffer including null terminator.
// Returns the number of characters successfully written (excluding null terminator),
// or 0 on error/if no space was available.
static int append_to_buffer(char **p_ptr, char *buf_start, size_t buf_capacity, const char *format, ...)
{
  size_t current_offset = *p_ptr - buf_start;
  size_t remaining_space = (buf_capacity > current_offset) ? (buf_capacity - current_offset) : 0;

  if (remaining_space == 0) {
    return 0; // No space left to write
  }

  va_list args;
  va_start(args, format);
  int written_chars = vsnprintf(*p_ptr, remaining_space, format, args);
  va_end(args);

  if (written_chars < 0) {
    return 0; // Encoding error or similar failure
  }

  if ((size_t)written_chars >= remaining_space) {
    // Truncation occurred, or buffer was exactly full (including null).
    // Advance p_ptr to the end of usable buffer space (before null terminator).
    *p_ptr = buf_start + buf_capacity - 1;
    return (int)remaining_space - 1; // Return count of characters written before truncation
  } else {
    *p_ptr += written_chars;
    return written_chars;
  }
}

// Helper for printing human-readable strings with padding based on mbswidth.
// 'p_ptr' points to the current write position.
// 'buf_start' is the start of the buffer.
// 'buf_capacity' is the total allocated size of the buffer including null terminator.
// 'hr_str' is the string to print.
// 'field_width' is the minimum desired visual width.
// 'add_trailing_space' indicates whether to append an extra space after the string.
// Returns total characters written to buffer.
static int append_human_readable_padded(char **p_ptr, char *buf_start, size_t buf_capacity,
                                        const char *hr_str, int field_width, bool add_trailing_space)
{
  size_t current_offset = *p_ptr - buf_start;
  size_t remaining_space = (buf_capacity > current_offset) ? (buf_capacity - current_offset) : 0;

  if (remaining_space == 0) {
    return 0;
  }

  int str_mbswidth = mbswidth(hr_str, MBSWIDTH_FLAGS);
  if (str_mbswidth < 0) {
    str_mbswidth = 0; // Treat error as zero width for padding calculation.
  }

  int pad_len = field_width - str_mbswidth;
  if (pad_len < 0) {
    pad_len = 0; // No negative padding.
  }

  int total_written_here = 0;

  // Append padding spaces
  for (int i = 0; i < pad_len; ++i) {
    if (remaining_space > 1) { // Ensure space for char and null terminator
      **p_ptr = ' ';
      (*p_ptr)++;
      remaining_space--;
      total_written_here++;
    } else {
      break; // Not enough space
    }
  }

  // Append the string content
  size_t hr_str_len = strlen(hr_str);
  size_t chars_to_copy = MIN(hr_str_len, remaining_space > 0 ? remaining_space - 1 : 0); // Leave space for null
  if (chars_to_copy > 0) {
    memcpy(*p_ptr, hr_str, chars_to_copy);
    (*p_ptr) += chars_to_copy;
    remaining_space -= chars_to_copy;
    total_written_here += chars_to_copy;
  }

  // Add trailing space if requested and space allows
  if (add_trailing_space && remaining_space > 0) {
    **p_ptr = ' ';
    (*p_ptr)++;
    remaining_space--;
    total_written_here++;
  }

  return total_written_here;
}

#define AVERAGE_SECONDS_IN_SIX_MONTHS (31556952 / 2)

static void
print_long_format (const struct fileinfo *f)
{
  char modebuf[12]; // Room for 10 mode chars, 1 ACL char, 1 null
  char buf
    [LONGEST_HUMAN_READABLE + 1		/* inode */
     + LONGEST_HUMAN_READABLE + 1	/* size in blocks */
     + sizeof (modebuf) - 1 + 1		/* mode string (11 chars incl. ACL) + space */
     + INT_BUFSIZE_BOUND (uintmax_t) + 1	/* st_nlink + space */
     + LONGEST_HUMAN_READABLE + 2	/* major device number + ", " */
     + LONGEST_HUMAN_READABLE + 1	/* minor device number + space */
     + TIME_STAMP_LEN_MAXIMUM + 1	/* max length of time/date + space */
     ];
  char *p;
  const size_t buf_capacity = sizeof(buf);
  size_t s_strftime_result;
  struct timespec when_timespec;
  struct tm when_local;
  bool btime_ok = true;

  // --- Mode String Generation ---
  if (f->stat_ok) {
    filemodestring (&f->stat, modebuf);
  } else {
    modebuf[0] = filetype_letter[f->filetype];
    memset (modebuf + 1, '?', 9); // Fill modebuf[1] through modebuf[9] with '?'
    modebuf[10] = ' '; // Default space for position 10 if stat failed or no ACL
    modebuf[11] = '\0';
  }

  char acl_char = get_acl_indicator_char(any_has_acl, f->acl_type);
  if (acl_char != '\0') {
      modebuf[10] = acl_char;
      modebuf[11] = '\0';
  } else {
      // If acl_char_val is '\0', it means `!any_has_acl`.
      // In this case, modebuf[10] must be '\0' to effectively shorten the string.
      // If filemodestring set modebuf[10] to '\0' this is a no-op, otherwise it overwrites ' '.
      modebuf[10] = '\0';
  }

  // --- Time Type Selection ---
  if (!f->stat_ok) { // If stat failed, time info is also unavailable
      when_timespec.tv_sec = -1;
      when_timespec.tv_nsec = -1;
      btime_ok = false;
  } else {
      switch (time_type) {
      case time_ctime:
        when_timespec = get_stat_ctime (&f->stat);
        break;
      case time_mtime:
        when_timespec = get_stat_mtime (&f->stat);
        break;
      case time_atime:
        when_timespec = get_stat_atime (&f->stat);
        break;
      case time_btime:
        when_timespec = get_stat_btime (&f->stat);
        if (when_timespec.tv_sec == -1 && when_timespec.tv_nsec == -1)
          btime_ok = false;
        break;
      case time_numtypes: default:
        unreachable ();
      }
  }

  p = buf; // Reset buffer pointer for first segment

  // --- Inode Printing ---
  if (print_inode) {
    char hbuf_inode[INT_BUFSIZE_BOUND (uintmax_t)];
    const char *inode_str = f->stat_ok ? format_inode (hbuf_inode, f) : "?";
    append_to_buffer(&p, buf, buf_capacity, "%*s ", inode_number_width, inode_str);
  }

  // --- Block Size Printing ---
  if (print_block_size) {
    char hbuf_blocks[LONGEST_HUMAN_READABLE + 1];
    const char *blocks_str =
      (! f->stat_ok
       ? "?"
       : human_readable (STP_NBLOCKS (&f->stat), hbuf_blocks, human_output_opts,
                         ST_NBLOCKSIZE, output_block_size));
    append_human_readable_padded(&p, buf, buf_capacity, blocks_str, block_size_width, true);
  }

  // --- Mode and Nlink Printing ---
  {
    char hbuf_nlink[INT_BUFSIZE_BOUND (uintmax_t)];
    const char *nlink_str = ! f->stat_ok ? "?" : umaxtostr (f->stat.st_nlink, hbuf_nlink);
    append_to_buffer(&p, buf, buf_capacity, "%s %*s ", modebuf, nlink_width, nlink_str);
  }

  dired_indent (); // This might print leading spaces or similar

  // Owner/Group/Author/Scontext printing often flushes previous buffer content.
  if (print_owner || print_group || print_author || print_scontext) {
    dired_outbuf (buf, p - buf); // Output the content accumulated so far

    // These functions typically print directly to the output stream.
    if (print_owner)
      format_user (f->stat.st_uid, owner_width, f->stat_ok);

    if (print_group)
      format_group (f->stat.st_gid, group_width, f->stat_ok);

    if (print_author)
      format_user (f->stat.st_author, author_width, f->stat_ok);

    if (print_scontext)
      format_user_or_group (f->scontext, 0, scontext_width);

    p = buf; // Reset buffer pointer for next segment
  }

  // --- Device or File Size Printing ---
  if (f->stat_ok && (S_ISCHR (f->stat.st_mode) || S_ISBLK (f->stat.st_mode))) {
    char majorbuf[INT_BUFSIZE_BOUND (uintmax_t)];
    char minorbuf[INT_BUFSIZE_BOUND (uintmax_t)];
    int blanks_width = (file_size_width
                        - (major_device_number_width + 2 /* ", " */
                           + minor_device_number_width));
    int effective_major_width = major_device_number_width + MAX (0, blanks_width);
    append_to_buffer(&p, buf, buf_capacity, "%*s, %*s ",
                     effective_major_width,
                     umaxtostr (major (f->stat.st_rdev), majorbuf),
                     minor_device_number_width,
                     umaxtostr (minor (f->stat.st_rdev), minorbuf));
  } else {
    char hbuf_size[LONGEST_HUMAN_READABLE + 1];
    const char *size_str =
      (! f->stat_ok
       ? "?"
       : human_readable (unsigned_file_size (f->stat.st_size),
                         hbuf_size, file_human_output_opts, 1,
                         file_output_block_size));
    append_human_readable_padded(&p, buf, buf_capacity, size_str, file_size_width, true);
  }

  s_strftime_result = 0;
  *p = '\0'; // Ensure null termination for potential empty string or start of time string.

  // --- Time Stamp Printing ---
  if (f->stat_ok && btime_ok && when_timespec.tv_sec != -1
      && localtime_rz (localtz, &when_timespec.tv_sec, &when_local))
    {
      struct timespec six_months_ago;
      bool recent;

      // Update current time if file appears to be in the future.
      if (timespec_cmp (current_time, when_timespec) < 0)
        gettime (&current_time);

      six_months_ago.tv_sec = current_time.tv_sec - AVERAGE_SECONDS_IN_SIX_MONTHS;
      six_months_ago.tv_nsec = current_time.tv_nsec;

      recent = (timespec_cmp (six_months_ago, when_timespec) < 0
                && timespec_cmp (when_timespec, current_time) < 0);

      // Attempt to format the time stamp.
      s_strftime_result = align_nstrftime (p, buf_capacity - (p - buf), recent,
                                           &when_local, localtz, when_timespec.tv_nsec);

      // If align_nstrftime wrote something, advance p
      if (s_strftime_result > 0) {
          p += s_strftime_result;
      } else {
          // It failed or wrote nothing. Reset p to where it was for fallback.
          *p = '\0'; // Ensure it's null-terminated for the fallback logic to work
      }
    }

  if (s_strftime_result > 0) { // If align_nstrftime succeeded
      append_to_buffer(&p, buf, buf_capacity, " "); // Add trailing space
  } else {
      // The time cannot be converted or was unavailable, print as integer seconds.
      char hbuf_time[INT_BUFSIZE_BOUND (intmax_t)];
      const char *time_str = (!f->stat_ok || !btime_ok || when_timespec.tv_sec == -1)
                             ? "?"
                             : timetostr (when_timespec.tv_sec, hbuf_time);
      append_to_buffer(&p, buf, buf_capacity, "%*s ", long_time_expected_width (), time_str);
      /* FIXME: (maybe) We discarded when_timespec.tv_nsec. */
  }

  // Flush final part of the buffer
  dired_outbuf (buf, p - buf);
  size_t name_width = print_name_with_quoting (f, false, &dired_obstack, p - buf);

  // --- Link Name and Type Indicator Printing ---
  if (f->filetype == symbolic_link) {
      if (f->linkname) {
          dired_outstring (" -> ");
          print_name_with_quoting (f, true, nullptr, (p - buf) + name_width + 4); // +4 for " -> "
          if (indicator_style != none)
            print_type_indicator (true, f->linkmode, unknown);
      }
  } else if (indicator_style != none) {
      print_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
  }
}

/* Write to *BUF a quoted representation of the file name NAME, if non-null,
   using OPTIONS to control quoting.  *BUF is set to NAME if no quoting
   is required.  *BUF is allocated if more space required (and the original
   *BUF is not deallocated).
   Store the number of screen columns occupied by NAME's quoted
   representation into WIDTH, if non-null.
   Store into PAD whether an initial space is needed for padding.
   Return the number of bytes in *BUF.  */

static void
process_multibyte_funny_chars (char *buf, size_t *len_ptr, size_t *displayed_width_ptr)
{
  char const *p = buf;
  char const *plimit = buf + *len_ptr;
  char *q = buf;
  size_t current_displayed_width = 0;

  mbstate_t mbstate;
  mbszero (&mbstate);

  while (p < plimit)
    {
      char32_t wc;
      size_t bytes;
      int w;

      bytes = mbrtoc32 (&wc, p, plimit - p, &mbstate);

      if (bytes == (size_t) -1) /* Invalid multibyte sequence */
        {
          p++;
          *q++ = '?';
          current_displayed_width += 1;
          mbszero(&mbstate); /* Reset state after error */
          continue;
        }

      if (bytes == (size_t) -2) /* Incomplete multibyte character at end */
        {
          p = plimit; /* Consume remaining bytes */
          *q++ = '?';
          current_displayed_width += 1;
          continue;
        }

      if (bytes == 0) /* Null wide character */
        bytes = 1;

      w = c32width (wc);
      if (w >= 0) /* Printable multibyte character */
        {
          for (size_t i = 0; i < bytes; ++i)
            *q++ = *p++;
          current_displayed_width += w;
        }
      else /* Non-printable multibyte character */
        {
          p += bytes;
          *q++ = '?';
          current_displayed_width += 1;
        }
    }
  *len_ptr = q - buf;
  *displayed_width_ptr = current_displayed_width;
}

static void
process_singlebyte_funny_chars (char *buf, size_t *len_ptr, size_t *displayed_width_ptr)
{
  char *p = buf;
  char const *plimit = buf + *len_ptr;

  while (p < plimit)
    {
      if (! isprint (to_uchar (*p)))
        *p = '?';
      p++;
    }
  *displayed_width_ptr = *len_ptr;
}

static size_t
calculate_multibyte_string_width (char const *buf, size_t len)
{
  size_t dw = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
  return MAX (0, dw);
}

static size_t
calculate_singlebyte_string_width (char const *buf, size_t len)
{
  size_t dw = 0;
  char const *p = buf;
  char const *plimit = buf + len;

  while (p < plimit)
    {
      if (isprint (to_uchar (*p)))
        dw++;
      p++;
    }
  return dw;
}


static size_t
quote_name_buf (char **inbuf, size_t bufsize, char *name,
                struct quoting_options const *options,
                int needs_general_quoting, size_t *width, bool *pad)
{
  char *buf = *inbuf;
  size_t len;
  bool quoted;
  size_t displayed_width = 0;

  enum quoting_style qs = get_quoting_style (options);
  bool needs_funny_char_processing = qmark_funny_chars
                               && (qs == shell_quoting_style
                                   || qs == shell_always_quoting_style
                                   || qs == literal_quoting_style);

  if (needs_general_quoting)
    {
      len = quotearg_buffer (buf, bufsize, name, -1, options);
      if (bufsize <= len)
        {
          buf = xmalloc (len + 1);
          quotearg_buffer (buf, len + 1, name, -1, options);
        }
      quoted = (*name != *buf) || (strlen(name) != len);
    }
  else if (needs_funny_char_processing)
    {
      len = strlen (name);
      if (bufsize <= len)
        buf = xmalloc (len + 1);
      memcpy (buf, name, len + 1);
      quoted = false;
    }
  else
    {
      len = strlen (name);
      buf = name;
      quoted = false;
    }

  if (needs_funny_char_processing)
    {
      if (MB_CUR_MAX > 1)
        process_multibyte_funny_chars (buf, &len, &displayed_width);
      else
        process_singlebyte_funny_chars (buf, &len, &displayed_width);
    }
  else if (width != NULL)
    {
      if (MB_CUR_MAX > 1)
        displayed_width = calculate_multibyte_string_width (buf, len);
      else
        displayed_width = calculate_singlebyte_string_width (buf, len);
    }

  *pad = (align_variable_outer_quotes && cwd_some_quoted && ! quoted);

  if (width != NULL)
    *width = displayed_width;

  *inbuf = buf;

  return len;
}

static size_t
quote_name_width (char const *name, struct quoting_options const *options,
                  int needs_general_quoting)
{
  char smallbuf[BUFSIZ];
  char *buf = smallbuf;
  size_t width;
  bool pad;

  quote_name_buf (&buf, sizeof smallbuf, name, options,
                  needs_general_quoting, &width, &pad);

  if (buf != smallbuf && buf != name)
    free (buf);

  width += pad;

  return width;
}

/* %XX escape any input out of range as defined in RFC3986,
   and also if PATH, convert all path separators to '/'.  */
static char *
file_escape (char const *str, bool path)
{
  size_t len = strlen(str);
  char *esc = xnmalloc(3, len + 1);
  char *p = esc;
  const char *s = str;
  const char hex_digits[] = "0123456789abcdef";

  while (*s)
    {
      if (path && ISSLASH(*s))
        {
          *p++ = '/';
          s++;
        }
      else
        {
          unsigned char uc = to_uchar(*s);
          if (RFC3986[uc])
            {
              *p++ = *s++;
            }
          else
            {
              *p++ = '%';
              *p++ = hex_digits[(uc >> 4) & 0xF];
              *p++ = hex_digits[uc & 0xF];
              s++;
            }
        }
    }
  *p = '\0';
  return esc;
}

static size_t
quote_name (char const *name, struct quoting_options const *options,
            int needs_general_quoting, const struct bin_str *color,
            bool allow_pad, struct obstack *stack, char const *absolute_name)
{
  char smallbuf[BUFSIZ];
  char *buf = smallbuf;
  size_t len;
  bool pad;
  bool skip_quotes = false;

  len = quote_name_buf (&buf, sizeof smallbuf, (char *) name, options,
                        needs_general_quoting, nullptr, &pad);

  if (pad && allow_pad)
    dired_outbyte (' ');

  if (color)
    print_color_indicator (color);

  char *h_escaped = NULL;
  char *n_escaped = NULL;

  if (absolute_name)
    {
      if (align_variable_outer_quotes && cwd_some_quoted && !pad)
        {
          skip_quotes = true;
          // Print the leading quote character if skipping outer quotes.
          // This ensures visual alignment when the hyperlink is active.
          if (len > 0)
            putchar (*buf);
        }

      // Escape hostname and absolute path for URI.
      // Check for allocation failures to improve reliability.
      h_escaped = file_escape (hostname, /* path= */ false);
      if (h_escaped != NULL) {
        n_escaped = file_escape (absolute_name, /* path= */ true);
        if (n_escaped == NULL) {
          // If n_escaped allocation fails, free h_escaped and clear its pointer
          // to prevent memory leaks and ensure the hyperlink is skipped.
          free (h_escaped);
          h_escaped = NULL;
        }
      }

      // Only print the hyperlink if both parts were successfully escaped.
      if (h_escaped != NULL && n_escaped != NULL)
        {
          printf ("\033]8;;file://%s%s%s\a", h_escaped, *n_escaped == '/' ? "" : "/", n_escaped);
        }
    }

  if (stack)
    push_current_dired_pos (stack);

  // Write the quoted name to stdout.
  // If skip_quotes is true, we skip the first character and reduce the length by 2,
  // effectively removing the outer quotes that are printed manually.
  // The condition ensures that the calculated length for fwrite is non-negative,
  // preventing potential size_t underflow and undefined behavior.
  if (len >= (size_t)(skip_quotes * 2))
    fwrite (buf + skip_quotes, 1, len - (skip_quotes * 2), stdout);

  dired_pos += len;

  if (stack)
    push_current_dired_pos (stack);

  if (absolute_name)
    {
      // End the hyperlink.
      fputs ("\033]8;;\a", stdout);
      // Print the trailing quote character if skipping outer quotes.
      // Guard with len > 0 to prevent access to invalid memory if len is 0.
      if (skip_quotes && len > 0)
        putchar (*(buf + len - 1));
    }

  // Clean up dynamically allocated memory for escaped strings.
  if (h_escaped != NULL)
    free (h_escaped);
  if (n_escaped != NULL)
    free (n_escaped);

  // Free the buffer returned by quote_name_buf if it was dynamically allocated
  // and is not the original 'name' string.
  if (buf != smallbuf && buf != (char *) name)
    free (buf);

  return len + pad;
}

static size_t
print_name_with_quoting (const struct fileinfo *f,
                         bool symlink_target,
                         struct obstack *stack,
                         size_t start_col)
{
  const char *name = symlink_target ? f->linkname : f->name;

  const struct bin_str *color = print_with_color ? get_color_indicator(f, symlink_target) : NULL;

  const bool used_color_this_time = print_with_color && (color || is_colored(C_NORM));

  size_t len = quote_name(name, filename_quoting_options, f->quoted,
                           color, !symlink_target, stack, f->absolute_name);

  process_signals();

  if (used_color_this_time)
    {
      prep_non_filename_text();

      if (line_length && (start_col / line_length != (start_col + len - 1) / line_length))
        {
          put_indicator(&color_indicator[C_CLR_TO_EOL]);
        }
    }

  return len;
}

static void
prep_non_filename_text (void)
{
  if (color_indicator[C_END].string != NULL)
    put_indicator (&color_indicator[C_END]);
  else
    {
      put_indicator (&color_indicator[C_LEFT]);
      put_indicator (&color_indicator[C_RESET]);
      put_indicator (&color_indicator[C_RIGHT]);
    }
}

/* Print the file name of 'f' with appropriate quoting.
   Also print file size, inode number, and filetype indicator character,
   as requested by switches.  */

static size_t
print_file_name_and_frills (const struct fileinfo *f, size_t start_col)
{
  char buf[MAX (LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND (uintmax_t))];

  set_normal_color ();

  if (print_inode)
    printf ("%*s ", format == with_commas ? 0 : inode_number_width,
            format_inode (buf, f));

  if (print_block_size)
    {
      char const *blocks =
        (! f->stat_ok
         ? "?"
         : human_readable (STP_NBLOCKS (&f->stat), buf, human_output_opts,
                           ST_NBLOCKSIZE, output_block_size));
      int blocks_width = mbswidth (blocks, MBSWIDTH_FLAGS);
      int pad = 0;
      if (0 <= blocks_width && block_size_width && format != with_commas)
        pad = block_size_width - blocks_width;
      printf ("%*s%s ", pad, "", blocks);
    }

  if (print_scontext)
    printf ("%*s ", format == with_commas ? 0 : scontext_width, f->scontext);

  size_t width = print_name_with_quoting (f, false, NULL, start_col);

  if (indicator_style != none)
    width += print_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);

  return width;
}

/* Given these arguments describing a file, return the single-byte
   type indicator, or 0.  */
static char
get_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  if (stat_ok)
    {
      if (S_ISREG (mode))
        {
          if (indicator_style == classify && (mode & (S_IXUSR | S_IXGRP | S_IXOTH)))
            {
              return '*';
            }
          return 0;
        }
      else if (S_ISDIR (mode))
        {
          return '/';
        }
      else if (indicator_style == slash)
        {
          return 0;
        }
      else if (S_ISLNK (mode))
        {
          return '@';
        }
      else if (S_ISFIFO (mode))
        {
          return '|';
        }
      else if (S_ISSOCK (mode))
        {
          return '=';
        }
      else if (S_ISDOOR (mode))
        {
          return '>';
        }
      return 0;
    }
  else
    {
      if (type == directory || type == arg_directory)
        {
          return '/';
        }
      else if (indicator_style == slash)
        {
          return 0;
        }
      else if (type == symbolic_link)
        {
          return '@';
        }
      else if (type == fifo)
        {
          return '|';
        }
      else if (type == sock)
        {
          return '=';
        }
      return 0;
    }
}

static bool
print_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  char indicator = get_type_indicator (stat_ok, mode, type);
  if (indicator != '\0')
    {
      dired_outbyte (indicator);
    }
  return indicator != '\0';
}

/* Returns if color sequence was printed.  */
static bool
print_color_indicator (const struct bin_str *ind)
{
  if (ind == NULL)
    {
      return false;
    }

  if (is_colored (C_NORM))
    {
      restore_default_color ();
    }

  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (ind);
  put_indicator (&color_indicator[C_RIGHT]);

  return true;
}

/* Returns color indicator or nullptr if none.  */
static enum indicator_no
get_indicator_for_regular_file (mode_t mode, const struct fileinfo *f)
{
  enum indicator_no type = C_FILE;

  if ((mode & S_ISUID) && is_colored (C_SETUID))
    type = C_SETUID;
  else if ((mode & S_ISGID) && is_colored (C_SETGID))
    type = C_SETGID;
  else if (f->has_capability)
    type = C_CAP;
  else if ((mode & S_IXUGO) && is_colored (C_EXEC))
    type = C_EXEC;
  else if ((1 < f->stat.st_nlink) && is_colored (C_MULTIHARDLINK))
    type = C_MULTIHARDLINK;

  return type;
}

static enum indicator_no
get_indicator_for_directory (mode_t mode)
{
  enum indicator_no type = C_DIR;

  if ((mode & S_ISVTX) && (mode & S_IWOTH) && is_colored (C_STICKY_OTHER_WRITABLE))
    type = C_STICKY_OTHER_WRITABLE;
  else if ((mode & S_IWOTH) && is_colored (C_OTHER_WRITABLE))
    type = C_OTHER_WRITABLE;
  else if ((mode & S_ISVTX) && is_colored (C_STICKY))
    type = C_STICKY;

  return type;
}

static struct color_ext_type*
find_matching_extension (const char *name)
{
  size_t len = strlen (name);
  const char *name_end_ptr = name + len;

  for (struct color_ext_type *ext = color_ext_list; ext != nullptr; ext = ext->next)
    {
      if (ext->ext.len > len)
        continue;

      const char *suffix_start = name_end_ptr - ext->ext.len;

      if (ext->exact_match)
        {
          if (STREQ_LEN (suffix_start, ext->ext.string, ext->ext.len))
            return ext;
        }
      else
        {
          if (c_strncasecmp (suffix_start, ext->ext.string, ext->ext.len) == 0)
            return ext;
        }
    }
  return nullptr;
}

ATTRIBUTE_PURE
static const struct bin_str*
get_color_indicator (const struct fileinfo *f, bool symlink_target)
{
  enum indicator_no type;
  const char *effective_name;
  mode_t effective_mode;
  bool target_entity_is_missing;
  bool is_original_file_a_broken_symlink = false;

  if (symlink_target)
    {
      effective_name = f->linkname;
      effective_mode = f->linkmode;
      target_entity_is_missing = !f->linkok;
    }
  else
    {
      effective_name = f->name;
      effective_mode = file_or_link_mode (f);
      target_entity_is_missing = !f->stat_ok;

      if (f->stat_ok && S_ISLNK (f->stat.st_mode) && !f->linkok)
        is_original_file_a_broken_symlink = true;
    }

  if (effective_name == nullptr) {
      return nullptr;
  }

  if (target_entity_is_missing && is_colored (C_MISSING))
    {
      type = C_MISSING;
    }
  else if (!f->stat_ok)
    {
      static enum indicator_no const filetype_indicator[] =
        {
          C_ORPHAN, C_FIFO, C_CHR, C_DIR, C_BLK, C_FILE,
          C_LINK, C_SOCK, C_FILE, C_DIR
        };
      type = filetype_indicator[f->filetype];
    }
  else
    {
      if (S_ISREG (effective_mode))
        {
          type = get_indicator_for_regular_file (effective_mode, f);
        }
      else if (S_ISDIR (effective_mode))
        {
          type = get_indicator_for_directory (effective_mode);
        }
      else if (S_ISLNK (effective_mode))
        type = C_LINK;
      else if (S_ISFIFO (effective_mode))
        type = C_FIFO;
      else if (S_ISSOCK (effective_mode))
        type = C_SOCK;
      else if (S_ISBLK (effective_mode))
        type = C_BLK;
      else if (S_ISCHR (effective_mode))
        type = C_CHR;
      else if (S_ISDOOR (effective_mode))
        type = C_DOOR;
      else
        {
          type = C_ORPHAN;
        }
    }

  struct color_ext_type *ext = nullptr;
  if (type == C_FILE)
    {
      ext = find_matching_extension (effective_name);
    }

  if (type == C_LINK && is_original_file_a_broken_symlink)
    {
      if (color_symlink_as_referent || is_colored (C_ORPHAN))
        type = C_ORPHAN;
    }

  const struct bin_str *const s
    = ext ? &(ext->seq) : &color_indicator[type];

  return s->string ? s : nullptr;
}

/* Output a color indicator (which may contain nulls).  */
static bool output_failure_occurred = false;

static void
setup_color_environment(void)
{
  static bool initialized = false;

  if (!initialized)
    {
      initialized = true;

      if (0 <= tcgetpgrp (STDOUT_FILENO))
        signal_init ();

      prep_non_filename_text ();
    }
}

static void
put_indicator (const struct bin_str *ind)
{
  if (output_failure_occurred)
    {
      return;
    }

  setup_color_environment();

  if (ind && ind->string && ind->len > 0)
    {
      if (fwrite (ind->string, ind->len, 1, stdout) != 1)
        {
          output_failure_occurred = true;
        }
    }
}

static size_t
length_of_file_name_and_frills (const struct fileinfo *f)
{
  size_t len = 0;
  char buf[MAX (LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND (uintmax_t))];

  if (print_inode)
    {
      size_t inode_value_len;
      if (format == with_commas)
        inode_value_len = strlen (umaxtostr (f->stat.st_ino, buf));
      else
        inode_value_len = inode_number_width;
      len += 1 + inode_value_len;
    }

  if (print_block_size)
    {
      size_t block_value_len;
      if (format == with_commas)
        {
          block_value_len = strlen (! f->stat_ok ? "?"
                                    : human_readable (STP_NBLOCKS (&f->stat), buf,
                                                      human_output_opts, ST_NBLOCKSIZE,
                                                      output_block_size));
        }
      else
        block_value_len = block_size_width;
      len += 1 + block_value_len;
    }

  if (print_scontext)
    {
      size_t scontext_value_len;
      if (format == with_commas)
        scontext_value_len = strlen (f->scontext);
      else
        scontext_value_len = scontext_width;
      len += 1 + scontext_value_len;
    }

  len += fileinfo_name_width (f);

  if (indicator_style != none)
    {
      char c = get_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
      len += (c != 0);
    }

  return len;
}

static void
print_many_per_line (void)
{
  idx_t cols = calculate_columns (true);
  // It is assumed that 'cols' returned by calculate_columns is always at least 1,
  // preventing out-of-bounds access to column_info.
  struct column_info const *line_fmt = &column_info[cols - 1];

  // Calculate the number of rows that will be in each column.
  // This is a ceiling division: ceil(cwd_n_used / cols).
  // Explicitly handle cwd_n_used == 0 to ensure rows is 0 in that case.
  idx_t rows = (cwd_n_used == 0) ? 0 : (cwd_n_used + cols - 1) / cols;

  for (idx_t row = 0; row < rows; row++)
    {
      size_t pos = 0; // Reset horizontal position for each new row

      for (size_t col_idx = 0; col_idx < cols; col_idx++)
        {
          idx_t filesno = row + col_idx * rows;

          // If the calculated file index is beyond the total number of used files,
          // it means there are no more files to print in this row's remaining columns.
          // Break the inner loop and move to the next row.
          if (filesno >= cwd_n_used)
            {
              break;
            }

          struct fileinfo const *f = sorted_file[filesno];
          size_t name_length = length_of_file_name_and_frills (f);

          // Access col_arr to get the maximum name length for the current column.
          // This assumes line_fmt->col_arr has at least 'cols' elements.
          size_t max_name_length = line_fmt->col_arr[col_idx];

          print_file_name_and_frills (f, pos);

          // Indent only if:
          // 1. This is not the last column in the layout AND
          // 2. There is actually another file that would be printed in the next column's slot for this row.
          if (col_idx < cols - 1 && (row + (col_idx + 1) * rows < cwd_n_used))
            {
              indent (pos + name_length, pos + max_name_length);
              pos += max_name_length;
            }
          // If it's the last column or no more files for the next slot, no indentation is needed,
          // and 'pos' does not need to be updated as the line is ending after this item.
        }
      putchar (eolbyte);
    }
}

static void
print_horizontal (void)
{
  if (cwd_n_used == 0)
    {
      return;
    }

  idx_t cols = calculate_columns (false);
  if (cols == 0)
    {
      return;
    }

  struct column_info const *column_layout = &column_info[cols - 1];

  size_t current_col_start_pos = 0;
  
  size_t last_printed_file_actual_len;
  size_t last_occupied_col_allocated_width;

  struct fileinfo const *file_to_process = sorted_file[0];
  print_file_name_and_frills (file_to_process, current_col_start_pos);
  
  last_printed_file_actual_len = length_of_file_name_and_frills (file_to_process);
  last_occupied_col_allocated_width = column_layout->col_arr[0];

  for (idx_t filesno = 1; filesno < cwd_n_used; filesno++)
    {
      idx_t col_index = filesno % cols;

      if (col_index == 0)
        {
          putchar (eolbyte);
          current_col_start_pos = 0;
        }
      else
        {
          indent (current_col_start_pos + last_printed_file_actual_len,
                  current_col_start_pos + last_occupied_col_allocated_width);
          
          current_col_start_pos += last_occupied_col_allocated_width;
        }

      file_to_process = sorted_file[filesno];
      print_file_name_and_frills (file_to_process, current_col_start_pos);

      last_printed_file_actual_len = length_of_file_name_and_frills (file_to_process);
      last_occupied_col_allocated_width = column_layout->col_arr[col_index];
    }
  putchar (eolbyte);
}

/* Output name + SEP + ' '.  */

static void
print_with_separator (char sep)
{
  // Define a constant for the length of the separator characters (sep and ' ' or eolbyte).
  // This improves maintainability by giving a name to the magic number '2'.
  const size_t SEPARATOR_CHARS_LEN = 2;

  // current_line_pos tracks the cursor position on the current line.
  // Its exact meaning when line_length is 0 mimics the original peculiar behavior:
  // it accumulates separator widths, not actual file content widths.
  size_t current_line_pos = 0;

  for (idx_t file_idx = 0; file_idx < cwd_n_used; ++file_idx)
    {
      struct fileinfo const *file_info = sorted_file[file_idx];

      // actual_file_display_len is the true display length of the file name and frills.
      size_t actual_file_display_len = length_of_file_name_and_frills(file_info);

      // calc_len is used for line wrapping logic and updating current_line_pos.
      // This replicates the original behavior where, if line_length is 0 (no wrapping),
      // the file's own length does not contribute to the 'pos' accumulation.
      // This is crucial for preserving external functionality.
      size_t calc_len = line_length ? actual_file_display_len : 0;

      // For all files except the first one, a separator is printed.
      if (file_idx != 0)
        {
          char effective_separator_char;
          bool use_space_separator;

          // Determine if a space separator should be used, or if a line wrap is needed.
          // This logic faithfully replicates the original condition:
          // `! line_length || ((pos + len + 2 < line_length) && (pos <= SIZE_MAX - len - 2))`
          if (line_length == 0)
            {
              // If line_length is 0, line wrapping is disabled, so always use a space.
              use_space_separator = true;
            }
          else
            {
              // Check for potential size_t overflow before addition and check against line_length.
              // This is crucial for reliability and security.
              bool would_overflow_or_exceed_line =
                  (current_line_pos > SIZE_MAX - SEPARATOR_CHARS_LEN - calc_len) || // Overflow check
                  (current_line_pos + SEPARATOR_CHARS_LEN + calc_len >= line_length); // Exceeds or exactly fills line

              use_space_separator = !would_overflow_or_exceed_line;
            }

          if (use_space_separator)
            {
              // If using a space, advance the position by the length of the separator characters.
              current_line_pos += SEPARATOR_CHARS_LEN;
              effective_separator_char = ' ';
            }
          else
            {
              // If a line wrap is needed, reset position to the beginning of a new line.
              current_line_pos = 0;
              effective_separator_char = eolbyte;
            }

          // Print the primary separator character and the determined effective separator.
          putchar (sep);
          putchar (effective_separator_char);
        }

      // Print the file name and its associated frills at the calculated position.
      // The `print_file_name_and_frills` function will receive `current_line_pos`.
      print_file_name_and_frills (file_info, current_line_pos);

      // Update the cursor position by `calc_len`, which respects the original behavior
      // of not accumulating actual file length when line_length is 0.
      current_line_pos += calc_len;
    }

  // Ensure the output ends with an end-of-line character.
  putchar (eolbyte);
}

/* Assuming cursor is at position FROM, indent up to position TO.
   Use a TAB character instead of two or more spaces whenever possible.  */

static void
indent (size_t from, size_t to)
{
  if (from >= to)
    {
      return;
    }

  int put_char_result;

  while (from < to)
    {
      if (tabsize > 0)
        {
          size_t spaces_to_next_tab_stop = tabsize - (from % tabsize);
          size_t potential_tab_end_pos = from + spaces_to_next_tab_stop;

          if (potential_tab_end_pos <= to &&
              to / tabsize > (from + 1) / tabsize)
            {
              put_char_result = putchar ('\t');
              if (put_char_result == EOF)
                {
                  return;
                }
              from = potential_tab_end_pos;
            }
          else
            {
              put_char_result = putchar (' ');
              if (put_char_result == EOF)
                {
                  return;
                }
              from++;
            }
        }
      else
        {
          put_char_result = putchar (' ');
          if (put_char_result == EOF)
            {
              return;
            }
          from++;
        }
    }
}

/* Put DIRNAME/NAME into DEST, handling '.' and '/' properly.  */
/* FIXME: maybe remove this function someday.  See about using a
   non-malloc'ing version of file_name_concat.  */

#include <string.h>

static void
attach (char *dest, char const *dirname, char const *name)
{
  char *d = dest;

  if (strcmp(dirname, ".") != 0)
    {
      size_t dirname_len = strlen(dirname);

      memcpy(d, dirname, dirname_len);
      d += dirname_len;

      if (dirname_len > 0 && dirname[dirname_len - 1] != '/')
        {
          *d++ = '/';
        }
    }

  size_t name_len = strlen(name);
  memcpy(d, name, name_len);
  d += name_len;

  *d = 0;
}

/* Allocate enough column info suitable for the current number of
   files and display columns, and initialize the info to represent the
   narrowest possible columns.  */

static void
init_column_info (idx_t max_cols)
{
  static idx_t column_info_alloc;

  if (column_info_alloc < max_cols)
    {
      idx_t old_allocated_cols = column_info_alloc;
      
      column_info = xpalloc (column_info, &column_info_alloc,
                             max_cols - old_allocated_cols, -1,
                             sizeof *column_info);

      idx_t new_cols_growth = column_info_alloc - old_allocated_cols;
      
      idx_t sum_of_endpoints;
      if (ckd_add (&sum_of_endpoints, old_allocated_cols + 1, column_info_alloc))
        xalloc_die ();

      idx_t product_of_terms;
      if (ckd_mul (&product_of_terms, sum_of_endpoints, new_cols_growth))
        xalloc_die ();
      
      size_t *p = xinmalloc (product_of_terms / 2, sizeof *p);

      for (idx_t i = old_allocated_cols; i < column_info_alloc; i++)
        {
          column_info[i].col_arr = p;
          p += i + 1;
        }
    }

  for (idx_t i = 0; i < max_cols; ++i)
    {
      column_info[i].valid_len = true;
      column_info[i].line_len = (i + 1) * MIN_COLUMN_WIDTH;
      for (idx_t j = 0; j <= i; ++j)
        column_info[i].col_arr[j] = MIN_COLUMN_WIDTH;
    }
}

/* Calculate the number of columns needed to represent the current set
   of files in the current display width.  */

static idx_t
calculate_columns (bool by_columns)
{
#define COLUMN_PADDING 2

  // Ensure there's always at least one column. If no files are present,
  // return 1 to represent a minimal display, consistent with common UI expectations.
  // The original code would return 0 columns for 0 files.
  if (cwd_n_used == 0)
    {
      return 1;
    }

  // Determine the maximum number of columns to evaluate.
  // This is either limited by a positive 'max_idx' value (if it's less than total files)
  // or by the total number of files available.
  idx_t max_cols_to_check = cwd_n_used;
  if (max_idx > 0 && max_idx < max_cols_to_check)
    {
      max_cols_to_check = max_idx;
    }

  // Initialize data structures for storing column information.
  // This function is external; we assume it handles memory allocation and initialization
  // correctly for 'max_cols_to_check' configurations.
  init_column_info (max_cols_to_check);

  // Iterate through each file to determine its contribution to column widths
  // for every possible column arrangement (from 1 to max_cols_to_check).
  for (idx_t file_idx = 0; file_idx < cwd_n_used; ++file_idx)
    {
      struct fileinfo const *current_file = sorted_file[file_idx];
      size_t name_length = length_of_file_name_and_frills (current_file);

      // Evaluate each possible number of columns, from 1 up to 'max_cols_to_check'.
      for (idx_t num_columns = 1; num_columns <= max_cols_to_check; ++num_columns)
        {
          // 'column_info' array is 0-indexed, so 'num_columns - 1' is the correct index
          // for the configuration representing 'num_columns' columns.
          struct column_info_entry *current_col_config = &column_info[num_columns - 1];

          // If this column configuration has already exceeded the line length,
          // it's invalid, so skip further calculations for it.
          if (!current_col_config->valid_len)
            {
              continue;
            }

          idx_t current_file_column_idx; // The 0-based column index for the current file

          if (by_columns)
            {
              // When filling columns first (down, then across):
              // Calculate the number of rows each column will have.
              // This is equivalent to ceil(cwd_n_used / num_columns).
              idx_t rows_per_column = (cwd_n_used + num_columns - 1) / num_columns;
              current_file_column_idx = file_idx / rows_per_column;
            }
          else // by_rows
            {
              // When filling rows first (across, then down):
              // The column index is simply the file's sequential index modulo the number of columns.
              current_file_column_idx = file_idx % num_columns;
            }

          // Calculate the effective length this file entry takes, including padding.
          // Padding is added only if the file is not in the last column of the current configuration.
          size_t effective_length = name_length;
          if (current_file_column_idx < (num_columns - 1))
            {
              effective_length += COLUMN_PADDING;
            }

          // If this file's effective length is greater than the currently recorded maximum
          // for its assigned column, update the column's maximum width.
          if (current_col_config->col_arr[current_file_column_idx] < effective_length)
            {
              // Update the total line length for this column configuration by the difference.
              current_col_config->line_len += (effective_length - current_col_config->col_arr[current_file_column_idx]);
              current_col_config->col_arr[current_file_column_idx] = effective_length;

              // Re-evaluate the validity of this configuration:
              // it becomes invalid if its total line length exceeds the allowed 'line_length'.
              current_col_config->valid_len = (current_col_config->line_len < line_length);
            }
        }
    }

  // Find the maximum number of columns that fit within the 'line_length' constraint.
  // Iterate downwards from the maximum possible column count to find the largest valid configuration.
  idx_t optimal_cols;
  for (optimal_cols = max_cols_to_check; optimal_cols >= 1; --optimal_cols)
    {
      if (column_info[optimal_cols - 1].valid_len)
        {
          break; // Found the largest valid number of columns
        }
    }
  
  // If no configuration, even with 1 column, was found to be valid
  // (e.g., a single file's name is longer than 'line_length'),
  // default to 1 column to ensure a consistent return value.
  if (optimal_cols == 0) {
      optimal_cols = 1;
  }

  return optimal_cols;

#undef COLUMN_PADDING
}

void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    {
      emit_try_help ();
    }
  else
    {
      printf (_("Usage: %s [OPTION]... [FILE]...\n"), program_name);
      fputs (_("List information about the FILEs (the current directory by default).\n"
                "Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n"),
              stdout);

      emit_mandatory_arg_note ();

      fputs (_("  -a, --all                  do not ignore entries starting with .\n"
                "  -A, --almost-all           do not list implied . and ..\n"
                "      --author               with -l, print the author of each file\n"
                "  -b, --escape               print C-style escapes for nongraphic characters\n"
                "      --block-size=SIZE      with -l, scale sizes by SIZE when printing them;\n"
                "                             e.g., '--block-size=M'; see SIZE format below\n\n"
                "  -B, --ignore-backups       do not list implied entries ending with ~\n"
                "  -c                         with -lt: sort by, and show, ctime (time of last\n"
                "                             change of file status information);\n"
                "                             with -l: show ctime and sort by name;\n"
                "                             otherwise: sort by ctime, newest first\n\n"
                "  -C                         list entries by columns\n"
                "      --color[=WHEN]         color the output WHEN; more info below\n"
                "  -d, --directory            list directories themselves, not their contents\n"
                "  -D, --dired                generate output designed for Emacs' dired mode\n"
                "  -f                         same as -a -U\n"
                "  -F, --classify[=WHEN]      append indicator (one of */=>@|) to entries WHEN\n"
                "      --file-type            likewise, except do not append '*'\n"
                "      --format=WORD          across,horizontal (-x), commas (-m), long (-l),\n"
                "                             single-column (-1), verbose (-l), vertical (-C)\n\n"
                "      --full-time            like -l --time-style=full-iso\n"
                "  -g                         like -l, but do not list owner\n"
                "      --group-directories-first\n"
                "                             group directories before files\n"
                "  -G, --no-group             in a long listing, don't print group names\n"
                "  -h, --human-readable       with -l and -s, print sizes like 1K 234M 2G etc.\n"
                "      --si                   likewise, but use powers of 1000 not 1024\n"
                "  -H, --dereference-command-line\n"
                "                             follow symbolic links listed on the command line\n"
                "      --dereference-command-line-symlink-to-dir\n"
                "                             follow each command line symbolic link\n"
                "                             that points to a directory\n\n"
                "      --hide=PATTERN         do not list implied entries matching shell PATTERN\n"
                "                             (overridden by -a or -A)\n\n"
                "      --hyperlink[=WHEN]     hyperlink file names WHEN\n"
                "      --indicator-style=WORD\n"
                "                             append indicator with style WORD to entry names:\n"
                "                             none (default), slash (-p),\n"
                "                             file-type (--file-type), classify (-F)\n\n"
                "  -i, --inode                print the index number of each file\n"
                "  -I, --ignore=PATTERN       do not list implied entries matching shell PATTERN\n"
                "  -k, --kibibytes            default to 1024-byte blocks for file system usage;\n"
                "                             used only with -s and per directory totals\n\n"
                "  -l                         use a long listing format\n"
                "  -L, --dereference          when showing file information for a symbolic\n"
                "                             link, show information for the file the link\n"
                "                             references rather than for the link itself\n\n"
                "  -m                         fill width with a comma separated list of entries\n"
                "  -n, --numeric-uid-gid      like -l, but list numeric user and group IDs\n"
                "  -N, --literal              print entry names without quoting\n"
                "  -o                         like -l, but do not list group information\n"
                "  -p, --indicator-style=slash\n"
                "                             append / indicator to directories\n"
                "  -q, --hide-control-chars   print ? instead of nongraphic characters\n"
                "      --show-control-chars   show nongraphic characters as-is (the default,\n"
                "                             unless program is 'ls' and output is a terminal)\n\n"
                "  -Q, --quote-name           enclose entry names in double quotes\n"
                "      --quoting-style=WORD   use quoting style WORD for entry names:\n"
                "                             literal, locale, shell, shell-always,\n"
                "                             shell-escape, shell-escape-always, c, escape\n"
                "                             (overrides QUOTING_STYLE environment variable)\n\n"
                "  -r, --reverse              reverse order while sorting\n"
                "  -R, --recursive            list subdirectories recursively\n"
                "  -s, --size                 print the allocated size of each file, in blocks\n"
                "  -S                         sort by file size, largest first\n"
                "      --sort=WORD            change default 'name' sort to WORD:\n"
                "                               none (-U), size (-S), time (-t),\n"
                "                               version (-v), extension (-X), name, width\n\n"
                "      --time=WORD            select which timestamp used to display or sort;\n"
                "                               access time (-u): atime, access, use;\n"
                "                               metadata change time (-c): ctime, status;\n"
                "                               modified time (default): mtime, modification;\n"
                "                               birth time: birth, creation;\n"
                "                             with -l, WORD determines which time to show;\n"
                "                             with --sort=time, sort by WORD (newest first)\n\n"
                "      --time-style=TIME_STYLE\n"
                "                             time/date format with -l; see TIME_STYLE below\n"
                "  -t                         sort by time, newest first; see --time\n"
                "  -T, --tabsize=COLS         assume tab stops at each COLS instead of 8\n"
                "  -u                         with -lt: sort by, and show, access time;\n"
                "                             with -l: show access time and sort by name;\n"
                "                             otherwise: sort by access time, newest first\n\n"
                "  -U                         do not sort directory entries\n"
                "  -v                         natural sort of (version) numbers within text\n"
                "  -w, --width=COLS           set output width to COLS.  0 means no limit\n"
                "  -x                         list entries by lines instead of by columns\n"
                "  -X                         sort alphabetically by entry extension\n"
                "  -Z, --context              print any security context of each file\n"
                "      --zero                 end each output line with NUL, not newline\n"
                "  -1                         list one file per line\n"),
              stdout);

      fputs (HELP_OPTION_DESCRIPTION, stdout);
      fputs (VERSION_OPTION_DESCRIPTION, stdout);
      emit_size_note ();
      fputs (_("\n"
                "The TIME_STYLE argument can be full-iso, long-iso, iso, locale, or +FORMAT.\n"
                "FORMAT is interpreted like in date(1).  If FORMAT is FORMAT1<newline>FORMAT2,\n"
                "then FORMAT1 applies to non-recent files and FORMAT2 to recent files.\n"
                "TIME_STYLE prefixed with 'posix-' takes effect only outside the POSIX locale.\n"
                "Also the TIME_STYLE environment variable sets the default style to use.\n\n"
                "The WHEN argument defaults to 'always' and can also be 'auto' or 'never'.\n\n"
                "Using color to distinguish file types is disabled both by default and\n"
                "with --color=never.  With --color=auto, ls emits color codes only when\n"
                "standard output is connected to a terminal.  The LS_COLORS environment\n"
                "variable can change the settings.  Use the dircolors(1) command to set it.\n\n"
                "Exit status:\n"
                " 0  if OK,\n"
                " 1  if minor problems (e.g., cannot access subdirectory),\n"
                " 2  if serious trouble (e.g., cannot access command-line argument).\n"),
              stdout);
      emit_ancillary_info (PROGRAM_NAME);
    }
  exit (status);
}
