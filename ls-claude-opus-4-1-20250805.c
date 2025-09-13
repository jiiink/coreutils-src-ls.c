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
  return file->stat.st_mode;
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

static void dired_outbyte(char c)
{
    dired_pos++;
    if (putchar(c) == EOF) {
        return;
    }
}

/* Output the buffer S, of length S_LEN, and increment DIRED_POS by S_LEN.  */
static void
dired_outbuf (char const *s, size_t s_len)
{
  if (s == NULL || s_len == 0)
    return;
    
  if (fwrite (s, sizeof *s, s_len, stdout) != s_len)
    return;
    
  dired_pos += s_len;
}

/* Output the string S, and increment DIRED_POS by its length.  */
static void
dired_outstring (char const *s)
{
  if (s != NULL)
  {
    dired_outbuf (s, strlen (s));
  }
}

static void dired_indent(void)
{
    if (!dired) {
        return;
    }
    dired_outstring("  ");
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
static void push_current_dired_pos(struct obstack *obs)
{
    if (!dired || !obs) {
        return;
    }
    obstack_grow(obs, &dired_pos, sizeof(dired_pos));
}

/* With -R, this stack is used to help detect directory cycles.
   The device/inode pairs on this stack mirror the pairs in the
   active_dir_set hash table.  */
static struct obstack dev_ino_obstack;

/* Push a pair onto the device/inode stack.  */
static void
dev_ino_push (dev_t dev, ino_t ino)
{
  struct dev_ino *di = obstack_alloc (&dev_ino_obstack, sizeof *di);
  if (di == NULL)
    return;
  di->st_dev = dev;
  di->st_ino = ino;
}

/* Pop a dev/ino struct off the global dev_ino_obstack
   and return that struct.  */
static struct dev_ino
dev_ino_pop (void)
{
  struct dev_ino result;
  int dev_ino_size = sizeof (struct dev_ino);
  
  affirm (dev_ino_size <= obstack_object_size (&dev_ino_obstack));
  obstack_blank_fast (&dev_ino_obstack, -dev_ino_size);
  
  void *vdi = obstack_next_free (&dev_ino_obstack);
  if (vdi == NULL)
  {
    struct dev_ino empty = {0};
    return empty;
  }
  
  memcpy (&result, vdi, dev_ino_size);
  return result;
}

static void
assert_matching_dev_ino (char const *name, struct dev_ino di)
{
  struct stat sb;
  if (stat (name, &sb) != 0)
    {
      abort ();
    }
  if (sb.st_dev != di.st_dev || sb.st_ino != di.st_ino)
    {
      abort ();
    }
}

static char eolbyte = '\n';

/* Write to standard output PREFIX, followed by the quoting style and
   a space-separated list of the integers stored in OS all on one line.  */

static void
dired_dump_obstack (char const *prefix, struct obstack *os)
{
  if (!prefix || !os)
    return;

  size_t object_size = obstack_object_size (os);
  if (object_size == 0)
    return;

  size_t n_pos = object_size / sizeof (dired_pos);
  if (n_pos == 0)
    return;

  off_t *pos = obstack_finish (os);
  if (!pos)
    return;

  if (fputs (prefix, stdout) == EOF)
    return;

  for (size_t i = 0; i < n_pos; i++)
    {
      if (printf (" %jd", (intmax_t)pos[i]) < 0)
        return;
    }
  
  if (putchar ('\n') == EOF)
    return;
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
static int do_stat(char const *name, struct stat *st)
{
    if (name == NULL || st == NULL) {
        errno = EINVAL;
        return -1;
    }
    return stat(name, st);
}

static int do_lstat(char const *name, struct stat *st)
{
    if (name == NULL || st == NULL) {
        errno = EINVAL;
        return -1;
    }
    return lstat(name, st);
}

static int stat_for_mode(char const *name, struct stat *st)
{
    if (name == NULL || st == NULL) {
        errno = EINVAL;
        return -1;
    }
    return stat(name, st);
}

static int stat_for_ino(const char *name, struct stat *st)
{
    if (name == NULL || st == NULL) {
        errno = EINVAL;
        return -1;
    }
    return stat(name, st);
}

static int fstat_for_ino(int fd, struct stat *st)
{
    if (fd < 0 || st == NULL) {
        errno = EINVAL;
        return -1;
    }
    return fstat(fd, st);
}
#endif

/* Return the address of the first plain %b spec in FMT, or nullptr if
   there is no such spec.  %5b etc. do not match, so that user
   widths/flags are honored.  */

ATTRIBUTE_PURE
static char const *
first_percent_b (char const *fmt)
{
  if (!fmt)
    return nullptr;
    
  while (*fmt)
    {
      if (*fmt == '%')
        {
          if (fmt[1] == 'b')
            return fmt;
          if (fmt[1] == '%')
            fmt++;
        }
      fmt++;
    }
  return nullptr;
}

static char RFC3986[256];
static void
file_escape_init (void)
{
  for (int i = 0; i < 256; i++)
    {
      RFC3986[i] |= (c_isalnum (i) != 0) || (i == '~') || (i == '-') || (i == '.') || (i == '_');
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

  for (int i = 0; i < 12; i++)
    {
      char const *abbr = nl_langinfo (ABMON_1 + i);
      if (!abbr)
        return false;
      
      mon_len[i] = strnlen (abbr, ABFORMAT_SIZE);
      if (mon_len[i] >= ABFORMAT_SIZE)
        return false;
      
      if (strchr (abbr, '%'))
        return false;
      
      strncpy (abmon[i], abbr, ABFORMAT_SIZE - 1);
      abmon[i][ABFORMAT_SIZE - 1] = '\0';
      
      mon_width[i] = mbswidth (abmon[i], MBSWIDTH_FLAGS);
      if (mon_width[i] < 0)
        return false;
      
      if (mon_width[i] > max_mon_width)
        max_mon_width = mon_width[i];
    }

  for (int i = 0; i < 12; i++)
    {
      int fill = max_mon_width - mon_width[i];
      if (fill <= 0)
        continue;
      
      if (mon_len[i] + fill >= ABFORMAT_SIZE)
        return false;
      
      if (c_isdigit (abmon[i][0]))
        {
          memmove (abmon[i] + fill, abmon[i], mon_len[i] + 1);
          memset (abmon[i], ' ', fill);
        }
      else
        {
          memset (abmon[i] + mon_len[i], ' ', fill);
          abmon[i][mon_len[i] + fill] = '\0';
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
  char abmon[12][ABFORMAT_SIZE];
  
  for (int recent = 0; recent < 2; recent++)
    pb[recent] = first_percent_b (long_time_format[recent]);
    
  if (!pb[0] && !pb[1])
    return;
    
  if (!abmon_init (abmon))
    return;
    
  for (int recent = 0; recent < 2; recent++)
    {
      char const *fmt = long_time_format[recent];
      
      for (int i = 0; i < 12; i++)
        {
          char *nfmt = abformat[recent][i];
          int nbytes;
          
          if (!pb[recent])
            {
              nbytes = snprintf (nfmt, ABFORMAT_SIZE, "%s", fmt);
            }
          else
            {
              int prefix_len = pb[recent] - fmt;
              
              if (prefix_len > MIN (ABFORMAT_SIZE, INT_MAX) || prefix_len < 0)
                return;
                
              nbytes = snprintf (nfmt, ABFORMAT_SIZE, "%.*s%s%s",
                                 prefix_len, fmt, abmon[i], pb[recent] + 2);
            }
            
          if (nbytes < 0 || nbytes >= ABFORMAT_SIZE)
            return;
        }
    }
    
  use_abformat = true;
}

static size_t
dev_ino_hash (void const *x, size_t table_size)
{
  if (!x || table_size == 0)
    return 0;
    
  struct dev_ino const *p = x;
  return (uintmax_t) p->st_ino % table_size;
}

static bool
dev_ino_compare (void const *x, void const *y)
{
  if (x == NULL || y == NULL)
    {
      return false;
    }
  
  struct dev_ino const *a = x;
  struct dev_ino const *b = y;
  return PSAME_INODE (a, b);
}

static void dev_ino_free(void *x)
{
  free(x);
}

/* Add the device/inode pair (P->st_dev/P->st_ino) to the set of
   active directories.  Return true if there is already a matching
   entry in the table.  */

static bool
visit_dir (dev_t dev, ino_t ino)
{
  struct dev_ino *ent = xmalloc (sizeof *ent);
  ent->st_ino = ino;
  ent->st_dev = dev;

  struct dev_ino *ent_from_table = hash_insert (active_dir_set, ent);

  if (ent_from_table == NULL)
    xalloc_die ();

  if (ent_from_table != ent)
    {
      free (ent);
      return true;
    }

  return false;
}

static void
free_pending_ent (struct pending *p)
{
  if (p == NULL)
    return;
  
  free (p->name);
  free (p->realname);
  free (p);
}

static bool
is_colored (enum indicator_no type)
{
  size_t len = color_indicator[type].len;
  if (len == 0)
    return false;
  if (len > 2)
    return true;
  char const *s = color_indicator[type].string;
  if (len == 1)
    return s[0] != '0';
  return s[0] != '0' || s[1] != '0';
}

static void restore_default_color(void)
{
    put_indicator(&color_indicator[C_LEFT]);
    put_indicator(&color_indicator[C_RIGHT]);
}

static void set_normal_color(void)
{
    if (!print_with_color || !is_colored(C_NORM)) {
        return;
    }
    
    put_indicator(&color_indicator[C_LEFT]);
    put_indicator(&color_indicator[C_NORM]);
    put_indicator(&color_indicator[C_RIGHT]);
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void sighandler(int sig)
{
    if (!SA_NOCLDSTOP)
    {
        (void)signal(sig, SIG_IGN);
    }
    if (interrupt_signal == 0)
    {
        interrupt_signal = sig;
    }
}

/* A SIGTSTP was received; arrange for the program to suspend itself.  */

static void stophandler(int sig)
{
    if (!SA_NOCLDSTOP)
    {
        if (signal(sig, stophandler) == SIG_ERR)
        {
            return;
        }
    }
    
    if (!interrupt_signal)
    {
        stop_signal_count++;
    }
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
      int sig;
      sigset_t oldset;

      if (used_color)
        restore_default_color ();
      fflush (stdout);

      sigprocmask (SIG_BLOCK, &caught_signals, &oldset);

      sig = interrupt_signal;

      if (stop_signal_count)
        {
          stop_signal_count--;
          sig = SIGSTOP;
        }
      else
        {
          signal (sig, SIG_DFL);
        }

      raise (sig);
      sigprocmask (SIG_SETMASK, &oldset, NULL);
    }
}

/* Setup signal handlers if INIT is true,
   otherwise restore to the default.  */

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
  enum { nsigs = ARRAY_CARDINALITY (sig) };

#if !SA_NOCLDSTOP
  static bool caught_sig[nsigs];
#endif

  if (init)
    {
      setup_signal_handlers(sig, nsigs);
    }
  else
    {
      restore_signal_handlers(sig, nsigs);
    }
}

static void
setup_signal_handlers(int const *sig, int nsigs)
{
#if SA_NOCLDSTOP
  struct sigaction act;
  
  sigemptyset(&caught_signals);
  
  for (int j = 0; j < nsigs; j++)
    {
      sigaction(sig[j], NULL, &act);
      if (act.sa_handler != SIG_IGN)
        sigaddset(&caught_signals, sig[j]);
    }
  
  act.sa_mask = caught_signals;
  act.sa_flags = SA_RESTART;
  
  for (int j = 0; j < nsigs; j++)
    {
      if (sigismember(&caught_signals, sig[j]))
        {
          act.sa_handler = (sig[j] == SIGTSTP) ? stophandler : sighandler;
          sigaction(sig[j], &act, NULL);
        }
    }
#else
  for (int j = 0; j < nsigs; j++)
    {
      void (*old_handler)(int) = signal(sig[j], SIG_IGN);
      caught_sig[j] = (old_handler != SIG_IGN);
      
      if (caught_sig[j])
        {
          void (*handler)(int) = (sig[j] == SIGTSTP) ? stophandler : sighandler;
          signal(sig[j], handler);
          siginterrupt(sig[j], 0);
        }
    }
#endif
}

static void
restore_signal_handlers(int const *sig, int nsigs)
{
#if SA_NOCLDSTOP
  for (int j = 0; j < nsigs; j++)
    {
      if (sigismember(&caught_signals, sig[j]))
        signal(sig[j], SIG_DFL);
    }
#else
  for (int j = 0; j < nsigs; j++)
    {
      if (caught_sig[j])
        signal(sig[j], SIG_DFL);
    }
#endif
}

static void signal_init(void)
{
    signal_setup(true);
}

static void signal_restore(void)
{
    signal_setup(false);
}

int
main (int argc, char **argv)
{
  int i;
  struct pending *thispend;
  int n_files;

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

  i = decode_switches (argc, argv);

  if (print_with_color)
    parse_ls_color ();

  if (print_with_color)
    {
      tabsize = 0;
    }

  if (directories_first)
    {
      check_symlink_mode = true;
    }
  else if (print_with_color)
    {
      if (is_colored (C_ORPHAN)
          || (is_colored (C_EXEC) && color_symlink_as_referent)
          || (is_colored (C_MISSING) && format == long_format))
        check_symlink_mode = true;
    }

  if (dereference == DEREF_UNDEFINED)
    {
      dereference = ((immediate_dirs
                      || indicator_style == classify
                      || format == long_format)
                     ? DEREF_NEVER
                     : DEREF_COMMAND_LINE_SYMLINK_TO_DIR);
    }

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

  format_needs_stat = ((sort_type == sort_time) || (sort_type == sort_size)
                       || (format == long_format)
                       || print_block_size || print_hyperlink || print_scontext);
  format_needs_type = ((!format_needs_stat)
                       && (recursive || print_with_color || print_scontext
                           || directories_first
                           || (indicator_style != none)));
  format_needs_capability = print_with_color && is_colored (C_CAP);

  if (dired)
    {
      obstack_init (&dired_obstack);
      obstack_init (&subdired_obstack);
    }

  if (print_hyperlink)
    {
      file_escape_init ();

      hostname = xgethostname ();
      if (!hostname)
        hostname = "";
    }

  cwd_n_alloc = 100;
  cwd_file = xmalloc (cwd_n_alloc * sizeof *cwd_file);
  cwd_n_used = 0;

  clear_files ();

  n_files = argc - i;

  if (n_files <= 0)
    {
      if (immediate_dirs)
        gobble_file (".", directory, NOT_AN_INODE_NUMBER, true, nullptr);
      else
        queue_directory (".", nullptr, true);
    }
  else
    {
      do
        {
          gobble_file (argv[i++], unknown, NOT_AN_INODE_NUMBER, true, nullptr);
        }
      while (i < argc);
    }

  if (cwd_n_used)
    {
      sort_files ();
      if (!immediate_dirs)
        extract_dirs_from_files (nullptr, true);
    }

  if (cwd_n_used)
    {
      print_current_files ();
      if (pending_dirs)
        dired_outbyte ('\n');
    }
  else if (n_files <= 1 && pending_dirs && pending_dirs->next == 0)
    {
      print_dir_name = false;
    }

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

  if (print_with_color && used_color)
    {
      int j;

      if (!(color_indicator[C_LEFT].len == 2
            && memcmp (color_indicator[C_LEFT].string, "\033[", 2) == 0
            && color_indicator[C_RIGHT].len == 1
            && color_indicator[C_RIGHT].string[0] == 'm'))
        {
          restore_default_color ();
        }

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

  return exit_status;
}

/* Return the line length indicated by the value given by SPEC, or -1
   if unsuccessful.  0 means no limit on line length.  */

static ptrdiff_t
decode_line_length (char const *spec)
{
  uintmax_t val;
  ptrdiff_t max_val = PTRDIFF_MAX;
  
  if (SIZE_MAX < PTRDIFF_MAX)
    max_val = SIZE_MAX;

  switch (xstrtoumax (spec, NULL, 0, &val, ""))
    {
    case LONGINT_OK:
      if (val <= max_val)
        return val;
      return 0;

    case LONGINT_OVERFLOW:
      return 0;

    case LONGINT_INVALID:
    case LONGINT_INVALID_SUFFIX_CHAR:
    case LONGINT_INVALID_SUFFIX_CHAR_WITH_OVERFLOW:
      return -1;

    default:
      return -1;
    }
}

/* Return true if standard output is a tty, caching the result.  */

static bool
stdout_isatty (void)
{
  static signed char out_tty = -1;
  if (out_tty < 0)
    {
      int result = isatty (STDOUT_FILENO);
      out_tty = (result != 0) ? 1 : 0;
    }
  return out_tty != 0;
}

/* Set all the option flags according to the switches specified.
   Return the index of the first non-option argument.  */

static int
decode_switches (int argc, char **argv)
{
  char const *time_style_option = NULL;
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
      int c = getopt_long (argc, argv,
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
          ignore_mode = IGNORE_MINIMAL;
          sort_opt = sort_none;
          break;
        case FILE_TYPE_INDICATOR_OPTION:
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
        case 'o':
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
          width_opt = decode_line_length (optarg);
          if (width_opt < 0)
            error (LS_FAILURE, 0, "%s: %s", _("invalid line width"),
                   quote (optarg));
          break;
        case 'x':
          format_opt = horizontal;
          break;
        case 'A':
          ignore_mode = IGNORE_DOT_AND_DOTDOT;
          break;
        case 'B':
          add_ignore_pattern ("*~");
          add_ignore_pattern (".*~");
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
            int i = optarg ? XARGMATCH ("--classify", optarg, when_args, when_types)
                           : when_always;
            if (i == when_always || (i == when_if_tty && stdout_isatty ()))
              indicator_style = classify;
          }
          break;
        case 'G':
          print_group = false;
          break;
        case 'H':
          dereference = DEREF_COMMAND_LINE_ARGUMENTS;
          break;
        case DEREFERENCE_COMMAND_LINE_SYMLINK_TO_DIR_OPTION:
          dereference = DEREF_COMMAND_LINE_SYMLINK_TO_DIR;
          break;
        case 'I':
          add_ignore_pattern (optarg);
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
          tabsize_opt = xnumtoumax (optarg, 0, 0, MIN (PTRDIFF_MAX, SIZE_MAX),
                                    "", _("invalid tab size"), LS_FAILURE, 0);
          break;
        case 'U':
          sort_opt = sort_none;
          break;
        case 'X':
          sort_opt = sort_extension;
          break;
        case '1':
          if (format_opt != long_format)
            format_opt = one_per_line;
          break;
        case AUTHOR_OPTION:
          print_author = true;
          break;
        case HIDE_OPTION:
          {
            struct ignore_pattern *hide = xmalloc (sizeof *hide);
            hide->pattern = optarg;
            hide->next = hide_patterns;
            hide_patterns = hide;
          }
          break;
        case SORT_OPTION:
          sort_opt = XARGMATCH ("--sort", optarg, sort_args, sort_types);
          break;
        case GROUP_DIRECTORIES_FIRST_OPTION:
          directories_first = true;
          break;
        case TIME_OPTION:
          time_type = XARGMATCH ("--time", optarg, time_args, time_types);
          explicit_time = true;
          break;
        case FORMAT_OPTION:
          format_opt = XARGMATCH ("--format", optarg, format_args,
                                  format_types);
          break;
        case FULL_TIME_OPTION:
          format_opt = long_format;
          time_style_option = "full-iso";
          break;
        case COLOR_OPTION:
          {
            int i = optarg ? XARGMATCH ("--color", optarg, when_args, when_types)
                           : when_always;
            print_with_color = (i == when_always
                                || (i == when_if_tty && stdout_isatty ()));
          }
          break;
        case HYPERLINK_OPTION:
          {
            int i = optarg ? XARGMATCH ("--hyperlink", optarg, when_args, when_types)
                           : when_always;
            print_hyperlink = (i == when_always
                               || (i == when_if_tty && stdout_isatty ()));
          }
          break;
        case INDICATOR_STYLE_OPTION:
          indicator_style = XARGMATCH ("--indicator-style", optarg,
                                       indicator_style_args,
                                       indicator_style_types);
          break;
        case QUOTING_STYLE_OPTION:
          quoting_style_opt = XARGMATCH ("--quoting-style", optarg,
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
            enum strtol_error e = human_options (optarg, &human_output_opts,
                                                 &output_block_size);
            if (e != LONGINT_OK)
              xstrtol_fatal (e, oi, 0, long_options, optarg);
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
          usage (LS_FAILURE);
        }
    }

  if (!output_block_size)
    {
      char const *ls_block_size = getenv ("LS_BLOCK_SIZE");
      human_options (ls_block_size,
                     &human_output_opts, &output_block_size);
      if (ls_block_size || getenv ("BLOCK_SIZE"))
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
            : ls_mode == LS_LS ? (stdout_isatty ()
                                  ? many_per_line : one_per_line)
            : ls_mode == LS_MULTI_COL ? many_per_line
            : long_format);

  ptrdiff_t linelen = width_opt;
  if (format == many_per_line || format == horizontal || format == with_commas
      || print_with_color)
    {
#ifdef TIOCGWINSZ
      if (linelen < 0)
        {
          struct winsize ws;
          if (stdout_isatty ()
              && 0 <= ioctl (STDOUT_FILENO, TIOCGWINSZ, &ws)
              && 0 < ws.ws_col)
            linelen = ws.ws_col <= MIN (PTRDIFF_MAX, SIZE_MAX) ? ws.ws_col : 0;
        }
#endif
      if (linelen < 0)
        {
          char const *p = getenv ("COLUMNS");
          if (p && *p)
            {
              linelen = decode_line_length (p);
              if (linelen < 0)
                error (0, 0,
                       _("ignoring invalid width"
                         " in environment variable COLUMNS: %s"),
                       quote (p));
            }
        }
    }

  line_length = linelen < 0 ? 80 : linelen;
  max_idx = line_length / MIN_COLUMN_WIDTH;
  max_idx += line_length % MIN_COLUMN_WIDTH != 0;

  if (format == many_per_line || format == horizontal || format == with_commas)
    {
      if (0 <= tabsize_opt)
        tabsize = tabsize_opt;
      else
        {
          tabsize = 8;
          char const *p = getenv ("TABSIZE");
          if (p)
            {
              uintmax_t tmp;
              if (xstrtoumax (p, NULL, 0, &tmp, "") == LONGINT_OK
                  && tmp <= SIZE_MAX)
                tabsize = tmp;
              else
                error (0, 0,
                       _("ignoring invalid tab size"
                         " in environment variable TABSIZE: %s"),
                       quote (p));
            }
        }
    }

  qmark_funny_chars = (hide_control_chars_opt < 0
                       ? ls_mode == LS_LS && stdout_isatty ()
                       : hide_control_chars_opt);

  int qs = quoting_style_opt;
  if (qs < 0)
    qs = getenv_quoting_style ();
  if (qs < 0)
    qs = (ls_mode == LS_LS
          ? (stdout_isatty () ? shell_escape_quoting_style : -1)
          : escape_quoting_style);
  if (0 <= qs)
    set_quoting_style (NULL, qs);
  qs = get_quoting_style (NULL);
  align_variable_outer_quotes
    = ((format == long_format
        || ((format == many_per_line || format == horizontal) && line_length))
       && (qs == shell_quoting_style
           || qs == shell_escape_quoting_style
           || qs == c_maybe_quoting_style));
  filename_quoting_options = clone_quoting_options (NULL);
  if (qs == escape_quoting_style)
    set_char_quoting (filename_quoting_options, ' ', 1);
  if (file_type <= indicator_style)
    {
      char const *p;
      for (p = &"*=>@|"[indicator_style - file_type]; *p; p++)
        set_char_quoting (filename_quoting_options, *p, 1);
    }

  dirname_quoting_options = clone_quoting_options (NULL);
  set_char_quoting (dirname_quoting_options, ':', 1);

  dired &= (format == long_format) & !print_hyperlink;

  if (eolbyte < dired)
    error (LS_FAILURE, 0, _("--dired and --zero are incompatible"));

  sort_type = (0 <= sort_opt ? sort_opt
               : (format != long_format && explicit_time)
               ? sort_time : sort_name);

  if (format == long_format)
    {
      char const *style = time_style_option;
      static char const posix_prefix[] = "posix-";

      if (!style)
        {
          style = getenv ("TIME_STYLE");
          if (!style)
            style = "locale";
        }

      while (STREQ_LEN (style, posix_prefix, sizeof posix_prefix - 1))
        {
          if (!hard_locale (LC_TIME))
            return optind;
          style += sizeof posix_prefix - 1;
        }

      if (*style == '+')
        {
          char const *p0 = style + 1;
          char *p0nl = strchr (p0, '\n');
          char const *p1 = p0;
          if (p0nl)
            {
              if (strchr (p0nl + 1, '\n'))
                error (LS_FAILURE, 0, _("invalid time style format %s"),
                       quote (p0));
              *p0nl++ = '\0';
              p1 = p0nl;
            }
          long_time_format[0] = p0;
          long_time_format[1] = p1;
        }
      else
        {
          switch (x_timestyle_match (style, true,
                                     time_style_args,
                                     (char const *) time_style_types,
                                     sizeof (*time_style_types), LS_FAILURE))
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
              if (hard_locale (LC_TIME))
                {
                  for (int i = 0; i < 2; i++)
                    long_time_format[i] =
                      dcgettext (NULL, long_time_format[i], LC_TIME);
                }
            }
        }
      abformat_init ();
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

static bool
get_funky_string (char **dest, char const **src, bool equals_end,
                  size_t *output_count)
{
  char num = 0;
  size_t count = 0;
  enum {
    ST_GND, ST_BACKSLASH, ST_OCTAL, ST_HEX, ST_CARET, ST_END, ST_ERROR
  } state = ST_GND;
  char const *p = *src;
  char *q = *dest;

  if (!dest || !src || !output_count || !*dest || !*src)
    return false;

  while (state < ST_END)
    {
      switch (state)
        {
        case ST_GND:
          if (*p == ':' || *p == '\0')
            state = ST_END;
          else if (*p == '\\')
            {
              state = ST_BACKSLASH;
              ++p;
            }
          else if (*p == '^')
            {
              state = ST_CARET;
              ++p;
            }
          else if (*p == '=' && equals_end)
            state = ST_END;
          else
            {
              *(q++) = *(p++);
              ++count;
            }
          break;

        case ST_BACKSLASH:
          if (*p >= '0' && *p <= '7')
            {
              state = ST_OCTAL;
              num = *p - '0';
              ++p;
            }
          else if (*p == 'x' || *p == 'X')
            {
              state = ST_HEX;
              num = 0;
              ++p;
            }
          else if (*p == '\0')
            {
              state = ST_ERROR;
            }
          else
            {
              switch (*p)
                {
                case 'a': num = '\a'; break;
                case 'b': num = '\b'; break;
                case 'e': num = 27; break;
                case 'f': num = '\f'; break;
                case 'n': num = '\n'; break;
                case 'r': num = '\r'; break;
                case 't': num = '\t'; break;
                case 'v': num = '\v'; break;
                case '?': num = 127; break;
                case '_': num = ' '; break;
                default: num = *p; break;
                }
              *(q++) = num;
              ++count;
              state = ST_GND;
              ++p;
            }
          break;

        case ST_OCTAL:
          if (*p >= '0' && *p <= '7')
            {
              num = (num << 3) + (*p - '0');
              ++p;
            }
          else
            {
              *(q++) = num;
              ++count;
              state = ST_GND;
            }
          break;

        case ST_HEX:
          if (*p >= '0' && *p <= '9')
            {
              num = (num << 4) + (*p - '0');
              ++p;
            }
          else if (*p >= 'a' && *p <= 'f')
            {
              num = (num << 4) + (*p - 'a' + 10);
              ++p;
            }
          else if (*p >= 'A' && *p <= 'F')
            {
              num = (num << 4) + (*p - 'A' + 10);
              ++p;
            }
          else
            {
              *(q++) = num;
              ++count;
              state = ST_GND;
            }
          break;

        case ST_CARET:
          if (*p >= '@' && *p <= '~')
            {
              *(q++) = *p & 037;
              ++p;
              ++count;
              state = ST_GND;
            }
          else if (*p == '?')
            {
              *(q++) = 127;
              ++p;
              ++count;
              state = ST_GND;
            }
          else
            {
              state = ST_ERROR;
            }
          break;

        default:
          state = ST_ERROR;
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

static bool
known_term_type (void)
{
  char const *term = getenv ("TERM");
  if (term == NULL || term[0] == '\0')
    return false;

  char const *line = G_line;
  size_t offset = 0;
  size_t line_size = sizeof (G_line);
  
  while (offset < line_size)
    {
      if (STRNCMP_LIT (line, "TERM ") == 0)
        {
          if (fnmatch (line + 5, term, 0) == 0)
            return true;
        }
      
      size_t len = strlen (line);
      if (len >= line_size - offset)
        break;
        
      offset += len + 1;
      line = G_line + offset;
    }

  return false;
}

static void
parse_ls_color (void)
{
  char const *p;
  char *buf;
  char label0, label1;
  struct color_ext_type *ext;

  p = getenv ("LS_COLORS");
  if (p == nullptr || *p == '\0')
    {
      char const *colorterm = getenv ("COLORTERM");
      if (! (colorterm && *colorterm) && ! known_term_type ())
        print_with_color = false;
      return;
    }

  ext = nullptr;
  buf = color_buf = xstrdup (p);
  enum parse_state state = PS_START;

  while (state != PS_DONE && state != PS_FAIL)
    {
      if (state == PS_START)
        {
          if (*p == ':')
            {
              ++p;
            }
          else if (*p == '*')
            {
              ext = xmalloc (sizeof *ext);
              ext->next = color_ext_list;
              color_ext_list = ext;
              ext->exact_match = false;
              ++p;
              ext->ext.string = buf;
              state = get_funky_string (&buf, &p, true, &ext->ext.len)
                      ? PS_4 : PS_FAIL;
            }
          else if (*p == '\0')
            {
              state = PS_DONE;
            }
          else
            {
              label0 = *p++;
              state = PS_2;
            }
        }
      else if (state == PS_2)
        {
          if (*p)
            {
              label1 = *p++;
              state = PS_3;
            }
          else
            {
              state = PS_FAIL;
            }
        }
      else if (state == PS_3)
        {
          if (*p++ != '=')
            {
              state = PS_FAIL;
            }
          else
            {
              state = PS_FAIL;
              for (int i = 0; i < ARRAY_CARDINALITY (indicator_name); i++)
                {
                  if (label0 == indicator_name[i][0] &&
                      label1 == indicator_name[i][1])
                    {
                      color_indicator[i].string = buf;
                      state = get_funky_string (&buf, &p, false,
                                               &color_indicator[i].len)
                              ? PS_START : PS_FAIL;
                      break;
                    }
                }
              if (state == PS_FAIL)
                {
                  error (0, 0, _("unrecognized prefix: %s"),
                         quote ((char []) {label0, label1, '\0'}));
                }
            }
        }
      else if (state == PS_4)
        {
          if (*p++ != '=')
            {
              state = PS_FAIL;
            }
          else
            {
              ext->seq.string = buf;
              state = get_funky_string (&buf, &p, false, &ext->seq.len)
                      ? PS_START : PS_FAIL;
            }
        }
    }

  if (state == PS_FAIL)
    {
      struct color_ext_type *e = color_ext_list;
      struct color_ext_type *e2;
      
      error (0, 0,
             _("unparsable value for LS_COLORS environment variable"));
      free (color_buf);
      
      while (e != nullptr)
        {
          e2 = e;
          e = e->next;
          free (e2);
        }
      color_ext_list = nullptr;
      print_with_color = false;
      return;
    }

  struct color_ext_type *e1;
  for (e1 = color_ext_list; e1 != nullptr; e1 = e1->next)
    {
      struct color_ext_type *e2;
      bool case_ignored = false;

      for (e2 = e1->next; e2 != nullptr; e2 = e2->next)
        {
          if (e2->ext.len >= SIZE_MAX || e1->ext.len != e2->ext.len)
            continue;

          if (memcmp (e1->ext.string, e2->ext.string, e1->ext.len) == 0)
            {
              e2->ext.len = SIZE_MAX;
            }
          else if (c_strncasecmp (e1->ext.string, e2->ext.string,
                                  e1->ext.len) == 0)
            {
              if (case_ignored)
                {
                  e2->ext.len = SIZE_MAX;
                }
              else if (e1->seq.len == e2->seq.len &&
                       memcmp (e1->seq.string, e2->seq.string,
                              e1->seq.len) == 0)
                {
                  e2->ext.len = SIZE_MAX;
                  case_ignored = true;
                }
              else
                {
                  e1->exact_match = true;
                  e2->exact_match = true;
                }
            }
        }
    }

  if (color_indicator[C_LINK].len == 6 &&
      !STRNCMP_LIT (color_indicator[C_LINK].string, "target"))
    {
      color_symlink_as_referent = true;
    }
}

/* Return the quoting style specified by the environment variable
   QUOTING_STYLE if set and valid, -1 otherwise.  */

static int
getenv_quoting_style (void)
{
  char const *q_style = getenv ("QUOTING_STYLE");
  if (!q_style)
    return -1;
  
  int i = ARGMATCH (q_style, quoting_style_args, quoting_style_vals);
  if (i < 0)
    {
      error (0, 0,
             _("ignoring invalid value"
               " of environment variable QUOTING_STYLE: %s"),
             quote (q_style));
      return -1;
    }
  
  return quoting_style_vals[i];
}

/* Set the exit status to report a failure.  If SERIOUS, it is a
   serious failure; otherwise, it is merely a minor problem.  */

static void
set_exit_status (bool serious)
{
  if (serious)
  {
    exit_status = LS_FAILURE;
  }
  else if (exit_status == EXIT_SUCCESS)
  {
    exit_status = LS_MINOR_PROBLEM;
  }
}

/* Assuming a failure is serious if SERIOUS, use the printf-style
   MESSAGE to report the failure to access a file named FILE.  Assume
   errno is set appropriately for the failure.  */

static void
file_failure (bool serious, char const *message, char const *file)
{
  if (message == NULL || file == NULL)
    return;
    
  error (0, errno, message, quoteaf (file));
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
  struct pending *new = xmalloc (sizeof *new);
  if (!new)
    return;
  
  new->realname = realname ? xstrdup (realname) : NULL;
  new->name = name ? xstrdup (name) : NULL;
  new->command_line_arg = command_line_arg;
  new->next = pending_dirs;
  pending_dirs = new;
}

/* Read directory NAME, and list the files in it.
   If REALNAME is nonzero, print its name instead of NAME;
   this is used for symbolic links to directories.
   COMMAND_LINE_ARG means this directory was mentioned on the command line.  */

static void
print_dir (char const *name, char const *realname, bool command_line_arg)
{
  DIR *dirp;
  struct dirent *next;
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
      if (!check_directory_loop (dirp, name, command_line_arg))
        {
          closedir (dirp);
          return;
        }
    }

  clear_files ();

  if (recursive || print_dir_name)
    {
      print_directory_header (name, realname, &first, command_line_arg);
    }

  total_blocks = process_directory_entries (dirp, name, command_line_arg);

  if (closedir (dirp) != 0)
    {
      file_failure (command_line_arg, _("closing directory %s"), name);
    }

  sort_files ();

  if (recursive)
    extract_dirs_from_files (name, false);

  if (format == long_format || print_block_size)
    {
      print_total_blocks (total_blocks);
    }

  if (cwd_n_used)
    print_current_files ();
}

static bool
check_directory_loop (DIR *dirp, char const *name, bool command_line_arg)
{
  struct stat dir_stat;
  int fd = dirfd (dirp);

  if ((0 <= fd
       ? fstat_for_ino (fd, &dir_stat)
       : stat_for_ino (name, &dir_stat)) < 0)
    {
      file_failure (command_line_arg,
                    _("cannot determine device and inode of %s"), name);
      return false;
    }

  if (visit_dir (dir_stat.st_dev, dir_stat.st_ino))
    {
      error (0, 0, _("%s: not listing already-listed directory"),
             quotef (name));
      set_exit_status (true);
      return false;
    }

  dev_ino_push (dir_stat.st_dev, dir_stat.st_ino);
  return true;
}

static void
print_directory_header (char const *name, char const *realname, 
                        bool *first, bool command_line_arg)
{
  if (!*first)
    dired_outbyte ('\n');
  *first = false;
  dired_indent ();

  char *absolute_name = nullptr;
  if (print_hyperlink)
    {
      absolute_name = canonicalize_filename_mode (name, CAN_MISSING);
      if (!absolute_name)
        file_failure (command_line_arg,
                      _("error canonicalizing %s"), name);
    }
  
  quote_name (realname ? realname : name, dirname_quoting_options, -1,
              nullptr, true, &subdired_obstack, absolute_name);

  free (absolute_name);
  dired_outstring (":\n");
}

static uintmax_t
process_directory_entries (DIR *dirp, char const *name, bool command_line_arg)
{
  struct dirent *next;
  uintmax_t total_blocks = 0;

  while (true)
    {
      errno = 0;
      next = readdir (dirp);
      
      if (!next)
        {
          if (!handle_readdir_error (errno, command_line_arg, name))
            break;
          continue;
        }

      if (file_ignored (next->d_name))
        continue;

      total_blocks += process_single_entry (next, name);
      
      maybe_print_immediately ();
      process_signals ();
    }

  return total_blocks;
}

static bool
handle_readdir_error (int err, bool command_line_arg, char const *name)
{
  if (err == 0)
    return false;
    
#if ! (2 < __GLIBC__ + (3 <= __GLIBC_MINOR__))
  if (err == ENOENT)
    return false;
#endif

  file_failure (command_line_arg, _("reading directory %s"), name);
  return err == EOVERFLOW;
}

static uintmax_t
process_single_entry (struct dirent *entry, char const *dir_name)
{
  enum filetype type;
#if HAVE_STRUCT_DIRENT_D_TYPE
  type = d_type_filetype[entry->d_type];
#else
  type = unknown;
#endif
  
  return gobble_file (entry->d_name, type,
                     RELIABLE_D_INO (entry),
                     false, dir_name);
}

static void
maybe_print_immediately (void)
{
  if (format == one_per_line && sort_type == sort_none
      && !print_block_size && !recursive)
    {
      sort_files ();
      print_current_files ();
      clear_files ();
    }
}

static void
print_total_blocks (uintmax_t total_blocks)
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

/* Add 'pattern' to the list of patterns for which files that match are
   not listed.  */

static void
add_ignore_pattern (char const *pattern)
{
  struct ignore_pattern *ignore;

  if (pattern == NULL)
    return;

  ignore = xmalloc (sizeof *ignore);
  if (ignore == NULL)
    return;

  ignore->pattern = pattern;
  ignore->next = ignore_patterns;
  ignore_patterns = ignore;
}

/* Return true if one of the PATTERNS matches FILE.  */

static bool
patterns_match (struct ignore_pattern const *patterns, char const *file)
{
  if (!patterns || !file)
    return false;
    
  struct ignore_pattern const *p = patterns;
  while (p)
    {
      if (p->pattern && fnmatch (p->pattern, file, FNM_PERIOD) == 0)
        return true;
      p = p->next;
    }
  return false;
}

/* Return true if FILE should be ignored.  */

static bool
file_ignored (char const *name)
{
  if (name == NULL) {
    return false;
  }

  if (ignore_mode != IGNORE_MINIMAL && name[0] == '.') {
    if (ignore_mode == IGNORE_DEFAULT) {
      return true;
    }
    if (name[1] == '\0') {
      return true;
    }
    if (name[1] == '.' && name[2] == '\0') {
      return true;
    }
  }

  if (ignore_mode == IGNORE_DEFAULT && patterns_match (hide_patterns, name)) {
    return true;
  }

  return patterns_match (ignore_patterns, name);
}

/* POSIX requires that a file size be printed without a sign, even
   when negative.  Assume the typical case where negative sizes are
   actually positive values that have wrapped around.  */

static uintmax_t
unsigned_file_size (off_t size)
{
  if (size < 0) {
    return (uintmax_t)size + ((uintmax_t)OFF_T_MAX - (uintmax_t)OFF_T_MIN + 1);
  }
  return (uintmax_t)size;
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
static bool has_capability(MAYBE_UNUSED char const *name)
{
    errno = ENOTSUP;
    return false;
}
#endif

/* Enter and remove entries in the table 'cwd_file'.  */

static void
free_ent (struct fileinfo *f)
{
  if (f == NULL)
    return;
    
  free (f->name);
  free (f->linkname);
  free (f->absolute_name);
  
  if (f->scontext != UNKNOWN_SECURITY_CONTEXT)
    {
      aclinfo_scontext_free (f->scontext);
      f->scontext = UNKNOWN_SECURITY_CONTEXT;
    }
    
  f->name = NULL;
  f->linkname = NULL;
  f->absolute_name = NULL;
}

/* Empty the table of files.  */
static void
clear_files (void)
{
  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
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
static int
file_has_aclinfo_cache (char const *file, struct fileinfo *f,
                        struct aclinfo *ai, int flags)
{
  static int unsupported_return;
  static char *unsupported_scontext;
  static int unsupported_scontext_err;
  static dev_t unsupported_device;

  if (f->stat_ok && unsupported_scontext
      && f->stat.st_dev == unsupported_device)
    {
      ai->buf = ai->u.__gl_acl_ch;
      ai->size = 0;
      ai->scontext = unsupported_scontext;
      ai->scontext_err = unsupported_scontext_err;
      errno = ENOTSUP;
      return unsupported_return;
    }

  errno = 0;
  int n = file_has_aclinfo (file, ai, flags);
  int err = errno;
  
  if (!f->stat_ok || n > 0)
    {
      return n;
    }
  
  if (acl_errno_valid (err))
    {
      return n;
    }
  
  if ((flags & ACL_GET_SCONTEXT) && acl_errno_valid (ai->scontext_err))
    {
      return n;
    }
  
  unsupported_return = n;
  unsupported_scontext = ai->scontext;
  unsupported_scontext_err = ai->scontext_err;
  unsupported_device = f->stat.st_dev;
  
  return n;
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

  bool has_cap = has_capability (file);
  
  if (!has_cap && f->stat_ok && !acl_errno_valid (errno))
    {
      unsupported_cached = true;
      unsupported_device = f->stat.st_dev;
    }
  
  return has_cap;
}

static bool needs_quoting(char const *name)
{
    if (name == NULL) {
        return false;
    }
    
    char test[2];
    size_t len = quotearg_buffer(test, sizeof test, name, -1,
                                  filename_quoting_options);
    
    if (len == 0) {
        return false;
    }
    
    return *name != test[0] || strlen(name) != len;
}

/* Add a file to the current table of files.
   Verify that the file exists, and print an error message if it does not.
   Return the number of blocks that the file occupies.  */
static uintmax_t
gobble_file (char const *name, enum filetype type, ino_t inode,
             bool command_line_arg, char const *dirname)
{
  affirm (! command_line_arg || inode == NOT_AN_INODE_NUMBER);

  if (cwd_n_used == cwd_n_alloc)
    cwd_file = xpalloc (cwd_file, &cwd_n_alloc, 1, -1, sizeof *cwd_file);

  struct fileinfo *f = &cwd_file[cwd_n_used];
  memset (f, '\0', sizeof *f);
  f->stat.st_ino = inode;
  f->filetype = type;
  f->scontext = UNKNOWN_SECURITY_CONTEXT;
  f->quoted = -1;

  if ((! cwd_some_quoted) && align_variable_outer_quotes)
    {
      f->quoted = needs_quoting (name);
      if (f->quoted)
        cwd_some_quoted = 1;
    }

  bool check_stat = needs_stat_check(command_line_arg, type, inode);
  
  char const *full_name = name;
  if ((check_stat | print_scontext | format_needs_capability) 
      && name[0] != '/' && dirname)
    {
      char *p = alloca (strlen (name) + strlen (dirname) + 2);
      attach (p, dirname, name);
      full_name = p;
    }

  bool do_deref = false;
  if (check_stat)
    {
      int err = perform_stat_operation(full_name, f, command_line_arg, &do_deref);
      if (err != 0)
        {
          file_failure (command_line_arg, _("cannot access %s"), full_name);
          if (command_line_arg)
            return 0;
          f->name = xstrdup (name);
          cwd_n_used++;
          return 0;
        }
      f->stat_ok = true;
      f->filetype = type = d_type_filetype[IFTODT (f->stat.st_mode)];
    }
  else
    {
      do_deref = dereference == DEREF_ALWAYS;
    }

  if (type == directory && command_line_arg && !immediate_dirs)
    f->filetype = type = arg_directory;

  process_security_context(full_name, f, type, do_deref);
  process_symlink_info(full_name, f, type, command_line_arg);
  
  uintmax_t blocks = update_width_metrics(f, type);
  
  f->name = xstrdup (name);
  cwd_n_used++;
  return blocks;
}

static bool needs_stat_check(bool command_line_arg, enum filetype type, ino_t inode)
{
  if (command_line_arg || print_hyperlink || format_needs_stat)
    return true;
    
  if (format_needs_type && type == unknown)
    return true;
    
  if ((type == directory || type == unknown) && print_with_color)
    {
      if (is_colored (C_OTHER_WRITABLE) || is_colored (C_STICKY) 
          || is_colored (C_STICKY_OTHER_WRITABLE))
        return true;
    }
    
  if (print_inode || format_needs_type)
    {
      if ((type == symbolic_link || type == unknown) 
          && (dereference == DEREF_ALWAYS || color_symlink_as_referent 
              || check_symlink_mode))
        return true;
    }
    
  if (print_inode && inode == NOT_AN_INODE_NUMBER)
    return true;
    
  if (type == normal || type == unknown)
    {
      if (indicator_style == classify)
        return true;
      if (print_with_color && (is_colored (C_EXEC) || is_colored (C_SETUID) 
          || is_colored (C_SETGID)))
        return true;
    }
    
  return false;
}

static int perform_stat_operation(char const *full_name, struct fileinfo *f, 
                                  bool command_line_arg, bool *do_deref)
{
  int err;
  
  if (print_hyperlink)
    {
      f->absolute_name = canonicalize_filename_mode (full_name, CAN_MISSING);
      if (! f->absolute_name)
        file_failure (command_line_arg, _("error canonicalizing %s"), full_name);
    }

  switch (dereference)
    {
    case DEREF_ALWAYS:
      err = do_stat (full_name, &f->stat);
      *do_deref = true;
      break;

    case DEREF_COMMAND_LINE_ARGUMENTS:
    case DEREF_COMMAND_LINE_SYMLINK_TO_DIR:
      if (command_line_arg)
        {
          err = do_stat (full_name, &f->stat);
          *do_deref = true;
          
          if (dereference == DEREF_COMMAND_LINE_ARGUMENTS)
            break;
            
          bool need_lstat = (err < 0
                            ? (errno == ENOENT || errno == ELOOP)
                            : ! S_ISDIR (f->stat.st_mode));
          if (!need_lstat)
            break;
        }
      FALLTHROUGH;

    case DEREF_NEVER:
      err = do_lstat (full_name, &f->stat);
      *do_deref = false;
      break;

    case DEREF_UNDEFINED:
    default:
      unreachable ();
    }
    
  return err;
}

static void process_security_context(char const *full_name, struct fileinfo *f, 
                                     enum filetype type, bool do_deref)
{
  bool get_scontext = (format == long_format) | print_scontext;
  bool check_capability = format_needs_capability & (type == normal);

  if (!get_scontext && !check_capability)
    return;

  struct aclinfo ai;
  int aclinfo_flags = ((do_deref ? ACL_SYMLINK_FOLLOW : 0)
                       | (get_scontext ? ACL_GET_SCONTEXT : 0)
                       | filetype_d_type[type]);
  int n = file_has_aclinfo_cache (full_name, f, &ai, aclinfo_flags);
  
  bool have_acl = 0 < n;
  bool have_scontext = !ai.scontext_err;
  bool cannot_access_acl = n < 0 && (errno == EACCES || errno == ENOENT);

  f->acl_type = (!have_scontext && !have_acl
                 ? (cannot_access_acl ? ACL_T_UNKNOWN : ACL_T_NONE)
                 : (have_scontext && !have_acl
                    ? ACL_T_LSM_CONTEXT_ONLY
                    : ACL_T_YES));
  any_has_acl |= f->acl_type != ACL_T_NONE;

  if (format == long_format && n < 0 && !cannot_access_acl)
    error (0, errno, "%s", quotef (full_name));
  else if (print_scontext && ai.scontext_err
           && (! (is_ENOTSUP (ai.scontext_err) || ai.scontext_err == ENODATA)))
    error (0, ai.scontext_err, "%s", quotef (full_name));

  if (check_capability && aclinfo_has_xattr (&ai, XATTR_NAME_CAPS))
    f->has_capability = has_capability_cache (full_name, f);

  f->scontext = ai.scontext;
  ai.scontext = nullptr;
  aclinfo_free (&ai);
}

static void process_symlink_info(char const *full_name, struct fileinfo *f,
                                 enum filetype type, bool command_line_arg)
{
  if ((type != symbolic_link) 
      || !((format == long_format) | check_symlink_mode))
    return;

  get_link_name (full_name, f, command_line_arg);

  if (f->linkname && f->quoted == 0 && needs_quoting (f->linkname))
    f->quoted = -1;

  if (f->linkname 
      && (file_type <= indicator_style || check_symlink_mode))
    {
      struct stat linkstats;
      if (stat_for_mode (full_name, &linkstats) == 0)
        {
          f->linkok = true;
          f->linkmode = linkstats.st_mode;
        }
    }
}

static uintmax_t update_width_metrics(struct fileinfo *f, enum filetype type)
{
  uintmax_t blocks = STP_NBLOCKS (&f->stat);
  
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
      update_user_group_widths(f);
      update_nlink_width(f);
      update_size_width(f, type);
    }

  if (print_scontext)
    {
      int len = strlen (f->scontext);
      if (scontext_width < len)
        scontext_width = len;
    }

  if (print_inode)
    {
      char buf[INT_BUFSIZE_BOUND (uintmax_t)];
      int len = strlen (umaxtostr (f->stat.st_ino, buf));
      if (inode_number_width < len)
        inode_number_width = len;
    }
    
  return blocks;
}

static void update_user_group_widths(struct fileinfo *f)
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

static void update_nlink_width(struct fileinfo *f)
{
  char b[INT_BUFSIZE_BOUND (uintmax_t)];
  int b_len = strlen (umaxtostr (f->stat.st_nlink, b));
  if (nlink_width < b_len)
    nlink_width = b_len;
}

static void update_size_width(struct fileinfo *f, enum filetype type)
{
  if ((type == chardev) | (type == blockdev))
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

/* Return true if F refers to a directory.  */
static bool is_directory(const struct fileinfo *f)
{
  if (f == NULL) {
    return false;
  }
  return f->filetype == directory || f->filetype == arg_directory;
}

/* Return true if F refers to a (symlinked) directory.  */
static bool is_linked_directory(const struct fileinfo *f)
{
    if (f == NULL) {
        return false;
    }
    
    return f->filetype == directory || 
           f->filetype == arg_directory || 
           S_ISDIR(f->linkmode);
}

/* Put the name of the file that FILENAME is a symbolic link to
   into the LINKNAME field of 'f'.  COMMAND_LINE_ARG indicates whether
   FILENAME is a command-line argument.  */

static void
get_link_name (char const *filename, struct fileinfo *f, bool command_line_arg)
{
  if (filename == NULL || f == NULL)
    return;
    
  f->linkname = areadlink_with_size (filename, f->stat.st_size);
  if (f->linkname == NULL)
    file_failure (command_line_arg, _("cannot read symbolic link %s"),
                  filename);
}

/* Return true if the last component of NAME is '.' or '..'
   This is so we don't try to recurse on '././././. ...' */

static bool basename_is_dot_or_dotdot(char const *name)
{
  if (!name) {
    return false;
  }
  
  char const *base = last_component(name);
  if (!base) {
    return false;
  }
  
  return dot_or_dotdot(base);
}

/* Remove any entries from CWD_FILE that are for directories,
   and queue them to be listed as directories instead.
   DIRNAME is the prefix to prepend to each dirname
   to make it correct relative to ls's working dir;
   if it is null, no prefix is needed and "." and ".." should not be ignored.
   If COMMAND_LINE_ARG is true, this directory was mentioned at the top level,
   This is desirable when processing directories recursively.  */

static void
extract_dirs_from_files (char const *dirname, bool command_line_arg)
{
  bool ignore_dot_and_dot_dot = (dirname != NULL);

  if (dirname && LOOP_DETECT)
    {
      queue_directory (NULL, dirname, false);
    }

  for (idx_t i = cwd_n_used; i > 0; i--)
    {
      struct fileinfo *f = sorted_file[i - 1];
      
      if (!is_directory (f))
        continue;
        
      if (ignore_dot_and_dot_dot && basename_is_dot_or_dotdot (f->name))
        continue;

      if (!dirname || f->name[0] == '/')
        {
          queue_directory (f->name, f->linkname, command_line_arg);
        }
      else
        {
          char *name = file_name_concat (dirname, f->name, NULL);
          if (name)
            {
              queue_directory (name, f->linkname, command_line_arg);
              free (name);
            }
        }
      
      if (f->filetype == arg_directory)
        {
          free_ent (f);
        }
    }

  idx_t j = 0;
  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
      if (f->filetype != arg_directory)
        {
          sorted_file[j] = f;
          j++;
        }
    }
  cwd_n_used = j;
}

/* Use strcoll to compare strings in this locale.  If an error occurs,
   report an error and longjmp to failed_strcoll.  */

static jmp_buf failed_strcoll;

static int
xstrcoll (char const *a, char const *b)
{
  if (a == NULL || b == NULL)
    {
      error (0, EINVAL, _("cannot compare file names %s and %s"),
             quote_n (0, a ? a : "(null)"), quote_n (1, b ? b : "(null)"));
      set_exit_status (false);
      longjmp (failed_strcoll, 1);
    }

  errno = 0;
  int diff = strcoll (a, b);
  
  if (errno != 0)
    {
      int saved_errno = errno;
      error (0, saved_errno, _("cannot compare file names %s and %s"),
             quote_n (0, a), quote_n (1, b));
      set_exit_status (false);
      longjmp (failed_strcoll, 1);
    }
  
  return diff;
}

/* Comparison routines for sorting the files.  */

typedef void const *V;
typedef int (*qsortFunc)(V a, V b);

/* Used below in DEFINE_SORT_FUNCTIONS for _df_ sort function variants.  */
static int dirfirst_check(struct fileinfo const *a, struct fileinfo const *b, int (*cmp)(V, V))
{
    int a_is_dir = is_linked_directory(a);
    int b_is_dir = is_linked_directory(b);
    
    if (b_is_dir != a_is_dir) {
        return b_is_dir - a_is_dir;
    }
    
    return cmp(a, b);
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
  if (a == NULL || b == NULL || cmp == NULL)
    return 0;
    
  int diff = timespec_cmp (get_stat_ctime (&b->stat),
                           get_stat_ctime (&a->stat));
  if (diff != 0)
    return diff;
    
  return cmp (a->name, b->name);
}

static int
cmp_mtime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == NULL || b == NULL || cmp == NULL)
    return 0;
    
  int diff = timespec_cmp (get_stat_mtime (&b->stat),
                           get_stat_mtime (&a->stat));
  if (diff != 0)
    return diff;
    
  return cmp (a->name, b->name);
}

static int
cmp_atime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == NULL || b == NULL || cmp == NULL) {
    return 0;
  }
  
  int diff = timespec_cmp (get_stat_atime (&b->stat),
                           get_stat_atime (&a->stat));
  if (diff != 0) {
    return diff;
  }
  
  return cmp (a->name, b->name);
}

static int
cmp_btime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == NULL || b == NULL || cmp == NULL) {
    return 0;
  }
  
  int diff = timespec_cmp (get_stat_btime (&b->stat),
                           get_stat_btime (&a->stat));
  if (diff != 0) {
    return diff;
  }
  
  return cmp (a->name, b->name);
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
  int diff = off_cmp (b->stat.st_size, a->stat.st_size);
  if (diff != 0)
    return diff;
  return cmp (a->name, b->name);
}

static int cmp_name(struct fileinfo const *a, struct fileinfo const *b,
                    int (*cmp)(char const *, char const *))
{
    if (a == NULL || b == NULL || cmp == NULL) {
        return 0;
    }
    
    if (a->name == NULL || b->name == NULL) {
        if (a->name == NULL && b->name == NULL) {
            return 0;
        }
        return (a->name == NULL) ? -1 : 1;
    }
    
    return cmp(a->name, b->name);
}

/* Compare file extensions.  Files with no extension are 'smallest'.
   If extensions are the same, compare by file names instead.  */

static int
cmp_extension (struct fileinfo const *a, struct fileinfo const *b,
               int (*cmp) (char const *, char const *))
{
  char const *base1 = strrchr (a->name, '.');
  char const *base2 = strrchr (b->name, '.');
  
  if (base1 == NULL) {
    base1 = "";
  }
  
  if (base2 == NULL) {
    base2 = "";
  }
  
  int diff = cmp (base1, base2);
  
  if (diff != 0) {
    return diff;
  }
  
  return cmp (a->name, b->name);
}

/* Return the (cached) screen width,
   for the NAME associated with the passed fileinfo F.  */

static size_t
fileinfo_name_width (struct fileinfo const *f)
{
  if (f->width != 0)
  {
    return f->width;
  }
  return quote_name_width (f->name, filename_quoting_options, f->quoted);
}

static int
cmp_width (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  int diff = fileinfo_name_width (a) - fileinfo_name_width (b);
  if (diff != 0)
    return diff;
  return cmp (a->name, b->name);
}

#define DEFINE_SORT_FUNCTIONS(suffix, cmp_func) \
static int sort_##suffix(const void *a, const void *b) { \
    if (a == NULL || b == NULL) { \
        return 0; \
    } \
    return cmp_func(a, b); \
} \
\
static void qsort_##suffix(void *base, size_t nmemb, size_t size) { \
    if (base == NULL || nmemb == 0 || size == 0) { \
        return; \
    } \
    qsort(base, nmemb, size, sort_##suffix); \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(suffix, cmp_func) \
    void sort_##suffix(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb == 0 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, cmp_func); \
    } \
    \
    int is_sorted_##suffix(const void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb <= 1 || size == 0) { \
            return 1; \
        } \
        const unsigned char *arr = (const unsigned char *)base; \
        for (size_t i = 1; i < nmemb; i++) { \
            if (cmp_func(arr + (i - 1) * size, arr + i * size) > 0) { \
                return 0; \
            } \
        } \
        return 1; \
    }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)static int cmp_ctime(struct fileinfo const *a, struct fileinfo const *b)
{
    int diff = timespec_cmp(get_stat_ctime(&a->stat), get_stat_ctime(&b->stat));
    return (diff != 0) ? diff : strcmp(a->name, b->name);
}

static int compare_ctime(const void *a, const void *b)
{
    return cmp_ctime(*(struct fileinfo const *const *)a, *(struct fileinfo const *const *)b);
}

static int rev_cmp_ctime(struct fileinfo const *a, struct fileinfo const *b)
{
    return cmp_ctime(b, a);
}

static int rev_compare_ctime(const void *a, const void *b)
{
    return rev_cmp_ctime(*(struct fileinfo const *const *)a, *(struct fileinfo const *const *)b);
}#define DEFINE_SORT_FUNCTIONS(field, comparator) \
    static int sort_##field##_ascending(const void *a, const void *b) { \
        return comparator(a, b); \
    } \
    static int sort_##field##_descending(const void *a, const void *b) { \
        return comparator(b, a); \
    }

static int cmp_ctime(const void *a, const void *b) {
    const struct file_entry *entry_a = (const struct file_entry *)a;
    const struct file_entry *entry_b = (const struct file_entry *)b;
    
    if (entry_a->ctime < entry_b->ctime) {
        return -1;
    }
    if (entry_a->ctime > entry_b->ctime) {
        return 1;
    }
    return 0;
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb == 0 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, compare_func); \
    }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)static int cmp_ctime(const void *a, const void *b) {
    const struct file_info *file_a = (const struct file_info *)a;
    const struct file_info *file_b = (const struct file_info *)b;
    
    if (file_a->ctime < file_b->ctime) {
        return -1;
    }
    if (file_a->ctime > file_b->ctime) {
        return 1;
    }
    return 0;
}

static void sort_by_ctime(struct file_info *files, size_t count) {
    if (files == NULL || count <= 1) {
        return;
    }
    qsort(files, count, sizeof(struct file_info), cmp_ctime);
}#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb == 0 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)static int cmp_ctime(const struct fileinfo *a, const struct fileinfo *b)
{
    if (a->stat.st_ctime > b->stat.st_ctime)
        return 1;
    if (a->stat.st_ctime < b->stat.st_ctime)
        return -1;
    return 0;
}

static int cmp_ctime_reverse(const struct fileinfo *a, const struct fileinfo *b)
{
    return -cmp_ctime(a, b);
}

static void sort_ctime(struct fileinfo *files, size_t count)
{
    if (files == NULL || count <= 1)
        return;
    qsort(files, count, sizeof(struct fileinfo), 
          (int (*)(const void *, const void *))cmp_ctime);
}

static void sort_ctime_reverse(struct fileinfo *files, size_t count)
{
    if (files == NULL || count <= 1)
        return;
    qsort(files, count, sizeof(struct fileinfo),
          (int (*)(const void *, const void *))cmp_ctime_reverse);
}
DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)void sort_mtime(void **files, size_t n) {
    qsort(files, n, sizeof(void *), cmp_mtime);
}

int cmp_mtime(const void *a, const void *b) {
    const struct file_info *file_a = *(const struct file_info **)a;
    const struct file_info *file_b = *(const struct file_info **)b;
    
    if (file_a->mtime < file_b->mtime) {
        return -1;
    }
    if (file_a->mtime > file_b->mtime) {
        return 1;
    }
    return 0;
}DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static struct fileinfo *sort_reverse_##name(struct fileinfo *list, int n) \
{ \
    if (n <= 1) return list; \
    \
    struct fileinfo **array = calloc(n, sizeof(struct fileinfo *)); \
    if (!array) return list; \
    \
    struct fileinfo *p = list; \
    for (int i = 0; i < n && p; i++) { \
        array[i] = p; \
        p = p->next; \
    } \
    \
    for (int i = 0; i < n - 1; i++) { \
        for (int j = i + 1; j < n; j++) { \
            if (cmp_func(array[j], array[i]) < 0) { \
                struct fileinfo *temp = array[i]; \
                array[i] = array[j]; \
                array[j] = temp; \
            } \
        } \
    } \
    \
    for (int i = 0; i < n - 1; i++) { \
        array[i]->next = array[i + 1]; \
    } \
    array[n - 1]->next = NULL; \
    \
    struct fileinfo *sorted = array[0]; \
    free(array); \
    return sorted; \
} \
\
static struct fileinfo *sort_##name(struct fileinfo *list, int n) \
{ \
    if (n <= 1) return list; \
    \
    struct fileinfo **array = calloc(n, sizeof(struct fileinfo *)); \
    if (!array) return list; \
    \
    struct fileinfo *p = list; \
    for (int i = 0; i < n && p; i++) { \
        array[i] = p; \
        p = p->next; \
    } \
    \
    for (int i = 0; i < n - 1; i++) { \
        for (int j = i + 1; j < n; j++) { \
            if (cmp_func(array[i], array[j]) > 0) { \
                struct fileinfo *temp = array[i]; \
                array[i] = array[j]; \
                array[j] = temp; \
            } \
        } \
    } \
    \
    for (int i = 0; i < n - 1; i++) { \
        array[i]->next = array[i + 1]; \
    } \
    array[n - 1]->next = NULL; \
    \
    struct fileinfo *sorted = array[0]; \
    free(array); \
    return sorted; \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, comparison_func) \
    static int sort_##name##_ascending(const void *a, const void *b) { \
        return comparison_func(a, b); \
    } \
    static int sort_##name##_descending(const void *a, const void *b) { \
        return comparison_func(b, a); \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static int sort_##name##_ascending(const void *a, const void *b) { \
    return cmp_func(a, b); \
} \
\
static int sort_##name##_descending(const void *a, const void *b) { \
    return cmp_func(b, a); \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)
#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb == 0 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, compare_func); \
    }

static int cmp_atime(const void *a, const void *b) {
    if (a == NULL || b == NULL) {
        return 0;
    }
    const struct stat *stat_a = (const struct stat *)a;
    const struct stat *stat_b = (const struct stat *)b;
    
    if (stat_a->st_atime < stat_b->st_atime) {
        return -1;
    }
    if (stat_a->st_atime > stat_b->st_atime) {
        return 1;
    }
    return 0;
}

void sort_atime(void *base, size_t nmemb, size_t size) {
    if (base == NULL || nmemb == 0 || size == 0) {
        return;
    }
    qsort(base, nmemb, size, cmp_atime);
}DEFINE_SORT_FUNCTIONS(atime, cmp_atime)static int cmp_atime(const void *a, const void *b)
{
    return compare_times(((const struct file_entry *)a)->atime,
                         ((const struct file_entry *)b)->atime);
}

static void sort_by_atime(struct file_entry *entries, size_t count)
{
    if (entries == NULL || count == 0) {
        return;
    }
    qsort(entries, count, sizeof(struct file_entry), cmp_atime);
}

static void sort_by_atime_reverse(struct file_entry *entries, size_t count)
{
    if (entries == NULL || count == 0) {
        return;
    }
    sort_by_atime(entries, count);
    reverse_array(entries, count, sizeof(struct file_entry));
}#define DEFINE_SORT_FUNCTIONS(name, comparison_func) \
    void sort_##name(void *array, size_t count, size_t size) { \
        if (array == NULL || count <= 1 || size == 0) { \
            return; \
        } \
        qsort(array, count, size, comparison_func); \
    }

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)DEFINE_SORT_FUNCTIONS(atime, cmp_atime)static inline int cmp_atime(const FTSENT **a, const FTSENT **b)
{
    return cmp_atime(a, b);
}

static int sort_atime(const FTSENT **a, const FTSENT **b)
{
    return cmp_atime(a, b);
}

static int revsort_atime(const FTSENT **a, const FTSENT **b)
{
    return -cmp_atime(a, b);
}#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb == 0 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)DEFINE_SORT_FUNCTIONS(atime, cmp_atime)
int cmp_btime(const void *a, const void *b) {
    const struct btime *btime_a = (const struct btime *)a;
    const struct btime *btime_b = (const struct btime *)b;
    
    if (btime_a == NULL || btime_b == NULL) {
        return 0;
    }
    
    if (btime_a->value < btime_b->value) {
        return -1;
    }
    if (btime_a->value > btime_b->value) {
        return 1;
    }
    return 0;
}

void sort_btime(struct btime *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(struct btime), cmp_btime);
}static int cmp_btime(const void *a, const void *b) {
    return ((struct entry *)a)->btime - ((struct entry *)b)->btime;
}

static void sort_btime(struct entry *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(struct entry), cmp_btime);
}#ifndef DEFINE_SORT_FUNCTIONS_HELPER
#define DEFINE_SORT_FUNCTIONS_HELPER(name, compare_func) \
    static int compare_##name(const void *a, const void *b) { \
        if (a == NULL || b == NULL) { \
            return 0; \
        } \
        return compare_func(a, b); \
    } \
    \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (base != NULL && nmemb > 0 && size > 0) { \
            qsort(base, nmemb, size, compare_##name); \
        } \
    }
#endif

#ifndef DEFINE_SORT_FUNCTIONS
#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    DEFINE_SORT_FUNCTIONS_HELPER(name, compare_func)
#endif

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)static int cmp_btime(const void *p1, const void *p2);

static void sort_btime(void *base, size_t nmemb, size_t size) {
    qsort(base, nmemb, size, cmp_btime);
}

static void stable_sort_btime(void *base, size_t nmemb, size_t size) {
    qsort(base, nmemb, size, cmp_btime);
}

static void *bsearch_btime(const void *key, const void *base, size_t nmemb, size_t size) {
    return bsearch(key, base, nmemb, size, cmp_btime);
}static int cmp_btime(const void *a, const void *b) {
    return 0;
}

static void sort_btime(void *base, size_t nmemb, size_t size) {
    qsort(base, nmemb, size, cmp_btime);
}static int cmp_btime(const void *a, const void *b) {
    return ((struct btime *)a)->value - ((struct btime *)b)->value;
}

static void sort_btime(struct btime *arr, size_t n) {
    if (arr == NULL || n == 0) {
        return;
    }
    qsort(arr, n, sizeof(struct btime), cmp_btime);
}static int cmp_btime(const void *a, const void *b)
{
    if (a == NULL || b == NULL) {
        return 0;
    }
    
    const typeof(((struct btime *)0)->value) *val_a = &((const struct btime *)a)->value;
    const typeof(((struct btime *)0)->value) *val_b = &((const struct btime *)b)->value;
    
    if (*val_a < *val_b) {
        return -1;
    }
    if (*val_a > *val_b) {
        return 1;
    }
    return 0;
}

static void sort_btime(struct btime *array, size_t count)
{
    if (array != NULL && count > 1) {
        qsort(array, count, sizeof(struct btime), cmp_btime);
    }
}

static struct btime *sorted_copy_btime(const struct btime *array, size_t count)
{
    if (array == NULL || count == 0) {
        return NULL;
    }
    
    struct btime *copy = malloc(count * sizeof(struct btime));
    if (copy == NULL) {
        return NULL;
    }
    
    memcpy(copy, array, count * sizeof(struct btime));
    sort_btime(copy, count);
    return copy;
}void sort_btime(void *base, size_t nmemb, size_t size) {
    qsort(base, nmemb, size, cmp_btime);
}

void stable_sort_btime(void *base, size_t nmemb, size_t size) {
    qsort_r(base, nmemb, size, cmp_btime, NULL);
}
static int cmp_size(const void *a, const void *b) {
    const size_t *size_a = (const size_t *)a;
    const size_t *size_b = (const size_t *)b;
    
    if (*size_a < *size_b) {
        return -1;
    }
    if (*size_a > *size_b) {
        return 1;
    }
    return 0;
}

static void sort_size(void *base, size_t nmemb, size_t size) {
    if (base == NULL || nmemb == 0 || size == 0) {
        return;
    }
    qsort(base, nmemb, size, cmp_size);
}static int cmp_size(const void *p1, const void *p2)
{
    const struct entry *e1 = p1;
    const struct entry *e2 = p2;
    
    if (e1->size < e2->size)
        return -1;
    if (e1->size > e2->size)
        return 1;
    return 0;
}

static void sort_size(struct entry *entries, size_t count)
{
    if (entries == NULL || count == 0)
        return;
    
    qsort(entries, count, sizeof(struct entry), cmp_size);
}void size_sort(struct file *files, int count) {
    if (!files || count <= 0) {
        return;
    }
    
    for (int i = 0; i < count - 1; i++) {
        for (int j = 0; j < count - i - 1; j++) {
            if (cmp_size(&files[j], &files[j + 1]) > 0) {
                struct file temp = files[j];
                files[j] = files[j + 1];
                files[j + 1] = temp;
            }
        }
    }
}

void size_rev_sort(struct file *files, int count) {
    if (!files || count <= 0) {
        return;
    }
    
    for (int i = 0; i < count - 1; i++) {
        for (int j = 0; j < count - i - 1; j++) {
            if (cmp_size(&files[j], &files[j + 1]) < 0) {
                struct file temp = files[j];
                files[j] = files[j + 1];
                files[j + 1] = temp;
            }
        }
    }
}static int cmp_size(const void *a, const void *b) {
    if (*(size_t *)a < *(size_t *)b) return -1;
    if (*(size_t *)a > *(size_t *)b) return 1;
    return 0;
}

static void sort_size(void *base, size_t nmemb, size_t size) {
    qsort(base, nmemb, size, cmp_size);
}void sort_size(void **base, size_t nmemb) {
    if (base == NULL || nmemb <= 1) {
        return;
    }
    
    for (size_t i = 1; i < nmemb; i++) {
        void *key = base[i];
        size_t j = i;
        
        while (j > 0 && cmp_size(base[j - 1], key) > 0) {
            base[j] = base[j - 1];
            j--;
        }
        
        base[j] = key;
    }
}

void sort_size_r(void **base, size_t nmemb) {
    if (base == NULL || nmemb <= 1) {
        return;
    }
    
    for (size_t i = 1; i < nmemb; i++) {
        void *key = base[i];
        size_t j = i;
        
        while (j > 0 && cmp_size(base[j - 1], key) < 0) {
            base[j] = base[j - 1];
            j--;
        }
        
        base[j] = key;
    }
}#define DEFINE_SORT_FUNCTIONS(suffix, compare_func) \
static void sort_##suffix(void *base, size_t n, size_t size) \
{ \
    if (base == NULL || n <= 1 || size == 0) { \
        return; \
    } \
    char *arr = (char *)base; \
    for (size_t i = 0; i < n - 1; i++) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < n; j++) { \
            if (compare_func(arr + j * size, arr + min_idx * size) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            swap_elements(arr + i * size, arr + min_idx * size, size); \
        } \
    } \
} \
\
static void swap_elements(void *a, void *b, size_t size) \
{ \
    if (a == NULL || b == NULL || a == b || size == 0) { \
        return; \
    } \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    for (size_t i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#include <stddef.h>
#include <stdbool.h>

static inline int cmp_size(const void *a, const void *b) {
    size_t val_a = *(const size_t *)a;
    size_t val_b = *(const size_t *)b;
    
    if (val_a < val_b) {
        return -1;
    }
    if (val_a > val_b) {
        return 1;
    }
    return 0;
}

static void swap_size(size_t *a, size_t *b) {
    size_t temp = *a;
    *a = *b;
    *b = temp;
}

static size_t partition_size(size_t *arr, size_t low, size_t high) {
    size_t pivot = arr[high];
    size_t i = low;
    
    for (size_t j = low; j < high; j++) {
        if (arr[j] <= pivot) {
            if (i != j) {
                swap_size(&arr[i], &arr[j]);
            }
            i++;
        }
    }
    
    swap_size(&arr[i], &arr[high]);
    return i;
}

static void quicksort_size(size_t *arr, size_t low, size_t high) {
    if (low >= high || low == SIZE_MAX) {
        return;
    }
    
    size_t pi = partition_size(arr, low, high);
    
    if (pi > 0) {
        quicksort_size(arr, low, pi - 1);
    }
    quicksort_size(arr, pi + 1, high);
}

void sort_size(size_t *arr, size_t n) {
    if (arr == NULL || n <= 1) {
        return;
    }
    
    quicksort_size(arr, 0, n - 1);
}static int cmp_size(const void *a, const void *b) {
    const size_t *size_a = (const size_t *)a;
    const size_t *size_b = (const size_t *)b;
    
    if (*size_a < *size_b) {
        return -1;
    }
    if (*size_a > *size_b) {
        return 1;
    }
    return 0;
}

static void sort_by_size(void *array, size_t count, size_t element_size) {
    if (array == NULL || count == 0 || element_size == 0) {
        return;
    }
    qsort(array, count, element_size, cmp_size);
}
#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void sort_##name##_swap(void *a, void *b, size_t size) \
{ \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    size_t i; \
    for (i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void sort_##name##_quicksort(void *base, size_t num, size_t size, \
                                    int (*cmp)(const void *, const void *)) \
{ \
    if (num <= 1) { \
        return; \
    } \
    \
    unsigned char *arr = (unsigned char *)base; \
    size_t pivot_idx = num / 2; \
    unsigned char *pivot = arr + (pivot_idx * size); \
    size_t i = 0; \
    size_t j = num - 1; \
    \
    while (i <= j) { \
        while (i < num && cmp(arr + (i * size), pivot) < 0) { \
            i++; \
        } \
        while (j > 0 && cmp(arr + (j * size), pivot) > 0) { \
            j--; \
        } \
        if (i <= j) { \
            if (i != j) { \
                sort_##name##_swap(arr + (i * size), arr + (j * size), size); \
                if (i == pivot_idx) { \
                    pivot_idx = j; \
                    pivot = arr + (pivot_idx * size); \
                } else if (j == pivot_idx) { \
                    pivot_idx = i; \
                    pivot = arr + (pivot_idx * size); \
                } \
            } \
            i++; \
            if (j > 0) { \
                j--; \
            } \
        } \
    } \
    \
    if (j > 0) { \
        sort_##name##_quicksort(arr, j + 1, size, cmp); \
    } \
    if (i < num) { \
        sort_##name##_quicksort(arr + (i * size), num - i, size, cmp); \
    } \
} \
\
void sort_##name(void *base, size_t num, size_t size) \
{ \
    if (base == NULL || num == 0 || size == 0) { \
        return; \
    } \
    sort_##name##_quicksort(base, num, size, cmp_name); \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static int name##_cmp(const void *a, const void *b) \
{ \
    if (a == NULL || b == NULL) { \
        return 0; \
    } \
    return cmp_name(*(const typeof(name) *)a, *(const typeof(name) *)b); \
} \
\
static void name##_sort(typeof(name) *array, size_t count) \
{ \
    if (array == NULL || count == 0) { \
        return; \
    } \
    qsort(array, count, sizeof(typeof(name)), name##_cmp); \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void name##_swap(void *a, void *b, size_t size) { \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    for (size_t i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void name##_sort(void *base, size_t num, size_t size) { \
    if (base == NULL || num <= 1 || size == 0) { \
        return; \
    } \
    unsigned char *arr = (unsigned char *)base; \
    for (size_t i = 0; i < num - 1; i++) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < num; j++) { \
            if (cmp_name(arr + j * size, arr + min_idx * size) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            name##_swap(arr + i * size, arr + min_idx * size, size); \
        } \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void name##_swap(void *a, void *b, size_t size) { \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    for (size_t i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void name##_sort(void *base, size_t nmemb, size_t size) { \
    if (base == NULL || nmemb <= 1 || size == 0) { \
        return; \
    } \
    unsigned char *arr = (unsigned char *)base; \
    for (size_t i = 0; i < nmemb - 1; i++) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < nmemb; j++) { \
            if (cmp_name(arr + j * size, arr + min_idx * size) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            name##_swap(arr + i * size, arr + min_idx * size, size); \
        } \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static int name##_cmp(const void *a, const void *b) \
{ \
    if (a == NULL || b == NULL) { \
        return 0; \
    } \
    return cmp_name(*(const typeof(**(name##_t **)a) **)a, \
                    *(const typeof(**(name##_t **)b) **)b); \
} \
\
static void name##_sort(name##_t **array, size_t count) \
{ \
    if (array == NULL || count == 0) { \
        return; \
    } \
    qsort(array, count, sizeof(name##_t *), name##_cmp); \
} \
\
static name##_t **name##_sorted_copy(name##_t **array, size_t count) \
{ \
    if (array == NULL || count == 0) { \
        return NULL; \
    } \
    name##_t **copy = calloc(count, sizeof(name##_t *)); \
    if (copy == NULL) { \
        return NULL; \
    } \
    for (size_t i = 0; i < count; i++) { \
        copy[i] = array[i]; \
    } \
    name##_sort(copy, count); \
    return copy; \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static int name##_cmp(const void *a, const void *b) \
{ \
    if (a == NULL || b == NULL) { \
        return 0; \
    } \
    return cmp_name(*(const typeof(((void)0, a)))a, *(const typeof(((void)0, b)))b); \
} \
\
static void name##_sort(void *array, size_t count, size_t size) \
{ \
    if (array == NULL || count == 0 || size == 0) { \
        return; \
    } \
    qsort(array, count, size, name##_cmp); \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void name##_swap(void *a, void *b, size_t size) { \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    for (size_t i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void name##_sort(void *base, size_t nmemb, size_t size) { \
    if (base == NULL || nmemb <= 1 || size == 0) { \
        return; \
    } \
    unsigned char *arr = (unsigned char *)base; \
    for (size_t i = 0; i < nmemb - 1; i++) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < nmemb; j++) { \
            if (cmp_name(&arr[j * size], &arr[min_idx * size]) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            name##_swap(&arr[i * size], &arr[min_idx * size], size); \
        } \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void name##_swap(void *a, void *b, size_t size) { \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    size_t i; \
    for (i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void name##_sort(void *base, size_t num, size_t size) { \
    if (base == NULL || num <= 1 || size == 0) { \
        return; \
    } \
    unsigned char *array = (unsigned char *)base; \
    size_t i, j; \
    for (i = 0; i < num - 1; i++) { \
        for (j = 0; j < num - i - 1; j++) { \
            void *elem1 = array + (j * size); \
            void *elem2 = array + ((j + 1) * size); \
            if (cmp_name(elem1, elem2) > 0) { \
                name##_swap(elem1, elem2, size); \
            } \
        } \
    } \
}
static inline void swap_extension(struct extension *a, struct extension *b)
{
    struct extension temp = *a;
    *a = *b;
    *b = temp;
}

void sort_extension(struct extension *array, size_t count)
{
    if (array == NULL || count <= 1) {
        return;
    }
    
    for (size_t i = 1; i < count; i++) {
        for (size_t j = i; j > 0 && cmp_extension(&array[j - 1], &array[j]) > 0; j--) {
            swap_extension(&array[j - 1], &array[j]);
        }
    }
}void sort_extension(void **array, size_t count) {
    if (array == NULL || count <= 1) {
        return;
    }
    
    for (size_t i = 1; i < count; i++) {
        void *key = array[i];
        size_t j = i;
        
        while (j > 0 && cmp_extension(array[j - 1], key) > 0) {
            array[j] = array[j - 1];
            j--;
        }
        
        array[j] = key;
    }
}

int is_sorted_extension(void **array, size_t count) {
    if (array == NULL || count <= 1) {
        return 1;
    }
    
    for (size_t i = 1; i < count; i++) {
        if (cmp_extension(array[i - 1], array[i]) > 0) {
            return 0;
        }
    }
    
    return 1;
}static inline int extension_lt(const struct extension *a, const struct extension *b)
{
    return cmp_extension(a, b) < 0;
}

static void extension_swap(struct extension *a, struct extension *b)
{
    struct extension tmp = *a;
    *a = *b;
    *b = tmp;
}

static void extension_sort(struct extension *array, size_t count)
{
    if (!array || count < 2) {
        return;
    }
    
    for (size_t i = 1; i < count; i++) {
        size_t j = i;
        while (j > 0 && extension_lt(&array[j], &array[j - 1])) {
            extension_swap(&array[j], &array[j - 1]);
            j--;
        }
    }
}static void sort_extension(void **array, size_t count) {
    if (array == NULL || count <= 1) {
        return;
    }
    
    for (size_t i = 1; i < count; i++) {
        void *key = array[i];
        size_t j = i;
        
        while (j > 0 && cmp_extension(array[j - 1], key) > 0) {
            array[j] = array[j - 1];
            j--;
        }
        
        array[j] = key;
    }
}

static int bsearch_extension(void **array, size_t count, void *key) {
    if (array == NULL || key == NULL || count == 0) {
        return -1;
    }
    
    size_t left = 0;
    size_t right = count;
    
    while (left < right) {
        size_t mid = left + (right - left) / 2;
        int cmp_result = cmp_extension(array[mid], key);
        
        if (cmp_result == 0) {
            return (int)mid;
        }
        
        if (cmp_result < 0) {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    return -1;
}static int extension_compar(const void *a, const void *b)
{
    return cmp_extension(*(const extension **)a, *(const extension **)b);
}

void sort_extension(extension **array, size_t count)
{
    if (array != NULL && count > 0) {
        qsort(array, count, sizeof(extension *), extension_compar);
    }
}#include <string.h>

static int cmp_extension(const void *a, const void *b) {
    return strcmp(*(const char **)a, *(const char **)b);
}

static void sort_extension(void **array, size_t count) {
    if (array == NULL || count <= 1) {
        return;
    }
    qsort(array, count, sizeof(void *), cmp_extension);
}

static void *bsearch_extension(const void *key, void **array, size_t count) {
    if (array == NULL || count == 0 || key == NULL) {
        return NULL;
    }
    return bsearch(&key, array, count, sizeof(void *), cmp_extension);
}void sort_extension(extension *array, size_t n) {
    if (array == NULL || n <= 1) {
        return;
    }
    
    for (size_t i = 1; i < n; i++) {
        extension key = array[i];
        size_t j = i;
        
        while (j > 0 && cmp_extension(&array[j - 1], &key) > 0) {
            array[j] = array[j - 1];
            j--;
        }
        
        array[j] = key;
    }
}

int bsearch_extension(const extension *key, const extension *array, size_t n, extension **result) {
    if (key == NULL || array == NULL || result == NULL) {
        return -1;
    }
    
    *result = NULL;
    
    if (n == 0) {
        return -1;
    }
    
    size_t left = 0;
    size_t right = n;
    
    while (left < right) {
        size_t mid = left + (right - left) / 2;
        int cmp_result = cmp_extension(key, &array[mid]);
        
        if (cmp_result < 0) {
            right = mid;
        } else if (cmp_result > 0) {
            left = mid + 1;
        } else {
            *result = (extension *)&array[mid];
            return 0;
        }
    }
    
    return -1;
}static int cmp_extension(const void *a, const void *b);

static void sort_extension(void *base, size_t num, size_t size) {
    qsort(base, num, size, cmp_extension);
}
void width_sort(void *base, size_t nmemb, size_t size) {
    if (base == NULL || nmemb <= 1 || size == 0) {
        return;
    }
    
    char *arr = (char *)base;
    char *temp = malloc(size);
    if (temp == NULL) {
        return;
    }
    
    for (size_t i = 1; i < nmemb; i++) {
        for (size_t j = i; j > 0; j--) {
            if (cmp_width(arr + (j - 1) * size, arr + j * size) <= 0) {
                break;
            }
            memcpy(temp, arr + (j - 1) * size, size);
            memcpy(arr + (j - 1) * size, arr + j * size, size);
            memcpy(arr + j * size, temp, size);
        }
    }
    
    free(temp);
}

int width_find(const void *key, const void *base, size_t nmemb, size_t size) {
    if (key == NULL || base == NULL || nmemb == 0 || size == 0) {
        return -1;
    }
    
    const char *arr = (const char *)base;
    size_t left = 0;
    size_t right = nmemb;
    
    while (left < right) {
        size_t mid = left + (right - left) / 2;
        int cmp = cmp_width(key, arr + mid * size);
        
        if (cmp == 0) {
            return (int)mid;
        } else if (cmp < 0) {
            right = mid;
        } else {
            left = mid + 1;
        }
    }
    
    return -1;
}#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || nmemb <= 1 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, compare_func); \
    }

DEFINE_SORT_FUNCTIONS(width, cmp_width)const struct comb *width_left = left;
const struct comb *width_right = right;
return width_left->width - width_right->width;#include <stdlib.h>
#include <string.h>

typedef struct width {
    int value;
} width;

static int cmp_width(const void *a, const void *b) {
    const width *wa = (const width *)a;
    const width *wb = (const width *)b;
    
    if (wa->value < wb->value) return -1;
    if (wa->value > wb->value) return 1;
    return 0;
}

static void sort_width_array(width *array, size_t count) {
    if (array != NULL && count > 0) {
        qsort(array, count, sizeof(width), cmp_width);
    }
}

static int width_binary_search(const width *array, size_t count, int target) {
    if (array == NULL || count == 0) {
        return -1;
    }
    
    size_t left = 0;
    size_t right = count - 1;
    
    while (left <= right) {
        size_t mid = left + (right - left) / 2;
        
        if (array[mid].value == target) {
            return (int)mid;
        }
        
        if (array[mid].value < target) {
            left = mid + 1;
        } else {
            if (mid == 0) break;
            right = mid - 1;
        }
    }
    
    return -1;
}

static width* width_find_min(width *array, size_t count) {
    if (array == NULL || count == 0) {
        return NULL;
    }
    
    width *min = &array[0];
    for (size_t i = 1; i < count; i++) {
        if (cmp_width(&array[i], min) < 0) {
            min = &array[i];
        }
    }
    return min;
}

static width* width_find_max(width *array, size_t count) {
    if (array == NULL || count == 0) {
        return NULL;
    }
    
    width *max = &array[0];
    for (size_t i = 1; i < count; i++) {
        if (cmp_width(&array[i], max) > 0) {
            max = &array[i];
        }
    }
    return max;
}DEFINE_SORT_FUNCTIONS(width, cmp_width)int cmp_width(const void *a, const void *b) {
    const struct width *wa = a;
    const struct width *wb = b;
    
    if (wa->value < wb->value) return -1;
    if (wa->value > wb->value) return 1;
    return 0;
}

void sort_width(struct width *array, size_t count) {
    if (array == NULL || count == 0) return;
    qsort(array, count, sizeof(struct width), cmp_width);
}typedef struct {
    int (*compare)(const void *, const void *);
} width_sort_context;

static int width_compare_wrapper(const void *a, const void *b, void *context) {
    width_sort_context *ctx = (width_sort_context *)context;
    return ctx->compare(a, b);
}

void sort_width(void *base, size_t nmemb, size_t size) {
    if (base == NULL || nmemb == 0 || size == 0) {
        return;
    }
    
    width_sort_context ctx = { .compare = cmp_width };
    qsort_r(base, nmemb, size, width_compare_wrapper, &ctx);
}

void sort_width_r(void *base, size_t nmemb, size_t size, 
                  int (*compare)(const void *, const void *, void *), void *arg) {
    if (base == NULL || nmemb == 0 || size == 0 || compare == NULL) {
        return;
    }
    
    qsort_r(base, nmemb, size, compare, arg);
}static void sort_width(void **array, size_t count) {
    if (array == NULL || count <= 1) {
        return;
    }
    
    for (size_t i = 0; i < count - 1; i++) {
        for (size_t j = 0; j < count - i - 1; j++) {
            if (cmp_width(array[j], array[j + 1]) > 0) {
                void *temp = array[j];
                array[j] = array[j + 1];
                array[j + 1] = temp;
            }
        }
    }
}

static void *find_min_width(void **array, size_t count) {
    if (array == NULL || count == 0) {
        return NULL;
    }
    
    void *min = array[0];
    for (size_t i = 1; i < count; i++) {
        if (cmp_width(array[i], min) < 0) {
            min = array[i];
        }
    }
    return min;
}

static void *find_max_width(void **array, size_t count) {
    if (array == NULL || count == 0) {
        return NULL;
    }
    
    void *max = array[0];
    for (size_t i = 1; i < count; i++) {
        if (cmp_width(array[i], max) > 0) {
            max = array[i];
        }
    }
    return max;
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
static int cmp_version(struct fileinfo const *a, struct fileinfo const *b)
{
    int diff = filevercmp(a->name, b->name);
    if (diff != 0) {
        return diff;
    }
    return strcmp(a->name, b->name);
}

static int xstrcoll_version(V a, V b)
{
    if (a == NULL || b == NULL) {
        if (a == NULL && b == NULL) {
            return 0;
        }
        return (a == NULL) ? -1 : 1;
    }
    return cmp_version(a, b);
}
static int
rev_xstrcoll_version (V a, V b)
{
  return cmp_version (b, a);
}
static int xstrcoll_df_version(V a, V b)
{
    if (a == NULL || b == NULL) {
        return 0;
    }
    return dirfirst_check(a, b, xstrcoll_version);
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

static void initialize_ordering_vector(void)
{
    if (sorted_file == NULL || cwd_file == NULL) {
        return;
    }
    
    for (idx_t i = 0; i < cwd_n_used; i++) {
        sorted_file[i] = &cwd_file[i];
    }
}

/* Cache values based on attributes global to all files.  */

static void
update_current_files_info (void)
{
  if (sort_type != sort_width && 
      (!line_length || (format != many_per_line && format != horizontal)))
    {
      return;
    }

  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
      if (f != NULL)
        {
          f->width = fileinfo_name_width (f);
        }
    }
}

/* Sort the files now in the table.  */

static void
sort_files (void)
{
  bool use_strcmp;

  if (sorted_file_alloc < cwd_n_used + (cwd_n_used >> 1))
    {
      free (sorted_file);
      sorted_file_alloc = 3 * cwd_n_used;
      sorted_file = xinmalloc (cwd_n_used, sorted_file_alloc * sizeof *sorted_file);
    }

  initialize_ordering_vector ();

  update_current_files_info ();

  if (sort_type == sort_none)
    return;

  if (! setjmp (failed_strcoll))
    {
      use_strcmp = false;
    }
  else
    {
      use_strcmp = true;
      affirm (sort_type != sort_version);
      initialize_ordering_vector ();
    }

  int sort_index = sort_type;
  if (sort_type == sort_time)
    {
      sort_index += time_type;
    }

  qsort_function comparator = sort_functions[sort_index]
                                             [use_strcmp]
                                             [sort_reverse]
                                             [directories_first];

  mpsort ((void const **) sorted_file, cwd_n_used, comparator);
}

/* List all the files now in the table.  */

static void
print_current_files (void)
{
  if (format == one_per_line)
    {
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          print_file_name_and_frills (sorted_file[i], 0);
          putchar (eolbyte);
        }
      return;
    }

  if (format == long_format)
    {
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          set_normal_color ();
          print_long_format (sorted_file[i]);
          dired_outbyte (eolbyte);
        }
      return;
    }

  if (format == with_commas)
    {
      print_with_separator (',');
      return;
    }

  if (format == many_per_line)
    {
      if (line_length == 0)
        print_with_separator (' ');
      else
        print_many_per_line ();
      return;
    }

  if (format == horizontal)
    {
      if (line_length == 0)
        print_with_separator (' ');
      else
        print_horizontal ();
    }
}

/* Replace the first %b with precomputed aligned month names.
   Note on glibc-2.7 at least, this speeds up the whole 'ls -lU'
   process by around 17%, compared to letting strftime() handle the %b.  */

static size_t
align_nstrftime (char *buf, size_t size, bool recent, struct tm const *tm,
                 timezone_t tz, int ns)
{
  if (buf == NULL || tm == NULL || size == 0) {
    return 0;
  }
  
  size_t recent_index = recent ? 1 : 0;
  char const *nfmt = NULL;
  
  if (use_abformat) {
    if (tm->tm_mon >= 0 && tm->tm_mon < 12) {
      nfmt = abformat[recent_index][tm->tm_mon];
    }
  } else {
    nfmt = long_time_format[recent_index];
  }
  
  if (nfmt == NULL) {
    return 0;
  }
  
  return nstrftime (buf, size, nfmt, tm, tz, ns);
}

/* Return the expected number of columns in a long-format timestamp,
   or zero if it cannot be calculated.  */

static int
long_time_expected_width (void)
{
  static int width = -1;

  if (width >= 0)
    return width;

  time_t epoch = 0;
  struct tm tm;
  char buf[TIME_STAMP_LEN_MAXIMUM + 1];

  if (!localtime_rz (localtz, &epoch, &tm))
    {
      width = 0;
      return width;
    }

  size_t len = align_nstrftime (buf, sizeof buf, false, &tm, localtz, 0);
  if (len == 0)
    {
      width = 0;
      return width;
    }

  width = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
  if (width < 0)
    width = 0;

  return width;
}

/* Print the user or group name NAME, with numeric id ID, using a
   print width of WIDTH columns.  */

static void
format_user_or_group (char const *name, uintmax_t id, int width)
{
  if (name)
    {
      int name_width = mbswidth (name, MBSWIDTH_FLAGS);
      int pad = 0;
      
      if (name_width >= 0 && width > name_width)
        {
          pad = width - name_width;
        }
      
      dired_outstring (name);
      
      for (int i = 0; i < pad; i++)
        {
          dired_outbyte (' ');
        }
    }
  else
    {
      dired_pos += printf ("%*ju ", width, id);
    }
}

/* Print the name or id of the user with id U, using a print width of
   WIDTH.  */

static void
format_user (uid_t u, int width, bool stat_ok)
{
  const char *user_name = NULL;
  
  if (!stat_ok) {
    user_name = "?";
  } else if (!numeric_ids) {
    user_name = getuser (u);
  }
  
  format_user_or_group (user_name, u, width);
}

/* Likewise, for groups.  */

static void
format_group (gid_t g, int width, bool stat_ok)
{
  const char *group_name = NULL;
  
  if (!stat_ok) {
    group_name = "?";
  } else if (!numeric_ids) {
    group_name = getgroup (g);
  }
  
  format_user_or_group (group_name, g, width);
}

/* Return the number of columns that format_user_or_group will print,
   or -1 if unknown.  */

static int
format_user_or_group_width (char const *name, uintmax_t id)
{
  if (name != NULL)
  {
    return mbswidth (name, MBSWIDTH_FLAGS);
  }
  
  return snprintf (NULL, 0, "%ju", id);
}

/* Return the number of columns that format_user will print,
   or -1 if unknown.  */

static int
format_user_width (uid_t u)
{
  const char *user_name = numeric_ids ? NULL : getuser (u);
  return format_user_or_group_width (user_name, u);
}

/* Likewise, for groups.  */

static int
format_group_width (gid_t g)
{
  const char *group_name = numeric_ids ? NULL : getgroup (g);
  return format_user_or_group_width (group_name, g);
}

/* Return a pointer to a formatted version of F->stat.st_ino,
   possibly using buffer, which must be at least
   INT_BUFSIZE_BOUND (uintmax_t) bytes.  */
static char *
format_inode (char buf[INT_BUFSIZE_BOUND (uintmax_t)],
              const struct fileinfo *f)
{
  if (f == NULL) {
    return (char *) "?";
  }
  
  if (!f->stat_ok) {
    return (char *) "?";
  }
  
  if (f->stat.st_ino == NOT_AN_INODE_NUMBER) {
    return (char *) "?";
  }
  
  return umaxtostr (f->stat.st_ino, buf);
}

/* Print information about F in long format.  */
static void
print_long_format (const struct fileinfo *f)
{
  char modebuf[12];
  char buf[LONGEST_HUMAN_READABLE + 1
           + LONGEST_HUMAN_READABLE + 1
           + sizeof (modebuf) - 1 + 1
           + INT_BUFSIZE_BOUND (uintmax_t)
           + LONGEST_HUMAN_READABLE + 2
           + LONGEST_HUMAN_READABLE + 1
           + TIME_STAMP_LEN_MAXIMUM + 1];
  size_t s;
  char *p;
  struct timespec when_timespec;
  struct tm when_local;
  bool btime_ok = true;

  build_mode_string(f, modebuf);
  when_timespec = get_time_for_display(f, &btime_ok);

  p = buf;
  p = append_inode_info(p, f);
  p = append_block_size_info(p, f);
  p = append_mode_and_links(p, f, modebuf);

  dired_indent();
  p = handle_ownership_info(buf, p, f);
  p = append_size_or_device_info(p, f);

  s = format_time_string(p, f, &when_timespec, &when_local, btime_ok);
  p = finalize_time_output(p, s, f, &when_timespec, btime_ok);

  dired_outbuf(buf, p - buf);
  size_t w = print_name_with_quoting(f, false, &dired_obstack, p - buf);

  print_link_or_indicator(f, p, buf, w);
}

static void build_mode_string(const struct fileinfo *f, char *modebuf)
{
  if (f->stat_ok)
    filemodestring(&f->stat, modebuf);
  else
  {
    modebuf[0] = filetype_letter[f->filetype];
    memset(modebuf + 1, '?', 10);
    modebuf[11] = '\0';
  }
  
  if (!any_has_acl)
    modebuf[10] = '\0';
  else if (f->acl_type == ACL_T_LSM_CONTEXT_ONLY)
    modebuf[10] = '.';
  else if (f->acl_type == ACL_T_YES)
    modebuf[10] = '+';
  else if (f->acl_type == ACL_T_UNKNOWN)
    modebuf[10] = '?';
}

static struct timespec get_time_for_display(const struct fileinfo *f, bool *btime_ok)
{
  struct timespec when_timespec;
  
  switch (time_type)
  {
    case time_ctime:
      when_timespec = get_stat_ctime(&f->stat);
      break;
    case time_mtime:
      when_timespec = get_stat_mtime(&f->stat);
      break;
    case time_atime:
      when_timespec = get_stat_atime(&f->stat);
      break;
    case time_btime:
      when_timespec = get_stat_btime(&f->stat);
      if (when_timespec.tv_sec == -1 && when_timespec.tv_nsec == -1)
        *btime_ok = false;
      break;
    default:
      unreachable();
  }
  
  return when_timespec;
}

static char* append_inode_info(char *p, const struct fileinfo *f)
{
  if (!print_inode)
    return p;
    
  char hbuf[INT_BUFSIZE_BOUND(uintmax_t)];
  p += sprintf(p, "%*s ", inode_number_width, format_inode(hbuf, f));
  return p;
}

static char* append_block_size_info(char *p, const struct fileinfo *f)
{
  if (!print_block_size)
    return p;
    
  char hbuf[LONGEST_HUMAN_READABLE + 1];
  char const *blocks = (!f->stat_ok
                        ? "?"
                        : human_readable(STP_NBLOCKS(&f->stat), hbuf, human_output_opts,
                                       ST_NBLOCKSIZE, output_block_size));
  int blocks_width = mbswidth(blocks, MBSWIDTH_FLAGS);
  
  for (int pad = blocks_width < 0 ? 0 : block_size_width - blocks_width;
       0 < pad; pad--)
    *p++ = ' ';
    
  while ((*p++ = *blocks++))
    continue;
  p[-1] = ' ';
  
  return p;
}

static char* append_mode_and_links(char *p, const struct fileinfo *f, const char *modebuf)
{
  char hbuf[INT_BUFSIZE_BOUND(uintmax_t)];
  p += sprintf(p, "%s %*s ", modebuf, nlink_width,
              !f->stat_ok ? "?" : umaxtostr(f->stat.st_nlink, hbuf));
  return p;
}

static char* handle_ownership_info(char *buf, char *p, const struct fileinfo *f)
{
  if (!print_owner && !print_group && !print_author && !print_scontext)
    return p;
    
  dired_outbuf(buf, p - buf);
  
  if (print_owner)
    format_user(f->stat.st_uid, owner_width, f->stat_ok);
  if (print_group)
    format_group(f->stat.st_gid, group_width, f->stat_ok);
  if (print_author)
    format_user(f->stat.st_author, author_width, f->stat_ok);
  if (print_scontext)
    format_user_or_group(f->scontext, 0, scontext_width);
    
  return buf;
}

static char* append_size_or_device_info(char *p, const struct fileinfo *f)
{
  if (f->stat_ok && (S_ISCHR(f->stat.st_mode) || S_ISBLK(f->stat.st_mode)))
  {
    char majorbuf[INT_BUFSIZE_BOUND(uintmax_t)];
    char minorbuf[INT_BUFSIZE_BOUND(uintmax_t)];
    int blanks_width = file_size_width - (major_device_number_width + 2 + minor_device_number_width);
    
    p += sprintf(p, "%*s, %*s ",
                major_device_number_width + MAX(0, blanks_width),
                umaxtostr(major(f->stat.st_rdev), majorbuf),
                minor_device_number_width,
                umaxtostr(minor(f->stat.st_rdev), minorbuf));
  }
  else
  {
    char hbuf[LONGEST_HUMAN_READABLE + 1];
    char const *size = (!f->stat_ok
                       ? "?"
                       : human_readable(unsigned_file_size(f->stat.st_size),
                                      hbuf, file_human_output_opts, 1,
                                      file_output_block_size));
    int size_width = mbswidth(size, MBSWIDTH_FLAGS);
    
    for (int pad = size_width < 0 ? 0 : file_size_width - size_width;
         0 < pad; pad--)
      *p++ = ' ';
      
    while ((*p++ = *size++))
      continue;
    p[-1] = ' ';
  }
  
  return p;
}

static size_t format_time_string(char *p, const struct fileinfo *f, 
                                 const struct timespec *when_timespec,
                                 struct tm *when_local, bool btime_ok)
{
  size_t s = 0;
  *p = '\1';
  
  if (!f->stat_ok || !btime_ok)
    return 0;
    
  if (!localtime_rz(localtz, &when_timespec->tv_sec, when_local))
    return 0;
    
  struct timespec six_months_ago;
  
  if (timespec_cmp(current_time, *when_timespec) < 0)
    gettime(&current_time);
    
  six_months_ago.tv_sec = current_time.tv_sec - 31556952 / 2;
  six_months_ago.tv_nsec = current_time.tv_nsec;
  
  bool recent = (timespec_cmp(six_months_ago, *when_timespec) < 0
                && timespec_cmp(*when_timespec, current_time) < 0);
                
  s = align_nstrftime(p, TIME_STAMP_LEN_MAXIMUM + 1, recent,
                     when_local, localtz, when_timespec->tv_nsec);
  return s;
}

static char* finalize_time_output(char *p, size_t s, const struct fileinfo *f,
                                  const struct timespec *when_timespec, bool btime_ok)
{
  if (s || !*p)
  {
    p += s;
    *p++ = ' ';
  }
  else
  {
    char hbuf[INT_BUFSIZE_BOUND(intmax_t)];
    p += sprintf(p, "%*s ", long_time_expected_width(),
                (!f->stat_ok || !btime_ok
                 ? "?"
                 : timetostr(when_timespec->tv_sec, hbuf)));
  }
  
  return p;
}

static void print_link_or_indicator(const struct fileinfo *f, const char *p,
                                   const char *buf, size_t w)
{
  if (f->filetype == symbolic_link)
  {
    if (f->linkname)
    {
      dired_outstring(" -> ");
      print_name_with_quoting(f, true, nullptr, (p - buf) + w + 4);
      if (indicator_style != none)
        print_type_indicator(true, f->linkmode, unknown);
    }
  }
  else if (indicator_style != none)
  {
    print_type_indicator(f->stat_ok, f->stat.st_mode, f->filetype);
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

static size_t
quote_name_buf (char **inbuf, size_t bufsize, char *name,
                struct quoting_options const *options,
                int needs_general_quoting, size_t *width, bool *pad)
{
  char *buf = *inbuf;
  size_t displayed_width = 0;
  size_t len = 0;
  bool quoted = false;

  enum quoting_style qs = get_quoting_style (options);
  bool needs_further_quoting = qmark_funny_chars
                               && (qs == shell_quoting_style
                                   || qs == shell_always_quoting_style
                                   || qs == literal_quoting_style);

  if (needs_general_quoting != 0)
    {
      len = quotearg_buffer (buf, bufsize, name, -1, options);
      if (bufsize <= len)
        {
          buf = xmalloc (len + 1);
          quotearg_buffer (buf, len + 1, name, -1, options);
        }
      quoted = (*name != *buf) || strlen (name) != len;
    }
  else if (needs_further_quoting)
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

  if (needs_further_quoting)
    {
      if (MB_CUR_MAX > 1)
        displayed_width = process_multibyte_chars (buf, &len);
      else
        displayed_width = process_single_byte_chars (buf, len);
    }
  else if (width != nullptr)
    {
      displayed_width = calculate_display_width (buf, len);
    }

  if (pad != nullptr)
    *pad = (align_variable_outer_quotes && cwd_some_quoted && ! quoted);

  if (width != nullptr)
    *width = displayed_width;

  *inbuf = buf;

  return len;
}

static size_t
process_multibyte_chars (char *buf, size_t *len)
{
  char const *p = buf;
  char const *plimit = buf + *len;
  char *q = buf;
  size_t displayed_width = 0;

  while (p < plimit)
    {
      if (is_printable_ascii (*p))
        {
          *q++ = *p++;
          displayed_width += 1;
        }
      else
        {
          size_t processed = process_multibyte_sequence (p, plimit, &q, &displayed_width);
          p += processed;
        }
    }

  *len = q - buf;
  return displayed_width;
}

static bool
is_printable_ascii (char c)
{
  return (c >= ' ' && c <= '~') || c == '\t';
}

static size_t
process_multibyte_sequence (char const *p, char const *plimit, char **q, size_t *displayed_width)
{
  mbstate_t mbstate;
  mbszero (&mbstate);
  size_t total_bytes = 0;

  do
    {
      char32_t wc;
      size_t bytes = mbrtoc32 (&wc, p, plimit - p, &mbstate);

      if (bytes == (size_t) -1)
        {
          **q = '?';
          (*q)++;
          (*displayed_width)++;
          return 1;
        }

      if (bytes == (size_t) -2)
        {
          **q = '?';
          (*q)++;
          (*displayed_width)++;
          return plimit - p;
        }

      if (bytes == 0)
        bytes = 1;

      int w = c32width (wc);
      if (w >= 0)
        {
          memcpy (*q, p, bytes);
          *q += bytes;
          *displayed_width += w;
        }
      else
        {
          **q = '?';
          (*q)++;
          (*displayed_width)++;
        }

      p += bytes;
      total_bytes += bytes;
    }
  while (!mbsinit (&mbstate) && p < plimit);

  return total_bytes;
}

static size_t
process_single_byte_chars (char *buf, size_t len)
{
  char *p = buf;
  char const *plimit = buf + len;
  size_t displayed_width = 0;

  while (p < plimit)
    {
      if (isprint (to_uchar (*p)))
        displayed_width++;
      else
        *p = '?';
      p++;
    }

  return displayed_width;
}

static size_t
calculate_display_width (char const *buf, size_t len)
{
  size_t displayed_width = 0;

  if (MB_CUR_MAX > 1)
    {
      displayed_width = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
      if (displayed_width == (size_t) -1)
        displayed_width = 0;
    }
  else
    {
      char const *p = buf;
      char const *plimit = buf + len;

      while (p < plimit)
        {
          if (isprint (to_uchar (*p)))
            displayed_width++;
          p++;
        }
    }

  return displayed_width;
}

static size_t
quote_name_width (char const *name, struct quoting_options const *options,
                  int needs_general_quoting)
{
  char smallbuf[BUFSIZ];
  char *buf = smallbuf;
  size_t width = 0;
  bool pad = false;

  if (name == NULL) {
    return 0;
  }

  quote_name_buf (&buf, sizeof smallbuf, (char *) name, options,
                  needs_general_quoting, &width, &pad);

  if (buf != smallbuf && buf != name) {
    free (buf);
  }

  if (pad) {
    width++;
  }

  return width;
}

/* %XX escape any input out of range as defined in RFC3986,
   and also if PATH, convert all path separators to '/'.  */
static char *file_escape(char const *str, bool path)
{
    if (!str) {
        return NULL;
    }

    size_t len = strlen(str);
    size_t max_size = (len * 3) + 1;
    char *esc = xnmalloc(max_size, 1);
    if (!esc) {
        return NULL;
    }

    char *p = esc;
    char *end = esc + max_size - 4;

    for (size_t i = 0; i < len && p < end; i++) {
        unsigned char ch = to_uchar(str[i]);
        
        if (path && ISSLASH(str[i])) {
            *p++ = '/';
        } else if (RFC3986[ch]) {
            *p++ = str[i];
        } else {
            *p++ = '%';
            *p++ = "0123456789abcdef"[ch >> 4];
            *p++ = "0123456789abcdef"[ch & 0x0F];
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
  bool pad = false;
  bool skip_quotes = false;

  if (!name)
    return 0;

  len = quote_name_buf (&buf, sizeof smallbuf, (char *) name, options,
                        needs_general_quoting, nullptr, &pad);

  if (pad && allow_pad)
    dired_outbyte (' ');

  if (color)
    print_color_indicator (color);

  if (absolute_name)
    {
      if (align_variable_outer_quotes && cwd_some_quoted && !pad)
        {
          skip_quotes = true;
          putchar (*buf);
        }
      
      char *h = file_escape (hostname, false);
      char *n = file_escape (absolute_name, true);
      
      if (h && n)
        {
          printf ("\033]8;;file://%s%s%s\a", h, *n == '/' ? "" : "/", n);
        }
      
      free (h);
      free (n);
    }

  if (stack)
    push_current_dired_pos (stack);

  size_t write_offset = skip_quotes ? 1 : 0;
  size_t write_len = len - (skip_quotes ? 2 : 0);
  
  if (write_len > 0 && write_len <= len)
    {
      fwrite (buf + write_offset, 1, write_len, stdout);
      dired_pos += len;
    }

  if (stack)
    push_current_dired_pos (stack);

  if (absolute_name)
    {
      fputs ("\033]8;;\a", stdout);
      if (skip_quotes && len > 0)
        putchar (buf[len - 1]);
    }

  if (buf != smallbuf && buf != name)
    free (buf);

  return len + (pad ? 1 : 0);
}

static size_t
print_name_with_quoting (const struct fileinfo *f,
                         bool symlink_target,
                         struct obstack *stack,
                         size_t start_col)
{
  if (!f || !stack)
    return 0;

  char const *name = symlink_target ? f->linkname : f->name;
  if (!name)
    return 0;

  const struct bin_str *color = NULL;
  bool used_color_this_time = false;

  if (print_with_color)
    {
      color = get_color_indicator (f, symlink_target);
      used_color_this_time = (color || is_colored (C_NORM));
    }

  size_t len = quote_name (name, filename_quoting_options, f->quoted,
                           color, !symlink_target, stack, f->absolute_name);

  process_signals ();

  if (!used_color_this_time || !line_length)
    return len;

  prep_non_filename_text ();

  size_t start_line = start_col / line_length;
  size_t end_line = (start_col + len - 1) / line_length;

  if (start_line != end_line)
    put_indicator (&color_indicator[C_CLR_TO_EOL]);

  return len;
}

static void
prep_non_filename_text (void)
{
  if (color_indicator[C_END].string != NULL)
    {
      put_indicator (&color_indicator[C_END]);
      return;
    }
  
  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (&color_indicator[C_RESET]);
  put_indicator (&color_indicator[C_RIGHT]);
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
    {
      int width = (format == with_commas) ? 0 : inode_number_width;
      printf ("%*s ", width, format_inode (buf, f));
    }

  if (print_block_size)
    {
      char const *blocks = "?";
      
      if (f->stat_ok)
        {
          blocks = human_readable (STP_NBLOCKS (&f->stat), buf, human_output_opts,
                                   ST_NBLOCKSIZE, output_block_size);
        }
      
      int pad = 0;
      if (format != with_commas && block_size_width)
        {
          int blocks_width = mbswidth (blocks, MBSWIDTH_FLAGS);
          if (blocks_width >= 0)
            {
              pad = block_size_width - blocks_width;
            }
        }
      
      printf ("%*s%s ", pad, "", blocks);
    }

  if (print_scontext)
    {
      int width = (format == with_commas) ? 0 : scontext_width;
      printf ("%*s ", width, f->scontext);
    }

  size_t width = print_name_with_quoting (f, false, nullptr, start_col);

  if (indicator_style != none)
    {
      width += print_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
    }

  return width;
}

/* Given these arguments describing a file, return the single-byte
   type indicator, or 0.  */
static char
get_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  if (stat_ok) {
    if (S_ISREG (mode)) {
      if (indicator_style == classify && (mode & S_IXUGO))
        return '*';
      return 0;
    }
    if (S_ISDIR (mode))
      return '/';
    if (indicator_style == slash)
      return 0;
    if (S_ISLNK (mode))
      return '@';
    if (S_ISFIFO (mode))
      return '|';
    if (S_ISSOCK (mode))
      return '=';
    if (S_ISDOOR (mode))
      return '>';
    return 0;
  }
  
  if (type == normal)
    return 0;
  if (type == directory || type == arg_directory)
    return '/';
  if (indicator_style == slash)
    return 0;
  if (type == symbolic_link)
    return '@';
  if (type == fifo)
    return '|';
  if (type == sock)
    return '=';
  return 0;
}

static bool
print_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  char c = get_type_indicator (stat_ok, mode, type);
  if (c != '\0')
    {
      dired_outbyte (c);
      return true;
    }
  return false;
}

/* Returns if color sequence was printed.  */
static bool
print_color_indicator (const struct bin_str *ind)
{
  if (!ind)
    return false;

  if (is_colored (C_NORM))
    restore_default_color ();
    
  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (ind);
  put_indicator (&color_indicator[C_RIGHT]);
  
  return true;
}

/* Returns color indicator or nullptr if none.  */
ATTRIBUTE_PURE
static const struct bin_str*
get_color_indicator (const struct fileinfo *f, bool symlink_target)
{
  char const *name;
  mode_t mode;
  int linkok;
  
  if (symlink_target)
    {
      name = f->linkname;
      mode = f->linkmode;
      linkok = f->linkok ? 0 : -1;
    }
  else
    {
      name = f->name;
      mode = file_or_link_mode (f);
      linkok = f->linkok;
    }

  enum indicator_no type = determine_file_type(f, mode, linkok);
  
  if (type == C_FILE)
    {
      struct color_ext_type *ext = find_matching_extension(name);
      if (ext != nullptr)
        {
          const struct bin_str *s = &(ext->seq);
          return s->string ? s : nullptr;
        }
    }

  if (type == C_LINK && !linkok)
    {
      if (color_symlink_as_referent || is_colored (C_ORPHAN))
        type = C_ORPHAN;
    }

  const struct bin_str *s = &color_indicator[type];
  return s->string ? s : nullptr;
}

static enum indicator_no
determine_file_type(const struct fileinfo *f, mode_t mode, int linkok)
{
  if (linkok == -1 && is_colored (C_MISSING))
    return C_MISSING;
    
  if (!f->stat_ok)
    return get_filetype_indicator(f->filetype);
    
  if (S_ISREG (mode))
    return get_regular_file_type(f, mode);
    
  if (S_ISDIR (mode))
    return get_directory_type(mode);
    
  if (S_ISLNK (mode))
    return C_LINK;
  if (S_ISFIFO (mode))
    return C_FIFO;
  if (S_ISSOCK (mode))
    return C_SOCK;
  if (S_ISBLK (mode))
    return C_BLK;
  if (S_ISCHR (mode))
    return C_CHR;
  if (S_ISDOOR (mode))
    return C_DOOR;
    
  return C_ORPHAN;
}

static enum indicator_no
get_filetype_indicator(int filetype)
{
  static enum indicator_no const filetype_indicator[] =
    {
      C_ORPHAN, C_FIFO, C_CHR, C_DIR, C_BLK, C_FILE,
      C_LINK, C_SOCK, C_FILE, C_DIR
    };
  static_assert (ARRAY_CARDINALITY (filetype_indicator)
                 == filetype_cardinality);
  return filetype_indicator[filetype];
}

static enum indicator_no
get_regular_file_type(const struct fileinfo *f, mode_t mode)
{
  if ((mode & S_ISUID) != 0 && is_colored (C_SETUID))
    return C_SETUID;
  if ((mode & S_ISGID) != 0 && is_colored (C_SETGID))
    return C_SETGID;
  if (f->has_capability)
    return C_CAP;
  if ((mode & S_IXUGO) != 0 && is_colored (C_EXEC))
    return C_EXEC;
  if ((1 < f->stat.st_nlink) && is_colored (C_MULTIHARDLINK))
    return C_MULTIHARDLINK;
  return C_FILE;
}

static enum indicator_no
get_directory_type(mode_t mode)
{
  if ((mode & S_ISVTX) && (mode & S_IWOTH)
      && is_colored (C_STICKY_OTHER_WRITABLE))
    return C_STICKY_OTHER_WRITABLE;
  if ((mode & S_IWOTH) != 0 && is_colored (C_OTHER_WRITABLE))
    return C_OTHER_WRITABLE;
  if ((mode & S_ISVTX) != 0 && is_colored (C_STICKY))
    return C_STICKY;
  return C_DIR;
}

static struct color_ext_type*
find_matching_extension(const char *name)
{
  size_t len = strlen(name);
  const char *name_end = name + len;
  
  for (struct color_ext_type *ext = color_ext_list; ext != nullptr; ext = ext->next)
    {
      if (ext->ext.len > len)
        continue;
        
      const char *suffix_start = name_end - ext->ext.len;
      bool matches = ext->exact_match
        ? STREQ_LEN(suffix_start, ext->ext.string, ext->ext.len)
        : (c_strncasecmp(suffix_start, ext->ext.string, ext->ext.len) == 0);
        
      if (matches)
        return ext;
    }
  return nullptr;
}

/* Output a color indicator (which may contain nulls).  */
static void
put_indicator (const struct bin_str *ind)
{
  if (ind == NULL) {
    return;
  }

  if (!used_color) {
    used_color = true;

    if (tcgetpgrp(STDOUT_FILENO) >= 0) {
      signal_init();
    }

    prep_non_filename_text();
  }

  if (ind->string != NULL && ind->len > 0) {
    fwrite(ind->string, ind->len, 1, stdout);
  }
}

static size_t
length_of_file_name_and_frills (const struct fileinfo *f)
{
  size_t len = 0;
  char buf[MAX (LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND (uintmax_t))];

  if (print_inode)
    {
      size_t inode_len = (format == with_commas)
                         ? strlen (umaxtostr (f->stat.st_ino, buf))
                         : inode_number_width;
      len += 1 + inode_len;
    }

  if (print_block_size)
    {
      size_t block_len;
      if (format == with_commas)
        {
          if (!f->stat_ok)
            {
              block_len = 1;
            }
          else
            {
              block_len = strlen (human_readable (STP_NBLOCKS (&f->stat), buf,
                                                 human_output_opts, ST_NBLOCKSIZE,
                                                 output_block_size));
            }
        }
      else
        {
          block_len = block_size_width;
        }
      len += 1 + block_len;
    }

  if (print_scontext)
    {
      size_t scontext_len = (format == with_commas)
                           ? strlen (f->scontext)
                           : scontext_width;
      len += 1 + scontext_len;
    }

  len += fileinfo_name_width (f);

  if (indicator_style != none)
    {
      char c = get_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
      if (c != 0)
        {
          len += 1;
        }
    }

  return len;
}

static void
print_many_per_line (void)
{
  idx_t cols = calculate_columns (true);
  if (cols == 0)
    return;
    
  struct column_info const *line_fmt = &column_info[cols - 1];
  idx_t rows = (cwd_n_used + cols - 1) / cols;

  for (idx_t row = 0; row < rows; row++)
    {
      print_row (row, rows, cols, line_fmt);
      putchar (eolbyte);
    }
}

static void
print_row (idx_t row, idx_t rows, idx_t cols, struct column_info const *line_fmt)
{
  size_t pos = 0;
  
  for (size_t col = 0; col < cols; col++)
    {
      idx_t filesno = row + (col * rows);
      
      if (filesno >= cwd_n_used)
        break;
        
      struct fileinfo const *f = sorted_file[filesno];
      size_t name_length = length_of_file_name_and_frills (f);
      size_t max_name_length = line_fmt->col_arr[col];
      
      print_file_name_and_frills (f, pos);
      
      if (filesno + rows < cwd_n_used)
        {
          indent (pos + name_length, pos + max_name_length);
          pos += max_name_length;
        }
    }
}

static void
print_horizontal (void)
{
  idx_t cols = calculate_columns (false);
  if (cols <= 0 || cwd_n_used <= 0)
    {
      return;
    }

  struct column_info const *line_fmt = &column_info[cols - 1];
  if (line_fmt == NULL || line_fmt->col_arr == NULL)
    {
      return;
    }

  size_t pos = 0;
  
  for (idx_t filesno = 0; filesno < cwd_n_used; filesno++)
    {
      if (sorted_file[filesno] == NULL)
        {
          continue;
        }

      idx_t col = filesno % cols;
      
      if (filesno > 0 && col == 0)
        {
          putchar (eolbyte);
          pos = 0;
        }

      if (filesno > 0 && col != 0)
        {
          size_t prev_name_length = length_of_file_name_and_frills (sorted_file[filesno - 1]);
          size_t prev_max_name_length = line_fmt->col_arr[(filesno - 1) % cols];
          indent (pos + prev_name_length, pos + prev_max_name_length);
          pos += prev_max_name_length;
        }

      print_file_name_and_frills (sorted_file[filesno], pos);
    }
  
  putchar (eolbyte);
}

/* Output name + SEP + ' '.  */

static void
print_with_separator (char sep)
{
  size_t pos = 0;

  for (idx_t filesno = 0; filesno < cwd_n_used; filesno++)
    {
      struct fileinfo const *f = sorted_file[filesno];
      size_t len = line_length ? length_of_file_name_and_frills (f) : 0;

      if (filesno != 0)
        {
          bool fits_on_line = !line_length || (pos + len + 2 < line_length);
          
          if (fits_on_line)
            {
              pos += 2;
              putchar (sep);
              putchar (' ');
            }
          else
            {
              pos = 0;
              putchar (sep);
              putchar (eolbyte);
            }
        }

      print_file_name_and_frills (f, pos);
      pos += len;
    }
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

  if (tabsize == 0)
    {
      for (size_t i = from; i < to; i++)
        {
          putchar (' ');
        }
      return;
    }

  size_t current = from;
  size_t next_tab_stop = ((current / tabsize) + 1) * tabsize;

  while (current < to)
    {
      if (next_tab_stop <= to)
        {
          putchar ('\t');
          current = next_tab_stop;
          next_tab_stop += tabsize;
        }
      else
        {
          putchar (' ');
          current++;
        }
    }
}

/* Put DIRNAME/NAME into DEST, handling '.' and '/' properly.  */
/* FIXME: maybe remove this function someday.  See about using a
   non-malloc'ing version of file_name_concat.  */

static void
attach (char *dest, char const *dirname, char const *name)
{
  if (dest == NULL || dirname == NULL || name == NULL)
    return;

  size_t dirname_len = strlen(dirname);
  int is_current_dir = (dirname_len == 1 && dirname[0] == '.');
  
  if (!is_current_dir)
    {
      memcpy(dest, dirname, dirname_len);
      dest += dirname_len;
      
      if (dirname_len > 0 && dirname[dirname_len - 1] != '/')
        {
          *dest = '/';
          dest++;
        }
    }
  
  strcpy(dest, name);
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
      idx_t old_alloc = column_info_alloc;
      column_info = xpalloc (column_info, &column_info_alloc,
                             max_cols - column_info_alloc, -1,
                             sizeof *column_info);

      idx_t growth = column_info_alloc - old_alloc;
      idx_t sum_bounds;
      idx_t total_size;
      
      if (ckd_add (&sum_bounds, old_alloc + 1, column_info_alloc))
        xalloc_die ();
        
      if (ckd_mul (&total_size, sum_bounds, growth))
        xalloc_die ();
        
      size_t *p = xinmalloc (total_size >> 1, sizeof *p);

      for (idx_t i = old_alloc; i < column_info_alloc; i++)
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
  idx_t max_cols = (max_idx > 0 && max_idx < cwd_n_used) ? max_idx : cwd_n_used;
  
  if (max_cols == 0) {
    return 0;
  }

  init_column_info (max_cols);

  for (idx_t filesno = 0; filesno < cwd_n_used; ++filesno)
    {
      struct fileinfo const *f = sorted_file[filesno];
      if (!f) {
        continue;
      }
      
      size_t name_length = length_of_file_name_and_frills (f);

      for (idx_t i = 0; i < max_cols; ++i)
        {
          if (!column_info[i].valid_len) {
            continue;
          }

          idx_t idx = calculate_index(by_columns, filesno, cwd_n_used, i);
          size_t real_length = calculate_real_length(name_length, idx, i);
          
          update_column_info(i, idx, real_length);
        }
    }

  return find_maximum_columns(max_cols);
}

static idx_t
calculate_index(bool by_columns, idx_t filesno, idx_t total_files, idx_t col_index)
{
  if (by_columns) {
    idx_t divisor = col_index + 1;
    if (divisor == 0) {
      return 0;
    }
    return filesno / ((total_files + col_index) / divisor);
  }
  return filesno % (col_index + 1);
}

static size_t
calculate_real_length(size_t name_length, idx_t idx, idx_t col_index)
{
  size_t padding = (idx == col_index) ? 0 : 2;
  return name_length + padding;
}

static void
update_column_info(idx_t col_index, idx_t idx, size_t real_length)
{
  if (column_info[col_index].col_arr[idx] >= real_length) {
    return;
  }
  
  size_t length_diff = real_length - column_info[col_index].col_arr[idx];
  column_info[col_index].line_len += length_diff;
  column_info[col_index].col_arr[idx] = real_length;
  column_info[col_index].valid_len = (column_info[col_index].line_len < line_length);
}

static idx_t
find_maximum_columns(idx_t max_cols)
{
  for (idx_t cols = max_cols; cols > 1; --cols)
    {
      if (column_info[cols - 1].valid_len) {
        return cols;
      }
    }
  return 1;
}

void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    {
      emit_try_help ();
      exit (status);
    }

  printf (_("Usage: %s [OPTION]... [FILE]...\n"), program_name);
  fputs (_("\
List information about the FILEs (the current directory by default).\n\
Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n\
"), stdout);

  emit_mandatory_arg_note ();

  fputs (_("\
  -a, --all                  do not ignore entries starting with .\n\
  -A, --almost-all           do not list implied . and ..\n\
      --author               with -l, print the author of each file\n\
  -b, --escape               print C-style escapes for nongraphic characters\n\
      --block-size=SIZE      with -l, scale sizes by SIZE when printing them;\n\
                             e.g., '--block-size=M'; see SIZE format below\n\
\n\
  -B, --ignore-backups       do not list implied entries ending with ~\n\
  -c                         with -lt: sort by, and show, ctime (time of last\n\
                             change of file status information);\n\
                             with -l: show ctime and sort by name;\n\
                             otherwise: sort by ctime, newest first\n\
\n\
  -C                         list entries by columns\n\
      --color[=WHEN]         color the output WHEN; more info below\n\
  -d, --directory            list directories themselves, not their contents\n\
  -D, --dired                generate output designed for Emacs' dired mode\n\
  -f                         same as -a -U\n\
  -F, --classify[=WHEN]      append indicator (one of */=>@|) to entries WHEN\n\
      --file-type            likewise, except do not append '*'\n\
      --format=WORD          across,horizontal (-x), commas (-m), long (-l),\n\
                             single-column (-1), verbose (-l), vertical (-C)\n\
\n\
      --full-time            like -l --time-style=full-iso\n\
  -g                         like -l, but do not list owner\n\
      --group-directories-first\n\
                             group directories before files\n\
  -G, --no-group             in a long listing, don't print group names\n\
  -h, --human-readable       with -l and -s, print sizes like 1K 234M 2G etc.\n\
      --si                   likewise, but use powers of 1000 not 1024\n\
  -H, --dereference-command-line\n\
                             follow symbolic links listed on the command line\n\
      --dereference-command-line-symlink-to-dir\n\
                             follow each command line symbolic link\n\
                             that points to a directory\n\
\n\
      --hide=PATTERN         do not list implied entries matching shell PATTERN\n\
                             (overridden by -a or -A)\n\
\n\
      --hyperlink[=WHEN]     hyperlink file names WHEN\n\
      --indicator-style=WORD\n\
                             append indicator with style WORD to entry names:\n\
                             none (default), slash (-p),\n\
                             file-type (--file-type), classify (-F)\n\
\n\
  -i, --inode                print the index number of each file\n\
  -I, --ignore=PATTERN       do not list implied entries matching shell PATTERN\n\
  -k, --kibibytes            default to 1024-byte blocks for file system usage;\n\
                             used only with -s and per directory totals\n\
\n\
  -l                         use a long listing format\n\
  -L, --dereference          when showing file information for a symbolic\n\
                             link, show information for the file the link\n\
                             references rather than for the link itself\n\
\n\
  -m                         fill width with a comma separated list of entries\n\
  -n, --numeric-uid-gid      like -l, but list numeric user and group IDs\n\
  -N, --literal              print entry names without quoting\n\
  -o                         like -l, but do not list group information\n\
  -p, --indicator-style=slash\n\
                             append / indicator to directories\n\
  -q, --hide-control-chars   print ? instead of nongraphic characters\n\
      --show-control-chars   show nongraphic characters as-is (the default,\n\
                             unless program is 'ls' and output is a terminal)\n\
\n\
  -Q, --quote-name           enclose entry names in double quotes\n\
      --quoting-style=WORD   use quoting style WORD for entry names:\n\
                             literal, locale, shell, shell-always,\n\
                             shell-escape, shell-escape-always, c, escape\n\
                             (overrides QUOTING_STYLE environment variable)\n\
\n\
  -r, --reverse              reverse order while sorting\n\
  -R, --recursive            list subdirectories recursively\n\
  -s, --size                 print the allocated size of each file, in blocks\n\
  -S                         sort by file size, largest first\n\
      --sort=WORD            change default 'name' sort to WORD:\n\
                               none (-U), size (-S), time (-t),\n\
                               version (-v), extension (-X), name, width\n\
\n\
      --time=WORD            select which timestamp used to display or sort;\n\
                               access time (-u): atime, access, use;\n\
                               metadata change time (-c): ctime, status;\n\
                               modified time (default): mtime, modification;\n\
                               birth time: birth, creation;\n\
                             with -l, WORD determines which time to show;\n\
                             with --sort=time, sort by WORD (newest first)\n\
\n\
      --time-style=TIME_STYLE\n\
                             time/date format with -l; see TIME_STYLE below\n\
  -t                         sort by time, newest first; see --time\n\
  -T, --tabsize=COLS         assume tab stops at each COLS instead of 8\n\
  -u                         with -lt: sort by, and show, access time;\n\
                             with -l: show access time and sort by name;\n\
                             otherwise: sort by access time, newest first\n\
\n\
  -U                         do not sort directory entries\n\
  -v                         natural sort of (version) numbers within text\n\
  -w, --width=COLS           set output width to COLS.  0 means no limit\n\
  -x                         list entries by lines instead of by columns\n\
  -X                         sort alphabetically by entry extension\n\
  -Z, --context              print any security context of each file\n\
      --zero                 end each output line with NUL, not newline\n\
  -1                         list one file per line\n\
"), stdout);

  fputs (HELP_OPTION_DESCRIPTION, stdout);
  fputs (VERSION_OPTION_DESCRIPTION, stdout);
  emit_size_note ();

  fputs (_("\
\n\
The TIME_STYLE argument can be full-iso, long-iso, iso, locale, or +FORMAT.\n\
FORMAT is interpreted like in date(1).  If FORMAT is FORMAT1<newline>FORMAT2,\n\
then FORMAT1 applies to non-recent files and FORMAT2 to recent files.\n\
TIME_STYLE prefixed with 'posix-' takes effect only outside the POSIX locale.\n\
Also the TIME_STYLE environment variable sets the default style to use.\n\
\n\
The WHEN argument defaults to 'always' and can also be 'auto' or 'never'.\n\
\n\
Using color to distinguish file types is disabled both by default and\n\
with --color=never.  With --color=auto, ls emits color codes only when\n\
standard output is connected to a terminal.  The LS_COLORS environment\n\
variable can change the settings.  Use the dircolors(1) command to set it.\n\
\n\
Exit status:\n\
 0  if OK,\n\
 1  if minor problems (e.g., cannot access subdirectory),\n\
 2  if serious trouble (e.g., cannot access command-line argument).\n\
"), stdout);

  emit_ancillary_info (PROGRAM_NAME);
  exit (status);
}
