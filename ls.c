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
    return file->linkmode;
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
    putchar(c);
}

/* Output the buffer S, of length S_LEN, and increment DIRED_POS by S_LEN.  */
static void dired_outbuf(char const *s, size_t s_len)
{
    dired_pos += s_len;
    fwrite(s, sizeof *s, s_len, stdout);
}

/* Output the string S, and increment DIRED_POS by its length.  */
static void
dired_outstring (char const *s)
{
  dired_outbuf (s, strlen (s));
}

static void
dired_indent (void)
{
  if (dired)
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
static void
push_current_dired_pos (struct obstack *obs)
{
  if (dired)
    obstack_grow (obs, &dired_pos, sizeof dired_pos);
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
  int dev_ino_size = sizeof *di;
  
  obstack_blank (&dev_ino_obstack, dev_ino_size);
  di = (struct dev_ino *) obstack_next_free (&dev_ino_obstack) - 1;
  di->st_dev = dev;
  di->st_ino = ino;
}

/* Pop a dev/ino struct off the global dev_ino_obstack
   and return that struct.  */
static struct dev_ino
dev_ino_pop (void)
{
  const int dev_ino_size = sizeof (struct dev_ino);
  affirm (dev_ino_size <= obstack_object_size (&dev_ino_obstack));
  obstack_blank_fast (&dev_ino_obstack, -dev_ino_size);
  struct dev_ino *di = (struct dev_ino *) obstack_next_free (&dev_ino_obstack);
  return *di;
}

static void
assert_matching_dev_ino (char const *name, struct dev_ino di)
{
  MAYBE_UNUSED struct stat sb;
  assure (0 <= stat (name, &sb));
  assure (sb.st_dev == di.st_dev);
  assure (sb.st_ino == di.st_ino);
}

static char eolbyte = '\n';

/* Write to standard output PREFIX, followed by the quoting style and
   a space-separated list of the integers stored in OS all on one line.  */

static void print_positions(const char *prefix, const off_t *positions, size_t count)
{
    fputs(prefix, stdout);
    for (size_t i = 0; i < count; i++)
    {
        intmax_t p = positions[i];
        printf(" %jd", p);
    }
    putchar('\n');
}

static void dired_dump_obstack(const char *prefix, struct obstack *os)
{
    size_t n_pos = obstack_object_size(os) / sizeof(dired_pos);
    if (n_pos == 0)
        return;
    
    off_t *positions = obstack_finish(os);
    print_positions(prefix, positions, n_pos);
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
do_stat (char const *name, struct stat *st)
{
  return stat (name, st);
}

static int
do_lstat (char const *name, struct stat *st)
{
  return lstat (name, st);
}

static int
stat_for_mode (char const *name, struct stat *st)
{
  return stat (name, st);
}

static int
stat_for_ino (char const *name, struct stat *st)
{
  return stat (name, st);
}

static int
fstat_for_ino (int fd, struct stat *st)
{
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
  for (; *fmt; fmt++)
    {
      if (fmt[0] != '%')
        continue;
      
      if (fmt[1] == 'b')
        return fmt;
      
      if (fmt[1] == '%')
        fmt++;
    }
  return nullptr;
}

static char RFC3986[256];
static void
file_escape_init (void)
{
  const char ALLOWED_CHARS[] = {'~', '-', '.', '_'};
  const int ALLOWED_CHARS_COUNT = sizeof(ALLOWED_CHARS) / sizeof(ALLOWED_CHARS[0]);
  const int ASCII_TABLE_SIZE = 256;
  
  for (int i = 0; i < ASCII_TABLE_SIZE; i++)
  {
    int is_allowed = c_isalnum(i);
    
    for (int j = 0; j < ALLOWED_CHARS_COUNT && !is_allowed; j++)
    {
      if (i == ALLOWED_CHARS[j])
      {
        is_allowed = 1;
      }
    }
    
    RFC3986[i] |= is_allowed;
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

  if (!load_month_abbreviations(abmon, mon_width, mon_len, &max_mon_width))
    return false;

  if (!align_month_abbreviations(abmon, mon_width, mon_len, max_mon_width))
    return false;

  return true;
#endif
}

static bool
load_month_abbreviations(char abmon[12][ABFORMAT_SIZE], int mon_width[12], 
                         int mon_len[12], int *max_mon_width)
{
  for (int i = 0; i < 12; i++)
    {
      if (!load_single_month(abmon[i], &mon_width[i], &mon_len[i], i))
        return false;
      *max_mon_width = MAX(*max_mon_width, mon_width[i]);
    }
  return true;
}

static bool
load_single_month(char *month_buffer, int *width, int *length, int month_index)
{
  char const *abbr = nl_langinfo(ABMON_1 + month_index);
  *length = strnlen(abbr, ABFORMAT_SIZE);
  
  if (*length == ABFORMAT_SIZE)
    return false;
  if (strchr(abbr, '%'))
    return false;
  
  *width = mbswidth(strcpy(month_buffer, abbr), MBSWIDTH_FLAGS);
  return *width >= 0;
}

static bool
align_month_abbreviations(char abmon[12][ABFORMAT_SIZE], int mon_width[12],
                          int mon_len[12], int max_mon_width)
{
  for (int i = 0; i < 12; i++)
    {
      if (!align_single_month(abmon[i], mon_width[i], mon_len[i], max_mon_width))
        return false;
    }
  return true;
}

static bool
align_single_month(char *month_buffer, int width, int length, int max_width)
{
  int fill = max_width - width;
  
  if (ABFORMAT_SIZE - length <= fill)
    return false;
  
  bool align_left = !c_isdigit(month_buffer[0]);
  apply_alignment(month_buffer, length, fill, align_left);
  month_buffer[length + fill] = '\0';
  
  return true;
}

static void
apply_alignment(char *buffer, int length, int fill, bool align_left)
{
  int fill_offset;
  
  if (align_left)
    {
      fill_offset = length;
    }
  else
    {
      memmove(buffer + fill, buffer, length);
      fill_offset = 0;
    }
  
  memset(buffer + fill_offset, ' ', fill);
}

/* Initialize ABFORMAT and USE_ABFORMAT.  */

static void
abformat_init (void)
{
  char const *pb[2];
  for (int recent = 0; recent < 2; recent++)
    pb[recent] = first_percent_b (long_time_format[recent]);
  if (! (pb[0] || pb[1]))
    return;

  char abmon[12][ABFORMAT_SIZE];
  if (! abmon_init (abmon))
    return;

  for (int recent = 0; recent < 2; recent++)
    if (!format_month_names(recent, pb[recent], long_time_format[recent], abmon))
      return;

  use_abformat = true;
}

static bool
format_month_names(int recent, char const *percent_b, char const *fmt, char abmon[][ABFORMAT_SIZE])
{
  for (int i = 0; i < 12; i++)
    if (!format_single_month(abformat[recent][i], percent_b, fmt, abmon[i]))
      return false;
  return true;
}

static bool
format_single_month(char *nfmt, char const *percent_b, char const *fmt, char const *month_abbr)
{
  int nbytes;
  
  if (!percent_b)
    nbytes = snprintf(nfmt, ABFORMAT_SIZE, "%s", fmt);
  else
    nbytes = format_with_month_substitution(nfmt, percent_b, fmt, month_abbr);
  
  return (0 <= nbytes && nbytes < ABFORMAT_SIZE);
}

static int
format_with_month_substitution(char *nfmt, char const *percent_b, char const *fmt, char const *month_abbr)
{
  int prefix_len = percent_b - fmt;
  if (prefix_len > MIN(ABFORMAT_SIZE, INT_MAX))
    return -1;
  
  return snprintf(nfmt, ABFORMAT_SIZE, "%.*s%s%s",
                  prefix_len, fmt, month_abbr, percent_b + 2);
}

static size_t
dev_ino_hash (void const *x, size_t table_size)
{
  struct dev_ino const *p = x;
  return (uintmax_t) p->st_ino % table_size;
}

static bool
dev_ino_compare (void const *x, void const *y)
{
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

static struct dev_ino* create_dev_ino_entry(dev_t dev, ino_t ino)
{
  struct dev_ino *ent = xmalloc(sizeof *ent);
  ent->st_ino = ino;
  ent->st_dev = dev;
  return ent;
}

static void handle_insertion_failure(void)
{
  xalloc_die();
}

static bool is_duplicate_entry(struct dev_ino *inserted, struct dev_ino *original)
{
  return inserted != original;
}

static bool visit_dir(dev_t dev, ino_t ino)
{
  struct dev_ino *ent = create_dev_ino_entry(dev, ino);
  struct dev_ino *ent_from_table = hash_insert(active_dir_set, ent);

  if (ent_from_table == nullptr)
    handle_insertion_failure();

  bool found_match = is_duplicate_entry(ent_from_table, ent);

  if (found_match)
    free(ent);

  return found_match;
}

static void
free_pending_ent (struct pending *p)
{
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
  return (s[0] != '0') | (s[len - 1] != '0');
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
    return;
    
  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (&color_indicator[C_NORM]);
  put_indicator (&color_indicator[C_RIGHT]);
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void sighandler(int sig)
{
    if (!SA_NOCLDSTOP) {
        signal(sig, SIG_IGN);
    }
    
    if (!interrupt_signal) {
        interrupt_signal = sig;
    }
}

/* A SIGTSTP was received; arrange for the program to suspend itself.  */

static void stophandler(int sig) {
    if (!SA_NOCLDSTOP) {
        signal(sig, stophandler);
    }
    
    if (!interrupt_signal) {
        stop_signal_count++;
    }
}

/* Process any pending signals.  If signals are caught, this function
   should be called periodically.  Ideally there should never be an
   unbounded amount of time when signals are not being processed.
   Signal handling can restore the default colors, so callers must
   immediately change colors after invoking this function.  */

static void restore_output_state(void)
{
    if (used_color)
        restore_default_color();
    fflush(stdout);
}

static void block_signals(sigset_t *oldset)
{
    sigprocmask(SIG_BLOCK, &caught_signals, oldset);
}

static void restore_signals(const sigset_t *oldset)
{
    sigprocmask(SIG_SETMASK, oldset, nullptr);
}

static int determine_signal_to_raise(int *stops)
{
    int sig = interrupt_signal;
    *stops = stop_signal_count;
    
    if (*stops)
    {
        stop_signal_count = *stops - 1;
        return SIGSTOP;
    }
    
    signal(sig, SIG_DFL);
    return sig;
}

static void handle_one_signal(void)
{
    int stops;
    sigset_t oldset;
    
    restore_output_state();
    block_signals(&oldset);
    
    int sig = determine_signal_to_raise(&stops);
    
    raise(sig);
    restore_signals(&oldset);
}

static void process_signals(void)
{
    while (interrupt_signal || stop_signal_count)
    {
        handle_one_signal();
    }
}

/* Setup signal handlers if INIT is true,
   otherwise restore to the default.  */

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

#if ! SA_NOCLDSTOP
static bool caught_sig[nsigs];
#endif

static void (*get_signal_handler(int signal_num))(int)
{
    return signal_num == SIGTSTP ? stophandler : sighandler;
}

#if SA_NOCLDSTOP
static void setup_signal_action(int signal_num, struct sigaction *act)
{
    if (sigismember(&caught_signals, signal_num))
    {
        act->sa_handler = get_signal_handler(signal_num);
        sigaction(signal_num, act, nullptr);
    }
}

static void collect_non_ignored_signals(void)
{
    struct sigaction act;
    int j;
    
    sigemptyset(&caught_signals);
    for (j = 0; j < nsigs; j++)
    {
        sigaction(sig[j], nullptr, &act);
        if (act.sa_handler != SIG_IGN)
            sigaddset(&caught_signals, sig[j]);
    }
}

static void install_signal_handlers(void)
{
    struct sigaction act;
    int j;
    
    collect_non_ignored_signals();
    
    act.sa_mask = caught_signals;
    act.sa_flags = SA_RESTART;
    
    for (j = 0; j < nsigs; j++)
        setup_signal_action(sig[j], &act);
}

static void restore_signal_defaults(void)
{
    int j;
    
    for (j = 0; j < nsigs; j++)
        if (sigismember(&caught_signals, sig[j]))
            signal(sig[j], SIG_DFL);
}
#else
static void setup_single_signal(int j)
{
    caught_sig[j] = (signal(sig[j], SIG_IGN) != SIG_IGN);
    if (caught_sig[j])
    {
        signal(sig[j], get_signal_handler(sig[j]));
        siginterrupt(sig[j], 0);
    }
}

static void install_signal_handlers(void)
{
    int j;
    
    for (j = 0; j < nsigs; j++)
        setup_single_signal(j);
}

static void restore_signal_defaults(void)
{
    int j;
    
    for (j = 0; j < nsigs; j++)
        if (caught_sig[j])
            signal(sig[j], SIG_DFL);
}
#endif

static void signal_setup(bool init)
{
    if (init)
        install_signal_handlers();
    else
        restore_signal_defaults();
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

  setup_color_output();
  setup_symlink_checking();
  setup_dereference_mode();
  setup_recursive_mode();
  setup_format_flags();
  setup_auxiliary_structures();

  cwd_n_alloc = 100;
  cwd_file = xmalloc (cwd_n_alloc * sizeof *cwd_file);
  cwd_n_used = 0;

  clear_files ();

  n_files = argc - i;

  process_file_arguments(n_files, argc, argv, i);

  if (cwd_n_used)
    {
      sort_files ();
      if (!immediate_dirs)
        extract_dirs_from_files (nullptr, true);
    }

  handle_current_files_output(n_files);
  process_pending_directories();
  finalize_color_output();
  finalize_dired_output();
  cleanup_recursive_structures();

  return exit_status;
}

static void setup_color_output(void)
{
  if (print_with_color)
    parse_ls_color ();

  if (print_with_color)
    {
      tabsize = 0;
    }
}

static void setup_symlink_checking(void)
{
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
}

static void setup_dereference_mode(void)
{
  if (dereference == DEREF_UNDEFINED)
    {
      dereference = ((immediate_dirs
                      || indicator_style == classify
                      || format == long_format)
                     ? DEREF_NEVER
                     : DEREF_COMMAND_LINE_SYMLINK_TO_DIR);
    }
}

static void setup_recursive_mode(void)
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
}

static void setup_format_flags(void)
{
  localtz = tzalloc (getenv ("TZ"));

  format_needs_stat = ((sort_type == sort_time) | (sort_type == sort_size)
                       | (format == long_format)
                       | print_block_size | print_hyperlink | print_scontext);
  format_needs_type = ((! format_needs_stat)
                       & (recursive | print_with_color | print_scontext
                          | directories_first
                          | (indicator_style != none)));
  format_needs_capability = print_with_color && is_colored (C_CAP);
}

static void setup_auxiliary_structures(void)
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

static void process_file_arguments(int n_files, int argc, char **argv, int i)
{
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
        gobble_file (argv[i++], unknown, NOT_AN_INODE_NUMBER, true, nullptr);
      while (i < argc);
    }
}

static void handle_current_files_output(int n_files)
{
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
}

static void process_pending_directories(void)
{
  struct pending *thispend;
  
  while (pending_dirs)
    {
      thispend = pending_dirs;
      pending_dirs = pending_dirs->next;

      if (LOOP_DETECT && process_marker_entry(thispend))
        continue;

      print_dir (thispend->name, thispend->realname,
                 thispend->command_line_arg);

      free_pending_ent (thispend);
      print_dir_name = true;
    }
}

static bool process_marker_entry(struct pending *thispend)
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
      return true;
    }
  return false;
}

static void finalize_color_output(void)
{
  int j;
  
  if (!print_with_color || !used_color)
    return;

  if (!is_default_color_restore_needed())
    restore_default_color ();

  fflush (stdout);

  signal_restore ();

  for (j = stop_signal_count; j; j--)
    raise (SIGSTOP);
  j = interrupt_signal;
  if (j)
    raise (j);
}

static bool is_default_color_restore_needed(void)
{
  #define COLOR_LEFT_LEN 2
  #define COLOR_LEFT_STR "\033["
  #define COLOR_RIGHT_LEN 1
  #define COLOR_RIGHT_CHAR 'm'
  
  return (color_indicator[C_LEFT].len == COLOR_LEFT_LEN
          && memcmp (color_indicator[C_LEFT].string, COLOR_LEFT_STR, COLOR_LEFT_LEN) == 0
          && color_indicator[C_RIGHT].len == COLOR_RIGHT_LEN
          && color_indicator[C_RIGHT].string[0] == COLOR_RIGHT_CHAR);
}

static void finalize_dired_output(void)
{
  if (dired)
    {
      dired_dump_obstack ("//DIRED//", &dired_obstack);
      dired_dump_obstack ("//SUBDIRED//", &subdired_obstack);
      printf ("//DIRED-OPTIONS// --quoting-style=%s\n",
              quoting_style_args[get_quoting_style (filename_quoting_options)]);
    }
}

static void cleanup_recursive_structures(void)
{
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
  
  switch (xstrtoumax (spec, nullptr, 0, &val, ""))
    {
    case LONGINT_OK:
      return val <= MIN (PTRDIFF_MAX, SIZE_MAX) ? val : 0;

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

static bool
stdout_isatty (void)
{
  static signed char out_tty = -1;
  if (out_tty < 0)
    out_tty = isatty (STDOUT_FILENO);
  assume (out_tty == 0 || out_tty == 1);
  return out_tty;
}

/* Set all the option flags according to the switches specified.
   Return the index of the first non-option argument.  */

static void handle_option_a(void) {
    ignore_mode = IGNORE_MINIMAL;
}

static void handle_option_f(void) {
    ignore_mode = IGNORE_MINIMAL;
    sort_opt = sort_none;
}

static void handle_option_g(int *format_opt) {
    *format_opt = long_format;
    print_owner = false;
}

static void handle_option_h(void) {
    file_human_output_opts = human_output_opts =
        human_autoscale | human_SI | human_base_1024;
    file_output_block_size = output_block_size = 1;
}

static void handle_option_n(int *format_opt) {
    numeric_ids = true;
    *format_opt = long_format;
}

static void handle_option_o(int *format_opt) {
    *format_opt = long_format;
    print_group = false;
}

static void handle_option_D(int *format_opt) {
    *format_opt = long_format;
    print_hyperlink = false;
    dired = true;
}

static void handle_option_B(void) {
    add_ignore_pattern("*~");
    add_ignore_pattern(".*~");
}

static void handle_classify_option(char *optarg) {
    int i = optarg ? XARGMATCH("--classify", optarg, when_args, when_types) : when_always;
    if (i == when_always || (i == when_if_tty && stdout_isatty()))
        indicator_style = classify;
}

static void handle_color_option(char *optarg) {
    int i = optarg ? XARGMATCH("--color", optarg, when_args, when_types) : when_always;
    print_with_color = (i == when_always || (i == when_if_tty && stdout_isatty()));
}

static void handle_hyperlink_option(char *optarg) {
    int i = optarg ? XARGMATCH("--hyperlink", optarg, when_args, when_types) : when_always;
    print_hyperlink = (i == when_always || (i == when_if_tty && stdout_isatty()));
}

static void handle_hide_option(char *optarg) {
    struct ignore_pattern *hide = xmalloc(sizeof *hide);
    hide->pattern = optarg;
    hide->next = hide_patterns;
    hide_patterns = hide;
}

static void handle_block_size_option(char *optarg, int oi) {
    enum strtol_error e = human_options(optarg, &human_output_opts, &output_block_size);
    if (e != LONGINT_OK)
        xstrtol_fatal(e, oi, 0, long_options, optarg);
    file_human_output_opts = human_output_opts;
    file_output_block_size = output_block_size;
}

static void handle_si_option(void) {
    file_human_output_opts = human_output_opts = human_autoscale | human_SI;
    file_output_block_size = output_block_size = 1;
}

static void handle_zero_option(int *format_opt, int *hide_control_chars_opt, int *quoting_style_opt) {
    eolbyte = 0;
    *hide_control_chars_opt = false;
    if (*format_opt != long_format)
        *format_opt = one_per_line;
    print_with_color = false;
    *quoting_style_opt = literal_quoting_style;
}

static void process_block_size_env(bool kibibytes_specified) {
    if (!output_block_size) {
        char const *ls_block_size = getenv("LS_BLOCK_SIZE");
        human_options(ls_block_size, &human_output_opts, &output_block_size);
        if (ls_block_size || getenv("BLOCK_SIZE")) {
            file_human_output_opts = human_output_opts;
            file_output_block_size = output_block_size;
        }
        if (kibibytes_specified) {
            human_output_opts = 0;
            output_block_size = 1024;
        }
    }
}

static int determine_format(int format_opt) {
    if (format_opt >= 0)
        return format_opt;
    if (ls_mode == LS_LS)
        return stdout_isatty() ? many_per_line : one_per_line;
    if (ls_mode == LS_MULTI_COL)
        return many_per_line;
    return long_format;
}

static ptrdiff_t get_terminal_width(void) {
    ptrdiff_t width = -1;
#ifdef TIOCGWINSZ
    struct winsize ws;
    if (stdout_isatty() && ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) >= 0 && ws.ws_col > 0)
        width = ws.ws_col <= MIN(PTRDIFF_MAX, SIZE_MAX) ? ws.ws_col : 0;
#endif
    return width;
}

static ptrdiff_t get_env_columns(void) {
    char const *p = getenv("COLUMNS");
    if (p && *p) {
        ptrdiff_t width = decode_line_length(p);
        if (width < 0)
            error(0, 0, _("ignoring invalid width in environment variable COLUMNS: %s"), quote(p));
        return width;
    }
    return -1;
}

static ptrdiff_t determine_line_length(ptrdiff_t width_opt, int format) {
    ptrdiff_t linelen = width_opt;
    if (format == many_per_line || format == horizontal || format == with_commas || print_with_color) {
        if (linelen < 0)
            linelen = get_terminal_width();
        if (linelen < 0)
            linelen = get_env_columns();
    }
    return linelen < 0 ? 80 : linelen;
}

static void set_tabsize(ptrdiff_t tabsize_opt, int format) {
    if (format == many_per_line || format == horizontal || format == with_commas) {
        if (tabsize_opt >= 0) {
            tabsize = tabsize_opt;
        } else {
            tabsize = 8;
            char const *p = getenv("TABSIZE");
            if (p) {
                uintmax_t tmp;
                if (xstrtoumax(p, nullptr, 0, &tmp, "") == LONGINT_OK && tmp <= SIZE_MAX)
                    tabsize = tmp;
                else
                    error(0, 0, _("ignoring invalid tab size in environment variable TABSIZE: %s"), quote(p));
            }
        }
    }
}

static void configure_quoting(int quoting_style_opt, int format) {
    int qs = quoting_style_opt;
    if (qs < 0)
        qs = getenv_quoting_style();
    if (qs < 0)
        qs = (ls_mode == LS_LS ? (stdout_isatty() ? shell_escape_quoting_style : -1) : escape_quoting_style);
    if (qs >= 0)
        set_quoting_style(nullptr, qs);
    
    qs = get_quoting_style(nullptr);
    align_variable_outer_quotes =
        ((format == long_format || ((format == many_per_line || format == horizontal) && line_length))
         && (qs == shell_quoting_style || qs == shell_escape_quoting_style || qs == c_maybe_quoting_style));
    
    filename_quoting_options = clone_quoting_options(nullptr);
    if (qs == escape_quoting_style)
        set_char_quoting(filename_quoting_options, ' ', 1);
    if (file_type <= indicator_style) {
        char const *p;
        for (p = &"*=>@|"[indicator_style - file_type]; *p; p++)
            set_char_quoting(filename_quoting_options, *p, 1);
    }
    
    dirname_quoting_options = clone_quoting_options(nullptr);
    set_char_quoting(dirname_quoting_options, ':', 1);
}

static void configure_time_style(char const *time_style_option) {
    static char const posix_prefix[] = "posix-";
    char const *style = time_style_option;
    
    if (!style) {
        style = getenv("TIME_STYLE");
        if (!style)
            style = "locale";
    }
    
    while (STREQ_LEN(style, posix_prefix, sizeof posix_prefix - 1)) {
        if (!hard_locale(LC_TIME))
            return;
        style += sizeof posix_prefix - 1;
    }
    
    if (*style == '+') {
        char const *p0 = style + 1;
        char *p0nl = strchr(p0, '\n');
        char const *p1 = p0;
        if (p0nl) {
            if (strchr(p0nl + 1, '\n'))
                error(LS_FAILURE, 0, _("invalid time style format %s"), quote(p0));
            *p0nl++ = '\0';
            p1 = p0nl;
        }
        long_time_format[0] = p0;
        long_time_format[1] = p1;
    } else {
        switch (x_timestyle_match(style, true, time_style_args, (char const *)time_style_types, sizeof(*time_style_types), LS_FAILURE)) {
        case full_iso_time_style:
            long_time_format[0] = long_time_format[1] = "%Y-%m-%d %H:%M:%S.%N %z";
            break;
        case long_iso_time_style:
            long_time_format[0] = long_time_format[1] = "%Y-%m-%d %H:%M";
            break;
        case iso_time_style:
            long_time_format[0] = "%Y-%m-%d ";
            long_time_format[1] = "%m-%d %H:%M";
            break;
        case locale_time_style:
            if (hard_locale(LC_TIME)) {
                for (int i = 0; i < 2; i++)
                    long_time_format[i] = dcgettext(nullptr, long_time_format[i], LC_TIME);
            }
        }
    }
    abformat_init();
}

static int decode_switches(int argc, char **argv) {
    char const *time_style_option = nullptr;
    bool kibibytes_specified = false;
    int format_opt = -1;
    int hide_control_chars_opt = -1;
    int quoting_style_opt = -1;
    int sort_opt = -1;
    ptrdiff_t tabsize_opt = -1;
    ptrdiff_t width_opt = -1;

    while (true) {
        int oi = -1;
        int c = getopt_long(argc, argv, "abcdfghiklmnopqrstuvw:xABCDFGHI:LNQRST:UXZ1", long_options, &oi);
        if (c == -1)
            break;

        switch (c) {
        case 'a': handle_option_a(); break;
        case 'b': quoting_style_opt = escape_quoting_style; break;
        case 'c': time_type = time_ctime; explicit_time = true; break;
        case 'd': immediate_dirs = true; break;
        case 'f': handle_option_f(); break;
        case FILE_TYPE_INDICATOR_OPTION: indicator_style = file_type; break;
        case 'g': handle_option_g(&format_opt); break;
        case 'h': handle_option_h(); break;
        case 'i': print_inode = true; break;
        case 'k': kibibytes_specified = true; break;
        case 'l': format_opt = long_format; break;
        case 'm': format_opt = with_commas; break;
        case 'n': handle_option_n(&format_opt); break;
        case 'o': handle_option_o(&format_opt); break;
        case 'p': indicator_style = slash; break;
        case 'q': hide_control_chars_opt = true; break;
        case 'r': sort_reverse = true; break;
        case 's': print_block_size = true; break;
        case 't': sort_opt = sort_time; break;
        case 'u': time_type = time_atime; explicit_time = true; break;
        case 'v': sort_opt = sort_version; break;
        case 'w':
            width_opt = decode_line_length(optarg);
            if (width_opt < 0)
                error(LS_FAILURE, 0, "%s: %s", _("invalid line width"), quote(optarg));
            break;
        case 'x': format_opt = horizontal; break;
        case 'A': ignore_mode = IGNORE_DOT_AND_DOTDOT; break;
        case 'B': handle_option_B(); break;
        case 'C': format_opt = many_per_line; break;
        case 'D': handle_option_D(&format_opt); break;
        case 'F': handle_classify_option(optarg); break;
        case 'G': print_group = false; break;
        case 'H': dereference = DEREF_COMMAND_LINE_ARGUMENTS; break;
        case DEREFERENCE_COMMAND_LINE_SYMLINK_TO_DIR_OPTION:
            dereference = DEREF_COMMAND_LINE_SYMLINK_TO_DIR; break;
        case 'I': add_ignore_pattern(optarg); break;
        case 'L': dereference = DEREF_ALWAYS; break;
        case 'N': quoting_style_opt = literal_quoting_style; break;
        case 'Q': quoting_style_opt = c_quoting_style; break;
        case 'R': recursive = true; break;
        case 'S': sort_opt = sort_size; break;
        case 'T':
            tabsize_opt = xnumtoumax(optarg, 0, 0, MIN(PTRDIFF_MAX, SIZE_MAX), "", _("invalid tab size"), LS_FAILURE, 0);
            break;
        case 'U': sort_opt = sort_none; break;
        case 'X': sort_opt = sort_extension; break;
        case '1':
            if (format_opt != long_format)
                format_opt = one_per_line;
            break;
        case AUTHOR_OPTION: print_author = true; break;
        case HIDE_OPTION: handle_hide_option(optarg); break;
        case SORT_OPTION: sort_opt = XARGMATCH("--sort", optarg, sort_args, sort_types); break;
        case GROUP_DIRECTORIES_FIRST_OPTION: directories_first = true; break;
        case TIME_OPTION:
            time_type = XARGMATCH("--time", optarg, time_args, time_types);
            explicit_time = true;
            break;
        case FORMAT_OPTION: format_opt = XARGMATCH("--format", optarg, format_args, format_types); break;
        case FULL_TIME_OPTION:
            format_opt = long_format;
            time_style_option = "full-iso";
            break;
        case COLOR_OPTION: handle_color_option(optarg); break;
        case HYPERLINK_OPTION: handle_hyperlink_option(optarg); break;
        case INDICATOR_STYLE_OPTION:
            indicator_style = XARGMATCH("--indicator-style", optarg, indicator_style_args, indicator_style_types);
            break;
        case QUOTING_STYLE_OPTION:
            quoting_style_opt = XARGMATCH("--quoting-style", optarg, quoting_style_args, quoting_style_vals);
            break;
        case TIME_STYLE_OPTION: time_style_option = optarg; break;
        case SHOW_CONTROL_CHARS_OPTION: hide_control_chars_opt = false; break;
        case BLOCK_SIZE_OPTION: handle_block_size_option(optarg, oi); break;
        case SI_OPTION: handle_si_option(); break;
        case 'Z': print_scontext = true; break;
        case ZERO_OPTION: handle_zero_option(&format_opt, &hide_control_chars_opt, &quoting_style_opt); break;
        case_GETOPT_HELP_CHAR;
        case_GETOPT_VERSION_CHAR(PROGRAM_NAME, AUTHORS);
        default: usage(LS_FAILURE);
        }
    }

    process_block_size_env(kibibytes_specified);
    format = determine_format(format_opt);
    line_length = determine_line_length(width_opt, format);
    max_idx = line_length / MIN_COLUMN_WIDTH;
    max_idx += line_length % MIN_COLUMN_WIDTH != 0;
    set_tabsize(tabsize_opt, format);
    qmark_funny_chars = (hide_control_chars_opt < 0 ? ls_mode == LS_LS && stdout_isatty() : hide_control_chars_opt);
    configure_quoting(quoting_style_opt, format);
    dired &= (format == long_format) & !print_hyperlink;
    if (eolbyte < dired)
        error(LS_FAILURE, 0, _("--dired and --zero are incompatible"));
    sort_type = (sort_opt >= 0 ? sort_opt : (format != long_format && explicit_time) ? sort_time : sort_name);
    if (format == long_format)
        configure_time_style(time_style_option);
    
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

#define OCTAL_BASE 8
#define HEX_BASE 16
#define ESCAPE_CHAR 27
#define DELETE_CHAR 127
#define CONTROL_MASK 037
#define HEX_DIGIT_OFFSET 10

typedef enum {
    ST_GND, ST_BACKSLASH, ST_OCTAL, ST_HEX, ST_CARET, ST_END, ST_ERROR
} parse_state;

static bool is_octal_digit(char c)
{
    return c >= '0' && c <= '7';
}

static bool is_hex_digit(char c)
{
    return (c >= '0' && c <= '9') || 
           (c >= 'a' && c <= 'f') || 
           (c >= 'A' && c <= 'F');
}

static int hex_digit_value(char c)
{
    if (c >= '0' && c <= '9')
        return c - '0';
    if (c >= 'a' && c <= 'f')
        return c - 'a' + HEX_DIGIT_OFFSET;
    if (c >= 'A' && c <= 'F')
        return c - 'A' + HEX_DIGIT_OFFSET;
    return -1;
}

static char get_escape_char(char c)
{
    switch (c)
    {
    case 'a': return '\a';
    case 'b': return '\b';
    case 'e': return ESCAPE_CHAR;
    case 'f': return '\f';
    case 'n': return '\n';
    case 'r': return '\r';
    case 't': return '\t';
    case 'v': return '\v';
    case '?': return DELETE_CHAR;
    case '_': return ' ';
    default: return c;
    }
}

static void write_char(char **q, char c, size_t *count)
{
    *(*q)++ = c;
    (*count)++;
}

static parse_state process_ground_state(char const **p, char **q, 
                                       size_t *count, bool equals_end)
{
    char c = **p;
    
    if (c == ':' || c == '\0')
        return ST_END;
    
    if (c == '\\')
    {
        (*p)++;
        return ST_BACKSLASH;
    }
    
    if (c == '^')
    {
        (*p)++;
        return ST_CARET;
    }
    
    if (c == '=' && equals_end)
        return ST_END;
    
    write_char(q, *(*p)++, count);
    return ST_GND;
}

static parse_state process_backslash_state(char const **p, char **q, 
                                          size_t *count, char *num)
{
    char c = **p;
    
    if (c == '\0')
    {
        (*p)++;
        return ST_ERROR;
    }
    
    if (is_octal_digit(c))
    {
        *num = c - '0';
        (*p)++;
        return ST_OCTAL;
    }
    
    if (c == 'x' || c == 'X')
    {
        *num = 0;
        (*p)++;
        return ST_HEX;
    }
    
    *num = get_escape_char(c);
    write_char(q, *num, count);
    (*p)++;
    return ST_GND;
}

static parse_state process_octal_state(char const **p, char **q, 
                                      size_t *count, char *num)
{
    if (!is_octal_digit(**p))
    {
        write_char(q, *num, count);
        return ST_GND;
    }
    
    *num = (*num << 3) + (*(*p)++ - '0');
    return ST_OCTAL;
}

static parse_state process_hex_state(char const **p, char **q, 
                                    size_t *count, char *num)
{
    int value = hex_digit_value(**p);
    
    if (value < 0)
    {
        write_char(q, *num, count);
        return ST_GND;
    }
    
    *num = (*num << 4) + value;
    (*p)++;
    return ST_HEX;
}

static parse_state process_caret_state(char const **p, char **q, 
                                      size_t *count)
{
    char c = **p;
    
    if (c >= '@' && c <= '~')
    {
        write_char(q, *(*p)++ & CONTROL_MASK, count);
        return ST_GND;
    }
    
    if (c == '?')
    {
        write_char(q, DELETE_CHAR, count);
        (*p)++;
        return ST_GND;
    }
    
    return ST_ERROR;
}

static bool
get_funky_string (char **dest, char const **src, bool equals_end,
                  size_t *output_count)
{
    char num = 0;
    size_t count = 0;
    parse_state state = ST_GND;
    char const *p = *src;
    char *q = *dest;

    while (state < ST_END)
    {
        switch (state)
        {
        case ST_GND:
            state = process_ground_state(&p, &q, &count, equals_end);
            break;

        case ST_BACKSLASH:
            state = process_backslash_state(&p, &q, &count, &num);
            break;

        case ST_OCTAL:
            state = process_octal_state(&p, &q, &count, &num);
            break;

        case ST_HEX:
            state = process_hex_state(&p, &q, &count, &num);
            break;

        case ST_CARET:
            state = process_caret_state(&p, &q, &count);
            break;

        case ST_END: 
        case ST_ERROR: 
        default:
            unreachable();
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
  if (! term || ! *term)
    return false;

  return term_matches_any_in_list(term);
}

static bool
term_matches_any_in_list(char const *term)
{
  char const *line = G_line;
  while (line - G_line < sizeof (G_line))
    {
      if (is_term_line(line) && term_matches_pattern(line, term))
        return true;
      
      line += strlen (line) + 1;
    }
  return false;
}

static bool
is_term_line(char const *line)
{
  return STRNCMP_LIT (line, "TERM ") == 0;
}

static bool
term_matches_pattern(char const *line, char const *term)
{
  const int TERM_PREFIX_LENGTH = 5;
  return fnmatch (line + TERM_PREFIX_LENGTH, term, 0) == 0;
}

static bool should_disable_colors(void)
{
    char const *colorterm = getenv("COLORTERM");
    return !(colorterm && *colorterm) && !known_term_type();
}

static struct color_ext_type* allocate_extension(void)
{
    struct color_ext_type *ext = xmalloc(sizeof *ext);
    ext->next = color_ext_list;
    color_ext_list = ext;
    ext->exact_match = false;
    return ext;
}

static enum parse_state process_extension_definition(struct color_ext_type *ext, char **buf, char const **p)
{
    ext->ext.string = *buf;
    return get_funky_string(buf, p, true, &ext->ext.len) ? PS_4 : PS_FAIL;
}

static enum parse_state process_indicator_label(char label0, char label1, char **buf, char const **p)
{
    for (int i = 0; i < ARRAY_CARDINALITY(indicator_name); i++)
    {
        if (label0 == indicator_name[i][0] && label1 == indicator_name[i][1])
        {
            color_indicator[i].string = *buf;
            return get_funky_string(buf, p, false, &color_indicator[i].len) ? PS_START : PS_FAIL;
        }
    }
    error(0, 0, _("unrecognized prefix: %s"), quote((char []){label0, label1, '\0'}));
    return PS_FAIL;
}

static enum parse_state handle_start_state(char const **p, char **buf, struct color_ext_type **ext)
{
    switch (**p)
    {
    case ':':
        ++(*p);
        return PS_START;
    case '*':
        *ext = allocate_extension();
        ++(*p);
        return process_extension_definition(*ext, buf, p);
    case '\0':
        return PS_DONE;
    default:
        return PS_2;
    }
}

static void cleanup_on_failure(void)
{
    struct color_ext_type *e;
    struct color_ext_type *e2;
    
    error(0, 0, _("unparsable value for LS_COLORS environment variable"));
    free(color_buf);
    
    for (e = color_ext_list; e != nullptr;)
    {
        e2 = e;
        e = e->next;
        free(e2);
    }
    print_with_color = false;
}

static bool extensions_match_exact(struct color_ext_type *e1, struct color_ext_type *e2)
{
    return e2->ext.len < SIZE_MAX && 
           e1->ext.len == e2->ext.len && 
           memcmp(e1->ext.string, e2->ext.string, e1->ext.len) == 0;
}

static bool extensions_match_case_insensitive(struct color_ext_type *e1, struct color_ext_type *e2)
{
    return e2->ext.len < SIZE_MAX && 
           e1->ext.len == e2->ext.len && 
           c_strncasecmp(e1->ext.string, e2->ext.string, e1->ext.len) == 0;
}

static bool sequences_are_identical(struct color_ext_type *e1, struct color_ext_type *e2)
{
    return e1->seq.len == e2->seq.len && 
           memcmp(e1->seq.string, e2->seq.string, e1->seq.len) == 0;
}

static void process_case_insensitive_match(struct color_ext_type *e1, struct color_ext_type *e2, bool *case_ignored)
{
    if (*case_ignored)
    {
        e2->ext.len = SIZE_MAX;
    }
    else if (sequences_are_identical(e1, e2))
    {
        e2->ext.len = SIZE_MAX;
        *case_ignored = true;
    }
    else
    {
        e1->exact_match = true;
        e2->exact_match = true;
    }
}

static void mark_duplicate_extensions(struct color_ext_type *e1)
{
    struct color_ext_type *e2;
    bool case_ignored = false;
    
    for (e2 = e1->next; e2 != nullptr; e2 = e2->next)
    {
        if (extensions_match_exact(e1, e2))
        {
            e2->ext.len = SIZE_MAX;
        }
        else if (extensions_match_case_insensitive(e1, e2))
        {
            process_case_insensitive_match(e1, e2, &case_ignored);
        }
    }
}

static void postprocess_extension_list(void)
{
    struct color_ext_type *e1;
    
    for (e1 = color_ext_list; e1 != nullptr; e1 = e1->next)
    {
        mark_duplicate_extensions(e1);
    }
}

static void check_symlink_color_setting(void)
{
    if (color_indicator[C_LINK].len == 6 && 
        !STRNCMP_LIT(color_indicator[C_LINK].string, "target"))
    {
        color_symlink_as_referent = true;
    }
}

static void parse_ls_color(void)
{
    char const *p;
    char *buf;
    char label0, label1;
    struct color_ext_type *ext;
    
    if ((p = getenv("LS_COLORS")) == nullptr || *p == '\0')
    {
        if (should_disable_colors())
            print_with_color = false;
        return;
    }
    
    ext = nullptr;
    buf = color_buf = xstrdup(p);
    
    enum parse_state state = PS_START;
    while (true)
    {
        switch (state)
        {
        case PS_START:
            label0 = *p++;
            state = handle_start_state(&p, &buf, &ext);
            break;
            
        case PS_2:
            if (*p)
            {
                label1 = *p++;
                state = PS_3;
            }
            else
            {
                state = PS_FAIL;
            }
            break;
            
        case PS_3:
            state = PS_FAIL;
            if (*(p++) == '=')
            {
                state = process_indicator_label(label0, label1, &buf, &p);
            }
            break;
            
        case PS_4:
            if (*(p++) == '=')
            {
                ext->seq.string = buf;
                state = get_funky_string(&buf, &p, false, &ext->seq.len) ? PS_START : PS_FAIL;
            }
            else
            {
                state = PS_FAIL;
            }
            break;
            
        case PS_FAIL:
            goto done;
            
        case PS_DONE:
            goto done;
            
        default:
            affirm(false);
        }
    }
    
done:
    if (state == PS_FAIL)
    {
        cleanup_on_failure();
    }
    else
    {
        postprocess_extension_list();
        check_symlink_color_setting();
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
    return;
  }
  
  if (exit_status == EXIT_SUCCESS)
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

static bool open_directory(DIR **dirp, const char *name, bool command_line_arg)
{
    errno = 0;
    *dirp = opendir(name);
    if (!*dirp)
    {
        file_failure(command_line_arg, _("cannot open directory %s"), name);
        return false;
    }
    return true;
}

static bool check_directory_loop(DIR *dirp, const char *name, bool command_line_arg)
{
    if (!LOOP_DETECT)
        return true;

    struct stat dir_stat;
    int fd = dirfd(dirp);

    if ((0 <= fd ? fstat_for_ino(fd, &dir_stat) : stat_for_ino(name, &dir_stat)) < 0)
    {
        file_failure(command_line_arg, _("cannot determine device and inode of %s"), name);
        closedir(dirp);
        return false;
    }

    if (visit_dir(dir_stat.st_dev, dir_stat.st_ino))
    {
        error(0, 0, _("%s: not listing already-listed directory"), quotef(name));
        closedir(dirp);
        set_exit_status(true);
        return false;
    }

    dev_ino_push(dir_stat.st_dev, dir_stat.st_ino);
    return true;
}

static void print_directory_header(const char *name, const char *realname, bool command_line_arg)
{
    static bool first = true;
    
    if (!recursive && !print_dir_name)
        return;

    if (!first)
        dired_outbyte('\n');
    first = false;
    dired_indent();

    char *absolute_name = nullptr;
    if (print_hyperlink)
    {
        absolute_name = canonicalize_filename_mode(name, CAN_MISSING);
        if (!absolute_name)
            file_failure(command_line_arg, _("error canonicalizing %s"), name);
    }
    
    quote_name(realname ? realname : name, dirname_quoting_options, -1,
               nullptr, true, &subdired_obstack, absolute_name);
    free(absolute_name);
    dired_outstring(":\n");
}

static bool should_print_immediately(void)
{
    return format == one_per_line && sort_type == sort_none &&
           !print_block_size && !recursive;
}

static void process_directory_entry(struct dirent *entry, const char *name, uintmax_t *total_blocks)
{
    if (file_ignored(entry->d_name))
        return;

    enum filetype type;
#if HAVE_STRUCT_DIRENT_D_TYPE
    type = d_type_filetype[entry->d_type];
#else
    type = unknown;
#endif
    
    *total_blocks += gobble_file(entry->d_name, type, RELIABLE_D_INO(entry), false, name);

    if (should_print_immediately())
    {
        sort_files();
        print_current_files();
        clear_files();
    }
}

static bool should_continue_reading(int err)
{
    if (err == 0)
        return false;
        
#if !(2 < __GLIBC__ + (3 <= __GLIBC_MINOR__))
    if (err == ENOENT)
        return false;
#endif
    
    return err == EOVERFLOW;
}

static uintmax_t read_directory_entries(DIR *dirp, const char *name, bool command_line_arg)
{
    uintmax_t total_blocks = 0;
    struct dirent *next;

    while (true)
    {
        errno = 0;
        next = readdir(dirp);
        
        if (next)
        {
            process_directory_entry(next, name, &total_blocks);
        }
        else
        {
            int err = errno;
            if (!should_continue_reading(err))
            {
                if (err != 0 && err != ENOENT)
                    file_failure(command_line_arg, _("reading directory %s"), name);
                break;
            }
            file_failure(command_line_arg, _("reading directory %s"), name);
        }
        
        process_signals();
    }
    
    return total_blocks;
}

static void print_total_blocks(uintmax_t total_blocks)
{
    if (!format == long_format && !print_block_size)
        return;

    char buf[LONGEST_HUMAN_READABLE + 3];
    char *p = human_readable(total_blocks, buf + 1, human_output_opts,
                            ST_NBLOCKSIZE, output_block_size);
    char *pend = p + strlen(p);
    *--p = ' ';
    *pend++ = eolbyte;
    dired_indent();
    dired_outstring(_("total"));
    dired_outbuf(p, pend - p);
}

static void print_dir(char const *name, char const *realname, bool command_line_arg)
{
    DIR *dirp;
    
    if (!open_directory(&dirp, name, command_line_arg))
        return;

    if (!check_directory_loop(dirp, name, command_line_arg))
        return;

    clear_files();
    print_directory_header(name, realname, command_line_arg);
    
    uintmax_t total_blocks = read_directory_entries(dirp, name, command_line_arg);

    if (closedir(dirp) != 0)
        file_failure(command_line_arg, _("closing directory %s"), name);

    sort_files();

    if (recursive)
        extract_dirs_from_files(name, false);

    print_total_blocks(total_blocks);

    if (cwd_n_used)
        print_current_files();
}

/* Add 'pattern' to the list of patterns for which files that match are
   not listed.  */

static void
add_ignore_pattern (char const *pattern)
{
  struct ignore_pattern *ignore = xmalloc (sizeof *ignore);
  ignore->pattern = pattern;
  ignore->next = ignore_patterns;
  ignore_patterns = ignore;
}

/* Return true if one of the PATTERNS matches FILE.  */

static bool
patterns_match (struct ignore_pattern const *patterns, char const *file)
{
  struct ignore_pattern const *p;
  for (p = patterns; p; p = p->next)
    if (fnmatch (p->pattern, file, FNM_PERIOD) == 0)
      return true;
  return false;
}

/* Return true if FILE should be ignored.  */

static bool is_dot_file(char const *name)
{
    return name[0] == '.';
}

static bool is_special_dot_file(char const *name)
{
    return name[1] == '\0' || (name[1] == '.' && name[2] == '\0');
}

static bool should_ignore_dot_file(char const *name)
{
    if (ignore_mode == IGNORE_MINIMAL) {
        return false;
    }
    
    if (!is_dot_file(name)) {
        return false;
    }
    
    if (ignore_mode == IGNORE_DEFAULT) {
        return true;
    }
    
    return !is_special_dot_file(name);
}

static bool should_apply_hide_patterns(char const *name)
{
    return ignore_mode == IGNORE_DEFAULT && patterns_match(hide_patterns, name);
}

static bool file_ignored(char const *name)
{
    if (should_ignore_dot_file(name)) {
        return true;
    }
    
    if (should_apply_hide_patterns(name)) {
        return true;
    }
    
    return patterns_match(ignore_patterns, name);
}

/* POSIX requires that a file size be printed without a sign, even
   when negative.  Assume the typical case where negative sizes are
   actually positive values that have wrapped around.  */

static uintmax_t
unsigned_file_size (off_t size)
{
  if (size < 0)
  {
    return size + ((uintmax_t) OFF_T_MAX - OFF_T_MIN + 1);
  }
  return size;
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
has_capability (MAYBE_UNUSED char const *name)
{
  errno = ENOTSUP;
  return false;
}
#endif

/* Enter and remove entries in the table 'cwd_file'.  */

static void
free_ent (struct fileinfo *f)
{
  free (f->name);
  free (f->linkname);
  free (f->absolute_name);
  if (f->scontext != UNKNOWN_SECURITY_CONTEXT)
    aclinfo_scontext_free (f->scontext);
}

/* Empty the table of files.  */
static void reset_width_counters(void)
{
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

static void reset_file_flags(void)
{
    cwd_n_used = 0;
    cwd_some_quoted = false;
    any_has_acl = false;
}

static void free_all_files(void)
{
    for (idx_t i = 0; i < cwd_n_used; i++)
    {
        struct fileinfo *f = sorted_file[i];
        free_ent(f);
    }
}

static void clear_files(void)
{
    free_all_files();
    reset_file_flags();
    reset_width_counters();
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

  if (is_cached_unsupported_device(f, unsupported_scontext, unsupported_device))
    {
      return setup_cached_unsupported_response(ai, unsupported_scontext, 
                                                unsupported_scontext_err, 
                                                unsupported_return);
    }

  errno = 0;
  int n = file_has_aclinfo (file, ai, flags);
  int err = errno;
  
  if (should_cache_as_unsupported(f, n, err, flags, ai->scontext_err))
    {
      cache_unsupported_device(n, ai->scontext, ai->scontext_err, 
                                f->stat.st_dev, &unsupported_return,
                                &unsupported_scontext, &unsupported_scontext_err,
                                &unsupported_device);
    }
  return n;
}

static int 
is_cached_unsupported_device(struct fileinfo *f, char *unsupported_scontext, 
                              dev_t unsupported_device)
{
  return f->stat_ok && unsupported_scontext && 
         f->stat.st_dev == unsupported_device;
}

static int 
setup_cached_unsupported_response(struct aclinfo *ai, char *unsupported_scontext,
                                   int unsupported_scontext_err, int unsupported_return)
{
  ai->buf = ai->u.__gl_acl_ch;
  ai->size = 0;
  ai->scontext = unsupported_scontext;
  ai->scontext_err = unsupported_scontext_err;
  errno = ENOTSUP;
  return unsupported_return;
}

static int 
should_cache_as_unsupported(struct fileinfo *f, int n, int err, 
                             int flags, int scontext_err)
{
  if (!f->stat_ok || n > 0)
    return 0;
  
  if (acl_errno_valid(err))
    return 0;
  
  if ((flags & ACL_GET_SCONTEXT) && acl_errno_valid(scontext_err))
    return 0;
  
  return 1;
}

static void 
cache_unsupported_device(int n, char *scontext, int scontext_err, 
                          dev_t device, int *unsupported_return,
                          char **unsupported_scontext, int *unsupported_scontext_err,
                          dev_t *unsupported_device)
{
  *unsupported_return = n;
  *unsupported_scontext = scontext;
  *unsupported_scontext_err = scontext_err;
  *unsupported_device = device;
}

/* Cache has_capability failure, when it's trivial to do.
   Like has_capability, but when F's st_dev says it's on a file
   system lacking capability support, return 0 with ENOTSUP immediately.  */
static bool is_unsupported_device(struct fileinfo *f, bool unsupported_cached, dev_t unsupported_device)
{
    return f->stat_ok && unsupported_cached && f->stat.st_dev == unsupported_device;
}

static void cache_unsupported_device(struct fileinfo *f, bool *unsupported_cached, dev_t *unsupported_device)
{
    if (f->stat_ok && !acl_errno_valid(errno))
    {
        *unsupported_cached = true;
        *unsupported_device = f->stat.st_dev;
    }
}

static bool
has_capability_cache (char const *file, struct fileinfo *f)
{
    static bool unsupported_cached;
    static dev_t unsupported_device;

    if (is_unsupported_device(f, unsupported_cached, unsupported_device))
    {
        errno = ENOTSUP;
        return 0;
    }

    bool b = has_capability(file);
    if (!b)
    {
        cache_unsupported_device(f, &unsupported_cached, &unsupported_device);
    }
    return b;
}

static bool needs_quoting(char const *name)
{
    char test[2];
    size_t len = quotearg_buffer(test, sizeof test, name, -1,
                                  filename_quoting_options);
    return *name != *test || strlen(name) != len;
}

/* Add a file to the current table of files.
   Verify that the file exists, and print an error message if it does not.
   Return the number of blocks that the file occupies.  */
static void initialize_fileinfo(struct fileinfo *f, ino_t inode, enum filetype type)
{
    memset(f, '\0', sizeof *f);
    f->stat.st_ino = inode;
    f->filetype = type;
    f->scontext = UNKNOWN_SECURITY_CONTEXT;
    f->quoted = -1;
}

static void update_quoted_status(struct fileinfo *f, char const *name)
{
    if ((! cwd_some_quoted) && align_variable_outer_quotes)
    {
        f->quoted = needs_quoting(name);
        if (f->quoted)
            cwd_some_quoted = 1;
    }
}

static bool needs_color_stat(enum filetype type)
{
    return (type == directory || type == unknown) && print_with_color
           && (is_colored(C_OTHER_WRITABLE)
               || is_colored(C_STICKY)
               || is_colored(C_STICKY_OTHER_WRITABLE));
}

static bool needs_symlink_stat(enum filetype type)
{
    return (print_inode || format_needs_type)
           && (type == symbolic_link || type == unknown)
           && (dereference == DEREF_ALWAYS
               || color_symlink_as_referent || check_symlink_mode);
}

static bool needs_executable_stat(enum filetype type)
{
    return (type == normal || type == unknown)
           && (indicator_style == classify
               || (print_with_color && (is_colored(C_EXEC)
                                        || is_colored(C_SETUID)
                                        || is_colored(C_SETGID))));
}

static bool should_check_stat(enum filetype type, bool command_line_arg, ino_t inode)
{
    return command_line_arg
           || print_hyperlink
           || format_needs_stat
           || (format_needs_type && type == unknown)
           || needs_color_stat(type)
           || needs_symlink_stat(type)
           || (print_inode && inode == NOT_AN_INODE_NUMBER)
           || needs_executable_stat(type);
}

static char const *build_full_path(char const *name, char const *dirname)
{
    if (name[0] != '/' && dirname)
    {
        char *p = alloca(strlen(name) + strlen(dirname) + 2);
        attach(p, dirname, name);
        return p;
    }
    return name;
}

static void handle_hyperlink(struct fileinfo *f, char const *full_name, bool command_line_arg)
{
    if (print_hyperlink)
    {
        f->absolute_name = canonicalize_filename_mode(full_name, CAN_MISSING);
        if (!f->absolute_name)
            file_failure(command_line_arg, _("error canonicalizing %s"), full_name);
    }
}

static int perform_stat_operation(char const *full_name, struct fileinfo *f,
                                 bool command_line_arg, bool *do_deref)
{
    int err;
    
    switch (dereference)
    {
    case DEREF_ALWAYS:
        err = do_stat(full_name, &f->stat);
        *do_deref = true;
        break;

    case DEREF_COMMAND_LINE_ARGUMENTS:
    case DEREF_COMMAND_LINE_SYMLINK_TO_DIR:
        if (command_line_arg)
        {
            err = do_stat(full_name, &f->stat);
            *do_deref = true;

            if (dereference == DEREF_COMMAND_LINE_ARGUMENTS)
                break;

            bool need_lstat = (err < 0
                              ? (errno == ENOENT || errno == ELOOP)
                              : !S_ISDIR(f->stat.st_mode));
            if (!need_lstat)
                break;
        }
        FALLTHROUGH;

    case DEREF_NEVER:
        err = do_lstat(full_name, &f->stat);
        *do_deref = false;
        break;

    case DEREF_UNDEFINED:
    default:
        unreachable();
    }
    
    return err;
}

static void process_acl_and_scontext(struct fileinfo *f, char const *full_name,
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
    int n = file_has_aclinfo_cache(full_name, f, &ai, aclinfo_flags);
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
        error(0, errno, "%s", quotef(full_name));
    else if (print_scontext && ai.scontext_err
             && (!(is_ENOTSUP(ai.scontext_err) || ai.scontext_err == ENODATA)))
        error(0, ai.scontext_err, "%s", quotef(full_name));

    if (check_capability && aclinfo_has_xattr(&ai, XATTR_NAME_CAPS))
        f->has_capability = has_capability_cache(full_name, f);

    f->scontext = ai.scontext;
    ai.scontext = nullptr;
    aclinfo_free(&ai);
}

static void process_symlink(struct fileinfo *f, char const *full_name, bool command_line_arg)
{
    struct stat linkstats;

    get_link_name(full_name, f, command_line_arg);

    if (f->linkname && f->quoted == 0 && needs_quoting(f->linkname))
        f->quoted = -1;

    if (f->linkname
        && (file_type <= indicator_style || check_symlink_mode)
        && stat_for_mode(full_name, &linkstats) == 0)
    {
        f->linkok = true;
        f->linkmode = linkstats.st_mode;
    }
}

static void update_width_field(int *width, int new_len)
{
    if (*width < new_len)
        *width = new_len;
}

static void update_block_size_width(uintmax_t blocks)
{
    char buf[LONGEST_HUMAN_READABLE + 1];
    int len = mbswidth(human_readable(blocks, buf, human_output_opts,
                                     ST_NBLOCKSIZE, output_block_size),
                      MBSWIDTH_FLAGS);
    update_width_field(&block_size_width, len);
}

static void update_user_group_widths(struct fileinfo *f)
{
    if (print_owner)
        update_width_field(&owner_width, format_user_width(f->stat.st_uid));

    if (print_group)
        update_width_field(&group_width, format_group_width(f->stat.st_gid));

    if (print_author)
        update_width_field(&author_width, format_user_width(f->stat.st_author));
}

static void update_device_widths(struct fileinfo *f)
{
    char buf[INT_BUFSIZE_BOUND(uintmax_t)];
    int len = strlen(umaxtostr(major(f->stat.st_rdev), buf));
    update_width_field(&major_device_number_width, len);
    
    len = strlen(umaxtostr(minor(f->stat.st_rdev), buf));
    update_width_field(&minor_device_number_width, len);
    
    len = major_device_number_width + 2 + minor_device_number_width;
    update_width_field(&file_size_width, len);
}

static void update_file_size_width(struct fileinfo *f)
{
    char buf[LONGEST_HUMAN_READABLE + 1];
    uintmax_t size = unsigned_file_size(f->stat.st_size);
    int len = mbswidth(human_readable(size, buf, file_human_output_opts,
                                     1, file_output_block_size),
                      MBSWIDTH_FLAGS);
    update_width_field(&file_size_width, len);
}

static void update_long_format_widths(struct fileinfo *f, enum filetype type)
{
    if (format != long_format)
        return;

    update_user_group_widths(f);

    char b[INT_BUFSIZE_BOUND(uintmax_t)];
    int b_len = strlen(umaxtostr(f->stat.st_nlink, b));
    update_width_field(&nlink_width, b_len);

    if ((type == chardev) | (type == blockdev))
        update_device_widths(f);
    else
        update_file_size_width(f);
}

static uintmax_t
gobble_file(char const *name, enum filetype type, ino_t inode,
           bool command_line_arg, char const *dirname)
{
    uintmax_t blocks = 0;
    struct fileinfo *f;

    affirm(!command_line_arg || inode == NOT_AN_INODE_NUMBER);

    if (cwd_n_used == cwd_n_alloc)
        cwd_file = xpalloc(cwd_file, &cwd_n_alloc, 1, -1, sizeof *cwd_file);

    f = &cwd_file[cwd_n_used];
    initialize_fileinfo(f, inode, type);
    update_quoted_status(f, name);

    bool check_stat = should_check_stat(type, command_line_arg, inode);
    
    char const *full_name = name;
    if (check_stat | print_scontext | format_needs_capability)
        full_name = build_full_path(name, dirname);

    bool do_deref = dereference == DEREF_ALWAYS;

    if (check_stat)
    {
        handle_hyperlink(f, full_name, command_line_arg);
        
        int err = perform_stat_operation(full_name, f, command_line_arg, &do_deref);

        if (err != 0)
        {
            file_failure(command_line_arg, _("cannot access %s"), full_name);

            if (command_line_arg)
                return 0;

            f->name = xstrdup(name);
            cwd_n_used++;
            return 0;
        }

        f->stat_ok = true;
        f->filetype = type = d_type_filetype[IFTODT(f->stat.st_mode)];
    }

    if (type == directory && command_line_arg && !immediate_dirs)
        f->filetype = type = arg_directory;

    process_acl_and_scontext(f, full_name, type, do_deref);

    if ((type == symbolic_link) & ((format == long_format) | check_symlink_mode))
        process_symlink(f, full_name, command_line_arg);

    blocks = STP_NBLOCKS(&f->stat);
    if (format == long_format || print_block_size)
        update_block_size_width(blocks);

    update_long_format_widths(f, type);

    if (print_scontext)
        update_width_field(&scontext_width, strlen(f->scontext));

    if (print_inode)
    {
        char buf[INT_BUFSIZE_BOUND(uintmax_t)];
        update_width_field(&inode_number_width, strlen(umaxtostr(f->stat.st_ino, buf)));
    }

    f->name = xstrdup(name);
    cwd_n_used++;

    return blocks;
}

/* Return true if F refers to a directory.  */
static bool
is_directory (const struct fileinfo *f)
{
  return f->filetype == directory || f->filetype == arg_directory;
}

/* Return true if F refers to a (symlinked) directory.  */
static bool
is_linked_directory (const struct fileinfo *f)
{
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
  char const *base = last_component (name);
  return dot_or_dotdot (base);
}

/* Remove any entries from CWD_FILE that are for directories,
   and queue them to be listed as directories instead.
   DIRNAME is the prefix to prepend to each dirname
   to make it correct relative to ls's working dir;
   if it is null, no prefix is needed and "." and ".." should not be ignored.
   If COMMAND_LINE_ARG is true, this directory was mentioned at the top level,
   This is desirable when processing directories recursively.  */

static bool should_queue_directory(struct fileinfo *f, bool ignore_dot_and_dot_dot)
{
    return is_directory(f) && 
           (!ignore_dot_and_dot_dot || !basename_is_dot_or_dotdot(f->name));
}

static void queue_file_directory(struct fileinfo *f, const char *dirname, bool command_line_arg)
{
    if (!dirname || f->name[0] == '/')
    {
        queue_directory(f->name, f->linkname, command_line_arg);
    }
    else
    {
        char *name = file_name_concat(dirname, f->name, nullptr);
        queue_directory(name, f->linkname, command_line_arg);
        free(name);
    }
}

static void queue_marker_if_needed(const char *dirname)
{
    if (dirname && LOOP_DETECT)
    {
        queue_directory(nullptr, dirname, false);
    }
}

static void queue_subdirectories(const char *dirname, bool command_line_arg)
{
    bool ignore_dot_and_dot_dot = (dirname != nullptr);
    
    for (idx_t i = cwd_n_used; 0 < i; )
    {
        i--;
        struct fileinfo *f = sorted_file[i];
        
        if (should_queue_directory(f, ignore_dot_and_dot_dot))
        {
            queue_file_directory(f, dirname, command_line_arg);
            
            if (f->filetype == arg_directory)
            {
                free_ent(f);
            }
        }
    }
}

static void compact_sorted_files(void)
{
    idx_t j = 0;
    
    for (idx_t i = 0; i < cwd_n_used; i++)
    {
        struct fileinfo *f = sorted_file[i];
        sorted_file[j] = f;
        j += (f->filetype != arg_directory);
    }
    
    cwd_n_used = j;
}

static void extract_dirs_from_files(char const *dirname, bool command_line_arg)
{
    queue_marker_if_needed(dirname);
    queue_subdirectories(dirname, command_line_arg);
    compact_sorted_files();
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
      longjmp (failed_strcoll, 1);
    }
  return diff;
}

/* Comparison routines for sorting the files.  */

typedef void const *V;
typedef int (*qsortFunc)(V a, V b);

/* Used below in DEFINE_SORT_FUNCTIONS for _df_ sort function variants.  */
static int
dirfirst_check (struct fileinfo const *a, struct fileinfo const *b,
                int (*cmp) (V, V))
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
  return diff ? diff : cmp (a->name, b->name);
}

static int
cmp_mtime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int diff = timespec_cmp (get_stat_mtime (&b->stat),
                           get_stat_mtime (&a->stat));
  return diff ? diff : cmp (a->name, b->name);
}

static int
cmp_atime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int diff = timespec_cmp (get_stat_atime (&b->stat),
                           get_stat_atime (&a->stat));
  return diff ? diff : cmp (a->name, b->name);
}

static int
cmp_btime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int diff = timespec_cmp (get_stat_btime (&b->stat),
                           get_stat_btime (&a->stat));
  return diff ? diff : cmp (a->name, b->name);
}

static int
off_cmp (off_t a, off_t b)
{
  return _GL_CMP (a, b);
}

static int
cmp_size (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  int diff = off_cmp (b->stat.st_size, a->stat.st_size);
  return diff ? diff : cmp (a->name, b->name);
}

static int cmp_name(struct fileinfo const *a, struct fileinfo const *b,
                    int (*cmp)(char const *, char const *))
{
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
  char const *ext1 = base1 ? base1 : "";
  char const *ext2 = base2 ? base2 : "";
  
  int diff = cmp (ext1, ext2);
  if (diff)
    return diff;
    
  return cmp (a->name, b->name);
}

/* Return the (cached) screen width,
   for the NAME associated with the passed fileinfo F.  */

static size_t
fileinfo_name_width (struct fileinfo const *f)
{
  if (f->width) {
    return f->width;
  }
  return quote_name_width (f->name, filename_quoting_options, f->quoted);
}

static int
cmp_width (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  int diff = fileinfo_name_width (a) - fileinfo_name_width (b);
  return diff ? diff : cmp (a->name, b->name);
}

#define DEFINE_SORT_FUNCTIONS(sort_type, compare_func) \
    static int compare_func(const void *a, const void *b); \
    \
    void sort_by_##sort_type(void *array, size_t count, size_t size) { \
        qsort(array, count, size, compare_func); \
    }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static int sort_##name##_ascending(const void *a, const void *b) \
{ \
    return cmp_func(a, b); \
} \
\
static int sort_##name##_descending(const void *a, const void *b) \
{ \
    return cmp_func(b, a); \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static int sort_##name##_ascending(const void *a, const void *b) \
{ \
    return cmp_func(a, b); \
} \
\
static int sort_##name##_descending(const void *a, const void *b) \
{ \
    return cmp_func(b, a); \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(field, compare_func) \
  void sort_by_##field(void *base, size_t num, size_t size) { \
    qsort(base, num, size, compare_func); \
  } \
  void stable_sort_by_##field(void *base, size_t num, size_t size) { \
    stable_sort(base, num, size, compare_func); \
  }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)static int cmp_ctime(struct fileinfo const *a, struct fileinfo const *b)
{
    return timespec_cmp(get_stat_ctime(&a->stat), get_stat_ctime(&b->stat));
}

static int sort_ctime(void const *a, void const *b)
{
    return cmp_ctime(a, b);
}

static int rev_sort_ctime(void const *a, void const *b)
{
    return -cmp_ctime(a, b);
}

static int xstrcoll_ctime(void const *a, void const *b)
{
    return cmp_ctime(a, b) ? cmp_ctime(a, b) : xstrcoll(((struct fileinfo const *)a)->name, ((struct fileinfo const *)b)->name);
}

static int rev_xstrcoll_ctime(void const *a, void const *b)
{
    return cmp_ctime(a, b) ? -cmp_ctime(a, b) : xstrcoll(((struct fileinfo const *)a)->name, ((struct fileinfo const *)b)->name);
}static int cmp_ctime(const void *a, const void *b) {
    const struct dirent *da = *(const struct dirent **)a;
    const struct dirent *db = *(const struct dirent **)b;
    
    if (da->d_ctime < db->d_ctime) return -1;
    if (da->d_ctime > db->d_ctime) return 1;
    return 0;
}

static void sort_by_ctime(struct dirent **entries, size_t count) {
    qsort(entries, count, sizeof(struct dirent *), cmp_ctime);
}

static void sort_by_ctime_reverse(struct dirent **entries, size_t count) {
    qsort(entries, count, sizeof(struct dirent *), cmp_ctime);
    
    size_t start = 0;
    size_t end = count - 1;
    
    while (start < end) {
        struct dirent *temp = entries[start];
        entries[start] = entries[end];
        entries[end] = temp;
        start++;
        end--;
    }
}#define DEFINE_SORT_FUNCTIONS(field_name, cmp_func) \
static void sort_by_##field_name(void) { \
    perform_sort(cmp_func); \
} \
\
static void reverse_sort_by_##field_name(void) { \
    perform_reverse_sort(cmp_func); \
}

static void perform_sort(int (*cmp_func)(const void *, const void *)) {
    qsort(entries, entry_count, sizeof(void *), cmp_func);
}

static void perform_reverse_sort(int (*cmp_func)(const void *, const void *)) {
    qsort(entries, entry_count, sizeof(void *), cmp_func);
    reverse_entries();
}

static void reverse_entries(void) {
    size_t start = 0;
    size_t end = entry_count - 1;
    
    while (start < end) {
        void *temp = entries[start];
        entries[start] = entries[end];
        entries[end] = temp;
        start++;
        end--;
    }
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
  void sort_by_##field(void) { \
    qsort(files, files_index, sizeof(struct fileinfo), cmp_func); \
  }

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)
#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        qsort(base, nmemb, size, cmp_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t nmemb, size_t size) { \
        stable_sort(base, nmemb, size, cmp_func); \
    } \
    \
    void partial_sort_##name(void *base, size_t nmemb, size_t k, size_t size) { \
        partial_sort(base, nmemb, k, size, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    static int sort_##name##_ascending(const void *a, const void *b) { \
        return cmp_func(a, b); \
    } \
    \
    static int sort_##name##_descending(const void *a, const void *b) { \
        return cmp_func(b, a); \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static int compare_##name(const void *a, const void *b) { \
        return compare_func(*(const void **)a, *(const void **)b); \
    } \
    \
    void sort_by_##name(void **array, size_t count) { \
        if (array != NULL && count > 0) { \
            qsort(array, count, sizeof(void *), compare_##name); \
        } \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static int sort_##name(const void *a, const void *b) \
{ \
    return cmp_func(*(const void **)a, *(const void **)b); \
} \
\
static int sort_##name##_reverse(const void *a, const void *b) \
{ \
    return -cmp_func(*(const void **)a, *(const void **)b); \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
static int sort_##name##_ascending(const void *a, const void *b) \
{ \
    return compare_func(a, b); \
} \
\
static int sort_##name##_descending(const void *a, const void *b) \
{ \
    return compare_func(b, a); \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static void sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, compare_func); \
    } \
    \
    static void stable_sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, compare_func); \
    } \
    \
    static int reverse_##name(const void *a, const void *b) { \
        return -compare_func(a, b); \
    } \
    \
    static void sort_reverse_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, reverse_##name); \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    static int sort_##name##_ascending(const void *a, const void *b) { \
        return cmp_func(a, b); \
    } \
    \
    static int sort_##name##_descending(const void *a, const void *b) { \
        return cmp_func(b, a); \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)
#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static int sort_##name##_ascending(const void *a, const void *b) { \
        return compare_func(a, b); \
    } \
    static int sort_##name##_descending(const void *a, const void *b) { \
        return compare_func(b, a); \
    }

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static int sort_##name##_ascending(const void *a, const void *b) { \
        return compare_func(a, b); \
    } \
    \
    static int sort_##name##_descending(const void *a, const void *b) { \
        return compare_func(b, a); \
    }

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static int sort_##name##_ascending(const void *a, const void *b) { \
        return compare_func(a, b); \
    } \
    \
    static int sort_##name##_descending(const void *a, const void *b) { \
        return compare_func(b, a); \
    }

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(sort_name, compare_func) \
static void sort_##sort_name(void *base, size_t n, size_t size) { \
    qsort(base, n, size, compare_func); \
} \
\
static void* search_##sort_name(const void *key, const void *base, size_t n, size_t size) { \
    return bsearch(key, base, n, size, compare_func); \
}

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)static int cmp_atime(const void *a, const void *b) {
    return ((struct file_info *)a)->atime - ((struct file_info *)b)->atime;
}

static void swap_atime(void *a, void *b) {
    struct file_info temp = *(struct file_info *)a;
    *(struct file_info *)a = *(struct file_info *)b;
    *(struct file_info *)b = temp;
}

static void sort_atime(void *base, size_t nmemb, size_t size) {
    for (size_t i = 0; i < nmemb - 1; i++) {
        for (size_t j = 0; j < nmemb - i - 1; j++) {
            void *elem1 = (char *)base + j * size;
            void *elem2 = (char *)base + (j + 1) * size;
            if (cmp_atime(elem1, elem2) > 0) {
                swap_atime(elem1, elem2);
            }
        }
    }
}static int cmp_atime(const void *a, const void *b) {
    return compare_time_fields(a, b, offsetof(struct file_info, atime));
}

static void sort_by_atime(struct file_info *files, size_t count) {
    qsort(files, count, sizeof(struct file_info), cmp_atime);
}

static struct file_info* sorted_copy_by_atime(const struct file_info *files, size_t count) {
    struct file_info *sorted = malloc(count * sizeof(struct file_info));
    if (sorted) {
        memcpy(sorted, files, count * sizeof(struct file_info));
        sort_by_atime(sorted, count);
    }
    return sorted;
}DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static void sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, compare_func); \
    } \
    \
    static void stable_sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, compare_func); \
    } \
    \
    static int is_sorted_##name(const void *base, size_t n, size_t size) { \
        const char *arr = (const char *)base; \
        for (size_t i = 1; i < n; i++) { \
            if (compare_func(arr + (i - 1) * size, arr + i * size) > 0) { \
                return 0; \
            } \
        } \
        return 1; \
    }

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)
#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        qsort(base, nmemb, size, cmp_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t nmemb, size_t size) { \
        stable_sort(base, nmemb, size, cmp_func); \
    } \
    \
    void* bsearch_##name(const void *key, const void *base, size_t nmemb, size_t size) { \
        return bsearch(key, base, nmemb, size, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, cmp_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t n, size_t size) { \
        merge_sort(base, n, size, cmp_func); \
    } \
    \
    void partial_sort_##name(void *base, size_t n, size_t k, size_t size) { \
        heap_sort_partial(base, n, k, size, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, cmp_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t n, size_t size) { \
        qsort(base, n, size, cmp_func); \
    } \
    \
    void partial_sort_##name(void *base, size_t n, size_t k, size_t size) { \
        if (k > n) k = n; \
        for (size_t i = 0; i < k; i++) { \
            size_t min_idx = i; \
            for (size_t j = i + 1; j < n; j++) { \
                if (cmp_func((char*)base + j * size, (char*)base + min_idx * size) < 0) { \
                    min_idx = j; \
                } \
            } \
            if (min_idx != i) { \
                swap_elements((char*)base + i * size, (char*)base + min_idx * size, size); \
            } \
        } \
    } \
    \
    static void swap_elements(void *a, void *b, size_t size) { \
        char temp[size]; \
        memcpy(temp, a, size); \
        memcpy(a, b, size); \
        memcpy(b, temp, size); \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        qsort(base, nmemb, size, cmp_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t nmemb, size_t size) { \
        stable_sort(base, nmemb, size, cmp_func); \
    } \
    \
    void partial_sort_##name(void *base, size_t nmemb, size_t size, size_t n) { \
        partial_sort(base, nmemb, size, n, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    void sort_##name(void *array, size_t count, size_t size) { \
        qsort(array, count, size, compare_func); \
    } \
    \
    void *find_##name(const void *key, const void *array, size_t count, size_t size) { \
        return bsearch(key, array, count, size, compare_func); \
    } \
    \
    int is_sorted_##name(const void *array, size_t count, size_t size) { \
        const char *arr = (const char *)array; \
        for (size_t i = 1; i < count; i++) { \
            if (compare_func(arr + (i - 1) * size, arr + i * size) > 0) { \
                return 0; \
            } \
        } \
        return 1; \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        qsort(base, nmemb, size, cmp_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t nmemb, size_t size) { \
        merge_sort(base, nmemb, size, cmp_func); \
    } \
    \
    void* bsearch_##name(const void *key, const void *base, size_t nmemb, size_t size) { \
        return bsearch(key, base, nmemb, size, cmp_func); \
    } \
    \
    int is_sorted_##name(const void *base, size_t nmemb, size_t size) { \
        return is_array_sorted(base, nmemb, size, cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        qsort(base, nmemb, size, compare_func); \
    } \
    \
    void stable_sort_##name(void *base, size_t nmemb, size_t size) { \
        stable_sort_impl(base, nmemb, size, compare_func); \
    } \
    \
    void* bsearch_##name(const void *key, const void *base, size_t nmemb, size_t size) { \
        return bsearch(key, base, nmemb, size, compare_func); \
    }

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)DEFINE_SORT_FUNCTIONS (btime, cmp_btime)
#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static void swap_##name(void *a, void *b, size_t size) { \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    char temp; \
    while (size > 0) { \
        temp = *pa; \
        *pa = *pb; \
        *pb = temp; \
        pa++; \
        pb++; \
        size--; \
    } \
} \
\
static void sort_##name(void *base, size_t num, size_t size) { \
    char *arr = (char *)base; \
    for (size_t i = 0; i < num - 1; i++) { \
        for (size_t j = 0; j < num - i - 1; j++) { \
            if (cmp_func(arr + j * size, arr + (j + 1) * size) > 0) { \
                swap_##name(arr + j * size, arr + (j + 1) * size, size); \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define COMPARE_FUNC(name) cmp_##name
#define SORT_FUNC(name) sort_by_##name
#define SWAP_FUNC(name) swap_##name##_elements

#define DEFINE_SWAP_FUNCTION(type) \
static void SWAP_FUNC(type)(void* a, void* b) { \
    void* temp = a; \
    a = b; \
    b = temp; \
}

#define DEFINE_COMPARISON_FUNCTION(type) \
static int COMPARE_FUNC(type)(const void* a, const void* b) { \
    return cmp_size(a, b); \
}

#define DEFINE_SORT_IMPLEMENTATION(type) \
static void SORT_FUNC(type)(void* array, size_t count) { \
    qsort(array, count, sizeof(void*), COMPARE_FUNC(type)); \
}

#define DEFINE_SORT_FUNCTIONS(type, comparison) \
    DEFINE_SWAP_FUNCTION(type) \
    DEFINE_COMPARISON_FUNCTION(type) \
    DEFINE_SORT_IMPLEMENTATION(type)

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
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
static void sort_##name##_heapify(void *base, size_t n, size_t i, size_t size) \
{ \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < n && cmp_func(arr + left * size, arr + largest * size) > 0) \
        largest = left; \
    \
    if (right < n && cmp_func(arr + right * size, arr + largest * size) > 0) \
        largest = right; \
    \
    if (largest != i) { \
        sort_##name##_swap(arr + i * size, arr + largest * size, size); \
        sort_##name##_heapify(base, n, largest, size); \
    } \
} \
\
void sort_##name(void *base, size_t nmemb, size_t size) \
{ \
    if (nmemb <= 1) \
        return; \
    \
    char *arr = (char *)base; \
    size_t i; \
    \
    for (i = nmemb / 2; i > 0; i--) \
        sort_##name##_heapify(base, nmemb, i - 1, size); \
    \
    for (i = nmemb - 1; i > 0; i--) { \
        sort_##name##_swap(arr, arr + i * size, size); \
        sort_##name##_heapify(base, i, 0, size); \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static void swap_##field(void *a, void *b) \
{ \
    struct entry *entry_a = (struct entry *)a; \
    struct entry *entry_b = (struct entry *)b; \
    struct entry temp = *entry_a; \
    *entry_a = *entry_b; \
    *entry_b = temp; \
} \
\
static int partition_##field(void *arr, int low, int high) \
{ \
    struct entry *entries = (struct entry *)arr; \
    struct entry *pivot = &entries[high]; \
    int i = low - 1; \
    \
    for (int j = low; j < high; j++) { \
        if (cmp_func(&entries[j], pivot) <= 0) { \
            i++; \
            swap_##field(&entries[i], &entries[j]); \
        } \
    } \
    swap_##field(&entries[i + 1], &entries[high]); \
    return i + 1; \
} \
\
static void quicksort_##field(void *arr, int low, int high) \
{ \
    if (low < high) { \
        int pi = partition_##field(arr, low, high); \
        quicksort_##field(arr, low, pi - 1); \
        quicksort_##field(arr, pi + 1, high); \
    } \
} \
\
void sort_by_##field(void *arr, int count) \
{ \
    if (count > 1) { \
        quicksort_##field(arr, 0, count - 1); \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static void swap_##field(void *a, void *b) \
{ \
    void *temp = *(void **)a; \
    *(void **)a = *(void **)b; \
    *(void **)b = temp; \
} \
\
static void sort_##field(void *base, size_t nmemb) \
{ \
    for (size_t i = 0; i < nmemb - 1; i++) { \
        for (size_t j = 0; j < nmemb - i - 1; j++) { \
            void **elem1 = (void **)base + j; \
            void **elem2 = (void **)base + j + 1; \
            if (cmp_func(*elem1, *elem2) > 0) { \
                swap_##field(elem1, elem2); \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
void swap_##field(void *a, void *b) { \
    void *temp = *(void **)a; \
    *(void **)a = *(void **)b; \
    *(void **)b = temp; \
} \
\
void sort_##field(void **array, size_t count) { \
    if (count <= 1) return; \
    \
    for (size_t i = 0; i < count - 1; i++) { \
        size_t min_idx = find_min_##field(array, i, count); \
        if (min_idx != i) { \
            swap_##field(&array[i], &array[min_idx]); \
        } \
    } \
} \
\
size_t find_min_##field(void **array, size_t start, size_t count) { \
    size_t min_idx = start; \
    for (size_t j = start + 1; j < count; j++) { \
        if (cmp_func(array[j], array[min_idx]) < 0) { \
            min_idx = j; \
        } \
    } \
    return min_idx; \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static void swap_##field(void *a, void *b) { \
    void *temp = *(void **)a; \
    *(void **)a = *(void **)b; \
    *(void **)b = temp; \
} \
\
static int partition_##field(void **arr, int low, int high) { \
    void *pivot = arr[high]; \
    int i = low - 1; \
    \
    for (int j = low; j < high; j++) { \
        if (cmp_func(arr[j], pivot) <= 0) { \
            i++; \
            swap_##field(&arr[i], &arr[j]); \
        } \
    } \
    swap_##field(&arr[i + 1], &arr[high]); \
    return i + 1; \
} \
\
static void quicksort_##field(void **arr, int low, int high) { \
    if (low < high) { \
        int pi = partition_##field(arr, low, high); \
        quicksort_##field(arr, low, pi - 1); \
        quicksort_##field(arr, pi + 1, high); \
    } \
} \
\
void sort_by_##field(void **arr, int count) { \
    if (arr != NULL && count > 1) { \
        quicksort_##field(arr, 0, count - 1); \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(name, compare_func) \
    static void swap_##name(void *a, void *b, size_t element_size) { \
        char temp[element_size]; \
        memcpy(temp, a, element_size); \
        memcpy(a, b, element_size); \
        memcpy(b, temp, element_size); \
    } \
    \
    static void bubble_sort_##name(void *array, size_t count, size_t element_size) { \
        for (size_t i = 0; i < count - 1; i++) { \
            for (size_t j = 0; j < count - i - 1; j++) { \
                void *elem1 = (char*)array + j * element_size; \
                void *elem2 = (char*)array + (j + 1) * element_size; \
                if (compare_func(elem1, elem2) > 0) { \
                    swap_##name(elem1, elem2, element_size); \
                } \
            } \
        } \
    } \
    \
    static void quick_sort_##name(void *array, size_t count, size_t element_size) { \
        if (count <= 1) return; \
        \
        size_t pivot = count / 2; \
        void *pivot_elem = (char*)array + pivot * element_size; \
        size_t i = 0, j = count - 1; \
        \
        while (i <= j) { \
            while (i < count && compare_func((char*)array + i * element_size, pivot_elem) < 0) i++; \
            while (j > 0 && compare_func((char*)array + j * element_size, pivot_elem) > 0) j--; \
            \
            if (i <= j) { \
                swap_##name((char*)array + i * element_size, (char*)array + j * element_size, element_size); \
                i++; \
                if (j > 0) j--; \
            } \
        } \
        \
        if (j > 0) quick_sort_##name(array, j + 1, element_size); \
        if (i < count) quick_sort_##name((char*)array + i * element_size, count - i, element_size); \
    }

DEFINE_SORT_FUNCTIONS(size, cmp_size)
#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void swap_##name(void *a, void *b, int size) { \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    char temp; \
    while (size > 0) { \
        temp = *pa; \
        *pa = *pb; \
        *pb = temp; \
        pa++; \
        pb++; \
        size--; \
    } \
} \
\
static void heapify_##name(void *base, size_t n, size_t i, size_t size) { \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < n && cmp_name(arr + left * size, arr + largest * size) > 0) \
        largest = left; \
    \
    if (right < n && cmp_name(arr + right * size, arr + largest * size) > 0) \
        largest = right; \
    \
    if (largest != i) { \
        swap_##name(arr + i * size, arr + largest * size, size); \
        heapify_##name(base, n, largest, size); \
    } \
} \
\
static void sort_##name(void *base, size_t n, size_t size) { \
    char *arr = (char *)base; \
    \
    for (int i = n / 2 - 1; i >= 0; i--) \
        heapify_##name(base, n, i, size); \
    \
    for (int i = n - 1; i > 0; i--) { \
        swap_##name(arr, arr + i * size, size); \
        heapify_##name(base, i, 0, size); \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void swap_##name(void *a, void *b, size_t size) { \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    char temp; \
    size_t i; \
    for (i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void heapify_##name(void *base, size_t n, size_t i, size_t size, \
                           int (*cmp)(const void *, const void *)) { \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < n && cmp(arr + left * size, arr + largest * size) > 0) \
        largest = left; \
    \
    if (right < n && cmp(arr + right * size, arr + largest * size) > 0) \
        largest = right; \
    \
    if (largest != i) { \
        swap_##name(arr + i * size, arr + largest * size, size); \
        heapify_##name(base, n, largest, size, cmp); \
    } \
} \
\
void sort_##name(void *base, size_t n, size_t size) { \
    size_t i; \
    char *arr = (char *)base; \
    \
    for (i = n / 2; i > 0; i--) { \
        heapify_##name(base, n, i - 1, size, cmp_name); \
    } \
    \
    for (i = n - 1; i > 0; i--) { \
        swap_##name(arr, arr + i * size, size); \
        heapify_##name(base, i, 0, size, cmp_name); \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static int cmp_name##_wrapper(const void *a, const void *b) { \
    return cmp_name(*(const typeof(*name) *)a, *(const typeof(*name) *)b); \
} \
\
static void name##_sort(typeof(*name) *array, size_t count) { \
    qsort(array, count, sizeof(*array), cmp_name##_wrapper); \
} \
\
static typeof(*name) *name##_bsearch(const typeof(*name) *key, \
                                      const typeof(*name) *array, \
                                      size_t count) { \
    return bsearch(key, array, count, sizeof(*array), cmp_name##_wrapper); \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static int cmp_name(const void *a, const void *b); \
\
static void swap_##name(void *a, void *b, size_t size) { \
    unsigned char *pa = (unsigned char *)a; \
    unsigned char *pb = (unsigned char *)b; \
    unsigned char temp; \
    \
    while (size > 0) { \
        temp = *pa; \
        *pa = *pb; \
        *pb = temp; \
        pa++; \
        pb++; \
        size--; \
    } \
} \
\
static void *partition_##name(void *base, size_t nmemb, size_t size) { \
    char *pivot = (char *)base + (nmemb - 1) * size; \
    char *i = (char *)base - size; \
    char *j; \
    \
    for (j = (char *)base; j < pivot; j += size) { \
        if (cmp_name(j, pivot) <= 0) { \
            i += size; \
            swap_##name(i, j, size); \
        } \
    } \
    \
    i += size; \
    swap_##name(i, pivot, size); \
    return i; \
} \
\
static void quicksort_##name(void *base, size_t nmemb, size_t size) { \
    if (nmemb <= 1) { \
        return; \
    } \
    \
    char *pivot = (char *)partition_##name(base, nmemb, size); \
    size_t left_count = (pivot - (char *)base) / size; \
    size_t right_count = nmemb - left_count - 1; \
    \
    quicksort_##name(base, left_count, size); \
    quicksort_##name(pivot + size, right_count, size); \
} \
\
static void sort_##name(void *base, size_t nmemb, size_t size) { \
    quicksort_##name(base, nmemb, size); \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void swap_##name(void *a, void *b, size_t size) { \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    char temp; \
    while (size > 0) { \
        temp = *pa; \
        *pa = *pb; \
        *pb = temp; \
        pa++; \
        pb++; \
        size--; \
    } \
} \
\
static void heapify_##name(void *base, size_t nmemb, size_t size, size_t i) { \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < nmemb && cmp_name(arr + left * size, arr + largest * size) > 0) { \
        largest = left; \
    } \
    \
    if (right < nmemb && cmp_name(arr + right * size, arr + largest * size) > 0) { \
        largest = right; \
    } \
    \
    if (largest != i) { \
        swap_##name(arr + i * size, arr + largest * size, size); \
        heapify_##name(base, nmemb, size, largest); \
    } \
} \
\
static void build_heap_##name(void *base, size_t nmemb, size_t size) { \
    if (nmemb == 0) return; \
    for (size_t i = nmemb / 2; i > 0; i--) { \
        heapify_##name(base, nmemb, size, i - 1); \
    } \
} \
\
void sort_##name(void *base, size_t nmemb, size_t size) { \
    if (nmemb <= 1) return; \
    \
    char *arr = (char *)base; \
    build_heap_##name(base, nmemb, size); \
    \
    for (size_t i = nmemb - 1; i > 0; i--) { \
        swap_##name(arr, arr + i * size, size); \
        heapify_##name(base, i, size, 0); \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void swap_##name(void *a, void *b, int size) { \
    char temp; \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    for (int i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void heapify_##name(void *base, size_t n, size_t i, size_t size) { \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < n && cmp_name(arr + left * size, arr + largest * size) > 0) { \
        largest = left; \
    } \
    \
    if (right < n && cmp_name(arr + right * size, arr + largest * size) > 0) { \
        largest = right; \
    } \
    \
    if (largest != i) { \
        swap_##name(arr + i * size, arr + largest * size, size); \
        heapify_##name(base, n, largest, size); \
    } \
} \
\
static void build_heap_##name(void *base, size_t n, size_t size) { \
    for (int i = n / 2 - 1; i >= 0; i--) { \
        heapify_##name(base, n, i, size); \
    } \
} \
\
void sort_##name(void *base, size_t n, size_t size) { \
    build_heap_##name(base, n, size); \
    char *arr = (char *)base; \
    \
    for (size_t i = n - 1; i > 0; i--) { \
        swap_##name(arr, arr + i * size, size); \
        heapify_##name(base, i, 0, size); \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void name##_swap(void *a, void *b, size_t size) { \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    char temp; \
    size_t i; \
    for (i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void name##_heapify(void *base, size_t nmemb, size_t size, \
                           size_t root, int (*cmp)(const void *, const void *)) { \
    size_t largest = root; \
    size_t left = 2 * root + 1; \
    size_t right = 2 * root + 2; \
    char *arr = (char *)base; \
    \
    if (left < nmemb && cmp(arr + left * size, arr + largest * size) > 0) \
        largest = left; \
    \
    if (right < nmemb && cmp(arr + right * size, arr + largest * size) > 0) \
        largest = right; \
    \
    if (largest != root) { \
        name##_swap(arr + root * size, arr + largest * size, size); \
        name##_heapify(base, nmemb, size, largest, cmp); \
    } \
} \
\
static void name##_build_heap(void *base, size_t nmemb, size_t size, \
                              int (*cmp)(const void *, const void *)) { \
    if (nmemb <= 1) return; \
    size_t i; \
    for (i = nmemb / 2; i > 0; i--) { \
        name##_heapify(base, nmemb, size, i - 1, cmp); \
    } \
} \
\
void name##_sort(void *base, size_t nmemb, size_t size) { \
    if (nmemb <= 1) return; \
    \
    name##_build_heap(base, nmemb, size, cmp_name); \
    \
    size_t i; \
    for (i = nmemb - 1; i > 0; i--) { \
        name##_swap(base, (char *)base + i * size, size); \
        name##_heapify(base, i, size, 0, cmp_name); \
    } \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static void swap_##name(void *a, void *b, size_t size) { \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    char tmp; \
    for (size_t i = 0; i < size; i++) { \
        tmp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = tmp; \
    } \
} \
\
static void *find_min_##name(void *start, size_t n, size_t size, \
                             int (*cmp)(const void *, const void *)) { \
    void *min = start; \
    char *current = (char *)start; \
    for (size_t i = 1; i < n; i++) { \
        current += size; \
        if (cmp(current, min) < 0) { \
            min = current; \
        } \
    } \
    return min; \
} \
\
static void heapify_##name(void *base, size_t size, size_t n, size_t i, \
                           int (*cmp)(const void *, const void *)) { \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < n && cmp(arr + left * size, arr + largest * size) > 0) { \
        largest = left; \
    } \
    \
    if (right < n && cmp(arr + right * size, arr + largest * size) > 0) { \
        largest = right; \
    } \
    \
    if (largest != i) { \
        swap_##name(arr + i * size, arr + largest * size, size); \
        heapify_##name(base, size, n, largest, cmp); \
    } \
} \
\
static void build_heap_##name(void *base, size_t size, size_t n, \
                              int (*cmp)(const void *, const void *)) { \
    for (int i = n / 2 - 1; i >= 0; i--) { \
        heapify_##name(base, size, n, i, cmp); \
    } \
} \
\
void sort_##name(void *base, size_t n, size_t size) { \
    if (n <= 1) return; \
    \
    build_heap_##name(base, size, n, cmp_name); \
    \
    char *arr = (char *)base; \
    for (size_t i = n - 1; i > 0; i--) { \
        swap_##name(arr, arr + i * size, size); \
        heapify_##name(base, size, i, 0, cmp_name); \
    } \
}
#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void swap_##name(void *a, void *b, size_t size) { \
        char *pa = (char *)a; \
        char *pb = (char *)b; \
        for (size_t i = 0; i < size; i++) { \
            char temp = pa[i]; \
            pa[i] = pb[i]; \
            pb[i] = temp; \
        } \
    } \
    \
    void sort_##name(void *base, size_t num, size_t size) { \
        char *arr = (char *)base; \
        for (size_t i = 0; i < num - 1; i++) { \
            for (size_t j = 0; j < num - i - 1; j++) { \
                if (cmp_func(arr + j * size, arr + (j + 1) * size) > 0) { \
                    swap_##name(arr + j * size, arr + (j + 1) * size, size); \
                } \
            } \
        } \
    }

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)#define SWAP(a, b) do { \
    typeof(a) temp = (a); \
    (a) = (b); \
    (b) = temp; \
} while(0)

static void heapify_extension(void *base, size_t nmemb, size_t size, 
                              size_t parent, int (*cmp)(const void *, const void *)) {
    size_t largest = parent;
    size_t left = 2 * parent + 1;
    size_t right = 2 * parent + 2;
    
    char *arr = (char *)base;
    
    if (left < nmemb && cmp(arr + left * size, arr + largest * size) > 0) {
        largest = left;
    }
    
    if (right < nmemb && cmp(arr + right * size, arr + largest * size) > 0) {
        largest = right;
    }
    
    if (largest != parent) {
        for (size_t i = 0; i < size; i++) {
            SWAP(arr[parent * size + i], arr[largest * size + i]);
        }
        heapify_extension(base, nmemb, size, largest, cmp);
    }
}

static void build_heap_extension(void *base, size_t nmemb, size_t size,
                                 int (*cmp)(const void *, const void *)) {
    if (nmemb <= 1) return;
    
    for (ssize_t i = nmemb / 2 - 1; i >= 0; i--) {
        heapify_extension(base, nmemb, size, i, cmp);
    }
}

void sort_extension(void *base, size_t nmemb, size_t size) {
    if (nmemb <= 1) return;
    
    build_heap_extension(base, nmemb, size, cmp_extension);
    
    char *arr = (char *)base;
    
    for (size_t i = nmemb - 1; i > 0; i--) {
        for (size_t j = 0; j < size; j++) {
            SWAP(arr[j], arr[i * size + j]);
        }
        heapify_extension(base, i, size, 0, cmp_extension);
    }
}#define SWAP(a, b, type) do { type temp = (a); (a) = (b); (b) = temp; } while(0)

#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static void sort_##name##_swap(void *a, void *b, size_t size) \
{ \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    while (size > 0) { \
        SWAP(*pa, *pb, char); \
        pa++; \
        pb++; \
        size--; \
    } \
} \
\
static void sort_##name##_heapify(void *base, size_t n, size_t i, size_t size, \
                                   int (*cmp)(const void *, const void *)) \
{ \
    size_t largest = i; \
    size_t left = 2 * i + 1; \
    size_t right = 2 * i + 2; \
    char *arr = (char *)base; \
    \
    if (left < n && cmp(arr + left * size, arr + largest * size) > 0) \
        largest = left; \
    \
    if (right < n && cmp(arr + right * size, arr + largest * size) > 0) \
        largest = right; \
    \
    if (largest != i) { \
        sort_##name##_swap(arr + i * size, arr + largest * size, size); \
        sort_##name##_heapify(base, n, largest, size, cmp); \
    } \
} \
\
void sort_##name(void *base, size_t n, size_t size) \
{ \
    char *arr = (char *)base; \
    \
    for (int i = n / 2 - 1; i >= 0; i--) \
        sort_##name##_heapify(base, n, i, size, cmp_func); \
    \
    for (int i = n - 1; i > 0; i--) { \
        sort_##name##_swap(arr, arr + i * size, size); \
        sort_##name##_heapify(base, i, 0, size, cmp_func); \
    } \
}

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)DEFINE_SORT_FUNCTIONS(extension, cmp_extension)static void swap_extension(void *a, void *b, int size)
{
    char temp[size];
    memcpy(temp, a, size);
    memcpy(a, b, size);
    memcpy(b, temp, size);
}

static void sort_extension(void *base, size_t nmemb, size_t size)
{
    char *arr = (char *)base;
    for (size_t i = 0; i < nmemb - 1; i++) {
        for (size_t j = 0; j < nmemb - i - 1; j++) {
            if (cmp_extension(arr + j * size, arr + (j + 1) * size) > 0) {
                swap_extension(arr + j * size, arr + (j + 1) * size, size);
            }
        }
    }
}

static void qsort_extension(void *base, size_t nmemb, size_t size)
{
    qsort(base, nmemb, size, cmp_extension);
}#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static void swap_##name(void *a, void *b, size_t size) { \
    unsigned char *pa = a; \
    unsigned char *pb = b; \
    unsigned char temp; \
    size_t i; \
    for (i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void sort_##name(void *base, size_t num, size_t size) { \
    char *arr = base; \
    size_t i, j; \
    for (i = 0; i < num - 1; i++) { \
        for (j = 0; j < num - i - 1; j++) { \
            if (cmp_func(arr + j * size, arr + (j + 1) * size) > 0) { \
                swap_##name(arr + j * size, arr + (j + 1) * size, size); \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
static void swap_##name(void *a, void *b, size_t size) { \
    char temp; \
    char *pa = (char *)a; \
    char *pb = (char *)b; \
    for (size_t i = 0; i < size; i++) { \
        temp = pa[i]; \
        pa[i] = pb[i]; \
        pb[i] = temp; \
    } \
} \
\
static void sort_##name(void *base, size_t num, size_t size) { \
    char *arr = (char *)base; \
    for (size_t i = 0; i < num - 1; i++) { \
        for (size_t j = 0; j < num - i - 1; j++) { \
            if (cmp_func(arr + j * size, arr + (j + 1) * size) > 0) { \
                swap_##name(arr + j * size, arr + (j + 1) * size, size); \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    static void swap_##name(void *a, void *b, size_t size) { \
        char temp[size]; \
        memcpy(temp, a, size); \
        memcpy(a, b, size); \
        memcpy(b, temp, size); \
    } \
    \
    static void sort_##name(void *base, size_t num, size_t size) { \
        for (size_t i = 0; i < num - 1; i++) { \
            for (size_t j = 0; j < num - i - 1; j++) { \
                void *elem1 = (char *)base + j * size; \
                void *elem2 = (char *)base + (j + 1) * size; \
                if (cmp_func(elem1, elem2) > 0) { \
                    swap_##name(elem1, elem2, size); \
                } \
            } \
        } \
    }

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)
#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static int cmp_func(const void *a, const void *b) { \
    return compare_field(a, b, offsetof(struct item, field)); \
} \
\
static void sort_by_##field(struct item *items, size_t count) { \
    qsort(items, count, sizeof(struct item), cmp_func); \
}

static int compare_field(const void *a, const void *b, size_t offset) {
    const struct item *item_a = (const struct item *)a;
    const struct item *item_b = (const struct item *)b;
    int *field_a = (int *)((char *)item_a + offset);
    int *field_b = (int *)((char *)item_b + offset);
    
    if (*field_a < *field_b) return -1;
    if (*field_a > *field_b) return 1;
    return 0;
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
    void swap_##field(void *a, void *b, size_t size) { \
        char temp[size]; \
        memcpy(temp, a, size); \
        memcpy(a, b, size); \
        memcpy(b, temp, size); \
    } \
    \
    void sort_##field(void *base, size_t num, size_t size) { \
        for (size_t i = 0; i < num - 1; i++) { \
            for (size_t j = 0; j < num - i - 1; j++) { \
                void *elem1 = (char *)base + j * size; \
                void *elem2 = (char *)base + (j + 1) * size; \
                if (cmp_func(elem1, elem2) > 0) { \
                    swap_##field(elem1, elem2, size); \
                } \
            } \
        } \
    }

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(field, cmp_func)                              \
static void swap_##field(void *a, void *b, size_t size) {                   \
    char temp[size];                                                         \
    memcpy(temp, a, size);                                                   \
    memcpy(a, b, size);                                                      \
    memcpy(b, temp, size);                                                   \
}                                                                            \
                                                                             \
static void sort_##field(void *base, size_t num, size_t size) {            \
    for (size_t i = 0; i < num - 1; i++) {                                  \
        size_t min_idx = i;                                                  \
        for (size_t j = i + 1; j < num; j++) {                              \
            void *elem_j = (char *)base + j * size;                         \
            void *elem_min = (char *)base + min_idx * size;                 \
            if (cmp_func(elem_j, elem_min) < 0) {                           \
                min_idx = j;                                                 \
            }                                                                \
        }                                                                    \
        if (min_idx != i) {                                                 \
            void *elem_i = (char *)base + i * size;                         \
            void *elem_min = (char *)base + min_idx * size;                 \
            swap_##field(elem_i, elem_min, size);                           \
        }                                                                    \
    }                                                                        \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static void swap_##field(void *a, void *b, size_t size) { \
    char temp[size]; \
    memcpy(temp, a, size); \
    memcpy(a, b, size); \
    memcpy(b, temp, size); \
} \
\
static void sort_##field(void *base, size_t num, size_t size) { \
    for (size_t i = 0; i < num - 1; i++) { \
        for (size_t j = 0; j < num - i - 1; j++) { \
            void *elem1 = (char *)base + j * size; \
            void *elem2 = (char *)base + (j + 1) * size; \
            if (cmp_func(elem1, elem2) > 0) { \
                swap_##field(elem1, elem2, size); \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static void swap_##field(void *a, void *b, size_t size) { \
    char temp[size]; \
    memcpy(temp, a, size); \
    memcpy(a, b, size); \
    memcpy(b, temp, size); \
} \
\
static void sort_##field(void *base, size_t num, size_t size) { \
    for (size_t i = 0; i < num - 1; i++) { \
        for (size_t j = 0; j < num - i - 1; j++) { \
            void *elem1 = (char*)base + j * size; \
            void *elem2 = (char*)base + (j + 1) * size; \
            if (cmp_func(elem1, elem2) > 0) { \
                swap_##field(elem1, elem2, size); \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
static int cmp_func(const void *a, const void *b) { \
    return compare_##field(a, b); \
} \
\
static void sort_by_##field(void *array, size_t count, size_t size) { \
    qsort(array, count, size, cmp_func); \
} \
\
static int compare_##field(const void *a, const void *b) { \
    const struct item *item_a = (const struct item *)a; \
    const struct item *item_b = (const struct item *)b; \
    if (item_a->field < item_b->field) return -1; \
    if (item_a->field > item_b->field) return 1; \
    return 0; \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(field, cmp_func) \
    void sort_by_##field(void *array, size_t count, size_t size) { \
        qsort(array, count, size, cmp_func); \
    } \
    \
    void stable_sort_by_##field(void *array, size_t count, size_t size) { \
        merge_sort(array, count, size, cmp_func); \
    } \
    \
    void* find_min_##field(void *array, size_t count, size_t size) { \
        return find_element(array, count, size, cmp_func, -1); \
    } \
    \
    void* find_max_##field(void *array, size_t count, size_t size) { \
        return find_element(array, count, size, cmp_func, 1); \
    }

static void* find_element(void *array, size_t count, size_t size, 
                          int (*cmp)(const void*, const void*), int direction) {
    if (count == 0) return NULL;
    
    void *result = array;
    for (size_t i = 1; i < count; i++) {
        void *current = (char*)array + i * size;
        if (cmp(current, result) * direction > 0) {
            result = current;
        }
    }
    return result;
}

static void merge_sort(void *array, size_t count, size_t size,
                      int (*cmp)(const void*, const void*)) {
    if (count <= 1) return;
    
    size_t mid = count / 2;
    void *temp = malloc(count * size);
    if (!temp) return;
    
    merge_sort(array, mid, size, cmp);
    merge_sort((char*)array + mid * size, count - mid, size, cmp);
    merge_arrays(array, mid, count - mid, size, cmp, temp);
    
    memcpy(array, temp, count * size);
    free(temp);
}

static void merge_arrays(void *array, size_t left_count, size_t right_count,
                        size_t size, int (*cmp)(const void*, const void*), void *temp) {
    void *left = array;
    void *right = (char*)array + left_count * size;
    size_t i = 0, j = 0, k = 0;
    
    while (i < left_count && j < right_count) {
        void *left_elem = (char*)left + i * size;
        void *right_elem = (char*)right + j * size;
        
        if (cmp(left_elem, right_elem) <= 0) {
            memcpy((char*)temp + k * size, left_elem, size);
            i++;
        } else {
            memcpy((char*)temp + k * size, right_elem, size);
            j++;
        }
        k++;
    }
    
    copy_remaining(temp, left, size, i, left_count, k);
    copy_remaining(temp, right, size, j, right_count, k + left_count - i);
}

static void copy_remaining(void *dest, void *src, size_t size, 
                           size_t start, size_t end, size_t dest_start) {
    while (start < end) {
        memcpy((char*)dest + dest_start * size, (char*)src + start * size, size);
        start++;
        dest_start++;
    }
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)

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
  int diff = filevercmp (a->name, b->name);
  return diff ? diff : strcmp (a->name, b->name);
}

static int
xstrcoll_version (V a, V b)
{
  return cmp_version (a, b);
}
static int
rev_xstrcoll_version (V a, V b)
{
  return cmp_version (b, a);
}
static int
xstrcoll_df_version (V a, V b)
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

static void initialize_ordering_vector(void)
{
    for (idx_t i = 0; i < cwd_n_used; i++)
    {
        sorted_file[i] = &cwd_file[i];
    }
}

/* Cache values based on attributes global to all files.  */

static void
update_current_files_info (void)
{
  if (!needs_width_calculation())
    return;
    
  calculate_all_file_widths();
}

static bool
needs_width_calculation (void)
{
  return sort_type == sort_width || 
         (line_length && (format == many_per_line || format == horizontal));
}

static void
calculate_all_file_widths (void)
{
  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
      f->width = fileinfo_name_width (f);
    }
}

/* Sort the files now in the table.  */

static void grow_sorted_file_buffer_if_needed(void)
{
    if (sorted_file_alloc < cwd_n_used + (cwd_n_used >> 1))
    {
        free(sorted_file);
        sorted_file = xinmalloc(cwd_n_used, 3 * sizeof *sorted_file);
        sorted_file_alloc = 3 * cwd_n_used;
    }
}

static bool try_strcoll_with_fallback(void)
{
    if (!setjmp(failed_strcoll))
        return false;
    
    affirm(sort_type != sort_version);
    initialize_ordering_vector();
    return true;
}

static int get_sort_function_index(void)
{
    if (sort_type == sort_time)
        return sort_type + time_type;
    return sort_type;
}

static void sort_files(void)
{
    bool use_strcmp;

    grow_sorted_file_buffer_if_needed();
    initialize_ordering_vector();
    update_current_files_info();

    if (sort_type == sort_none)
        return;

    use_strcmp = try_strcoll_with_fallback();

    int sort_index = get_sort_function_index();
    mpsort((void const **)sorted_file, cwd_n_used,
           sort_functions[sort_index][use_strcmp][sort_reverse][directories_first]);
}

/* List all the files now in the table.  */

static void print_one_per_line(void)
{
    for (idx_t i = 0; i < cwd_n_used; i++)
    {
        print_file_name_and_frills(sorted_file[i], 0);
        putchar(eolbyte);
    }
}

static void print_long_format_files(void)
{
    for (idx_t i = 0; i < cwd_n_used; i++)
    {
        set_normal_color();
        print_long_format(sorted_file[i]);
        dired_outbyte(eolbyte);
    }
}

static void print_multi_column(void)
{
    if (!line_length)
        print_with_separator(' ');
    else
        print_many_per_line();
}

static void print_horizontal_format(void)
{
    if (!line_length)
        print_with_separator(' ');
    else
        print_horizontal();
}

static void print_current_files(void)
{
    switch (format)
    {
    case one_per_line:
        print_one_per_line();
        break;

    case many_per_line:
        print_multi_column();
        break;

    case horizontal:
        print_horizontal_format();
        break;

    case with_commas:
        print_with_separator(',');
        break;

    case long_format:
        print_long_format_files();
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
  char const *nfmt = get_time_format(recent, tm->tm_mon);
  return nstrftime (buf, size, nfmt, tm, tz, ns);
}

static char const *
get_time_format(bool recent, int month)
{
  if (use_abformat)
    return abformat[recent][month];
  return long_time_format[recent];
}

/* Return the expected number of columns in a long-format timestamp,
   or zero if it cannot be calculated.  */

static int
long_time_expected_width (void)
{
  static int width = -1;

  if (width >= 0)
    return width;

  width = calculate_time_width();
  if (width < 0)
    width = 0;

  return width;
}

static int
calculate_time_width (void)
{
  time_t epoch = 0;
  struct tm tm;
  char buf[TIME_STAMP_LEN_MAXIMUM + 1];

  if (!localtime_rz (localtz, &epoch, &tm))
    return -1;

  size_t len = align_nstrftime (buf, sizeof buf, false, &tm, localtz, 0);
  if (len == 0)
    return -1;

  return mbsnwidth (buf, len, MBSWIDTH_FLAGS);
}

/* Print the user or group name NAME, with numeric id ID, using a
   print width of WIDTH columns.  */

static void
format_user_or_group (char const *name, uintmax_t id, int width)
{
  if (name)
    {
      int name_width = mbswidth (name, MBSWIDTH_FLAGS);
      int width_gap = name_width < 0 ? 0 : width - name_width;
      int pad = MAX (0, width_gap);
      dired_outstring (name);

      for (int i = 0; i < pad; i++)
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
  const char *user_name = stat_ok ? (numeric_ids ? nullptr : getuser (u)) : "?";
  format_user_or_group (user_name, u, width);
}

/* Likewise, for groups.  */

static void
format_group (gid_t g, int width, bool stat_ok)
{
  const char *group_name = nullptr;
  
  if (!stat_ok)
    {
      group_name = "?";
    }
  else if (!numeric_ids)
    {
      group_name = getgroup (g);
    }
  
  format_user_or_group (group_name, g, width);
}

/* Return the number of columns that format_user_or_group will print,
   or -1 if unknown.  */

static int
format_user_or_group_width (char const *name, uintmax_t id)
{
  if (name)
    return mbswidth (name, MBSWIDTH_FLAGS);
  
  return snprintf (nullptr, 0, "%ju", id);
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
  if (!f->stat_ok || f->stat.st_ino == NOT_AN_INODE_NUMBER)
    return (char *) "?";
  
  return umaxtostr (f->stat.st_ino, buf);
}

/* Print information about F in long format.  */
static void format_mode_string(const struct fileinfo *f, char *modebuf)
{
  if (f->stat_ok)
    {
      filemodestring(&f->stat, modebuf);
    }
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

static struct timespec get_file_timestamp(const struct fileinfo *f, bool *btime_ok)
{
  struct timespec when_timespec;
  *btime_ok = true;

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
    case time_numtypes:
    default:
      unreachable();
    }
  return when_timespec;
}

static char *format_inode_info(char *p, const struct fileinfo *f)
{
  if (print_inode)
    {
      char hbuf[INT_BUFSIZE_BOUND(uintmax_t)];
      p += sprintf(p, "%*s ", inode_number_width, format_inode(hbuf, f));
    }
  return p;
}

static char *format_block_size_info(char *p, const struct fileinfo *f)
{
  if (print_block_size)
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      char const *blocks =
        (!f->stat_ok
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
    }
  return p;
}

static char *format_mode_and_links(char *p, const struct fileinfo *f, const char *modebuf)
{
  char hbuf[INT_BUFSIZE_BOUND(uintmax_t)];
  p += sprintf(p, "%s %*s ", modebuf, nlink_width,
               !f->stat_ok ? "?" : umaxtostr(f->stat.st_nlink, hbuf));
  return p;
}

static void format_ownership_info(const struct fileinfo *f)
{
  if (print_owner)
    format_user(f->stat.st_uid, owner_width, f->stat_ok);

  if (print_group)
    format_group(f->stat.st_gid, group_width, f->stat_ok);

  if (print_author)
    format_user(f->stat.st_author, author_width, f->stat_ok);

  if (print_scontext)
    format_user_or_group(f->scontext, 0, scontext_width);
}

static char *format_device_numbers(char *p, const struct fileinfo *f)
{
  char majorbuf[INT_BUFSIZE_BOUND(uintmax_t)];
  char minorbuf[INT_BUFSIZE_BOUND(uintmax_t)];
  int blanks_width = (file_size_width
                      - (major_device_number_width + 2
                         + minor_device_number_width));
  p += sprintf(p, "%*s, %*s ",
               major_device_number_width + MAX(0, blanks_width),
               umaxtostr(major(f->stat.st_rdev), majorbuf),
               minor_device_number_width,
               umaxtostr(minor(f->stat.st_rdev), minorbuf));
  return p;
}

static char *format_file_size(char *p, const struct fileinfo *f)
{
  char hbuf[LONGEST_HUMAN_READABLE + 1];
  char const *size =
    (!f->stat_ok
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
  return p;
}

static bool is_recent_time(struct timespec when_timespec)
{
  struct timespec six_months_ago;
  
  if (timespec_cmp(current_time, when_timespec) < 0)
    gettime(&current_time);

  #define SIX_MONTHS_IN_SECONDS (31556952 / 2)
  six_months_ago.tv_sec = current_time.tv_sec - SIX_MONTHS_IN_SECONDS;
  six_months_ago.tv_nsec = current_time.tv_nsec;

  return (timespec_cmp(six_months_ago, when_timespec) < 0
          && timespec_cmp(when_timespec, current_time) < 0);
}

static size_t format_time_string(char *p, struct timespec when_timespec,
                                 struct tm *when_local, bool btime_ok,
                                 const struct fileinfo *f)
{
  if (f->stat_ok && btime_ok
      && localtime_rz(localtz, &when_timespec.tv_sec, when_local))
    {
      bool recent = is_recent_time(when_timespec);
      return align_nstrftime(p, TIME_STAMP_LEN_MAXIMUM + 1, recent,
                            when_local, localtz, when_timespec.tv_nsec);
    }
  return 0;
}

static char *format_timestamp(char *p, struct timespec when_timespec,
                              struct tm *when_local, bool btime_ok,
                              const struct fileinfo *f)
{
  size_t s = format_time_string(p, when_timespec, when_local, btime_ok, f);
  *p = '\1';

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
                   : timetostr(when_timespec.tv_sec, hbuf)));
    }
  return p;
}

static void print_link_and_indicator(const struct fileinfo *f, size_t w, char *p, char *buf)
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

static void print_long_format(const struct fileinfo *f)
{
  char modebuf[12];
  char buf[LONGEST_HUMAN_READABLE + 1
           + LONGEST_HUMAN_READABLE + 1
           + sizeof(modebuf) - 1 + 1
           + INT_BUFSIZE_BOUND(uintmax_t)
           + LONGEST_HUMAN_READABLE + 2
           + LONGEST_HUMAN_READABLE + 1
           + TIME_STAMP_LEN_MAXIMUM + 1];
  char *p;
  struct timespec when_timespec;
  struct tm when_local;
  bool btime_ok;

  format_mode_string(f, modebuf);
  when_timespec = get_file_timestamp(f, &btime_ok);

  p = buf;
  p = format_inode_info(p, f);
  p = format_block_size_info(p, f);
  p = format_mode_and_links(p, f, modebuf);

  dired_indent();

  if (print_owner || print_group || print_author || print_scontext)
    {
      dired_outbuf(buf, p - buf);
      format_ownership_info(f);
      p = buf;
    }

  if (f->stat_ok && (S_ISCHR(f->stat.st_mode) || S_ISBLK(f->stat.st_mode)))
    {
      p = format_device_numbers(p, f);
    }
  else
    {
      p = format_file_size(p, f);
    }

  p = format_timestamp(p, when_timespec, &when_local, btime_ok, f);

  dired_outbuf(buf, p - buf);
  size_t w = print_name_with_quoting(f, false, &dired_obstack, p - buf);

  print_link_and_indicator(f, w, p, buf);
}

/* Write to *BUF a quoted representation of the file name NAME, if non-null,
   using OPTIONS to control quoting.  *BUF is set to NAME if no quoting
   is required.  *BUF is allocated if more space required (and the original
   *BUF is not deallocated).
   Store the number of screen columns occupied by NAME's quoted
   representation into WIDTH, if non-null.
   Store into PAD whether an initial space is needed for padding.
   Return the number of bytes in *BUF.  */

static bool is_printable_ascii(char c)
{
  return (c >= ' ' && c <= '~') || c == '\t';
}

static bool needs_further_quoting_check(enum quoting_style qs)
{
  return qmark_funny_chars
         && (qs == shell_quoting_style
             || qs == shell_always_quoting_style
             || qs == literal_quoting_style);
}

static size_t handle_general_quoting(char **buf, size_t bufsize, char *name,
                                    struct quoting_options const *options,
                                    bool *quoted)
{
  size_t len = quotearg_buffer (*buf, bufsize, name, -1, options);
  if (bufsize <= len)
    {
      *buf = xmalloc (len + 1);
      quotearg_buffer (*buf, len + 1, name, -1, options);
    }
  *quoted = (*name != **buf) || strlen (name) != len;
  return len;
}

static size_t copy_name_to_buffer(char **buf, size_t bufsize, char *name,
                                 bool *quoted)
{
  size_t len = strlen (name);
  if (bufsize <= len)
    *buf = xmalloc (len + 1);
  memcpy (*buf, name, len + 1);
  *quoted = false;
  return len;
}

static size_t process_multibyte_char(char const **p, char const *plimit,
                                    char **q, size_t *displayed_width)
{
  mbstate_t mbstate;
  mbszero (&mbstate);
  
  do
    {
      char32_t wc;
      size_t bytes = mbrtoc32 (&wc, *p, plimit - *p, &mbstate);

      if (bytes == (size_t) -1)
        {
          (*p)++;
          *(*q)++ = '?';
          (*displayed_width)++;
          break;
        }

      if (bytes == (size_t) -2)
        {
          *p = plimit;
          *(*q)++ = '?';
          (*displayed_width)++;
          break;
        }

      if (bytes == 0)
        bytes = 1;

      int w = c32width (wc);
      if (w >= 0)
        {
          for (; bytes > 0; --bytes)
            *(*q)++ = *(*p)++;
          *displayed_width += w;
        }
      else
        {
          *p += bytes;
          *(*q)++ = '?';
          (*displayed_width)++;
        }
    }
  while (! mbsinit (&mbstate));
  
  return 0;
}

static size_t quote_multibyte_chars(char *buf, size_t len)
{
  char const *p = buf;
  char const *plimit = buf + len;
  char *q = buf;
  size_t displayed_width = 0;

  while (p < plimit)
    {
      if (is_printable_ascii(*p) && *p != '?' && *p != '@')
        {
          *q++ = *p++;
          displayed_width++;
        }
      else
        {
          process_multibyte_char(&p, plimit, &q, &displayed_width);
        }
    }

  return q - buf;
}

static void replace_unprintable_chars(char *buf, size_t len)
{
  char *p = buf;
  char const *plimit = buf + len;

  while (p < plimit)
    {
      if (! isprint (to_uchar (*p)))
        *p = '?';
      p++;
    }
}

static size_t calculate_displayed_width_mb(char const *buf, size_t len)
{
  size_t displayed_width = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
  return MAX (0, displayed_width);
}

static size_t calculate_displayed_width_sb(char const *buf, size_t len)
{
  char const *p = buf;
  char const *plimit = buf + len;
  size_t displayed_width = 0;

  while (p < plimit)
    {
      if (isprint (to_uchar (*p)))
        displayed_width++;
      p++;
    }
  
  return displayed_width;
}

static size_t
quote_name_buf (char **inbuf, size_t bufsize, char *name,
                struct quoting_options const *options,
                int needs_general_quoting, size_t *width, bool *pad)
{
  char *buf = *inbuf;
  size_t displayed_width IF_LINT ( = 0);
  size_t len = 0;
  bool quoted;

  enum quoting_style qs = get_quoting_style (options);
  bool needs_further_quoting = needs_further_quoting_check(qs);

  if (needs_general_quoting != 0)
    {
      len = handle_general_quoting(&buf, bufsize, name, options, &quoted);
    }
  else if (needs_further_quoting)
    {
      len = copy_name_to_buffer(&buf, bufsize, name, &quoted);
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
        {
          len = quote_multibyte_chars(buf, len);
          displayed_width = len;
        }
      else
        {
          replace_unprintable_chars(buf, len);
          displayed_width = len;
        }
    }
  else if (width != nullptr)
    {
      if (MB_CUR_MAX > 1)
        {
          displayed_width = calculate_displayed_width_mb(buf, len);
        }
      else
        {
          displayed_width = calculate_displayed_width_sb(buf, len);
        }
    }

  *pad = (align_variable_outer_quotes && cwd_some_quoted && ! quoted);

  if (width != nullptr)
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

  quote_name_buf (&buf, sizeof smallbuf, (char *) name, options,
                  needs_general_quoting, &width, &pad);

  if (buf != smallbuf && buf != name)
    free (buf);

  return width + pad;
}

/* %XX escape any input out of range as defined in RFC3986,
   and also if PATH, convert all path separators to '/'.  */
static char *
file_escape (char const *str, bool path)
{
  char *esc = xnmalloc (3, strlen (str) + 1);
  char *p = esc;
  while (*str)
    {
      if (path && ISSLASH (*str))
        {
          *p++ = '/';
          str++;
        }
      else if (RFC3986[to_uchar (*str)])
        {
          *p++ = *str++;
        }
      else
        {
          p += sprintf (p, "%%%02x", to_uchar (*str++));
        }
    }
  *p = '\0';
  return esc;
}

static void print_hyperlink_start(const char *absolute_name, const char *buf, bool *skip_quotes)
{
  if (align_variable_outer_quotes && cwd_some_quoted && !pad)
  {
    *skip_quotes = true;
    putchar(*buf);
  }
  
  char *h = file_escape(hostname, false);
  char *n = file_escape(absolute_name, true);
  printf("\033]8;;file://%s%s%s\a", h, *n == '/' ? "" : "/", n);
  free(h);
  free(n);
}

static void print_hyperlink_end(const char *buf, size_t len, bool skip_quotes)
{
  fputs("\033]8;;\a", stdout);
  if (skip_quotes)
    putchar(*(buf + len - 1));
}

static void output_quoted_content(const char *buf, size_t len, bool skip_quotes, struct obstack *stack)
{
  if (stack)
    push_current_dired_pos(stack);
    
  size_t offset = skip_quotes ? 1 : 0;
  size_t output_len = len - (skip_quotes ? 2 : 0);
  fwrite(buf + offset, 1, output_len, stdout);
  
  dired_pos += len;
  
  if (stack)
    push_current_dired_pos(stack);
}

static void cleanup_buffer(char *buf, const char *smallbuf, const char *name)
{
  if (buf != smallbuf && buf != name)
    free(buf);
}

static size_t
quote_name(char const *name, struct quoting_options const *options,
          int needs_general_quoting, const struct bin_str *color,
          bool allow_pad, struct obstack *stack, char const *absolute_name)
{
  char smallbuf[BUFSIZ];
  char *buf = smallbuf;
  size_t len;
  bool pad;
  bool skip_quotes = false;

  len = quote_name_buf(&buf, sizeof smallbuf, (char *)name, options,
                       needs_general_quoting, nullptr, &pad);

  if (pad && allow_pad)
    dired_outbyte(' ');

  if (color)
    print_color_indicator(color);

  if (absolute_name)
    print_hyperlink_start(absolute_name, buf, &skip_quotes);

  output_quoted_content(buf, len, skip_quotes, stack);

  if (absolute_name)
    print_hyperlink_end(buf, len, skip_quotes);

  cleanup_buffer(buf, smallbuf, name);

  return len + pad;
}

static bool should_use_color(const struct bin_str *color)
{
    return print_with_color && (color || is_colored(C_NORM));
}

static bool name_might_wrap(size_t start_col, size_t len)
{
    return line_length && 
           (start_col / line_length != (start_col + len - 1) / line_length);
}

static void handle_color_cleanup(size_t start_col, size_t len)
{
    prep_non_filename_text();
    
    if (name_might_wrap(start_col, len))
        put_indicator(&color_indicator[C_CLR_TO_EOL]);
}

static size_t
print_name_with_quoting (const struct fileinfo *f,
                         bool symlink_target,
                         struct obstack *stack,
                         size_t start_col)
{
    char const *name = symlink_target ? f->linkname : f->name;

    const struct bin_str *color = print_with_color ? 
                                   get_color_indicator(f, symlink_target) : 
                                   nullptr;

    bool used_color_this_time = should_use_color(color);

    size_t len = quote_name(name, filename_quoting_options, f->quoted,
                           color, !symlink_target, stack, f->absolute_name);

    process_signals();
    
    if (used_color_this_time)
        handle_color_cleanup(start_col, len);

    return len;
}

static void
prep_non_filename_text (void)
{
  if (color_indicator[C_END].string != nullptr)
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

static void print_inode_info(const struct fileinfo *f, char *buf)
{
    printf("%*s ", format == with_commas ? 0 : inode_number_width,
           format_inode(buf, f));
}

static void print_block_info(const struct fileinfo *f, char *buf)
{
    char const *blocks = f->stat_ok
        ? human_readable(STP_NBLOCKS(&f->stat), buf, human_output_opts,
                        ST_NBLOCKSIZE, output_block_size)
        : "?";
    
    int blocks_width = mbswidth(blocks, MBSWIDTH_FLAGS);
    int pad = 0;
    
    if (blocks_width >= 0 && block_size_width && format != with_commas)
        pad = block_size_width - blocks_width;
    
    printf("%*s%s ", pad, "", blocks);
}

static void print_scontext_info(const struct fileinfo *f)
{
    printf("%*s ", format == with_commas ? 0 : scontext_width, f->scontext);
}

static size_t print_file_name_and_frills(const struct fileinfo *f, size_t start_col)
{
    char buf[MAX(LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND(uintmax_t))];

    set_normal_color();

    if (print_inode)
        print_inode_info(f, buf);

    if (print_block_size)
        print_block_info(f, buf);

    if (print_scontext)
        print_scontext_info(f);

    size_t width = print_name_with_quoting(f, false, nullptr, start_col);

    if (indicator_style != none)
        width += print_type_indicator(f->stat_ok, f->stat.st_mode, f->filetype);

    return width;
}

/* Given these arguments describing a file, return the single-byte
   type indicator, or 0.  */
static bool is_regular_file(bool stat_ok, mode_t mode, enum filetype type)
{
    return stat_ok ? S_ISREG(mode) : type == normal;
}

static bool is_directory(bool stat_ok, mode_t mode, enum filetype type)
{
    return stat_ok ? S_ISDIR(mode) : (type == directory || type == arg_directory);
}

static bool is_symbolic_link(bool stat_ok, mode_t mode, enum filetype type)
{
    return stat_ok ? S_ISLNK(mode) : type == symbolic_link;
}

static bool is_fifo(bool stat_ok, mode_t mode, enum filetype type)
{
    return stat_ok ? S_ISFIFO(mode) : type == fifo;
}

static bool is_socket(bool stat_ok, mode_t mode, enum filetype type)
{
    return stat_ok ? S_ISSOCK(mode) : type == sock;
}

static bool is_door(bool stat_ok, mode_t mode)
{
    return stat_ok && S_ISDOOR(mode);
}

static bool is_executable(bool stat_ok, mode_t mode)
{
    return stat_ok && indicator_style == classify && (mode & S_IXUGO);
}

static char get_regular_file_indicator(bool stat_ok, mode_t mode)
{
    return is_executable(stat_ok, mode) ? '*' : 0;
}

static char get_special_file_indicator(bool stat_ok, mode_t mode, enum filetype type)
{
    if (is_directory(stat_ok, mode, type))
        return '/';
    
    if (indicator_style == slash)
        return 0;
    
    if (is_symbolic_link(stat_ok, mode, type))
        return '@';
    
    if (is_fifo(stat_ok, mode, type))
        return '|';
    
    if (is_socket(stat_ok, mode, type))
        return '=';
    
    if (is_door(stat_ok, mode))
        return '>';
    
    return 0;
}

static char get_type_indicator(bool stat_ok, mode_t mode, enum filetype type)
{
    if (is_regular_file(stat_ok, mode, type))
        return get_regular_file_indicator(stat_ok, mode);
    
    return get_special_file_indicator(stat_ok, mode, type);
}

static bool
print_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  char c = get_type_indicator (stat_ok, mode, type);
  if (c)
    dired_outbyte (c);
  return c != 0;
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
  
  struct color_ext_type *ext = find_matching_extension(name, type);
  
  if (type == C_LINK && !linkok)
    {
      if (color_symlink_as_referent || is_colored (C_ORPHAN))
        type = C_ORPHAN;
    }

  const struct bin_str *const s
    = ext ? &(ext->seq) : &color_indicator[type];

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
    return determine_regular_file_type(f, mode);
    
  if (S_ISDIR (mode))
    return determine_directory_type(mode);
    
  return determine_special_file_type(mode);
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
determine_regular_file_type(const struct fileinfo *f, mode_t mode)
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
determine_directory_type(mode_t mode)
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

static enum indicator_no
determine_special_file_type(mode_t mode)
{
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

static struct color_ext_type*
find_matching_extension(const char *name, enum indicator_no type)
{
  if (type != C_FILE)
    return nullptr;
    
  size_t len = strlen (name);
  name += len;
  
  for (struct color_ext_type *ext = color_ext_list; ext != nullptr; ext = ext->next)
    {
      if (ext->ext.len > len)
        continue;
        
      bool matches = ext->exact_match 
        ? STREQ_LEN (name - ext->ext.len, ext->ext.string, ext->ext.len)
        : c_strncasecmp (name - ext->ext.len, ext->ext.string, ext->ext.len) == 0;
        
      if (matches)
        return ext;
    }
    
  return nullptr;
}

/* Output a color indicator (which may contain nulls).  */
static void
put_indicator (const struct bin_str *ind)
{
  if (! used_color)
    {
      used_color = true;

      if (0 <= tcgetpgrp (STDOUT_FILENO))
        signal_init ();

      prep_non_filename_text ();
    }

  fwrite (ind->string, ind->len, 1, stdout);
}

static size_t calculate_inode_length(const struct fileinfo *f, const char *buf)
{
    if (format == with_commas)
        return strlen(umaxtostr(f->stat.st_ino, buf));
    return inode_number_width;
}

static size_t calculate_block_size_length(const struct fileinfo *f, const char *buf)
{
    if (format == with_commas) {
        if (!f->stat_ok)
            return strlen("?");
        return strlen(human_readable(STP_NBLOCKS(&f->stat), buf,
                                    human_output_opts, ST_NBLOCKSIZE,
                                    output_block_size));
    }
    return block_size_width;
}

static size_t calculate_scontext_length(const struct fileinfo *f)
{
    if (format == with_commas)
        return strlen(f->scontext);
    return scontext_width;
}

static size_t calculate_indicator_length(const struct fileinfo *f)
{
    if (indicator_style == none)
        return 0;
    
    char c = get_type_indicator(f->stat_ok, f->stat.st_mode, f->filetype);
    return (c != 0) ? 1 : 0;
}

static size_t length_of_file_name_and_frills(const struct fileinfo *f)
{
    size_t len = 0;
    char buf[MAX(LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND(uintmax_t))];
    
    if (print_inode)
        len += 1 + calculate_inode_length(f, buf);
    
    if (print_block_size)
        len += 1 + calculate_block_size_length(f, buf);
    
    if (print_scontext)
        len += 1 + calculate_scontext_length(f);
    
    len += fileinfo_name_width(f);
    len += calculate_indicator_length(f);
    
    return len;
}

static void print_row_element(struct fileinfo const *f, size_t *pos, size_t max_name_length)
{
    size_t name_length = length_of_file_name_and_frills(f);
    print_file_name_and_frills(f, *pos);
    
    indent(*pos + name_length, *pos + max_name_length);
    *pos += max_name_length;
}

static int should_continue_row(idx_t filesno, idx_t rows)
{
    return cwd_n_used - rows > filesno;
}

static void print_single_row(idx_t row, idx_t rows, struct column_info const *line_fmt)
{
    size_t col = 0;
    idx_t filesno = row;
    size_t pos = 0;
    
    while (1)
    {
        struct fileinfo const *f = sorted_file[filesno];
        size_t name_length = length_of_file_name_and_frills(f);
        size_t max_name_length = line_fmt->col_arr[col++];
        
        print_file_name_and_frills(f, pos);
        
        if (!should_continue_row(filesno, rows))
            break;
            
        filesno += rows;
        indent(pos + name_length, pos + max_name_length);
        pos += max_name_length;
    }
    
    putchar(eolbyte);
}

static void print_many_per_line(void)
{
    idx_t cols = calculate_columns(1);
    struct column_info const *line_fmt = &column_info[cols - 1];
    idx_t rows = cwd_n_used / cols + (cwd_n_used % cols != 0);
    
    for (idx_t row = 0; row < rows; row++)
    {
        print_single_row(row, rows, line_fmt);
    }
}

static void print_first_entry(struct fileinfo const *f)
{
    print_file_name_and_frills(f, 0);
}

static void handle_new_line(size_t *pos)
{
    putchar(eolbyte);
    *pos = 0;
}

static void handle_column_spacing(size_t *pos, size_t name_length, size_t max_name_length)
{
    indent(*pos + name_length, *pos + max_name_length);
    *pos += max_name_length;
}

static void print_entry(struct fileinfo const *f, size_t pos)
{
    print_file_name_and_frills(f, pos);
}

static void process_file_entry(idx_t filesno, idx_t cols, 
                               struct column_info const *line_fmt,
                               size_t *pos, size_t *name_length)
{
    idx_t col = filesno % cols;
    
    if (col == 0)
    {
        handle_new_line(pos);
    }
    else
    {
        size_t max_name_length = line_fmt->col_arr[col - 1];
        handle_column_spacing(pos, *name_length, max_name_length);
    }
    
    struct fileinfo const *f = sorted_file[filesno];
    print_entry(f, *pos);
    
    *name_length = length_of_file_name_and_frills(f);
}

static void print_horizontal(void)
{
    size_t pos = 0;
    idx_t cols = calculate_columns(false);
    struct column_info const *line_fmt = &column_info[cols - 1];
    
    struct fileinfo const *first_file = sorted_file[0];
    print_first_entry(first_file);
    
    size_t name_length = length_of_file_name_and_frills(first_file);
    
    for (idx_t filesno = 1; filesno < cwd_n_used; filesno++)
    {
        process_file_entry(filesno, cols, line_fmt, &pos, &name_length);
    }
    
    putchar(eolbyte);
}

/* Output name + SEP + ' '.  */

static size_t get_file_name_length(const struct fileinfo *f)
{
    return line_length ? length_of_file_name_and_frills(f) : 0;
}

static int fits_on_current_line(size_t pos, size_t len)
{
    return (pos + len + 2 < line_length) && (pos <= SIZE_MAX - len - 2);
}

static size_t print_separator(char sep, size_t pos, size_t len)
{
    char separator;
    size_t new_pos;
    
    if (!line_length || fits_on_current_line(pos, len))
    {
        new_pos = pos + 2;
        separator = ' ';
    }
    else
    {
        new_pos = 0;
        separator = eolbyte;
    }
    
    putchar(sep);
    putchar(separator);
    
    return new_pos;
}

static void print_with_separator(char sep)
{
    size_t pos = 0;
    
    for (idx_t filesno = 0; filesno < cwd_n_used; filesno++)
    {
        struct fileinfo const *f = sorted_file[filesno];
        size_t len = get_file_name_length(f);
        
        if (filesno != 0)
        {
            pos = print_separator(sep, pos, len);
        }
        
        print_file_name_and_frills(f, pos);
        pos += len;
    }
    
    putchar(eolbyte);
}

/* Assuming cursor is at position FROM, indent up to position TO.
   Use a TAB character instead of two or more spaces whenever possible.  */

static void output_tab(size_t *from)
{
    putchar('\t');
    *from += tabsize - *from % tabsize;
}

static void output_space(size_t *from)
{
    putchar(' ');
    (*from)++;
}

static int should_use_tab(size_t from, size_t to)
{
    return tabsize != 0 && to / tabsize > (from + 1) / tabsize;
}

static void indent(size_t from, size_t to)
{
    while (from < to)
    {
        if (should_use_tab(from, to))
            output_tab(&from);
        else
            output_space(&from);
    }
}

/* Put DIRNAME/NAME into DEST, handling '.' and '/' properly.  */
/* FIXME: maybe remove this function someday.  See about using a
   non-malloc'ing version of file_name_concat.  */

static void copy_string(char **dest, char const **src)
{
    while (**src)
    {
        **dest = **src;
        (*dest)++;
        (*src)++;
    }
}

static int is_current_directory(char const *dirname)
{
    return dirname[0] == '.' && dirname[1] == 0;
}

static int needs_separator(char const *dirnamep, char const *dirname)
{
    return dirnamep > dirname && dirnamep[-1] != '/';
}

static void attach(char *dest, char const *dirname, char const *name)
{
    char const *dirnamep = dirname;

    if (!is_current_directory(dirname))
    {
        copy_string(&dest, &dirnamep);
        
        if (needs_separator(dirnamep, dirname))
        {
            *dest++ = '/';
        }
    }
    
    copy_string(&dest, &name);
    *dest = 0;
}

/* Allocate enough column info suitable for the current number of
   files and display columns, and initialize the info to represent the
   narrowest possible columns.  */

static void grow_column_info_allocation(idx_t old_alloc, idx_t new_alloc)
{
    idx_t growth = new_alloc - old_alloc;
    idx_t s;
    
    if (ckd_add(&s, old_alloc + 1, new_alloc) || ckd_mul(&s, s, growth))
        xalloc_die();
    
    size_t *p = xinmalloc(s >> 1, sizeof *p);
    
    for (idx_t i = old_alloc; i < new_alloc; i++)
    {
        column_info[i].col_arr = p;
        p += i + 1;
    }
}

static void initialize_column_widths(idx_t max_cols)
{
    for (idx_t i = 0; i < max_cols; ++i)
    {
        column_info[i].valid_len = true;
        column_info[i].line_len = (i + 1) * MIN_COLUMN_WIDTH;
        for (idx_t j = 0; j <= i; ++j)
            column_info[i].col_arr[j] = MIN_COLUMN_WIDTH;
    }
}

static void ensure_column_info_capacity(idx_t max_cols, idx_t *column_info_alloc)
{
    if (*column_info_alloc >= max_cols)
        return;
    
    idx_t old_column_info_alloc = *column_info_alloc;
    column_info = xpalloc(column_info, column_info_alloc,
                         max_cols - *column_info_alloc, -1,
                         sizeof *column_info);
    
    grow_column_info_allocation(old_column_info_alloc, *column_info_alloc);
}

static void init_column_info(idx_t max_cols)
{
    static idx_t column_info_alloc;
    
    ensure_column_info_capacity(max_cols, &column_info_alloc);
    initialize_column_widths(max_cols);
}

/* Calculate the number of columns needed to represent the current set
   of files in the current display width.  */

static idx_t
get_max_columns(void)
{
  return 0 < max_idx && max_idx < cwd_n_used ? max_idx : cwd_n_used;
}

static idx_t
calculate_index(idx_t filesno, idx_t i, bool by_columns)
{
  if (by_columns)
    return filesno / ((cwd_n_used + i) / (i + 1));
  return filesno % (i + 1);
}

static size_t
calculate_real_length(size_t name_length, idx_t idx, idx_t i)
{
  #define SPACING_BETWEEN_COLUMNS 2
  return name_length + (idx == i ? 0 : SPACING_BETWEEN_COLUMNS);
}

static void
update_column_info(idx_t i, idx_t idx, size_t real_length)
{
  if (column_info[i].col_arr[idx] < real_length)
    {
      column_info[i].line_len += (real_length - column_info[i].col_arr[idx]);
      column_info[i].col_arr[idx] = real_length;
      column_info[i].valid_len = (column_info[i].line_len < line_length);
    }
}

static void
process_file_columns(idx_t filesno, idx_t max_cols, bool by_columns)
{
  struct fileinfo const *f = sorted_file[filesno];
  size_t name_length = length_of_file_name_and_frills(f);

  for (idx_t i = 0; i < max_cols; ++i)
    {
      if (!column_info[i].valid_len)
        continue;

      idx_t idx = calculate_index(filesno, i, by_columns);
      size_t real_length = calculate_real_length(name_length, idx, i);
      update_column_info(i, idx, real_length);
    }
}

static void
compute_column_widths(idx_t max_cols, bool by_columns)
{
  for (idx_t filesno = 0; filesno < cwd_n_used; ++filesno)
    {
      process_file_columns(filesno, max_cols, by_columns);
    }
}

static idx_t
find_maximum_valid_columns(idx_t max_cols)
{
  idx_t cols;
  for (cols = max_cols; 1 < cols; --cols)
    {
      if (column_info[cols - 1].valid_len)
        break;
    }
  return cols;
}

static idx_t
calculate_columns(bool by_columns)
{
  idx_t max_cols = get_max_columns();
  init_column_info(max_cols);
  compute_column_widths(max_cols, by_columns);
  return find_maximum_valid_columns(max_cols);
}

void print_basic_options(void)
{
    fputs(_("\
  -a, --all                  do not ignore entries starting with .\n\
  -A, --almost-all           do not list implied . and ..\n\
      --author               with -l, print the author of each file\n\
  -b, --escape               print C-style escapes for nongraphic characters\n\
"), stdout);
    fputs(_("\
      --block-size=SIZE      with -l, scale sizes by SIZE when printing them;\n\
                             e.g., '--block-size=M'; see SIZE format below\n\
\n\
"), stdout);
    fputs(_("\
  -B, --ignore-backups       do not list implied entries ending with ~\n\
"), stdout);
}

void print_sorting_options(void)
{
    fputs(_("\
  -c                         with -lt: sort by, and show, ctime (time of last\n\
                             change of file status information);\n\
                             with -l: show ctime and sort by name;\n\
                             otherwise: sort by ctime, newest first\n\
\n\
"), stdout);
    fputs(_("\
  -C                         list entries by columns\n\
      --color[=WHEN]         color the output WHEN; more info below\n\
  -d, --directory            list directories themselves, not their contents\n\
  -D, --dired                generate output designed for Emacs' dired mode\n\
"), stdout);
}

void print_format_options(void)
{
    fputs(_("\
  -f                         same as -a -U\n\
  -F, --classify[=WHEN]      append indicator (one of */=>@|) to entries WHEN\n\
      --file-type            likewise, except do not append '*'\n\
"), stdout);
    fputs(_("\
      --format=WORD          across,horizontal (-x), commas (-m), long (-l),\n\
                             single-column (-1), verbose (-l), vertical (-C)\n\
\n\
"), stdout);
    fputs(_("\
      --full-time            like -l --time-style=full-iso\n\
"), stdout);
    fputs(_("\
  -g                         like -l, but do not list owner\n\
"), stdout);
    fputs(_("\
      --group-directories-first\n\
                             group directories before files\n\
"), stdout);
    fputs(_("\
  -G, --no-group             in a long listing, don't print group names\n\
"), stdout);
}

void print_size_options(void)
{
    fputs(_("\
  -h, --human-readable       with -l and -s, print sizes like 1K 234M 2G etc.\n\
      --si                   likewise, but use powers of 1000 not 1024\n\
"), stdout);
}

void print_symlink_options(void)
{
    fputs(_("\
  -H, --dereference-command-line\n\
                             follow symbolic links listed on the command line\n\
"), stdout);
    fputs(_("\
      --dereference-command-line-symlink-to-dir\n\
                             follow each command line symbolic link\n\
                             that points to a directory\n\
\n\
"), stdout);
}

void print_filter_options(void)
{
    fputs(_("\
      --hide=PATTERN         do not list implied entries matching shell PATTERN\
\n\
                             (overridden by -a or -A)\n\
\n\
"), stdout);
    fputs(_("\
      --hyperlink[=WHEN]     hyperlink file names WHEN\n\
"), stdout);
    fputs(_("\
      --indicator-style=WORD\n\
                             append indicator with style WORD to entry names:\n\
                             none (default), slash (-p),\n\
                             file-type (--file-type), classify (-F)\n\
\n\
"), stdout);
    fputs(_("\
  -i, --inode                print the index number of each file\n\
  -I, --ignore=PATTERN       do not list implied entries matching shell PATTERN\
\n\
"), stdout);
    fputs(_("\
  -k, --kibibytes            default to 1024-byte blocks for file system usage;\
\n\
                             used only with -s and per directory totals\n\
\n\
"), stdout);
}

void print_listing_options(void)
{
    fputs(_("\
  -l                         use a long listing format\n\
"), stdout);
    fputs(_("\
  -L, --dereference          when showing file information for a symbolic\n\
                             link, show information for the file the link\n\
                             references rather than for the link itself\n\
\n\
"), stdout);
    fputs(_("\
  -m                         fill width with a comma separated list of entries\
\n\
"), stdout);
    fputs(_("\
  -n, --numeric-uid-gid      like -l, but list numeric user and group IDs\n\
  -N, --literal              print entry names without quoting\n\
  -o                         like -l, but do not list group information\n\
  -p, --indicator-style=slash\n\
                             append / indicator to directories\n\
"), stdout);
}

void print_quoting_options(void)
{
    fputs(_("\
  -q, --hide-control-chars   print ? instead of nongraphic characters\n\
"), stdout);
    fputs(_("\
      --show-control-chars   show nongraphic characters as-is (the default,\n\
                             unless program is 'ls' and output is a terminal)\
\n\
\n\
"), stdout);
    fputs(_("\
  -Q, --quote-name           enclose entry names in double quotes\n\
"), stdout);
    fputs(_("\
      --quoting-style=WORD   use quoting style WORD for entry names:\n\
                             literal, locale, shell, shell-always,\n\
                             shell-escape, shell-escape-always, c, escape\n\
                             (overrides QUOTING_STYLE environment variable)\n\
\n\
"), stdout);
}

void print_advanced_sort_options(void)
{
    fputs(_("\
  -r, --reverse              reverse order while sorting\n\
  -R, --recursive            list subdirectories recursively\n\
  -s, --size                 print the allocated size of each file, in blocks\n\
"), stdout);
    fputs(_("\
  -S                         sort by file size, largest first\n\
"), stdout);
    fputs(_("\
      --sort=WORD            change default 'name' sort to WORD:\n\
                               none (-U), size (-S), time (-t),\n\
                               version (-v), extension (-X), name, width\n\
\n\
"), stdout);
}

void print_time_options(void)
{
    fputs(_("\
      --time=WORD            select which timestamp used to display or sort;\n\
                               access time (-u): atime, access, use;\n\
                               metadata change time (-c): ctime, status;\n\
                               modified time (default): mtime, modification;\n\
                               birth time: birth, creation;\n\
                             with -l, WORD determines which time to show;\n\
                             with --sort=time, sort by WORD (newest first)\n\
\n\
"), stdout);
    fputs(_("\
      --time-style=TIME_STYLE\n\
                             time/date format with -l; see TIME_STYLE below\n\
"), stdout);
    fputs(_("\
  -t                         sort by time, newest first; see --time\n\
  -T, --tabsize=COLS         assume tab stops at each COLS instead of 8\n\
"), stdout);
    fputs(_("\
  -u                         with -lt: sort by, and show, access time;\n\
                             with -l: show access time and sort by name;\n\
                             otherwise: sort by access time, newest first\n\
\n\
"), stdout);
}

void print_misc_options(void)
{
    fputs(_("\
  -U                         do not sort directory entries\n\
"), stdout);
    fputs(_("\
  -v                         natural sort of (version) numbers within text\n\
"), stdout);
    fputs(_("\
  -w, --width=COLS           set output width to COLS.  0 means no limit\n\
  -x                         list entries by lines instead of by columns\n\
  -X                         sort alphabetically by entry extension\n\
  -Z, --context              print any security context of each file\n\
      --zero                 end each output line with NUL, not newline\n\
  -1                         list one file per line\n\
"), stdout);
}

void print_additional_info(void)
{
    emit_size_note();
    fputs(_("\
\n\
The TIME_STYLE argument can be full-iso, long-iso, iso, locale, or +FORMAT.\n\
FORMAT is interpreted like in date(1).  If FORMAT is FORMAT1<newline>FORMAT2,\n\
then FORMAT1 applies to non-recent files and FORMAT2 to recent files.\n\
TIME_STYLE prefixed with 'posix-' takes effect only outside the POSIX locale.\n\
Also the TIME_STYLE environment variable sets the default style to use.\n\
"), stdout);
    fputs(_("\
\n\
The WHEN argument defaults to 'always' and can also be 'auto' or 'never'.\n\
"), stdout);
    fputs(_("\
\n\
Using color to distinguish file types is disabled both by default and\n\
with --color=never.  With --color=auto, ls emits color codes only when\n\
standard output is connected to a terminal.  The LS_COLORS environment\n\
variable can change the settings.  Use the dircolors(1) command to set it.\n\
"), stdout);
    fputs(_("\
\n\
Exit status:\n\
 0  if OK,\n\
 1  if minor problems (e.g., cannot access subdirectory),\n\
 2  if serious trouble (e.g., cannot access command-line argument).\n\
"), stdout);
}

void print_all_options(void)
{
    print_basic_options();
    print_sorting_options();
    print_format_options();
    print_size_options();
    print_symlink_options();
    print_filter_options();
    print_listing_options();
    print_quoting_options();
    print_advanced_sort_options();
    print_time_options();
    print_misc_options();
    fputs(HELP_OPTION_DESCRIPTION, stdout);
    fputs(VERSION_OPTION_DESCRIPTION, stdout);
    print_additional_info();
    emit_ancillary_info(PROGRAM_NAME);
}

void usage(int status)
{
    if (status != EXIT_SUCCESS) {
        emit_try_help();
        exit(status);
    }
    
    printf(_("Usage: %s [OPTION]... [FILE]...\n"), program_name);
    fputs(_("\
List information about the FILEs (the current directory by default).\n\
Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n\
"), stdout);
    
    emit_mandatory_arg_note();
    print_all_options();
    exit(status);
}
