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
  if (!color_symlink_as_referent || !file->linkok)
    return file->stat.st_mode;

  return file->linkmode;
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
    (void)putchar((unsigned char)c);
}

/* Output the buffer S, of length S_LEN, and increment DIRED_POS by S_LEN.  */
static void
dired_outbuf(char const *s, size_t s_len)
{
  size_t total_written = 0;

  if (s == NULL || s_len == 0)
    return;

  while (total_written < s_len)
    {
      size_t n = fwrite(s + total_written, 1, s_len - total_written, stdout);
      if (n == 0)
        {
          if (ferror(stdout))
            break;
          break;
        }
      total_written += n;
    }

  if (total_written > 0)
    dired_pos += total_written;
}

/* Output the string S, and increment DIRED_POS by its length.  */
#include <string.h>

static void
dired_outstring (char const *s)
{
  size_t len = 0;

  if (s == NULL)
    {
      dired_outbuf ("", 0);
      return;
    }

  len = strlen (s);
  dired_outbuf (s, len);
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
static void
push_current_dired_pos(struct obstack *obs)
{
  if (!obs || !dired)
    return;

  obstack_grow(obs, &dired_pos, (int)sizeof dired_pos);
}

/* With -R, this stack is used to help detect directory cycles.
   The device/inode pairs on this stack mirror the pairs in the
   active_dir_set hash table.  */
static struct obstack dev_ino_obstack;

/* Push a pair onto the device/inode stack.  */
static void
dev_ino_push(dev_t dev, ino_t ino)
{
    const int size = (int)sizeof(struct dev_ino);
    struct dev_ino *di;

    obstack_blank(&dev_ino_obstack, size);
    di = (struct dev_ino *)((char *)obstack_next_free(&dev_ino_obstack) - size);
    di->st_dev = dev;
    di->st_ino = ino;
}

/* Pop a dev/ino struct off the global dev_ino_obstack
   and return that struct.  */
static struct dev_ino
dev_ino_pop(void)
{
    const int dev_ino_size = (int)sizeof(struct dev_ino);
    affirm(dev_ino_size <= obstack_object_size(&dev_ino_obstack));
    obstack_blank_fast(&dev_ino_obstack, -dev_ino_size);
    return *(struct dev_ino *)obstack_next_free(&dev_ino_obstack);
}

static void
assert_matching_dev_ino (char const *name, struct dev_ino di)
{
  assure (name != NULL);
  MAYBE_UNUSED struct stat sb;
  assure (stat (name, &sb) == 0);
  assure (sb.st_dev == di.st_dev);
  assure (sb.st_ino == di.st_ino);
}

static char eolbyte = '\n';

/* Write to standard output PREFIX, followed by the quoting style and
   a space-separated list of the integers stored in OS all on one line.  */

static void
dired_dump_obstack(const char *prefix, struct obstack *os)
{
    size_t n_pos = obstack_object_size(os) / sizeof(dired_pos);
    if (n_pos == 0) {
        return;
    }

    const off_t *pos = obstack_finish(os);

    if (prefix == NULL) {
        prefix = "";
    }
    if (fputs(prefix, stdout) == EOF) {
        return;
    }

    for (size_t i = 0; i < n_pos; i++) {
        intmax_t p = pos[i];
        if (printf(" %jd", p) < 0) {
            return;
        }
    }

    putchar('\n');
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
static int do_stat(const char *path, struct stat *buf)
{
    return stat(path, buf);
}

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <errno.h>

static int do_lstat(const char *name, struct stat *st)
{
    if (name == NULL || st == NULL) {
        errno = EFAULT;
        return -1;
    }

    int ret;
    do {
        ret = lstat(name, st);
    } while (ret == -1 && errno == EINTR);

    return ret;
}

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

static inline int stat_for_mode(const char *path, struct stat *st)
{
    return stat(path, st);
}

#include <errno.h>
#include <sys/stat.h>

static int
stat_for_ino(const char *name, struct stat *st)
{
  if (name == NULL || st == NULL)
    {
      errno = EINVAL;
      return -1;
    }
  return stat(name, st);
}

#include <errno.h>
#include <sys/stat.h>

static int
fstat_for_ino (int fd, struct stat *st)
{
  if (st == NULL)
    {
      errno = EFAULT;
      return -1;
    }

  int ret;
  do
    {
      ret = fstat (fd, st);
    }
  while (ret == -1 && errno == EINTR);

  return ret;
}
#endif

/* Return the address of the first plain %b spec in FMT, or nullptr if
   there is no such spec.  %5b etc. do not match, so that user
   widths/flags are honored.  */

ATTRIBUTE_PURE
static char const *
first_percent_b (char const *fmt)
{
  if (fmt == NULL)
    return NULL;

  for (; *fmt; ++fmt)
    {
      if (*fmt != '%')
        continue;

      char next = fmt[1];

      if (next == 'b')
        return fmt;

      if (next == '%')
        ++fmt;
    }

  return NULL;
}

static char RFC3986[256];
static void
file_escape_init(void)
{
  enum { RFC3986_SIZE = 256 };
  for (unsigned int i = 0; i < RFC3986_SIZE; ++i)
    {
      unsigned int ch = i;
      unsigned char allowed =
        (unsigned char)(c_isalnum((int)ch) || ch == '~' || ch == '-' || ch == '.' || ch == '_');
      RFC3986[i] |= allowed;
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
  enum { MONTHS = 12 };
  int max_mon_width = 0;
  int mon_width[MONTHS];
  size_t mon_len[MONTHS];

  for (size_t i = 0; i < MONTHS; i++)
    {
      char const *abbr = nl_langinfo (ABMON_1 + (int)i);
      if (!abbr)
        return false;

      mon_len[i] = strnlen (abbr, ABFORMAT_SIZE);
      if (mon_len[i] == ABFORMAT_SIZE)
        return false;
      if (memchr (abbr, '%', mon_len[i]) != NULL)
        return false;

      memcpy (abmon[i], abbr, mon_len[i] + 1);

      mon_width[i] = mbswidth (abmon[i], MBSWIDTH_FLAGS);
      if (mon_width[i] < 0)
        return false;

      if (mon_width[i] > max_mon_width)
        max_mon_width = mon_width[i];
    }

  for (size_t i = 0; i < MONTHS; i++)
    {
      int fill = max_mon_width - mon_width[i];
      if ((size_t) fill >= ABFORMAT_SIZE - mon_len[i])
        return false;

      bool align_left = !c_isdigit ((unsigned char) abmon[i][0]);

      if (!align_left && fill > 0)
        {
          memmove (abmon[i] + fill, abmon[i], mon_len[i]);
          memset (abmon[i], ' ', (size_t) fill);
          abmon[i][mon_len[i] + fill] = '\0';
        }
      else
        {
          memset (abmon[i] + mon_len[i], ' ', (size_t) fill);
          abmon[i][mon_len[i] + fill] = '\0';
        }
    }

  return true;
#endif
}

/* Initialize ABFORMAT and USE_ABFORMAT.  */

static void
abformat_init(void)
{
  enum { FORMAT_COUNT = 2, MONTH_COUNT = 12 };

  const char *pb[FORMAT_COUNT] = { NULL, NULL };
  for (int recent = 0; recent < FORMAT_COUNT; recent++)
    pb[recent] = first_percent_b(long_time_format[recent]);

  if (pb[0] == NULL && pb[1] == NULL)
    return;

  char abmon[MONTH_COUNT][ABFORMAT_SIZE];
  if (!abmon_init(abmon))
    return;

  const int prefix_limit = (ABFORMAT_SIZE < INT_MAX) ? (int)ABFORMAT_SIZE : INT_MAX;

  for (int recent = 0; recent < FORMAT_COUNT; recent++)
    {
      const char *fmt = long_time_format[recent];
      const char *percent_b = pb[recent];

      for (int i = 0; i < MONTH_COUNT; i++)
        {
          char *nfmt = abformat[recent][i];
          int nbytes;

          if (percent_b == NULL)
            {
              nbytes = snprintf(nfmt, ABFORMAT_SIZE, "%s", fmt);
            }
          else
            {
              if (!(percent_b - fmt <= prefix_limit))
                return;

              int prefix_len = (int)(percent_b - fmt);
              nbytes = snprintf(nfmt, ABFORMAT_SIZE, "%.*s%s%s",
                                prefix_len, fmt, abmon[i], percent_b + 2);
            }

          if (nbytes < 0 || (size_t)nbytes >= (size_t)ABFORMAT_SIZE)
            return;
        }
    }

  use_abformat = true;
}

static size_t
dev_ino_hash(void const *x, size_t table_size)
{
    if (x == NULL || table_size == 0) {
        return 0;
    }

    struct dev_ino const *p = (struct dev_ino const *)x;
    uintmax_t ino = (uintmax_t)p->st_ino;
    return (size_t)(ino % (uintmax_t)table_size);
}

static bool
dev_ino_compare(void const *x, void const *y)
{
  if (x == NULL || y == NULL)
    return false;

  struct dev_ino const *a = (struct dev_ino const *)x;
  struct dev_ino const *b = (struct dev_ino const *)y;
  return PSAME_INODE(a, b);
}

#include <stdlib.h>

static void dev_ino_free(void *ptr)
{
  free(ptr);
}

/* Add the device/inode pair (P->st_dev/P->st_ino) to the set of
   active directories.  Return true if there is already a matching
   entry in the table.  */

static bool
visit_dir (dev_t dev, ino_t ino)
{
  struct dev_ino *ent = xmalloc (sizeof *ent);
  struct dev_ino *ent_from_table;

  ent->st_ino = ino;
  ent->st_dev = dev;

  ent_from_table = hash_insert (active_dir_set, ent);
  if (ent_from_table == NULL)
    xalloc_die ();

  {
    bool found_match = (ent_from_table != ent);
    if (found_match)
      free (ent);
    return found_match;
  }
}

static void
free_pending_ent (struct pending *p)
{
  if (p == NULL)
    return;

  if (p->name != NULL && p->name == p->realname)
    {
      free (p->name);
      p->name = NULL;
      p->realname = NULL;
    }
  else
    {
      if (p->name != NULL)
        {
          free (p->name);
          p->name = NULL;
        }
      if (p->realname != NULL)
        {
          free (p->realname);
          p->realname = NULL;
        }
    }

  free (p);
}

static bool is_colored(enum indicator_no type)
{
    size_t len = color_indicator[type].len;
    if (len == 0)
        return false;
    if (len > 2)
        return true;
    const char *s = color_indicator[type].string;
    if (s == NULL)
        return false;
    return (s[0] != '0') || (s[len - 1] != '0');
}

static void
restore_default_color (void)
{
  const int indices[2] = { C_LEFT, C_RIGHT };
  int i;
  for (i = 0; i < 2; ++i)
    put_indicator (&color_indicator[indices[i]]);
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
#if defined(SA_NOCLDSTOP) && (SA_NOCLDSTOP == 0)
    (void)signal(sig, SIG_IGN);
#endif
    if (interrupt_signal == 0) {
        interrupt_signal = sig;
    }
}

/* A SIGTSTP was received; arrange for the program to suspend itself.  */

static void stophandler(int sig)
{
    (void)sig;
#if !defined(SA_NOCLDSTOP) || !(SA_NOCLDSTOP)
    (void)signal(sig, stophandler);
#endif
    if (!interrupt_signal) {
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
      int sig = 0;
      int stops = 0;
      sigset_t oldset;
      int mask_set = 0;
      int can_raise = 1;

      if (used_color)
        restore_default_color ();

      if (fflush (stdout) == EOF)
        clearerr (stdout);

      if (sigprocmask (SIG_BLOCK, &caught_signals, &oldset) == 0)
        mask_set = 1;

      sig = interrupt_signal;
      stops = stop_signal_count;

      if (stops > 0)
        {
          stop_signal_count = stops - 1;
          sig = SIGSTOP;
        }
      else
        {
          if (sig != 0)
            {
              if (signal (sig, SIG_DFL) == SIG_ERR)
                {
                  can_raise = 0;
                  interrupt_signal = 0;
                }
            }
          else
            {
              if (mask_set)
                sigprocmask (SIG_SETMASK, &oldset, NULL);
              continue;
            }
        }

      if (can_raise && raise (sig) != 0 && stops == 0)
        interrupt_signal = 0;

      if (mask_set)
        sigprocmask (SIG_SETMASK, &oldset, NULL);
    }
}

/* Setup signal handlers if INIT is true,
   otherwise restore to the default.  */

static void
signal_setup(bool init)
{
  static const int sigv[] = {
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
  enum { nsigs = ARRAY_CARDINALITY(sigv) };

#if ! SA_NOCLDSTOP
  static bool caught_sig[nsigs];
#endif

  if (init)
    {
#if SA_NOCLDSTOP
      struct sigaction sa;
      (void) sigemptyset(&caught_signals);
      for (size_t i = 0; i < nsigs; i++)
        {
          struct sigaction current;
          if (sigaction(sigv[i], NULL, &current) == 0 && current.sa_handler != SIG_IGN)
            (void) sigaddset(&caught_signals, sigv[i]);
        }

      sa.sa_mask = caught_signals;
      sa.sa_flags = SA_RESTART;

      for (size_t i = 0; i < nsigs; i++)
        {
          int s = sigv[i];
          if (sigismember(&caught_signals, s) == 1)
            {
              sa.sa_handler = (s == SIGTSTP) ? stophandler : sighandler;
              (void) sigaction(s, &sa, NULL);
            }
        }
#else
      for (size_t i = 0; i < nsigs; i++)
        {
          int s = sigv[i];
          void (*old_handler)(int) = signal(s, SIG_IGN);
          if (old_handler == SIG_ERR)
            {
              caught_sig[i] = false;
              continue;
            }
          caught_sig[i] = (old_handler != SIG_IGN);
          if (caught_sig[i])
            {
              (void) signal(s, (s == SIGTSTP) ? stophandler : sighandler);
              (void) siginterrupt(s, 0);
            }
        }
#endif
    }
  else
    {
#if SA_NOCLDSTOP
      for (size_t i = 0; i < nsigs; i++)
        {
          int s = sigv[i];
          if (sigismember(&caught_signals, s) == 1)
            (void) signal(s, SIG_DFL);
        }
#else
      for (size_t i = 0; i < nsigs; i++)
        if (caught_sig[i])
          (void) signal(sigv[i], SIG_DFL);
#endif
    }
}

static inline void signal_init(void)
{
    (void)signal_setup(true);
}

static void signal_restore(void)
{
    (void)signal_setup(false);
}

int
main (int argc, char **argv)
{
  int i = 0;
  struct pending *thispend = nullptr;
  int n_files = 0;

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
    {
      parse_ls_color ();

      if (print_with_color)
        {
          tabsize = 0;
        }
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
        {
          check_symlink_mode = true;
        }
    }

  if (dereference == DEREF_UNDEFINED)
    {
      bool cond = (immediate_dirs
                   || indicator_style == classify
                   || format == long_format);
      dereference = cond ? DEREF_NEVER : DEREF_COMMAND_LINE_SYMLINK_TO_DIR;
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
  format_needs_type = (!format_needs_stat)
                      && (recursive || print_with_color || print_scontext
                          || directories_first
                          || (indicator_style != none));
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
      if (! hostname)
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
        {
          gobble_file (".", directory, NOT_AN_INODE_NUMBER, true, nullptr);
        }
      else
        {
          queue_directory (".", nullptr, true);
        }
    }
  else
    {
      for (int idx = i; idx < argc; idx++)
        {
          gobble_file (argv[idx], unknown, NOT_AN_INODE_NUMBER, true, nullptr);
        }
    }

  if (cwd_n_used)
    {
      sort_files ();
      if (!immediate_dirs)
        {
          extract_dirs_from_files (nullptr, true);
        }
    }

  if (cwd_n_used)
    {
      print_current_files ();
      if (pending_dirs)
        {
          dired_outbyte ('\n');
        }
    }
  else if (n_files <= 1 && pending_dirs && pending_dirs->next == nullptr)
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
      bool skip_restore = (color_indicator[C_LEFT].len == 2
                           && memcmp (color_indicator[C_LEFT].string, "\033[", 2) == 0
                           && color_indicator[C_RIGHT].len == 1
                           && color_indicator[C_RIGHT].string[0] == 'm');
      if (!skip_restore)
        {
          restore_default_color ();
        }

      fflush (stdout);

      signal_restore ();

      for (int j = stop_signal_count; j; j--)
        raise (SIGSTOP);
      {
        int j = interrupt_signal;
        if (j)
          raise (j);
      }
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
  if (spec == NULL)
    return -1;

  uintmax_t val = 0;
  int status = xstrtoumax (spec, NULL, 0, &val, "");

  switch (status)
    {
    case LONGINT_OK:
      {
        uintmax_t limit_ptrdiff = (uintmax_t) PTRDIFF_MAX;
        uintmax_t limit_size = (uintmax_t) SIZE_MAX;
        uintmax_t max_allowed = (limit_ptrdiff < limit_size) ? limit_ptrdiff : limit_size;
        return (val <= max_allowed) ? (ptrdiff_t) val : 0;
      }

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

#include <stdbool.h>
#include <unistd.h>
#include <stdatomic.h>

static bool
stdout_isatty(void)
{
  static atomic_int cached = ATOMIC_VAR_INIT(-1);
  int value = atomic_load_explicit(&cached, memory_order_acquire);
  if (value < 0)
    {
      int result = isatty(STDOUT_FILENO) ? 1 : 0;
      (void)atomic_compare_exchange_strong_explicit(&cached, &value, result,
                                                    memory_order_release,
                                                    memory_order_relaxed);
      value = atomic_load_explicit(&cached, memory_order_acquire);
    }
  return value != 0;
}

/* Set all the option flags according to the switches specified.
   Return the index of the first non-option argument.  */

static inline int parse_when_arg(char const *context, char const *arg) {
  return arg ? XARGMATCH(context, arg, when_args, when_types) : when_always;
}

static inline int need_line_length_calc(int format, bool use_color) {
  return (format == many_per_line || format == horizontal || format == with_commas || use_color);
}

static ptrdiff_t resolve_line_length(ptrdiff_t width_opt, int format, bool use_color) {
  ptrdiff_t linelen = width_opt;
  if (!need_line_length_calc(format, use_color))
    return linelen;
#ifdef TIOCGWINSZ
  if (linelen < 0) {
    struct winsize ws;
    if (stdout_isatty() && 0 <= ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) && 0 < ws.ws_col)
      linelen = (ws.ws_col <= MIN(PTRDIFF_MAX, SIZE_MAX)) ? ws.ws_col : 0;
  }
#endif
  if (linelen < 0) {
    char const *p = getenv("COLUMNS");
    if (p && *p) {
      linelen = decode_line_length(p);
      if (linelen < 0)
        error(0, 0, _("ignoring invalid width in environment variable COLUMNS: %s"), quote(p));
    }
  }
  return linelen;
}

static void configure_tabsize(int format, ptrdiff_t tabsize_opt_local) {
  if (format == many_per_line || format == horizontal || format == with_commas) {
    if (0 <= tabsize_opt_local) {
      tabsize = tabsize_opt_local;
    } else {
      tabsize = 8;
      char const *p = getenv("TABSIZE");
      if (p) {
        uintmax_t tmp;
        if (xstrtoumax(p, NULL, 0, &tmp, "") == LONGINT_OK && tmp <= SIZE_MAX) {
          tabsize = tmp;
        } else {
          error(0, 0, _("ignoring invalid tab size in environment variable TABSIZE: %s"), quote(p));
        }
      }
    }
  }
}

static void setup_quoting(int quoting_style_opt_local, int format_local, ptrdiff_t line_length_local) {
  int qs = quoting_style_opt_local;
  if (qs < 0)
    qs = getenv_quoting_style();
  if (qs < 0)
    qs = (ls_mode == LS_LS ? (stdout_isatty() ? shell_escape_quoting_style : -1) : escape_quoting_style);
  if (0 <= qs)
    set_quoting_style(NULL, qs);
  qs = get_quoting_style(NULL);

  align_variable_outer_quotes =
    ((format_local == long_format
      || ((format_local == many_per_line || format_local == horizontal) && line_length_local))
     && (qs == shell_quoting_style || qs == shell_escape_quoting_style || qs == c_maybe_quoting_style));

  filename_quoting_options = clone_quoting_options(NULL);
  if (qs == escape_quoting_style)
    set_char_quoting(filename_quoting_options, ' ', 1);
  if (file_type <= indicator_style) {
    char const *p;
    for (p = &"*=>@|"[indicator_style - file_type]; *p; p++)
      set_char_quoting(filename_quoting_options, *p, 1);
  }

  dirname_quoting_options = clone_quoting_options(NULL);
  set_char_quoting(dirname_quoting_options, ':', 1);
}

static void apply_block_size_env(bool kibibytes_specified_local) {
  if (!output_block_size) {
    char const *ls_block_size = getenv("LS_BLOCK_SIZE");
    human_options(ls_block_size, &human_output_opts, &output_block_size);
    if (ls_block_size || getenv("BLOCK_SIZE")) {
      file_human_output_opts = human_output_opts;
      file_output_block_size = output_block_size;
    }
    if (kibibytes_specified_local) {
      human_output_opts = 0;
      output_block_size = 1024;
    }
  }
}

static int decode_switches(int argc, char **argv) {
  char const *time_style_option = NULL;

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
        file_human_output_opts = human_output_opts = human_autoscale | human_SI | human_base_1024;
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
        width_opt = decode_line_length(optarg);
        if (width_opt < 0)
          error(LS_FAILURE, 0, "%s: %s", _("invalid line width"), quote(optarg));
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

      case 'F': {
        int i = parse_when_arg("--classify", optarg);
        if (i == when_always || (i == when_if_tty && stdout_isatty()))
          indicator_style = classify;
        break;
      }

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
        tabsize_opt = xnumtoumax(optarg, 0, 0, MIN(PTRDIFF_MAX, SIZE_MAX), "", _("invalid tab size"), LS_FAILURE, 0);
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

      case HIDE_OPTION: {
        struct ignore_pattern *hide = xmalloc(sizeof *hide);
        hide->pattern = optarg;
        hide->next = hide_patterns;
        hide_patterns = hide;
        break;
      }

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
        format_opt = XARGMATCH("--format", optarg, format_args, format_types);
        break;

      case FULL_TIME_OPTION:
        format_opt = long_format;
        time_style_option = "full-iso";
        break;

      case COLOR_OPTION: {
        int i = parse_when_arg("--color", optarg);
        print_with_color = (i == when_always || (i == when_if_tty && stdout_isatty()));
        break;
      }

      case HYPERLINK_OPTION: {
        int i = parse_when_arg("--hyperlink", optarg);
        print_hyperlink = (i == when_always || (i == when_if_tty && stdout_isatty()));
        break;
      }

      case INDICATOR_STYLE_OPTION:
        indicator_style = XARGMATCH("--indicator-style", optarg, indicator_style_args, indicator_style_types);
        break;

      case QUOTING_STYLE_OPTION:
        quoting_style_opt = XARGMATCH("--quoting-style", optarg, quoting_style_args, quoting_style_vals);
        break;

      case TIME_STYLE_OPTION:
        time_style_option = optarg;
        break;

      case SHOW_CONTROL_CHARS_OPTION:
        hide_control_chars_opt = false;
        break;

      case BLOCK_SIZE_OPTION: {
        enum strtol_error e = human_options(optarg, &human_output_opts, &output_block_size);
        if (e != LONGINT_OK)
          xstrtol_fatal(e, oi, 0, long_options, optarg);
        file_human_output_opts = human_output_opts;
        file_output_block_size = output_block_size;
        break;
      }

      case SI_OPTION:
        file_human_output_opts = human_output_opts = human_autoscale | human_SI;
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
      case_GETOPT_VERSION_CHAR(PROGRAM_NAME, AUTHORS);

      default:
        usage(LS_FAILURE);
    }
  }

  apply_block_size_env(kibibytes_specified);

  format = (0 <= format_opt ? format_opt
           : ls_mode == LS_LS ? (stdout_isatty() ? many_per_line : one_per_line)
           : ls_mode == LS_MULTI_COL ? many_per_line
           : long_format);

  ptrdiff_t linelen = resolve_line_length(width_opt, format, print_with_color);
  line_length = linelen < 0 ? 80 : linelen;

  max_idx = line_length / MIN_COLUMN_WIDTH;
  max_idx += line_length % MIN_COLUMN_WIDTH != 0;

  configure_tabsize(format, tabsize_opt);

  qmark_funny_chars = (hide_control_chars_opt < 0 ? (ls_mode == LS_LS && stdout_isatty()) : hide_control_chars_opt);

  setup_quoting(quoting_style_opt, format, line_length);

  dired = dired && (format == long_format) && !print_hyperlink;

  if (dired && eolbyte == 0)
    error(LS_FAILURE, 0, _("--dired and --zero are incompatible"));

  sort_type = (0 <= sort_opt ? sort_opt : (format != long_format && explicit_time) ? sort_time : sort_name);

  if (format == long_format) {
    char const *style = time_style_option;
    static char const posix_prefix[] = "posix-";

    if (!style) {
      style = getenv("TIME_STYLE");
      if (!style)
        style = "locale";
    }

    while (STREQ_LEN(style, posix_prefix, sizeof posix_prefix - 1)) {
      if (!hard_locale(LC_TIME))
        return optind;
      style += sizeof posix_prefix - 1;
    }

    if (*style == '+') {
      char *style_copy = xstrdup(style);
      char const *p0 = style_copy + 1;
      char *p0nl = strchr(style_copy + 1, '\n');
      char const *p1 = p0;
      if (p0nl) {
        if (strchr(p0nl + 1, '\n')) {
          error(LS_FAILURE, 0, _("invalid time style format %s"), quote(p0));
        }
        *p0nl++ = '\0';
        p1 = p0nl;
      }
      long_time_format[0] = p0;
      long_time_format[1] = p1;
    } else {
      switch (x_timestyle_match(style, true, time_style_args, (char const *) time_style_types, sizeof(*time_style_types), LS_FAILURE)) {
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
              long_time_format[i] = dcgettext(NULL, long_time_format[i], LC_TIME);
          }
          break;
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

static bool
get_funky_string(char **dest, char const **src, bool equals_end, size_t *output_count)
{
  if (!dest || !src || !*dest || !*src || !output_count)
    return false;

  char const *p = *src;
  char *q = *dest;

  size_t count = 0;
  unsigned int num = 0;

  enum { ST_GND, ST_BACKSLASH, ST_OCTAL, ST_HEX, ST_CARET, ST_END, ST_ERROR } state = ST_GND;

  while (state < ST_END)
    {
      switch (state)
        {
        case ST_GND:
          {
            unsigned char c = (unsigned char)*p;
            if (c == ':' || c == '\0' || (equals_end && c == '='))
              {
                state = ST_END;
              }
            else if (c == '\\')
              {
                state = ST_BACKSLASH;
                ++p;
              }
            else if (c == '^')
              {
                state = ST_CARET;
                ++p;
              }
            else
              {
                *q++ = (char)c;
                ++p;
                ++count;
              }
          }
          break;

        case ST_BACKSLASH:
          {
            unsigned char c = (unsigned char)*p;
            if (c >= '0' && c <= '7')
              {
                state = ST_OCTAL;
                num = c - '0';
              }
            else if (c == 'x' || c == 'X')
              {
                state = ST_HEX;
                num = 0;
              }
            else if (c == 'a')
              {
                num = '\a';
              }
            else if (c == 'b')
              {
                num = '\b';
              }
            else if (c == 'e')
              {
                num = '\x1b';
              }
            else if (c == 'f')
              {
                num = '\f';
              }
            else if (c == 'n')
              {
                num = '\n';
              }
            else if (c == 'r')
              {
                num = '\r';
              }
            else if (c == 't')
              {
                num = '\t';
              }
            else if (c == 'v')
              {
                num = '\v';
              }
            else if (c == '?')
              {
                num = '\x7f';
              }
            else if (c == '_')
              {
                num = ' ';
              }
            else if (c == '\0')
              {
                state = ST_ERROR;
              }
            else
              {
                num = c;
              }

            if (state == ST_BACKSLASH)
              {
                *q++ = (char)num;
                ++count;
                state = ST_GND;
              }
            ++p;
          }
          break;

        case ST_OCTAL:
          if (*p < '0' || *p > '7')
            {
              *q++ = (char)num;
              ++count;
              state = ST_GND;
            }
          else
            {
              num = (num << 3) + (unsigned)(*p - '0');
              ++p;
            }
          break;

        case ST_HEX:
          {
            int v = -1;
            unsigned char c = (unsigned char)*p;
            if (c >= '0' && c <= '9')
              v = c - '0';
            else if (c >= 'a' && c <= 'f')
              v = c - 'a' + 10;
            else if (c >= 'A' && c <= 'F')
              v = c - 'A' + 10;

            if (v >= 0)
              {
                num = (num << 4) + (unsigned)v;
                ++p;
              }
            else
              {
                *q++ = (char)num;
                ++count;
                state = ST_GND;
              }
          }
          break;

        case ST_CARET:
          state = ST_GND;
          if (*p >= '@' && *p <= '~')
            {
              *q++ = (char)(*p & 037);
              ++p;
              ++count;
            }
          else if (*p == '?')
            {
              *q++ = '\x7f';
              ++p;
              ++count;
            }
          else
            {
              state = ST_ERROR;
            }
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
known_term_type(void)
{
  const char *term = getenv("TERM");
  if (term == NULL || *term == '\0')
    return false;

  const char *p = G_line;
  const char *const end = G_line + sizeof(G_line);

  while (p < end)
  {
    const char *s = p;
    while (s < end && *s != '\0')
      s++;
    if (s == end)
      break;

    size_t len = (size_t)(s - p);
    if (len >= 5 &&
        p[0] == 'T' && p[1] == 'E' && p[2] == 'R' && p[3] == 'M' && p[4] == ' ')
    {
      const char *pattern = p + 5;
      if (fnmatch(pattern, term, 0) == 0)
        return true;
    }

    p = s + 1;
  }

  return false;
}

static void free_color_ext_list_and_reset(void)
{
  struct color_ext_type *e = color_ext_list;
  while (e != NULL)
    {
      struct color_ext_type *next = e->next;
      free (e);
      e = next;
    }
  color_ext_list = NULL;
}

static void postprocess_color_ext_list(void)
{
  struct color_ext_type *e1;
  for (e1 = color_ext_list; e1 != NULL; e1 = e1->next)
    {
      struct color_ext_type *e2;
      bool case_ignored = false;

      for (e2 = e1->next; e2 != NULL; e2 = e2->next)
        {
          if (e2->ext.len < SIZE_MAX && e1->ext.len == e2->ext.len)
            {
              if (memcmp (e1->ext.string, e2->ext.string, e1->ext.len) == 0)
                {
                  e2->ext.len = SIZE_MAX;
                }
              else if (c_strncasecmp (e1->ext.string, e2->ext.string, e1->ext.len) == 0)
                {
                  if (case_ignored)
                    {
                      e2->ext.len = SIZE_MAX;
                    }
                  else if (e1->seq.len == e2->seq.len
                           && memcmp (e1->seq.string, e2->seq.string, e1->seq.len) == 0)
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
    }
}

static void
parse_ls_color (void)
{
  char const *p;
  char *buf;
  char label0 = '\0', label1 = '\0';
  struct color_ext_type *ext;

  p = getenv ("LS_COLORS");
  if (p == NULL || *p == '\0')
    {
      char const *colorterm = getenv ("COLORTERM");
      if (!(colorterm && *colorterm) && ! known_term_type ())
        print_with_color = false;
      return;
    }

  ext = NULL;
  buf = color_buf = xstrdup (p);

  enum parse_state state = PS_START;

  for (;;)
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

              state = (get_funky_string (&buf, &p, true, &ext->ext.len)
                       ? PS_4 : PS_FAIL);
              break;

            case '\0':
              state = PS_DONE;
              break;

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
            {
              state = PS_FAIL;
            }
          break;

        case PS_3:
          state = PS_FAIL;
          if (*(p++) == '=')
            {
              size_t count = ARRAY_CARDINALITY (indicator_name);
              for (size_t i = 0; i < count; i++)
                {
                  if (label0 == indicator_name[i][0]
                      && label1 == indicator_name[i][1])
                    {
                      color_indicator[i].string = buf;
                      state = (get_funky_string (&buf, &p, false,
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
              state = (get_funky_string (&buf, &p, false, &ext->seq.len)
                       ? PS_START : PS_FAIL);
            }
          else
            {
              state = PS_FAIL;
            }
          break;

        case PS_FAIL:
        case PS_DONE:
        default:
          break;
        }

      if (state == PS_FAIL || state == PS_DONE)
        break;
    }

  if (state == PS_FAIL)
    {
      error (0, 0, _("unparsable value for LS_COLORS environment variable"));
      free (color_buf);
      color_buf = NULL;
      free_color_ext_list_and_reset ();
      print_with_color = false;
    }
  else
    {
      postprocess_color_ext_list ();
    }

  if (color_indicator[C_LINK].len == 6
      && !STRNCMP_LIT (color_indicator[C_LINK].string, "target"))
    color_symlink_as_referent = true;
}

/* Return the quoting style specified by the environment variable
   QUOTING_STYLE if set and valid, -1 otherwise.  */

static int getenv_quoting_style(void)
{
    const char *q_style = getenv("QUOTING_STYLE");
    if (q_style == NULL)
        return -1;

    int idx = ARGMATCH(q_style, quoting_style_args, quoting_style_vals);
    if (idx >= 0)
        return quoting_style_vals[idx];

    error(0, 0,
          _("ignoring invalid value of environment variable QUOTING_STYLE: %s"),
          quote(q_style));
    return -1;
}

/* Set the exit status to report a failure.  If SERIOUS, it is a
   serious failure; otherwise, it is merely a minor problem.  */

static void set_exit_status(bool serious)
{
    if (serious) {
        exit_status = LS_FAILURE;
        return;
    }

    if (exit_status == EXIT_SUCCESS) {
        exit_status = LS_MINOR_PROBLEM;
    }
}

/* Assuming a failure is serious if SERIOUS, use the printf-style
   MESSAGE to report the failure to access a file named FILE.  Assume
   errno is set appropriately for the failure.  */

static void
file_failure(bool serious, char const *message, char const *file)
{
  int saved_errno = errno;
  char const *quoted_file = quoteaf(file);
  error(0, saved_errno, message, quoted_file);
  set_exit_status(serious);
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

static char *dup_or_null(const char *s)
{
  return s ? xstrdup(s) : NULL;
}

static void queue_directory(const char *name, const char *realname, bool command_line_arg)
{
  struct pending *node = xmalloc(sizeof *node);
  node->realname = dup_or_null(realname);
  node->name = dup_or_null(name);
  node->command_line_arg = command_line_arg;
  node->next = pending_dirs;
  pending_dirs = node;
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
      struct stat dir_stat;
      int fd = dirfd (dirp);
      int r = (0 <= fd) ? fstat_for_ino (fd, &dir_stat)
                        : stat_for_ino (name, &dir_stat);

      if (r < 0)
        {
          file_failure (command_line_arg,
                        _("cannot determine device and inode of %s"), name);
          closedir (dirp);
          return;
        }

      if (visit_dir (dir_stat.st_dev, dir_stat.st_ino))
        {
          error (0, 0, _("%s: not listing already-listed directory"),
                 quotef (name));
          closedir (dirp);
          set_exit_status (true);
          return;
        }

      dev_ino_push (dir_stat.st_dev, dir_stat.st_ino);
    }

  clear_files ();

  if (recursive || print_dir_name)
    {
      if (!first)
        dired_outbyte ('\n');
      first = false;
      dired_indent ();

      char *absolute_name = NULL;
      if (print_hyperlink)
        {
          absolute_name = canonicalize_filename_mode (name, CAN_MISSING);
          if (!absolute_name)
            file_failure (command_line_arg, _("error canonicalizing %s"), name);
        }

      quote_name (realname ? realname : name,
                  dirname_quoting_options, -1, NULL, true,
                  &subdired_obstack, absolute_name);

      free (absolute_name);

      dired_outstring (":\n");
    }

  for (;;)
    {
      errno = 0;
      next = readdir (dirp);
      if (next)
        {
          if (!file_ignored (next->d_name))
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
          int saved_errno = errno;
          if (saved_errno == 0)
            break;
#if ! (2 < __GLIBC__ + (3 <= __GLIBC_MINOR__))
          if (saved_errno == ENOENT)
            break;
#endif
          file_failure (command_line_arg, _("reading directory %s"), name);
          if (saved_errno != EOVERFLOW)
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

  if (format == long_format || print_block_size)
    {
      char buf[LONGEST_HUMAN_READABLE + 3];
      char *p = human_readable (total_blocks, buf + 1, human_output_opts,
                                ST_NBLOCKSIZE, output_block_size);
      char *pend = p + strlen (p);
      size_t len;
      *--p = ' ';
      *pend++ = eolbyte;
      len = (size_t)(pend - p);
      dired_indent ();
      dired_outstring (_("total"));
      dired_outbuf (p, len);
    }

  if (cwd_n_used)
    print_current_files ();
}

/* Add 'pattern' to the list of patterns for which files that match are
   not listed.  */

static void
add_ignore_pattern(char const *pattern)
{
    struct ignore_pattern *new_node = xmalloc(sizeof *new_node);
    *new_node = (struct ignore_pattern){
        .pattern = pattern,
        .next = ignore_patterns
    };
    ignore_patterns = new_node;
}

/* Return true if one of the PATTERNS matches FILE.  */

static bool
patterns_match (struct ignore_pattern const *patterns, char const *file)
{
  struct ignore_pattern const *p;

  if (!file || !patterns)
    return false;

  for (p = patterns; p; p = p->next)
    {
      char const *pattern = p->pattern;
      int rc;

      if (!pattern)
        continue;

      rc = fnmatch (pattern, file, FNM_PERIOD);
      if (rc == 0)
        return true;
    }
  return false;
}

/* Return true if FILE should be ignored.  */

static bool
file_ignored(char const *name)
{
    if (!name) {
        return false;
    }

    bool is_default = (ignore_mode == IGNORE_DEFAULT);
    bool is_minimal = (ignore_mode == IGNORE_MINIMAL);

    if (!is_minimal && name[0] == '.') {
        if (is_default) {
            return true;
        }
        if (name[1] == '\0') {
            return true;
        }
        if (name[1] == '.' && name[2] == '\0') {
            return true;
        }
    }

    if (is_default && patterns_match(hide_patterns, name)) {
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

static uintmax_t
unsigned_file_size(off_t size)
{
    if (size >= 0) {
        return (uintmax_t) size;
    }
    const uintmax_t range = (uintmax_t) OFF_T_MAX - OFF_T_MIN + 1;
    return (uintmax_t) size + range;
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
#include <errno.h>
#include <stdbool.h>

static int get_unsupported_errno(void)
{
#if defined(ENOTSUP)
    return ENOTSUP;
#elif defined(EOPNOTSUPP)
    return EOPNOTSUPP;
#elif defined(ENOSYS)
    return ENOSYS;
#else
    return EINVAL;
#endif
}

static bool has_capability(char const *name)
{
    (void)name;
    errno = get_unsupported_errno();
    return false;
}
#endif

/* Enter and remove entries in the table 'cwd_file'.  */

static void
free_ent(struct fileinfo *f)
{
  if (f == NULL)
    return;

  free(f->name);
  f->name = NULL;

  free(f->linkname);
  f->linkname = NULL;

  free(f->absolute_name);
  f->absolute_name = NULL;

  if (f->scontext != UNKNOWN_SECURITY_CONTEXT)
  {
    aclinfo_scontext_free(f->scontext);
    f->scontext = UNKNOWN_SECURITY_CONTEXT;
  }
}

/* Empty the table of files.  */
static void reset_listing_state(void)
{
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

static void
clear_files (void)
{
  idx_t used = cwd_n_used;

  if (used == 0)
    {
      reset_listing_state();
      return;
    }

  if (sorted_file)
    {
      for (idx_t i = 0; i < used; i++)
        {
          struct fileinfo *f = sorted_file[i];
          if (f)
            free_ent (f);
          sorted_file[i] = NULL;
        }
    }

  cwd_n_used = 0;
  reset_listing_state();
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

  if (f->stat_ok
      && unsupported_scontext
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
  int result = file_has_aclinfo (file, ai, flags);
  int err = errno;

  if (f->stat_ok && result <= 0)
    {
      int request_scontext = (flags & ACL_GET_SCONTEXT) != 0;
      int should_cache = (!acl_errno_valid (err)
                          && (!request_scontext
                              || !acl_errno_valid (ai->scontext_err)));

      if (should_cache)
        {
          unsupported_return = result;
          unsupported_scontext = ai->scontext;
          unsupported_scontext_err = ai->scontext_err;
          unsupported_device = f->stat.st_dev;
        }
    }

  return result;
}

/* Cache has_capability failure, when it's trivial to do.
   Like has_capability, but when F's st_dev says it's on a file
   system lacking capability support, return 0 with ENOTSUP immediately.  */
static bool
has_capability_cache (char const *file, struct fileinfo *f)
{
  static bool unsupported_cached;
  static dev_t unsupported_device;

  const bool has_stat = f->stat_ok;
  dev_t dev = 0;
  if (has_stat)
    dev = f->stat.st_dev;

  if (has_stat && unsupported_cached && dev == unsupported_device)
    {
      errno = ENOTSUP;
      return false;
    }

  bool supported = has_capability (file);

  if (has_stat && !supported && !acl_errno_valid (errno))
    {
      unsupported_cached = true;
      unsupported_device = dev;
    }

  return supported;
}

static bool
needs_quoting (char const *name)
{
  char buf[2];
  size_t quoted_len;
  size_t name_len;

  if (!name)
    return false;

  quoted_len = quotearg_buffer (buf, sizeof buf, name, (size_t) -1,
                                filename_quoting_options);
  name_len = strlen (name);

  return (name_len != quoted_len) || (name[0] != buf[0]);
}

/* Add a file to the current table of files.
   Verify that the file exists, and print an error message if it does not.
   Return the number of blocks that the file occupies.  */
static uintmax_t
gobble_file (char const *name, enum filetype type, ino_t inode,
             bool command_line_arg, char const *dirname)
{
  uintmax_t blocks = 0;
  struct fileinfo *f;

  affirm (! command_line_arg || inode == NOT_AN_INODE_NUMBER);

  if (cwd_n_used == cwd_n_alloc)
    cwd_file = xpalloc (cwd_file, &cwd_n_alloc, 1, -1, sizeof *cwd_file);

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
        cwd_some_quoted = 1;
    }

  bool need_stat_for_type_unknown = (format_needs_type && type == unknown);
  bool need_stat_for_color = ((type == directory || type == unknown) && print_with_color
                              && (is_colored (C_OTHER_WRITABLE)
                                  || is_colored (C_STICKY)
                                  || is_colored (C_STICKY_OTHER_WRITABLE)));
  bool need_stat_for_symlink = ((print_inode || format_needs_type)
                                && (type == symbolic_link || type == unknown)
                                && (dereference == DEREF_ALWAYS
                                    || color_symlink_as_referent || check_symlink_mode));
  bool need_stat_for_exec = ((type == normal || type == unknown)
                             && (indicator_style == classify
                                 || (print_with_color && (is_colored (C_EXEC)
                                                          || is_colored (C_SETUID)
                                                          || is_colored (C_SETGID)))));
  bool need_stat_inode_unknown = (print_inode && inode == NOT_AN_INODE_NUMBER);
  bool check_stat =
     (command_line_arg
      || print_hyperlink
      || format_needs_stat
      || need_stat_for_type_unknown
      || need_stat_for_color
      || need_stat_for_symlink
      || need_stat_inode_unknown
      || need_stat_for_exec);

  char const *full_name = name;
  bool need_full_name = (check_stat || print_scontext || format_needs_capability)
                        && name[0] != '/' && dirname;
  if (need_full_name)
    {
      char *p = alloca (strlen (name) + strlen (dirname) + 2);
      attach (p, dirname, name);
      full_name = p;
    }

  bool do_deref;

  if (!check_stat)
    {
      do_deref = (dereference == DEREF_ALWAYS);
    }
  else
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
          do_deref = true;
          break;

        case DEREF_COMMAND_LINE_ARGUMENTS:
        case DEREF_COMMAND_LINE_SYMLINK_TO_DIR:
          if (command_line_arg)
            {
              bool need_lstat;
              err = do_stat (full_name, &f->stat);
              do_deref = true;

              if (dereference == DEREF_COMMAND_LINE_ARGUMENTS)
                break;

              need_lstat = (err < 0
                            ? (errno == ENOENT || errno == ELOOP)
                            : ! S_ISDIR (f->stat.st_mode));
              if (!need_lstat)
                break;
            }
          FALLTHROUGH;

        case DEREF_NEVER:
          err = do_lstat (full_name, &f->stat);
          do_deref = false;
          break;

        case DEREF_UNDEFINED: default:
          unreachable ();
        }

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

  if (type == directory && command_line_arg && !immediate_dirs)
    f->filetype = type = arg_directory;

  bool get_scontext = ((format == long_format) || print_scontext);
  bool check_capability = (format_needs_capability && (type == normal));

  if (get_scontext || check_capability)
    {
      struct aclinfo ai;
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
      any_has_acl |= f->acl_type != ACL_T_NONE;

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
is_directory(const struct fileinfo *f)
{
    if (f == NULL) {
        return false;
    }

    switch (f->filetype) {
        case directory:
        case arg_directory:
            return true;
        default:
            return false;
    }
}

/* Return true if F refers to a (symlinked) directory.  */
static bool
is_linked_directory(const struct fileinfo *f)
{
    if (f == NULL) {
        return false;
    }

    switch (f->filetype) {
        case directory:
        case arg_directory:
            return true;
        default:
            break;
    }

    return S_ISDIR(f->linkmode) != 0;
}

/* Put the name of the file that FILENAME is a symbolic link to
   into the LINKNAME field of 'f'.  COMMAND_LINE_ARG indicates whether
   FILENAME is a command-line argument.  */

static void
get_link_name (char const *filename, struct fileinfo *f, bool command_line_arg)
{
  off_t sz = f->stat.st_size;
  size_t hint = (sz > 0) ? (size_t) sz : 0;

  f->linkname = areadlink_with_size (filename, hint);
  if (f->linkname == NULL)
    file_failure (command_line_arg, _("cannot read symbolic link %s"), filename);
}

/* Return true if the last component of NAME is '.' or '..'
   This is so we don't try to recurse on '././././. ...' */

static bool
basename_is_dot_or_dotdot (char const *name)
{
  if (name == NULL || *name == '\0')
    return false;

  char const *base = last_component (name);
  if (base == NULL || *base == '\0')
    return false;

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
extract_dirs_from_files (char const *dirname, bool command_line_arg)
{
  idx_t i, j;
  bool ignore_dot_and_dot_dot = (dirname != NULL);

  if (dirname != NULL && LOOP_DETECT)
    {
      queue_directory (NULL, dirname, false);
    }

  for (i = cwd_n_used; i > 0; i--)
    {
      struct fileinfo *f = sorted_file[i - 1];

      if (!is_directory (f))
        continue;

      if (ignore_dot_and_dot_dot && basename_is_dot_or_dotdot (f->name))
        continue;

      if (dirname == NULL || f->name[0] == '/')
        {
          queue_directory (f->name, f->linkname, command_line_arg);
        }
      else
        {
          char *name = file_name_concat (dirname, f->name, NULL);
          queue_directory (name, f->linkname, command_line_arg);
          free (name);
        }

      if (f->filetype == arg_directory)
        free_ent (f);
    }

  for (i = 0, j = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
      if (f->filetype != arg_directory)
        {
          sorted_file[j++] = f;
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
  int diff;
  errno = 0;
  diff = strcoll (a, b);
  if (errno != 0)
    {
      int saved_errno = errno;
      char const *qa = quote_n (0, a);
      char const *qb = quote_n (1, b);
      error (0, saved_errno, _("cannot compare file names %s and %s"), qa, qb);
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
  int a_is_dir;
  int b_is_dir;

  if (!a || !b)
    return 0;

  a_is_dir = is_linked_directory (a) ? 1 : 0;
  b_is_dir = is_linked_directory (b) ? 1 : 0;

  if (b_is_dir != a_is_dir)
    return b_is_dir ? 1 : -1;

  return cmp ? cmp (a, b) : 0;
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
  if (!a || !b || !cmp)
    return 0;

  int diff = timespec_cmp (get_stat_ctime (&b->stat),
                           get_stat_ctime (&a->stat));
  if (diff)
    return diff;

  char const *an = a->name ? a->name : "";
  char const *bn = b->name ? b->name : "";
  return cmp (an, bn);
}

static int
cmp_mtime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (!a || !b)
    return 0;

  int diff = timespec_cmp(get_stat_mtime(&b->stat),
                          get_stat_mtime(&a->stat));
  if (diff != 0)
    return diff;

  const char *an = a->name ? a->name : "";
  const char *bn = b->name ? b->name : "";
  int (*name_cmp)(char const *, char const *) = cmp ? cmp : strcmp;

  return name_cmp(an, bn);
}

static int
cmp_atime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == b)
    return 0;

  if (!a)
    return b ? 1 : 0;

  if (!b)
    return -1;

  int result = timespec_cmp (get_stat_atime (&b->stat),
                             get_stat_atime (&a->stat));
  if (result != 0)
    return result;

  if (!cmp)
    return 0;

  const char *an = a->name ? a->name : "";
  const char *bn = b->name ? b->name : "";

  return cmp (an, bn);
}

static int
cmp_btime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == NULL || b == NULL || cmp == NULL)
    return 0;

  int diff = timespec_cmp (get_stat_btime (&b->stat),
                           get_stat_btime (&a->stat));
  if (diff != 0)
    return diff;

  return cmp (a->name, b->name);
}

static int off_cmp(off_t a, off_t b)
{
    if (a < b) {
        return -1;
    }
    if (a > b) {
        return 1;
    }
    return 0;
}

static int
cmp_size(const struct fileinfo *a, const struct fileinfo *b,
         int (*cmp)(const char *, const char *))
{
    int diff;

    if (a == NULL || b == NULL || cmp == NULL) {
        return 0;
    }
    if (a->name == NULL || b->name == NULL) {
        return 0;
    }

    diff = off_cmp(b->stat.st_size, a->stat.st_size);
    if (diff != 0) {
        return diff;
    }
    return cmp(a->name, b->name);
}

static int
cmp_name(struct fileinfo const *a, struct fileinfo const *b,
         int (*cmp)(char const *, char const *))
{
  if (a == b)
    return 0;

  if (cmp == NULL)
    return 0;

  if (a == NULL || b == NULL)
    return (a != NULL) - (b != NULL);

  const char *an = a->name;
  const char *bn = b->name;

  if (an == NULL || bn == NULL)
    return (an != NULL) - (bn != NULL);

  return cmp(an, bn);
}

/* Compare file extensions.  Files with no extension are 'smallest'.
   If extensions are the same, compare by file names instead.  */

static int
cmp_extension (struct fileinfo const *a, struct fileinfo const *b,
               int (*cmp) (char const *, char const *))
{
  if (!cmp) {
    return 0;
  }

  const char *name1 = (a && a->name) ? a->name : "";
  const char *name2 = (b && b->name) ? b->name : "";

  const char *ext1 = strrchr(name1, '.');
  const char *ext2 = strrchr(name2, '.');

  int diff = cmp(ext1 ? ext1 : "", ext2 ? ext2 : "");
  if (diff != 0) {
    return diff;
  }
  return cmp(name1, name2);
}

/* Return the (cached) screen width,
   for the NAME associated with the passed fileinfo F.  */

static size_t
fileinfo_name_width (struct fileinfo const *f)
{
  if (f->width != 0)
    return f->width;

  return quote_name_width (f->name, filename_quoting_options, f->quoted);
}

static int
cmp_width(const struct fileinfo *a, const struct fileinfo *b,
          int (*cmp)(const char *, const char *))
{
    if (a == b) {
        return 0;
    }

    int width_a = fileinfo_name_width(a);
    int width_b = fileinfo_name_width(b);

    if (width_a < width_b) {
        return -1;
    }
    if (width_a > width_b) {
        return 1;
    }

    return cmp(a->name, b->name);
}

static int sort_ctime(const void *a, const void *b)
{
    return cmp_ctime(a, b);
}

static int rev_sort_ctime(const void *a, const void *b)
{
    return cmp_ctime(b, a);
}static int ctime_cmp(const void *a, const void *b)
{
    if (a == NULL || b == NULL)
        return (a != NULL) - (b != NULL);

    const void *const *pa = (const void *const *)a;
    const void *const *pb = (const void *const *)b;

    if (pa == NULL || pb == NULL)
        return (pa != NULL) - (pb != NULL);

    const void *va = *pa;
    const void *vb = *pb;

    if (va == NULL || vb == NULL)
        return (va != NULL) - (vb != NULL);

    int diff = cmp_ctime(va, vb);

    if (diff > 0)
        return 1;
    if (diff < 0)
        return -1;
    return 0;
}

static int rev_ctime_cmp(const void *a, const void *b)
{
    return ctime_cmp(b, a);
}#include <stddef.h>
#include <stdlib.h>
#include <string.h>

static int ctime_cmp(const void *pa, const void *pb)
{
    const void *a = NULL;
    const void *b = NULL;

    if (pa == NULL || pb == NULL) {
        return 0;
    }

    memcpy(&a, pa, sizeof a);
    memcpy(&b, pb, sizeof b);

    return cmp_ctime(a, b);
}

void ctime_sort(void *base, size_t nmemb)
{
    if (base == NULL || nmemb < 2) {
        return;
    }

    qsort(base, nmemb, sizeof(void *), ctime_cmp);
}#include <stddef.h>
#include <stdlib.h>

extern int cmp_ctime(const void *a, const void *b);

static int cmp_ctime_desc(const void *a, const void *b) {
    int r = cmp_ctime(a, b);
    return (r > 0) ? -1 : (r < 0) ? 1 : 0;
}

static int validate_qsort_args(const void *base, size_t nmemb, size_t size) {
    if (!base) {
        return -1;
    }
    if (nmemb > 0 && size == 0) {
        return -1;
    }
    return 0;
}

int ctime_sort(void *base, size_t nmemb, size_t size) {
    if (nmemb < 2) {
        return 0;
    }
    if (validate_qsort_args(base, nmemb, size) != 0) {
        return -1;
    }
    qsort(base, nmemb, size, cmp_ctime);
    return 0;
}

int rev_ctime_sort(void *base, size_t nmemb, size_t size) {
    if (nmemb < 2) {
        return 0;
    }
    if (validate_qsort_args(base, nmemb, size) != 0) {
        return -1;
    }
    qsort(base, nmemb, size, cmp_ctime_desc);
    return 0;
}

int sort_ctime(void *base, size_t nmemb, size_t size) {
    return ctime_sort(base, nmemb, size);
}

int sort_by_ctime(void *base, size_t nmemb, size_t size) {
    return ctime_sort(base, nmemb, size);
}

int ctime_sort_desc(void *base, size_t nmemb, size_t size) {
    return rev_ctime_sort(base, nmemb, size);
}

int sort_ctime_reverse(void *base, size_t nmemb, size_t size) {
    return rev_ctime_sort(base, nmemb, size);
}DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#include <stddef.h>
#include <stdlib.h>

extern int cmp_ctime(const void *, const void *);

static int reverse_cmp_ctime(const void *a, const void *b) {
    int r = cmp_ctime(a, b);
    if (r > 0) return -1;
    if (r < 0) return 1;
    return 0;
}

static void safe_qsort(void *base, size_t nmemb, size_t size, int (*cmp)(const void *, const void *)) {
    if (!base || !cmp || size == 0 || nmemb < 2) {
        return;
    }
    qsort(base, nmemb, size, cmp);
}

void sort_ctime(void *base, size_t nmemb, size_t size) {
    safe_qsort(base, nmemb, size, cmp_ctime);
}

void rsort_ctime(void *base, size_t nmemb, size_t size) {
    safe_qsort(base, nmemb, size, reverse_cmp_ctime);
}struct ctime;
int cmp_ctime(const struct ctime *, const struct ctime *);

static int cmp_ctime_cmp(const void *a, const void *b)
{
    const struct ctime *const lhs = (const struct ctime *)a;
    const struct ctime *const rhs = (const struct ctime *)b;
    return cmp_ctime(lhs, rhs);
}

static int cmp_ctime_cmp_s(const void *a, const void *b, void *ctx)
{
    (void)ctx;
    const struct ctime *const lhs = (const struct ctime *)a;
    const struct ctime *const rhs = (const struct ctime *)b;
    return cmp_ctime(lhs, rhs);
}extern int cmp_ctime(const void *a, const void *b);

static int compare_ctime(const void *a, const void *b)
{
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return -1;
    }
    if (b == NULL) {
        return 1;
    }
    return cmp_ctime(a, b);
}

static int rev_ctime(const void *a, const void *b)
{
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return 1;
    }
    if (b == NULL) {
        return -1;
    }
    int r = cmp_ctime(a, b);
    if (r < 0) {
        return 1;
    }
    if (r > 0) {
        return -1;
    }
    return 0;
}
DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)extern int cmp_mtime(const void *a, const void *b);

static int cmp_mtime_safe(const void *a, const void *b) {
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return -1;
    }
    if (b == NULL) {
        return 1;
    }
    return cmp_mtime(a, b);
}

int sort_mtime(const void *a, const void *b) {
    return cmp_mtime_safe(a, b);
}

int rev_sort_mtime(const void *a, const void *b) {
    return cmp_mtime_safe(b, a);
}static void sort_mtime(struct fileinfo **files, size_t n_files)
{
    if (n_files < 2)
        return;

    int (*cmp)(const void *, const void *) =
        (int (*)(const void *, const void *)) cmp_mtime;

    qsort(files, n_files, sizeof *files, cmp);
}

static void revsort_mtime(struct fileinfo **files, size_t n_files)
{
    if (n_files < 2)
        return;

    int (*cmp)(const void *, const void *) =
        (int (*)(const void *, const void *)) cmp_mtime;

    revsort(files, n_files, sizeof *files, cmp);
}extern int cmp_mtime(const void *a, const void *b);

static int sort_mtime(const void *a, const void *b)
{
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return -1;
    }
    if (b == NULL) {
        return 1;
    }
    return cmp_mtime(a, b);
}

static int rev_mtime(const void *a, const void *b)
{
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return 1;
    }
    if (b == NULL) {
        return -1;
    }
    return cmp_mtime(b, a);
}DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)static int sort_mtime(const void *a, const void *b)
{
    const void *const left = *(const void *const *)a;
    const void *const right = *(const void *const *)b;
    return cmp_mtime(left, right);
}

static int rev_mtime(const void *a, const void *b)
{
    int r = sort_mtime(a, b);
    if (r > 0) return -1;
    if (r < 0) return 1;
    return 0;
}DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)DEFINE_SORT_FUNCTIONS (mtime, cmp_mtime)
DEFINE_SORT_FUNCTIONS(atime, cmp_atime)int cmp_atime(const void *, const void *);

static int sort_atime(const void *a, const void *b)
{
    return cmp_atime(a, b);
}

static int rsort_atime(const void *a, const void *b)
{
    int r = cmp_atime(a, b);
    return (r > 0) ? -1 : (r < 0) ? 1 : 0;
}DEFINE_SORT_FUNCTIONS (atime, cmp_atime)DEFINE_SORT_FUNCTIONS(atime, cmp_atime)struct fileinfo;

extern int cmp_atime(const struct fileinfo *a, const struct fileinfo *b);

static int compare_atime(const void *va, const void *vb)
{
    const struct fileinfo *const *a = (const struct fileinfo *const *)va;
    const struct fileinfo *const *b = (const struct fileinfo *const *)vb;

    if (a == b) return 0;
    if (!a) return -1;
    if (!b) return 1;

    const struct fileinfo *fa = *a;
    const struct fileinfo *fb = *b;

    if (fa == fb) return 0;
    if (!fa) return -1;
    if (!fb) return 1;

    {
        const int r = cmp_atime(fa, fb);
        return (r > 0) - (r < 0);
    }
}

static int atime_before(const struct fileinfo *a, const struct fileinfo *b)
{
    if (a == b) return 0;
    if (!a) return 1;
    if (!b) return 0;

    return cmp_atime(a, b) < 0;
}#if !defined(DEFINE_SORT_FUNCTIONS)
#error "DEFINE_SORT_FUNCTIONS is not defined"
#endif
DEFINE_SORT_FUNCTIONS(atime, cmp_atime)DEFINE_SORT_FUNCTIONS (atime, cmp_atime)#ifndef DEFINE_SORT_FUNCTIONS
#error "DEFINE_SORT_FUNCTIONS must be defined"
#endif
DEFINE_SORT_FUNCTIONS(atime, cmp_atime)
#include <stdlib.h>
#include <limits.h>

typedef struct btime btime;

extern int cmp_btime(const btime *a, const btime *b);

static int cmp_btime_adapter(const void *a, const void *b) {
    const btime *pa = (const btime *)a;
    const btime *pb = (const btime *)b;
    return cmp_btime(pa, pb);
}

void btime_sort(btime *base, size_t nmemb) {
    if (!base || nmemb < 2)
        return;
    if (nmemb > SIZE_MAX / sizeof(btime))
        return;
    qsort(base, nmemb, sizeof(btime), cmp_btime_adapter);
}

btime *btime_bsearch(const btime *key, btime *base, size_t nmemb) {
    if (!key || !base || nmemb == 0)
        return NULL;
    if (nmemb > SIZE_MAX / sizeof(btime))
        return NULL;
    return (btime *)bsearch(key, base, nmemb, sizeof(btime), cmp_btime_adapter);
}DEFINE_SORT_FUNCTIONS(btime, cmp_btime)DEFINE_SORT_FUNCTIONS(btime, cmp_btime)DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#include <stddef.h>
#include <stdlib.h>

static int btime_compare(const void *a, const void *b) {
    if (a == NULL || b == NULL)
        return 0;

    const btime *lhs = (const btime *)a;
    const btime *rhs = (const btime *)b;

    return cmp_btime(lhs, rhs);
}

void btime_sort(btime *base, size_t nmemb) {
    if (base == NULL || nmemb < 2)
        return;

    qsort(base, nmemb, sizeof(*base), btime_compare);
}#include <stddef.h>
#include <stdlib.h>

extern int cmp_btime(const btime *a, const btime *b);

static int qsort_cmp_btime(const void *a, const void *b) {
    const btime *pa = (const btime *)a;
    const btime *pb = (const btime *)b;
    return cmp_btime(pa, pb);
}

void sort_btime(btime *array, size_t n) {
    if (!array || n < 2)
        return;
    qsort(array, n, sizeof(*array), qsort_cmp_btime);
}#include <stddef.h>
#include <stdlib.h>

typedef struct btime btime;

int cmp_btime(const btime *a, const btime *b);

int btime_compare(const void *a, const void *b) {
    if (a == b) return 0;
    if (a == NULL) return -1;
    if (b == NULL) return 1;
    return cmp_btime((const btime *)a, (const btime *)b);
}

void btime_sort(btime *array, size_t n) {
    if (array == NULL || n < 2) return;
    qsort(array, n, sizeof(*array), btime_compare);
}DEFINE_SORT_FUNCTIONS(btime, cmp_btime)
DEFINE_SORT_FUNCTIONS(size, cmp_size)#include <stddef.h>
#include <stdlib.h>

#define DEFINE_SORT_FUNCTIONS(T, CMP) \
static int CMP##_adapter(const void *a, const void *b) { \
    const T *lhs = (const T *)a; \
    const T *rhs = (const T *)b; \
    return CMP(lhs, rhs); \
} \
void sort_##T(T *base, size_t nmemb) { \
    if (base == NULL || nmemb < 2) { \
        return; \
    } \
    qsort(base, nmemb, sizeof(*base), CMP##_adapter); \
} \
int is_sorted_##T(const T *base, size_t nmemb) { \
    if (base == NULL || nmemb < 2) { \
        return 1; \
    } \
    for (size_t i = 1; i < nmemb; ++i) { \
        if (CMP(&base[i - 1], &base[i]) > 0) { \
            return 0; \
        } \
    } \
    return 1; \
}

DEFINE_SORT_FUNCTIONS (size, cmp_size)#include <stddef.h>
#include <stdlib.h>
#include <errno.h>

int cmp_size(const void *a, const void *b) {
    const size_t lhs = *(const size_t *)a;
    const size_t rhs = *(const size_t *)b;
    return (lhs > rhs) - (lhs < rhs);
}

int sort_size(size_t *base, size_t nmemb) {
    if (base == NULL && nmemb > 0) {
        return EINVAL;
    }
    if (nmemb < 2) {
        return 0;
    }
    qsort(base, nmemb, sizeof(*base), cmp_size);
    return 0;
}DEFINE_SORT_FUNCTIONS(size, cmp_size)#if !defined(DEFINE_SORT_FUNCTIONS)
#error "Required macro DEFINE_SORT_FUNCTIONS is not defined"
#endif
DEFINE_SORT_FUNCTIONS (size, cmp_size)DEFINE_SORT_FUNCTIONS(size, cmp_size);#ifndef DEFINE_SORT_FUNCTIONS
#error "DEFINE_SORT_FUNCTIONS is not defined"
#endif
DEFINE_SORT_FUNCTIONS(size, cmp_size)DEFINE_SORT_FUNCTIONS (size, cmp_size)
DEFINE_SORT_FUNCTIONS(name, cmp_name)#include <stddef.h>
#include <stdlib.h>

#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
    static int name##_cmp_adapter(const void *a, const void *b) { \
        return cmp_name(a, b); \
    } \
    static inline void name##_sort(void *base, size_t nmemb, size_t size) { \
        if (base == NULL || size == 0 || nmemb < 2) { \
            return; \
        } \
        qsort(base, nmemb, size, name##_cmp_adapter); \
    } \
    static inline int name##_is_sorted(const void *base, size_t nmemb, size_t size) { \
        if (base == NULL || size == 0 || nmemb < 2) { \
            return 1; \
        } \
        const unsigned char *prev = (const unsigned char *)base; \
        const unsigned char *cur = prev + size; \
        for (size_t i = 1; i < nmemb; ++i) { \
            if (name##_cmp_adapter(prev, cur) > 0) { \
                return 0; \
            } \
            prev = cur; \
            cur += size; \
        } \
        return 1; \
    }

DEFINE_SORT_FUNCTIONS (name, cmp_name)DEFINE_SORT_FUNCTIONS (name, cmp_name)DEFINE_SORT_FUNCTIONS(name, cmp_name);DEFINE_SORT_FUNCTIONS(name, cmp_name)#include <stddef.h>
#include <stdlib.h>

#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
static int cmp_name##_adapter(const void *a, const void *b) { \
    const name *lhs = (const name *)a; \
    const name *rhs = (const name *)b; \
    return cmp_name(lhs, rhs); \
} \
void name##_sort(name *array, size_t count) { \
    if (array == NULL || count < 2) { \
        return; \
    } \
    qsort(array, count, sizeof(name), cmp_name##_adapter); \
}

DEFINE_SORT_FUNCTIONS (name, cmp_name)DEFINE_SORT_FUNCTIONS(name, cmp_name)DEFINE_SORT_FUNCTIONS (name, cmp_name)
#include <stddef.h>
#include <stdlib.h>

typedef struct extension extension;

extern int cmp_extension(const extension *a, const extension *b);

static int qsort_cmp_extension(const void *pa, const void *pb)
{
    const extension *a = pa ? *(const extension * const *)pa : NULL;
    const extension *b = pb ? *(const extension * const *)pb : NULL;

    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return 1;
    }
    if (b == NULL) {
        return -1;
    }
    return cmp_extension(a, b);
}

void sort_extension(extension **array, size_t count)
{
    if (array == NULL || count < 2) {
        return;
    }
    qsort(array, count, sizeof(*array), qsort_cmp_extension);
}#include <stddef.h>

extern int cmp_extension(const void *a, const void *b);

int cmp_extension_ascending(const void *a, const void *b) {
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return -1;
    }
    if (b == NULL) {
        return 1;
    }
    return cmp_extension(a, b);
}

int cmp_extension_descending(const void *a, const void *b) {
    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return 1;
    }
    if (b == NULL) {
        return -1;
    }
    int r = cmp_extension(a, b);
    return (r > 0) ? -1 : (r < 0) ? 1 : 0;
}#include <stdlib.h>

struct extension;

int cmp_extension(const void *a, const void *b);

static void sort_extension(struct extension *array, size_t count) {
    if (array == NULL || count < 2) {
        return;
    }
    qsort(array, count, sizeof(*array), cmp_extension);
}

static size_t uniq_extension(struct extension *array, size_t count) {
    if (array == NULL || count == 0) {
        return 0;
    }
    size_t write = 1;
    for (size_t read = 1; read < count; ++read) {
        if (cmp_extension(&array[read], &array[write - 1]) != 0) {
            if (write != read) {
                array[write] = array[read];
            }
            ++write;
        }
    }
    return write;
}DEFINE_SORT_FUNCTIONS(extension, cmp_extension)#include <stddef.h>
#include <stdlib.h>

#ifndef DEFINE_SORT_FUNCTIONS
#define DEFINE_SORT_FUNCTIONS(NAME, CMP) \
static int CMP##_indirect_compare(const void *a, const void *b) { \
    const NAME *const *pa = (const NAME *const *)a; \
    const NAME *const *pb = (const NAME *const *)b; \
    return CMP(*pa, *pb); \
} \
static void sort_##NAME(NAME **arr, size_t n) { \
    if (arr == NULL || n < 2) { \
        return; \
    } \
    qsort(arr, n, sizeof(*arr), CMP##_indirect_compare); \
}
#endif

DEFINE_SORT_FUNCTIONS (extension, cmp_extension)#include <stddef.h>
#include <stdlib.h>

typedef struct extension extension;

extern int cmp_extension(const extension *a, const extension *b);

static int qsort_cmp_extension_adapter(const void *lhs, const void *rhs) {
    const extension *const a = *(const extension *const *)lhs;
    const extension *const b = *(const extension *const *)rhs;

    if (a == b) {
        return 0;
    }
    if (a == NULL) {
        return -1;
    }
    if (b == NULL) {
        return 1;
    }

    return cmp_extension(a, b);
}

void sort_extension(extension **items, size_t count) {
    if (items == NULL || count < 2) {
        return;
    }

    qsort(items, count, sizeof(*items), qsort_cmp_extension_adapter);
}DEFINE_SORT_FUNCTIONS (extension, cmp_extension)#include <stddef.h>
#include <stdlib.h>

static int extension_qsort_adapter(const void *a, const void *b) {
    const extension *ea = (const extension *)a;
    const extension *eb = (const extension *)b;

    return cmp_extension(ea, eb);
}

void extension_sort(extension *array, size_t count) {
    if (!array || count < 2)
        return;

    qsort(array, count, sizeof(*array), extension_qsort_adapter);
}
DEFINE_SORT_FUNCTIONS(width, cmp_width)DEFINE_SORT_FUNCTIONS(width, cmp_width);DEFINE_SORT_FUNCTIONS (width, cmp_width)DEFINE_SORT_FUNCTIONS(width, cmp_width)DEFINE_SORT_FUNCTIONS(width, cmp_width)DEFINE_SORT_FUNCTIONS(width, cmp_width)#ifndef DEFINE_SORT_FUNCTIONS
#error "DEFINE_SORT_FUNCTIONS macro is not defined"
#endif
DEFINE_SORT_FUNCTIONS (width, cmp_width)#include <stddef.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>

extern int cmp_width(const void *, const void *);

static void width_merge(width *arr, width *aux, size_t lo, size_t mid, size_t hi, int (*cmp)(const void *, const void *)) {
    size_t i = lo;
    size_t j = mid;
    size_t k = lo;

    while (i < mid && j < hi) {
        if (cmp(&arr[i], &arr[j]) <= 0) {
            aux[k++] = arr[i++];
        } else {
            aux[k++] = arr[j++];
        }
    }
    while (i < mid) {
        aux[k++] = arr[i++];
    }
    while (j < hi) {
        aux[k++] = arr[j++];
    }
    for (k = lo; k < hi; ++k) {
        arr[k] = aux[k];
    }
}

static void width_mergesort_rec(width *arr, width *aux, size_t lo, size_t hi, int (*cmp)(const void *, const void *)) {
    if (hi - lo <= 1) {
        return;
    }
    size_t mid = lo + (hi - lo) / 2;
    width_mergesort_rec(arr, aux, lo, mid, cmp);
    width_mergesort_rec(arr, aux, mid, hi, cmp);
    width_merge(arr, aux, lo, mid, hi, cmp);
}

int width_stable_sort(width *base, size_t n) {
    if (n == 0) {
        return 0;
    }
    if (!base) {
        return EINVAL;
    }
    if (n > SIZE_MAX / sizeof *base) {
        return ENOMEM;
    }
    width *aux = (width *)malloc(n * sizeof *aux);
    if (!aux) {
        return ENOMEM;
    }
    width_mergesort_rec(base, aux, 0, n, cmp_width);
    free(aux);
    return 0;
}

int stable_sort_width(width *base, size_t n) {
    return width_stable_sort(base, n);
}

int width_sort(width *base, size_t n) {
    if (n == 0) {
        return 0;
    }
    if (!base) {
        return EINVAL;
    }
    qsort(base, n, sizeof *base, cmp_width);
    return 0;
}

int sort_width(width *base, size_t n) {
    return width_sort(base, n);
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
  if (a == b)
    return 0;
  if (!a)
    return -1;
  if (!b)
    return 1;

  const char *an = a->name;
  const char *bn = b->name;

  if (an == bn)
    return 0;
  if (!an)
    return -1;
  if (!bn)
    return 1;

  int diff = filevercmp (an, bn);
  if (diff != 0)
    return diff;

  return strcmp (an, bn);
}

static int xstrcoll_version(V left, V right)
{
    return cmp_version(left, right);
}
static int rev_xstrcoll_version(V lhs, V rhs)
{
    return cmp_version(rhs, lhs);
}
static int
xstrcoll_df_version (V left, V right)
{
  return dirfirst_check(left, right, xstrcoll_version);
}
static int rev_xstrcoll_df_version(V a, V b)
{
    return dirfirst_check(a, b, rev_xstrcoll_version);
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
initialize_ordering_vector(void)
{
  idx_t n = cwd_n_used;

  if (n <= 0 || sorted_file == NULL || cwd_file == NULL)
    return;

  for (idx_t i = 0; i < n; i++)
    sorted_file[i] = &cwd_file[i];
}

/* Cache values based on attributes global to all files.  */

static void
update_current_files_info(void)
{
  const int need_widths =
    (sort_type == sort_width)
    || (line_length && (format == many_per_line || format == horizontal));

  if (!need_widths || cwd_n_used == 0)
    return;

  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
      if (f)
        f->width = fileinfo_name_width(f);
    }
}

/* Sort the files now in the table.  */

static void
sort_files (void)
{
  if (sorted_file_alloc < cwd_n_used + (cwd_n_used >> 1))
    {
      free (sorted_file);
      sorted_file = xinmalloc (cwd_n_used, 3 * sizeof *sorted_file);
      sorted_file_alloc = 3 * cwd_n_used;
    }

  initialize_ordering_vector ();
  update_current_files_info ();

  if (sort_type == sort_none)
    return;

  if (! setjmp (failed_strcoll))
    {
      size_t idx = sort_type + (sort_type == sort_time ? time_type : 0);
      mpsort ((void const **) sorted_file, cwd_n_used,
              sort_functions[idx][0][sort_reverse][directories_first]);
    }
  else
    {
      affirm (sort_type != sort_version);
      initialize_ordering_vector ();
      size_t idx = sort_type + (sort_type == sort_time ? time_type : 0);
      mpsort ((void const **) sorted_file, cwd_n_used,
              sort_functions[idx][1][sort_reverse][directories_first]);
    }
}

/* List all the files now in the table.  */

static void
print_current_files(void)
{
  switch (format)
    {
    case one_per_line:
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          print_file_name_and_frills(sorted_file[i], 0);
          if (putchar((unsigned char)eolbyte) == EOF)
            return;
        }
      break;

    case many_per_line:
    case horizontal:
      if (!line_length)
        {
          print_with_separator(' ');
        }
      else
        {
          void (*printer)(void) = (format == many_per_line) ? print_many_per_line : print_horizontal;
          printer();
        }
      break;

    case with_commas:
      print_with_separator(',');
      break;

    case long_format:
      for (idx_t i = 0; i < cwd_n_used; i++)
        {
          set_normal_color();
          print_long_format(sorted_file[i]);
          dired_outbyte(eolbyte);
        }
      break;

    default:
      break;
    }
}

/* Replace the first %b with precomputed aligned month names.
   Note on glibc-2.7 at least, this speeds up the whole 'ls -lU'
   process by around 17%, compared to letting strftime() handle the %b.  */

static size_t
align_nstrftime(char *buf, size_t size, bool recent, struct tm const *tm,
                timezone_t tz, int ns)
{
    if (!buf || size == 0 || !tm) {
        if (buf && size > 0) {
            buf[0] = '\0';
        }
        return 0;
    }

    int recent_idx = recent ? 1 : 0;
    const char *fmt = NULL;

    if (use_abformat) {
        int mon = tm->tm_mon;
        if (mon >= 0 && mon <= 11) {
            fmt = abformat[recent_idx][mon];
        }
    }

    if (!fmt) {
        fmt = long_time_format[recent_idx];
    }

    if (!fmt) {
        buf[0] = '\0';
        return 0;
    }

    return nstrftime(buf, size, fmt, tm, tz, ns);
}

/* Return the expected number of columns in a long-format timestamp,
   or zero if it cannot be calculated.  */

static int
long_time_expected_width (void)
{
  static int width = -1;

  if (width >= 0)
    return width;

  time_t epoch = (time_t) 0;
  struct tm tm_buf;
  char buf[TIME_STAMP_LEN_MAXIMUM + 1];
  int computed_width = -1;

  if (localtime_rz (localtz, &epoch, &tm_buf))
    {
      size_t len = align_nstrftime (buf, sizeof buf, false, &tm_buf, localtz, 0);
      if (len > 0 && len < sizeof buf)
        {
          int w = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
          if (w >= 0)
            computed_width = w;
        }
    }

  width = (computed_width >= 0) ? computed_width : 0;
  return width;
}

/* Print the user or group name NAME, with numeric id ID, using a
   print width of WIDTH columns.  */

static void
format_user_or_group (char const *name, uintmax_t id, int width)
{
  if (!name)
    {
      int r = printf ("%*ju ", width, id);
      if (r > 0)
        dired_pos += r;
      return;
    }

  int name_width = mbswidth (name, MBSWIDTH_FLAGS);
  int width_gap;

  if (name_width < 0)
    width_gap = 0;
  else
    {
      long long diff = (long long) width - (long long) name_width;
      width_gap = (diff > 0) ? (int) diff : 0;
    }

  int pad = width_gap;

  dired_outstring (name);

  while (pad-- >= 0)
    dired_outbyte (' ');
}

/* Print the name or id of the user with id U, using a print width of
   WIDTH.  */

static void
format_user(uid_t u, int width, bool stat_ok)
{
  const char *name = NULL;

  if (!stat_ok)
    name = "?";
  else if (!numeric_ids)
    name = getuser(u);

  format_user_or_group(name, u, width);
}

/* Likewise, for groups.  */

static void
format_group(gid_t g, int width, bool stat_ok)
{
  const char *name = NULL;

  if (!stat_ok) {
    name = "?";
  } else if (!numeric_ids) {
    name = getgroup(g);
  }

  format_user_or_group(name, g, width);
}

/* Return the number of columns that format_user_or_group will print,
   or -1 if unknown.  */

static int
format_user_or_group_width (char const *name, uintmax_t id)
{
  if (name != NULL)
    return mbswidth (name, MBSWIDTH_FLAGS);

  int digits = 1;
  uintmax_t v = id;
  while (v >= 10)
    {
      v /= 10;
      ++digits;
    }
  return digits;
}

/* Return the number of columns that format_user will print,
   or -1 if unknown.  */

static int
format_user_width(uid_t u)
{
    const char *name = NULL;
    if (!numeric_ids) {
        name = getuser(u);
    }
    return format_user_or_group_width(name, u);
}

/* Likewise, for groups.  */

static int
format_group_width(gid_t g)
{
    const char *group_name = NULL;

    if (!numeric_ids) {
        group_name = getgroup(g);
    }

    return format_user_or_group_width(group_name, g);
}

/* Return a pointer to a formatted version of F->stat.st_ino,
   possibly using buffer, which must be at least
   INT_BUFSIZE_BOUND (uintmax_t) bytes.  */
static char *
format_inode(char buf[INT_BUFSIZE_BOUND(uintmax_t)], const struct fileinfo *f)
{
  if (!buf)
    return (char *) "?";

  if (f && f->stat_ok && f->stat.st_ino != NOT_AN_INODE_NUMBER)
    return umaxtostr(f->stat.st_ino, buf);

  buf[0] = '?';
  buf[1] = '\0';
  return buf;
}

/* Print information about F in long format.  */
static void
print_long_format (const struct fileinfo *f)
{
  char modebuf[12];
  char buf
    [LONGEST_HUMAN_READABLE + 1
     + LONGEST_HUMAN_READABLE + 1
     + sizeof (modebuf) - 1 + 1
     + INT_BUFSIZE_BOUND (uintmax_t)
     + LONGEST_HUMAN_READABLE + 2
     + LONGEST_HUMAN_READABLE + 1
     + TIME_STAMP_LEN_MAXIMUM + 1
     ];
  char *p = buf;
  char *end = buf + sizeof buf;
  size_t s;
  struct timespec when_timespec;
  struct tm when_local;
  bool btime_ok = true;

  if (f->stat_ok)
    filemodestring (&f->stat, modebuf);
  else
    {
      modebuf[0] = filetype_letter[f->filetype];
      memset (modebuf + 1, '?', 10);
      modebuf[11] = '\0';
    }
  if (! any_has_acl)
    modebuf[10] = '\0';
  else if (f->acl_type == ACL_T_LSM_CONTEXT_ONLY)
    modebuf[10] = '.';
  else if (f->acl_type == ACL_T_YES)
    modebuf[10] = '+';
  else if (f->acl_type == ACL_T_UNKNOWN)
    modebuf[10] = '?';

  switch (time_type)
    {
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

  if (print_inode)
    {
      char hbuf[INT_BUFSIZE_BOUND (uintmax_t)];
      size_t rem = (size_t) (end - p);
      if (rem > 0)
        {
          int n = snprintf (p, rem, "%*s ", inode_number_width,
                            format_inode (hbuf, f));
          if (n > 0)
            p += (size_t) n < rem ? (size_t) n : rem - 1;
        }
    }

  if (print_block_size)
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      char const *blocks =
        (! f->stat_ok
         ? "?"
         : human_readable (STP_NBLOCKS (&f->stat), hbuf, human_output_opts,
                           ST_NBLOCKSIZE, output_block_size));
      int blocks_width = mbswidth (blocks, MBSWIDTH_FLAGS);
      int pad = blocks_width < 0 ? 0 : block_size_width - blocks_width;
      for (int i = 0; i < pad && p < end; i++)
        *p++ = ' ';
      for (const char *q = blocks; *q && p < end; q++)
        *p++ = *q;
      if (p < end)
        *p++ = ' ';
    }

  {
    char hbuf[INT_BUFSIZE_BOUND (uintmax_t)];
    size_t rem = (size_t) (end - p);
    if (rem > 0)
      {
        int n = snprintf (p, rem, "%s %*s ", modebuf, nlink_width,
                          ! f->stat_ok ? "?" : umaxtostr (f->stat.st_nlink, hbuf));
        if (n > 0)
          p += (size_t) n < rem ? (size_t) n : rem - 1;
      }
  }

  dired_indent ();

  if (print_owner || print_group || print_author || print_scontext)
    {
      dired_outbuf (buf, (size_t) (p - buf));

      if (print_owner)
        format_user (f->stat.st_uid, owner_width, f->stat_ok);

      if (print_group)
        format_group (f->stat.st_gid, group_width, f->stat_ok);

      if (print_author)
        format_user (f->stat.st_author, author_width, f->stat_ok);

      if (print_scontext)
        format_user_or_group (f->scontext, 0, scontext_width);

      p = buf;
    }

  if (f->stat_ok && (S_ISCHR (f->stat.st_mode) || S_ISBLK (f->stat.st_mode)))
    {
      char majorbuf[INT_BUFSIZE_BOUND (uintmax_t)];
      char minorbuf[INT_BUFSIZE_BOUND (uintmax_t)];
      int blanks_width = (file_size_width
                          - (major_device_number_width + 2
                             + minor_device_number_width));
      size_t rem = (size_t) (end - p);
      if (rem > 0)
        {
          int n = snprintf (p, rem, "%*s, %*s ",
                            major_device_number_width + MAX (0, blanks_width),
                            umaxtostr (major (f->stat.st_rdev), majorbuf),
                            minor_device_number_width,
                            umaxtostr (minor (f->stat.st_rdev), minorbuf));
          if (n > 0)
            p += (size_t) n < rem ? (size_t) n : rem - 1;
        }
    }
  else
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      char const *size =
        (! f->stat_ok
         ? "?"
         : human_readable (unsigned_file_size (f->stat.st_size),
                           hbuf, file_human_output_opts, 1,
                           file_output_block_size));
      int size_width = mbswidth (size, MBSWIDTH_FLAGS);
      int pad = size_width < 0 ? 0 : file_size_width - size_width;
      for (int i = 0; i < pad && p < end; i++)
        *p++ = ' ';
      for (const char *q = size; *q && p < end; q++)
        *p++ = *q;
      if (p < end)
        *p++ = ' ';
    }

  s = 0;
  if (p < end)
    *p = '\1';

  if (f->stat_ok && btime_ok
      && localtime_rz (localtz, &when_timespec.tv_sec, &when_local))
    {
      struct timespec six_months_ago;
      bool recent;

      if (timespec_cmp (current_time, when_timespec) < 0)
        gettime (&current_time);

      six_months_ago.tv_sec = current_time.tv_sec - 31556952 / 2;
      six_months_ago.tv_nsec = current_time.tv_nsec;

      recent = (timespec_cmp (six_months_ago, when_timespec) < 0
                && timespec_cmp (when_timespec, current_time) < 0);

      size_t tlen = (size_t) (end - p);
      if (tlen > 0)
        {
          size_t maxlen = TIME_STAMP_LEN_MAXIMUM + 1;
          size_t buflen = tlen < maxlen ? tlen : maxlen;
          s = align_nstrftime (p, buflen, recent,
                               &when_local, localtz, when_timespec.tv_nsec);
        }
    }

  if (s || (p < end && !*p))
    {
      p += s;
      if (p < end)
        *p++ = ' ';
    }
  else
    {
      char hbuf[INT_BUFSIZE_BOUND (intmax_t)];
      size_t rem = (size_t) (end - p);
      if (rem > 0)
        {
          int n = snprintf (p, rem, "%*s ", long_time_expected_width (),
                            (! f->stat_ok || ! btime_ok
                             ? "?"
                             : timetostr (when_timespec.tv_sec, hbuf)));
          if (n > 0)
            p += (size_t) n < rem ? (size_t) n : rem - 1;
        }
    }

  dired_outbuf (buf, (size_t) (p - buf));
  size_t w = print_name_with_quoting (f, false, &dired_obstack, (size_t) (p - buf));

  if (f->filetype == symbolic_link)
    {
      if (f->linkname)
        {
          dired_outstring (" -> ");
          print_name_with_quoting (f, true, NULL, (size_t) ((p - buf) + w + 4));
          if (indicator_style != none)
            print_type_indicator (true, f->linkmode, unknown);
        }
    }
  else if (indicator_style != none)
    print_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
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
  bool quoted;

  enum quoting_style qs = get_quoting_style (options);
  bool needs_further_quoting = qmark_funny_chars
                               && (qs == shell_quoting_style
                                   || qs == shell_always_quoting_style
                                   || qs == literal_quoting_style);

  if (needs_general_quoting != 0)
    {
      size_t name_len = strlen (name);
      len = quotearg_buffer (buf, bufsize, name, -1, options);
      if (bufsize <= len)
        {
          buf = xmalloc (len + 1);
          len = quotearg_buffer (buf, len + 1, name, -1, options);
        }
      quoted = (*name != *buf) || name_len != len;
    }
  else if (needs_further_quoting)
    {
      size_t name_len = strlen (name);
      if (bufsize <= name_len)
        buf = xmalloc (name_len + 1);
      memcpy (buf, name, name_len + 1);
      len = name_len;
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
        {
          const char *p = buf;
          const char *plimit = buf + len;
          char *q = buf;
          displayed_width = 0;

          while (p < plimit)
            {
              unsigned char uc = (unsigned char) *p;
              if (uc >= 0x20 && uc <= 0x7E)
                {
                  *q++ = *p++;
                  displayed_width += 1;
                  continue;
                }

              {
                mbstate_t mbstate; mbszero (&mbstate);
                do
                  {
                    char32_t wc;
                    size_t bytes = mbrtoc32 (&wc, p, (size_t) (plimit - p), &mbstate);

                    if (bytes == (size_t) -1)
                      {
                        p++;
                        *q++ = '?';
                        displayed_width += 1;
                        break;
                      }

                    if (bytes == (size_t) -2)
                      {
                        p = plimit;
                        *q++ = '?';
                        displayed_width += 1;
                        break;
                      }

                    if (bytes == 0)
                      bytes = 1;

                    {
                      int w = c32width (wc);
                      if (w >= 0)
                        {
                          for (; bytes > 0; --bytes)
                            *q++ = *p++;
                          displayed_width += (size_t) w;
                        }
                      else
                        {
                          p += bytes;
                          *q++ = '?';
                          displayed_width += 1;
                        }
                    }
                  }
                while (! mbsinit (&mbstate));
              }
            }

          len = (size_t) (q - buf);
        }
      else
        {
          char *p = buf;
          char const *plimit = buf + len;

          while (p < plimit)
            {
              if (! isprint (to_uchar (*p)))
                *p = '?';
              p++;
            }
          displayed_width = len;
        }
    }
  else if (width != NULL)
    {
      if (MB_CUR_MAX > 1)
        {
          displayed_width = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
          displayed_width = MAX (0, displayed_width);
        }
      else
        {
          char const *p = buf;
          char const *plimit = buf + len;

          displayed_width = 0;
          while (p < plimit)
            {
              if (isprint (to_uchar (*p)))
                displayed_width++;
              p++;
            }
        }
    }

  *pad = (align_variable_outer_quotes && cwd_some_quoted && ! quoted);

  if (width != NULL)
    *width = displayed_width;

  *inbuf = buf;

  return len;
}

static size_t
quote_name_width(char const *name, struct quoting_options const *options,
                 int needs_general_quoting)
{
  char smallbuf[BUFSIZ];
  char *buf = smallbuf;
  size_t width = 0;
  bool pad = false;

  quote_name_buf(&buf, sizeof smallbuf, (char *) name, options,
                 needs_general_quoting, &width, &pad);

  if (buf && buf != smallbuf && buf != (char *) name)
    free(buf);

  return width + (pad ? 1u : 0u);
}

/* %XX escape any input out of range as defined in RFC3986,
   and also if PATH, convert all path separators to '/'.  */
static char *
file_escape (char const *str, bool path)
{
  size_t len = strlen (str);
  char *esc = xnmalloc (3, len + 1);
  char *p = esc;
  const char *hexdigits = "0123456789abcdef";

  while (*str)
    {
      if (path && ISSLASH (*str))
        {
          *p++ = '/';
          str++;
          continue;
        }

        {
          unsigned char uc = to_uchar (*str);
          if (RFC3986[uc])
            {
              *p++ = *str++;
              continue;
            }

          *p++ = '%';
          *p++ = hexdigits[uc >> 4];
          *p++ = hexdigits[uc & 0x0F];
          str++;
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

  len = quote_name_buf(&buf, sizeof smallbuf, (char *) name, options,
                       needs_general_quoting, NULL, &pad);

  if (pad && allow_pad)
    dired_outbyte(' ');

  if (color)
    print_color_indicator(color);

  bool skip_quotes = false;
  bool link_started = false;

  if (absolute_name)
    {
      char *h = file_escape(hostname, false);
      char *n = file_escape(absolute_name, true);

      if (h && n)
        {
          if (align_variable_outer_quotes && cwd_some_quoted && !pad && len >= 2)
            {
              skip_quotes = true;
              putchar(*buf);
            }
          printf("\033]8;;file://%s%s%s\a", h, (n[0] == '/' ? "" : "/"), n);
          link_started = true;
        }

      free(h);
      free(n);
    }

  if (stack)
    push_current_dired_pos(stack);

  {
    size_t offset = skip_quotes ? 1u : 0u;
    size_t to_write = len - (skip_quotes ? 2u : 0u);
    size_t written = 0;

    while (written < to_write)
      {
        size_t w = fwrite(buf + offset + written, 1, to_write - written, stdout);
        if (w == 0)
          break;
        written += w;
      }
  }

  dired_pos += len;

  if (stack)
    push_current_dired_pos(stack);

  if (link_started)
    {
      fputs("\033]8;;\a", stdout);
      if (skip_quotes)
        putchar(*(buf + len - 1));
    }

  if (buf != smallbuf && buf != name)
    free(buf);

  return len + (pad ? 1u : 0u);
}

static size_t
print_name_with_quoting (const struct fileinfo *f,
                         bool symlink_target,
                         struct obstack *stack,
                         size_t start_col)
{
  if (!f || !stack)
    return 0;

  const char *name = symlink_target ? f->linkname : f->name;

  const struct bin_str *color = NULL;
  bool used_color_this_time = false;

  if (print_with_color)
    {
      color = get_color_indicator (f, symlink_target);
      used_color_this_time = (color != NULL) || is_colored (C_NORM);
    }

  size_t len = quote_name (name, filename_quoting_options, f->quoted,
                           color, !symlink_target, stack, f->absolute_name);

  process_signals ();

  if (used_color_this_time)
    {
      prep_non_filename_text ();

      if (line_length && len > 0)
        {
          size_t rem = start_col % line_length;
          if ((len - 1) >= (line_length - rem))
            put_indicator (&color_indicator[C_CLR_TO_EOL]);
        }
    }

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
  size_t width = 0;
  int use_commas = (format == with_commas);

  set_normal_color ();

  if (print_inode)
    {
      int inode_w = use_commas ? 0 : inode_number_width;
      char const *inode_str = format_inode (buf, f);
      if (!inode_str)
        inode_str = "";
      printf ("%*s ", inode_w, inode_str);
    }

  if (print_block_size)
    {
      char const *blocks =
        (f->stat_ok
         ? human_readable (STP_NBLOCKS (&f->stat), buf, human_output_opts,
                           ST_NBLOCKSIZE, output_block_size)
         : "?");
      int blocks_width = mbswidth (blocks, MBSWIDTH_FLAGS);
      int pad = 0;
      if (0 <= blocks_width && block_size_width && !use_commas)
        {
          pad = block_size_width - blocks_width;
          if (pad < 0)
            pad = 0;
        }
      printf ("%*s%s ", pad, "", blocks);
    }

  if (print_scontext)
    {
      int sctx_w = use_commas ? 0 : scontext_width;
      char const *sctx = f->scontext ? f->scontext : "";
      printf ("%*s ", sctx_w, sctx);
    }

  width = print_name_with_quoting (f, false, NULL, start_col);

  if (indicator_style != none)
    width += print_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);

  return width;
}

/* Given these arguments describing a file, return the single-byte
   type indicator, or 0.  */
static char
get_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  const bool style_slash = (indicator_style == slash);
  const bool style_classify = (indicator_style == classify);

  const bool is_reg = stat_ok ? S_ISREG (mode) : (type == normal);
  if (is_reg)
    return (stat_ok && style_classify && (mode & S_IXUGO)) ? '*' : 0;

  const bool is_dir = stat_ok ? S_ISDIR (mode) : (type == directory || type == arg_directory);
  if (is_dir)
    return '/';

  if (style_slash)
    return 0;

  const bool is_lnk = stat_ok ? S_ISLNK (mode) : (type == symbolic_link);
  if (is_lnk)
    return '@';

  const bool is_fifo = stat_ok ? S_ISFIFO (mode) : (type == fifo);
  if (is_fifo)
    return '|';

  const bool is_sock = stat_ok ? S_ISSOCK (mode) : (type == sock);
  if (is_sock)
    return '=';

  if (stat_ok && S_ISDOOR (mode))
    return '>';

  return 0;
}

static bool
print_type_indicator(bool stat_ok, mode_t mode, enum filetype type)
{
    const char indicator = get_type_indicator(stat_ok, mode, type);
    const bool has_indicator = (indicator != '\0');

    if (has_indicator)
        dired_outbyte(indicator);

    return has_indicator;
}

/* Returns if color sequence was printed.  */
static bool
print_color_indicator (const struct bin_str *ind)
{
  if (ind == NULL)
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
  if (!f)
    return nullptr;

  enum indicator_no type = C_FILE;
  struct color_ext_type *ext = nullptr;
  size_t len = 0;

  const char *name;
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

  if (linkok == -1 && is_colored (C_MISSING))
    {
      type = C_MISSING;
    }
  else if (!f->stat_ok)
    {
      static const enum indicator_no filetype_indicator[] =
        {
          C_ORPHAN, C_FIFO, C_CHR, C_DIR, C_BLK, C_FILE,
          C_LINK, C_SOCK, C_FILE, C_DIR
        };
      static_assert (ARRAY_CARDINALITY (filetype_indicator)
                     == filetype_cardinality);
      type = filetype_indicator[f->filetype];
    }
  else
    {
      if (S_ISREG (mode))
        {
          type = C_FILE;

          if ((mode & S_ISUID) && is_colored (C_SETUID))
            type = C_SETUID;
          else if ((mode & S_ISGID) && is_colored (C_SETGID))
            type = C_SETGID;
          else if (f->has_capability)
            type = C_CAP;
          else if ((mode & S_IXUGO) && is_colored (C_EXEC))
            type = C_EXEC;
          else if (f->stat.st_nlink > 1 && is_colored (C_MULTIHARDLINK))
            type = C_MULTIHARDLINK;
        }
      else if (S_ISDIR (mode))
        {
          type = C_DIR;

          if ((mode & S_ISVTX) && (mode & S_IWOTH)
              && is_colored (C_STICKY_OTHER_WRITABLE))
            type = C_STICKY_OTHER_WRITABLE;
          else if ((mode & S_IWOTH) && is_colored (C_OTHER_WRITABLE))
            type = C_OTHER_WRITABLE;
          else if ((mode & S_ISVTX) && is_colored (C_STICKY))
            type = C_STICKY;
        }
      else if (S_ISLNK (mode))
        {
          type = C_LINK;
        }
      else if (S_ISFIFO (mode))
        {
          type = C_FIFO;
        }
      else if (S_ISSOCK (mode))
        {
          type = C_SOCK;
        }
      else if (S_ISBLK (mode))
        {
          type = C_BLK;
        }
      else if (S_ISCHR (mode))
        {
          type = C_CHR;
        }
      else if (S_ISDOOR (mode))
        {
          type = C_DOOR;
        }
      else
        {
          type = C_ORPHAN;
        }
    }

  if (type == C_FILE && name)
    {
      len = strlen (name);
      const char *end = name + len;

      for (ext = color_ext_list; ext; ext = ext->next)
        {
          if (ext->ext.len <= len)
            {
              const char *start = end - ext->ext.len;
              if (ext->exact_match)
                {
                  if (STREQ_LEN (start, ext->ext.string, ext->ext.len))
                    break;
                }
              else
                {
                  if (c_strncasecmp (start, ext->ext.string, ext->ext.len) == 0)
                    break;
                }
            }
        }
    }

  if (type == C_LINK && !linkok)
    {
      if (color_symlink_as_referent || is_colored (C_ORPHAN))
        type = C_ORPHAN;
    }

  const struct bin_str *const s =
    ext ? &ext->seq : &color_indicator[type];

  return s->string ? s : nullptr;
}

/* Output a color indicator (which may contain nulls).  */
static void
put_indicator (const struct bin_str *ind)
{
  const unsigned char *ptr;
  size_t remaining;
  size_t written;

  if (ind == NULL || ind->string == NULL || ind->len == 0)
    return;

  if (! used_color)
    {
      used_color = true;

      if (0 <= tcgetpgrp (STDOUT_FILENO))
        signal_init ();

      prep_non_filename_text ();
    }

  ptr = (const unsigned char *) ind->string;
  remaining = ind->len;

  while (remaining > 0)
    {
      written = fwrite (ptr, 1, remaining, stdout);
      if (written == 0)
        break;

      ptr += written;
      remaining -= written;
    }
}

static inline size_t safe_strlen0(const char *s)
{
  return s ? strlen(s) : 0;
}

static inline void size_add_checked(size_t *acc, size_t inc)
{
  if (SIZE_MAX - *acc < inc)
    *acc = SIZE_MAX;
  else
    *acc += inc;
}

static size_t
length_of_file_name_and_frills (const struct fileinfo *f)
{
  size_t len = 0;
  char buf[MAX (LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND (uintmax_t))];

  if (print_inode)
    {
      size_t add = 1;
      if (format == with_commas)
        {
          umaxtostr (f->stat.st_ino, buf);
          add += strlen (buf);
        }
      else
        {
          add += (size_t) inode_number_width;
        }
      size_add_checked (&len, add);
    }

  if (print_block_size)
    {
      size_t add = 1;
      if (format == with_commas)
        {
          const char *bs;
          if (!f->stat_ok)
            {
              bs = "?";
            }
          else
            {
              human_readable (STP_NBLOCKS (&f->stat), buf,
                              human_output_opts, ST_NBLOCKSIZE,
                              output_block_size);
              bs = buf;
            }
          add += strlen (bs);
        }
      else
        {
          add += (size_t) block_size_width;
        }
      size_add_checked (&len, add);
    }

  if (print_scontext)
    {
      size_t add = 1;
      if (format == with_commas)
        add += safe_strlen0 (f->scontext);
      else
        add += (size_t) scontext_width;
      size_add_checked (&len, add);
    }

  size_add_checked (&len, fileinfo_name_width (f));

  if (indicator_style != none)
    {
      char c = get_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
      if (c != 0)
        size_add_checked (&len, 1);
    }

  return len;
}

static void
print_many_per_line (void)
{
  if (cwd_n_used == 0)
    return;

  idx_t cols = calculate_columns (true);
  if (cols <= 0)
    return;

  struct column_info const *line_fmt = &column_info[cols - 1];
  idx_t rows = (cwd_n_used + cols - 1) / cols;

  for (idx_t row = 0; row < rows; row++)
    {
      size_t col = 0;
      idx_t filesno = row;
      size_t pos = 0;

      while (filesno < cwd_n_used)
        {
          struct fileinfo const *f = sorted_file[filesno];
          size_t name_length = length_of_file_name_and_frills (f);
          size_t max_name_length = line_fmt->col_arr[col++];
          print_file_name_and_frills (f, pos);

          idx_t next = filesno + rows;
          if (next >= cwd_n_used)
            break;

          indent (pos + name_length, pos + max_name_length);
          pos += max_name_length;
          filesno = next;
        }
      putchar (eolbyte);
    }
}

static void
print_horizontal (void)
{
  if (cwd_n_used == 0)
    {
      putchar (eolbyte);
      return;
    }

  idx_t cols = calculate_columns (false);
  if (cols <= 0)
    {
      putchar (eolbyte);
      return;
    }

  struct column_info const *line_fmt = &column_info[cols - 1];
  size_t pos = 0;
  size_t prev_name_length = 0;
  size_t prev_max_width = 0;

  for (idx_t filesno = 0; filesno < cwd_n_used; ++filesno)
    {
      idx_t col = filesno % cols;

      if (filesno != 0)
        {
          if (col == 0)
            {
              putchar (eolbyte);
              pos = 0;
            }
          else
            {
              indent (pos + prev_name_length, pos + prev_max_width);
              pos += prev_max_width;
            }
        }

      struct fileinfo const *f = sorted_file[filesno];
      print_file_name_and_frills (f, pos);

      prev_name_length = length_of_file_name_and_frills (f);
      prev_max_width = line_fmt->col_arr[col];
    }

  putchar (eolbyte);
}

/* Output name + SEP + ' '.  */

static void
print_with_separator(char sep)
{
  size_t pos = 0;
  size_t ll = (size_t) line_length;
  int has_line_length = (ll != 0);

  for (idx_t filesno = 0; filesno < cwd_n_used; filesno++)
    {
      const struct fileinfo *f = sorted_file[filesno];
      size_t len = has_line_length ? length_of_file_name_and_frills(f) : 0;

      if (filesno != 0)
        {
          char separator = ' ';
          int fits = 1;

          if (has_line_length)
            {
              fits = 0;
              if (len <= SIZE_MAX - 2)
                {
                  size_t limit = SIZE_MAX - (len + 2);
                  if (pos <= limit)
                    {
                      size_t needed = pos + len + 2;
                      fits = (needed < ll);
                    }
                }
            }

          if (fits)
            {
              pos += 2;
            }
            else
            {
              pos = 0;
              separator = eolbyte;
            }

          (void) putchar(sep);
          (void) putchar(separator);
        }

      print_file_name_and_frills(f, pos);
      pos += len;
    }
  (void) putchar(eolbyte);
}

/* Assuming cursor is at position FROM, indent up to position TO.
   Use a TAB character instead of two or more spaces whenever possible.  */

static void
indent(size_t from, size_t to)
{
    if (from >= to)
        return;

    size_t ts = tabsize;
    int rc;

    if (ts == 0) {
        size_t spaces = to - from;
        while (spaces--) {
            rc = putchar(' ');
            if (rc == EOF)
                break;
        }
        return;
    }

    size_t to_div = to / ts;

    while (from < to) {
        size_t from_mod = from % ts;
        size_t from_div = from / ts;
        size_t b = from_div + (from_mod == ts - 1 ? 1u : 0u);

        if (to_div > b) {
            rc = putchar('\t');
            if (rc == EOF)
                break;

            size_t advance = ts - from_mod;
            size_t max_advance = to - from;
            if (advance > max_advance) {
                from = to;
            } else {
                from += advance;
            }
        } else {
            rc = putchar(' ');
            if (rc == EOF)
                break;
            from++;
        }
    }
}

/* Put DIRNAME/NAME into DEST, handling '.' and '/' properly.  */
/* FIXME: maybe remove this function someday.  See about using a
   non-malloc'ing version of file_name_concat.  */

static void
attach(char *dest, const char *dirname, const char *name)
{
  if (!dest || !dirname || !name)
    return;

  if (!(dirname[0] == '.' && dirname[1] == '\0'))
    {
      const char *p = dirname;
      while (*p)
        *dest++ = *p++;
      if (p != dirname && p[-1] != '/')
        *dest++ = '/';
    }

  while (*name)
    *dest++ = *name++;
  *dest = '\0';
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

      size_t growth = (size_t)(column_info_alloc - old_alloc);
      size_t first = (size_t)old_alloc + 1;
      size_t last = (size_t)column_info_alloc;
      size_t sum_first_last;
      if (ckd_add (&sum_first_last, first, last))
        xalloc_die ();
      size_t cells_times_two;
      if (ckd_mul (&cells_times_two, sum_first_last, growth))
        xalloc_die ();
      size_t total_new_cells = cells_times_two / 2;

      size_t *p = xinmalloc (total_new_cells, sizeof *p);
      for (idx_t i = old_alloc; i < column_info_alloc; i++)
        {
          column_info[i].col_arr = p;
          p += (size_t)i + 1;
        }
    }

  for (idx_t i = 0; i < max_cols; ++i)
    {
      column_info[i].valid_len = true;
      size_t line_len_val;
      if (ckd_mul (&line_len_val, (size_t)(i + 1), (size_t)MIN_COLUMN_WIDTH))
        xalloc_die ();
      column_info[i].line_len = line_len_val;
      for (idx_t j = 0; j <= i; ++j)
        column_info[i].col_arr[j] = MIN_COLUMN_WIDTH;
    }
}

/* Calculate the number of columns needed to represent the current set
   of files in the current display width.  */

static idx_t
calculate_columns (bool by_columns)
{
  idx_t max_cols = cwd_n_used;
  if (0 < max_idx && max_idx < cwd_n_used)
    max_cols = max_idx;

  init_column_info (max_cols);

  for (idx_t filesno = 0; filesno < cwd_n_used; ++filesno)
    {
      struct fileinfo const *f = sorted_file[filesno];
      size_t name_length = length_of_file_name_and_frills (f);

      for (idx_t i = 0; i < max_cols; ++i)
        {
          if (!column_info[i].valid_len)
            continue;

          idx_t idx;
          if (by_columns)
            {
              idx_t denom = (cwd_n_used + i) / (i + 1);
              if (denom == 0)
                continue;
              idx = filesno / denom;
            }
          else
            {
              idx = filesno % (i + 1);
            }

          size_t real_length = name_length + (idx == i ? 0u : 2u);
          size_t *col_arr = column_info[i].col_arr;

          if (col_arr[idx] < real_length)
            {
              column_info[i].line_len += (real_length - col_arr[idx]);
              col_arr[idx] = real_length;
              column_info[i].valid_len = (column_info[i].line_len < line_length);
            }
        }
    }

  idx_t cols = max_cols;
  for (; cols > 1; --cols)
    {
      if (column_info[cols - 1].valid_len)
        break;
    }

  return cols;
}

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

static void xputs(const char *s) {
  if (fputs(s, stdout) == EOF) {
    exit(EXIT_FAILURE);
  }
}

static void xprintf(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  if (vfprintf(stdout, fmt, ap) < 0) {
    va_end(ap);
    exit(EXIT_FAILURE);
  }
  va_end(ap);
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
      xprintf (_("Usage: %s [OPTION]... [FILE]...\n"), program_name);

      {
        static const char *const pre_note[] = {
          _("\
List information about the FILEs (the current directory by default).\n\
Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n\
")
        };
        for (size_t i = 0; i < sizeof pre_note / sizeof pre_note[0]; i++)
          xputs(pre_note[i]);
      }

      emit_mandatory_arg_note ();

      {
        static const char *const chunks[] = {
          _("\
  -a, --all                  do not ignore entries starting with .\n\
  -A, --almost-all           do not list implied . and ..\n\
      --author               with -l, print the author of each file\n\
  -b, --escape               print C-style escapes for nongraphic characters\n\
"),
          _("\
      --block-size=SIZE      with -l, scale sizes by SIZE when printing them;\n\
                             e.g., '--block-size=M'; see SIZE format below\n\
\n\
"),
          _("\
  -B, --ignore-backups       do not list implied entries ending with ~\n\
"),
          _("\
  -c                         with -lt: sort by, and show, ctime (time of last\n\
                             change of file status information);\n\
                             with -l: show ctime and sort by name;\n\
                             otherwise: sort by ctime, newest first\n\
\n\
"),
          _("\
  -C                         list entries by columns\n\
      --color[=WHEN]         color the output WHEN; more info below\n\
  -d, --directory            list directories themselves, not their contents\n\
  -D, --dired                generate output designed for Emacs' dired mode\n\
"),
          _("\
  -f                         same as -a -U\n\
  -F, --classify[=WHEN]      append indicator (one of */=>@|) to entries WHEN\n\
      --file-type            likewise, except do not append '*'\n\
"),
          _("\
      --format=WORD          across,horizontal (-x), commas (-m), long (-l),\n\
                             single-column (-1), verbose (-l), vertical (-C)\n\
\n\
"),
          _("\
      --full-time            like -l --time-style=full-iso\n\
"),
          _("\
  -g                         like -l, but do not list owner\n\
"),
          _("\
      --group-directories-first\n\
                             group directories before files\n\
"),
          _("\
  -G, --no-group             in a long listing, don't print group names\n\
"),
          _("\
  -h, --human-readable       with -l and -s, print sizes like 1K 234M 2G etc.\n\
      --si                   likewise, but use powers of 1000 not 1024\n\
"),
          _("\
  -H, --dereference-command-line\n\
                             follow symbolic links listed on the command line\n\
"),
          _("\
      --dereference-command-line-symlink-to-dir\n\
                             follow each command line symbolic link\n\
                             that points to a directory\n\
\n\
"),
          _("\
      --hide=PATTERN         do not list implied entries matching shell PATTERN\
\n\
                             (overridden by -a or -A)\n\
\n\
"),
          _("\
      --hyperlink[=WHEN]     hyperlink file names WHEN\n\
"),
          _("\
      --indicator-style=WORD\n\
                             append indicator with style WORD to entry names:\n\
                             none (default), slash (-p),\n\
                             file-type (--file-type), classify (-F)\n\
\n\
"),
          _("\
  -i, --inode                print the index number of each file\n\
  -I, --ignore=PATTERN       do not list implied entries matching shell PATTERN\
\n\
"),
          _("\
  -k, --kibibytes            default to 1024-byte blocks for file system usage;\
\n\
                             used only with -s and per directory totals\n\
\n\
"),
          _("\
  -l                         use a long listing format\n\
"),
          _("\
  -L, --dereference          when showing file information for a symbolic\n\
                             link, show information for the file the link\n\
                             references rather than for the link itself\n\
\n\
"),
          _("\
  -m                         fill width with a comma separated list of entries\
\n\
"),
          _("\
  -n, --numeric-uid-gid      like -l, but list numeric user and group IDs\n\
  -N, --literal              print entry names without quoting\n\
  -o                         like -l, but do not list group information\n\
  -p, --indicator-style=slash\n\
                             append / indicator to directories\n\
"),
          _("\
  -q, --hide-control-chars   print ? instead of nongraphic characters\n\
"),
          _("\
      --show-control-chars   show nongraphic characters as-is (the default,\n\
                             unless program is 'ls' and output is a terminal)\
\n\
\n\
"),
          _("\
  -Q, --quote-name           enclose entry names in double quotes\n\
"),
          _("\
      --quoting-style=WORD   use quoting style WORD for entry names:\n\
                             literal, locale, shell, shell-always,\n\
                             shell-escape, shell-escape-always, c, escape\n\
                             (overrides QUOTING_STYLE environment variable)\n\
\n\
"),
          _("\
  -r, --reverse              reverse order while sorting\n\
  -R, --recursive            list subdirectories recursively\n\
  -s, --size                 print the allocated size of each file, in blocks\n\
"),
          _("\
  -S                         sort by file size, largest first\n\
"),
          _("\
      --sort=WORD            change default 'name' sort to WORD:\n\
                               none (-U), size (-S), time (-t),\n\
                               version (-v), extension (-X), name, width\n\
\n\
"),
          _("\
      --time=WORD            select which timestamp used to display or sort;\n\
                               access time (-u): atime, access, use;\n\
                               metadata change time (-c): ctime, status;\n\
                               modified time (default): mtime, modification;\n\
                               birth time: birth, creation;\n\
                             with -l, WORD determines which time to show;\n\
                             with --sort=time, sort by WORD (newest first)\n\
\n\
"),
          _("\
      --time-style=TIME_STYLE\n\
                             time/date format with -l; see TIME_STYLE below\n\
"),
          _("\
  -t                         sort by time, newest first; see --time\n\
  -T, --tabsize=COLS         assume tab stops at each COLS instead of 8\n\
"),
          _("\
  -u                         with -lt: sort by, and show, access time;\n\
                             with -l: show access time and sort by name;\n\
                             otherwise: sort by access time, newest first\n\
\n\
"),
          _("\
  -U                         do not sort directory entries\n\
"),
          _("\
  -v                         natural sort of (version) numbers within text\n\
"),
          _("\
  -w, --width=COLS           set output width to COLS.  0 means no limit\n\
  -x                         list entries by lines instead of by columns\n\
  -X                         sort alphabetically by entry extension\n\
  -Z, --context              print any security context of each file\n\
      --zero                 end each output line with NUL, not newline\n\
  -1                         list one file per line\n\
")
        };
        for (size_t i = 0; i < sizeof chunks / sizeof chunks[0]; i++)
          xputs(chunks[i]);
      }

      xputs(HELP_OPTION_DESCRIPTION);
      xputs(VERSION_OPTION_DESCRIPTION);

      emit_size_note ();

      {
        static const char *const post_notes[] = {
          _("\
\n\
The TIME_STYLE argument can be full-iso, long-iso, iso, locale, or +FORMAT.\n\
FORMAT is interpreted like in date(1).  If FORMAT is FORMAT1<newline>FORMAT2,\n\
then FORMAT1 applies to non-recent files and FORMAT2 to recent files.\n\
TIME_STYLE prefixed with 'posix-' takes effect only outside the POSIX locale.\n\
Also the TIME_STYLE environment variable sets the default style to use.\n\
"),
          _("\
\n\
The WHEN argument defaults to 'always' and can also be 'auto' or 'never'.\n\
"),
          _("\
\n\
Using color to distinguish file types is disabled both by default and\n\
with --color=never.  With --color=auto, ls emits color codes only when\n\
standard output is connected to a terminal.  The LS_COLORS environment\n\
variable can change the settings.  Use the dircolors(1) command to set it.\n\
"),
          _("\
\n\
Exit status:\n\
 0  if OK,\n\
 1  if minor problems (e.g., cannot access subdirectory),\n\
 2  if serious trouble (e.g., cannot access command-line argument).\n\
")
        };
        for (size_t i = 0; i < sizeof post_notes / sizeof post_notes[0]; i++)
          xputs(post_notes[i]);
      }

      emit_ancillary_info (PROGRAM_NAME);
    }
  exit (status);
}
