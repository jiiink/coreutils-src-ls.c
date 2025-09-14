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
static mode_t file_or_link_mode(const struct fileinfo *file) {
    if (file == NULL) {
        return 0;
    }
    if (color_symlink_as_referent && file->linkok) {
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
    if (putchar((unsigned char)c) == EOF) {
        // Handle error as appropriate, e.g., log or report
        return;
    }
    dired_pos++;
}


/* Output the buffer S, of length S_LEN, and increment DIRED_POS by S_LEN.  */
static void dired_outbuf(const char *s, size_t s_len) {
    if (!s || s_len == 0) {
        return;
    }
    dired_pos += s_len;
    if (fwrite(s, 1, s_len, stdout) != s_len) {
        // Handle output error if needed
        clearerr(stdout);
    }
}

/* Output the string S, and increment DIRED_POS by its length.  */
static void dired_outstring(const char *s) {
    if (s == NULL) {
        return;
    }
    dired_outbuf(s, strlen(s));
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
    if (dired == NULL || obs == NULL) {
        return;
    }
    obstack_grow(obs, &dired_pos, sizeof(dired_pos));
}

/* With -R, this stack is used to help detect directory cycles.
   The device/inode pairs on this stack mirror the pairs in the
   active_dir_set hash table.  */
static struct obstack dev_ino_obstack;

/* Push a pair onto the device/inode stack.  */
static void dev_ino_push(dev_t dev, ino_t ino)
{
    struct dev_ino *di;
    di = obstack_alloc(&dev_ino_obstack, sizeof *di);
    if (di) {
        di->st_dev = dev;
        di->st_ino = ino;
    }
}

/* Pop a dev/ino struct off the global dev_ino_obstack
   and return that struct.  */
static struct dev_ino dev_ino_pop(void)
{
    struct dev_ino *di;
    int dev_ino_size = sizeof(struct dev_ino);

    if (dev_ino_size > obstack_object_size(&dev_ino_obstack)) {
        struct dev_ino empty = {0};
        return empty;
    }

    obstack_blank_fast(&dev_ino_obstack, -dev_ino_size);
    di = (struct dev_ino *)obstack_next_free(&dev_ino_obstack);
    return *di;
}

static int assert_matching_dev_ino(const char *name, struct dev_ino di)
{
    struct stat sb;
    if (stat(name, &sb) < 0)
        return -1;
    if (sb.st_dev != di.st_dev)
        return -1;
    if (sb.st_ino != di.st_ino)
        return -1;
    return 0;
}

static char eolbyte = '\n';

/* Write to standard output PREFIX, followed by the quoting style and
   a space-separated list of the integers stored in OS all on one line.  */

static void dired_dump_obstack(const char *prefix, struct obstack *os) {
    size_t n_pos = obstack_object_size(os) / sizeof(dired_pos);
    if (n_pos == 0) {
        return;
    }

    off_t *pos = obstack_finish(os);
    if (!pos) {
        return;
    }

    if (fputs(prefix, stdout) == EOF) {
        return;
    }

    for (size_t i = 0; i < n_pos; i++) {
        if (printf(" %jd", (intmax_t)pos[i]) < 0) {
            return;
        }
    }

    putchar('\n');
}

/* Return the platform birthtime member of the stat structure,
   or fallback to the mtime member, which we have populated
   from the statx structure or reset to an invalid timestamp
   where birth time is not supported.  */
static struct timespec get_stat_btime(const struct stat *st)
{
#if HAVE_STATX && defined STATX_INO
    return get_stat_mtime(st);
#else
    return get_stat_birthtime(st);
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
int get_file_stat(const char *filename, struct stat *st)
{
    if (!filename || !st) {
        return -1;
    }
    return stat(filename, st);
}

int do_lstat(const char *name, struct stat *st) {
    if (name == NULL || st == NULL) {
        return -1;
    }
    return lstat(name, st);
}

static int stat_for_mode(const char *name, struct stat *st) {
    if (!name || !st) {
        return -1;
    }
    return stat(name, st);
}

static int stat_for_ino(const char *name, struct stat *st) {
    if (!name || !st) {
        return -1;
    }
    return stat(name, st);
}

static int fstat_for_ino(int fd, struct stat *st) {
    if (!st) {
        return -1;
    }
    return fstat(fd, st);
}
#endif

/* Return the address of the first plain %b spec in FMT, or nullptr if
   there is no such spec.  %5b etc. do not match, so that user
   widths/flags are honored.  */

ATTRIBUTE_PURE
static const char *
first_percent_b(const char *fmt)
{
    if (!fmt) {
        return NULL;
    }
    while (*fmt) {
        if (*fmt == '%') {
            if (*(fmt + 1) == 'b') {
                return fmt;
            } else if (*(fmt + 1) == '%') {
                fmt++;
            }
        }
        fmt++;
    }
    return NULL;
}

static char RFC3986[256];
static void file_escape_init(void) {
    for (int i = 0; i < 256; i++) {
        if (c_isalnum(i) || i == '~' || i == '-' || i == '.' || i == '_') {
            RFC3986[i] |= 1;
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

static bool abmon_init(char abmon[12][ABFORMAT_SIZE]) {
#ifndef HAVE_NL_LANGINFO
    return false;
#else
    int max_mon_width = 0;
    int mon_width[12];
    int mon_len[12];

    for (int i = 0; i < 12; i++) {
        const char *abbr = nl_langinfo(ABMON_1 + i);
        size_t len = strnlen(abbr, ABFORMAT_SIZE);
        if (len == ABFORMAT_SIZE || strchr(abbr, '%'))
            return false;
        mon_len[i] = (int)len;
        if (strncpy(abmon[i], abbr, ABFORMAT_SIZE) == NULL)
            return false;
        abmon[i][ABFORMAT_SIZE - 1] = '\0';
        int width = mbswidth(abmon[i], MBSWIDTH_FLAGS);
        if (width < 0)
            return false;
        mon_width[i] = width;
        if (width > max_mon_width)
            max_mon_width = width;
    }

    for (int i = 0; i < 12; i++) {
        int fill = max_mon_width - mon_width[i];
        if (ABFORMAT_SIZE - mon_len[i] <= fill)
            return false;
        bool align_left = !c_isdigit((unsigned char)abmon[i][0]);
        if (fill > 0) {
            if (align_left) {
                memset(abmon[i] + mon_len[i], ' ', fill);
                abmon[i][mon_len[i] + fill] = '\0';
            } else {
                memmove(abmon[i] + fill, abmon[i], mon_len[i] + 1);
                memset(abmon[i], ' ', fill);
            }
        }
    }

    return true;
#endif
}

/* Initialize ABFORMAT and USE_ABFORMAT.  */

static void abformat_init(void) {
    char const *pb[2];
    for (int recent = 0; recent < 2; recent++) {
        pb[recent] = first_percent_b(long_time_format[recent]);
    }
    if (!(pb[0] || pb[1])) {
        return;
    }

    char abmon[12][ABFORMAT_SIZE];
    if (!abmon_init(abmon)) {
        return;
    }

    for (int recent = 0; recent < 2; recent++) {
        char const *fmt = long_time_format[recent];
        for (int i = 0; i < 12; i++) {
            char *nfmt = abformat[recent][i];
            int nbytes;

            if (!pb[recent]) {
                nbytes = snprintf(nfmt, ABFORMAT_SIZE, "%s", fmt);
                if (nbytes < 0 || nbytes >= ABFORMAT_SIZE) {
                    return;
                }
                continue;
            }

            ptrdiff_t prefix_len = pb[recent] - fmt;
            if (prefix_len < 0 || prefix_len >= ABFORMAT_SIZE) {
                return;
            }

            nbytes = snprintf(nfmt, ABFORMAT_SIZE, "%.*s%s%s",
                              (int)prefix_len, fmt, abmon[i], pb[recent] + 2);

            if (nbytes < 0 || nbytes >= ABFORMAT_SIZE) {
                return;
            }
        }
    }

    use_abformat = true;
}

static size_t dev_ino_hash(const void *x, size_t table_size)
{
    if (!x || table_size == 0)
        return 0;

    const struct dev_ino *p = (const struct dev_ino *)x;
    return (size_t)(p->st_ino % (uintmax_t)table_size);
}

static bool dev_ino_compare(const void *x, const void *y)
{
    if (!x || !y) {
        return false;
    }
    const struct dev_ino *a = x;
    const struct dev_ino *b = y;
    return PSAME_INODE(a, b);
}

static void dev_ino_free(void *x) {
    if (x != NULL) {
        free(x);
    }
}

/* Add the device/inode pair (P->st_dev/P->st_ino) to the set of
   active directories.  Return true if there is already a matching
   entry in the table.  */

static bool visit_dir(dev_t dev, ino_t ino)
{
    struct dev_ino *ent = xmalloc(sizeof *ent);
    if (!ent)
        xalloc_die();

    ent->st_ino = ino;
    ent->st_dev = dev;

    struct dev_ino *ent_from_table = hash_insert(active_dir_set, ent);
    if (!ent_from_table)
    {
        free(ent);
        xalloc_die();
    }

    if (ent_from_table != ent)
    {
        free(ent);
        return true;
    }

    return false;
}

static void free_pending_ent(struct pending *p)
{
    if (!p) {
        return;
    }
    free(p->name);
    p->name = NULL;
    free(p->realname);
    p->realname = NULL;
    free(p);
}

static bool is_colored(enum indicator_no type)
{
    size_t len = color_indicator[type].len;
    if (len == 0)
        return false;
    if (len > 2)
        return true;
    const char *s = color_indicator[type].string;
    if (len == 1)
        return s[0] != '0';
    return !(s[0] == '0' && s[1] == '0');
}

static void restore_default_color(void)
{
    if (color_indicator == NULL) {
        return;
    }

    put_indicator(&color_indicator[C_LEFT]);
    put_indicator(&color_indicator[C_RIGHT]);
}

static void set_normal_color(void) {
    if (!print_with_color)
        return;

    if (!is_colored(C_NORM))
        return;

    put_indicator(&color_indicator[C_LEFT]);
    put_indicator(&color_indicator[C_NORM]);
    put_indicator(&color_indicator[C_RIGHT]);
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void sighandler(int sig) {
    if (!SA_NOCLDSTOP) {
        if (signal(sig, SIG_IGN) == SIG_ERR) {
            return;
        }
    }
    if (!interrupt_signal) {
        interrupt_signal = sig;
    }
}

/* A SIGTSTP was received; arrange for the program to suspend itself.  */

static void stophandler(int sig)
{
    if (sig == 0) {
        return;
    }
    if (!(SA_NOCLDSTOP)) {
        if (signal(sig, stophandler) == SIG_ERR) {
            // Handle signal error if required
            return;
        }
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

static void process_signals(void) {
    while (interrupt_signal || stop_signal_count) {
        int sig;
        int stops;
        sigset_t oldset;

        if (used_color)
            restore_default_color();

        if (fflush(stdout) == EOF) {
            /* handle error if needed, but preserve external functionality */
        }

        if (sigprocmask(SIG_BLOCK, &caught_signals, &oldset) == -1) {
            /* handle error if needed */
        }

        sig = interrupt_signal;
        stops = stop_signal_count;

        if (stops > 0) {
            stop_signal_count = stops - 1;
            sig = SIGSTOP;
        } else {
            signal(sig, SIG_DFL);
        }

        raise(sig);

        sigprocmask(SIG_SETMASK, &oldset, NULL);
    }
}

/* Setup signal handlers if INIT is true,
   otherwise restore to the default.  */

static void signal_setup(bool init) {
    static const int sig[] = {
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

#if !SA_NOCLDSTOP
    static bool caught_sig[sizeof(sig) / sizeof(sig[0])];
#endif

    int j;

    if (init) {
#if SA_NOCLDSTOP
        struct sigaction act, oldact;
        sigset_t caught_signals;
        if (sigemptyset(&caught_signals) == -1)
            return;
        for (j = 0; j < nsigs; j++) {
            if (sigaction(sig[j], NULL, &oldact) == -1)
                continue;
            if (oldact.sa_handler != SIG_IGN)
                sigaddset(&caught_signals, sig[j]);
        }
        act.sa_mask = caught_signals;
        act.sa_flags = SA_RESTART;
        for (j = 0; j < nsigs; j++) {
            if (sigismember(&caught_signals, sig[j])) {
                act.sa_handler = (sig[j] == SIGTSTP) ? stophandler : sighandler;
                sigaction(sig[j], &act, NULL);
            }
        }
#else
        for (j = 0; j < nsigs; j++) {
            void (*prev_handler)(int) = signal(sig[j], SIG_IGN);
            caught_sig[j] = (prev_handler != SIG_IGN);
            if (caught_sig[j]) {
                signal(sig[j], sig[j] == SIGTSTP ? stophandler : sighandler);
#if defined(SIGINT) || defined(SIGTERM) || defined(SIGQUIT) || defined(SIGALRM)
                siginterrupt(sig[j], 0);
#endif
            }
        }
#endif
    } else {
#if SA_NOCLDSTOP
        sigset_t caught_signals;
        if (sigemptyset(&caught_signals) == -1)
            return;
        struct sigaction oldact;
        for (j = 0; j < nsigs; j++) {
            if (sigaction(sig[j], NULL, &oldact) == -1)
                continue;
            if (oldact.sa_handler != SIG_IGN)
                signal(sig[j], SIG_DFL);
        }
#else
        for (j = 0; j < nsigs; j++) {
            if (caught_sig[j])
                signal(sig[j], SIG_DFL);
        }
#endif
    }
}


static void signal_init(void) {
    if (!signal_setup(true)) {
        // handle error appropriately, e.g., log or safely abort
    }
}

static void signal_restore(void) {
    signal_setup(false);
}

int main(int argc, char **argv)
{
    int i;
    struct pending *thispend;
    int n_files;

    initialize_main(&argc, &argv);
    set_program_name(argv[0]);
    setlocale(LC_ALL, "");
    bindtextdomain(PACKAGE, LOCALEDIR);
    textdomain(PACKAGE);

    initialize_exit_failure(LS_FAILURE);
    if (atexit(close_stdout) != 0) {
        fprintf(stderr, "Failed to set atexit handler\n");
        exit(EXIT_FAILURE);
    }

    static_assert(ARRAY_CARDINALITY(color_indicator) == ARRAY_CARDINALITY(indicator_name));

    exit_status = EXIT_SUCCESS;
    print_dir_name = true;
    pending_dirs = NULL;

    current_time.tv_sec = TYPE_MINIMUM(time_t);
    current_time.tv_nsec = -1;

    i = decode_switches(argc, argv);

    if (print_with_color)
        parse_ls_color();

    if (print_with_color)
        tabsize = 0;

    if (directories_first) {
        check_symlink_mode = true;
    } else if (print_with_color) {
        if (is_colored(C_ORPHAN)
            || (is_colored(C_EXEC) && color_symlink_as_referent)
            || (is_colored(C_MISSING) && format == long_format))
            check_symlink_mode = true;
    }

    if (dereference == DEREF_UNDEFINED) {
        dereference = ((immediate_dirs
                        || indicator_style == classify
                        || format == long_format)
                        ? DEREF_NEVER
                        : DEREF_COMMAND_LINE_SYMLINK_TO_DIR);
    }

    if (recursive) {
        active_dir_set = hash_initialize(INITIAL_TABLE_SIZE, NULL,
                                         dev_ino_hash, dev_ino_compare, dev_ino_free);
        if (!active_dir_set)
            xalloc_die();
        obstack_init(&dev_ino_obstack);
    }

    localtz = tzalloc(getenv("TZ"));

    format_needs_stat = ((sort_type == sort_time) || (sort_type == sort_size)
                         || (format == long_format)
                         || print_block_size || print_hyperlink || print_scontext);
    format_needs_type = (!format_needs_stat)
                        && (recursive || print_with_color || print_scontext
                            || directories_first
                            || (indicator_style != none));
    format_needs_capability = print_with_color && is_colored(C_CAP);

    if (dired) {
        obstack_init(&dired_obstack);
        obstack_init(&subdired_obstack);
    }

    if (print_hyperlink) {
        file_escape_init();

        hostname = xgethostname();
        if (!hostname)
            hostname = "";
    }

    cwd_n_alloc = 100;
    cwd_file = xmalloc(cwd_n_alloc * sizeof *cwd_file);
    if (!cwd_file)
        xalloc_die();
    cwd_n_used = 0;

    clear_files();

    n_files = argc - i;

    if (n_files <= 0) {
        if (immediate_dirs)
            gobble_file(".", directory, NOT_AN_INODE_NUMBER, true, NULL);
        else
            queue_directory(".", NULL, true);
    } else {
        while (i < argc)
            gobble_file(argv[i++], unknown, NOT_AN_INODE_NUMBER, true, NULL);
    }

    if (cwd_n_used) {
        sort_files();
        if (!immediate_dirs)
            extract_dirs_from_files(NULL, true);
    }

    if (cwd_n_used) {
        print_current_files();
        if (pending_dirs)
            dired_outbyte('\n');
    } else if (n_files <= 1 && pending_dirs && pending_dirs->next == NULL) {
        print_dir_name = false;
    }

    while (pending_dirs) {
        thispend = pending_dirs;
        pending_dirs = pending_dirs->next;

        if (LOOP_DETECT) {
            if (thispend->name == NULL) {
                struct dev_ino di = dev_ino_pop();
                struct dev_ino *found = hash_remove(active_dir_set, &di);
                affirm(found);
                dev_ino_free(found);
                free_pending_ent(thispend);
                continue;
            }
        }

        print_dir(thispend->name, thispend->realname, thispend->command_line_arg);

        free_pending_ent(thispend);
        print_dir_name = true;
    }

    if (print_with_color && used_color) {
        int j;

        if (!(color_indicator[C_LEFT].len == 2
              && memcmp(color_indicator[C_LEFT].string, "\033[", 2) == 0
              && color_indicator[C_RIGHT].len == 1
              && color_indicator[C_RIGHT].string[0] == 'm'))
            restore_default_color();

        fflush(stdout);
        signal_restore();

        for (j = stop_signal_count; j; j--)
            raise(SIGSTOP);
        j = interrupt_signal;
        if (j)
            raise(j);
    }

    if (dired) {
        dired_dump_obstack("//DIRED//", &dired_obstack);
        dired_dump_obstack("//SUBDIRED//", &subdired_obstack);
        printf("//DIRED-OPTIONS// --quoting-style=%s\n",
               quoting_style_args[get_quoting_style(filename_quoting_options)]);
    }

    if (LOOP_DETECT) {
        assure(hash_get_n_entries(active_dir_set) == 0);
        hash_free(active_dir_set);
    }

    return exit_status;
}

/* Return the line length indicated by the value given by SPEC, or -1
   if unsuccessful.  0 means no limit on line length.  */

static ptrdiff_t decode_line_length(const char *spec)
{
    uintmax_t val;
    int result = xstrtoumax(spec, NULL, 0, &val, "");
    if (result == LONGINT_OK) {
        return (val <= (uintmax_t)(MIN(PTRDIFF_MAX, SIZE_MAX))) ? (ptrdiff_t)val : 0;
    } else if (result == LONGINT_OVERFLOW) {
        return 0;
    } else if (result == LONGINT_INVALID ||
               result == LONGINT_INVALID_SUFFIX_CHAR ||
               result == LONGINT_INVALID_SUFFIX_CHAR_WITH_OVERFLOW) {
        return -1;
    }
    return -1;
}

/* Return true if standard output is a tty, caching the result.  */

static bool stdout_isatty(void) {
    static int out_tty = -1;
    if (out_tty < 0) {
        int res = isatty(STDOUT_FILENO);
        out_tty = (res == 1) ? 1 : 0;
    }
    return out_tty == 1;
}

/* Set all the option flags according to the switches specified.
   Return the index of the first non-option argument.  */

static int decode_switches(int argc, char **argv)
{
    const char *time_style_option = NULL;

    bool kibibytes_specified = false;
    int format_opt = -1;
    int hide_control_chars_opt = -1;
    int quoting_style_opt = -1;
    int sort_opt = -1;
    ptrdiff_t tabsize_opt = -1;
    ptrdiff_t width_opt = -1;

    while (1) {
        int oi = -1;
        int c = getopt_long(argc, argv,
                            "abcdfghiklmnopqrstuvw:xABCDFGHI:LNQRST:UXZ1",
                            long_options, &oi);
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
                int i;
                if (optarg)
                    i = XARGMATCH("--classify", optarg, when_args, when_types);
                else
                    i = when_always;
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
                if (!hide)
                    error(LS_FAILURE, 0, _("memory allocation failure"));
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
                int i;
                if (optarg)
                    i = XARGMATCH("--color", optarg, when_args, when_types);
                else
                    i = when_always;
                print_with_color = (i == when_always || (i == when_if_tty && stdout_isatty()));
                break;
            }
            case HYPERLINK_OPTION: {
                int i;
                if (optarg)
                    i = XARGMATCH("--hyperlink", optarg, when_args, when_types);
                else
                    i = when_always;
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

    if (!output_block_size) {
        const char *ls_block_size = getenv("LS_BLOCK_SIZE");
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

    if (format_opt >= 0)
        format = format_opt;
    else if (ls_mode == LS_LS)
        format = stdout_isatty() ? many_per_line : one_per_line;
    else if (ls_mode == LS_MULTI_COL)
        format = many_per_line;
    else
        format = long_format;

    ptrdiff_t linelen = width_opt;
    if (format == many_per_line || format == horizontal || format == with_commas || print_with_color) {
#ifdef TIOCGWINSZ
        if (linelen < 0) {
            struct winsize ws;
            if (stdout_isatty() && ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) >= 0 && ws.ws_col > 0)
                linelen = ws.ws_col <= MIN(PTRDIFF_MAX, SIZE_MAX) ? ws.ws_col : 0;
        }
#endif
        if (linelen < 0) {
            const char *p = getenv("COLUMNS");
            if (p && *p) {
                linelen = decode_line_length(p);
                if (linelen < 0)
                    error(0, 0, _("ignoring invalid width in environment variable COLUMNS: %s"), quote(p));
            }
        }
    }

    line_length = linelen < 0 ? 80 : linelen;
    max_idx = line_length / MIN_COLUMN_WIDTH;
    max_idx += (line_length % MIN_COLUMN_WIDTH != 0);

    if (format == many_per_line || format == horizontal || format == with_commas) {
        if (tabsize_opt >= 0)
            tabsize = tabsize_opt;
        else {
            tabsize = 8;
            const char *p = getenv("TABSIZE");
            if (p) {
                uintmax_t tmp = 0;
                if (xstrtoumax(p, NULL, 0, &tmp, "") == LONGINT_OK && tmp <= SIZE_MAX)
                    tabsize = tmp;
                else
                    error(0, 0, _("ignoring invalid tab size in environment variable TABSIZE: %s"), quote(p));
            }
        }
    }

    if (hide_control_chars_opt < 0)
        qmark_funny_chars = (ls_mode == LS_LS && stdout_isatty());
    else
        qmark_funny_chars = hide_control_chars_opt;

    int qs = quoting_style_opt;
    if (qs < 0)
        qs = getenv_quoting_style();
    if (qs < 0)
        qs = (ls_mode == LS_LS ? (stdout_isatty() ? shell_escape_quoting_style : -1) : escape_quoting_style);
    if (qs >= 0)
        set_quoting_style(NULL, qs);
    qs = get_quoting_style(NULL);
    align_variable_outer_quotes = ((format == long_format ||
            ((format == many_per_line || format == horizontal) && line_length)) &&
            (qs == shell_quoting_style ||
            qs == shell_escape_quoting_style ||
            qs == c_maybe_quoting_style));
    filename_quoting_options = clone_quoting_options(NULL);
    if (qs == escape_quoting_style)
        set_char_quoting(filename_quoting_options, ' ', 1);
    if (file_type <= indicator_style) {
        const char *p;
        for (p = &"*=>@|"[indicator_style - file_type]; *p; p++)
            set_char_quoting(filename_quoting_options, *p, 1);
    }
    dirname_quoting_options = clone_quoting_options(NULL);
    set_char_quoting(dirname_quoting_options, ':', 1);

    dired = dired && (format == long_format) && !print_hyperlink;

    if (eolbyte < dired)
        error(LS_FAILURE, 0, _("--dired and --zero are incompatible"));

    sort_type = (sort_opt >= 0 ? sort_opt : (format != long_format && explicit_time) ? sort_time : sort_name);

    if (format == long_format) {
        const char *style = time_style_option;
        static const char posix_prefix[] = "posix-";

        if (!style) {
            style = getenv("TIME_STYLE");
            if (!style)
                style = "locale";
        }

        while (strncmp(style, posix_prefix, sizeof(posix_prefix) - 1) == 0) {
            if (!hard_locale(LC_TIME))
                return optind;
            style += sizeof(posix_prefix) - 1;
        }

        if (*style == '+') {
            const char *p0 = style + 1;
            char *p0nl = strchr((char *)p0, '\n');
            const char *p1 = p0;
            if (p0nl) {
                if (strchr(p0nl + 1, '\n'))
                    error(LS_FAILURE, 0, _("invalid time style format %s"),
                          quote(p0));
                *p0nl++ = '\0';
                p1 = p0nl;
            }
            long_time_format[0] = p0;
            long_time_format[1] = p1;
        } else {
            switch (x_timestyle_match(style, 1, time_style_args,
                                      (const char *)time_style_types,
                                      sizeof(*time_style_types), LS_FAILURE)) {
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
                            long_time_format[i] =
                                dcgettext(NULL, long_time_format[i], LC_TIME);
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

static bool get_funky_string(char **dest, const char **src, bool equals_end, size_t *output_count)
{
    size_t count = 0;
    unsigned char num = 0;
    enum {
        ST_GND, ST_BACKSLASH, ST_OCTAL, ST_HEX, ST_CARET, ST_END, ST_ERROR
    } state = ST_GND;
    const char *p = *src;
    char *q = *dest;

    while (state < ST_END) {
        switch (state) {
            case ST_GND:
                switch (*p) {
                    case ':':
                    case '\0':
                        state = ST_END;
                        break;
                    case '\\':
                        state = ST_BACKSLASH;
                        p++;
                        break;
                    case '^':
                        state = ST_CARET;
                        p++;
                        break;
                    case '=':
                        if (equals_end) {
                            state = ST_END;
                            break;
                        }
                        /* fallthrough */
                    default:
                        *q++ = *p++;
                        count++;
                        break;
                }
                break;

            case ST_BACKSLASH:
                switch (*p) {
                    case '0': case '1': case '2': case '3':
                    case '4': case '5': case '6': case '7':
                        state = ST_OCTAL;
                        num = (unsigned char)(*p - '0');
                        p++;
                        break;
                    case 'x': case 'X':
                        state = ST_HEX;
                        num = 0;
                        p++;
                        break;
                    case 'a':
                        num = '\a'; goto bs_done;
                    case 'b':
                        num = '\b'; goto bs_done;
                    case 'e':
                        num = 27; goto bs_done;
                    case 'f':
                        num = '\f'; goto bs_done;
                    case 'n':
                        num = '\n'; goto bs_done;
                    case 'r':
                        num = '\r'; goto bs_done;
                    case 't':
                        num = '\t'; goto bs_done;
                    case 'v':
                        num = '\v'; goto bs_done;
                    case '?':
                        num = 127; goto bs_done;
                    case '_':
                        num = ' '; goto bs_done;
                    case '\0':
                        state = ST_ERROR;
                        break;
                    default:
                        num = *p; goto bs_done;
bs_done:
                        *q++ = (char)num;
                        count++;
                        p++;
                        state = ST_GND;
                        break;
                }
                break;

            case ST_OCTAL: {
                int digits = 0;
                while (digits < 2 && *p >= '0' && *p <= '7') {
                    num = (unsigned char)((num << 3) + (*p - '0'));
                    p++;
                    digits++;
                }
                *q++ = (char)num;
                count++;
                state = ST_GND;
                break;
            }

            case ST_HEX: {
                int digits = 0;
                while (digits < 2) {
                    if (*p >= '0' && *p <= '9') {
                        num = (unsigned char)((num << 4) + (*p - '0'));
                        p++;
                    } else if (*p >= 'a' && *p <= 'f') {
                        num = (unsigned char)((num << 4) + (*p - 'a' + 10));
                        p++;
                    } else if (*p >= 'A' && *p <= 'F') {
                        num = (unsigned char)((num << 4) + (*p - 'A' + 10));
                        p++;
                    } else {
                        break;
                    }
                    digits++;
                }
                *q++ = (char)num;
                count++;
                state = ST_GND;
                break;
            }

            case ST_CARET:
                if (*p >= '@' && *p <= '~') {
                    *q++ = (char)(*p++ & 0x1F);
                    count++;
                    state = ST_GND;
                } else if (*p == '?') {
                    *q++ = 127;
                    p++;
                    count++;
                    state = ST_GND;
                } else {
                    state = ST_ERROR;
                }
                break;

            case ST_END:
            case ST_ERROR:
            default:
                goto finish;
        }
    }
finish:
    *dest = q;
    *src = p;
    *output_count = count;
    return (state != ST_ERROR);
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

static bool known_term_type(void) {
    const char *term = getenv("TERM");
    if (!term || !*term)
        return false;

    const char *line = G_line;
    size_t offset = 0;
    size_t g_line_size = sizeof(G_line);

    while (offset < g_line_size && line[offset] != '\0') {
        if (strncmp(line + offset, "TERM ", 5) == 0) {
            if (fnmatch(line + offset + 5, term, 0) == 0)
                return true;
        }
        size_t len = strnlen(line + offset, g_line_size - offset);
        if (len == g_line_size - offset)
            break;
        offset += len + 1;
    }

    return false;
}

static void parse_ls_color(void)
{
    const char *p;
    char *buf;
    char label0 = '\0', label1 = '\0';
    struct color_ext_type *ext = NULL;

    p = getenv("LS_COLORS");
    if (!p || *p == '\0') {
        const char *colorterm = getenv("COLORTERM");
        if (!(colorterm && *colorterm) && !known_term_type())
            print_with_color = false;
        return;
    }

    buf = color_buf = xstrdup(p);
    enum parse_state state = PS_START;

    while (1) {
        switch (state) {
            case PS_START:
                if (*p == ':') {
                    p++;
                } else if (*p == '*') {
                    ext = xmalloc(sizeof *ext);
                    if (!ext) {
                        free(color_buf);
                        print_with_color = false;
                        return;
                    }
                    ext->next = color_ext_list;
                    color_ext_list = ext;
                    ext->exact_match = false;
                    p++;
                    ext->ext.string = buf;
                    state = get_funky_string(&buf, &p, true, &ext->ext.len) ? PS_4 : PS_FAIL;
                } else if (*p == '\0') {
                    state = PS_DONE;
                    goto done;
                } else {
                    label0 = *p++;
                    state = PS_2;
                }
                break;

            case PS_2:
                if (*p) {
                    label1 = *p++;
                    state = PS_3;
                } else {
                    state = PS_FAIL;
                }
                break;

            case PS_3: {
                state = PS_FAIL;
                if (*(p++) == '=') {
                    bool found = false;
                    for (int i = 0; i < ARRAY_CARDINALITY(indicator_name); i++) {
                        if (label0 == indicator_name[i][0] && label1 == indicator_name[i][1]) {
                            color_indicator[i].string = buf;
                            if (get_funky_string(&buf, &p, false, &color_indicator[i].len)) {
                                state = PS_START;
                            }
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        char prefix[3] = {label0, label1, '\0'};
                        error(0, 0, _("unrecognized prefix: %s"), quote(prefix));
                    }
                }
                break;
            }
            case PS_4:
                if (*(p++) == '=') {
                    ext->seq.string = buf;
                    state = get_funky_string(&buf, &p, false, &ext->seq.len) ? PS_START : PS_FAIL;
                } else {
                    state = PS_FAIL;
                }
                break;

            case PS_FAIL:
                goto done;

            case PS_DONE:
            default:
                affirm(0);
        }
    }
done:

    if (state == PS_FAIL) {
        struct color_ext_type *e = color_ext_list;
        struct color_ext_type *e2;
        error(0, 0, _("unparsable value for LS_COLORS environment variable"));
        free(color_buf);
        while (e) {
            e2 = e;
            e = e->next;
            free(e2);
        }
        print_with_color = false;
    } else {
        for (struct color_ext_type *e1 = color_ext_list; e1; e1 = e1->next) {
            for (struct color_ext_type *e2 = e1->next; e2; e2 = e2->next) {
                if (e2->ext.len < SIZE_MAX && e1->ext.len == e2->ext.len) {
                    if (memcmp(e1->ext.string, e2->ext.string, e1->ext.len) == 0) {
                        e2->ext.len = SIZE_MAX;
                    } else if (c_strncasecmp(e1->ext.string, e2->ext.string, e1->ext.len) == 0) {
                        static bool case_ignored = false;
                        if (case_ignored) {
                            e2->ext.len = SIZE_MAX;
                        } else if (e1->seq.len == e2->seq.len &&
                                   memcmp(e1->seq.string, e2->seq.string, e1->seq.len) == 0) {
                            e2->ext.len = SIZE_MAX;
                            case_ignored = true;
                        } else {
                            e1->exact_match = true;
                            e2->exact_match = true;
                        }
                    }
                }
            }
        }
    }

    if (color_indicator[C_LINK].len == 6 &&
        !STRNCMP_LIT(color_indicator[C_LINK].string, "target"))
        color_symlink_as_referent = true;
}

/* Return the quoting style specified by the environment variable
   QUOTING_STYLE if set and valid, -1 otherwise.  */

static int getenv_quoting_style(void)
{
    const char *q_style = getenv("QUOTING_STYLE");
    int idx;

    if (!q_style)
        return -1;

    idx = ARGMATCH(q_style, quoting_style_args, quoting_style_vals);
    if (idx < 0) {
        error(0, 0,
              _("ignoring invalid value of environment variable QUOTING_STYLE: %s"),
              quote(q_style));
        return -1;
    }

    return quoting_style_vals[idx];
}

/* Set the exit status to report a failure.  If SERIOUS, it is a
   serious failure; otherwise, it is merely a minor problem.  */

static void set_exit_status(bool serious) {
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

static void file_failure(bool serious, const char *message, const char *file) {
    if (!message || !file) {
        error(0, 0, "Invalid parameter(s) to file_failure");
        set_exit_status(true);
        return;
    }
    error(0, errno, "%s: %s", message, quoteaf(file));
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

static void queue_directory(const char *name, const char *realname, bool command_line_arg) {
    struct pending *new_dir = xmalloc(sizeof(*new_dir));
    if (!new_dir) {
        // Proper error handling: xmalloc should not return NULL, but just in case
        exit(EXIT_FAILURE);
    }

    new_dir->realname = (realname && *realname) ? xstrdup(realname) : NULL;
    new_dir->name = (name && *name) ? xstrdup(name) : NULL;
    new_dir->command_line_arg = command_line_arg;
    new_dir->next = pending_dirs;
    pending_dirs = new_dir;
}

/* Read directory NAME, and list the files in it.
   If REALNAME is nonzero, print its name instead of NAME;
   this is used for symbolic links to directories.
   COMMAND_LINE_ARG means this directory was mentioned on the command line.  */

static void print_dir(const char *name, const char *realname, bool command_line_arg)
{
    DIR *dirp = NULL;
    struct dirent *next;
    uintmax_t total_blocks = 0;
    static bool first = true;
    int dirfd_value = -1;
    struct stat dir_stat;
    char *absolute_name = NULL;
    bool print_dir_header = recursive || print_dir_name;
    int err;

    errno = 0;
    dirp = opendir(name);
    if (!dirp) {
        file_failure(command_line_arg, _("cannot open directory %s"), name);
        return;
    }

    if (LOOP_DETECT) {
        dirfd_value = dirfd(dirp);
        if ((dirfd_value >= 0 ? fstat_for_ino(dirfd_value, &dir_stat) : stat_for_ino(name, &dir_stat)) < 0) {
            file_failure(command_line_arg, _("cannot determine device and inode of %s"), name);
            closedir(dirp);
            return;
        }
        if (visit_dir(dir_stat.st_dev, dir_stat.st_ino)) {
            error(0, 0, _("%s: not listing already-listed directory"), quotef(name));
            closedir(dirp);
            set_exit_status(true);
            return;
        }
        dev_ino_push(dir_stat.st_dev, dir_stat.st_ino);
    }

    clear_files();

    if (print_dir_header) {
        if (!first)
            dired_outbyte('\n');
        first = false;
        dired_indent();

        if (print_hyperlink) {
            absolute_name = canonicalize_filename_mode(name, CAN_MISSING);
            if (!absolute_name)
                file_failure(command_line_arg, _("error canonicalizing %s"), name);
        }
        quote_name(realname ? realname : name, dirname_quoting_options, -1, NULL, true,
                   &subdired_obstack, absolute_name);
        if (absolute_name)
            free(absolute_name);

        dired_outstring(":\n");
    }

    while (1) {
        errno = 0;
        next = readdir(dirp);
        if (!next) {
            err = errno;
#if ! (2 < __GLIBC__ + (3 <= __GLIBC_MINOR__))
            if (err == ENOENT)
                break;
#endif
            if (err == 0)
                break;
            file_failure(command_line_arg, _("reading directory %s"), name);
            if (err != EOVERFLOW)
                break;
            process_signals();
            continue;
        }

        if (file_ignored(next->d_name))
            continue;

        enum filetype type;
#if HAVE_STRUCT_DIRENT_D_TYPE
        type = d_type_filetype[next->d_type];
#else
        type = unknown;
#endif
        total_blocks += gobble_file(next->d_name, type, RELIABLE_D_INO(next), false, name);

        if (format == one_per_line && sort_type == sort_none && !print_block_size && !recursive) {
            sort_files();
            print_current_files();
            clear_files();
        }

        process_signals();
    }

    if (closedir(dirp) != 0) {
        file_failure(command_line_arg, _("closing directory %s"), name);
    }

    sort_files();

    if (recursive)
        extract_dirs_from_files(name, false);

    if (format == long_format || print_block_size) {
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

    if (cwd_n_used)
        print_current_files();
}

/* Add 'pattern' to the list of patterns for which files that match are
   not listed.  */

static void add_ignore_pattern(const char *pattern) {
    if (!pattern) {
        return;
    }

    struct ignore_pattern *ignore = malloc(sizeof(struct ignore_pattern));
    if (!ignore) {
        return;
    }
    ignore->pattern = pattern;
    ignore->next = ignore_patterns;
    ignore_patterns = ignore;
}

/* Return true if one of the PATTERNS matches FILE.  */

static bool
patterns_match(const struct ignore_pattern *patterns, const char *file)
{
    const struct ignore_pattern *p = patterns;
    if (!patterns || !file) {
        return false;
    }
    while (p) {
        if (fnmatch(p->pattern, file, FNM_PERIOD) == 0) {
            return true;
        }
        p = p->next;
    }
    return false;
}

/* Return true if FILE should be ignored.  */

static bool file_ignored(const char *name)
{
    if (!name) {
        return false;
    }

    bool is_dot = name[0] == '.';
    bool is_double_dot = is_dot && name[1] == '.' && name[2] == '\0';
    bool is_single_dot = is_dot && name[1] == '\0';

    if (ignore_mode != IGNORE_MINIMAL && is_dot) {
        if (ignore_mode == IGNORE_DEFAULT || (!is_single_dot && !is_double_dot)) {
            return true;
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

static uintmax_t unsigned_file_size(off_t size)
{
    if (size >= 0) {
        return (uintmax_t)size;
    }
    return (uintmax_t)(size) + (uintmax_t)OFF_T_MAX - (uintmax_t)OFF_T_MIN + 1;
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
static bool has_capability(const char *name)
{
    (void)name;
    errno = ENOTSUP;
    return false;
}

#endif

/* Enter and remove entries in the table 'cwd_file'.  */

static void free_ent(struct fileinfo *f) {
    if (!f) {
        return;
    }

    free(f->name);
    f->name = NULL;
    free(f->linkname);
    f->linkname = NULL;
    free(f->absolute_name);
    f->absolute_name = NULL;

    if (f->scontext && f->scontext != UNKNOWN_SECURITY_CONTEXT) {
        aclinfo_scontext_free(f->scontext);
        f->scontext = NULL;
    }
}

/* Empty the table of files.  */
static void clear_files(void)
{
    if (sorted_file)
    {
        for (idx_t i = 0; i < cwd_n_used; i++)
        {
            if (sorted_file[i])
            {
                free_ent(sorted_file[i]);
                sorted_file[i] = NULL;
            }
        }
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
static int file_has_aclinfo_cache(const char *file, struct fileinfo *f, struct aclinfo *ai, int flags)
{
    static int unsupported_return = 0;
    static char *unsupported_scontext = NULL;
    static int unsupported_scontext_err = 0;
    static dev_t unsupported_device = 0;

    if (f && f->stat_ok && unsupported_scontext && f->stat.st_dev == unsupported_device)
    {
        ai->buf = ai->u.__gl_acl_ch;
        ai->size = 0;
        ai->scontext = unsupported_scontext;
        ai->scontext_err = unsupported_scontext_err;
        errno = ENOTSUP;
        return unsupported_return;
    }

    errno = 0;
    int n = file_has_aclinfo(file, ai, flags);
    int err = errno;

    if (f && f->stat_ok && n <= 0 && !acl_errno_valid(err) &&
        (!(flags & ACL_GET_SCONTEXT) || !acl_errno_valid(ai->scontext_err)))
    {
        unsupported_return = n;
        unsupported_scontext = ai->scontext;
        unsupported_scontext_err = ai->scontext_err;
        unsupported_device = f->stat.st_dev;
    }

    return n;
}

/* Cache has_capability failure, when it's trivial to do.
   Like has_capability, but when F's st_dev says it's on a file
   system lacking capability support, return 0 with ENOTSUP immediately.  */
static bool has_capability_cache(const char *file, struct fileinfo *f) {
    static bool unsupported_cached = false;
    static dev_t unsupported_device = 0;
    bool has_cap;

    if (!file || !f) {
        errno = EINVAL;
        return false;
    }

    if (f->stat_ok && unsupported_cached && f->stat.st_dev == unsupported_device) {
        errno = ENOTSUP;
        return false;
    }

    has_cap = has_capability(file);
    if (f->stat_ok && !has_cap && !acl_errno_valid(errno)) {
        unsupported_cached = true;
        unsupported_device = f->stat.st_dev;
    }

    return has_cap;
}

static bool needs_quoting(const char *name) {
    char test[2] = {0};
    size_t len;
    if (!name) {
        return false;
    }
    len = quotearg_buffer(test, sizeof(test), name, -1, filename_quoting_options);
    if (len == (size_t)-1) {
        return false;
    }
    return (*name != *test) || (strlen(name) != len);
}

/* Add a file to the current table of files.
   Verify that the file exists, and print an error message if it does not.
   Return the number of blocks that the file occupies.  */
static uintmax_t gobble_file(const char *name, enum filetype type, ino_t inode,
                             bool command_line_arg, const char *dirname) {
  uintmax_t blocks = 0;
  struct fileinfo *f;

  affirm(!command_line_arg || inode == NOT_AN_INODE_NUMBER);

  if (cwd_n_used == cwd_n_alloc)
    cwd_file = xpalloc(cwd_file, &cwd_n_alloc, 1, -1, sizeof *cwd_file);

  f = &cwd_file[cwd_n_used];
  memset(f, 0, sizeof *f);
  f->stat.st_ino = inode;
  f->filetype = type;
  f->scontext = UNKNOWN_SECURITY_CONTEXT;
  f->quoted = -1;

  if (!cwd_some_quoted && align_variable_outer_quotes) {
    f->quoted = needs_quoting(name);
    if (f->quoted)
      cwd_some_quoted = 1;
  }

  bool is_directory = (type == directory || type == unknown);
  bool is_symlink = (type == symbolic_link || type == unknown);
  bool check_stat = command_line_arg || print_hyperlink || format_needs_stat ||
                    (format_needs_type && type == unknown) ||
                    (is_directory && print_with_color &&
                     (is_colored(C_OTHER_WRITABLE) ||
                      is_colored(C_STICKY) ||
                      is_colored(C_STICKY_OTHER_WRITABLE))) ||
                    ((print_inode || format_needs_type) && is_symlink &&
                     (dereference == DEREF_ALWAYS || color_symlink_as_referent || check_symlink_mode)) ||
                    (print_inode && inode == NOT_AN_INODE_NUMBER) ||
                    ((type == normal || type == unknown) &&
                     (indicator_style == classify ||
                      (print_with_color &&
                       (is_colored(C_EXEC) ||
                        is_colored(C_SETUID) ||
                        is_colored(C_SETGID)))));

  const char *full_name = name;
  if ((check_stat || print_scontext || format_needs_capability) &&
      name[0] != '/' && dirname) {
    size_t len = strlen(name) + strlen(dirname) + 2;
    char *p = alloca(len);
    attach(p, dirname, name);
    full_name = p;
  }

  bool do_deref = dereference == DEREF_ALWAYS;
  int err = 0;
  if (check_stat) {
    if (print_hyperlink) {
      f->absolute_name = canonicalize_filename_mode(full_name, CAN_MISSING);
      if (!f->absolute_name)
        file_failure(command_line_arg, _("error canonicalizing %s"), full_name);
    }

    switch (dereference) {
      case DEREF_ALWAYS:
        err = do_stat(full_name, &f->stat);
        do_deref = true;
        break;
      case DEREF_COMMAND_LINE_ARGUMENTS:
      case DEREF_COMMAND_LINE_SYMLINK_TO_DIR:
        if (command_line_arg) {
          err = do_stat(full_name, &f->stat);
          do_deref = true;
          if (dereference == DEREF_COMMAND_LINE_ARGUMENTS)
            break;
          bool need_lstat = (err < 0 ? (errno == ENOENT || errno == ELOOP)
                                     : !S_ISDIR(f->stat.st_mode));
          if (!need_lstat)
            break;
        }
        /* fallthrough */
      case DEREF_NEVER:
        err = do_lstat(full_name, &f->stat);
        do_deref = false;
        break;
      case DEREF_UNDEFINED:
      default:
        unreachable();
    }

    if (err != 0) {
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

  bool get_scontext = (format == long_format) || print_scontext;
  bool check_capability = format_needs_capability && (type == normal);

  if (get_scontext || check_capability) {
    struct aclinfo ai;
    int aclinfo_flags = (do_deref ? ACL_SYMLINK_FOLLOW : 0) |
                        (get_scontext ? ACL_GET_SCONTEXT : 0) |
                        filetype_d_type[type];
    int n = file_has_aclinfo_cache(full_name, f, &ai, aclinfo_flags);
    bool have_acl = n > 0;
    bool have_scontext = !ai.scontext_err;
    bool cannot_access_acl = (n < 0) && (errno == EACCES || errno == ENOENT);

    if (!have_scontext && !have_acl)
      f->acl_type = cannot_access_acl ? ACL_T_UNKNOWN : ACL_T_NONE;
    else if (have_scontext && !have_acl)
      f->acl_type = ACL_T_LSM_CONTEXT_ONLY;
    else
      f->acl_type = ACL_T_YES;
    any_has_acl |= f->acl_type != ACL_T_NONE;

    if (format == long_format && n < 0 && !cannot_access_acl)
      error(0, errno, "%s", quotef(full_name));
    else if (print_scontext && ai.scontext_err &&
             !(is_ENOTSUP(ai.scontext_err) || ai.scontext_err == ENODATA)) {
      error(0, ai.scontext_err, "%s", quotef(full_name));
    }

    if (check_capability && aclinfo_has_xattr(&ai, XATTR_NAME_CAPS))
      f->has_capability = has_capability_cache(full_name, f);

    f->scontext = ai.scontext;
    ai.scontext = NULL;
    aclinfo_free(&ai);
  }

  if (type == symbolic_link &&
      (format == long_format || check_symlink_mode)) {
    struct stat linkstats;
    get_link_name(full_name, f, command_line_arg);
    if (f->linkname && f->quoted == 0 && needs_quoting(f->linkname))
      f->quoted = -1;
    if (f->linkname &&
        (file_type <= indicator_style || check_symlink_mode) &&
        stat_for_mode(full_name, &linkstats) == 0) {
      f->linkok = true;
      f->linkmode = linkstats.st_mode;
    }
  }

  blocks = STP_NBLOCKS(&f->stat);
  if (format == long_format || print_block_size) {
    char buf[LONGEST_HUMAN_READABLE + 1];
    int len = mbswidth(human_readable(blocks, buf, human_output_opts,
                                      ST_NBLOCKSIZE, output_block_size),
                       MBSWIDTH_FLAGS);
    if (block_size_width < len)
      block_size_width = len;
  }

  if (format == long_format) {
    if (print_owner) {
      int len = format_user_width(f->stat.st_uid);
      if (owner_width < len)
        owner_width = len;
    }
    if (print_group) {
      int len = format_group_width(f->stat.st_gid);
      if (group_width < len)
        group_width = len;
    }
    if (print_author) {
      int len = format_user_width(f->stat.st_author);
      if (author_width < len)
        author_width = len;
    }
  }

  if (print_scontext) {
    int len = strlen(f->scontext);
    if (scontext_width < len)
      scontext_width = len;
  }

  if (format == long_format) {
    char b[INT_BUFSIZE_BOUND(uintmax_t)];
    int b_len = strlen(umaxtostr(f->stat.st_nlink, b));
    if (nlink_width < b_len)
      nlink_width = b_len;

    if ((type == chardev) || (type == blockdev)) {
      char buf[INT_BUFSIZE_BOUND(uintmax_t)];
      int len = strlen(umaxtostr(major(f->stat.st_rdev), buf));
      if (major_device_number_width < len)
        major_device_number_width = len;
      len = strlen(umaxtostr(minor(f->stat.st_rdev), buf));
      if (minor_device_number_width < len)
        minor_device_number_width = len;
      len = major_device_number_width + 2 + minor_device_number_width;
      if (file_size_width < len)
        file_size_width = len;
    } else {
      char buf[LONGEST_HUMAN_READABLE + 1];
      uintmax_t size = unsigned_file_size(f->stat.st_size);
      int len = mbswidth(human_readable(size, buf, file_human_output_opts,
                                        1, file_output_block_size),
                         MBSWIDTH_FLAGS);
      if (file_size_width < len)
        file_size_width = len;
    }
  }

  if (print_inode) {
    char buf[INT_BUFSIZE_BOUND(uintmax_t)];
    int len = strlen(umaxtostr(f->stat.st_ino, buf));
    if (inode_number_width < len)
      inode_number_width = len;
  }

  f->name = xstrdup(name);
  cwd_n_used++;

  return blocks;
}

/* Return true if F refers to a directory.  */
static bool is_directory(const struct fileinfo *f) {
    if (f == NULL) {
        return false;
    }
    return f->filetype == directory || f->filetype == arg_directory;
}

/* Return true if F refers to a (symlinked) directory.  */
static bool is_linked_directory(const struct fileinfo *f) {
    if (f == NULL) {
        return false;
    }
    return (f->filetype == directory) ||
           (f->filetype == arg_directory) ||
           S_ISDIR(f->linkmode);
}

/* Put the name of the file that FILENAME is a symbolic link to
   into the LINKNAME field of 'f'.  COMMAND_LINE_ARG indicates whether
   FILENAME is a command-line argument.  */

static void get_link_name(const char *filename, struct fileinfo *f, bool command_line_arg)
{
    if (!filename || !f)
    {
        file_failure(command_line_arg, _("invalid input to get_link_name"), filename ? filename : "(null)");
        f ? (f->linkname = NULL) : (void)0;
        return;
    }

    f->linkname = areadlink_with_size(filename, f->stat.st_size);
    if (f->linkname == NULL)
        file_failure(command_line_arg, _("cannot read symbolic link %s"), filename);
}

/* Return true if the last component of NAME is '.' or '..'
   This is so we don't try to recurse on '././././. ...' */

static bool basename_is_dot_or_dotdot(const char *name) {
    if (!name) {
        return false;
    }
    const char *base = last_component(name);
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

static void extract_dirs_from_files(const char *dirname, bool command_line_arg) {
    idx_t i, j;
    bool ignore_dot_and_dot_dot = (dirname != NULL);

    if (dirname && LOOP_DETECT) {
        if (!queue_directory(NULL, dirname, false)) {
            return;
        }
    }

    for (i = cwd_n_used; i > 0;) {
        i--;
        struct fileinfo *f = sorted_file[i];

        if (is_directory(f)
            && (!ignore_dot_and_dot_dot
                || !basename_is_dot_or_dotdot(f->name))) {
            if (!dirname || f->name[0] == '/') {
                if (!queue_directory(f->name, f->linkname, command_line_arg)) {
                    continue;
                }
            } else {
                char *name = file_name_concat(dirname, f->name, NULL);
                if (name) {
                    if (!queue_directory(name, f->linkname, command_line_arg)) {
                        free(name);
                        continue;
                    }
                    free(name);
                }
            }

            if (f->filetype == arg_directory) {
                free_ent(f);
            }
        }
    }

    for (i = 0, j = 0; i < cwd_n_used; i++) {
        struct fileinfo *f = sorted_file[i];
        if (f->filetype != arg_directory) {
            sorted_file[j++] = f;
        }
    }
    cwd_n_used = j;
}

/* Use strcoll to compare strings in this locale.  If an error occurs,
   report an error and longjmp to failed_strcoll.  */

static jmp_buf failed_strcoll;

static int xstrcoll(const char *a, const char *b)
{
    errno = 0;
    int diff = strcoll(a, b);
    if (errno != 0)
    {
        error(0, errno, _("cannot compare file names %s and %s"),
              quote_n(0, a), quote_n(1, b));
        set_exit_status(false);
        longjmp(failed_strcoll, 1);
    }
    return diff;
}

/* Comparison routines for sorting the files.  */

typedef void const *V;
typedef int (*qsortFunc)(V a, V b);

/* Used below in DEFINE_SORT_FUNCTIONS for _df_ sort function variants.  */
static int dirfirst_check(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const void *, const void *))
{
    int diff;
    if (!a || !b || !cmp) {
        return 0;
    }
    diff = is_linked_directory(b) - is_linked_directory(a);
    if (diff != 0) {
        return diff;
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

static int cmp_ctime(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    int diff;
    if (!a || !b || !cmp) {
        return 0;
    }
    diff = timespec_cmp(get_stat_ctime(&b->stat), get_stat_ctime(&a->stat));
    if (diff != 0) {
        return diff;
    }
    return cmp(a->name, b->name);
}

static int cmp_mtime(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    int diff;
    if (!a || !b || !cmp) {
        return 0;
    }
    diff = timespec_cmp(get_stat_mtime(&b->stat), get_stat_mtime(&a->stat));
    if (diff != 0) {
        return diff;
    }
    return cmp(a->name, b->name);
}

static int cmp_atime(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    int diff;
    if (!a || !b || !cmp) {
        return 0;
    }
    diff = timespec_cmp(get_stat_atime(&b->stat), get_stat_atime(&a->stat));
    if (diff != 0) {
        return diff;
    }
    return cmp(a->name, b->name);
}

static int cmp_btime(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    int diff = timespec_cmp(get_stat_btime(&b->stat), get_stat_btime(&a->stat));
    if (diff != 0)
        return diff;
    if (!a->name || !b->name || !cmp)
        return 0;
    return cmp(a->name, b->name);
}

static int off_cmp(off_t a, off_t b) {
    if (a < b) return -1;
    if (a > b) return 1;
    return 0;
}

static int cmp_size(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    int diff;
    if (b == NULL || a == NULL || cmp == NULL)
        return 0;
    diff = off_cmp(b->stat.st_size, a->stat.st_size);
    if (diff != 0)
        return diff;
    return cmp(a->name, b->name);
}

static int cmp_name(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    if (!a || !b || !cmp)
        return 0;
    return cmp(a->name, b->name);
}

/* Compare file extensions.  Files with no extension are 'smallest'.
   If extensions are the same, compare by file names instead.  */

static int cmp_extension(const struct fileinfo *a, const struct fileinfo *b, int (*cmp)(const char *, const char *)) {
    const char *base1 = strrchr(a && a->name ? a->name : "", '.');
    const char *base2 = strrchr(b && b->name ? b->name : "", '.');
    const char *ext1 = base1 ? base1 : "";
    const char *ext2 = base2 ? base2 : "";
    int diff;

    if (!cmp)
        return 0;

    diff = cmp(ext1, ext2);
    if (diff != 0)
        return diff;
    return cmp(a ? a->name : "", b ? b->name : "");
}

/* Return the (cached) screen width,
   for the NAME associated with the passed fileinfo F.  */

static size_t fileinfo_name_width(const struct fileinfo *f) {
    if (!f)
        return 0;
    if (f->width > 0)
        return f->width;
    return quote_name_width(f->name, filename_quoting_options, f->quoted);
}

static int cmp_width(const struct fileinfo *a, const struct fileinfo *b,
                     int (*cmp)(const char *, const char *)) {
    int width_a = fileinfo_name_width(a);
    int width_b = fileinfo_name_width(b);

    if (width_a != width_b) {
        return width_a - width_b;
    }

    if (!a->name || !b->name || !cmp) {
        return 0;
    }

    return cmp(a->name, b->name);
}

#include <stdlib.h>

static int cmp_ctime(const void *a, const void *b);

void sort_ctime(void *base, size_t nmemb, size_t size) {
    if (!base || nmemb == 0 || size == 0) {
        return;
    }
    qsort(base, nmemb, size, cmp_ctime);
}#define DEFINE_SORT_FUNCTIONS(type, cmp_func)                  \
void sort_##type(type *arr, size_t n) {                        \
    if (!arr || n == 0) return;                                \
    for (size_t i = 0; i < n - 1; ++i) {                      \
        size_t min_idx = i;                                    \
        for (size_t j = i + 1; j < n; ++j) {                  \
            if (cmp_func(&arr[j], &arr[min_idx]) < 0) {        \
                min_idx = j;                                   \
            }                                                  \
        }                                                      \
        if (min_idx != i) {                                    \
            type temp = arr[i];                                \
            arr[i] = arr[min_idx];                             \
            arr[min_idx] = temp;                               \
        }                                                      \
    }                                                          \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)static int cmp_ctime(const void *a, const void *b) {
    const struct stat *stat_a = (const struct stat *)a;
    const struct stat *stat_b = (const struct stat *)b;
    if (stat_a->st_ctime < stat_b->st_ctime) return -1;
    if (stat_a->st_ctime > stat_b->st_ctime) return 1;
    return 0;
}

void sort_ctime(struct stat *array, size_t n) {
    if (!array || n == 0) return;
    qsort(array, n, sizeof(struct stat), cmp_ctime);
}#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC)                     \
void sort_##NAME(void **array, size_t n) {                        \
    if (!array || n == 0) return;                                 \
    for (size_t i = 1; i < n; ++i) {                              \
        void *key = array[i];                                     \
        size_t j = i;                                             \
        while (j > 0 && CMP_FUNC(array[j - 1], key) > 0) {        \
            array[j] = array[j - 1];                              \
            --j;                                                  \
        }                                                         \
        array[j] = key;                                           \
    }                                                             \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)/**** Refactored code ****/

static int cmp_ctime(const void *a, const void *b) {
    const struct stat *stat_a = (const struct stat *)a;
    const struct stat *stat_b = (const struct stat *)b;

    if (stat_a->st_ctime < stat_b->st_ctime) {
        return -1;
    }
    if (stat_a->st_ctime > stat_b->st_ctime) {
        return 1;
    }
    return 0;
}

void sort_ctime(struct stat *array, size_t n) {
    if (!array || n == 0) {
        return;
    }
    qsort(array, n, sizeof(struct stat), cmp_ctime);
}#define DEFINE_SORT_FUNCTIONS(TYPE, CMP_FUNC) \
void sort_##TYPE(TYPE *array, size_t size) { \
    if (!array || size == 0) { \
        return; \
    } \
    for (size_t i = 0; i < size - 1; ++i) { \
        for (size_t j = 0; j < size - i - 1; ++j) { \
            if (CMP_FUNC(&array[j], &array[j + 1]) > 0) { \
                TYPE tmp = array[j]; \
                array[j] = array[j + 1]; \
                array[j + 1] = tmp; \
            } \
        } \
    } \
} 

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(type, cmp_func)                 \
void sort_##type(type *array, size_t count) {                 \
    if (!array || count == 0) {                               \
        return;                                               \
    }                                                         \
    for (size_t i = 0; i < count - 1; ++i) {                  \
        size_t min_idx = i;                                   \
        for (size_t j = i + 1; j < count; ++j) {              \
            if (cmp_func(&array[j], &array[min_idx]) < 0) {   \
                min_idx = j;                                  \
            }                                                 \
        }                                                     \
        if (min_idx != i) {                                   \
            type temp = array[i];                             \
            array[i] = array[min_idx];                        \
            array[min_idx] = temp;                            \
        }                                                     \
    }                                                         \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC) \
static int NAME##_cmp_wrapper(const void *a, const void *b) { \
    return CMP_FUNC(*(const FileInfo **)a, *(const FileInfo **)b); \
} \
void sort_##NAME(FileInfo **array, size_t size) { \
    if (!array || size == 0) return; \
    qsort(array, size, sizeof(FileInfo *), NAME##_cmp_wrapper); \
}

DEFINE_SORT_FUNCTIONS(ctime, cmp_ctime)
void sort_mtime(void **array, size_t n, int (*cmp_mtime)(const void *, const void *)) {
    if (array == NULL || cmp_mtime == NULL || n == 0) {
        return;
    }
    qsort(array, n, sizeof(void *), cmp_mtime);
}#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC)               \
    static int NAME##_compare(const void *a, const void *b) { \
        return CMP_FUNC(a, b);                               \
    }                                                        \
    void NAME##_sort(void *base, size_t nmemb, size_t size) { \
        if (!base || nmemb == 0 || size == 0) return;         \
        qsort(base, nmemb, size, NAME##_compare);             \
    }

static int cmp_mtime(const void *a, const void *b);

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC)        \
static int NAME##_compare(const void *a, const void *b) { \
    if (!a || !b) return 0; \
    return CMP_FUNC(a, b); \
} \
void sort_##NAME(void *base, size_t nitems, size_t size) { \
    if (!base || nitems == 0 || size == 0) return; \
    qsort(base, nitems, size, NAME##_compare); \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FN)                     \
    static int NAME##_compare(const void *a, const void *b) {    \
        return CMP_FN(*(const void **)a, *(const void **)b);     \
    }                                                           \
    void sort_##NAME(void **array, size_t count) {               \
        if (!array || count == 0) return;                        \
        qsort(array, count, sizeof(void *), NAME##_compare);     \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(prefix, cmp_func)                             \
void prefix##_sort(void **array, size_t n) {                                \
    if (!array || n < 2) return;                                            \
    size_t i, j;                                                            \
    for (i = 0; i < n - 1; ++i) {                                           \
        for (j = 0; j < n - i - 1; ++j) {                                   \
            if (cmp_func(array[j], array[j + 1]) > 0) {                     \
                void *tmp = array[j];                                       \
                array[j] = array[j + 1];                                    \
                array[j + 1] = tmp;                                         \
            }                                                               \
        }                                                                   \
    }                                                                       \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)#define DEFINE_SORT_FUNCTIONS(name, cmp) \
    void sort_##name(void **array, size_t n) { \
        if (!array || n == 0) return; \
        size_t i, j; \
        for (i = 0; i < n - 1; ++i) { \
            for (j = 0; j < n - i - 1; ++j) { \
                if (cmp(array[j], array[j + 1]) > 0) { \
                    void *tmp = array[j]; \
                    array[j] = array[j + 1]; \
                    array[j + 1] = tmp; \
                } \
            } \
        } \
    }

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)void sort_mtime(void **array, size_t n, int (*cmp)(const void *, const void *)) {
    if (!array || !cmp || n == 0) {
        return;
    }

    for (size_t i = 0; i < n - 1; ++i) {
        size_t min_idx = i;
        for (size_t j = i + 1; j < n; ++j) {
            if (cmp(array[j], array[min_idx]) < 0) {
                min_idx = j;
            }
        }
        if (min_idx != i) {
            void *tmp = array[i];
            array[i] = array[min_idx];
            array[min_idx] = tmp;
        }
    }
}#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC) \
int NAME##_compare(const void *a, const void *b) { \
    if (!a || !b) { \
        return (a == b) ? 0 : a ? 1 : -1; \
    } \
    return CMP_FUNC(a, b); \
} \
void NAME##_sort(void *base, size_t nmemb, size_t size) { \
    if (!base || nmemb < 2 || size == 0) { \
        return; \
    } \
    qsort(base, nmemb, size, NAME##_compare); \
}

DEFINE_SORT_FUNCTIONS(mtime, cmp_mtime)
#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC) \
    void sort_##NAME(void *base, size_t nitems, size_t size) { \
        if (!base || nitems < 2 || size == 0) return; \
        qsort(base, nitems, size, CMP_FUNC); \
    }

int cmp_atime(const void *a, const void *b);

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)void sort_by_atime(void **array, size_t n) {
    if (!array || n == 0) {
        return;
    }
    int compare(const void *a, const void *b) {
        const void *pa = *(const void **)a;
        const void *pb = *(const void **)b;
        return cmp_atime(pa, pb);
    }
    qsort(array, n, sizeof(void *), compare);
}static int cmp_atime(const void *a, const void *b);

void sort_atime(void *base, size_t num, size_t size) {
    if (base == NULL || num == 0 || size == 0) {
        return;
    }
    qsort(base, num, size, cmp_atime);
}#define SORT_FUNCTION_NAME(name) sort_##name
#define DECLARE_SORT_FUNCTION(name, cmp) \
    void SORT_FUNCTION_NAME(name)(void **array, size_t n) { \
        if (!array || n == 0) return; \
        qsort(array, n, sizeof(void *), cmp); \
    }
DECLARE_SORT_FUNCTION(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC) \
void sort_##NAME(void **array, size_t n) { \
    if (!array || n < 2) return; \
    for (size_t i = 0; i < n - 1; ++i) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < n; ++j) { \
            if (CMP_FUNC(array[j], array[min_idx]) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            void *tmp = array[i]; \
            array[i] = array[min_idx]; \
            array[min_idx] = tmp; \
        } \
    } \
}

int cmp_atime(const void *a, const void *b);

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(NAME, CMP)                      \
void sort_##NAME(void **array, size_t count) {                \
    if (array == NULL || count < 2) {                         \
        return;                                               \
    }                                                         \
    for (size_t i = 0; i < count - 1; ++i) {                  \
        size_t min_idx = i;                                   \
        for (size_t j = i + 1; j < count; ++j) {              \
            if (CMP(array[j], array[min_idx]) < 0) {          \
                min_idx = j;                                  \
            }                                                 \
        }                                                     \
        if (min_idx != i) {                                   \
            void *tmp = array[i];                             \
            array[i] = array[min_idx];                        \
            array[min_idx] = tmp;                             \
        }                                                     \
    }                                                         \
}

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func)                \
void sort_##name(void **array, size_t n) {                   \
    if (!array || n == 0) return;                            \
    for (size_t i = 0; i < n - 1; ++i) {                     \
        size_t min_idx = i;                                  \
        for (size_t j = i + 1; j < n; ++j) {                 \
            if (cmp_func(array[j], array[min_idx]) < 0) {    \
                min_idx = j;                                 \
            }                                                \
        }                                                    \
        if (min_idx != i) {                                  \
            void *tmp = array[i];                            \
            array[i] = array[min_idx];                       \
            array[min_idx] = tmp;                            \
        }                                                    \
    }                                                        \
}

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)#define DEFINE_SORT_FUNCTIONS(name, cmp_fn)                          \
static int name##_compare(const void *a, const void *b) {             \
    const typeof(*(const void **)a) *pa = *(const void **)a;          \
    const typeof(*(const void **)b) *pb = *(const void **)b;          \
    return cmp_fn(pa, pb);                                            \
}                                                                     \
void sort_##name(void **array, size_t nmemb) {                        \
    if (!array || nmemb == 0) {                                       \
        return;                                                       \
    }                                                                 \
    qsort(array, nmemb, sizeof(void *), name##_compare);              \
}

DEFINE_SORT_FUNCTIONS(atime, cmp_atime)
#define DEFINE_SORT_FUNCTIONS(TYPE, CMP_FUNC)                    \
void sort_##TYPE(TYPE *arr, size_t n) {                          \
    if (!arr || n < 2) return;                                   \
    for (size_t i = 0; i < n - 1; ++i) {                        \
        size_t min_idx = i;                                      \
        for (size_t j = i + 1; j < n; ++j) {                    \
            if (CMP_FUNC(&arr[j], &arr[min_idx]) < 0) {         \
                min_idx = j;                                     \
            }                                                   \
        }                                                       \
        if (min_idx != i) {                                      \
            TYPE temp = arr[i];                                  \
            arr[i] = arr[min_idx];                               \
            arr[min_idx] = temp;                                 \
        }                                                       \
    }                                                           \
}

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)
#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void **array, size_t len) { \
        if (!array || len == 0) { \
            return; \
        } \
        qsort(array, len, sizeof(void *), cmp_func); \
    }

static int cmp_btime(const void *a, const void *b) {
    const SomeType *item1 = *(const SomeType **)a;
    const SomeType *item2 = *(const SomeType **)b;
    if (!item1 || !item2) {
        return 0;
    }
    if (item1->btime < item2->btime) {
        return -1;
    } else if (item1->btime > item2->btime) {
        return 1;
    }
    return 0;
}

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define DEFINE_SORT_FUNCTIONS(name, cmp_func)                     \
void sort_##name(void *base, size_t n, size_t size,               \
                 int (*cmp)(const void *, const void *)) {        \
    if (!base || n == 0 || !cmp)                                  \
        return;                                                   \
    qsort(base, n, size, cmp);                                    \
}                                                                 \
int cmp_##name(const void *a, const void *b) {                    \
    return cmp_func(a, b);                                        \
}

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)#define SORT_FUNCTIONS(NAME, CMP) \
void sort_##NAME(void **arr, size_t n) { \
    if (!arr || n < 2) return; \
    for (size_t i = 1; i < n; ++i) { \
        void *key = arr[i]; \
        size_t j = i; \
        while (j > 0 && CMP(arr[j - 1], key) > 0) { \
            arr[j] = arr[j - 1]; \
            --j; \
        } \
        arr[j] = key; \
    } \
}

SORT_FUNCTIONS(btime, cmp_btime)#ifndef DEFINE_SORT_FUNCTIONS_BTIME
#define DEFINE_SORT_FUNCTIONS_BTIME

#include <stddef.h>
#include <stdlib.h>

static int cmp_btime(const void *a, const void *b);

static void sort_btime(void *base, size_t n, size_t size) {
    if (!base || n == 0 || size == 0) {
        return;
    }
    qsort(base, n, size, cmp_btime);
}

#endif#define DEFINE_SORT_FUNCTIONS(name, cmp_func)                   \
static int cmp_##name(const void *a, const void *b) {           \
    if (!a || !b) return 0;                                     \
    return cmp_func(a, b);                                      \
}                                                               \
void sort_##name(void *array, size_t count, size_t size) {      \
    if (!array || count == 0 || size == 0) return;              \
    qsort(array, count, size, cmp_##name);                      \
}

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)static int cmp_btime(const void *a, const void *b) {
    const typeof(*(btime)) *ba = a;
    const typeof(*(btime)) *bb = b;
    if (*ba < *bb) return -1;
    if (*ba > *bb) return 1;
    return 0;
}

static void sort_btime(btime *array, size_t n) {
    if (array == NULL || n == 0) return;
    qsort(array, n, sizeof(btime), cmp_btime);
}#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC) \
void sort_##NAME(NAME##_t *arr, size_t n) { \
    if (!arr || n == 0) return; \
    for (size_t i = 1; i < n; ++i) { \
        NAME##_t key = arr[i]; \
        size_t j = i; \
        while (j > 0 && CMP_FUNC(&arr[j - 1], &key) > 0) { \
            arr[j] = arr[j - 1]; \
            --j; \
        } \
        arr[j] = key; \
    } \
}

DEFINE_SORT_FUNCTIONS(btime, cmp_btime)
static int cmp_size(const void *a, const void *b) {
    const size_t *size_a = (const size_t *)a;
    const size_t *size_b = (const size_t *)b;
    if (*size_a < *size_b) return -1;
    if (*size_a > *size_b) return 1;
    return 0;
}

void sort_size(size_t *array, size_t n) {
    if (array == NULL || n == 0) return;
    qsort(array, n, sizeof(size_t), cmp_size);
}#define DEFINE_SORT_FUNCTIONS(type, cmp_func)                                             \
void sort_##type(type *array, size_t length) {                                            \
    if (!array || length < 2) return;                                                     \
    for (size_t i = 0; i < length - 1; ++i) {                                             \
        size_t min_idx = i;                                                               \
        for (size_t j = i + 1; j < length; ++j) {                                         \
            if (cmp_func(&array[j], &array[min_idx]) < 0) {                               \
                min_idx = j;                                                              \
            }                                                                             \
        }                                                                                 \
        if (min_idx != i) {                                                               \
            type temp = array[i];                                                         \
            array[i] = array[min_idx];                                                    \
            array[min_idx] = temp;                                                        \
        }                                                                                 \
    }                                                                                     \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(type, cmp_func) \
void sort_##type(type* array, size_t n) { \
    if (!array || n < 2) return; \
    for (size_t i = 0; i < n - 1; ++i) { \
        for (size_t j = 0; j < n - i - 1; ++j) { \
            if (cmp_func(&array[j], &array[j + 1]) > 0) { \
                type tmp = array[j]; \
                array[j] = array[j + 1]; \
                array[j + 1] = tmp; \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)static int cmp_size(const void *a, const void *b) {
    const size_t *sa = (const size_t *)a;
    const size_t *sb = (const size_t *)b;
    if (*sa < *sb) return -1;
    if (*sa > *sb) return 1;
    return 0;
}

void sort_size_array(size_t *array, size_t count) {
    if (array == NULL || count == 0) {
        return;
    }
    qsort(array, count, sizeof(size_t), cmp_size);
}#define DEFINE_SORT_FUNCTIONS(type, cmp_func) \
void sort_##type(type *array, size_t n) { \
    if (!array || n < 2) return; \
    for (size_t i = 0; i < n - 1; ++i) { \
        size_t min_index = i; \
        for (size_t j = i + 1; j < n; ++j) { \
            if (cmp_func(array[j], array[min_index]) < 0) { \
                min_index = j; \
            } \
        } \
        if (min_index != i) { \
            type temp = array[i]; \
            array[i] = array[min_index]; \
            array[min_index] = temp; \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(type, cmp_func)                     \
void sort_##type(type *arr, size_t n) {                          \
    if (arr == NULL || n < 2) return;                            \
    for (size_t i = 0; i < n - 1; ++i) {                         \
        size_t min_idx = i;                                      \
        for (size_t j = i + 1; j < n; ++j) {                     \
            if (cmp_func(&arr[j], &arr[min_idx]) < 0) {          \
                min_idx = j;                                     \
            }                                                    \
        }                                                        \
        if (min_idx != i) {                                      \
            type temp = arr[i];                                  \
            arr[i] = arr[min_idx];                               \
            arr[min_idx] = temp;                                 \
        }                                                        \
    }                                                            \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)#define DEFINE_SORT_FUNCTIONS(type, cmp_fn) \
void sort_##type(type *arr, size_t len) { \
    if (!arr || len < 2) return; \
    for (size_t i = 0; i < len - 1; ++i) { \
        for (size_t j = 0; j < len - i - 1; ++j) { \
            if (cmp_fn(&arr[j], &arr[j + 1]) > 0) { \
                type tmp = arr[j]; \
                arr[j] = arr[j + 1]; \
                arr[j + 1] = tmp; \
            } \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(size, cmp_size)void sort_size(void *base, size_t nitems, size_t size, int (*cmp)(const void *, const void *)) {
    if (!base || !cmp || nitems < 2 || size == 0) {
        return;
    }
    char *arr = (char *)base;
    for (size_t i = 0; i < nitems - 1; ++i) {
        size_t min_idx = i;
        for (size_t j = i + 1; j < nitems; ++j) {
            if (cmp(arr + j * size, arr + min_idx * size) < 0) {
                min_idx = j;
            }
        }
        if (min_idx != i) {
            for (size_t b = 0; b < size; ++b) {
                char tmp = arr[i * size + b];
                arr[i * size + b] = arr[min_idx * size + b];
                arr[min_idx * size + b] = tmp;
            }
        }
    }
}

int cmp_size(const void *a, const void *b) {
    const size_t *sa = (const size_t *)a;
    const size_t *sb = (const size_t *)b;
    if (*sa < *sb) return -1;
    if (*sa > *sb) return 1;
    return 0;
}
#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
    static int name##_compare(const void *a, const void *b) { \
        if (a == NULL || b == NULL) return 0; \
        return cmp_name(a, b); \
    } \
    void name##_sort(void *base, size_t nitems, size_t size) { \
        if (base == NULL || nitems == 0 || size == 0) return; \
        qsort(base, nitems, size, name##_compare); \
    }#define DEFINE_SORT_FUNCTIONS(name, cmp_name)                           \
    static int name##_cmp_wrapper(const void *a, const void *b) {        \
        if (!a || !b) return 0;                                         \
        return cmp_name(a, b);                                          \
    }                                                                   \
    void name##_sort(void *base, size_t nmemb, size_t size) {           \
        if (!base || nmemb <= 1 || size == 0) return;                   \
        qsort(base, nmemb, size, name##_cmp_wrapper);                   \
    }#define SORT_FUNCTION(type, name, cmp)        \
void sort_##name(type *arr, size_t n) {       \
    if (!arr || n < 2) return;                \
    for (size_t i = 0; i < n - 1; ++i) {      \
        size_t min_idx = i;                   \
        for (size_t j = i + 1; j < n; ++j) {  \
            if (cmp(&arr[j], &arr[min_idx]) < 0) {\
                min_idx = j;                  \
            }                                 \
        }                                     \
        if (min_idx != i) {                   \
            type temp = arr[i];               \
            arr[i] = arr[min_idx];            \
            arr[min_idx] = temp;              \
        }                                     \
    }                                         \
}

#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
    SORT_FUNCTION(name##_type, name, cmp_name)#define DEFINE_SORT_FUNCTIONS(name, cmp_name)                        \
static int name##_compare(const void *a, const void *b) {            \
    return cmp_name(a, b);                                           \
}                                                                    \
void name##_sort(void *base, size_t n, size_t size) {                \
    if (!base || n < 2 || size == 0) return;                         \
    qsort(base, n, size, name##_compare);                            \
}#define SORT_FUNCTION_PREFIX(name) name##_sort
#define SORT_FUNCTION_TYPE(name) name##_t

void SORT_FUNCTION_PREFIX(name)(SORT_FUNCTION_TYPE(name) *array, size_t n) {
    if (!array || n < 2) {
        return;
    }
    for (size_t i = 0; i < n - 1; ++i) {
        size_t min_idx = i;
        for (size_t j = i + 1; j < n; ++j) {
            if (cmp_name(&array[j], &array[min_idx]) < 0) {
                min_idx = j;
            }
        }
        if (min_idx != i) {
            SORT_FUNCTION_TYPE(name) temp = array[i];
            array[i] = array[min_idx];
            array[min_idx] = temp;
        }
    }
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name)                        \
static int name##_compare(const void *a, const void *b) {            \
    return cmp_name(*(const void **)a, *(const void **)b);           \
}                                                                    \
void name##_sort(void **array, size_t count) {                       \
    if (!array || count == 0) return;                                \
    qsort(array, count, sizeof(void *), name##_compare);             \
}#define DEFINE_SORT_FUNCTIONS(name, cmp_name) \
    void sort_##name(void *base, size_t nmemb, size_t size) { \
        if (!base || nmemb <= 1 || size == 0) { \
            return; \
        } \
        qsort(base, nmemb, size, cmp_name); \
    }#define SORT_FUNCTION_NAME(name, suffix) name ## _ ## suffix

static void SORT_FUNCTION_NAME(name, swap)(void *a, void *b, size_t size) {
    unsigned char *pa = a;
    unsigned char *pb = b;
    for (size_t i = 0; i < size; ++i) {
        unsigned char tmp = pa[i];
        pa[i] = pb[i];
        pb[i] = tmp;
    }
}

void SORT_FUNCTION_NAME(name, sort)(void *base, size_t nmemb, size_t size, int (*cmp_name)(const void *, const void *)) {
    if (base == NULL || nmemb <= 1 || size == 0 || cmp_name == NULL) {
        return;
    }
    for (size_t i = 0; i < nmemb - 1; ++i) {
        for (size_t j = 0; j < nmemb - i - 1; ++j) {
            unsigned char *p1 = (unsigned char *)base + j * size;
            unsigned char *p2 = (unsigned char *)base + (j + 1) * size;
            if (cmp_name(p1, p2) > 0) {
                SORT_FUNCTION_NAME(name, swap)(p1, p2, size);
            }
        }
    }
}
static int cmp_extension(const void *a, const void *b) {
    const extension *extA = (const extension *)a;
    const extension *extB = (const extension *)b;

    if (extA == NULL || extB == NULL)
        return 0;

    // Example: compare by name; adjust field as needed
    if (extA->name == NULL && extB->name == NULL) return 0;
    if (extA->name == NULL) return -1;
    if (extB->name == NULL) return 1;
    return strcmp(extA->name, extB->name);
}

void sort_extensions(extension *array, size_t n) {
    if (array == NULL || n == 0)
        return;
    qsort(array, n, sizeof(extension), cmp_extension);
}#define DEFINE_SORT_FUNCTIONS(name, cmp) \
    void sort_##name(void *base, size_t num, size_t size) { \
        if (!base || num == 0 || size == 0) { \
            return; \
        } \
        qsort(base, num, size, cmp); \
    }

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)static int cmp_extension(const void *a, const void *b) {
    const char *ext1 = *((const char **)a);
    const char *ext2 = *((const char **)b);

    if (!ext1 && !ext2) return 0;
    if (!ext1) return -1;
    if (!ext2) return 1;

    return strcmp(ext1, ext2);
}

void sort_extension(char **array, size_t n) {
    if (!array || n == 0) {
        return;
    }
    qsort(array, n, sizeof(char *), cmp_extension);
}static int cmp_extension(const void *a, const void *b) {
    const extension *extA = (const extension *)a;
    const extension *extB = (const extension *)b;

    if (!extA || !extB) {
        return 0;
    }

    if (extA->value < extB->value) {
        return -1;
    } else if (extA->value > extB->value) {
        return 1;
    }
    return 0;
}

void sort_extensions(extension *arr, size_t n) {
    if (!arr || n == 0) {
        return;
    }
    qsort(arr, n, sizeof(extension), cmp_extension);
}#define DEFINE_SORT_FUNCTIONS(name, cmp_fn)                                    \
void sort_##name(void *base, size_t nmemb, size_t size) {                      \
    if (!base || nmemb < 2 || size == 0) {                                     \
        return;                                                                \
    }                                                                          \
    qsort(base, nmemb, size, cmp_fn);                                          \
}

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)#define DEFINE_SORT_FUNCTIONS(NAME, CMP) \
    void sort_##NAME(TYPE *array, size_t size) { \
        if (!array || size == 0) return; \
        qsort(array, size, sizeof(TYPE), CMP); \
    }

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)static int cmp_extension(const void *a, const void *b) {
    const extension *ext1 = (const extension *)a;
    const extension *ext2 = (const extension *)b;
    if (ext1 == NULL || ext2 == NULL) {
        return 0;
    }
    return strcmp(ext1->name, ext2->name);
}

void sort_extension_array(extension *array, size_t n) {
    if (array == NULL || n == 0) {
        return;
    }
    qsort(array, n, sizeof(extension), cmp_extension);
}#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
    void sort_##name(void **array, size_t n) { \
        if (!array || n == 0) return; \
        qsort(array, n, sizeof(void *), cmp_func); \
    }

DEFINE_SORT_FUNCTIONS(extension, cmp_extension)
#define DEFINE_SORT_FUNCTIONS(NAME, CMP)                      \
static void sort_##NAME(void **array, size_t left, size_t right, int (*cmp)(const void*, const void*)) { \
    if (left >= right) return;                                 \
    size_t mid = left + (right - left) / 2;                    \
    size_t i = left, j = right;                                \
    void *pivot = array[mid];                                  \
    while (i <= j) {                                           \
        while (cmp(array[i], pivot) < 0) i++;                  \
        while (cmp(array[j], pivot) > 0) j--;                  \
        if (i <= j) {                                          \
            void *tmp = array[i];                              \
            array[i] = array[j];                               \
            array[j] = tmp;                                    \
            i++; j--;                                          \
        }                                                      \
    }                                                          \
    if (left < j) sort_##NAME(array, left, j, cmp);            \
    if (i < right) sort_##NAME(array, i, right, cmp);          \
}                                                              \
void NAME##_sort(void **array, size_t n) {                     \
    if (!array || n < 2) return;                               \
    sort_##NAME(array, 0, n - 1, CMP);                        \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(NAME, CMP_FUNC) \
void sort_##NAME(TYPE *array, size_t n) { \
    if (!array || n == 0) return; \
    for (size_t i = 0; i < n - 1; ++i) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < n; ++j) { \
            if (CMP_FUNC(&array[j], &array[min_idx]) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            TYPE temp = array[i]; \
            array[i] = array[min_idx]; \
            array[min_idx] = temp; \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(name, cmp_func) \
void sort_##name(void *base, size_t n, size_t size) { \
    if (!base || n == 0 || size == 0) return; \
    for (size_t i = 0; i < n - 1; ++i) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < n; ++j) { \
            void *a = (char *)base + j * size; \
            void *b = (char *)base + min_idx * size; \
            if (cmp_func(a, b) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            unsigned char tmp[size]; \
            memcpy(tmp, (char *)base + i * size, size); \
            memcpy((char *)base + i * size, (char *)base + min_idx * size, size); \
            memcpy((char *)base + min_idx * size, tmp, size); \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(type, cmp)                                      \
void type##_sort(type *array, size_t n) {                                     \
    if (!array || n < 2) return;                                              \
    for (size_t i = 0; i < n - 1; ++i) {                                      \
        size_t min_idx = i;                                                   \
        for (size_t j = i + 1; j < n; ++j) {                                  \
            if (cmp(&array[j], &array[min_idx]) < 0) {                        \
                min_idx = j;                                                  \
            }                                                                 \
        }                                                                     \
        if (min_idx != i) {                                                   \
            type tmp = array[i];                                              \
            array[i] = array[min_idx];                                        \
            array[min_idx] = tmp;                                             \
        }                                                                     \
    }                                                                         \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(NAME, COMPARE_FUNC) \
void sort_##NAME(void *base, size_t n, size_t size, int (*cmp)(const void *, const void *)) { \
    if (!base || n == 0 || size == 0 || !cmp) return; \
    qsort(base, n, size, cmp); \
} \
static int cmp_##NAME(const void *a, const void *b) { \
    return COMPARE_FUNC(a, b); \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(type, cmp_func)            \
void sort_##type(type *arr, size_t n) {                  \
    if (!arr || n == 0) return;                          \
    for (size_t i = 0; i < n - 1; ++i) {                 \
        size_t min_idx = i;                              \
        for (size_t j = i + 1; j < n; ++j) {             \
            if (cmp_func(&arr[j], &arr[min_idx]) < 0) {  \
                min_idx = j;                             \
            }                                            \
        }                                                \
        if (min_idx != i) {                              \
            type temp = arr[i];                          \
            arr[i] = arr[min_idx];                       \
            arr[min_idx] = temp;                         \
        }                                                \
    }                                                    \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)#define DEFINE_SORT_FUNCTIONS(type, cmp_func) \
void sort_##type(type *arr, size_t n) { \
    if (!arr || n == 0) return; \
    for (size_t i = 0; i < n - 1; ++i) { \
        size_t min_idx = i; \
        for (size_t j = i + 1; j < n; ++j) { \
            if (cmp_func(&arr[j], &arr[min_idx]) < 0) { \
                min_idx = j; \
            } \
        } \
        if (min_idx != i) { \
            type temp = arr[i]; \
            arr[i] = arr[min_idx]; \
            arr[min_idx] = temp; \
        } \
    } \
}

DEFINE_SORT_FUNCTIONS(width, cmp_width)static int cmp_width(const void *a, const void *b) {
    const int *wa = (const int *)a;
    const int *wb = (const int *)b;
    return (*wa > *wb) - (*wa < *wb);
}

void sort_width(int *array, size_t n) {
    if (array == NULL || n == 0) {
        return;
    }
    qsort(array, n, sizeof(int), cmp_width);
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
static int cmp_version(const struct fileinfo *a, const struct fileinfo *b) {
    if (!a || !b || !a->name || !b->name)
        return 0;
    int diff = filevercmp(a->name, b->name);
    if (diff != 0)
        return diff;
    return strcmp(a->name, b->name);
}

static int xstrcoll_version(V a, V b) {
    if (!a || !b) {
        return 0;
    }
    return cmp_version(a, b);
}
static int rev_xstrcoll_version(V a, V b) {
    return cmp_version(b, a);
}
static int xstrcoll_df_version(V a, V b) {
    return dirfirst_check(a, b, xstrcoll_version);
}
static int rev_xstrcoll_df_version(V a, V b)
{
    if (!a || !b) {
        return 0;
    }
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

static void initialize_ordering_vector(void)
{
    if (!sorted_file || !cwd_file) return;
    for (idx_t i = 0; i < cwd_n_used; ++i) {
        sorted_file[i] = &cwd_file[i];
    }
}

/* Cache values based on attributes global to all files.  */

static void update_current_files_info(void)
{
    int need_width = 0;

    if (sort_type == sort_width)
        need_width = 1;
    else if (line_length && (format == many_per_line || format == horizontal))
        need_width = 1;

    if (!need_width)
        return;

    for (idx_t i = 0; i < cwd_n_used; ++i)
    {
        struct fileinfo *f = sorted_file[i];
        if (f)
            f->width = fileinfo_name_width(f);
    }
}

/* Sort the files now in the table.  */

static void sort_files(void)
{
    bool use_strcmp = false;

    if (cwd_n_used == 0)
        return;

    if (sorted_file_alloc < cwd_n_used + (cwd_n_used >> 1))
    {
        free(sorted_file);
        sorted_file = xinmalloc(cwd_n_used, 3 * sizeof *sorted_file);
        if (!sorted_file)
            xalloc_die();
        sorted_file_alloc = 3 * cwd_n_used;
    }

    initialize_ordering_vector();

    update_current_files_info();

    if (sort_type == sort_none)
        return;

    if (setjmp(failed_strcoll) != 0)
    {
        use_strcmp = true;
        if (sort_type == sort_version)
            xalloc_die();
        initialize_ordering_vector();
    }

    int type_index = sort_type + ((sort_type == sort_time) ? time_type : 0);

    mpsort((void const **)sorted_file, cwd_n_used,
           sort_functions[type_index]
                         [use_strcmp][sort_reverse]
                         [directories_first]);
}

/* List all the files now in the table.  */

static void print_current_files(void)
{
    idx_t i;

    switch (format)
    {
        case one_per_line:
            for (i = 0; i < cwd_n_used; i++)
            {
                print_file_name_and_frills(sorted_file[i], 0);
                if (putchar(eolbyte) == EOF)
                    return;
            }
            break;

        case many_per_line:
        case horizontal:
            if (!line_length)
            {
                if (print_with_separator((format == with_commas) ? ',' : ' ') < 0)
                    return;
            }
            else
            {
                if (format == many_per_line)
                    print_many_per_line();
                else
                    print_horizontal();
            }
            break;

        case with_commas:
            if (print_with_separator(',') < 0)
                return;
            break;

        case long_format:
            for (i = 0; i < cwd_n_used; i++)
            {
                set_normal_color();
                print_long_format(sorted_file[i]);
                if (dired_outbyte(eolbyte) < 0)
                    return;
            }
            break;

        default:
            break;
    }
}

/* Replace the first %b with precomputed aligned month names.
   Note on glibc-2.7 at least, this speeds up the whole 'ls -lU'
   process by around 17%, compared to letting strftime() handle the %b.  */

static size_t align_nstrftime(char *buf, size_t size, bool recent, const struct tm *tm, timezone_t tz, int ns) {
    const char *nfmt;
    if (use_abformat) {
        nfmt = abformat[recent][tm->tm_mon];
    } else {
        nfmt = long_time_format[recent];
    }
    return nstrftime(buf, size, nfmt, tm, tz, ns);
}

/* Return the expected number of columns in a long-format timestamp,
   or zero if it cannot be calculated.  */

static int long_time_expected_width(void)
{
    static int width = -1;

    if (width >= 0)
        return width;

    time_t epoch = 0;
    struct tm tm;
    char buf[TIME_STAMP_LEN_MAXIMUM + 1];

    if (localtime_rz(localtz, &epoch, &tm)) {
        size_t len = align_nstrftime(buf, sizeof(buf), false, &tm, localtz, 0);
        if (len > 0) {
            int w = mbsnwidth(buf, len, MBSWIDTH_FLAGS);
            width = (w >= 0) ? w : 0;
        } else {
            width = 0;
        }
    } else {
        width = 0;
    }

    return width;
}

/* Print the user or group name NAME, with numeric id ID, using a
   print width of WIDTH columns.  */

static void format_user_or_group(const char *name, uintmax_t id, int width)
{
    if (name)
    {
        int name_width = mbswidth(name, MBSWIDTH_FLAGS);
        int pad = 0;
        if (name_width >= 0 && width > name_width)
            pad = width - name_width;

        dired_outstring(name);
        for (int i = 0; i < pad; i++)
            dired_outbyte(' ');
    }
    else
    {
        int printed = printf("%*ju ", width, id);
        if (printed > 0)
            dired_pos += printed;
    }
}

/* Print the name or id of the user with id U, using a print width of
   WIDTH.  */

static void format_user(uid_t u, int width, bool stat_ok)
{
    const char *name = NULL;
    if (stat_ok && !numeric_ids) {
        name = getuser(u);
    }
    format_user_or_group(name ? name : "?", u, width);
}

/* Likewise, for groups.  */

static void format_group(gid_t g, int width, bool stat_ok)
{
    const char *group_name = "?";
    if (stat_ok && !numeric_ids) {
        group_name = getgroup(g);
        if (!group_name)
            group_name = "?";
    }
    format_user_or_group(group_name, g, width);
}

/* Return the number of columns that format_user_or_group will print,
   or -1 if unknown.  */

static int format_user_or_group_width(const char *name, uintmax_t id) {
    int width = 0;
    if (name) {
        width = mbswidth(name, MBSWIDTH_FLAGS);
        if (width < 0) {
            width = 0;
        }
    } else {
        char buf[32];
        int ret = snprintf(buf, sizeof(buf), "%ju", id);
        width = (ret >= 0) ? ret : 0;
    }
    return width;
}

/* Return the number of columns that format_user will print,
   or -1 if unknown.  */

static int format_user_width(uid_t u) {
    const char *user_name = NULL;
    if (!numeric_ids) {
        user_name = getuser(u);
    }
    return format_user_or_group_width(user_name, u);
}

/* Likewise, for groups.  */

static int format_group_width(gid_t g) {
    const char *group_name = NULL;
    if (!numeric_ids) {
        group_name = getgroup(g);
    }
    return format_user_or_group_width(group_name, g);
}

/* Return a pointer to a formatted version of F->stat.st_ino,
   possibly using buffer, which must be at least
   INT_BUFSIZE_BOUND (uintmax_t) bytes.  */
static char *format_inode(char buf[INT_BUFSIZE_BOUND(uintmax_t)], const struct fileinfo *f) {
    if (!f || !f->stat_ok || f->stat.st_ino == NOT_AN_INODE_NUMBER) {
        return (char *)"?";
    }
    return umaxtostr(f->stat.st_ino, buf);
}

/* Print information about F in long format.  */
static void print_long_format(const struct fileinfo *f)
{
    char modebuf[12];
    char buf[
        LONGEST_HUMAN_READABLE + 1 +
        LONGEST_HUMAN_READABLE + 1 +
        sizeof(modebuf) +
        INT_BUFSIZE_BOUND(uintmax_t) +
        LONGEST_HUMAN_READABLE + 2 +
        LONGEST_HUMAN_READABLE + 1 +
        TIME_STAMP_LEN_MAXIMUM + 1
    ];
    char *p = buf;
    size_t s = 0;
    struct timespec when_timespec;
    struct tm when_local;
    bool btime_ok = true;

    if (f->stat_ok) {
        filemodestring(&f->stat, modebuf);
    } else {
        modebuf[0] = filetype_letter[f->filetype];
        memset(modebuf + 1, '?', 10);
        modebuf[11] = '\0';
    }
    if (!any_has_acl) {
        modebuf[10] = '\0';
    } else if (f->acl_type == ACL_T_LSM_CONTEXT_ONLY) {
        modebuf[10] = '.';
    } else if (f->acl_type == ACL_T_YES) {
        modebuf[10] = '+';
    } else if (f->acl_type == ACL_T_UNKNOWN) {
        modebuf[10] = '?';
    }

    switch (time_type) {
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
                btime_ok = false;
            break;
        default:
            unreachable();
    }

    if (print_inode) {
        char hbuf[INT_BUFSIZE_BOUND(uintmax_t)];
        p += sprintf(p, "%*s ", inode_number_width, format_inode(hbuf, f));
    }

    if (print_block_size) {
        char hbuf[LONGEST_HUMAN_READABLE + 1];
        const char *blocks = (!f->stat_ok)
            ? "?"
            : human_readable(STP_NBLOCKS(&f->stat), hbuf, human_output_opts,
                               ST_NBLOCKSIZE, output_block_size);
        int blocks_width = mbswidth(blocks, MBSWIDTH_FLAGS);
        int pad = block_size_width - ((blocks_width < 0) ? 0 : blocks_width);
        while (pad-- > 0) *p++ = ' ';
        while ((*p = *blocks++)) ++p;
        *p++ = ' ';
    }

    {
        char hbuf[INT_BUFSIZE_BOUND(uintmax_t)];
        p += sprintf(p, "%s %*s ", modebuf, nlink_width,
                     !f->stat_ok ? "?" : umaxtostr(f->stat.st_nlink, hbuf));
    }

    dired_indent();

    if (print_owner || print_group || print_author || print_scontext) {
        dired_outbuf(buf, p - buf);

        if (print_owner)
            format_user(f->stat.st_uid, owner_width, f->stat_ok);
        if (print_group)
            format_group(f->stat.st_gid, group_width, f->stat_ok);
        if (print_author)
            format_user(f->stat.st_author, author_width, f->stat_ok);
        if (print_scontext)
            format_user_or_group(f->scontext, 0, scontext_width);

        p = buf;
    }

    if (f->stat_ok && (S_ISCHR(f->stat.st_mode) || S_ISBLK(f->stat.st_mode))) {
        char majorbuf[INT_BUFSIZE_BOUND(uintmax_t)];
        char minorbuf[INT_BUFSIZE_BOUND(uintmax_t)];
        int blanks_width = file_size_width -
            (major_device_number_width + 2 + minor_device_number_width);
        p += sprintf(p, "%*s, %*s ",
            major_device_number_width + (blanks_width > 0 ? blanks_width : 0),
            umaxtostr(major(f->stat.st_rdev), majorbuf),
            minor_device_number_width,
            umaxtostr(minor(f->stat.st_rdev), minorbuf));
    } else {
        char hbuf[LONGEST_HUMAN_READABLE + 1];
        const char *size = (!f->stat_ok)
            ? "?"
            : human_readable(unsigned_file_size(f->stat.st_size), hbuf,
                             file_human_output_opts, 1, file_output_block_size);
        int size_width = mbswidth(size, MBSWIDTH_FLAGS);
        int pad = file_size_width - ((size_width < 0) ? 0 : size_width);
        while (pad-- > 0) *p++ = ' ';
        while ((*p = *size++)) ++p;
        *p++ = ' ';
    }

    *p = '\1';

    if (f->stat_ok && btime_ok &&
        localtime_rz(localtz, &when_timespec.tv_sec, &when_local)) {
        struct timespec six_months_ago;
        bool recent;

        if (timespec_cmp(current_time, when_timespec) < 0)
            gettime(&current_time);

        six_months_ago.tv_sec = current_time.tv_sec - 31556952 / 2;
        six_months_ago.tv_nsec = current_time.tv_nsec;
        recent = (timespec_cmp(six_months_ago, when_timespec) < 0
                  && timespec_cmp(when_timespec, current_time) < 0);

        s = align_nstrftime(p, TIME_STAMP_LEN_MAXIMUM + 1, recent,
                            &when_local, localtz, when_timespec.tv_nsec);
    }

    if (s || !*p) {
        p += s;
        *p++ = ' ';
    } else {
        char hbuf[INT_BUFSIZE_BOUND(intmax_t)];
        p += sprintf(p, "%*s ", long_time_expected_width(),
                     (!f->stat_ok || !btime_ok
                      ? "?"
                      : timetostr(when_timespec.tv_sec, hbuf)));
    }

    dired_outbuf(buf, p - buf);
    size_t w = print_name_with_quoting(f, false, &dired_obstack, p - buf);

    if (f->filetype == symbolic_link) {
        if (f->linkname) {
            dired_outstring(" -> ");
            print_name_with_quoting(f, true, nullptr, (p - buf) + w + 4);
            if (indicator_style != none)
                print_type_indicator(true, f->linkmode, unknown);
        }
    } else if (indicator_style != none) {
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
quote_name_buf(char **inbuf, size_t bufsize, char *name,
               struct quoting_options const *options,
               int needs_general_quoting, size_t *width, bool *pad)
{
    char *buf = *inbuf;
    size_t displayed_width = 0;
    size_t len = 0;
    bool quoted = false;

    enum quoting_style qs = get_quoting_style(options);
    bool needs_further_quoting = qmark_funny_chars
        && (qs == shell_quoting_style
            || qs == shell_always_quoting_style
            || qs == literal_quoting_style);

    if (needs_general_quoting) {
        len = quotearg_buffer(buf, bufsize, name, -1, options);
        if (bufsize <= len) {
            char *tmpbuf = (char *)xmalloc(len + 1);
            if (!tmpbuf)
                return 0;
            len = quotearg_buffer(tmpbuf, len + 1, name, -1, options);
            buf = tmpbuf;
        }
        quoted = (*name != *buf) || (strlen(name) != len);
    } else if (needs_further_quoting) {
        len = strlen(name);
        if (bufsize <= len) {
            char *tmpbuf = (char *)xmalloc(len + 1);
            if (!tmpbuf)
                return 0;
            buf = tmpbuf;
        }
        memcpy(buf, name, len + 1);
        quoted = false;
    } else {
        len = strlen(name);
        buf = name;
        quoted = false;
    }

    if (needs_further_quoting) {
        if (MB_CUR_MAX > 1) {
            const char *p = buf;
            const char *plimit = buf + len;
            char *q = buf;
            displayed_width = 0;
            while (p < plimit) {
                unsigned char c = (unsigned char)*p;
                if (isprint(c)) {
                    *q++ = *p++;
                    displayed_width++;
                } else {
                    mbstate_t mbstate;
                    mbszero(&mbstate);
                    do {
                        char32_t wc = 0;
                        size_t bytes = mbrtoc32(&wc, p, plimit - p, &mbstate);

                        if (bytes == (size_t)-1) {
                            p++;
                            *q++ = '?';
                            displayed_width++;
                            break;
                        }

                        if (bytes == (size_t)-2) {
                            p = plimit;
                            *q++ = '?';
                            displayed_width++;
                            break;
                        }

                        if (bytes == 0)
                            bytes = 1;

                        int w = c32width(wc);
                        if (w >= 0) {
                            size_t mb;
                            for (mb = 0; mb < bytes; ++mb)
                                *q++ = *p++;
                            displayed_width += w;
                        } else {
                            p += bytes;
                            *q++ = '?';
                            displayed_width++;
                        }
                    } while (!mbsinit(&mbstate));
                }
            }
            len = (size_t)(q - buf);
        } else {
            char *p = buf;
            char *plimit = buf + len;
            while (p < plimit) {
                if (!isprint((unsigned char)*p))
                    *p = '?';
                p++;
            }
            displayed_width = len;
        }
    } else if (width) {
        if (MB_CUR_MAX > 1) {
            displayed_width = mbsnwidth(buf, len, MBSWIDTH_FLAGS);
            if ((int)displayed_width < 0)
                displayed_width = 0;
        } else {
            const char *p = buf;
            const char *plimit = buf + len;
            displayed_width = 0;
            while (p < plimit) {
                if (isprint((unsigned char)*p))
                    displayed_width++;
                p++;
            }
        }
    }

    *pad = (align_variable_outer_quotes && cwd_some_quoted && !quoted);

    if (width)
        *width = displayed_width;

    *inbuf = buf;

    return len;
}

static size_t quote_name_width(const char *name, const struct quoting_options *options, int needs_general_quoting) {
    char smallbuf[BUFSIZ];
    char *buf = smallbuf;
    size_t width = 0;
    bool pad = false;

    quote_name_buf(&buf, sizeof smallbuf, (char *)name, options, needs_general_quoting, &width, &pad);

    if (buf != smallbuf && buf != name) {
        free(buf);
    }

    return width + (pad ? 1 : 0);
}

/* %XX escape any input out of range as defined in RFC3986,
   and also if PATH, convert all path separators to '/'.  */
char *file_escape(const char *str, bool path) {
    if (!str) {
        return NULL;
    }
    size_t len = strlen(str);
    char *esc = xnmalloc(3, len + 1);
    if (!esc) {
        return NULL;
    }
    char *p = esc;
    for (; *str; str++) {
        if (path && ISSLASH(*str)) {
            *p++ = '/';
            continue;
        }
        if (RFC3986[to_uchar(*str)]) {
            *p++ = *str;
            continue;
        }
        int written = snprintf(p, 4, "%%%02x", to_uchar(*str));
        if (written != 3) {
            free(esc);
            return NULL;
        }
        p += 3;
    }
    *p = '\0';
    return esc;
}

static size_t
quote_name(const char *name, const struct quoting_options *options,
           int needs_general_quoting, const struct bin_str *color,
           bool allow_pad, struct obstack *stack, const char *absolute_name)
{
    char smallbuf[BUFSIZ];
    char *buf = smallbuf;
    size_t len;
    bool pad = false;
    bool skip_quotes = false;

    if (!name)
        return 0;

    len = quote_name_buf(&buf, sizeof smallbuf, (char *)name, options,
                        needs_general_quoting, NULL, &pad);

    if (pad && allow_pad)
        dired_outbyte(' ');

    if (color)
        print_color_indicator(color);

    if (absolute_name) {
        if (align_variable_outer_quotes && cwd_some_quoted && !pad) {
            skip_quotes = true;
            putchar(*buf);
        }
        char *h = file_escape(hostname, false);
        char *n = file_escape(absolute_name, true);
        if (h && n)
            printf("\033]8;;file://%s%s%s\a", h, *n == '/' ? "" : "/", n);
        free(h);
        free(n);
    }

    if (stack)
        push_current_dired_pos(stack);

    size_t write_offset = skip_quotes ? 1 : 0;
    size_t write_len = len > (skip_quotes * 2) ? len - (skip_quotes * 2) : 0;
    if (write_len > 0)
        fwrite(buf + write_offset, 1, write_len, stdout);

    dired_pos += len;

    if (stack)
        push_current_dired_pos(stack);

    if (absolute_name) {
        fputs("\033]8;;\a", stdout);
        if (skip_quotes && len > 0)
            putchar(*(buf + len - 1));
    }

    if (buf != smallbuf && buf != name)
        free(buf);

    return len + (pad ? 1 : 0);
}

static size_t print_name_with_quoting(const struct fileinfo *f,
                                      bool symlink_target,
                                      struct obstack *stack,
                                      size_t start_col)
{
    char const *name = symlink_target ? f->linkname : f->name;
    const struct bin_str *color = NULL;
    bool used_color_this_time = false;
    size_t len;

    if (print_with_color)
    {
        color = get_color_indicator(f, symlink_target);
        used_color_this_time = (color != NULL) || is_colored(C_NORM);
    }

    len = quote_name(name, filename_quoting_options, f->quoted,
                     color, !symlink_target, stack, f->absolute_name);

    process_signals();

    if (used_color_this_time)
    {
        prep_non_filename_text();

        if (line_length)
        {
            size_t start = start_col;
            size_t end = start_col + len - 1;
            if ((start / line_length) != (end / line_length))
            {
                put_indicator(&color_indicator[C_CLR_TO_EOL]);
            }
        }
    }

    return len;
}

static void prep_non_filename_text(void) {
    if (color_indicator[C_END].string) {
        put_indicator(&color_indicator[C_END]);
        return;
    }
    put_indicator(&color_indicator[C_LEFT]);
    put_indicator(&color_indicator[C_RESET]);
    put_indicator(&color_indicator[C_RIGHT]);
}

/* Print the file name of 'f' with appropriate quoting.
   Also print file size, inode number, and filetype indicator character,
   as requested by switches.  */

static size_t print_file_name_and_frills(const struct fileinfo *f, size_t start_col)
{
    char buf[MAX(LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND(uintmax_t))];
    set_normal_color();

    if (print_inode) {
        const char *inode_str = format_inode(buf, f);
        int width = (format == with_commas) ? 0 : inode_number_width;
        if (inode_str)
            printf("%*s ", width, inode_str);
        else
            printf("%*s ", width, "?");
    }

    if (print_block_size) {
        const char *blocks;
        if (!f->stat_ok) {
            blocks = "?";
        } else {
            blocks = human_readable(STP_NBLOCKS(&f->stat), buf, human_output_opts, ST_NBLOCKSIZE, output_block_size);
            if (!blocks)
                blocks = "?";
        }
        int blocks_width = mbswidth(blocks, MBSWIDTH_FLAGS);
        int pad = 0;
        if (blocks_width >= 0 && block_size_width && format != with_commas)
            pad = block_size_width - blocks_width;
        printf("%*s%s ", pad, "", blocks);
    }

    if (print_scontext) {
        int width = (format == with_commas) ? 0 : scontext_width;
        const char *scontext = f->scontext ? f->scontext : "";
        printf("%*s ", width, scontext);
    }

    size_t width = print_name_with_quoting(f, false, NULL, start_col);

    if (indicator_style != none)
        width += print_type_indicator(f->stat_ok, f->stat.st_mode, f->filetype);

    return width;
}

/* Given these arguments describing a file, return the single-byte
   type indicator, or 0.  */
static char get_type_indicator(bool stat_ok, mode_t mode, enum filetype type)
{
    if (stat_ok ? S_ISREG(mode) : type == normal)
    {
        if (stat_ok && indicator_style == classify && (mode & S_IXUGO))
            return '*';
        return 0;
    }

    if (stat_ok ? S_ISDIR(mode) : type == directory || type == arg_directory)
        return '/';

    if (indicator_style == slash)
        return 0;

    if (stat_ok ? S_ISLNK(mode) : type == symbolic_link)
        return '@';

    if (stat_ok ? S_ISFIFO(mode) : type == fifo)
        return '|';

    if (stat_ok ? S_ISSOCK(mode) : type == sock)
        return '=';

    if (stat_ok && S_ISDOOR(mode))
        return '>';

    return 0;
}

static bool print_type_indicator(bool stat_ok, mode_t mode, enum filetype type)
{
    char c;
    if (!stat_ok)
        return false;

    c = get_type_indicator(true, mode, type);
    if (c) {
        dired_outbyte(c);
        return true;
    }

    return false;
}

/* Returns if color sequence was printed.  */
static bool print_color_indicator(const struct bin_str *ind) {
  if (!ind)
    return false;

  if (is_colored(C_NORM))
    restore_default_color();

  put_indicator(&color_indicator[C_LEFT]);
  put_indicator(ind);
  put_indicator(&color_indicator[C_RIGHT]);
  return true;
}

/* Returns color indicator or nullptr if none.  */
ATTRIBUTE_PURE
static const struct bin_str*
get_color_indicator(const struct fileinfo *f, bool symlink_target)
{
    enum indicator_no type = C_FILE;
    struct color_ext_type *ext = NULL;
    size_t len;
    const char *name;
    mode_t mode;
    int linkok;

    if (symlink_target) {
        name = f->linkname;
        mode = f->linkmode;
        linkok = f->linkok ? 0 : -1;
    } else {
        name = f->name;
        mode = file_or_link_mode(f);
        linkok = f->linkok;
    }

    if (linkok == -1 && is_colored(C_MISSING)) {
        type = C_MISSING;
    } else if (!f->stat_ok) {
        static const enum indicator_no filetype_indicator[] = {
            C_ORPHAN, C_FIFO, C_CHR, C_DIR, C_BLK, C_FILE,
            C_LINK, C_SOCK, C_FILE, C_DIR
        };
        type = filetype_indicator[f->filetype];
    } else {
        if (S_ISREG(mode)) {
            if ((mode & S_ISUID) != 0 && is_colored(C_SETUID)) {
                type = C_SETUID;
            } else if ((mode & S_ISGID) != 0 && is_colored(C_SETGID)) {
                type = C_SETGID;
            } else if (f->has_capability) {
                type = C_CAP;
            } else if ((mode & S_IXUGO) != 0 && is_colored(C_EXEC)) {
                type = C_EXEC;
            } else if ((1 < f->stat.st_nlink) && is_colored(C_MULTIHARDLINK)) {
                type = C_MULTIHARDLINK;
            } else {
                type = C_FILE;
            }
        } else if (S_ISDIR(mode)) {
            if ((mode & S_ISVTX) && (mode & S_IWOTH) && is_colored(C_STICKY_OTHER_WRITABLE)) {
                type = C_STICKY_OTHER_WRITABLE;
            } else if ((mode & S_IWOTH) != 0 && is_colored(C_OTHER_WRITABLE)) {
                type = C_OTHER_WRITABLE;
            } else if ((mode & S_ISVTX) != 0 && is_colored(C_STICKY)) {
                type = C_STICKY;
            } else {
                type = C_DIR;
            }
        } else if (S_ISLNK(mode)) {
            type = C_LINK;
        } else if (S_ISFIFO(mode)) {
            type = C_FIFO;
        } else if (S_ISSOCK(mode)) {
            type = C_SOCK;
        } else if (S_ISBLK(mode)) {
            type = C_BLK;
        } else if (S_ISCHR(mode)) {
            type = C_CHR;
        } else if (S_ISDOOR(mode)) {
            type = C_DOOR;
        } else {
            type = C_ORPHAN;
        }
    }

    if (type == C_FILE && name) {
        len = strlen(name);
        const char *name_end = name + len;
        for (ext = color_ext_list; ext != NULL; ext = ext->next) {
            if (ext->ext.len <= len) {
                const char *cmp_start = name_end - ext->ext.len;
                if (ext->exact_match) {
                    if (STREQ_LEN(cmp_start, ext->ext.string, ext->ext.len)) {
                        break;
                    }
                } else {
                    if (c_strncasecmp(cmp_start, ext->ext.string, ext->ext.len) == 0) {
                        break;
                    }
                }
            }
        }
    } else {
        ext = NULL;
    }

    if (type == C_LINK && !linkok) {
        if (color_symlink_as_referent || is_colored(C_ORPHAN)) {
            type = C_ORPHAN;
        }
    }

    const struct bin_str *s = ext ? &(ext->seq) : &color_indicator[type];
    return (s && s->string) ? s : NULL;
}

/* Output a color indicator (which may contain nulls).  */
static void put_indicator(const struct bin_str *ind)
{
    if (!ind || !ind->string || ind->len == 0)
        return;

    if (!used_color)
    {
        used_color = true;

        if (isatty(STDOUT_FILENO))
        {
            signal_init();
        }

        prep_non_filename_text();
    }

    if (fwrite(ind->string, ind->len, 1, stdout) != 1)
    {
        // Handle write error if necessary
    }
}

static size_t length_of_file_name_and_frills(const struct fileinfo *f) {
    size_t len = 0;
    char buf[MAX(LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND(uintmax_t))];

    if (!f) {
        return 0;
    }

    if (print_inode) {
        if (format == with_commas) {
            if (umaxtostr && f->stat_ok) {
                len += 1 + strlen(umaxtostr(f->stat.st_ino, buf));
            } else {
                len += 2; // Fallback for missing function or stat error
            }
        } else {
            len += 1 + inode_number_width;
        }
    }

    if (print_block_size) {
        if (format == with_commas) {
            if (!f->stat_ok) {
                len += 1 + 1;
            } else if (human_readable) {
                len += 1 + strlen(human_readable(STP_NBLOCKS(&f->stat), buf, human_output_opts, ST_NBLOCKSIZE, output_block_size));
            } else {
                len += 2; // Fallback for missing function
            }
        } else {
            len += 1 + block_size_width;
        }
    }

    if (print_scontext) {
        if (format == with_commas) {
            len += 1 + (f->scontext ? strlen(f->scontext) : 0);
        } else {
            len += 1 + scontext_width;
        }
    }

    len += fileinfo_name_width ? fileinfo_name_width(f) : 0;

    if (indicator_style != none) {
        char c = 0;
        if (get_type_indicator) {
            c = get_type_indicator(f->stat_ok, f->stat.st_mode, f->filetype);
        }
        len += (c != 0) ? 1 : 0;
    }

    return len;
}

static void print_many_per_line(void)
{
    idx_t cols = calculate_columns(true);
    if (cols == 0 || cols > cwd_n_used)
        return;

    const struct column_info *line_fmt = &column_info[cols - 1];
    idx_t rows = cwd_n_used / cols + (cwd_n_used % cols != 0);

    for (idx_t row = 0; row < rows; row++)
    {
        size_t pos = 0;
        idx_t filesno = row;

        for (size_t col = 0; col < (size_t)cols; col++)
        {
            if ((size_t)filesno >= cwd_n_used)
                break;

            const struct fileinfo *f = sorted_file[filesno];
            size_t name_length = length_of_file_name_and_frills(f);
            size_t max_name_length = line_fmt->col_arr[col];
            print_file_name_and_frills(f, pos);

            filesno += rows;
            if ((size_t)filesno >= cwd_n_used)
                break;

            indent(pos + name_length, pos + max_name_length);
            pos += max_name_length;
        }
        putchar(eolbyte);
    }
}

static void print_horizontal(void)
{
    idx_t cols = calculate_columns(false);
    if (cols == 0 || cwd_n_used == 0)
        return;

    struct column_info const *line_fmt = &column_info[cols - 1];
    size_t *max_name_lengths = line_fmt->col_arr;
    size_t pos = 0;

    for (idx_t filesno = 0; filesno < cwd_n_used; filesno++) {
        idx_t col = filesno % cols;
        struct fileinfo const *f = sorted_file[filesno];
        size_t name_length = length_of_file_name_and_frills(f);

        if (col == 0 && filesno != 0) {
            if (putchar(eolbyte) == EOF)
                return;
            pos = 0;
        } else if (col != 0) {
            indent(pos + name_length, pos + max_name_lengths[col]);
            pos += max_name_lengths[col];
        }

        print_file_name_and_frills(f, pos);
    }

    putchar(eolbyte);
}

/* Output name + SEP + ' '.  */

static void print_with_separator(char sep) {
    size_t pos = 0;

    for (idx_t filesno = 0; filesno < cwd_n_used; ++filesno) {
        struct fileinfo const *f = sorted_file[filesno];
        size_t len = line_length ? length_of_file_name_and_frills(f) : 0;

        if (filesno != 0) {
            bool can_append = line_length && pos <= SIZE_MAX - len - 2 && (pos + len + 2 < line_length);
            char separator = (can_append) ? ' ' : eolbyte;
            if (can_append) {
                pos += 2;
            } else {
                pos = 0;
            }

            if (putchar(sep) == EOF || putchar(separator) == EOF) {
                // Handle write error if required
                return;
            }
        }

        print_file_name_and_frills(f, pos);
        pos += len;
    }
    putchar(eolbyte);
}


/* Assuming cursor is at position FROM, indent up to position TO.
   Use a TAB character instead of two or more spaces whenever possible.  */

static void indent(size_t from, size_t to) {
    if (from >= to) return;

    while (from < to) {
        if (tabsize > 0) {
            size_t next_tab_stop = from + (tabsize - from % tabsize);
            if (next_tab_stop <= to) {
                putchar('\t');
                from = next_tab_stop;
                continue;
            }
        }
        putchar(' ');
        from++;
    }
}

/* Put DIRNAME/NAME into DEST, handling '.' and '/' properly.  */
/* FIXME: maybe remove this function someday.  See about using a
   non-malloc'ing version of file_name_concat.  */

static void attach(char *dest, const char *dirname, const char *name)
{
    if (!(dirname[0] == '.' && dirname[1] == '\0')) {
        size_t len = 0;
        while (dirname[len]) {
            dest[len] = dirname[len];
            len++;
        }
        if (len == 0 || dirname[len - 1] != '/')
            dest[len++] = '/';
        dest += len;
    }
    while (*name) {
        *dest++ = *name++;
    }
    *dest = '\0';
}

/* Allocate enough column info suitable for the current number of
   files and display columns, and initialize the info to represent the
   narrowest possible columns.  */

static void init_column_info(idx_t max_cols)
{
    static idx_t column_info_alloc = 0;

    if (column_info_alloc < max_cols)
    {
        idx_t old_column_info_alloc = column_info_alloc;
        idx_t growth = max_cols - column_info_alloc;

        column_info = xpalloc(column_info, &column_info_alloc, growth, -1, sizeof *column_info);

        idx_t triangle_n = old_column_info_alloc;
        idx_t triangle_m = column_info_alloc;
        idx_t s;
        if (ckd_add(&s, triangle_n + 1, triangle_m) || ckd_mul(&s, s, triangle_m - triangle_n))
            xalloc_die();

        size_t *p = xinmalloc(s >> 1, sizeof *p);

        for (idx_t i = old_column_info_alloc; i < column_info_alloc; ++i)
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

static idx_t calculate_columns(bool by_columns)
{
    idx_t max_cols = (max_idx > 0 && max_idx < cwd_n_used) ? max_idx : cwd_n_used;
    if (max_cols == 0)
        return 0;

    init_column_info(max_cols);

    for (idx_t filesno = 0; filesno < cwd_n_used; ++filesno) {
        struct fileinfo const *f = sorted_file[filesno];
        size_t name_length = length_of_file_name_and_frills(f);

        for (idx_t i = 0; i < max_cols; ++i) {
            if (!column_info[i].valid_len)
                continue;

            idx_t idx = by_columns
                        ? filesno / ((cwd_n_used + i) / (i + 1))
                        : filesno % (i + 1);
            size_t real_length = name_length + ((idx == i) ? 0 : 2);

            if (column_info[i].col_arr[idx] < real_length) {
                column_info[i].line_len += (real_length - column_info[i].col_arr[idx]);
                column_info[i].col_arr[idx] = real_length;
                column_info[i].valid_len = (column_info[i].line_len < line_length);
            }
        }
    }

    for (idx_t cols = max_cols; cols > 1; --cols) {
        if (column_info[cols - 1].valid_len)
            return cols;
    }

    return 1;
}

#include <stdlib.h>
#include <stdio.h>

void usage(int status)
{
    if (status != EXIT_SUCCESS)
    {
        emit_try_help();
        exit(status);
    }

    printf(_("Usage: %s [OPTION]... [FILE]...\n"), program_name);

    const char *help_msgs[] = {
        _("List information about the FILEs (the current directory by default).\n"
          "Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n"),
        NULL
    };

    for (int i = 0; help_msgs[i]; ++i)
        fputs(help_msgs[i], stdout);

    emit_mandatory_arg_note();

    const char *options[] = {
        _("  -a, --all                  do not ignore entries starting with .\n"
           "  -A, --almost-all           do not list implied . and ..\n"
           "      --author               with -l, print the author of each file\n"
           "  -b, --escape               print C-style escapes for nongraphic characters\n"),
        _("      --block-size=SIZE      with -l, scale sizes by SIZE when printing them;\n"
           "                             e.g., '--block-size=M'; see SIZE format below\n\n"),
        _("  -B, --ignore-backups       do not list implied entries ending with ~\n"),
        _("  -c                         with -lt: sort by, and show, ctime (time of last\n"
           "                             change of file status information);\n"
           "                             with -l: show ctime and sort by name;\n"
           "                             otherwise: sort by ctime, newest first\n\n"),
        _("  -C                         list entries by columns\n"
           "      --color[=WHEN]         color the output WHEN; more info below\n"
           "  -d, --directory            list directories themselves, not their contents\n"
           "  -D, --dired                generate output designed for Emacs' dired mode\n"),
        _("  -f                         same as -a -U\n"
           "  -F, --classify[=WHEN]      append indicator (one of */=>@|) to entries WHEN\n"
           "      --file-type            likewise, except do not append '*'\n"),
        _("      --format=WORD          across,horizontal (-x), commas (-m), long (-l),\n"
           "                             single-column (-1), verbose (-l), vertical (-C)\n\n"),
        _("      --full-time            like -l --time-style=full-iso\n"),
        _("  -g                         like -l, but do not list owner\n"),
        _("      --group-directories-first\n"
           "                             group directories before files\n"),
        _("  -G, --no-group             in a long listing, don't print group names\n"),
        _("  -h, --human-readable       with -l and -s, print sizes like 1K 234M 2G etc.\n"
           "      --si                   likewise, but use powers of 1000 not 1024\n"),
        _("  -H, --dereference-command-line\n"
           "                             follow symbolic links listed on the command line\n"),
        _("      --dereference-command-line-symlink-to-dir\n"
           "                             follow each command line symbolic link\n"
           "                             that points to a directory\n\n"),
        _("      --hide=PATTERN         do not list implied entries matching shell PATTERN\n"
           "                             (overridden by -a or -A)\n\n"),
        _("      --hyperlink[=WHEN]     hyperlink file names WHEN\n"),
        _("      --indicator-style=WORD\n"
           "                             append indicator with style WORD to entry names:\n"
           "                             none (default), slash (-p),\n"
           "                             file-type (--file-type), classify (-F)\n\n"),
        _("  -i, --inode                print the index number of each file\n"
           "  -I, --ignore=PATTERN       do not list implied entries matching shell PATTERN\n"),
        _("  -k, --kibibytes            default to 1024-byte blocks for file system usage;\n"
           "                             used only with -s and per directory totals\n\n"),
        _("  -l                         use a long listing format\n"),
        _("  -L, --dereference          when showing file information for a symbolic\n"
           "                             link, show information for the file the link\n"
           "                             references rather than for the link itself\n\n"),
        _("  -m                         fill width with a comma separated list of entries\n"),
        _("  -n, --numeric-uid-gid      like -l, but list numeric user and group IDs\n"
           "  -N, --literal              print entry names without quoting\n"
           "  -o                         like -l, but do not list group information\n"
           "  -p, --indicator-style=slash\n"
           "                             append / indicator to directories\n"),
        _("  -q, --hide-control-chars   print ? instead of nongraphic characters\n"),
        _("      --show-control-chars   show nongraphic characters as-is (the default,\n"
           "                             unless program is 'ls' and output is a terminal)\n\n"),
        _("  -Q, --quote-name           enclose entry names in double quotes\n"),
        _("      --quoting-style=WORD   use quoting style WORD for entry names:\n"
           "                             literal, locale, shell, shell-always,\n"
           "                             shell-escape, shell-escape-always, c, escape\n"
           "                             (overrides QUOTING_STYLE environment variable)\n\n"),
        _("  -r, --reverse              reverse order while sorting\n"
           "  -R, --recursive            list subdirectories recursively\n"
           "  -s, --size                 print the allocated size of each file, in blocks\n"),
        _("  -S                         sort by file size, largest first\n"),
        _("      --sort=WORD            change default 'name' sort to WORD:\n"
           "                               none (-U), size (-S), time (-t),\n"
           "                               version (-v), extension (-X), name, width\n\n"),
        _("      --time=WORD            select which timestamp used to display or sort;\n"
           "                               access time (-u): atime, access, use;\n"
           "                               metadata change time (-c): ctime, status;\n"
           "                               modified time (default): mtime, modification;\n"
           "                               birth time: birth, creation;\n"
           "                             with -l, WORD determines which time to show;\n"
           "                             with --sort=time, sort by WORD (newest first)\n\n"),
        _("      --time-style=TIME_STYLE\n"
           "                             time/date format with -l; see TIME_STYLE below\n"),
        _("  -t                         sort by time, newest first; see --time\n"
           "  -T, --tabsize=COLS         assume tab stops at each COLS instead of 8\n"),
        _("  -u                         with -lt: sort by, and show, access time;\n"
           "                             with -l: show access time and sort by name;\n"
           "                             otherwise: sort by access time, newest first\n\n"),
        _("  -U                         do not sort directory entries\n"),
        _("  -v                         natural sort of (version) numbers within text\n"),
        _("  -w, --width=COLS           set output width to COLS.  0 means no limit\n"
           "  -x                         list entries by lines instead of by columns\n"
           "  -X                         sort alphabetically by entry extension\n"
           "  -Z, --context              print any security context of each file\n"
           "      --zero                 end each output line with NUL, not newline\n"
           "  -1                         list one file per line\n"),
        NULL
    };

    for (int i = 0; options[i]; ++i)
        fputs(options[i], stdout);

    fputs(HELP_OPTION_DESCRIPTION, stdout);
    fputs(VERSION_OPTION_DESCRIPTION, stdout);

    emit_size_note();

    const char *notes[] = {
        _("\n"
          "The TIME_STYLE argument can be full-iso, long-iso, iso, locale, or +FORMAT.\n"
          "FORMAT is interpreted like in date(1).  If FORMAT is FORMAT1<newline>FORMAT2,\n"
          "then FORMAT1 applies to non-recent files and FORMAT2 to recent files.\n"
          "TIME_STYLE prefixed with 'posix-' takes effect only outside the POSIX locale.\n"
          "Also the TIME_STYLE environment variable sets the default style to use.\n"),
        _("\n"
          "The WHEN argument defaults to 'always' and can also be 'auto' or 'never'.\n"),
        _("\n"
          "Using color to distinguish file types is disabled both by default and\n"
          "with --color=never.  With --color=auto, ls emits color codes only when\n"
          "standard output is connected to a terminal.  The LS_COLORS environment\n"
          "variable can change the settings.  Use the dircolors(1) command to set it.\n"),
        _("\n"
          "Exit status:\n"
          " 0  if OK,\n"
          " 1  if minor problems (e.g., cannot access subdirectory),\n"
          " 2  if serious trouble (e.g., cannot access command-line argument).\n"),
        NULL
    };

    for (int i = 0; notes[i]; ++i)
        fputs(notes[i], stdout);

    emit_ancillary_info(PROGRAM_NAME);

    exit(status);
}
