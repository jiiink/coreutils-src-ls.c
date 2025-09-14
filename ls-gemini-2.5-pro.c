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
file_or_link_mode(struct fileinfo const *file)
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

static void
dired_outbyte (char c)
{
  dired_pos++;
  if (putchar ((unsigned char) c) == EOF)
    {
      perror ("Error writing to standard output");
      exit (EXIT_FAILURE);
    }
}

/* Output the buffer S, of length S_LEN, and increment DIRED_POS by S_LEN.  */
#include <stdio.h>
#include <stdlib.h>

static void
dired_outbuf (char const *s, size_t s_len)
{
  if (s_len > 0)
    {
      size_t items_written = fwrite (s, sizeof *s, s_len, stdout);
      if (items_written < s_len)
        {
          perror ("write error");
          exit (EXIT_FAILURE);
        }
      dired_pos += items_written;
    }
}

/* Output the string S, and increment DIRED_POS by its length.  */
static void
dired_outstring (char const *s)
{
  if (s)
    {
      dired_outbuf (s, strlen (s));
    }
}

static void
dired_indent (void)
{
  if (dired)
    {
      dired_outstring ("  ");
    }
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
  if (obs && dired)
    {
      obstack_grow (obs, &dired_pos, sizeof (dired_pos));
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
  struct dev_ino *di = obstack_alloc (&dev_ino_obstack, sizeof (struct dev_ino));
  di->st_dev = dev;
  di->st_ino = ino;
}

/* Pop a dev/ino struct off the global dev_ino_obstack
   and return that struct.  */
static struct dev_ino
dev_ino_pop (void)
{
  const size_t dev_ino_size = sizeof(struct dev_ino);
  affirm (dev_ino_size <= obstack_object_size (&dev_ino_obstack));

  obstack_blank_fast (&dev_ino_obstack, -((int) dev_ino_size));
  struct dev_ino *di = obstack_next_free (&dev_ino_obstack);

  return *di;
}

static void
assert_matching_dev_ino (char const *name, struct dev_ino di)
{
  struct stat sb;

  if (stat (name, &sb) != 0)
    {
      perror (name);
      abort ();
    }

  if (sb.st_dev != di.st_dev || sb.st_ino != di.st_ino)
    {
      fprintf (stderr, "Fatal: device/inode mismatch for %s\n", name);
      abort ();
    }
}

static char eolbyte = '\n';

/* Write to standard output PREFIX, followed by the quoting style and
   a space-separated list of the integers stored in OS all on one line.  */

static void
dired_dump_obstack (char const *prefix, struct obstack *os)
{
  const size_t n_pos = obstack_object_size (os) / sizeof (off_t);
  if (n_pos == 0)
    {
      return;
    }

  off_t * const pos = (off_t *) obstack_finish (os);

  if (fputs (prefix, stdout) == EOF)
    {
      return;
    }

  for (size_t i = 0; i < n_pos; i++)
    {
      const intmax_t p = pos[i];
      if (printf (" %jd", p) < 0)
        {
          return;
        }
    }

  if (putchar ('\n') == EOF)
    {
      return;
    }
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
static int do_stat(const char * const name, struct stat * const st)
{
    return stat(name, st);
}

static inline int do_lstat(const char *name, struct stat *st)
{
    return lstat(name, st);
}

static int
stat_for_mode (char const *name, struct stat *st)
{
  if (!name || !st)
    {
      errno = EINVAL;
      return -1;
    }
  return stat (name, st);
}

static inline int
stat_for_ino (char const *name, struct stat *st)
{
  return stat (name, st);
}

static inline int fstat_for_ino(int fd, struct stat *st)
{
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
  while (*fmt)
    {
      if (*fmt == '%')
        {
          char next_char = fmt[1];
          if (next_char == 'b')
            {
              return fmt;
            }
          if (next_char == '%')
            {
              fmt++;
            }
        }
      fmt++;
    }
  return NULL;
}

static char RFC3986[256];
static bool
is_rfc3986_unreserved_char (int c)
{
  return c_isalnum (c) || strchr ("-._~", c) != NULL;
}

static void
file_escape_init (void)
{
  for (int i = 0; i <= UCHAR_MAX; i++)
    {
      if (is_rfc3986_unreserved_char (i))
        {
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

static bool
abmon_init (char abmon[12][ABFORMAT_SIZE])
{
#ifndef HAVE_NL_LANGINFO
  return false;
#else
  enum { NUM_MONTHS = 12 };
  int max_mon_width = 0;
  int mon_width[NUM_MONTHS];
  size_t mon_len[NUM_MONTHS];

  for (int i = 0; i < NUM_MONTHS; i++)
    {
      const char *abbr = nl_langinfo (ABMON_1 + i);
      if (!abbr || strchr (abbr, '%'))
        return false;

      mon_len[i] = strnlen (abbr, ABFORMAT_SIZE);
      if (mon_len[i] == ABFORMAT_SIZE)
        return false;

      memcpy (abmon[i], abbr, mon_len[i]);
      abmon[i][mon_len[i]] = '\0';

      mon_width[i] = mbswidth (abmon[i], MBSWIDTH_FLAGS);
      if (mon_width[i] < 0)
        return false;

      if (max_mon_width < mon_width[i])
        max_mon_width = mon_width[i];
    }

  for (int i = 0; i < NUM_MONTHS; i++)
    {
      int fill = max_mon_width - mon_width[i];
      size_t final_len = mon_len[i] + fill;

      if (final_len >= ABFORMAT_SIZE)
        return false;

      if (!c_isdigit (abmon[i][0]))
        {
          memset (abmon[i] + mon_len[i], ' ', fill);
        }
      else
        {
          memmove (abmon[i] + fill, abmon[i], mon_len[i]);
          memset (abmon[i], ' ', fill);
        }

      abmon[i][final_len] = '\0';
    }

  return true;
#endif
}

/* Initialize ABFORMAT and USE_ABFORMAT.  */

#include <stdbool.h>
#include <stdio.h>
#include <stddef.h>
#include <limits.h>

// Assumed declarations from the original context for completeness.
#define ABFORMAT_SIZE 128
extern const char *long_time_format[2];
extern char abformat[2][12][ABFORMAT_SIZE];
extern bool use_abformat;
const char *first_percent_b(const char *format);
bool abmon_init(char (*abmon)[ABFORMAT_SIZE]);

static void
abformat_init (void)
{
  const char *pb[2];
  pb[0] = first_percent_b (long_time_format[0]);
  pb[1] = first_percent_b (long_time_format[1]);

  if (pb[0] == NULL && pb[1] == NULL)
    return;

  char abmon[12][ABFORMAT_SIZE];
  if (!abmon_init (abmon))
    return;

  for (int recent = 0; recent < 2; recent++)
    {
      const char *fmt = long_time_format[recent];
      const char *percent_b_ptr = pb[recent];

      for (int i = 0; i < 12; i++)
        {
          char *dest = abformat[recent][i];
          int nbytes;

          if (percent_b_ptr == NULL)
            {
              nbytes = snprintf (dest, ABFORMAT_SIZE, "%s", fmt);
            }
          else
            {
              ptrdiff_t prefix_len = percent_b_ptr - fmt;
              if (prefix_len < 0 || prefix_len > INT_MAX)
                return;

              nbytes = snprintf (dest, ABFORMAT_SIZE, "%.*s%s%s",
                                 (int) prefix_len, fmt, abmon[i],
                                 percent_b_ptr + 2);
            }

          if (nbytes < 0 || (size_t) nbytes >= ABFORMAT_SIZE)
            return;
        }
    }

  use_abformat = true;
}

static size_t
dev_ino_hash (void const *x, size_t table_size)
{
  if (!x || !table_size)
    {
      return 0;
    }

  struct dev_ino const *p = x;
  return (uintmax_t) p->st_ino % table_size;
}

static bool
dev_ino_compare (void const *x, void const *y)
{
  return PSAME_INODE ((struct dev_ino const *) x, (struct dev_ino const *) y);
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
    {
      xalloc_die ();
    }

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
  if (p)
    {
      free (p->name);
      free (p->realname);
      free (p);
    }
}

static bool
is_colored (enum indicator_no type)
{
  const char *s = color_indicator[type].string;
  size_t len = color_indicator[type].len;

  switch (len)
    {
    case 0:
      return false;
    case 1:
      return s[0] != '0';
    case 2:
      return s[0] != '0' || s[1] != '0';
    default:
      return true;
    }
}

static void
restore_default_color (void)
{
  const int indicators_to_restore[] = { C_LEFT, C_RIGHT };
  size_t num_indicators = sizeof (indicators_to_restore) / sizeof (indicators_to_restore[0]);

  for (size_t i = 0; i < num_indicators; ++i)
    {
      put_indicator (&color_indicator[indicators_to_restore[i]]);
    }
}

static void
set_normal_color(void)
{
    if (!print_with_color || !is_colored(C_NORM))
    {
        return;
    }

    put_indicator(&color_indicator[C_LEFT]);
    put_indicator(&color_indicator[C_NORM]);
    put_indicator(&color_indicator[C_RIGHT]);
}

/* An ordinary signal was received; arrange for the program to exit.  */

static void
sighandler (int sig)
{
  if (!interrupt_signal)
  {
    interrupt_signal = sig;
  }
}

/* A SIGTSTP was received; arrange for the program to suspend itself.  */

static void
stophandler (int sig)
{
  (void) sig;
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
  while (interrupt_signal || stop_signal_count > 0)
    {
      int sig_to_raise;
      sigset_t old_mask;

      if (used_color)
        restore_default_color ();
      fflush (stdout);

      if (sigprocmask (SIG_BLOCK, &caught_signals, &old_mask) != 0)
        abort ();

      if (stop_signal_count > 0)
        {
          stop_signal_count--;
          sig_to_raise = SIGSTOP;
        }
      else
        {
          struct sigaction sa;

          sig_to_raise = interrupt_signal;
          interrupt_signal = 0;

          sa.sa_handler = SIG_DFL;
          sigemptyset (&sa.sa_mask);
          sa.sa_flags = 0;

          if (sigaction (sig_to_raise, &sa, NULL) != 0)
            abort ();
        }

      raise (sig_to_raise);

      if (sigprocmask (SIG_SETMASK, &old_mask, NULL) != 0)
        abort ();
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

#if SA_NOCLDSTOP
  static sigset_t caught_signals;

  if (init)
    {
      struct sigaction new_act;
      struct sigaction old_act;

      sigemptyset (&caught_signals);

      for (size_t i = 0; i < nsigs; i++)
        {
          if (sigaction (sig[i], NULL, &old_act) == 0 && old_act.sa_handler != SIG_IGN)
            {
              sigaddset (&caught_signals, sig[i]);
            }
        }

      new_act.sa_mask = caught_signals;
      new_act.sa_flags = SA_RESTART;

      for (size_t i = 0; i < nsigs; i++)
        {
          if (sigismember (&caught_signals, sig[i]))
            {
              new_act.sa_handler = (sig[i] == SIGTSTP) ? stophandler : sighandler;
              if (sigaction (sig[i], &new_act, NULL) != 0)
                {
                  sigdelset (&caught_signals, sig[i]);
                }
            }
        }
    }
  else
    {
      struct sigaction dfl_act;
      sigemptyset (&dfl_act.sa_mask);
      dfl_act.sa_flags = 0;
      dfl_act.sa_handler = SIG_DFL;

      for (size_t i = 0; i < nsigs; i++)
        {
          if (sigismember (&caught_signals, sig[i]))
            {
              (void) sigaction (sig[i], &dfl_act, NULL);
            }
        }
    }
#else
  static bool caught_sig[nsigs];

  if (init)
    {
      for (size_t i = 0; i < nsigs; i++)
        {
          void (*old_handler) (int);

          old_handler = signal (sig[i], SIG_IGN);
          if (old_handler == SIG_ERR)
            {
              caught_sig[i] = false;
              continue;
            }

          caught_sig[i] = (old_handler != SIG_IGN);
          if (caught_sig[i])
            {
              void (*new_handler) (int) =
                (sig[i] == SIGTSTP) ? stophandler : sighandler;
              if (signal (sig[i], new_handler) == SIG_ERR)
                {
                  (void) signal (sig[i], old_handler);
                  caught_sig[i] = false;
                }
              else
                {
                  siginterrupt (sig[i], 0);
                }
            }
        }
    }
  else
    {
      for (size_t i = 0; i < nsigs; i++)
        {
          if (caught_sig[i])
            {
              (void) signal (sig[i], SIG_DFL);
            }
        }
    }
#endif
}

static void
signal_init (void)
{
  if (signal_setup (true) != 0)
    {
      perror ("Failed to initialize signal handlers");
      exit (EXIT_FAILURE);
    }
}

static void signal_restore(void)
{
    signal_setup(false);
}

static void
initialize_program (int *argc, char ***argv)
{
  initialize_main (argc, argv);
  set_program_name ((*argv)[0]);
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

static bool
needs_check_symlink_for_color (void)
{
  return is_colored (C_ORPHAN)
         || (is_colored (C_EXEC) && color_symlink_as_referent)
         || (is_colored (C_MISSING) && format == long_format);
}

static void
configure_output_options (void)
{
  if (print_with_color)
    parse_ls_color ();

  if (print_with_color)
    tabsize = 0;

  if (directories_first || (print_with_color && needs_check_symlink_for_color ()))
    check_symlink_mode = true;

  if (dereference == DEREF_UNDEFINED)
    {
      bool never_deref = immediate_dirs
                         || indicator_style == classify
                         || format == long_format;
      dereference = never_deref ? DEREF_NEVER : DEREF_COMMAND_LINE_SYMLINK_TO_DIR;
    }

  format_needs_stat = sort_type == sort_time
                      || sort_type == sort_size
                      || format == long_format
                      || print_block_size
                      || print_hyperlink
                      || print_scontext;

  format_needs_type = !format_needs_stat
                      && (recursive || print_with_color || print_scontext
                          || directories_first || (indicator_style != none));

  format_needs_capability = print_with_color && is_colored (C_CAP);
}

static void
initialize_special_modes (void)
{
  if (recursive)
    {
      active_dir_set = hash_initialize (INITIAL_TABLE_SIZE, NULL,
                                        dev_ino_hash,
                                        dev_ino_compare,
                                        dev_ino_free);
      if (active_dir_set == NULL)
        xalloc_die ();

      obstack_init (&dev_ino_obstack);
    }

  localtz = tzalloc (getenv ("TZ"));

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
  clear_files ();
}

static void
process_cmd_line_files (int n_files, char **files)
{
  if (n_files <= 0)
    {
      if (immediate_dirs)
        gobble_file (".", directory, NOT_AN_INODE_NUMBER, true, NULL);
      else
        queue_directory (".", NULL, true);
    }
  else
    {
      for (int i = 0; i < n_files; ++i)
        gobble_file (files[i], unknown, NOT_AN_INODE_NUMBER, true, NULL);
    }
}

static void
print_initial_files_and_prep_dirs (int n_files)
{
  if (cwd_n_used > 0)
    {
      print_current_files ();
      if (pending_dirs)
        dired_outbyte ('\n');
    }
  else if (n_files <= 1 && pending_dirs && !pending_dirs->next)
    {
      print_dir_name = false;
    }
}

static void
handle_loop_detection_marker (struct pending *p)
{
  struct dev_ino di = dev_ino_pop ();
  struct dev_ino *found = hash_remove (active_dir_set, &di);
  affirm (found);
  dev_ino_free (found);
  free_pending_ent (p);
}

static void
process_pending_dirs (void)
{
  while (pending_dirs)
    {
      struct pending *thispend = pending_dirs;
      pending_dirs = pending_dirs->next;

      if (LOOP_DETECT && thispend->name == NULL)
        {
          handle_loop_detection_marker (thispend);
          continue;
        }

      print_dir (thispend->name, thispend->realname,
                 thispend->command_line_arg);

      free_pending_ent (thispend);
      print_dir_name = true;
    }
}

static void
restore_color_and_handle_signals (void)
{
  bool is_default_escape =
    color_indicator[C_LEFT].len == 2
    && memcmp (color_indicator[C_LEFT].string, "\033[", 2) == 0
    && color_indicator[C_RIGHT].len == 1
    && color_indicator[C_RIGHT].string[0] == 'm';

  if (!is_default_escape)
    restore_default_color ();

  fflush (stdout);
  signal_restore ();

  for (int j = stop_signal_count; j > 0; j--)
    raise (SIGSTOP);

  if (interrupt_signal)
    raise (interrupt_signal);
}

static void
dump_dired_info (void)
{
  dired_dump_obstack ("//DIRED//", &dired_obstack);
  dired_dump_obstack ("//SUBDIRED//", &subdired_obstack);
  printf ("//DIRED-OPTIONS// --quoting-style=%s\n",
          quoting_style_args[get_quoting_style (filename_quoting_options)]);
}

static void
cleanup_and_exit (void)
{
  if (print_with_color && used_color)
    restore_color_and_handle_signals ();

  if (dired)
    dump_dired_info ();

  if (LOOP_DETECT)
    {
      assure (hash_get_n_entries (active_dir_set) == 0);
      hash_free (active_dir_set);
    }
}

int
main (int argc, char **argv)
{
  initialize_program (&argc, &argv);

  int first_file_index = decode_switches (argc, argv);

  configure_output_options ();
  initialize_special_modes ();

  int n_files = argc - first_file_index;
  process_cmd_line_files (n_files, argv + first_file_index);

  if (cwd_n_used > 0)
    {
      sort_files ();
      if (!immediate_dirs)
        extract_dirs_from_files (NULL, true);
    }

  print_initial_files_and_prep_dirs (n_files);

  process_pending_dirs ();

  cleanup_and_exit ();

  return exit_status;
}

/* Return the line length indicated by the value given by SPEC, or -1
   if unsuccessful.  0 means no limit on line length.  */

static ptrdiff_t
decode_line_length (char const *spec)
{
  uintmax_t val;
  enum strtol_error e = xstrtoumax (spec, nullptr, 0, &val, "");

  if (e != LONGINT_OK && e != LONGINT_OVERFLOW)
    {
      return -1;
    }

  if (e == LONGINT_OVERFLOW || val > PTRDIFF_MAX)
    {
      return 0;
    }

  return (ptrdiff_t)val;
}

/* Return true if standard output is a tty, caching the result.  */

static bool
stdout_isatty(void)
{
    static int is_tty_cached = -1;
    if (is_tty_cached < 0)
    {
        is_tty_cached = isatty(STDOUT_FILENO);
    }
    return is_tty_cached == 1;
}

/* Set all the option flags according to the switches specified.
   Return the index of the first non-option argument.  */

static int
get_when_option (const char *option_name, const char *optarg)
{
  if (optarg)
    return XARGMATCH (option_name, optarg, when_args, when_types);
  return when_always;
}

static void
handle_classify_option (const char *optarg)
{
  int i = get_when_option ("--classify", optarg);
  if (i == when_always || (i == when_if_tty && stdout_isatty ()))
    indicator_style = classify;
}

static void
handle_color_option (const char *optarg)
{
  int i = get_when_option ("--color", optarg);
  print_with_color = (i == when_always
                      || (i == when_if_tty && stdout_isatty ()));
}

static void
handle_hyperlink_option (const char *optarg)
{
  int i = get_when_option ("--hyperlink", optarg);
  print_hyperlink = (i == when_always
                     || (i == when_if_tty && stdout_isatty ()));
}

static void
handle_block_size_option (const char *optarg, int oi)
{
  enum strtol_error e = human_options (optarg, &human_output_opts,
                                       &output_block_size);
  if (e != LONGINT_OK)
    xstrtol_fatal (e, oi, 0, long_options, optarg);
  file_human_output_opts = human_output_opts;
  file_output_block_size = output_block_size;
}

static void
handle_hide_option (const char *optarg)
{
  struct ignore_pattern *hide = xmalloc (sizeof *hide);
  hide->pattern = optarg;
  hide->next = hide_patterns;
  hide_patterns = hide;
}

static void
finalize_block_size (bool kibibytes_specified)
{
  if (output_block_size)
    return;

  char const *ls_block_size = getenv ("LS_BLOCK_SIZE");
  human_options (ls_block_size, &human_output_opts, &output_block_size);
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

static void
finalize_format (int format_opt)
{
  if (format_opt >= 0)
    format = format_opt;
  else if (ls_mode == LS_LS)
    format = stdout_isatty () ? many_per_line : one_per_line;
  else if (ls_mode == LS_MULTI_COL)
    format = many_per_line;
  else /* ls_mode == LS_LONG_FORMAT */
    format = long_format;
}

static ptrdiff_t
determine_line_length (ptrdiff_t width_opt)
{
  ptrdiff_t len = width_opt;
  if (len < 0 && (format == many_per_line || format == horizontal
                  || format == with_commas || print_with_color))
    {
#ifdef TIOCGWINSZ
      struct winsize ws;
      if (stdout_isatty () && ioctl (STDOUT_FILENO, TIOCGWINSZ, &ws) >= 0
          && ws.ws_col > 0)
        len = ws.ws_col <= MIN (PTRDIFF_MAX, SIZE_MAX) ? ws.ws_col : 0;
#endif
      if (len < 0)
        {
          char const *p = getenv ("COLUMNS");
          if (p && *p)
            {
              len = decode_line_length (p);
              if (len < 0)
                error (0, 0,
                       _("ignoring invalid width"
                         " in environment variable COLUMNS: %s"),
                       quote (p));
            }
        }
    }
  return len < 0 ? 80 : len;
}

static void
determine_tab_size (ptrdiff_t tabsize_opt)
{
  if (tabsize_opt >= 0)
    {
      tabsize = tabsize_opt;
      return;
    }

  tabsize = 8;
  char const *p = getenv ("TABSIZE");
  if (p)
    {
      uintmax_t tmp;
      if (xstrtoumax (p, NULL, 0, &tmp, "") == LONGINT_OK && tmp <= SIZE_MAX)
        tabsize = tmp;
      else
        error (0, 0,
               _("ignoring invalid tab size"
                 " in environment variable TABSIZE: %s"),
               quote (p));
    }
}

static void
finalize_line_and_tab (ptrdiff_t width_opt, ptrdiff_t tabsize_opt)
{
  line_length = determine_line_length (width_opt);
  max_idx = line_length / MIN_COLUMN_WIDTH
            + (line_length % MIN_COLUMN_WIDTH != 0);

  if (format == many_per_line || format == horizontal || format == with_commas)
    determine_tab_size (tabsize_opt);
}

static void
finalize_quoting_style (int quoting_style_opt, int hide_control_chars_opt)
{
  qmark_funny_chars = (hide_control_chars_opt < 0
                       ? (ls_mode == LS_LS && stdout_isatty ())
                       : hide_control_chars_opt);

  int qs = quoting_style_opt;
  if (qs < 0)
    qs = getenv_quoting_style ();
  if (qs < 0)
    qs = (ls_mode == LS_LS
          ? (stdout_isatty () ? shell_escape_quoting_style : -1)
          : escape_quoting_style);
  if (qs >= 0)
    set_quoting_style (NULL, qs);

  qs = get_quoting_style (NULL);
  align_variable_outer_quotes =
    ((format == long_format
      || ((format == many_per_line || format == horizontal) && line_length))
     && (qs == shell_quoting_style || qs == shell_escape_quoting_style
         || qs == c_maybe_quoting_style));

  filename_quoting_options = clone_quoting_options (NULL);
  if (qs == escape_quoting_style)
    set_char_quoting (filename_quoting_options, ' ', 1);
  if (file_type <= indicator_style)
    {
      for (const char *p = &"*=>@|"[indicator_style - file_type]; *p; p++)
        set_char_quoting (filename_quoting_options, *p, 1);
    }

  dirname_quoting_options = clone_quoting_options (NULL);
  set_char_quoting (dirname_quoting_options, ':', 1);
}

static void
finalize_sort_type (int sort_opt, bool explicit_time)
{
  if (sort_opt >= 0)
    sort_type = sort_opt;
  else if (format != long_format && explicit_time)
    sort_type = sort_time;
  else
    sort_type = sort_name;
}

static void
parse_plus_time_style (const char *style)
{
  char const *p0 = style + 1;
  char *p0nl = strchr (p0, '\n');
  char const *p1 = p0;

  if (p0nl)
    {
      if (strchr (p0nl + 1, '\n'))
        error (LS_FAILURE, 0, _("invalid time style format %s"), quote (p0));
      *p0nl++ = '\0';
      p1 = p0nl;
    }
  long_time_format[0] = p0;
  long_time_format[1] = p1;
}

static void
set_time_format_from_style (int style_type)
{
  switch (style_type)
    {
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
      if (hard_locale (LC_TIME))
        {
          for (int i = 0; i < 2; i++)
            long_time_format[i] =
              dcgettext (NULL, long_time_format[i], LC_TIME);
        }
      break;
    default:
      break;
    }
}

static bool
finalize_time_style (const char *time_style_option)
{
  if (format != long_format)
    return true;

  char const *style = time_style_option;
  static char const posix_prefix[] = "posix-";

  if (!style)
    {
      style = getenv ("TIME_STYLE");
      if (!style)
        style = "locale";
    }

  if (STREQ_LEN (style, posix_prefix, sizeof posix_prefix - 1))
    {
      if (!hard_locale (LC_TIME))
        return false;
      style += sizeof posix_prefix - 1;
    }

  if (*style == '+')
    {
      parse_plus_time_style (style);
    }
  else
    {
      int style_type =
        x_timestyle_match (style, true, time_style_args,
                           (char const *) time_style_types,
                           sizeof (*time_style_types), LS_FAILURE);
      set_time_format_from_style (style_type);
    }

  abformat_init ();
  return true;
}

static int
decode_switches (int argc, char **argv)
{
  char const *time_style_option = NULL;
  bool kibibytes_specified = false;
  bool explicit_time = false;
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
        case 'a': ignore_mode = IGNORE_MINIMAL; break;
        case 'b': quoting_style_opt = escape_quoting_style; break;
        case 'c': time_type = time_ctime; explicit_time = true; break;
        case 'd': immediate_dirs = true; break;
        case 'f':
          ignore_mode = IGNORE_MINIMAL;
          sort_opt = sort_none;
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
        case 'i': print_inode = true; break;
        case 'k': kibibytes_specified = true; break;
        case 'l': format_opt = long_format; break;
        case 'm': format_opt = with_commas; break;
        case 'n': numeric_ids = true; format_opt = long_format; break;
        case 'o': format_opt = long_format; print_group = false; break;
        case 'p': indicator_style = slash; break;
        case 'q': hide_control_chars_opt = true; break;
        case 'r': sort_reverse = true; break;
        case 's': print_block_size = true; break;
        case 't': sort_opt = sort_time; break;
        case 'u': time_type = time_atime; explicit_time = true; break;
        case 'v': sort_opt = sort_version; break;
        case 'w':
          width_opt = decode_line_length (optarg);
          if (width_opt < 0)
            error (LS_FAILURE, 0, "%s: %s", _("invalid line width"),
                   quote (optarg));
          break;
        case 'x': format_opt = horizontal; break;
        case 'A': ignore_mode = IGNORE_DOT_AND_DOTDOT; break;
        case 'B':
          add_ignore_pattern ("*~");
          add_ignore_pattern (".*~");
          break;
        case 'C': format_opt = many_per_line; break;
        case 'D':
          format_opt = long_format;
          print_hyperlink = false;
          dired = true;
          break;
        case 'F': handle_classify_option (optarg); break;
        case 'G': print_group = false; break;
        case 'H': dereference = DEREF_COMMAND_LINE_ARGUMENTS; break;
        case 'I': add_ignore_pattern (optarg); break;
        case 'L': dereference = DEREF_ALWAYS; break;
        case 'N': quoting_style_opt = literal_quoting_style; break;
        case 'Q': quoting_style_opt = c_quoting_style; break;
        case 'R': recursive = true; break;
        case 'S': sort_opt = sort_size; break;
        case 'T':
          tabsize_opt = xnumtoumax (optarg, 0, 0, MIN (PTRDIFF_MAX, SIZE_MAX),
                                    "", _("invalid tab size"), LS_FAILURE, 0);
          break;
        case 'U': sort_opt = sort_none; break;
        case 'X': sort_opt = sort_extension; break;
        case 'Z': print_scontext = true; break;
        case '1':
          if (format_opt != long_format)
            format_opt = one_per_line;
          break;
        case FILE_TYPE_INDICATOR_OPTION: indicator_style = file_type; break;
        case DEREFERENCE_COMMAND_LINE_SYMLINK_TO_DIR_OPTION:
          dereference = DEREF_COMMAND_LINE_SYMLINK_TO_DIR;
          break;
        case AUTHOR_OPTION: print_author = true; break;
        case HIDE_OPTION: handle_hide_option (optarg); break;
        case SORT_OPTION:
          sort_opt = XARGMATCH ("--sort", optarg, sort_args, sort_types);
          break;
        case GROUP_DIRECTORIES_FIRST_OPTION: directories_first = true; break;
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
        case COLOR_OPTION: handle_color_option (optarg); break;
        case HYPERLINK_OPTION: handle_hyperlink_option (optarg); break;
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
        case TIME_STYLE_OPTION: time_style_option = optarg; break;
        case SHOW_CONTROL_CHARS_OPTION: hide_control_chars_opt = false; break;
        case BLOCK_SIZE_OPTION: handle_block_size_option (optarg, oi); break;
        case SI_OPTION:
          file_human_output_opts = human_output_opts =
            human_autoscale | human_SI;
          file_output_block_size = output_block_size = 1;
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

  finalize_block_size (kibibytes_specified);
  finalize_format (format_opt);
  finalize_line_and_tab (width_opt, tabsize_opt);
  finalize_quoting_style (quoting_style_opt, hide_control_chars_opt);
  finalize_sort_type (sort_opt, explicit_time);

  dired &= (format == long_format) & !print_hyperlink;
  if (eolbyte < dired)
    error (LS_FAILURE, 0, _("--dired and --zero are incompatible"));

  if (!finalize_time_style (time_style_option))
    return optind;

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
  enum
  {
    ST_GND, ST_BACKSLASH, ST_OCTAL, ST_HEX, ST_CARET, ST_END, ST_ERROR
  } state = ST_GND;
  char const *p = *src;
  char *q = *dest;

  while (state < ST_END)
    {
      switch (state)
        {
        case ST_GND:
          {
            const char c = *p;
            if (c == '\0' || c == ':')
              {
                state = ST_END;
              }
            else if (c == '=' && equals_end)
              {
                state = ST_END;
              }
            else if (c == '\\')
              {
                state = ST_BACKSLASH;
                p++;
              }
            else if (c == '^')
              {
                state = ST_CARET;
                p++;
              }
            else
              {
                *q++ = *p++;
                count++;
              }
          }
          break;

        case ST_BACKSLASH:
          {
            const char c = *p;
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
            else if (c == '\0')
              {
                state = ST_ERROR;
              }
            else
              {
                char out_char;
                switch (c)
                  {
                  case 'a': out_char = '\a'; break;
                  case 'b': out_char = '\b'; break;
                  case 'e': out_char = '\x1B'; break;
                  case 'f': out_char = '\f'; break;
                  case 'n': out_char = '\n'; break;
                  case 'r': out_char = '\r'; break;
                  case 't': out_char = '\t'; break;
                  case 'v': out_char = '\v'; break;
                  case '?': out_char = '\x7F'; break;
                  case '_': out_char = ' '; break;
                  default:  out_char = c; break;
                  }
                *q++ = out_char;
                count++;
                state = ST_GND;
              }
            p++;
          }
          break;

        case ST_OCTAL:
          {
            const char c = *p;
            if (c >= '0' && c <= '7')
              {
                num = (num << 3) + (c - '0');
                p++;
              }
            else
              {
                *q++ = num;
                count++;
                state = ST_GND;
              }
          }
          break;

        case ST_HEX:
          {
            const char c = *p;
            int digit_val = -1;
            if (c >= '0' && c <= '9')
              {
                digit_val = c - '0';
              }
            else if (c >= 'a' && c <= 'f')
              {
                digit_val = c - 'a' + 10;
              }
            else if (c >= 'A' && c <= 'F')
              {
                digit_val = c - 'A' + 10;
              }

            if (digit_val != -1)
              {
                num = (num << 4) + digit_val;
                p++;
              }
            else
              {
                *q++ = num;
                count++;
                state = ST_GND;
              }
          }
          break;

        case ST_CARET:
          {
            const char c = *p;
            if (c == '?')
              {
                *q++ = '\x7F';
                p++;
                count++;
                state = ST_GND;
              }
            else if (c >= '@' && c <= '~')
              {
                *q++ = c & 0x1F;
                p++;
                count++;
                state = ST_GND;
              }
            else
              {
                state = ST_ERROR;
              }
          }
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
  if (!term || !*term)
    {
      return false;
    }

  static const char TERM_PREFIX[] = "TERM ";
  const size_t PREFIX_LEN = sizeof (TERM_PREFIX) - 1;
  const char *line = G_line;
  const char * const end = G_line + sizeof (G_line);

  while (line < end && *line)
    {
      if (strncmp (line, TERM_PREFIX, PREFIX_LEN) == 0 &&
          fnmatch (line + PREFIX_LEN, term, 0) == 0)
        {
          return true;
        }

      const char *next = memchr (line, '\0', end - line);
      if (!next)
        {
          break;
        }
      line = next + 1;
    }

  return false;
}

static void
cleanup_on_parse_error (void)
{
  error (0, 0, _("unparsable value for LS_COLORS environment variable"));
  free (color_buf);
  color_buf = NULL;

  struct color_ext_type *e = color_ext_list;
  while (e != NULL)
    {
      struct color_ext_type *next = e->next;
      free (e);
      e = next;
    }
  color_ext_list = NULL;

  print_with_color = false;
}

static void
postprocess_extensions (void)
{
  for (struct color_ext_type *e1 = color_ext_list; e1 != NULL; e1 = e1->next)
    {
      bool case_ignored = false;
      for (struct color_ext_type *e2 = e1->next; e2 != NULL; e2 = e2->next)
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
              else if (e1->seq.len == e2->seq.len
                       && memcmp (e1->seq.string, e2->seq.string,
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
}

static bool
handle_indicator_entry (const char **p_ptr, char **buf_ptr)
{
  const char *p_start = *p_ptr;
  if (p_start[0] == '\0' || p_start[1] == '\0' || p_start[2] != '=')
    return false;

  char label0 = p_start[0];
  char label1 = p_start[1];
  const char *p = p_start + 3;

  for (size_t i = 0; i < ARRAY_CARDINALITY (indicator_name); i++)
    {
      if (label0 == indicator_name[i][0] && label1 == indicator_name[i][1])
        {
          color_indicator[i].string = *buf_ptr;
          if (get_funky_string (buf_ptr, &p, false, &color_indicator[i].len))
            {
              *p_ptr = p;
              return true;
            }
          return false;
        }
    }

  error (0, 0, _("unrecognized prefix: %s"),
         quote ((char[]) {label0, label1, '\0'}));
  return false;
}

static bool
handle_extension_entry (const char **p_ptr, char **buf_ptr)
{
  struct color_ext_type *ext = xmalloc (sizeof *ext);
  ext->next = color_ext_list;
  color_ext_list = ext;
  ext->exact_match = false;

  ext->ext.string = *buf_ptr;
  if (!get_funky_string (buf_ptr, p_ptr, true, &ext->ext.len))
    return false;

  if (*(*p_ptr)++ != '=')
    return false;

  ext->seq.string = *buf_ptr;
  return get_funky_string (buf_ptr, p_ptr, false, &ext->seq.len);
}

static void
parse_ls_color (void)
{
  const char *ls_colors = getenv ("LS_COLORS");
  if (ls_colors == NULL || *ls_colors == '\0')
    {
      const char *colorterm = getenv ("COLORTERM");
      if (!(colorterm && *colorterm) && !known_term_type ())
        print_with_color = false;
      return;
    }

  color_buf = xstrdup (ls_colors);
  char *buf = color_buf;
  const char *p = ls_colors;
  bool parsing_ok = true;

  while (*p != '\0')
    {
      if (*p == ':')
        {
          p++;
          continue;
        }

      bool success;
      if (*p == '*')
        {
          p++;
          success = handle_extension_entry (&p, &buf);
        }
      else
        {
          success = handle_indicator_entry (&p, &buf);
        }

      if (!success)
        {
          parsing_ok = false;
          break;
        }
    }

  if (parsing_ok)
    {
      postprocess_extensions ();
      if (color_indicator[C_LINK].len == 6
          && memcmp (color_indicator[C_LINK].string, "target", 6) == 0)
        color_symlink_as_referent = true;
    }
  else
    {
      cleanup_on_parse_error ();
    }
}

/* Return the quoting style specified by the environment variable
   QUOTING_STYLE if set and valid, -1 otherwise.  */

static int
getenv_quoting_style (void)
{
  char const *q_style = getenv ("QUOTING_STYLE");
  if (!q_style)
    {
      return -1;
    }

  const int i = ARGMATCH (q_style, quoting_style_args, quoting_style_vals);
  if (i >= 0)
    {
      return quoting_style_vals[i];
    }

  error (0, 0,
         _("ignoring invalid value of environment variable QUOTING_STYLE: %s"),
         quote (q_style));
  return -1;
}

/* Set the exit status to report a failure.  If SERIOUS, it is a
   serious failure; otherwise, it is merely a minor problem.  */

static void
set_exit_status (bool serious)
{
  int const new_status = serious ? LS_FAILURE : LS_MINOR_PROBLEM;

  if (new_status > exit_status)
    {
      exit_status = new_status;
    }
}

/* Assuming a failure is serious if SERIOUS, use the printf-style
   MESSAGE to report the failure to access a file named FILE.  Assume
   errno is set appropriately for the failure.  */

static void
file_failure (bool serious, char const *message, char const *file)
{
  char *quoted_file = quoteaf (file);
  error (0, errno, message, quoted_file);
  free (quoted_file);
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

static char *
safe_strdup (char const *s)
{
  return s ? xstrdup (s) : NULL;
}

static void
queue_directory (char const *name, char const *realname, bool command_line_arg)
{
  struct pending *new_node = xmalloc (sizeof *new_node);

  new_node->realname = safe_strdup (realname);
  new_node->name = safe_strdup (name);
  new_node->command_line_arg = command_line_arg;

  new_node->next = pending_dirs;
  pending_dirs = new_node;
}

/* Read directory NAME, and list the files in it.
   If REALNAME is nonzero, print its name instead of NAME;
   this is used for symbolic links to directories.
   COMMAND_LINE_ARG means this directory was mentioned on the command line.  */

static bool
check_for_directory_loop (char const *name, DIR *dirp, bool command_line_arg)
{
  struct stat dir_stat;
  int fd = dirfd (dirp);

  if ((0 <= fd ? fstat_for_ino (fd, &dir_stat)
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
                        bool command_line_arg)
{
  static bool first_dir = true;

  if (! (recursive || print_dir_name))
    return;

  if (!first_dir)
    dired_outbyte ('\n');
  first_dir = false;

  dired_indent ();

  char *absolute_name = NULL;
  if (print_hyperlink)
    {
      absolute_name = canonicalize_filename_mode (name, CAN_MISSING);
      if (!absolute_name)
        file_failure (command_line_arg, _("error canonicalizing %s"), name);
    }

  quote_name (realname ? realname : name, dirname_quoting_options, -1,
              NULL, true, &subdired_obstack, absolute_name);
  free (absolute_name);

  dired_outstring (":\n");
}

static uintmax_t
read_directory_entries (DIR *dirp, char const *name, bool command_line_arg)
{
  uintmax_t total_blocks = 0;

  while (true)
    {
      errno = 0;
      struct dirent *next = readdir (dirp);
      if (next)
        {
          if (!file_ignored (next->d_name))
            {
              enum filetype type = unknown;
#if HAVE_STRUCT_DIRENT_D_TYPE
              type = d_type_filetype[next->d_type];
#endif
              total_blocks += gobble_file (next->d_name, type,
                                           RELIABLE_D_INO (next), false, name);

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
  return total_blocks;
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

static void
print_dir (char const *name, char const *realname, bool command_line_arg)
{
  DIR *dirp = opendir (name);
  if (!dirp)
    {
      file_failure (command_line_arg, _("cannot open directory %s"), name);
      return;
    }

  if (LOOP_DETECT && !check_for_directory_loop (name, dirp, command_line_arg))
    {
      closedir (dirp);
      return;
    }

  clear_files ();
  print_directory_header (name, realname, command_line_arg);

  uintmax_t total_blocks = read_directory_entries (dirp, name, command_line_arg);

  if (closedir (dirp) != 0)
    {
      file_failure (command_line_arg, _("closing directory %s"), name);
    }

  sort_files ();

  if (recursive)
    extract_dirs_from_files (name, false);

  if (format == long_format || print_block_size)
    print_total_blocks (total_blocks);

  if (cwd_n_used)
    print_current_files ();
}

/* Add 'pattern' to the list of patterns for which files that match are
   not listed.  */

static void
add_ignore_pattern (struct ignore_pattern **list_head, char const *pattern)
{
  struct ignore_pattern *new_node = xmalloc (sizeof *new_node);
  new_node->pattern = pattern;
  new_node->next = *list_head;
  *list_head = new_node;
}

/* Return true if one of the PATTERNS matches FILE.  */

static bool
patterns_match (const struct ignore_pattern *patterns, const char *file)
{
  if (!file)
    {
      return false;
    }

  for (const struct ignore_pattern *p = patterns; p; p = p->next)
    {
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
  if (patterns_match (ignore_patterns, name))
    {
      return true;
    }

  switch (ignore_mode)
    {
    case IGNORE_DEFAULT:
      if (name[0] == '.' || patterns_match (hide_patterns, name))
        {
          return true;
        }
      break;

    case IGNORE_MINIMAL:
      return false;

    default:
      if (name[0] == '.' && (name[1] == '\0' || (name[1] == '.' && name[2] == '\0')))
        {
          return true;
        }
      break;
    }

  return false;
}

/* POSIX requires that a file size be printed without a sign, even
   when negative.  Assume the typical case where negative sizes are
   actually positive values that have wrapped around.  */

static uintmax_t
unsigned_file_size (off_t size)
{
  return (uintmax_t) size;
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
  if (f)
    {
      free (f->name);
      free (f->linkname);
      free (f->absolute_name);
      if (f->scontext != UNKNOWN_SECURITY_CONTEXT)
        {
          aclinfo_scontext_free (f->scontext);
        }
    }
}

/* Empty the table of files.  */
static void
clear_files (void)
{
  while (cwd_n_used > 0)
    {
      free_ent (sorted_file[--cwd_n_used]);
    }

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
#include <stdbool.h>
#include <sys/types.h>

struct fileinfo {
    bool stat_ok;
    struct stat stat;
};

struct aclinfo {
    char *buf;
    size_t size;
    char *scontext;
    int scontext_err;
    union {
        char __gl_acl_ch[1];
    } u;
};

extern int file_has_aclinfo(char const *file, struct aclinfo *ai, int flags);
extern bool acl_errno_valid(int err);

#define ACL_GET_SCONTEXT 1

struct unsupported_device_info
{
  dev_t dev;
  int return_code;
  char *scontext;
  int scontext_err;
};

static struct unsupported_device_info unsupported_cache;

static int
file_has_aclinfo_cache (char const *file, struct fileinfo *f,
                        struct aclinfo *ai, int flags)
{
  if (f->stat_ok && unsupported_cache.scontext
      && f->stat.st_dev == unsupported_cache.dev)
    {
      ai->buf = ai->u.__gl_acl_ch;
      ai->size = 0;
      ai->scontext = unsupported_cache.scontext;
      ai->scontext_err = unsupported_cache.scontext_err;
      errno = ENOTSUP;
      return unsupported_cache.return_code;
    }

  errno = 0;
  int n = file_has_aclinfo (file, ai, flags);
  int err = errno;

  bool is_unsupported_error = !acl_errno_valid(err)
    && (!(flags & ACL_GET_SCONTEXT) || !acl_errno_valid(ai->scontext_err));

  if (f->stat_ok && n <= 0 && is_unsupported_error)
    {
      unsupported_cache.dev = f->stat.st_dev;
      unsupported_cache.return_code = n;
      unsupported_cache.scontext = ai->scontext;
      unsupported_cache.scontext_err = ai->scontext_err;
    }
    
  return n;
}

/* Cache has_capability failure, when it's trivial to do.
   Like has_capability, but when F's st_dev says it's on a file
   system lacking capability support, return 0 with ENOTSUP immediately.  */
static bool
has_capability_cache (char const *file, struct fileinfo *f)
{
    static bool unsupported_cached = false;
    static dev_t unsupported_device;

    if (f->stat_ok && unsupported_cached && f->stat.st_dev == unsupported_device)
    {
        errno = ENOTSUP;
        return false;
    }

    const bool result = has_capability(file);

    if (f->stat_ok && !result && !acl_errno_valid(errno))
    {
        unsupported_cached = true;
        unsupported_device = f->stat.st_dev;
    }

    return result;
}

static bool
needs_quoting (char const *name)
{
  if (name == NULL || *name == '\0')
    {
      return false;
    }

  size_t name_len = strlen (name);
  size_t quoted_len = quotearg_buffer (NULL, 0, name, name_len,
                                       filename_quoting_options);

  return name_len != quoted_len;
}

/* Add a file to the current table of files.
   Verify that the file exists, and print an error message if it does not.
   Return the number of blocks that the file occupies.  */
static bool
should_stat_file (enum filetype type, ino_t inode, bool command_line_arg)
{
  if (command_line_arg || print_hyperlink || format_needs_stat)
    return true;

  if (format_needs_type && type == unknown)
    return true;

  if ((type == directory || type == unknown) && print_with_color
      && (is_colored (C_OTHER_WRITABLE)
          || is_colored (C_STICKY)
          || is_colored (C_STICKY_OTHER_WRITABLE)))
    return true;

  if ((print_inode || format_needs_type)
      && (type == symbolic_link || type == unknown)
      && (dereference == DEREF_ALWAYS
          || color_symlink_as_referent || check_symlink_mode))
    return true;

  if (print_inode && inode == NOT_AN_INODE_NUMBER)
    return true;

  if ((type == normal || type == unknown)
      && (indicator_style == classify
          || (print_with_color && (is_colored (C_EXEC)
                                   || is_colored (C_SETUID)
                                   || is_colored (C_SETGID)))))
    return true;

  return false;
}

static int
perform_stat (struct fileinfo *f, char const *full_name,
              bool command_line_arg, bool *do_deref)
{
  int err;

  if (print_hyperlink)
    {
      f->absolute_name = canonicalize_filename_mode (full_name, CAN_MISSING);
      if (!f->absolute_name)
        file_failure (command_line_arg,
                      _("error canonicalizing %s"), full_name);
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

          bool stat_failed_or_not_dir = (err < 0
              ? (errno == ENOENT || errno == ELOOP)
              : !S_ISDIR (f->stat.st_mode));

          if (!stat_failed_or_not_dir)
            break;
        }
      FALLTHROUGH;

    case DEREF_NEVER:
      err = do_lstat (full_name, &f->stat);
      *do_deref = false;
      break;

    case DEREF_UNDEFINED: default:
      unreachable ();
    }

  return err;
}

static void
get_security_and_acl_info (struct fileinfo *f, enum filetype type,
                           char const *full_name, bool do_deref)
{
  bool get_scontext = (format == long_format) || print_scontext;
  bool check_capability = format_needs_capability && (type == normal);

  if (!get_scontext && !check_capability)
    return;

  struct aclinfo ai;
  int aclinfo_flags = ((do_deref ? ACL_SYMLINK_FOLLOW : 0)
                       | (get_scontext ? ACL_GET_SCONTEXT : 0)
                       | filetype_d_type[type]);
  int n = file_has_aclinfo_cache (full_name, f, &ai, aclinfo_flags);
  bool have_acl = n > 0;
  bool have_scontext = !ai.scontext_err;

  bool cannot_access_acl = n < 0 && (errno == EACCES || errno == ENOENT);

  if (!have_scontext && !have_acl)
    f->acl_type = (cannot_access_acl ? ACL_T_UNKNOWN : ACL_T_NONE);
  else
    f->acl_type = (have_scontext && !have_acl
                   ? ACL_T_LSM_CONTEXT_ONLY
                   : ACL_T_YES);
  any_has_acl |= f->acl_type != ACL_T_NONE;

  if (format == long_format && n < 0 && !cannot_access_acl)
    error (0, errno, "%s", quotef (full_name));
  else
    {
      if (print_scontext && ai.scontext_err
          && !(is_ENOTSUP (ai.scontext_err) || ai.scontext_err == ENODATA))
        error (0, ai.scontext_err, "%s", quotef (full_name));
    }

  if (check_capability && aclinfo_has_xattr (&ai, XATTR_NAME_CAPS))
    f->has_capability = has_capability_cache (full_name, f);

  f->scontext = ai.scontext;
  ai.scontext = nullptr;
  aclinfo_free (&ai);
}

static void
process_symlink (struct fileinfo *f, char const *full_name, bool command_line_arg)
{
  if (!(format == long_format || check_symlink_mode))
    return;

  get_link_name (full_name, f, command_line_arg);

  if (f->linkname && f->quoted == 0 && needs_quoting (f->linkname))
    f->quoted = -1;

  if (f->linkname && (file_type <= indicator_style || check_symlink_mode))
    {
      struct stat linkstats;
      if (stat_for_mode (full_name, &linkstats) == 0)
        {
          f->linkok = true;
          f->linkmode = linkstats.st_mode;
        }
    }
}

static void
update_column_widths (struct fileinfo const *f, enum filetype type,
                      uintmax_t blocks)
{
  char buf[LONGEST_HUMAN_READABLE + 1];

  if (format == long_format || print_block_size)
    {
      int len = mbswidth (human_readable (blocks, buf, human_output_opts,
                                          ST_NBLOCKSIZE, output_block_size),
                          MBSWIDTH_FLAGS);
      if (block_size_width < len)
        block_size_width = len;
    }

  if (print_inode)
    {
      int len = strlen (umaxtostr (f->stat.st_ino, buf));
      if (inode_number_width < len)
        inode_number_width = len;
    }

  if (print_scontext)
    {
      int len = strlen (f->scontext);
      if (scontext_width < len)
        scontext_width = len;
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

      int b_len = strlen (umaxtostr (f->stat.st_nlink, buf));
      if (nlink_width < b_len)
        nlink_width = b_len;

      if (type == chardev || type == blockdev)
        {
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
          uintmax_t size = unsigned_file_size (f->stat.st_size);
          int len = mbswidth (human_readable (size, buf,
                                              file_human_output_opts,
                                              1, file_output_block_size),
                              MBSWIDTH_FLAGS);
          if (file_size_width < len)
            file_size_width = len;
        }
    }
}

static uintmax_t
gobble_file (char const *name, enum filetype type, ino_t inode,
             bool command_line_arg, char const *dirname)
{
  affirm (!command_line_arg || inode == NOT_AN_INODE_NUMBER);

  if (cwd_n_used == cwd_n_alloc)
    cwd_file = xpalloc (cwd_file, &cwd_n_alloc, 1, -1, sizeof *cwd_file);

  struct fileinfo *f = &cwd_file[cwd_n_used];
  memset (f, '\0', sizeof *f);
  f->stat.st_ino = inode;
  f->filetype = type;
  f->scontext = UNKNOWN_SECURITY_CONTEXT;
  f->quoted = -1;

  if (!cwd_some_quoted && align_variable_outer_quotes)
    {
      f->quoted = needs_quoting (name);
      if (f->quoted)
        cwd_some_quoted = true;
    }

  bool check_stat = should_stat_file (type, inode, command_line_arg);

  char const *full_name = name;
  if ((check_stat || print_scontext || format_needs_capability)
      && name[0] != '/' && dirname)
    {
      char *p = alloca (strlen (name) + strlen (dirname) + 2);
      attach (p, dirname, name);
      full_name = p;
    }

  bool do_deref = false;
  if (!check_stat)
    {
      do_deref = (dereference == DEREF_ALWAYS);
    }
  else
    {
      int err = perform_stat (f, full_name, command_line_arg, &do_deref);
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

  get_security_and_acl_info (f, type, full_name, do_deref);

  if (type == symbolic_link)
    process_symlink (f, full_name, command_line_arg);

  uintmax_t blocks = f->stat_ok ? STP_NBLOCKS (&f->stat) : 0;
  update_column_widths (f, type, blocks);

  f->name = xstrdup (name);
  cwd_n_used++;

  return blocks;
}

/* Return true if F refers to a directory.  */
static bool
is_directory (const struct fileinfo *f)
{
  return f && (f->filetype == directory || f->filetype == arg_directory);
}

/* Return true if F refers to a (symlinked) directory.  */
static bool
is_linked_directory (const struct fileinfo *f)
{
  const bool is_direct_directory = f->filetype == directory
                                    || f->filetype == arg_directory;
  const bool is_link_to_directory = S_ISDIR (f->linkmode);

  return is_direct_directory || is_link_to_directory;
}

/* Put the name of the file that FILENAME is a symbolic link to
   into the LINKNAME field of 'f'.  COMMAND_LINE_ARG indicates whether
   FILENAME is a command-line argument.  */

static void
get_link_name (char const *filename, struct fileinfo *f, bool command_line_arg)
{
  f->linkname = areadlink_with_size (filename, f->stat.st_size);
  if (f->linkname == NULL)
    {
      file_failure (command_line_arg, _("cannot read symbolic link %s"),
                    filename);
    }
}

/* Return true if the last component of NAME is '.' or '..'
   This is so we don't try to recurse on '././././. ...' */

static bool
basename_is_dot_or_dotdot (char const *name)
{
  return dot_or_dotdot (last_component (name));
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
  if (dirname && LOOP_DETECT)
    {
      queue_directory (nullptr, dirname, false);
    }

  idx_t write_idx = cwd_n_used;
  bool const ignore_dot_and_dot_dot = (dirname != nullptr);

  for (idx_t i = cwd_n_used; i > 0; )
    {
      i--;
      struct fileinfo *f = sorted_file[i];

      if (is_directory (f)
          && (!ignore_dot_and_dot_dot
              || !basename_is_dot_or_dotdot (f->name)))
        {
          char *name_to_queue = f->name;
          char *allocated_name = NULL;

          if (dirname && f->name[0] != '/')
            {
              allocated_name = file_name_concat (dirname, f->name, NULL);
              name_to_queue = allocated_name;
            }

          queue_directory (name_to_queue, f->linkname, command_line_arg);
          free (allocated_name);
        }

      if (f->filetype == arg_directory)
        {
          free_ent (f);
        }
      else
        {
          write_idx--;
          sorted_file[write_idx] = f;
        }
    }

  idx_t const kept_count = cwd_n_used - write_idx;
  if (write_idx > 0 && kept_count > 0)
    {
      memmove (sorted_file, &sorted_file[write_idx],
               kept_count * sizeof (*sorted_file));
    }
  cwd_n_used = kept_count;
}

/* Use strcoll to compare strings in this locale.  If an error occurs,
   report an error and longjmp to failed_strcoll.  */

static jmp_buf failed_strcoll;

static int
xstrcoll (char const *a, char const *b)
{
  errno = 0;
  int diff = strcoll (a, b);
  if (errno != 0)
    {
      error (EXIT_FAILURE, errno, _("cannot compare file names %s and %s"),
             quote_n (0, a), quote_n (1, b));
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
  int a_is_dir = is_linked_directory (a);
  int b_is_dir = is_linked_directory (b);

  if (a_is_dir != b_is_dir)
    {
      return a_is_dir ? -1 : 1;
    }

  return cmp (a, b);
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

  if (cmp)
  {
    return cmp (a->name, b->name);
  }

  return 0;
}

static int
cmp_mtime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int diff = timespec_cmp (get_stat_mtime (&b->stat),
                           get_stat_mtime (&a->stat));
  if (diff != 0)
    {
      return diff;
    }
  return cmp (a->name, b->name);
}

static int
cmp_atime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == b)
    {
      return 0;
    }
  if (a == NULL)
    {
      return -1;
    }
  if (b == NULL)
    {
      return 1;
    }

  const int diff = timespec_cmp(get_stat_atime(&b->stat),
                                get_stat_atime(&a->stat));
  if (diff != 0)
    {
      return diff;
    }

  if (cmp != NULL)
    {
      return cmp(a->name, b->name);
    }

  return 0;
}

static int
cmp_btime (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  if (a == b)
    {
      return 0;
    }
  if (!a)
    {
      return -1;
    }
  if (!b)
    {
      return 1;
    }

  int diff = timespec_cmp (get_stat_btime (&b->stat),
                           get_stat_btime (&a->stat));

  if (diff != 0)
    {
      return diff;
    }

  if (cmp)
    {
      return cmp (a->name, b->name);
    }

  return 0;
}

static int
off_cmp (off_t a, off_t b)
{
  if (a > b)
    {
      return 1;
    }
  if (a < b)
    {
      return -1;
    }
  return 0;
}

static int
cmp_size (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  int diff = off_cmp (b->stat.st_size, a->stat.st_size);
  if (diff != 0)
    {
      return diff;
    }

  if (a->name == b->name)
    {
      return 0;
    }
  if (a->name == NULL)
    {
      return -1;
    }
  if (b->name == NULL)
    {
      return 1;
    }

  if (cmp)
    {
      return cmp (a->name, b->name);
    }

  return 0;
}

static int
cmp_name (struct fileinfo const *a, struct fileinfo const *b,
          int (*cmp) (char const *, char const *))
{
  if (a->name == b->name)
    {
      return 0;
    }
  if (a->name == NULL)
    {
      return -1;
    }
  if (b->name == NULL)
    {
      return 1;
    }
  return cmp (a->name, b->name);
}

/* Compare file extensions.  Files with no extension are 'smallest'.
   If extensions are the same, compare by file names instead.  */

static int
cmp_extension (struct fileinfo const *a, struct fileinfo const *b,
               int (*cmp) (char const *, char const *))
{
  char const *ext_a = strrchr (a->name, '.');
  char const *ext_b = strrchr (b->name, '.');

  char const *cmp_str_a = ext_a ? ext_a : "";
  char const *cmp_str_b = ext_b ? ext_b : "";

  int diff = cmp (cmp_str_a, cmp_str_b);

  if (diff == 0)
    {
      return cmp (a->name, b->name);
    }

  return diff;
}

/* Return the (cached) screen width,
   for the NAME associated with the passed fileinfo F.  */

static size_t
fileinfo_name_width (struct fileinfo const *f)
{
  if (!f)
    {
      return 0;
    }

  if (f->width)
    {
      return f->width;
    }

  return quote_name_width (f->name, filename_quoting_options, f->quoted);
}

static int
cmp_width (struct fileinfo const *a, struct fileinfo const *b,
           int (*cmp) (char const *, char const *))
{
  int const width_a = fileinfo_name_width (a);
  int const width_b = fileinfo_name_width (b);

  if (width_a < width_b)
    return -1;

  if (width_a > width_b)
    return 1;

  return cmp (a->name, b->name);
}

#include <stdlib.h>
#include <time.h>

typedef time_t ctime;

static int cmp_ctime(const void *a, const void *b)
{
    const ctime *time_a = (const ctime *)a;
    const ctime *time_b = (const ctime *)b;

    if (*time_a < *time_b)
    {
        return -1;
    }
    if (*time_a > *time_b)
    {
        return 1;
    }
    return 0;
}

void sort_ctime(ctime *array, size_t count)
{
    if (array == NULL || count == 0)
    {
        return;
    }
    qsort(array, count, sizeof(ctime), cmp_ctime);
}static int cmp_ctime_qsort_adapter(const void *a, const void *b)
{
    return cmp_ctime((const ctime *)a, (const ctime *)b);
}

void sort_ctime(ctime *items, size_t count)
{
    if (items != NULL && count > 1)
    {
        qsort(items, count, sizeof(ctime), cmp_ctime_qsort_adapter);
    }
}#include <stddef.h>
#include <stdlib.h>

static int cmp_ctime(const void *a, const void *b)
{
    const struct item *item_a = (const struct item *)a;
    const struct item *item_b = (const struct item *)b;

    if (item_a->ctime < item_b->ctime)
    {
        return -1;
    }
    if (item_a->ctime > item_b->ctime)
    {
        return 1;
    }
    return 0;
}

void sort_by_ctime(struct item *items, size_t count)
{
    if (items == NULL || count < 2)
    {
        return;
    }
    qsort(items, count, sizeof(*items), cmp_ctime);
}#include <stdlib.h>
#include <stddef.h>
#include <time.h>

// A plausible definition for the type implied by 'ctime' in the macro.
// Using a more descriptive name to avoid conflict with the standard ctime().
typedef struct {
    time_t timestamp;
    const char *file_path; // Example of another relevant data field
} CTimeRecord;

// The comparison function, as named in the macro invocation.
// It is made static as it's a helper for sort_ctime and not for general use.
static int cmp_ctime(const void *a, const void *b)
{
    const CTimeRecord *record_a = (const CTimeRecord *)a;
    const CTimeRecord *record_b = (const CTimeRecord *)b;

    if (record_a->timestamp < record_b->timestamp) {
        return -1;
    }
    if (record_a->timestamp > record_b->timestamp) {
        return 1;
    }
    return 0;
}

// The sorting function generated by the macro.
// Its name is derived from the macro's parameters.
void sort_ctime(CTimeRecord *records, size_t count)
{
    // A sort is not necessary for 0 or 1 elements.
    if (records == NULL || count < 2) {
        return;
    }
    qsort(records, count, sizeof(CTimeRecord), cmp_ctime);
}#include <stdlib.h>

static int cmp_ctime(const void *a, const void *b)
{
    const ctime *elem_a = (const ctime *)a;
    const ctime *elem_b = (const ctime *)b;

    if (elem_a->timestamp < elem_b->timestamp) {
        return -1;
    }
    if (elem_a->timestamp > elem_b->timestamp) {
        return 1;
    }
    return 0;
}

void sort_ctime(ctime *items, size_t count)
{
    if (items == NULL || count == 0) {
        return;
    }
    qsort(items, count, sizeof(ctime), cmp_ctime);
}

ctime *bsearch_ctime(const ctime *key, const ctime *items, size_t count)
{
    if (key == NULL || items == NULL || count == 0) {
        return NULL;
    }
    return (ctime *)bsearch(key, items, count, sizeof(ctime), cmp_ctime);
}int cmp_ctime(const void *p1, const void *p2)
{
    const ctime *val1 = (const ctime *)p1;
    const ctime *val2 = (const ctime *)p2;

    if (*val1 < *val2)
    {
        return -1;
    }

    if (*val1 > *val2)
    {
        return 1;
    }

    return 0;
}static int cmp_ctime(const void *p1, const void *p2)
{
    const struct entry *e1 = *(const struct entry **)p1;
    const struct entry *e2 = *(const struct entry **)p2;

    if (e1->ctime < e2->ctime) {
        return -1;
    }
    if (e1->ctime > e2->ctime) {
        return 1;
    }
    return 0;
}

void sort_by_ctime(struct entry **entries, size_t count)
{
    if (!entries) {
        return;
    }
    qsort(entries, count, sizeof(*entries), cmp_ctime);
}#include <stdlib.h>

int cmp_ctime(const void *a, const void *b);

void sort_by_ctime(void *base, size_t num, size_t size)
{
    if (base != NULL && num > 0)
    {
        qsort(base, num, size, cmp_ctime);
    }
}

const void *search_by_ctime(const void *key, const void *base, size_t num, size_t size)
{
    if (key == NULL || base == NULL || num == 0)
    {
        return NULL;
    }
    return bsearch(key, base, num, size, cmp_ctime);
}
static int cmp_mtime(const void *a, const void *b)
{
    const struct file_info *file_a = *(const struct file_info **)a;
    const struct file_info *file_b = *(const struct file_info **)b;

    if (file_a->mtime < file_b->mtime)
    {
        return -1;
    }
    if (file_a->mtime > file_b->mtime)
    {
        return 1;
    }
    return 0;
}

void sort_by_mtime(struct file_info **files, size_t count)
{
    if (files && count > 1)
    {
        qsort(files, count, sizeof(*files), cmp_mtime);
    }
}static int cmp_mtime(const void *a, const void *b)
{
    const struct file_entry *info_a = *(const struct file_entry **)a;
    const struct file_entry *info_b = *(const struct file_entry **)b;

    if (info_a == NULL) {
        return (info_b == NULL) ? 0 : -1;
    }
    if (info_b == NULL) {
        return 1;
    }

    const struct timespec time_a = info_a->mtime;
    const struct timespec time_b = info_b->mtime;

    if (time_a.tv_sec != time_b.tv_sec) {
        return (time_a.tv_sec > time_b.tv_sec) - (time_a.tv_sec < time_b.tv_sec);
    }

    return (time_a.tv_nsec > time_b.tv_nsec) - (time_a.tv_nsec < time_b.tv_nsec);
}

void sort_by_mtime(struct file_entry **entries, size_t count)
{
    if (entries != NULL && count > 1) {
        qsort(entries, count, sizeof(*entries), cmp_mtime);
    }
}static int cmp_mtime(const void *a, const void *b)
{
    const struct file_info *info_a = *(const struct file_info **)a;
    const struct file_info *info_b = *(const struct file_info **)b;

    if (info_a->mtime < info_b->mtime)
    {
        return -1;
    }

    if (info_a->mtime > info_b->mtime)
    {
        return 1;
    }

    return 0;
}static int cmp_mtime(const void *p1, const void *p2)
{
    const struct entry * const *e1 = p1;
    const struct entry * const *e2 = p2;

    time_t time1 = (*e1)->mtime;
    time_t time2 = (*e2)->mtime;

    if (time1 < time2) {
        return -1;
    }
    if (time1 > time2) {
        return 1;
    }
    return 0;
}

void sort_by_mtime(struct entry **entries, size_t count)
{
    if (entries && count > 1) {
        qsort(entries, count, sizeof(*entries), cmp_mtime);
    }
}static int cmp_mtime(const void *a, const void *b)
{
    const struct file_info * const *entry_a = a;
    const struct file_info * const *entry_b = b;

    const time_t time_a = (*entry_a)->st.st_mtime;
    const time_t time_b = (*entry_b)->st.st_mtime;

    if (time_a < time_b)
    {
        return -1;
    }
    
    if (time_a > time_b)
    {
        return 1;
    }

    return 0;
}

void sort_by_mtime(struct file_info **entries, size_t count)
{
    if (entries == NULL || count < 2)
    {
        return;
    }

    qsort(entries, count, sizeof(*entries), cmp_mtime);
}int cmp_mtime(const void *a, const void *b)
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

    const struct file_info *info_a = (const struct file_info *)a;
    const struct file_info *info_b = (const struct file_info *)b;

    if (info_a->mtime < info_b->mtime) {
        return -1;
    }
    if (info_a->mtime > info_b->mtime) {
        return 1;
    }

    return 0;
}int cmp_mtime(const void *a, const void *b)
{
    const struct file_entry *entry_a = (const struct file_entry *)a;
    const struct file_entry *entry_b = (const struct file_entry *)b;

    if (entry_a->mtime < entry_b->mtime)
    {
        return -1;
    }

    if (entry_a->mtime > entry_b->mtime)
    {
        return 1;
    }

    return 0;
}static int cmp_mtime(const void *a, const void *b)
{
    const struct file_info *info_a = *(const struct file_info **)a;
    const struct file_info *info_b = *(const struct file_info **)b;

    if (info_a->mtime < info_b->mtime)
    {
        return -1;
    }
    if (info_a->mtime > info_b->mtime)
    {
        return 1;
    }
    return 0;
}
static int cmp_atime(const void *p1, const void *p2)
{
    const struct file_entry *entry1 = (const struct file_entry *)p1;
    const struct file_entry *entry2 = (const struct file_entry *)p2;

    if (entry1->atime < entry2->atime) {
        return 1;
    }
    if (entry1->atime > entry2->atime) {
        return -1;
    }
    return 0;
}

void sort_atime(struct file_entry *entries, size_t count)
{
    if (entries != NULL && count > 1) {
        qsort(entries, count, sizeof(*entries), cmp_atime);
    }
}static int cmp_atime(const void *p1, const void *p2)
{
    const struct entry *e1 = (const struct entry *)p1;
    const struct entry *e2 = (const struct entry *)p2;

    if (e1->atime < e2->atime) {
        return -1;
    }
    if (e1->atime > e2->atime) {
        return 1;
    }
    return 0;
}

void sort_by_atime(struct entry *entries, size_t count)
{
    if (entries == NULL || count == 0) {
        return;
    }
    qsort(entries, count, sizeof(*entries), cmp_atime);
}static int cmp_atime(const void *p1, const void *p2)
{
    const struct file_entry *entry1 = *(const struct file_entry **)p1;
    const struct file_entry *entry2 = *(const struct file_entry **)p2;

    if (entry1 == NULL) {
        return (entry2 == NULL) ? 0 : 1;
    }
    if (entry2 == NULL) {
        return -1;
    }

    if (entry1->atime < entry2->atime) {
        return -1;
    }
    if (entry1->atime > entry2->atime) {
        return 1;
    }

    return 0;
}

void sort_by_atime(struct file_entry **entries, size_t count)
{
    if (entries != NULL && count > 1) {
        qsort(entries, count, sizeof(*entries), cmp_atime);
    }
}static int cmp_atime(const void *p1, const void *p2)
{
    const struct file_entry * const *entry1_ptr = p1;
    const struct file_entry * const *entry2_ptr = p2;

    const struct file_entry *e1 = *entry1_ptr;
    const struct file_entry *e2 = *entry2_ptr;

    if (e1->atime < e2->atime) {
        return -1;
    }
    if (e1->atime > e2->atime) {
        return 1;
    }
    return 0;
}

void sort_atime(struct file_entry **entries, size_t count)
{
    if (entries != NULL) {
        qsort(entries, count, sizeof(*entries), cmp_atime);
    }
}#include <stdlib.h>
#include <stddef.h>
#include <time.h>

typedef struct {
    time_t atime;
} item_t;

static int cmp_atime(const void *a, const void *b)
{
    const item_t *item_a = (const item_t *)a;
    const item_t *item_b = (const item_t *)b;

    if (item_a->atime < item_b->atime) {
        return -1;
    }
    if (item_a->atime > item_b->atime) {
        return 1;
    }
    return 0;
}

void sort_by_atime(item_t *items, size_t count)
{
    if (items != NULL && count > 1) {
        qsort(items, count, sizeof(item_t), cmp_atime);
    }
}static int cmp_atime(const void *a, const void *b)
{
    const struct file_item *item_a = *(const struct file_item **)a;
    const struct file_item *item_b = *(const struct file_item **)b;

    if (item_a->atime < item_b->atime) {
        return -1;
    }
    if (item_a->atime > item_b->atime) {
        return 1;
    }
    return 0;
}

void sort_by_atime(struct file_item **items, size_t count)
{
    if (items == NULL) {
        return;
    }
    qsort(items, count, sizeof(*items), cmp_atime);
}#include <stdlib.h>

/*
 * The comparison function, cmp_atime, is assumed to be defined elsewhere
 * with the following signature, compatible with qsort:
 * int cmp_atime(const void *a, const void *b);
 */

static void sort_by_atime(void **items, size_t count)
{
    if (items != NULL && count > 1) {
        qsort(items, count, sizeof(void *), cmp_atime);
    }
}static int cmp_atime_reverse(const void *a, const void *b)
{
    return -cmp_atime(a, b);
}

void sort_by_atime(void **base, size_t count)
{
    if (base != NULL && count > 1)
    {
        qsort(base, count, sizeof(*base), cmp_atime);
    }
}

void sort_by_atime_reverse(void **base, size_t count)
{
    if (base != NULL && count > 1)
    {
        qsort(base, count, sizeof(*base), cmp_atime_reverse);
    }
}
void sort_btime(btime *items, size_t count)
{
    if (items != NULL && count > 1)
    {
        qsort(items, count, sizeof(*items), cmp_btime);
    }
}#include <stdlib.h>

static void sort_btime(btime *items, size_t count)
{
    if (items == NULL || count < 2) {
        return;
    }
    qsort(items, count, sizeof(*items), cmp_btime);
}#include <stdlib.h>

static inline void sort_btime(btime *elements, size_t num_elements)
{
    if (elements != NULL && num_elements > 0) {
        qsort(elements, num_elements, sizeof(*elements), cmp_btime);
    }
}void sort_btime(btime *array, size_t count)
{
    if (count > 0 && array != NULL)
    {
        qsort(array, count, sizeof(*array), cmp_btime);
    }
}static int qsort_btime_compare(const void *a, const void *b)
{
    const btime *elem_a = (const btime *)a;
    const btime *elem_b = (const btime *)b;

    return cmp_btime(elem_a, elem_b);
}

void sort_btime(btime *data, size_t count)
{
    if (data != NULL && count > 0) {
        qsort(data, count, sizeof(*data), qsort_btime_compare);
    }
}void sort_btime(struct btime *items, size_t count)
{
    if (items != NULL && count > 1) {
        qsort(items, count, sizeof(*items), cmp_btime);
    }
}#include <stdlib.h>
#include <time.h>

typedef struct timespec btime_t;

static int cmp_btime(const void *a, const void *b)
{
    const btime_t *const time_a = a;
    const btime_t *const time_b = b;

    if (time_a->tv_sec < time_b->tv_sec) {
        return -1;
    }
    if (time_a->tv_sec > time_b->tv_sec) {
        return 1;
    }

    if (time_a->tv_nsec < time_b->tv_nsec) {
        return -1;
    }
    if (time_a->tv_nsec > time_b->tv_nsec) {
        return 1;
    }

    return 0;
}

void sort_btime(btime_t *base, size_t count)
{
    if (base != NULL && count > 1) {
        qsort(base, count, sizeof(*base), cmp_btime);
    }
}static int btime_qsort_adapter(const void *p1, const void *p2)
{
    const btime_t *btime1 = (const btime_t *)p1;
    const btime_t *btime2 = (const btime_t *)p2;
    return cmp_btime(btime1, btime2);
}

void sort_btime_array(btime_t *array, size_t count)
{
    if (array == NULL || count < 2)
    {
        return;
    }
    qsort(array, count, sizeof(btime_t), btime_qsort_adapter);
}
#include <stddef.h>
#include <stdlib.h>

int cmp_size(const void *a, const void *b)
{
    const size val_a = *(const size *)a;
    const size val_b = *(const size *)b;

    if (val_a < val_b)
    {
        return -1;
    }
    
    if (val_a > val_b)
    {
        return 1;
    }

    return 0;
}

void sort_size(size *array, size_t count)
{
    if (array == NULL || count == 0)
    {
        return;
    }
    
    qsort(array, count, sizeof(*array), cmp_size);
}#include <stdlib.h>

static int cmp_size(const void *a, const void *b)
{
    const size *val_a = (const size *)a;
    const size *val_b = (const size *)b;

    if (*val_a < *val_b)
    {
        return -1;
    }
    if (*val_a > *val_b)
    {
        return 1;
    }
    return 0;
}

void sort_size_array(size *array, size_t count)
{
    if (array == NULL || count <= 1)
    {
        return;
    }
    qsort(array, count, sizeof(size), cmp_size);
}#include <stddef.h>
#include <stdlib.h>

#define CONCAT_IMPL(x, y) x##y
#define CONCAT(x, y) CONCAT_IMPL(x, y)

#define DEFINE_SORT_FUNCTIONS(type, cmp_func)                                \
    void CONCAT(sort_, type)(type *array, size_t count)                      \
    {                                                                        \
        if (array)                                                           \
        {                                                                    \
            qsort(array, count, sizeof(type), cmp_func);                     \
        }                                                                    \
    }#include <stdlib.h>

static int cmp_size(const void *a, const void *b)
{
    const size_t val1 = *(const size_t *)a;
    const size_t val2 = *(const size_t *)b;

    return (val1 > val2) - (val1 < val2);
}

void sort_size(size_t *data, size_t count)
{
    if (data == NULL || count < 2)
    {
        return;
    }
    qsort(data, count, sizeof(*data), cmp_size);
}#include <stddef.h>
#include <stdlib.h>

static int cmp_size(const void *a, const void *b)
{
    const size_t val_a = *(const size_t *)a;
    const size_t val_b = *(const size_t *)b;

    if (val_a < val_b) {
        return -1;
    }
    if (val_a > val_b) {
        return 1;
    }
    return 0;
}

void sort_size_array(size_t *array, size_t count)
{
    if (array != NULL && count > 1) {
        qsort(array, count, sizeof(size_t), cmp_size);
    }
}static int cmp_size(const void *a, const void *b)
{
    const struct Record *rec_a = (const struct Record *)a;
    const struct Record *rec_b = (const struct Record *)b;

    if (rec_a->size < rec_b->size)
    {
        return -1;
    }
    
    if (rec_a->size > rec_b->size)
    {
        return 1;
    }

    return 0;
}#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

static int cmp_size(const void *p1, const void *p2)
{
    const size_t val1 = *(const size_t *)p1;
    const size_t val2 = *(const size_t *)p2;

    if (val1 < val2)
    {
        return -1;
    }
    if (val1 > val2)
    {
        return 1;
    }
    return 0;
}

void sort_size(size_t *array, size_t count)
{
    if (array == NULL || count == 0)
    {
        return;
    }

    if (count > (SIZE_MAX / sizeof(*array)))
    {
        return;
    }

    qsort(array, count, sizeof(*array), cmp_size);
}#include <stdlib.h>

struct item_to_sort {
    size_t size;
};

static int cmp_size(const void *a, const void *b)
{
    const struct item_to_sort *item_a = (const struct item_to_sort *)a;
    const struct item_to_sort *item_b = (const struct item_to_sort *)b;

    if (item_a->size < item_b->size) {
        return -1;
    }
    if (item_a->size > item_b->size) {
        return 1;
    }
    return 0;
}

void sort_by_size(struct item_to_sort *items, size_t count)
{
    if (items == NULL || count < 2) {
        return;
    }
    qsort(items, count, sizeof(struct item_to_sort), cmp_size);
}
#include <stdlib.h>

static int name_qsort_adapter(const void *a, const void *b)
{
    const name *item_a = (const name *)a;
    const name *item_b = (const name *)b;
    return cmp_name(item_a, item_b);
}

void sort_name_array(name *array, size_t count)
{
    if (array == NULL || count < 2)
    {
        return;
    }
    qsort(array, count, sizeof(name), name_qsort_adapter);
}#include <stdlib.h>
#include <stddef.h>

typedef struct element_t {
    void *placeholder;
} element_t;

extern int cmp_name(const void *a, const void *b);

void sort_by_name(element_t *elements, size_t count)
{
    if (elements != NULL && count >= 2)
    {
        qsort(elements, count, sizeof(*elements), cmp_name);
    }
}#include <stdlib.h>

struct name;
int cmp_name(const void *a, const void *b);

static inline void sort_name_array(struct name *array, size_t count)
{
    if (array != NULL && count > 1) {
        qsort(array, count, sizeof(struct name), cmp_name);
    }
}#include <stdlib.h>

static int compare_name_qsort_adapter(const void *a, const void *b)
{
    const name *item_a = (const name *)a;
    const name *item_b = (const name *)b;
    return cmp_name(item_a, item_b);
}

void sort_name_items(name *items, size_t count)
{
    if (items == NULL || count < 2) {
        return;
    }
    qsort(items, count, sizeof(name), compare_name_qsort_adapter);
}#include <stdlib.h>

void sort_name(name_t *items, size_t count)
{
    if (items == NULL || count < 2)
    {
        return;
    }

    qsort(items, count, sizeof(name_t), cmp_name);
}#include <stdlib.h>

struct name;
int cmp_name(const void *a, const void *b);

void sort_name(struct name *items, size_t count)
{
    if (items != NULL && count > 0) {
        qsort(items, count, sizeof(struct name), cmp_name);
    }
}void sort_by_name(void *base, size_t num, size_t size)
{
    // It is assumed that a comparator function `cmp_name` with the signature
    // int cmp_name(const void *, const void *) is available in this scope.
    if (base != NULL && size > 0) {
        qsort(base, num, size, cmp_name);
    }
}#include <stdlib.h>
#include <stddef.h>

// The type 'name_t' is inferred from the 'name' argument to the original macro.
// It must be defined appropriately elsewhere in the project.
typedef struct name_t name_t;

// The comparison function 'cmp_name' is passed from the original macro.
// It must be defined elsewhere with a signature compatible with qsort.
extern int cmp_name(const void *a, const void *b);

static inline void sort_by_name(name_t *array, size_t count)
{
    if (array != NULL) {
        qsort(array, count, sizeof(*array), cmp_name);
    }
}
static int compare_extensions_for_qsort(const void *a, const void *b)
{
    const extension * const *ext_a = (const extension * const *)a;
    const extension * const *ext_b = (const extension * const *)b;

    return cmp_extension(*ext_a, *ext_b);
}

void sort_extensions(extension **extensions, size_t count)
{
    if (extensions != NULL && count > 1)
    {
        qsort(extensions, count, sizeof(*extensions), compare_extensions_for_qsort);
    }
}static int extension_qsort_compare(const void *a, const void *b)
{
    const extension *ext_a = *(const extension **)a;
    const extension *ext_b = *(const extension **)b;
    return cmp_extension(ext_a, ext_b);
}

void sort_extensions(extension **list, size_t count)
{
    if (list == NULL || count < 2) {
        return;
    }
    qsort(list, count, sizeof(*list), extension_qsort_compare);
}void sort_extension(extension *items, size_t count)
{
    if (items != NULL && count > 0)
    {
        qsort(items, count, sizeof(*items), cmp_extension);
    }
}#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>

int cmp_extension(const void *a, const void *b);

static void sort_extension(void **list, size_t count)
{
    if (list != NULL && count > 1) {
        qsort(list, count, sizeof(void *), cmp_extension);
    }
}

static bool add_and_sort_extension(void **list, size_t *current_count, size_t capacity, void *item_to_add)
{
    if (list == NULL || current_count == NULL || item_to_add == NULL) {
        return false;
    }

    if (*current_count >= capacity) {
        return false;
    }

    list[*current_count] = item_to_add;
    (*current_count)++;

    sort_extension(list, *current_count);

    return true;
}static int cmp_extension(const void *a, const void *b)
{
    const struct file_info *info_a = (const struct file_info *)a;
    const struct file_info *info_b = (const struct file_info *)b;

    if (info_a == info_b) {
        return 0;
    }
    if (info_a == NULL) {
        return -1;
    }
    if (info_b == NULL) {
        return 1;
    }

    const char *ext_a = info_a->extension;
    const char *ext_b = info_b->extension;

    if (ext_a == ext_b) {
        return 0;
    }
    if (ext_a == NULL) {
        return -1;
    }
    if (ext_b == NULL) {
        return 1;
    }

    return strcmp(ext_a, ext_b);
}

static void sort_by_extension(struct file_info *files, size_t count)
{
    if (files != NULL && count > 1) {
        qsort(files, count, sizeof(*files), cmp_extension);
    }
}void sort_extensions(struct extension **extensions, size_t count)
{
    if (extensions != NULL && count > 1)
    {
        qsort(extensions, count, sizeof(*extensions), cmp_extension);
    }
}void sort_extensions(struct extension **extensions, size_t count)
{
    if (extensions != NULL && count > 1) {
        qsort(extensions, count, sizeof(*extensions), cmp_extension);
    }
}#include <stdlib.h>
#include <string.h>

struct extension {
    char *name;
};

static int cmp_extension(const void *a, const void *b)
{
    const struct extension *ext_a = *(const struct extension **)a;
    const struct extension *ext_b = *(const struct extension **)b;

    if (!ext_a || !ext_a->name) {
        return (!ext_b || !ext_b->name) ? 0 : -1;
    }
    if (!ext_b || !ext_b->name) {
        return 1;
    }

    return strcmp(ext_a->name, ext_b->name);
}

void sort_extensions(struct extension **extensions, size_t count)
{
    if (extensions && count > 1) {
        qsort(extensions, count, sizeof(struct extension *), cmp_extension);
    }
}
#include <stdlib.h>

void sort_width_array(width *array_to_sort, size_t num_elements)
{
    if (array_to_sort == NULL || num_elements < 2)
    {
        return;
    }
    qsort(array_to_sort, num_elements, sizeof(*array_to_sort), cmp_width);
}#include <stdlib.h>
#include <stddef.h>

typedef struct
{
    int width;
} item_t;

static int cmp_width(const void *a, const void *b)
{
    const item_t *item_a = (const item_t *)a;
    const item_t *item_b = (const item_t *)b;

    if (item_a->width < item_b->width)
    {
        return -1;
    }
    
    if (item_a->width > item_b->width)
    {
        return 1;
    }

    return 0;
}

void sort_by_width(item_t *items, size_t count)
{
    if (items != NULL && count > 0)
    {
        qsort(items, count, sizeof(*items), cmp_width);
    }
}#include <stdlib.h>
#include <stddef.h>

typedef struct Item
{
    int width;
} Item;

static int cmp_width(const void *a, const void *b)
{
    const Item *item_a = (const Item *)a;
    const Item *item_b = (const Item *)b;

    if (item_a->width < item_b->width)
    {
        return -1;
    }
    if (item_a->width > item_b->width)
    {
        return 1;
    }
    return 0;
}

void sort_by_width(Item *items, size_t count)
{
    if (items != NULL && count > 1)
    {
        qsort(items, count, sizeof(Item), cmp_width);
    }
}static int compare_width(const void *a, const void *b)
{
    const width *elem1 = (const width *)a;
    const width *elem2 = (const width *)b;

    if (elem1->value < elem2->value)
    {
        return -1;
    }
    if (elem1->value > elem2->value)
    {
        return 1;
    }
    return 0;
}

void sort_width(width *array, size_t count)
{
    if (array == NULL || count < 2)
    {
        return;
    }
    qsort(array, count, sizeof(width), compare_width);
}void sort_width(width *array, size_t count)
{
    if (array != NULL)
    {
        qsort(array, count, sizeof(*array), cmp_width);
    }
}void sort_by_width(void *base, size_t num, size_t size)
{
    if (base != NULL && num > 0 && size > 0)
    {
        qsort(base, num, size, cmp_width);
    }
}#include <stdlib.h>
#include <stdbool.h>

void sort_width(Item *items, size_t count)
{
    if (items != NULL && count > 1) {
        qsort(items, count, sizeof(Item), cmp_width);
    }
}

bool is_width_sorted(const Item *items, size_t count)
{
    if (count < 2) {
        return true;
    }
    if (items == NULL) {
        return false;
    }

    for (size_t i = 0; i < count - 1; ++i) {
        if (cmp_width(&items[i], &items[i + 1]) > 0) {
            return false;
        }
    }

    return true;
}#include <stdlib.h>

/* The type 'widget_t' and the comparison function 'cmp_width' are assumed
   to be defined elsewhere in the codebase. 'widget_t' is a placeholder
   for the actual element type being sorted. */
void sort_width(widget_t *base, size_t count)
{
    if (base == NULL) {
        return;
    }
    qsort(base, count, sizeof(widget_t), cmp_width);
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
  int diff = filevercmp (a->name, b->name);
  if (diff != 0)
  {
    return diff;
  }
  return strcmp (a->name, b->name);
}

static int xstrcoll_version(const V a, const V b)
{
    return cmp_version(a, b);
}
static int compare_versions_reverse(const void *a, const void *b)
{
    return cmp_version(b, a);
}
static int
xstrcoll_df_version (const V a, const V b)
{
  return dirfirst_check (a, b, xstrcoll_version);
}
static inline int
rev_xstrcoll_df_version (V left, V right)
{
  return dirfirst_check (left, right, rev_xstrcoll_version);
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
  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      sorted_file[i] = &cwd_file[i];
    }
}

/* Cache values based on attributes global to all files.  */

static void
update_current_files_info (void)
{
  const bool is_multi_column_format = (format == many_per_line
                                       || format == horizontal);
  const bool needs_name_width = (sort_type == sort_width
                                 || (line_length && is_multi_column_format));

  if (!needs_name_width)
    {
      return;
    }

  for (idx_t i = 0; i < cwd_n_used; i++)
    {
      struct fileinfo *f = sorted_file[i];
      if (f)
        {
          f->width = fileinfo_name_width (f);
        }
    }
}

/* Sort the files now in the table.  */

static void
sort_files (void)
{
  size_t required_capacity = cwd_n_used + (cwd_n_used >> 1);
  if (sorted_file_alloc < required_capacity)
    {
      free (sorted_file);
      size_t new_capacity = 3 * cwd_n_used;
      sorted_file = xinmalloc (new_capacity, sizeof (*sorted_file));
      sorted_file_alloc = new_capacity;
    }

  initialize_ordering_vector ();
  update_current_files_info ();

  if (sort_type == sort_none)
    return;

  bool use_strcmp;
  if (!setjmp (failed_strcoll))
    {
      use_strcmp = false;
    }
  else
    {
      use_strcmp = true;
      affirm (sort_type != sort_version);
      initialize_ordering_vector ();
    }

  int sort_key = sort_type;
  if (sort_type == sort_time)
    {
      sort_key += time_type;
    }

  mpsort ((void const **) sorted_file, cwd_n_used,
          sort_functions[sort_key]
                        [use_strcmp]
                        [sort_reverse]
                        [directories_first]);
}

/* List all the files now in the table.  */

static void
print_current_files (void)
{
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
    case horizontal:
      if (line_length)
        {
          if (format == many_per_line)
            print_many_per_line ();
          else
            print_horizontal ();
        }
      else
        {
          print_with_separator (' ');
        }
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

    default:
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
  if (!tm || tm->tm_mon < 0 || tm->tm_mon > 11)
    {
      if (size > 0 && buf)
        {
          *buf = '\0';
        }
      return 0;
    }

  char const *nfmt;
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
      char buf[TIME_STAMP_LEN_MAXIMUM + 1];

      if (localtime_rz (localtz, &epoch, &tm))
        {
          size_t len = align_nstrftime (buf, sizeof buf, false,
                                        &tm, localtz, 0);
          if (len != 0)
            {
              int w = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
              if (w >= 0)
                {
                  calculated_width = w;
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
  if (!name)
    {
      dired_pos += printf ("%*ju ", width, id);
      return;
    }

  dired_outstring (name);

  int name_width = mbswidth (name, MBSWIDTH_FLAGS);
  int padding = 0;

  if (name_width >= 0 && name_width < width)
    {
      padding = width - name_width;
    }

  for (int i = 0; i < padding; i++)
    {
      dired_outbyte (' ');
    }
  dired_outbyte (' ');
}

/* Print the name or id of the user with id U, using a print width of
   WIDTH.  */

static void
format_user (uid_t u, int width, bool stat_ok)
{
    const char *user_name;

    if (!stat_ok)
    {
        user_name = "?";
    }
    else if (numeric_ids)
    {
        user_name = NULL;
    }
    else
    {
        user_name = getuser (u);
    }

    format_user_or_group (user_name, u, width);
}

/* Likewise, for groups.  */

static void
format_group (gid_t g, int width, bool stat_ok)
{
  void *group_info;

  if (!stat_ok)
  {
    group_info = "?";
  }
  else if (numeric_ids)
  {
    group_info = NULL;
  }
  else
  {
    group_info = getgroup (g);
  }

  format_user_or_group (group_info, g, width);
}

/* Return the number of columns that format_user_or_group will print,
   or -1 if unknown.  */

static int
format_user_or_group_width (char const *name, uintmax_t id)
{
  int width;

  if (name)
    {
      width = mbswidth (name, MBSWIDTH_FLAGS);
    }
  else
    {
      width = snprintf (NULL, 0, "%ju", id);
    }

  return (width < 0) ? 0 : width;
}

/* Return the number of columns that format_user will print,
   or -1 if unknown.  */

static int
format_user_width (uid_t u)
{
  void *user_data = NULL;

  if (!numeric_ids)
    {
      user_data = getuser (u);
    }

  return format_user_or_group_width (user_data, u);
}

/* Likewise, for groups.  */

static int
format_group_width (gid_t g)
{
  const struct group *grp = NULL;

  if (!numeric_ids)
    {
      grp = getgroup (g);
    }

  return format_user_or_group_width (grp, g);
}

/* Return a pointer to a formatted version of F->stat.st_ino,
   possibly using buffer, which must be at least
   INT_BUFSIZE_BOUND (uintmax_t) bytes.  */
static const char *
format_inode (char buf[INT_BUFSIZE_BOUND (uintmax_t)],
              const struct fileinfo *f)
{
  if (f->stat_ok && f->stat.st_ino != NOT_AN_INODE_NUMBER)
    {
      return umaxtostr (f->stat.st_ino, buf);
    }
  return "?";
}

/* Print information about F in long format.  */
static void
format_mode_string (const struct fileinfo *f, char *modebuf)
{
  if (f->stat_ok)
    filemodestring (&f->stat, modebuf);
  else
    {
      modebuf[0] = filetype_letter[f->filetype];
      memset (modebuf + 1, '?', 10);
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

static struct timespec
get_file_timespec (const struct fileinfo *f, bool *btime_ok)
{
  *btime_ok = true;
  if (!f->stat_ok)
    {
      *btime_ok = false;
      return (struct timespec) { 0, 0 };
    }

  switch (time_type)
    {
    case time_ctime:
      return get_stat_ctime (&f->stat);
    case time_mtime:
      return get_stat_mtime (&f->stat);
    case time_atime:
      return get_stat_atime (&f->stat);
    case time_btime:
      {
        struct timespec ts = get_stat_btime (&f->stat);
        if (ts.tv_sec == -1 && ts.tv_nsec == -1)
          *btime_ok = false;
        return ts;
      }
    default:
      unreachable ();
    }
}

static char *
append_inode (char *p, const struct fileinfo *f)
{
  if (print_inode)
    {
      char hbuf[INT_BUFSIZE_BOUND (uintmax_t)];
      p += sprintf (p, "%*s ", inode_number_width, format_inode (hbuf, f));
    }
  return p;
}

static char *
append_blocks (char *p, const struct fileinfo *f)
{
  if (print_block_size)
    {
      char hbuf[LONGEST_HUMAN_READABLE + 1];
      const char *blocks =
        !f->stat_ok
        ? "?"
        : human_readable (STP_NBLOCKS (&f->stat), hbuf, human_output_opts,
                          ST_NBLOCKSIZE, output_block_size);
      p += sprintf (p, "%*s ", block_size_width, blocks);
    }
  return p;
}

static char *
append_mode_and_links (char *p, const struct fileinfo *f, const char *modebuf)
{
  char hbuf[INT_BUFSIZE_BOUND (uintmax_t)];
  const char *nlink_str =
    !f->stat_ok ? "?" : umaxtostr (f->stat.st_nlink, hbuf);
  p += sprintf (p, "%s %*s ", modebuf, nlink_width, nlink_str);
  return p;
}

static void
print_owner_info (const struct fileinfo *f)
{
  if (print_owner)
    format_user (f->stat.st_uid, owner_width, f->stat_ok);
  if (print_group)
    format_group (f->stat.st_gid, group_width, f->stat_ok);
  if (print_author)
    format_user (f->stat.st_author, author_width, f->stat_ok);
  if (print_scontext)
    format_user_or_group (f->scontext, 0, scontext_width);
}

static char *
append_device_numbers (char *p, const struct stat *st)
{
  char majorbuf[INT_BUFSIZE_BOUND (uintmax_t)];
  char minorbuf[INT_BUFSIZE_BOUND (uintmax_t)];
  int blanks_width =
    (file_size_width -
     (major_device_number_width + 2 + minor_device_number_width));
  p += sprintf (p, "%*s, %*s ",
                major_device_number_width + MAX (0, blanks_width),
                umaxtostr (major (st->st_rdev), majorbuf),
                minor_device_number_width,
                umaxtostr (minor (st->st_rdev), minorbuf));
  return p;
}

static char *
append_file_size (char *p, const struct stat *st, bool stat_ok)
{
  char hbuf[LONGEST_HUMAN_READABLE + 1];
  const char *size =
    !stat_ok
    ? "?"
    : human_readable (unsigned_file_size (st->st_size),
                      hbuf, file_human_output_opts, 1,
                      file_output_block_size);
  p += sprintf (p, "%*s ", file_size_width, size);
  return p;
}

static char *
append_size_or_dev (char *p, const struct fileinfo *f)
{
  if (f->stat_ok
      && (S_ISCHR (f->stat.st_mode) || S_ISBLK (f->stat.st_mode)))
    return append_device_numbers (p, &f->stat);
  else
    return append_file_size (p, &f->stat, f->stat_ok);
}

static char *
append_time (char *p, bool stat_ok, const struct timespec *when, bool time_ok)
{
  size_t s = 0;
  struct tm when_local;
  static const long int half_year_in_seconds = 31556952L / 2;

  if (stat_ok && time_ok &&
      localtime_rz (localtz, &when->tv_sec, &when_local))
    {
      struct timespec six_months_ago;

      if (timespec_cmp (current_time, *when) < 0)
        gettime (&current_time);

      six_months_ago.tv_sec = current_time.tv_sec - half_year_in_seconds;
      six_months_ago.tv_nsec = current_time.tv_nsec;

      bool recent = (timespec_cmp (six_months_ago, *when) < 0
                     && timespec_cmp (*when, current_time) < 0);

      s = align_nstrftime (p, TIME_STAMP_LEN_MAXIMUM + 1, recent,
                           &when_local, localtz, when->tv_nsec);
    }

  if (s > 0)
    {
      p += s;
    }
  else
    {
      char hbuf[INT_BUFSIZE_BOUND (intmax_t)];
      const char *t_str = (!stat_ok || !time_ok)
                        ? "?"
                        : timetostr (when->tv_sec, hbuf);
      p += sprintf (p, "%*s", long_time_expected_width (), t_str);
    }

  *p++ = ' ';
  return p;
}

static void
print_name_and_link (const struct fileinfo *f, size_t prefix_len)
{
  size_t w = print_name_with_quoting (f, false, &dired_obstack, prefix_len);

  if (f->filetype == symbolic_link && f->linkname)
    {
      dired_outstring (" -> ");
      print_name_with_quoting (f, true, NULL, prefix_len + w + 4);
      if (indicator_style != none)
        print_type_indicator (true, f->linkmode, unknown);
    }
  else if (indicator_style != none)
    {
      print_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
    }
}

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
  bool btime_ok;

  format_mode_string (f, modebuf);
  struct timespec when_timespec = get_file_timespec (f, &btime_ok);

  p = append_inode (p, f);
  p = append_blocks (p, f);
  p = append_mode_and_links (p, f, modebuf);

  dired_indent ();

  if (print_owner || print_group || print_author || print_scontext)
    {
      dired_outbuf (buf, p - buf);
      print_owner_info (f);
      p = buf;
    }

  p = append_size_or_dev (p, f);
  p = append_time (p, f->stat_ok, &when_timespec, btime_ok);

  dired_outbuf (buf, p - buf);
  print_name_and_link (f, p - buf);
}

/* Write to *BUF a quoted representation of the file name NAME, if non-null,
   using OPTIONS to control quoting.  *BUF is set to NAME if no quoting
   is required.  *BUF is allocated if more space required (and the original
   *BUF is not deallocated).
   Store the number of screen columns occupied by NAME's quoted
   representation into WIDTH, if non-null.
   Store into PAD whether an initial space is needed for padding.
   Return the number of bytes in *BUF.  */

static bool
is_safe_char_for_quoting (unsigned char c)
{
  if (isalnum (c))
    return true;

  return strchr (" !\"#%&'()*+,-./:;<=>?[\\]^_{|}~", c) != NULL;
}

static int
sanitize_multibyte_sequence (char const **p_in, char const *plimit, char **q_out)
{
  char const *p = *p_in;
  char *q = *q_out;
  mbstate_t mbstate;
  int sequence_width = 1;

  mbszero (&mbstate);
  do
    {
      char32_t wc;
      size_t bytes = mbrtoc32 (&wc, p, plimit - p, &mbstate);

      if (bytes == (size_t) -1 || bytes == (size_t) -2)
        {
          *q++ = '?';
          p = (bytes == (size_t) -1) ? p + 1 : plimit;
          break;
        }

      if (bytes == 0)
        bytes = 1;

      int w = c32width (wc);
      if (w >= 0)
        {
          memcpy (q, p, bytes);
          q += bytes;
          p += bytes;
          sequence_width = w;
        }
      else
        {
          *q++ = '?';
          p += bytes;
        }
    }
  while (!mbsinit (&mbstate));

  *p_in = p;
  *q_out = q;
  return sequence_width;
}

static size_t
count_printable_sb (char const *s, size_t n)
{
  size_t count = 0;
  for (size_t i = 0; i < n; i++)
    {
      if (isprint (to_uchar (s[i])))
        count++;
    }
  return count;
}

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
        {
          char *q = buf;
          char const *p = buf;
          char const *plimit = buf + len;

          while (p < plimit)
            {
              if (is_safe_char_for_quoting (to_uchar (*p)))
                {
                  *q++ = *p++;
                  displayed_width++;
                }
              else
                {
                  displayed_width +=
                    sanitize_multibyte_sequence (&p, plimit, &q);
                }
            }
          len = q - buf;
        }
      else
        {
          for (size_t i = 0; i < len; i++)
            {
              if (!isprint (to_uchar (buf[i])))
                buf[i] = '?';
            }
          displayed_width = len;
        }
    }
  else if (width != nullptr)
    {
      if (MB_CUR_MAX > 1)
        {
          displayed_width = mbsnwidth (buf, len, MBSWIDTH_FLAGS);
          displayed_width = MAX (0, displayed_width);
        }
      else
        {
          displayed_width = count_printable_sb (buf, len);
        }
    }

  *pad = (align_variable_outer_quotes && cwd_some_quoted && !quoted);

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
  size_t width = 0;
  bool pad = false;

  quote_name_buf (&buf, sizeof smallbuf, name, options,
                  needs_general_quoting, &width, &pad);

  if (buf != smallbuf && buf != name)
    {
      free (buf);
    }

  return width + pad;
}

/* %XX escape any input out of range as defined in RFC3986,
   and also if PATH, convert all path separators to '/'.  */
static char *
file_escape (char const *str, bool path)
{
  char *esc = xnmalloc (3, strlen (str) + 1);
  char *p = esc;
  static const char hex_digits[] = "0123456789abcdef";

  for (; *str; str++)
    {
      unsigned char c = *str;

      if (path && ISSLASH (c))
        {
          *p++ = '/';
        }
      else if (RFC3986[c])
        {
          *p++ = c;
        }
      else
        {
          *p++ = '%';
          *p++ = hex_digits[c >> 4];
          *p++ = hex_digits[c & 0x0F];
        }
    }

  *p = '\0';
  return esc;
}

static void
print_hyperlinked_name (char const *buf, size_t len, char const *absolute_name,
                        bool skip_quotes)
{
  if (skip_quotes)
    putchar (*buf);

  char *h = file_escape (hostname, false);
  char *n = file_escape (absolute_name, true);
  printf ("\033]8;;file://%s%s%s\a", h, *n == '/' ? "" : "/", n);
  free (h);
  free (n);

  fwrite (buf + skip_quotes, 1, len - (skip_quotes * 2), stdout);

  fputs ("\033]8;;\a", stdout);

  if (skip_quotes)
    putchar (buf[len - 1]);
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

  len = quote_name_buf (&buf, sizeof smallbuf, (char *) name, options,
                        needs_general_quoting, NULL, &pad);

  if (pad && allow_pad)
    dired_outbyte (' ');

  if (color)
    print_color_indicator (color);

  bool const skip_quotes = absolute_name && align_variable_outer_quotes
                           && cwd_some_quoted && !pad;

  if (stack)
    push_current_dired_pos (stack);

  if (absolute_name)
    print_hyperlinked_name (buf, len, absolute_name, skip_quotes);
  else
    fwrite (buf, 1, len, stdout);

  dired_pos += len;

  if (stack)
    push_current_dired_pos (stack);

  if (buf != smallbuf && buf != name)
    free (buf);

  return len + pad;
}

static size_t
print_name_with_quoting (const struct fileinfo *f,
                         bool symlink_target,
                         struct obstack *stack,
                         size_t start_col)
{
  char const *name = symlink_target ? f->linkname : f->name;
  const struct bin_str *color = print_with_color
                                ? get_color_indicator (f, symlink_target)
                                : NULL;

  size_t len = quote_name (name, filename_quoting_options, f->quoted,
                           color, !symlink_target, stack, f->absolute_name);

  process_signals ();

  bool color_is_active = print_with_color && (color || is_colored (C_NORM));
  if (!color_is_active)
    {
      return len;
    }

  prep_non_filename_text ();

  if (line_length > 0)
    {
      size_t start_line = start_col / line_length;
      size_t end_line = (start_col + len - 1) / line_length;
      bool name_wraps_lines = (start_line != end_line);

      if (name_wraps_lines)
        {
          put_indicator (&color_indicator[C_CLR_TO_EOL]);
        }
    }

  return len;
}

static void
put_fallback_end_indicator (void)
{
  put_indicator (&color_indicator[C_LEFT]);
  put_indicator (&color_indicator[C_RESET]);
  put_indicator (&color_indicator[C_RIGHT]);
}

static void
prep_non_filename_text (void)
{
  if (color_indicator[C_END].string)
    {
      put_indicator (&color_indicator[C_END]);
    }
  else
    {
      put_fallback_end_indicator ();
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
    {
      int width = (format == with_commas) ? 0 : inode_number_width;
      printf ("%*s ", width, format_inode (buf, f));
    }

  if (print_block_size)
    {
      const char *blocks_str = f->stat_ok
        ? human_readable (STP_NBLOCKS (&f->stat), buf, human_output_opts,
                          ST_NBLOCKSIZE, output_block_size)
        : "?";

      int pad = 0;
      if (format != with_commas)
        {
          int blocks_width = mbswidth (blocks_str, MBSWIDTH_FLAGS);
          if (blocks_width >= 0 && block_size_width > blocks_width)
            {
              pad = block_size_width - blocks_width;
            }
        }
      printf ("%*s%s ", pad, "", blocks_str);
    }

  if (print_scontext)
    {
      int width = (format == with_commas) ? 0 : scontext_width;
      printf ("%*s ", width, f->scontext);
    }

  size_t width = print_name_with_quoting (f, false, NULL, start_col);

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
  if (stat_ok)
    {
      if (S_ISREG (mode))
        {
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
  else
    {
      if (type == directory || type == arg_directory)
        return '/';

      if (indicator_style == slash)
        return 0;

      switch (type)
        {
          case symbolic_link:
            return '@';
          case fifo:
            return '|';
          case sock:
            return '=';
          default:
            return 0;
        }
    }
}

static bool
print_type_indicator (bool stat_ok, mode_t mode, enum filetype type)
{
  const char c = get_type_indicator (stat_ok, mode, type);
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
ATTRIBUTE_PURE
static enum indicator_no
get_type_from_filetype (enum filetype type)
{
  static enum indicator_no const filetype_indicator[] =
    {
      C_ORPHAN, C_FIFO, C_CHR, C_DIR, C_BLK, C_FILE,
      C_LINK, C_SOCK, C_FILE, C_DIR
    };
  static_assert (ARRAY_CARDINALITY (filetype_indicator)
                 == filetype_cardinality);
  return filetype_indicator[type];
}

ATTRIBUTE_PURE
static enum indicator_no
get_indicator_type_from_mode (const struct fileinfo *f, mode_t mode)
{
  if (S_ISREG (mode))
    {
      if ((mode & S_ISUID) && is_colored (C_SETUID))
        return C_SETUID;
      if ((mode & S_ISGID) && is_colored (C_SETGID))
        return C_SETGID;
      if (f->has_capability)
        return C_CAP;
      if ((mode & S_IXUGO) && is_colored (C_EXEC))
        return C_EXEC;
      if ((1 < f->stat.st_nlink) && is_colored (C_MULTIHARDLINK))
        return C_MULTIHARDLINK;
      return C_FILE;
    }
  if (S_ISDIR (mode))
    {
      if ((mode & S_ISVTX) && (mode & S_IWOTH)
          && is_colored (C_STICKY_OTHER_WRITABLE))
        return C_STICKY_OTHER_WRITABLE;
      if ((mode & S_IWOTH) && is_colored (C_OTHER_WRITABLE))
        return C_OTHER_WRITABLE;
      if ((mode & S_ISVTX) && is_colored (C_STICKY))
        return C_STICKY;
      return C_DIR;
    }
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

ATTRIBUTE_PURE
static struct color_ext_type *
find_color_extension (const char *name)
{
  size_t len = strlen (name);

  for (struct color_ext_type *ext = color_ext_list; ext != NULL;
       ext = ext->next)
    {
      if (ext->ext.len > len)
        continue;

      const char *suffix = name + len - ext->ext.len;
      if (ext->exact_match)
        {
          if (memcmp (suffix, ext->ext.string, ext->ext.len) == 0)
            return ext;
        }
      else
        {
          if (c_strncasecmp (suffix, ext->ext.string, ext->ext.len) == 0)
            return ext;
        }
    }
  return NULL;
}

ATTRIBUTE_PURE
static const struct bin_str*
get_color_indicator (const struct fileinfo *f, bool symlink_target)
{
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

  enum indicator_no type;

  if (linkok == -1 && is_colored (C_MISSING))
    type = C_MISSING;
  else if (!f->stat_ok)
    type = get_type_from_filetype (f->filetype);
  else
    type = get_indicator_type_from_mode (f, mode);

  struct color_ext_type *ext = NULL;
  if (type == C_FILE)
    ext = find_color_extension (name);

  if (type == C_LINK && !linkok
      && (color_symlink_as_referent || is_colored (C_ORPHAN)))
    {
      type = C_ORPHAN;
    }

  const struct bin_str *s =
    ext ? &(ext->seq) : &color_indicator[type];

  return s->string ? s : NULL;
}

/* Output a color indicator (which may contain nulls).  */
static void
ensure_color_initialized (void)
{
  if (used_color)
    return;

  used_color = true;

  if (tcgetpgrp (STDOUT_FILENO) != -1)
    {
      signal_init ();
    }

  prep_non_filename_text ();
}

static void
put_indicator (const struct bin_str *ind)
{
  ensure_color_initialized ();

  if (fwrite (ind->string, ind->len, 1, stdout) != 1)
    {
      if (ferror (stdout))
        {
          perror ("write error");
          exit (EXIT_FAILURE);
        }
    }
}

static size_t
get_inode_width (const struct fileinfo *f, char *buf)
{
  if (format == with_commas)
    return strlen (umaxtostr (f->stat.st_ino, buf));

  return inode_number_width;
}

static size_t
get_block_size_width (const struct fileinfo *f, char *buf)
{
  if (format == with_commas)
    {
      const char *s = !f->stat_ok
        ? "?"
        : human_readable (STP_NBLOCKS (&f->stat), buf,
                          human_output_opts, ST_NBLOCKSIZE,
                          output_block_size);
      return strlen (s);
    }

  return block_size_width;
}

static size_t
get_scontext_width (const struct fileinfo *f)
{
  if (format == with_commas)
    return strlen (f->scontext);

  return scontext_width;
}

static size_t
get_indicator_length (const struct fileinfo *f)
{
  if (indicator_style != none)
    {
      char c = get_type_indicator (f->stat_ok, f->stat.st_mode, f->filetype);
      return (c != 0);
    }

  return 0;
}

static size_t
length_of_file_name_and_frills (const struct fileinfo *f)
{
  size_t len = 0;
  char buf[MAX (LONGEST_HUMAN_READABLE + 1, INT_BUFSIZE_BOUND (uintmax_t))];

  if (print_inode)
    len += 1 + get_inode_width (f, buf);

  if (print_block_size)
    len += 1 + get_block_size_width (f, buf);

  if (print_scontext)
    len += 1 + get_scontext_width (f);

  len += fileinfo_name_width (f);
  len += get_indicator_length (f);

  return len;
}

static void
print_many_per_line (void)
{
  if (cwd_n_used == 0)
    return;

  idx_t cols = calculate_columns (true);
  if (cols == 0)
    return;

  struct column_info const *line_fmt = &column_info[cols - 1];
  idx_t rows = (cwd_n_used + cols - 1) / cols;

  for (idx_t row = 0; row < rows; row++)
    {
      size_t pos = 0;
      for (idx_t filesno = row, col = 0;
           filesno < cwd_n_used;
           filesno += rows, col++)
        {
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
      putchar (eolbyte);
    }
}

static void
print_horizontal (void)
{
  if (cwd_n_used == 0)
    return;

  idx_t cols = calculate_columns (false);
  struct column_info const *line_fmt = &column_info[cols - 1];
  size_t pos = 0;
  size_t name_length = 0;
  size_t max_name_length = 0;

  for (idx_t filesno = 0; filesno < cwd_n_used; filesno++)
    {
      idx_t col = filesno % cols;
      if (filesno > 0)
        {
          if (col == 0)
            {
              putchar (eolbyte);
              pos = 0;
            }
          else
            {
              indent (pos + name_length, pos + max_name_length);
              pos += max_name_length;
            }
        }

      struct fileinfo const *f = sorted_file[filesno];
      print_file_name_and_frills (f, pos);

      name_length = length_of_file_name_and_frills (f);
      max_name_length = line_fmt->col_arr[col];
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

      if (filesno > 0)
        {
          const size_t separator_width = 2;
          char following_separator;

          const bool fits_on_line = !line_length
            || (pos <= SIZE_MAX - len - separator_width
                && pos + len + separator_width < line_length);

          if (fits_on_line)
            {
              following_separator = ' ';
              pos += separator_width;
            }
          else
            {
              following_separator = eolbyte;
              pos = 0;
            }

          putchar (sep);
          putchar (following_separator);
        }

      print_file_name_and_frills (f, pos);
      pos += len;
    }
  putchar (eolbyte);
}

/* Assuming cursor is at position FROM, indent up to position TO.
   Use a TAB character instead of two or more spaces whenever possible.  */

static void
indent (size_t from, size_t to, size_t tabsize)
{
  while (from < to)
    {
      char char_to_write;
      size_t next_from;

      if (tabsize > 0 && to / tabsize > (from + 1) / tabsize)
        {
          char_to_write = '\t';
          next_from = (from / tabsize + 1) * tabsize;
        }
      else
        {
          char_to_write = ' ';
          next_from = from + 1;
        }

      if (putchar (char_to_write) == EOF)
        {
          return;
        }
      from = next_from;
    }
}

/* Put DIRNAME/NAME into DEST, handling '.' and '/' properly.  */
/* FIXME: maybe remove this function someday.  See about using a
   non-malloc'ing version of file_name_concat.  */

static void
attach (char *dest, char const *dirname, char const *name)
{
  if (!dest)
    {
      return;
    }
  if (!dirname || !name)
    {
      *dest = '\0';
      return;
    }

  char *p = dest;

  if (strcmp(dirname, ".") != 0)
    {
      size_t len = strlen(dirname);
      if (len > 0)
        {
          memcpy(p, dirname, len);
          p += len;
          if (p[-1] != '/')
            {
              *p++ = '/';
            }
        }
    }

  strcpy(p, name);
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
                             max_cols - old_alloc, -1,
                             sizeof *column_info);
      idx_t new_alloc = column_info_alloc;

      idx_t new_triangle_numerator;
      if (ckd_add (&new_triangle_numerator, new_alloc, 1)
          || ckd_mul (&new_triangle_numerator, new_triangle_numerator,
                      new_alloc))
        xalloc_die ();

      idx_t old_triangle_numerator;
      if (ckd_add (&old_triangle_numerator, old_alloc, 1)
          || ckd_mul (&old_triangle_numerator, old_triangle_numerator,
                      old_alloc))
        xalloc_die ();

      size_t cells_to_alloc =
        (size_t) (new_triangle_numerator - old_triangle_numerator) / 2;

      if (cells_to_alloc > 0)
        {
          size_t *p = xinmalloc (cells_to_alloc, sizeof *p);
          for (idx_t i = old_alloc; i < new_alloc; i++)
            {
              column_info[i].col_arr = p;
              p += i + 1;
            }
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
    if (cwd_n_used == 0)
    {
        return 1;
    }

    idx_t max_cols = cwd_n_used;
    if (max_idx > 0 && max_idx < max_cols)
    {
        max_cols = max_idx;
    }

    init_column_info (max_cols);

    enum { COLUMN_SEPARATOR_WIDTH = 2 };

    for (idx_t fileno = 0; fileno < cwd_n_used; ++fileno)
    {
        size_t name_length = length_of_file_name_and_frills (sorted_file[fileno]);

        for (idx_t num_cols = 1; num_cols <= max_cols; ++num_cols)
        {
            idx_t layout_idx = num_cols - 1;
            struct column_info *layout = &column_info[layout_idx];

            if (!layout->valid_len)
            {
                continue;
            }

            idx_t col_idx;
            if (by_columns)
            {
                idx_t num_rows = (cwd_n_used + num_cols - 1) / num_cols;
                col_idx = fileno / num_rows;
            }
            else
            {
                col_idx = fileno % num_cols;
            }

            bool is_last_col = (col_idx == num_cols - 1);
            size_t required_width = name_length + (is_last_col ? 0 : COLUMN_SEPARATOR_WIDTH);

            if (layout->col_arr[col_idx] < required_width)
            {
                layout->line_len += required_width - layout->col_arr[col_idx];
                layout->col_arr[col_idx] = required_width;
                layout->valid_len = (layout->line_len < line_length);
            }
        }
    }

    for (idx_t cols = max_cols; cols > 0; --cols)
    {
        if (column_info[cols - 1].valid_len)
        {
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
    }
  else
    {
      static const char * const option_lines[] =
        {
          _("  -a, --all                  do not ignore entries starting with .\n\
  -A, --almost-all           do not list implied . and ..\n\
      --author               with -l, print the author of each file\n\
  -b, --escape               print C-style escapes for nongraphic characters\n\
"),
          _("      --block-size=SIZE      with -l, scale sizes by SIZE when printing them;\n\
                             e.g., '--block-size=M'; see SIZE format below\n\
\n\
"),
          _("  -B, --ignore-backups       do not list implied entries ending with ~\n\
"),
          _("  -c                         with -lt: sort by, and show, ctime (time of last\n\
                             change of file status information);\n\
                             with -l: show ctime and sort by name;\n\
                             otherwise: sort by ctime, newest first\n\
\n\
"),
          _("  -C                         list entries by columns\n\
      --color[=WHEN]         color the output WHEN; more info below\n\
  -d, --directory            list directories themselves, not their contents\n\
  -D, --dired                generate output designed for Emacs' dired mode\n\
"),
          _("  -f                         same as -a -U\n\
  -F, --classify[=WHEN]      append indicator (one of */=>@|) to entries WHEN\n\
      --file-type            likewise, except do not append '*'\n\
"),
          _("      --format=WORD          across,horizontal (-x), commas (-m), long (-l),\n\
                             single-column (-1), verbose (-l), vertical (-C)\n\
\n\
"),
          _("      --full-time            like -l --time-style=full-iso\n\
"),
          _("  -g                         like -l, but do not list owner\n\
"),
          _("      --group-directories-first\n\
                             group directories before files\n\
"),
          _("  -G, --no-group             in a long listing, don't print group names\n\
"),
          _("  -h, --human-readable       with -l and -s, print sizes like 1K 234M 2G etc.\n\
      --si                   likewise, but use powers of 1000 not 1024\n\
"),
          _("  -H, --dereference-command-line\n\
                             follow symbolic links listed on the command line\n\
"),
          _("      --dereference-command-line-symlink-to-dir\n\
                             follow each command line symbolic link\n\
                             that points to a directory\n\
\n\
"),
          _("      --hide=PATTERN         do not list implied entries matching shell PATTERN\
\n\
                             (overridden by -a or -A)\n\
\n\
"),
          _("      --hyperlink[=WHEN]     hyperlink file names WHEN\n\
"),
          _("      --indicator-style=WORD\n\
                             append indicator with style WORD to entry names:\n\
                             none (default), slash (-p),\n\
                             file-type (--file-type), classify (-F)\n\
\n\
"),
          _("  -i, --inode                print the index number of each file\n\
  -I, --ignore=PATTERN       do not list implied entries matching shell PATTERN\
\n\
"),
          _("  -k, --kibibytes            default to 1024-byte blocks for file system usage;\
\n\
                             used only with -s and per directory totals\n\
\n\
"),
          _("  -l                         use a long listing format\n\
"),
          _("  -L, --dereference          when showing file information for a symbolic\n\
                             link, show information for the file the link\n\
                             references rather than for the link itself\n\
\n\
"),
          _("  -m                         fill width with a comma separated list of entries\
\n\
"),
          _("  -n, --numeric-uid-gid      like -l, but list numeric user and group IDs\n\
  -N, --literal              print entry names without quoting\n\
  -o                         like -l, but do not list group information\n\
  -p, --indicator-style=slash\n\
                             append / indicator to directories\n\
"),
          _("  -q, --hide-control-chars   print ? instead of nongraphic characters\n\
"),
          _("      --show-control-chars   show nongraphic characters as-is (the default,\n\
                             unless program is 'ls' and output is a terminal)\
\n\
\n\
"),
          _("  -Q, --quote-name           enclose entry names in double quotes\n\
"),
          _("      --quoting-style=WORD   use quoting style WORD for entry names:\n\
                             literal, locale, shell, shell-always,\n\
                             shell-escape, shell-escape-always, c, escape\n\
                             (overrides QUOTING_STYLE environment variable)\n\
\n\
"),
          _("  -r, --reverse              reverse order while sorting\n\
  -R, --recursive            list subdirectories recursively\n\
  -s, --size                 print the allocated size of each file, in blocks\n\
"),
          _("  -S                         sort by file size, largest first\n\
"),
          _("      --sort=WORD            change default 'name' sort to WORD:\n\
                               none (-U), size (-S), time (-t),\n\
                               version (-v), extension (-X), name, width\n\
\n\
"),
          _("      --time=WORD            select which timestamp used to display or sort;\n\
                               access time (-u): atime, access, use;\n\
                               metadata change time (-c): ctime, status;\n\
                               modified time (default): mtime, modification;\n\
                               birth time: birth, creation;\n\
                             with -l, WORD determines which time to show;\n\
                             with --sort=time, sort by WORD (newest first)\n\
\n\
"),
          _("      --time-style=TIME_STYLE\n\
                             time/date format with -l; see TIME_STYLE below\n\
"),
          _("  -t                         sort by time, newest first; see --time\n\
  -T, --tabsize=COLS         assume tab stops at each COLS instead of 8\n\
"),
          _("  -u                         with -lt: sort by, and show, access time;\n\
                             with -l: show access time and sort by name;\n\
                             otherwise: sort by access time, newest first\n\
\n\
"),
          _("  -U                         do not sort directory entries\n\
"),
          _("  -v                         natural sort of (version) numbers within text\n\
"),
          _("  -w, --width=COLS           set output width to COLS.  0 means no limit\n\
  -x                         list entries by lines instead of by columns\n\
  -X                         sort alphabetically by entry extension\n\
  -Z, --context              print any security context of each file\n\
      --zero                 end each output line with NUL, not newline\n\
  -1                         list one file per line\n\
"),
          NULL
        };

      static const char * const note_lines[] =
        {
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
"),
          NULL
        };

      printf (_("Usage: %s [OPTION]... [FILE]...\n"), program_name);
      fputs (_("\
List information about the FILEs (the current directory by default).\n\
Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n\
"), stdout);

      emit_mandatory_arg_note ();

      for (size_t i = 0; option_lines[i] != NULL; i++)
        fputs (option_lines[i], stdout);

      fputs (HELP_OPTION_DESCRIPTION, stdout);
      fputs (VERSION_OPTION_DESCRIPTION, stdout);
      emit_size_note ();

      for (size_t i = 0; note_lines[i] != NULL; i++)
        fputs (note_lines[i], stdout);

      emit_ancillary_info (PROGRAM_NAME);
    }
  exit (status);
}
