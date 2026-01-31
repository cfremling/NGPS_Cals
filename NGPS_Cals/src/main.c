// ngps_cals_status_v7.c
// Terminal status dashboard for NGPS calibration completeness (multi-extension NGPS FITS).
//
// v7 updates (Jan 2026):
//  - ANSI red/green completion highlighting in terminal tables (no change to counting logic)
//  - Optional --gui: lightweight local web UI with compact tables and editable dir/csv fields
//  - Table printer aligns correctly even with ANSI color codes
//  - Underlying scan/count/group logic unchanged from v4
//
// Build:
//   gcc -O2 -Wall -Wextra -std=c11 -o ngps_cals_status ngps_cals_status_v7.c -lm
//
// Examples:
//   ./ngps_cals_status --dir /data/latest
//   ./ngps_cals_status --dir /data/latest --csv ngps_20260128.csv
//   ./ngps_cals_status --dir /data/latest --csv ngps_20260128.csv --debug --once
//   ./ngps_cals_status --gui --dir /data/latest --csv ngps_20260128.csv


#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <sys/stat.h>
#include <time.h>
#include <math.h>
#include <unistd.h>
#include <sys/select.h>
#include <termios.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

// ------------------------------
// Requirements
// ------------------------------
#define REQ_THAR     3
#define REQ_FEAR     3
#define REQ_BIAS     7
#define REQ_DOMEFLAT 5

// ------------------------------
// Channels
// ------------------------------
enum { CH_U=0, CH_G=1, CH_R=2, CH_I=3, CH_N=4 };
static const char *CH_NAME[CH_N] = {"U","G","R","I"};

// ------------------------------
// ANSI colors (only if stdout is a TTY)
// ------------------------------
static const char *C_RESET = "\033[0m";
static const char *C_GREEN = "\033[32m";
static const char *C_RED   = "\033[31m";

static bool is_tty_stdout(void){ return isatty(STDOUT_FILENO); }

// ------------------------------
// String helpers
// ------------------------------
static void rstrip(char *s){
    size_t n = strlen(s);
    while(n>0 && isspace((unsigned char)s[n-1])) s[--n] = 0;
}
static void lstrip_inplace(char *s){
    size_t i=0;
    while(s[i] && isspace((unsigned char)s[i])) i++;
    if(i) memmove(s, s+i, strlen(s+i)+1);
}
static void trim(char *s){ rstrip(s); lstrip_inplace(s); }

static void strtoupper_inplace(char *s){ for(; *s; s++) *s = (char)toupper((unsigned char)*s); }

static bool str_ieq(const char *a, const char *b){
    while(*a && *b){
        if(toupper((unsigned char)*a) != toupper((unsigned char)*b)) return false;
        a++; b++;
    }
    return *a==0 && *b==0;
}

static bool str_icontains(const char *hay, const char *needle){
    if(!hay || !needle) return false;
    size_t nlen = strlen(needle);
    if(nlen==0) return true;
    for(const char *p=hay; *p; p++){
        size_t i=0;
        while(p[i] && i<nlen && toupper((unsigned char)p[i])==toupper((unsigned char)needle[i])) i++;
        if(i==nlen) return true;
    }
    return false;
}

static void strip_utf8_bom(char *s){
    // Remove UTF-8 BOM if present at start of string
    unsigned char *u = (unsigned char*)s;
    if(u[0]==0xEF && u[1]==0xBB && u[2]==0xBF){
        memmove(s, s+3, strlen(s+3)+1);
    }
}

static bool is_fits_name(const char *name){
    const char *dot = strrchr(name, '.');
    if(!dot) return false;
    if(str_ieq(dot,".fits") || str_ieq(dot,".fit") || str_ieq(dot,".fts")) return true;
    if(str_ieq(dot,".fz")) return true;
    return false;
}

// ------------------------------
// Terminal raw mode for keypress
// ------------------------------
static struct termios g_term_orig;
static bool g_term_raw=false;

static void term_restore(void){
    if(g_term_raw){
        tcsetattr(STDIN_FILENO, TCSAFLUSH, &g_term_orig);
        g_term_raw=false;
    }
}

static void term_set_raw(void){
    if(g_term_raw) return;
    if(tcgetattr(STDIN_FILENO, &g_term_orig)!=0) return;
    atexit(term_restore);

    struct termios raw = g_term_orig;
    raw.c_lflag &= ~(ECHO | ICANON);
    raw.c_cc[VMIN]=0;
    raw.c_cc[VTIME]=0;
    if(tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw)==0) g_term_raw=true;
}

static int term_read_key_nonblock(void){
    unsigned char c;
    ssize_t r = read(STDIN_FILENO, &c, 1);
    if(r==1) return (int)c;
    return -1;
}

// ------------------------------
// FITS header parser (header-only)
// ------------------------------
typedef struct {
    // keys we care about
    char IMGTYPE[32];
    int BINSPAT;
    int BINSPEC;
    double SLITW;
    char SPEC_ID[32];

    // for skipping data
    int BITPIX;
    int NAXIS;
    int64_t NAXISn[8];
    int64_t PCOUNT;
    int64_t GCOUNT;
    char XTENSION[16];
} FitsHdr;

static void fits_hdr_init(FitsHdr *h){
    memset(h,0,sizeof(*h));
    h->BINSPAT=-1; h->BINSPEC=-1;
    h->SLITW = NAN;
    h->BITPIX=0; h->NAXIS=0; h->PCOUNT=0; h->GCOUNT=1;
    for(int i=0;i<8;i++) h->NAXISn[i]=0;
}

static int64_t pad2880(int64_t n){
    int64_t r = n % 2880;
    return (r==0) ? n : (n + (2880 - r));
}

static int64_t estimate_hdu_data_bytes(const FitsHdr *h){
    if(h->NAXIS<=0 || h->BITPIX==0) return 0;
    int64_t nelem=1;
    for(int i=0;i<h->NAXIS && i<8;i++){
        if(h->NAXISn[i]<=0) { nelem=0; break; }
        if(nelem > INT64_MAX / h->NAXISn[i]) { nelem=0; break; }
        nelem *= h->NAXISn[i];
    }
    int64_t bpe = llabs(h->BITPIX)/8;
    if(bpe<=0) bpe=1;
    int64_t mainBytes = nelem * bpe;
    int64_t gcount = h->GCOUNT; if(gcount<=0) gcount=1;
    int64_t total = (mainBytes + h->PCOUNT) * gcount;
    if(total<0) total=0;
    return total;
}

static void parse_value_string(const char *val, char *out, size_t outsz){
    if(!val || !out || outsz==0) return;
    out[0]=0;
    while(*val && isspace((unsigned char)*val)) val++;

    char tmp[256]={0};
    size_t i=0;
    if(*val=='\''){
        val++;
        while(*val && *val!='\'' && i<sizeof(tmp)-1) tmp[i++]=*val++;
    } else {
        while(*val && i<sizeof(tmp)-1) tmp[i++]=*val++;
    }
    tmp[i]=0;
    trim(tmp);
    size_t n = strlen(tmp);
    if(n >= outsz) n = outsz-1;
    memcpy(out, tmp, n);
    out[n]=0;
}

static double parse_value_double(const char *val, bool *ok){
    if(ok) *ok=false;
    if(!val) return NAN;
    char *end=NULL;
    double x = strtod(val,&end);
    if(end && end!=val){ if(ok) *ok=true; return x; }
    return NAN;
}

static int64_t parse_value_i64(const char *val, bool *ok){
    if(ok) *ok=false;
    if(!val) return 0;
    char *end=NULL;
    int64_t x = strtoll(val,&end,10);
    if(end && end!=val){ if(ok) *ok=true; return x; }
    return 0;
}

static void parse_card(FitsHdr *h, const char card[81]){
    char key[9];
    memcpy(key, card, 8);
    key[8]=0;
    rstrip(key);
    if(key[0]==0) return;
    if(str_ieq(key,"COMMENT") || str_ieq(key,"HISTORY")) return;
    if(card[8] != '=') return;

    char valbuf[128];
    memcpy(valbuf, card+10, 70);
    valbuf[70]=0;
    char *slash = strchr(valbuf,'/');
    if(slash) *slash=0;
    trim(valbuf);

    bool ok=false;
    if(str_ieq(key,"IMGTYPE")){
        parse_value_string(valbuf, h->IMGTYPE, sizeof(h->IMGTYPE));
    } else if(str_ieq(key,"BINSPAT")){
        h->BINSPAT = (int)parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"BINSPEC")){
        h->BINSPEC = (int)parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"SLITW") || str_ieq(key,"SLITWIDTH") || str_ieq(key,"SLITWDTH")){
        h->SLITW = parse_value_double(valbuf,&ok);
    } else if(str_ieq(key,"SPEC_ID")){
        parse_value_string(valbuf, h->SPEC_ID, sizeof(h->SPEC_ID));
    } else if(str_ieq(key,"BITPIX")){
        h->BITPIX = (int)parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"NAXIS")){
        h->NAXIS = (int)parse_value_i64(valbuf,&ok);
    } else if(strncmp(key,"NAXIS",5)==0 && strlen(key)==6 && isdigit((unsigned char)key[5])){
        int idx = key[5]-'1';
        if(idx>=0 && idx<8) h->NAXISn[idx] = parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"PCOUNT")){
        h->PCOUNT = parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"GCOUNT")){
        h->GCOUNT = parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"XTENSION")){
        parse_value_string(valbuf, h->XTENSION, sizeof(h->XTENSION));
    }
}

static bool read_header_cards(FILE *fp, FitsHdr *hdr, int64_t *hdrBytes){
    if(hdrBytes) *hdrBytes=0;
    char block[2880];
    bool foundEnd=false;
    while(!foundEnd){
        size_t nr = fread(block,1,sizeof(block),fp);
        if(nr != sizeof(block)) return false;
        if(hdrBytes) *hdrBytes += (int64_t)nr;
        for(int i=0;i<36;i++){
            char card[81];
            memcpy(card, block+i*80, 80);
            card[80]=0;
            if(strncmp(card,"END",3)==0){ foundEnd=true; break; }
            parse_card(hdr, card);
        }
    }
    return true;
}

// ------------------------------
// IMGTYPE normalization
// - Cal types are explicit
// - Anything else is SCI (per your request)
// ------------------------------
static void normalize_imgtype(const char *in, char out[16]){
    // Normalize IMGTYPE to one of:
    //   THAR, FEAR, DOMEFLAT, BIAS, DARK, CONT, SCI, OTHER
    // Rules:
    //   - Science frames must have IMGTYPE exactly "SCI"
    //   - A calibration frame counts only if IMGTYPE is one of:
    //     FEAR, THAR, DOMEFLAT, DARK, BIAS, CONT
    char tmp[64]={0};
    snprintf(tmp,sizeof(tmp),"%s", in?in:"");
    trim(tmp);
    strtoupper_inplace(tmp);

    // SCI must be exact
    if(strcmp(tmp,"SCI")==0) { strncpy(out,"SCI",16); return; }

    if(str_icontains(tmp,"THAR")) { strncpy(out,"THAR",16); return; }
    if(str_icontains(tmp,"FEAR")) { strncpy(out,"FEAR",16); return; }
    if(str_icontains(tmp,"BIAS")) { strncpy(out,"BIAS",16); return; }
    if(str_icontains(tmp,"DOMEFLAT") || (str_icontains(tmp,"DOME") && str_icontains(tmp,"FLAT"))) {
        strncpy(out,"DOMEFLAT",16); return;
    }
    if(str_icontains(tmp,"DARK")) { strncpy(out,"DARK",16); return; }
    if(str_icontains(tmp,"CONT")) { strncpy(out,"CONT",16); return; }

    strncpy(out,"OTHER",16);
}

static bool is_cal_type(const char *imgtype){
    return (strcmp(imgtype,"THAR")==0 ||
            strcmp(imgtype,"FEAR")==0 ||
            strcmp(imgtype,"BIAS")==0 ||
            strcmp(imgtype,"DOMEFLAT")==0 ||
            strcmp(imgtype,"DARK")==0 ||
            strcmp(imgtype,"CONT")==0);
}

static bool is_sci_type(const char *imgtype){
    return (strcmp(imgtype,"SCI")==0);
}

// ------------------------------
// SPEC_ID -> channel index
// Mirrors your MATLAB behavior: returns index if exactly one of U/G/R/I appears
// ------------------------------
static int specIdToIndex(const char *spec){
    if(!spec || !*spec) return -1;
    char s[64];
    snprintf(s,sizeof(s),"%s",spec);
    trim(s);
    strtoupper_inplace(s);
    if(strlen(s)==1){
        switch(s[0]){
            case 'U': return CH_U;
            case 'G': return CH_G;
            case 'R': return CH_R;
            case 'I': return CH_I;
            default: return -1;
        }
    }
    bool has[CH_N]={false,false,false,false};
    for(const char *p=s; *p; p++){
        if(*p=='U') has[CH_U]=true;
        else if(*p=='G') has[CH_G]=true;
        else if(*p=='R') has[CH_R]=true;
        else if(*p=='I') has[CH_I]=true;
    }
    int cnt=0, idx=-1;
    for(int i=0;i<CH_N;i++) if(has[i]){ cnt++; idx=i; }
    return (cnt==1) ? idx : -1;
}

// ------------------------------
// Per-file metadata
// ------------------------------
typedef struct {
    bool present;
    int ext; // hdu index
    int binspat, binspec;
    double slitw;
    char imgtype[16];
} ChanMeta;

typedef struct {
    bool ok;

    // primary fallback
    char base_imgtype[16];
    int base_binspat, base_binspec;
    double base_slitw;

    ChanMeta ch[CH_N];
} FileMeta;

static void chanmeta_init(ChanMeta *c){
    memset(c,0,sizeof(*c));
    c->present=false;
    c->ext=-1;
    c->binspat=-1;
    c->binspec=-1;
    c->slitw=NAN;
    strncpy(c->imgtype,"SCI",sizeof(c->imgtype));
}

static FileMeta scan_fits_file_multi(const char *path){
    FileMeta out;
    memset(&out,0,sizeof(out));
    out.ok=false;
    strncpy(out.base_imgtype,"OTHER",sizeof(out.base_imgtype));
    out.base_binspat=-1;
    out.base_binspec=-1;
    out.base_slitw=NAN;
    for(int i=0;i<CH_N;i++) chanmeta_init(&out.ch[i]);

    FILE *fp = fopen(path,"rb");
    if(!fp) return out;

    int64_t offset=0;
    const int MAX_HDU=16;

    for(int hdu=0; hdu<MAX_HDU; hdu++){
        if(fseeko(fp,(off_t)offset,SEEK_SET)!=0) break;

        FitsHdr hdr;
        fits_hdr_init(&hdr);
        int64_t hdrBytes=0;
        if(!read_header_cards(fp,&hdr,&hdrBytes)) break;

        // Primary HDU: fallback values
        if(hdu==0){
            if(hdr.IMGTYPE[0]) normalize_imgtype(hdr.IMGTYPE, out.base_imgtype);
            if(hdr.BINSPAT>0) out.base_binspat = hdr.BINSPAT;
            if(hdr.BINSPEC>0) out.base_binspec = hdr.BINSPEC;
            if(isfinite(hdr.SLITW)) out.base_slitw = hdr.SLITW;
        }

        // Image extensions: per-channel, order arbitrary
        if(hdu>0){
            int idx = specIdToIndex(hdr.SPEC_ID);
            if(idx>=0 && idx<CH_N && !out.ch[idx].present){
                ChanMeta *cm = &out.ch[idx];
                cm->present = true;
                cm->ext = hdu;

                // imgtype (fallback to primary)
                if(hdr.IMGTYPE[0]) normalize_imgtype(hdr.IMGTYPE, cm->imgtype);
                else strncpy(cm->imgtype, out.base_imgtype, sizeof(cm->imgtype));

                // binning (fallback to primary)
                cm->binspat = (hdr.BINSPAT>0) ? hdr.BINSPAT : out.base_binspat;
                cm->binspec = (hdr.BINSPEC>0) ? hdr.BINSPEC : out.base_binspec;

                // slit (fallback)
                cm->slitw = isfinite(hdr.SLITW) ? hdr.SLITW : out.base_slitw;
            }
        }

        // Skip data bytes to next HDU
        int64_t dataBytes = estimate_hdu_data_bytes(&hdr);
        offset += hdrBytes + pad2880(dataBytes);
    }

    fclose(fp);

    // ok if at least one channel present and has binning
    for(int ch=0; ch<CH_N; ch++){
        if(out.ch[ch].present && out.ch[ch].binspat>0 && out.ch[ch].binspec>0){
            out.ok=true;
            break;
        }
    }
    return out;
}


// ------------------------------
// Vectors and grouping
// ------------------------------
typedef struct {
    int binspat, binspec;
    int thar[CH_N], fear[CH_N], bias[CH_N], sci[CH_N];
    int thar_goodslit[CH_N], fear_goodslit[CH_N];
} BinGroup;

typedef struct {
    int binspat, binspec;
    double slitw;
    int domeflat[CH_N];
} FlatGroup;

typedef struct { BinGroup *v; int n, cap; } BinVec;

typedef struct { FlatGroup *v; int n, cap; } FlatVec;

static void binvec_free(BinVec *a){ free(a->v); a->v=NULL; a->n=a->cap=0; }
static void flatvec_free(FlatVec *a){ free(a->v); a->v=NULL; a->n=a->cap=0; }

static int binvec_find_or_add(BinVec *a, int binspat, int binspec){
    for(int i=0;i<a->n;i++) if(a->v[i].binspat==binspat && a->v[i].binspec==binspec) return i;
    if(a->n==a->cap){
        a->cap = a->cap? a->cap*2 : 16;
        a->v = (BinGroup*)realloc(a->v, (size_t)a->cap*sizeof(BinGroup));
        if(!a->v){ perror("realloc"); exit(2);}
    }
    BinGroup g; memset(&g,0,sizeof(g));
    g.binspat=binspat; g.binspec=binspec;
    a->v[a->n] = g;
    return a->n++;
}

static int flatvec_find_or_add(FlatVec *a, int binspat, int binspec, double slitw, double tol){
    for(int i=0;i<a->n;i++){
        if(a->v[i].binspat==binspat && a->v[i].binspec==binspec && fabs(a->v[i].slitw - slitw) <= tol) return i;
    }
    if(a->n==a->cap){
        a->cap = a->cap? a->cap*2 : 16;
        a->v = (FlatGroup*)realloc(a->v, (size_t)a->cap*sizeof(FlatGroup));
        if(!a->v){ perror("realloc"); exit(2);}
    }
    FlatGroup g; memset(&g,0,sizeof(g));
    g.binspat=binspat; g.binspec=binspec; g.slitw=slitw;
    a->v[a->n]=g;
    return a->n++;
}

static int cmp_bin_group(const void *A, const void *B){
    const BinGroup *a=(const BinGroup*)A;
    const BinGroup *b=(const BinGroup*)B;
    if(a->binspat != b->binspat) return a->binspat - b->binspat;
    return a->binspec - b->binspec;
}

static int cmp_flat_group(const void *A, const void *B){
    const FlatGroup *a=(const FlatGroup*)A;
    const FlatGroup *b=(const FlatGroup*)B;
    if(a->binspat != b->binspat) return a->binspat - b->binspat;
    if(a->binspec != b->binspec) return a->binspec - b->binspec;
    if(a->slitw < b->slitw) return -1;
    if(a->slitw > b->slitw) return 1;
    return 0;
}

static int find_found_bin(const BinVec *found, int binspat, int binspec){
    for(int i=0;i<found->n;i++) if(found->v[i].binspat==binspat && found->v[i].binspec==binspec) return i;
    return -1;
}

static int find_found_flat(const FlatVec *found, int binspat, int binspec, double slitw, double tol){
    for(int i=0;i<found->n;i++) if(found->v[i].binspat==binspat && found->v[i].binspec==binspec && fabs(found->v[i].slitw-slitw)<=tol) return i;
    return -1;
}

// ------------------------------
// Robust CSV parsing
// ------------------------------
static int csv_split_line(const char *line, char **fields, int maxfields){
    // State-machine CSV split, supports empty fields and quoted fields.
    int n=0;
    bool inq=false;
    char buf[8192];
    int bi=0;

    const char *p=line;
    while(1){
        char c = *p++;
        bool end = (c==0);

        if(!end){
            if(c=='\"'){
                inq = !inq;
                continue;
            }
            if(!inq && (c==',' || c=='\r' || c=='\n')){
                // finalize field
            } else {
                if(bi < (int)sizeof(buf)-1) buf[bi++] = c;
                continue;
            }
        }

        // finalize field
        buf[bi]=0;
        char *f = (char*)malloc(strlen(buf)+1);
        if(!f){ perror("malloc"); exit(2);}
        strcpy(f, buf);
        trim(f);
        strip_utf8_bom(f);
        fields[n++] = f;
        bi=0;

        if(n>=maxfields) break;
        if(end) break;
        if(!inq && (c=='\r' || c=='\n')) break;
        // if c==',' keep parsing next field (including possible empty)
    }

    return n;
}

static void csv_free_fields(char **fields, int n){ for(int i=0;i<n;i++) free(fields[i]); }

static int find_col(char **hdr, int nh, const char *name){
    for(int i=0;i<nh;i++) if(str_ieq(hdr[i], name)) return i;
    return -1;
}

typedef struct {
    bool ok;
    int nh;
    int iBINSPAT, iBINSPEC, iSLITW;
    int nrows_total;
    int nrows_valid;
    int nrows_invalid;
    int n_unique_bins;
    int n_unique_flats;
} CsvStats;

static bool read_required_from_csv(const char *csvPath, BinVec *reqBins, FlatVec *reqFlats,
                                  double default_slitw, double slit_tol, CsvStats *stats){
    if(stats) memset(stats,0,sizeof(*stats));

    FILE *fp = fopen(csvPath,"r");
    if(!fp){
        if(stats) stats->ok=false;
        return false;
    }

    char line[8192];
    if(!fgets(line,sizeof(line),fp)){
        fclose(fp);
        if(stats) stats->ok=false;
        return false;
    }

    char *fields[512];
    int nh = csv_split_line(line, fields, 512);
    int iBINSPAT = find_col(fields, nh, "BINSPAT");
    int iBINSPEC = find_col(fields, nh, "BINSPEC");
    if(iBINSPEC<0) iBINSPEC = find_col(fields, nh, "BINSPECT");
    int iSLITW = find_col(fields, nh, "SLITW");
    if(iSLITW<0) iSLITW = find_col(fields, nh, "SLITWIDTH");
    if(iSLITW<0) iSLITW = find_col(fields, nh, "SLITWDTH");

    if(stats){
        stats->nh = nh;
        stats->iBINSPAT=iBINSPAT;
        stats->iBINSPEC=iBINSPEC;
        stats->iSLITW=iSLITW;
    }

    csv_free_fields(fields, nh);

    if(iBINSPAT<0 || iBINSPEC<0){
        fclose(fp);
        if(stats) stats->ok=false;
        return false;
    }

    int rows_total=0, rows_valid=0, rows_invalid=0;

    while(fgets(line,sizeof(line),fp)){
        if(line[0]=='#' || line[0]==0) continue;
        int nf = csv_split_line(line, fields, 512);
        if(nf<=0){ csv_free_fields(fields,nf); continue; }
        rows_total++;

        int binspat = (iBINSPAT < nf) ? (int)strtol(fields[iBINSPAT],NULL,10) : 0;
        int binspec = (iBINSPEC < nf) ? (int)strtol(fields[iBINSPEC],NULL,10) : 0;
        if(binspat<=0 || binspec<=0){
            rows_invalid++;
            csv_free_fields(fields,nf);
            continue;
        }

        (void)binvec_find_or_add(reqBins, binspat, binspec);

        double slitw = default_slitw;
        if(iSLITW>=0 && iSLITW<nf && fields[iSLITW][0]) slitw = strtod(fields[iSLITW],NULL);
        if(isfinite(slitw) && slitw>0) (void)flatvec_find_or_add(reqFlats, binspat, binspec, slitw, slit_tol);

        rows_valid++;
        csv_free_fields(fields,nf);
    }

    fclose(fp);

    if(stats){
        stats->ok=true;
        stats->nrows_total = rows_total;
        stats->nrows_valid = rows_valid;
        stats->nrows_invalid = rows_invalid;
        stats->n_unique_bins = reqBins->n;
        stats->n_unique_flats = reqFlats->n;
    }

    return true;
}

// ------------------------------
// Directory scanning
// ------------------------------
typedef struct {
    int ug_suppressed[2]; // [U,G] cal channel-frames skipped because R and/or I extensions are present
} SuppressStats;

typedef struct {
    int files_ok;
    int type_counts[CH_N][8];
    // type idx:
    //  0 THAR, 1 FEAR, 2 BIAS, 3 DOMEFLAT, 4 DARK, 5 CONT, 6 SCI, 7 OTHER
    int ch_present[CH_N];
} ScanStats;

static int type_index(const char *imgtype){
    if(strcmp(imgtype,"THAR")==0) return 0;
    if(strcmp(imgtype,"FEAR")==0) return 1;
    if(strcmp(imgtype,"BIAS")==0) return 2;
    if(strcmp(imgtype,"DOMEFLAT")==0) return 3;
    if(strcmp(imgtype,"DARK")==0) return 4;
    if(strcmp(imgtype,"CONT")==0) return 5;
    if(strcmp(imgtype,"SCI")==0) return 6;
    return 7;
}

static void scan_dir_counts(
    const char *dirPath,
    BinVec *foundBins,
    FlatVec *foundFlats,
    BinVec *sciBins,
    FlatVec *sciFlats,
    double slit_tol,
    int *nFilesScanned,
    int *nFilesMatched,
    SuppressStats *supp,
    ScanStats *scanStats
){
    if(nFilesScanned) *nFilesScanned=0;
    if(nFilesMatched) *nFilesMatched=0;
    if(supp) memset(supp,0,sizeof(*supp));
    if(scanStats) memset(scanStats,0,sizeof(*scanStats));

    DIR *dp = opendir(dirPath);
    if(!dp) return;

    struct dirent *de;
    while((de=readdir(dp))){
        if(de->d_name[0]=='.') continue;
        if(!is_fits_name(de->d_name)) continue;
        if(nFilesScanned) (*nFilesScanned)++;

        char full[4096];
        snprintf(full,sizeof(full),"%s/%s",dirPath,de->d_name);
        FileMeta m = scan_fits_file_multi(full);
        if(!m.ok) continue;
        if(scanStats) scanStats->files_ok++;

        if(nFilesMatched) (*nFilesMatched)++;

        // For U/G calibration frames, require that R and I extensions are absent
        bool ri_absent = (!m.ch[CH_R].present && !m.ch[CH_I].present);

        for(int ch=0; ch<CH_N; ch++){
            ChanMeta *cm = &m.ch[ch];
            if(!cm->present) continue;
            if(cm->binspat<=0 || cm->binspec<=0) continue;

            if(scanStats){
                scanStats->ch_present[ch]++;
                int ti = type_index(cm->imgtype);
                if(ti>=0 && ti<8) scanStats->type_counts[ch][ti]++;
            }

            bool is_sci = is_sci_type(cm->imgtype);
            bool is_cal = is_cal_type(cm->imgtype);

            // SCI handling: must be IMGTYPE=="SCI"
            if(is_sci){
                int bi = binvec_find_or_add(foundBins, cm->binspat, cm->binspec);
                foundBins->v[bi].sci[ch]++;

                int sbi = binvec_find_or_add(sciBins, cm->binspat, cm->binspec);
                sciBins->v[sbi].sci[ch]++;

                if(isfinite(cm->slitw)) (void)flatvec_find_or_add(sciFlats, cm->binspat, cm->binspec, cm->slitw, slit_tol);
                continue;
            }

            // Ignore anything that's not SCI and not one of the allowed calibration IMGTYPEs
            if(!is_cal) continue;

            // U/G cal gating: require R and I extensions absent
            bool need_ri_absent = (ch==CH_U || ch==CH_G);
            if(need_ri_absent && !ri_absent){
                if(supp){
                    if(ch==CH_U) supp->ug_suppressed[0]++;
                    if(ch==CH_G) supp->ug_suppressed[1]++;
                }
                continue;
            }

            int bi = binvec_find_or_add(foundBins, cm->binspat, cm->binspec);
            bool goodslit = isfinite(cm->slitw) && cm->slitw <= 2.0;

            if(strcmp(cm->imgtype,"THAR")==0){
                foundBins->v[bi].thar[ch]++;
                if(goodslit) foundBins->v[bi].thar_goodslit[ch]++;
            } else if(strcmp(cm->imgtype,"FEAR")==0){
                foundBins->v[bi].fear[ch]++;
                if(goodslit) foundBins->v[bi].fear_goodslit[ch]++;
            } else if(strcmp(cm->imgtype,"BIAS")==0){
                foundBins->v[bi].bias[ch]++;
            } else if(strcmp(cm->imgtype,"DOMEFLAT")==0){
                if(isfinite(cm->slitw)){
                    int fi = flatvec_find_or_add(foundFlats, cm->binspat, cm->binspec, cm->slitw, slit_tol);
                    foundFlats->v[fi].domeflat[ch]++;
                }
            }
        }
    }

    closedir(dp);
}


// ------------------------------
// Rendering
// ------------------------------
static void clear_screen(void){ fputs("\033[2J\033[H", stdout); }

// ------------------------------
// Simple ASCII table printer (manual; no external deps)
// ------------------------------
static void table_border(const int *w, int ncols, char ch){
    putchar('+');
    for(int i=0;i<ncols;i++){
        for(int k=0;k<w[i]+2;k++) putchar(ch);
        putchar('+');
    }
    putchar('\n');
}


static int visible_len_ansi(const char *s){
    // Count printable characters, ignoring ANSI SGR sequences like "\033[31m".
    int n=0;
    for(size_t i=0; s && s[i]; ){
        if(s[i]=='\033' && s[i+1]=='['){
            i+=2;
            while(s[i] && s[i] != 'm') i++;
            if(s[i]=='m') i++;
        } else {
            n++; i++;
        }
    }
    return n;
}

static void table_row(const int *w, const bool *right, const char **cells, int ncols){
    putchar('|');
    for(int i=0;i<ncols;i++){
        int len = visible_len_ansi(cells[i]);
        int pad = w[i] - len;
        if(pad < 0) pad = 0;

        putchar(' ');
        if(right && right[i]){
            for(int k=0;k<pad;k++) putchar(' ');
            fputs(cells[i], stdout);
        } else {
            fputs(cells[i], stdout);
            for(int k=0;k<pad;k++) putchar(' ');
        }
        putchar(' ');
        putchar('|');
    }
    putchar('\n');
}

static void fmt_ratio(char *buf, size_t n, int have, int req){
    if(req > 0) snprintf(buf, n, "%d/%d", have, req);
    else snprintf(buf, n, "%d", have);
}

static void fmt_ratio_col(char *buf, size_t n, int have, int req, bool tty){
    char tmp[32];
    fmt_ratio(tmp, sizeof(tmp), have, req);
    if(!tty || req<=0){
        snprintf(buf, n, "%s", tmp);
        return;
    }
    const char *c = (have>=req) ? C_GREEN : C_RED;
    snprintf(buf, n, "%s%s%s", c, tmp, C_RESET);
}

static void fmt_ch_col(char *buf, size_t n, const char *ch, bool ok, bool tty){
    if(!tty){ snprintf(buf, n, "%s", ch); return; }
    snprintf(buf, n, "%s%s%s", ok?C_GREEN:C_RED, ch, C_RESET);
}

static void render_dashboard(
    const char *dirPath,
    const char *csvPath,
    bool csv_ok,
    bool inferred_from_sci,
    bool using_detected_fallback,
    const BinVec *reqBins,
    const FlatVec *reqFlats,
    const BinVec *foundBins,
    const FlatVec *foundFlats,
    double slit_tol,
    int nscan,
    int nmatch,
    const SuppressStats *supp,
    bool do_clear
){
    if(do_clear) clear_screen();

    bool tty = is_tty_stdout();

    time_t now=time(NULL);
    struct tm lt; localtime_r(&now,&lt);
    char tbuf[64]; strftime(tbuf,sizeof(tbuf),"%Y-%m-%d %H:%M:%S %Z",&lt);
    printf("NGPS calibration status (multi-ext)  %s\n", tbuf);
    printf("Directory: %s\n", dirPath);
    printf("Files scanned: %d, FITS ok: %d\n", nscan, nmatch);
    printf("Requirements per setup & per channel: THAR=%d FEAR=%d BIAS=%d DOMEFLAT=%d\n", REQ_THAR, REQ_FEAR, REQ_BIAS, REQ_DOMEFLAT);
    printf("U/G cal counts only include cal frames where R & I detectors are OFF (R.DBias<=0 AND I.DBias<=0).\n");
    printf("Cal frames are counted only if IMGTYPE is one of: FEAR, THAR, DOMEFLAT, DARK, BIAS, CONT. Science frames only if IMGTYPE==SCI.\n");
    printf("Flat slit match tolerance: %.2f\"\n", slit_tol);

    if(csvPath){
        printf("CSV: %s  [%s]\n", csvPath, csv_ok?"ok":"FAILED");
    } else {
        printf("CSV: (none)\n");
    }
    if(inferred_from_sci) printf("Required setups: inferred from SCI frames\n");
    if(using_detected_fallback) printf("Required setups: showing detected setups (no CSV/inference setups found)\n");

    if(supp){
        printf("Suppressed U/G cal channel-frames (IMGTYPE cal but R/I not both OFF): U=%d, G=%d\n",
               supp->ug_suppressed[0], supp->ug_suppressed[1]);
    }
    printf("\n");

    // ==========================
    // Arcs/Bias by binning table
    // ==========================
    printf("== Arcs/Bias by binning (BINSPAT x BINSPEC) ==\n");

    if(reqBins->n == 0){
        printf("(no required binnings found)\n\n");
    } else {
        enum { NC_ARC = 8 };
        const char *hdr[NC_ARC] = {"Binning","Ch","THAR","SLITW<=2","FEAR","SLITW<=2","BIAS","SCI"};
        bool right[NC_ARC]      = {false,false,true,true,true,true,true,true};
        int w[NC_ARC];
        for(int i=0;i<NC_ARC;i++) w[i]=(int)strlen(hdr[i]);

        int nrows = reqBins->n * CH_N;
        typedef struct { char c[NC_ARC][64]; } Row;
        Row *rows = (Row*)calloc((size_t)nrows, sizeof(Row));
        if(!rows){ perror("calloc"); exit(2); }

        int ridx=0;
        int complete_by_ch_bins[CH_N]={0,0,0,0};

        for(int i=0;i<reqBins->n;i++){
            int bs=reqBins->v[i].binspat;
            int bc=reqBins->v[i].binspec;
            int fi=find_found_bin(foundBins,bs,bc);

            for(int ch=0; ch<CH_N; ch++){
                int have_thar=0, have_fear=0, have_bias=0, have_sci=0;
                int good_thar=0, good_fear=0;

                if(fi>=0){
                    have_thar = foundBins->v[fi].thar[ch];
                    have_fear = foundBins->v[fi].fear[ch];
                    have_bias = foundBins->v[fi].bias[ch];
                    have_sci  = foundBins->v[fi].sci[ch];
                    good_thar = foundBins->v[fi].thar_goodslit[ch];
                    good_fear = foundBins->v[fi].fear_goodslit[ch];
                }

                bool ok = (have_thar>=REQ_THAR) && (have_fear>=REQ_FEAR) && (have_bias>=REQ_BIAS);
                if(ok) complete_by_ch_bins[ch]++;

                if(ch==0) snprintf(rows[ridx].c[0], sizeof(rows[ridx].c[0]), "%dx%d", bs, bc);
                else      rows[ridx].c[0][0]=0;

                fmt_ch_col(rows[ridx].c[1], sizeof(rows[ridx].c[1]), CH_NAME[ch], ok, tty);
                fmt_ratio_col(rows[ridx].c[2], sizeof(rows[ridx].c[2]), have_thar, REQ_THAR, tty);
                snprintf(rows[ridx].c[3], sizeof(rows[ridx].c[3]), "%d", good_thar);
                fmt_ratio_col(rows[ridx].c[4], sizeof(rows[ridx].c[4]), have_fear, REQ_FEAR, tty);
                snprintf(rows[ridx].c[5], sizeof(rows[ridx].c[5]), "%d", good_fear);
                fmt_ratio_col(rows[ridx].c[6], sizeof(rows[ridx].c[6]), have_bias, REQ_BIAS, tty);
                snprintf(rows[ridx].c[7], sizeof(rows[ridx].c[7]), "%d", have_sci);

                for(int k=0;k<NC_ARC;k++){
                    int L=visible_len_ansi(rows[ridx].c[k]);
                    if(L>w[k]) w[k]=L;
                }
                ridx++;
            }
        }

        table_border(w, NC_ARC, '-');
        table_row(w, right, hdr, NC_ARC);
        table_border(w, NC_ARC, '=');

        ridx=0;
        for(int i=0;i<reqBins->n;i++){
            for(int ch=0; ch<CH_N; ch++){
                const char *cells[NC_ARC];
                for(int k=0;k<NC_ARC;k++) cells[k]=rows[ridx].c[k];
                table_row(w, right, cells, NC_ARC);
                ridx++;
            }
            table_border(w, NC_ARC, '-');
        }

        free(rows);

        printf("\nSummary (complete arcs/bias setups / required setups):\n");
        for(int ch=0; ch<CH_N; ch++){
            printf("  %s: %d/%d\n", CH_NAME[ch], complete_by_ch_bins[ch], reqBins->n);
        }
        printf("\n");
    }

    // ======================
    // Dome flats by setup
    // ======================
    printf("== Dome flats by setup (BINSPAT x BINSPEC, SLITW) ==\n");

    if(reqFlats->n == 0){
        printf("(no required dome-flat setups found)\n\n");
    } else {
        enum { NC_FLAT = 3 };
        const char *hdr[NC_FLAT] = {"Setup","Ch","DOMEFLAT"};
        bool right[NC_FLAT]      = {false,false,true};
        int w[NC_FLAT];
        for(int i=0;i<NC_FLAT;i++) w[i]=(int)strlen(hdr[i]);

        int nrows = reqFlats->n * CH_N;
        typedef struct { char c[NC_FLAT][96]; } Row;
        Row *rows = (Row*)calloc((size_t)nrows, sizeof(Row));
        if(!rows){ perror("calloc"); exit(2); }

        int ridx=0;
        int complete_by_ch_flats[CH_N]={0,0,0,0};

        for(int i=0;i<reqFlats->n;i++){
            int bs=reqFlats->v[i].binspat;
            int bc=reqFlats->v[i].binspec;
            double sw=reqFlats->v[i].slitw;
            int fi=find_found_flat(foundFlats,bs,bc,sw,slit_tol);

            for(int ch=0; ch<CH_N; ch++){
                int have_flat=0;
                if(fi>=0) have_flat = foundFlats->v[fi].domeflat[ch];
                bool ok = (have_flat>=REQ_DOMEFLAT);
                if(ok) complete_by_ch_flats[ch]++;

                if(ch==0) snprintf(rows[ridx].c[0], sizeof(rows[ridx].c[0]), "%dx%d slit %.2f\"", bs, bc, sw);
                else      rows[ridx].c[0][0]=0;

                fmt_ch_col(rows[ridx].c[1], sizeof(rows[ridx].c[1]), CH_NAME[ch], ok, tty);
                fmt_ratio_col(rows[ridx].c[2], sizeof(rows[ridx].c[2]), have_flat, REQ_DOMEFLAT, tty);

                for(int k=0;k<NC_FLAT;k++){
                    int L=visible_len_ansi(rows[ridx].c[k]);
                    if(L>w[k]) w[k]=L;
                }
                ridx++;
            }
        }

        table_border(w, NC_FLAT, '-');
        table_row(w, right, hdr, NC_FLAT);
        table_border(w, NC_FLAT, '=');

        ridx=0;
        for(int i=0;i<reqFlats->n;i++){
            for(int ch=0; ch<CH_N; ch++){
                const char *cells[NC_FLAT];
                for(int k=0;k<NC_FLAT;k++) cells[k]=rows[ridx].c[k];
                table_row(w, right, cells, NC_FLAT);
                ridx++;
            }
            table_border(w, NC_FLAT, '-');
        }

        free(rows);

        printf("\nSummary (complete domeflat setups / required setups):\n");
        for(int ch=0; ch<CH_N; ch++){
            printf("  %s: %d/%d\n", CH_NAME[ch], complete_by_ch_flats[ch], reqFlats->n);
        }
        printf("\n");
    }

    printf("Keys: q=quit  r=refresh now\n");
    fflush(stdout);
}

// ------------------------------
// Options

// ------------------------------
typedef struct {
    const char *dirPath;
    const char *csvPath;
    int refresh_sec;
    bool once;
    double slit_tol;
    double default_slitw;
    bool infer_from_sci_if_no_csv;
    bool debug;
    bool gui;
    int gui_port;
} Options;

static void usage(const char *argv0){
    printf("Usage: %s [options]\n\n", argv0);
    printf("Options:\n");
    printf("  --dir PATH              Directory to scan (default: /data/latest)\n");
    printf("  --csv FILE.csv           Observing plan CSV with BINSPAT,(BINSPEC|BINSPECT)[,SLITW|SLITWIDTH]\n");
    printf("  --refresh N              Refresh every N seconds (default: 5)\n");
    printf("  --once                   Print once and exit\n");
    printf("  --slit-tol X             Slit match tolerance in arcsec (default: 0.05)\n");
    printf("  --default-slit X         If CSV has no slit column, assume this slit (default: 1.50)\n");
    printf("  --no-infer-sci           If no CSV (or CSV fails), do not infer required setups from SCI frames\n");
    printf("  --debug                  Print debug diagnostics (CSV columns, row parsing, scan stats)\n");
    printf("  --gui                    Launch a local web UI (compact tables) instead of terminal\n");
    printf("  --port P                 Port for --gui (default: 8787; tries next ports if busy)\n");
    printf("  -h, --help               Show this help\n");
}

static Options parse_args(int argc, char **argv){
    Options o={0};
    o.dirPath = "/data/latest";
    o.csvPath = NULL;
    o.refresh_sec = 5;
    o.once = false;
    o.slit_tol = 0.05;
    o.default_slitw = 1.50;
    o.infer_from_sci_if_no_csv = true;
    o.debug = false;
    o.gui = false;
    o.gui_port = 8787;

    for(int i=1;i<argc;i++){
        const char *a=argv[i];
        if(strcmp(a,"--dir")==0 && i+1<argc){ o.dirPath=argv[++i]; continue; }
        if(strcmp(a,"--csv")==0 && i+1<argc){ o.csvPath=argv[++i]; continue; }
        if(strcmp(a,"--refresh")==0 && i+1<argc){ o.refresh_sec=atoi(argv[++i]); continue; }
        if(strcmp(a,"--once")==0){ o.once=true; continue; }
        if(strcmp(a,"--slit-tol")==0 && i+1<argc){ o.slit_tol=atof(argv[++i]); continue; }
        if(strcmp(a,"--default-slit")==0 && i+1<argc){ o.default_slitw=atof(argv[++i]); continue; }
        if(strcmp(a,"--no-infer-sci")==0){ o.infer_from_sci_if_no_csv=false; continue; }
        if(strcmp(a,"--debug")==0){ o.debug=true; continue; }
        if(strcmp(a,"--gui")==0){ o.gui=true; continue; }
        if(strcmp(a,"--port")==0 && i+1<argc){ o.gui_port=atoi(argv[++i]); continue; }
        if(strcmp(a,"-h")==0 || strcmp(a,"--help")==0){ usage(argv[0]); exit(0); }
        fprintf(stderr,"Unknown option: %s\n", a);
        usage(argv[0]);
        exit(2);
    }

    if(o.refresh_sec < 1) o.refresh_sec = 1;
    return o;
}

// ------------------------------
// Sleep / key
// ------------------------------
static void sleep_or_key(int seconds, bool *quit, bool enable_keys){
    *quit=false;
    if(!enable_keys){ sleep((unsigned int)seconds); return; }

    fd_set rfds;
    FD_ZERO(&rfds);
    FD_SET(STDIN_FILENO,&rfds);
    struct timeval tv; tv.tv_sec=seconds; tv.tv_usec=0;

    int r = select(STDIN_FILENO+1, &rfds, NULL, NULL, &tv);
    if(r>0 && FD_ISSET(STDIN_FILENO,&rfds)){
        int c = term_read_key_nonblock();
        if(c=='q' || c=='Q') *quit=true;
        // 'r' just returns early to refresh
    }
}

static void debug_print_csv(const char *csvPath, const CsvStats *st){
    if(!csvPath || !st) return;
    fprintf(stderr,"[debug] CSV: %s\n", csvPath);
    fprintf(stderr,"[debug]  ok=%d, header_fields=%d\n", (int)st->ok, st->nh);
    fprintf(stderr,"[debug]  col BINSPAT=%d, col BINSPEC/BINSPECT=%d, col SLITW/SLITWIDTH=%d\n", st->iBINSPAT, st->iBINSPEC, st->iSLITW);
    fprintf(stderr,"[debug]  rows_total=%d, rows_valid=%d, rows_invalid=%d\n", st->nrows_total, st->nrows_valid, st->nrows_invalid);
    fprintf(stderr,"[debug]  unique bin setups=%d, unique flat setups=%d\n", st->n_unique_bins, st->n_unique_flats);
}

static void debug_print_scan(const ScanStats *ss){
    if(!ss) return;
    fprintf(stderr,"[debug] Scan summary: ok_files=%d\n", ss->files_ok);
    for(int ch=0; ch<CH_N; ch++){
        fprintf(stderr,"[debug]   %s: present_ext=%d  THAR=%d FEAR=%d BIAS=%d "
                       "DOMEFLAT=%d DARK=%d CONT=%d SCI=%d OTHER=%d\n",
                CH_NAME[ch], ss->ch_present[ch],
                ss->type_counts[ch][0], ss->type_counts[ch][1],
                ss->type_counts[ch][2], ss->type_counts[ch][3],
                ss->type_counts[ch][4], ss->type_counts[ch][5],
                ss->type_counts[ch][6], ss->type_counts[ch][7]);
    }
}

static void debug_print_requirements(const BinVec *reqBins, const FlatVec *reqFlats, bool from_csv, bool inferred_from_sci, bool using_detected_fallback){
    fprintf(stderr,"[debug] Requirements source: %s%s%s\n",
            from_csv ? "CSV" : (inferred_from_sci ? "SCI inference" : (using_detected_fallback ? "detected fallback" : "none")),
            (from_csv ? "" : ""),
            "");
    if(reqBins){
        fprintf(stderr,"[debug]  required bin setups (%d):", reqBins->n);
        for(int i=0;i<reqBins->n;i++){
            fprintf(stderr," %dx%d", reqBins->v[i].binspat, reqBins->v[i].binspec);
            if(i<reqBins->n-1) fprintf(stderr,",");
        }
        fprintf(stderr,"\n");
    }
    if(reqFlats){
        fprintf(stderr,"[debug]  required flat setups (%d):", reqFlats->n);
        for(int i=0;i<reqFlats->n;i++){
            fprintf(stderr," %dx%d slit %.2f\"", reqFlats->v[i].binspat, reqFlats->v[i].binspec, reqFlats->v[i].slitw);
            if(i<reqFlats->n-1) fprintf(stderr,",");
        }
        fprintf(stderr,"\n");
    }
}


// ------------------------------
// Lightweight GUI mode: local web UI (--gui)
// No external dependencies. Serves a compact HTML page on localhost.
// ------------------------------
static void url_decode_inplace(char *s){
    // Decodes %XX and '+' -> ' ' in-place.
    char *w=s;
    for(char *p=s; p && *p; p++){
        if(*p=='+'){ *w++=' '; }
        else if(*p=='%' && isxdigit((unsigned char)p[1]) && isxdigit((unsigned char)p[2])){
            char hx[3]={p[1],p[2],0};
            *w++ = (char)strtol(hx,NULL,16);
            p+=2;
        } else {
            *w++=*p;
        }
    }
    *w=0;
}

static bool query_get_value(const char *query, const char *key, char *out, size_t outsz){
    // query: "a=b&c=d"
    if(!query || !key || !out || outsz==0) return false;
    out[0]=0;
    size_t klen = strlen(key);
    const char *p = query;
    while(p && *p){
        const char *amp = strchr(p,'&');
        size_t seglen = amp ? (size_t)(amp - p) : strlen(p);
        const char *eq = memchr(p,'=',seglen);
        if(eq){
            size_t nlen = (size_t)(eq - p);
            if(nlen==klen && strncmp(p,key,klen)==0){
                size_t vlen = seglen - (size_t)(eq - p) - 1;
                if(vlen >= outsz) vlen = outsz-1;
                memcpy(out, eq+1, vlen);
                out[vlen]=0;
                url_decode_inplace(out);
                return true;
            }
        }
        p = amp ? (amp+1) : NULL;
    }
    return false;
}

static void html_escape_fputs(FILE *out, const char *s){
    if(!s){ return; }
    for(const unsigned char *p=(const unsigned char*)s; *p; p++){
        switch(*p){
            case '&': fputs("&amp;", out); break;
            case '<': fputs("&lt;", out); break;
            case '>': fputs("&gt;", out); break;
            case '"': fputs("&quot;", out); break;
            case '\'': fputs("&#39;", out); break;
            default: fputc(*p, out); break;
        }
    }
}

static void html_ratio(FILE *out, int have, int req){
    if(req<=0){
        fprintf(out, "%d", have);
        return;
    }
    const char *cls = (have>=req) ? "ok" : "bad";
    fprintf(out, "<span class=\"%s\">%d/%d</span>", cls, have, req);
}

static void compute_once_params(
    const char *dirPath,
    const char *csvPath,
    bool infer_from_sci_if_no_csv,
    double slit_tol,
    double default_slitw,
    bool debug,
    // outputs:
    bool *csv_ok_out,
    bool *inferred_out,
    bool *fallback_out,
    BinVec *reqBins,
    FlatVec *reqFlats,
    BinVec *foundBins,
    FlatVec *foundFlats,
    int *nscan_out,
    int *nmatch_out,
    SuppressStats *supp_out,
    CsvStats *csvStats_out
){
    // CSV requirements
    bool csv_ok=false;
    CsvStats csvStats={0};
    if(csvPath && csvPath[0]){
        csv_ok = read_required_from_csv(csvPath, reqBins, reqFlats, default_slitw, slit_tol, &csvStats);
        if(csv_ok && reqBins->n==0 && reqFlats->n==0) csv_ok=false;
        if(debug){
            debug_print_csv(csvPath, &csvStats);
            if(!csv_ok) fprintf(stderr,"[debug] CSV parse yielded no setups; will fall back to SCI inference and/or detected setups.\n");
        }
    }
    if(csv_ok_out) *csv_ok_out = csv_ok;
    if(csvStats_out) *csvStats_out = csvStats;

    // scan directory & group
    BinVec sciBins={0};
    FlatVec sciFlats={0};
    int nscan=0, nmatch=0;
    SuppressStats supp={0};
    ScanStats scanStatsLocal={0};

    scan_dir_counts(dirPath, foundBins, foundFlats, &sciBins, &sciFlats,
                    slit_tol, &nscan, &nmatch, &supp, debug?&scanStatsLocal:NULL);

    if(nscan_out) *nscan_out = nscan;
    if(nmatch_out) *nmatch_out = nmatch;
    if(supp_out) *supp_out = supp;

    if(debug) debug_print_scan(&scanStatsLocal);

    bool inferred=false;
    bool fallback=false;

    if(!csv_ok){
        if(infer_from_sci_if_no_csv){
            for(int i=0;i<sciBins.n;i++) (void)binvec_find_or_add(reqBins, sciBins.v[i].binspat, sciBins.v[i].binspec);
            for(int i=0;i<sciFlats.n;i++) (void)flatvec_find_or_add(reqFlats, sciFlats.v[i].binspat, sciFlats.v[i].binspec, sciFlats.v[i].slitw, slit_tol);
            if(reqBins->n>0 || reqFlats->n>0) inferred=true;
        }
    }


    // Always include any detected setups in the displayed setup list (e.g., if a new setup appears after startup)
    for(int i=0;i<foundBins->n;i++) (void)binvec_find_or_add(reqBins, foundBins->v[i].binspat, foundBins->v[i].binspec);
    for(int i=0;i<foundFlats->n;i++) (void)flatvec_find_or_add(reqFlats, foundFlats->v[i].binspat, foundFlats->v[i].binspec, foundFlats->v[i].slitw, slit_tol);

    if(reqBins->n==0 && reqFlats->n==0){
        for(int i=0;i<foundBins->n;i++) (void)binvec_find_or_add(reqBins, foundBins->v[i].binspat, foundBins->v[i].binspec);
        for(int i=0;i<foundFlats->n;i++) (void)flatvec_find_or_add(reqFlats, foundFlats->v[i].binspat, foundFlats->v[i].binspec, foundFlats->v[i].slitw, slit_tol);
        fallback = (reqBins->n>0 || reqFlats->n>0);
    }

    if(reqBins->n>1) qsort(reqBins->v,(size_t)reqBins->n,sizeof(BinGroup),cmp_bin_group);
    if(reqFlats->n>1) qsort(reqFlats->v,(size_t)reqFlats->n,sizeof(FlatGroup),cmp_flat_group);

    if(inferred_out) *inferred_out = inferred;
    if(fallback_out) *fallback_out = fallback;

    binvec_free(&sciBins);
    flatvec_free(&sciFlats);
}

static void render_dashboard_html(
    FILE *out,
    const char *dirPath,
    const char *csvPath,
    bool csv_ok,
    bool inferred_from_sci,
    bool using_detected_fallback,
    const BinVec *reqBins,
    const FlatVec *reqFlats,
    const BinVec *foundBins,
    const FlatVec *foundFlats,
    double slit_tol,
    int nscan,
    int nmatch,
    const SuppressStats *supp,
    int refresh_sec
){    fputs(
        "<!doctype html><html><head><meta charset=\"utf-8\">"
        "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
        "<title>NGPS Cals Status</title>"
        "<style>"
        "body{font-family:ui-sans-serif,system-ui,-apple-system,Segoe UI,Roboto,Helvetica,Arial; margin:14px;}"
        "h1{font-size:18px; margin:0 0 10px 0;}"
        ".sub{color:#555; font-size:12px; margin-bottom:10px;}"
        "form{display:flex; flex-wrap:wrap; gap:10px; align-items:end; margin:10px 0 12px 0;}"
        "label{font-size:12px; color:#444; display:flex; flex-direction:column; gap:4px;}"
        "input{font-size:12px; padding:6px 8px; border:1px solid #ccc; border-radius:6px; min-width:320px;}"
        "input.small{min-width:140px;}"
        "button{font-size:12px; padding:7px 10px; border:1px solid #777; border-radius:8px; background:#f6f6f6; cursor:pointer;}"
        "table{border-collapse:collapse; width:100%; font-size:12px;}"
        "th,td{border:1px solid #ddd; padding:4px 6px; text-align:right; white-space:nowrap;}"
        "th:first-child, td:first-child, th:nth-child(2), td:nth-child(2){text-align:left;}"
        "thead th{background:#f2f2f2;}"
        "tr.sep td{border:none; padding:2px; background:transparent;}"
        ".ok{color:#0a7a2f; font-weight:600;}"
        ".bad{color:#b00020; font-weight:600;}"
        ".muted{color:#666;}"
        ".note{font-size:12px; color:#555; margin:8px 0 12px 0;}"
        ".grid{display:grid; grid-template-columns:1fr; gap:14px;}"
        "@media(min-width:1100px){.grid{grid-template-columns:1fr 1fr;}}"
        "</style>"
        "</head><body>"
    , out);

    fprintf(out,"<h1>NGPS calibration status</h1>");
    fprintf(out,"<div class=\"sub\">files scanned: %d, FITS ok: %d &nbsp;|&nbsp; slit tol %.2f&quot; &nbsp;|&nbsp; req: THAR=%d FEAR=%d BIAS=%d DOMEFLAT=%d</div>",
            nscan, nmatch, slit_tol, REQ_THAR, REQ_FEAR, REQ_BIAS, REQ_DOMEFLAT);

    // form (dir/csv/refresh)
    fprintf(out,"<form method=\"GET\" action=\"/\">");
    fprintf(out,"<label>Data dir<input name=\"dir\" value=\""); html_escape_fputs(out, dirPath?dirPath:""); fprintf(out,"\"></label>");
    fprintf(out,"<label>CSV<input name=\"csv\" value=\""); html_escape_fputs(out, csvPath?csvPath:""); fprintf(out,"\"></label>");    fprintf(out,"<label>Refresh (s)<input class=\"small\" name=\"refresh\" value=\"%d\"></label>", refresh_sec);
    fprintf(out,"<button type=\"submit\">Update</button>");
    fprintf(out,"</form>");

    fprintf(out,"<div class=\"note\">CSV status: ");
    fprintf(out,"<span class=\"%s\">%s</span>", csv_ok?"ok":"bad", csv_ok?"ok":"FAILED");
    if(!csvPath || !csvPath[0]) fprintf(out," <span class=\"muted\">(none)</span>");
    fprintf(out," &nbsp;|&nbsp; required setups: ");
    if(csv_ok) fprintf(out,"CSV");
    else if(inferred_from_sci) fprintf(out,"SCI inference");
    else if(using_detected_fallback) fprintf(out,"detected fallback");
    else fprintf(out,"none");
    if(supp) fprintf(out," &nbsp;|&nbsp; suppressed U=%d G=%d", supp->ug_suppressed[0], supp->ug_suppressed[1]);
    fprintf(out,"</div>");

    fprintf(out,"<div class=\"grid\">");

    // Arcs table
    fprintf(out,"<div><h1 style=\"font-size:14px; margin:0 0 6px 0;\">Arcs/Bias by binning</h1>");
    if(reqBins->n==0){
        fprintf(out,"<div class=\"muted\">No required binnings found.</div></div>");
    } else {
        fprintf(out,"<table><thead><tr>"
                    "<th>Binning</th><th>Ch</th>"
                    "<th>THAR</th><th>THAR≤2</th>"
                    "<th>FEAR</th><th>FEAR≤2</th>"
                    "<th>BIAS</th><th>SCI</th>"
                    "</tr></thead><tbody>");
        for(int i=0;i<reqBins->n;i++){
            int bs=reqBins->v[i].binspat;
            int bc=reqBins->v[i].binspec;
            int fi=find_found_bin(foundBins,bs,bc);
            for(int ch=0; ch<CH_N; ch++){
                int have_thar=0, have_fear=0, have_bias=0, have_sci=0;
                int good_thar=0, good_fear=0;
                if(fi>=0){
                    have_thar = foundBins->v[fi].thar[ch];
                    have_fear = foundBins->v[fi].fear[ch];
                    have_bias = foundBins->v[fi].bias[ch];
                    have_sci  = foundBins->v[fi].sci[ch];
                    good_thar = foundBins->v[fi].thar_goodslit[ch];
                    good_fear = foundBins->v[fi].fear_goodslit[ch];
                }
                bool ok = (have_thar>=REQ_THAR) && (have_fear>=REQ_FEAR) && (have_bias>=REQ_BIAS);
                fprintf(out,"<tr>");
                if(ch==0) fprintf(out,"<td>%dx%d</td>", bs, bc);
                else fprintf(out,"<td></td>");
                fprintf(out,"<td><span class=\"%s\">%s</span></td>", ok?"ok":"bad", CH_NAME[ch]);
                fprintf(out,"<td>"); html_ratio(out, have_thar, REQ_THAR); fprintf(out,"</td>");
                fprintf(out,"<td class=\"muted\">%d</td>", good_thar);
                fprintf(out,"<td>"); html_ratio(out, have_fear, REQ_FEAR); fprintf(out,"</td>");
                fprintf(out,"<td class=\"muted\">%d</td>", good_fear);
                fprintf(out,"<td>"); html_ratio(out, have_bias, REQ_BIAS); fprintf(out,"</td>");
                fprintf(out,"<td>%d</td>", have_sci);
                fprintf(out,"</tr>");
            }
            fprintf(out,"<tr class=\"sep\"><td colspan=\"8\"></td></tr>");
        }
        fprintf(out,"</tbody></table></div>");
    }

    // Flats table
    fprintf(out,"<div><h1 style=\"font-size:14px; margin:0 0 6px 0;\">Dome flats by setup</h1>");
    if(reqFlats->n==0){
        fprintf(out,"<div class=\"muted\">No required dome-flat setups found.</div></div>");
    } else {
        fprintf(out,"<table><thead><tr>"
                    "<th>Setup</th><th>Ch</th><th>DOMEFLAT</th>"
                    "</tr></thead><tbody>");
        for(int i=0;i<reqFlats->n;i++){
            int bs=reqFlats->v[i].binspat;
            int bc=reqFlats->v[i].binspec;
            double sw=reqFlats->v[i].slitw;
            int fi=find_found_flat(foundFlats,bs,bc,sw,slit_tol);
            for(int ch=0; ch<CH_N; ch++){
                int have_flat=0;
                if(fi>=0) have_flat = foundFlats->v[fi].domeflat[ch];
                bool ok = (have_flat>=REQ_DOMEFLAT);
                fprintf(out,"<tr>");
                if(ch==0) fprintf(out,"<td>%dx%d slit %.2f&quot;</td>", bs, bc, sw);
                else fprintf(out,"<td></td>");
                fprintf(out,"<td><span class=\"%s\">%s</span></td>", ok?"ok":"bad", CH_NAME[ch]);
                fprintf(out,"<td>"); html_ratio(out, have_flat, REQ_DOMEFLAT); fprintf(out,"</td>");
                fprintf(out,"</tr>");
            }
            fprintf(out,"<tr class=\"sep\"><td colspan=\"3\"></td></tr>");
        }
        fprintf(out,"</tbody></table></div>");
    }

    fprintf(out,"</div>"); // grid

    // auto refresh
    fprintf(out,"<script>var r=%d; if(r>0){setTimeout(function(){location.reload();}, r*1000);} </script>", refresh_sec);

    fprintf(out,"</body></html>");
}

static int bind_listen_port(int start_port, int *chosen_port){
    int sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if(sockfd < 0) return -1;

    int yes=1;
    setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));

    struct sockaddr_in addr;
    memset(&addr,0,sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);

    int port = start_port;
    for(int k=0;k<10;k++,port++){
        addr.sin_port = htons((uint16_t)port);
        if(bind(sockfd, (struct sockaddr*)&addr, sizeof(addr))==0){
            if(listen(sockfd, 16)==0){
                if(chosen_port) *chosen_port = port;
                return sockfd;
            }
        }
    }
    close(sockfd);
    return -1;
}

static void try_open_browser(int port){
    char url[128];
    snprintf(url,sizeof(url),"http://127.0.0.1:%d/", port);
#ifdef __APPLE__
    char cmd[256]; snprintf(cmd,sizeof(cmd),"open \"%s\" >/dev/null 2>&1", url);
    system(cmd);
#else
    char cmd[256]; snprintf(cmd,sizeof(cmd),"xdg-open \"%s\" >/dev/null 2>&1", url);
    system(cmd);
#endif
}

static void handle_http_client(int cfd, const Options *opt){
    char buf[8192];
    ssize_t n = recv(cfd, buf, sizeof(buf)-1, 0);
    if(n<=0) return;
    buf[n]=0;

    // parse first line
    char method[8]={0}, pathq[4096]={0};
    if(sscanf(buf, "%7s %4095s", method, pathq) != 2) return;
    if(strcmp(method,"GET")!=0){
        const char *msg = "HTTP/1.1 405 Method Not Allowed\r\nConnection: close\r\n\r\n";
        send(cfd, msg, strlen(msg), 0);
        return;
    }

    // ignore favicon
    if(strncmp(pathq, "/favicon.ico", 12)==0){
        const char *msg = "HTTP/1.1 204 No Content\r\nConnection: close\r\n\r\n";
        send(cfd, msg, strlen(msg), 0);
        return;
    }

    // split query
    char *qmark = strchr(pathq,'?');
    char *query = NULL;
    if(qmark){ *qmark=0; query = qmark+1; }

    // params with defaults
    char dir[2048]={0}, csv[2048]={0};
    int refresh_sec = opt->refresh_sec;

    // defaults from command-line
    if(opt->dirPath) { size_t n=strlen(opt->dirPath); if(n>=sizeof(dir)) n=sizeof(dir)-1; memcpy(dir,opt->dirPath,n); dir[n]=0; }
    if(opt->csvPath) { size_t n=strlen(opt->csvPath); if(n>=sizeof(csv)) n=sizeof(csv)-1; memcpy(csv,opt->csvPath,n); csv[n]=0; }

    if(query){
        char tmp[2048];
        if(query_get_value(query,"dir",tmp,sizeof(tmp))) { size_t n=strlen(tmp); if(n>=sizeof(dir)) n=sizeof(dir)-1; memcpy(dir,tmp,n); dir[n]=0; }
        if(query_get_value(query,"csv",tmp,sizeof(tmp))) { size_t n=strlen(tmp); if(n>=sizeof(csv)) n=sizeof(csv)-1; memcpy(csv,tmp,n); csv[n]=0; }
        if(query_get_value(query,"refresh",tmp,sizeof(tmp))) refresh_sec = (int)strtol(tmp,NULL,10);
    }
    if(refresh_sec < 0) refresh_sec = 0;

    const char *csvPath = (csv[0] ? csv : NULL);

    // compute
    BinVec reqBins={0}, foundBins={0};
    FlatVec reqFlats={0}, foundFlats={0};
    bool csv_ok=false, inferred=false, fallback=false;
    int nscan=0, nmatch=0;
    SuppressStats supp={0};
    CsvStats csvStats={0};

    compute_once_params(dir, csvPath,
                        opt->infer_from_sci_if_no_csv,
                        opt->slit_tol, opt->default_slitw,
                        opt->debug,
                        &csv_ok, &inferred, &fallback,
                        &reqBins, &reqFlats, &foundBins, &foundFlats,
                        &nscan, &nmatch, &supp, &csvStats);

    // respond
    FILE *out = fdopen(dup(cfd), "w");
    if(out){
        setvbuf(out, NULL, _IONBF, 0);
        fprintf(out, "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nConnection: close\r\n\r\n");
        render_dashboard_html(out, dir, csvPath, csv_ok, inferred, fallback,
                             &reqBins, &reqFlats, &foundBins, &foundFlats,
                             opt->slit_tol, nscan, nmatch, &supp, refresh_sec);
        fclose(out);
    }

    binvec_free(&reqBins); binvec_free(&foundBins);
    flatvec_free(&reqFlats); flatvec_free(&foundFlats);
}

static int run_gui_server(const Options *opt){
    int port = opt->gui_port;
    if(port <= 0) port = 8787;

    int chosen=0;
    int sfd = bind_listen_port(port, &chosen);
    if(sfd < 0){
        fprintf(stderr,"[gui] Failed to bind localhost port starting at %d\n", port);
        return 2;
    }

    fprintf(stderr,"[gui] Listening on http://127.0.0.1:%d/  (Ctrl-C to quit)\n", chosen);
    try_open_browser(chosen);

    while(1){
        struct sockaddr_in caddr; socklen_t clen=sizeof(caddr);
        int cfd = accept(sfd, (struct sockaddr*)&caddr, &clen);
        if(cfd < 0){
            if(errno==EINTR) continue;
            break;
        }
        handle_http_client(cfd, opt);
        close(cfd);
    }
    close(sfd);
    return 0;
}

int main(int argc, char **argv){
    // Ensure Palomar local time
    setenv("TZ","America/Los_Angeles",1);
    tzset();

    Options opt = parse_args(argc, argv);

    if(opt.gui){
        return run_gui_server(&opt);
    }

    // Night filtering disabled: all .fits in the directory are considered part of the same observing set    // Read requirements from CSV (if given)
    BinVec reqBins={0};
    FlatVec reqFlats={0};
    CsvStats csvStats={0};
    bool csv_ok=false;

    if(opt.csvPath){
        csv_ok = read_required_from_csv(opt.csvPath, &reqBins, &reqFlats, opt.default_slitw, opt.slit_tol, &csvStats);
        // Treat "ok but empty" as failure for requirement purposes
        if(csv_ok && reqBins.n==0 && reqFlats.n==0) csv_ok=false;
        if(opt.debug){
            debug_print_csv(opt.csvPath, &csvStats);
            if(!csv_ok) fprintf(stderr,"[debug] CSV parse yielded no setups; will fall back to SCI inference and/or detected setups.\n");
        }
    }

    bool enable_keys = (!opt.once && !opt.debug);
    bool do_clear = (!opt.debug);

    if(enable_keys) term_set_raw();

    bool first_loop=true;

    while(1){
        BinVec foundBins={0}, sciBins={0};
        FlatVec foundFlats={0}, sciFlats={0};
        int nscan=0, nmatch=0;
        SuppressStats supp={0};
        ScanStats scanStatsLocal={0};

        scan_dir_counts(opt.dirPath, &foundBins, &foundFlats, &sciBins, &sciFlats,
                        opt.slit_tol, &nscan, &nmatch, &supp, opt.debug?&scanStatsLocal:NULL);

        if(opt.debug && first_loop) debug_print_scan(&scanStatsLocal);

        bool inferred_from_sci=false;
        bool using_detected_fallback=false;

        // Determine required setups
        if(!csv_ok){
            if(opt.infer_from_sci_if_no_csv){
                for(int i=0;i<sciBins.n;i++) (void)binvec_find_or_add(&reqBins, sciBins.v[i].binspat, sciBins.v[i].binspec);
                for(int i=0;i<sciFlats.n;i++) (void)flatvec_find_or_add(&reqFlats, sciFlats.v[i].binspat, sciFlats.v[i].binspec, sciFlats.v[i].slitw, opt.slit_tol);
                if(reqBins.n>0 || reqFlats.n>0) inferred_from_sci=true;
            }
        }

        // If still empty, fall back to detected setups so you always see something
        if(reqBins.n==0 && reqFlats.n==0){
            for(int i=0;i<foundBins.n;i++) (void)binvec_find_or_add(&reqBins, foundBins.v[i].binspat, foundBins.v[i].binspec);
            for(int i=0;i<foundFlats.n;i++) (void)flatvec_find_or_add(&reqFlats, foundFlats.v[i].binspat, foundFlats.v[i].binspec, foundFlats.v[i].slitw, opt.slit_tol);
            using_detected_fallback = (reqBins.n>0 || reqFlats.n>0);
        }

        // Always include any newly-detected setups in the displayed setup list
        for(int i=0;i<foundBins.n;i++) (void)binvec_find_or_add(&reqBins, foundBins.v[i].binspat, foundBins.v[i].binspec);
        for(int i=0;i<foundFlats.n;i++) (void)flatvec_find_or_add(&reqFlats, foundFlats.v[i].binspat, foundFlats.v[i].binspec, foundFlats.v[i].slitw, opt.slit_tol);

        if(reqBins.n>1) qsort(reqBins.v,(size_t)reqBins.n,sizeof(BinGroup),cmp_bin_group);
        if(reqFlats.n>1) qsort(reqFlats.v,(size_t)reqFlats.n,sizeof(FlatGroup),cmp_flat_group);

        
        if(opt.debug && first_loop){
            debug_print_requirements(&reqBins, &reqFlats, csv_ok, inferred_from_sci, using_detected_fallback);
        }
render_dashboard(opt.dirPath, opt.csvPath, csv_ok, inferred_from_sci, using_detected_fallback,
                         &reqBins, &reqFlats, &foundBins, &foundFlats, opt.slit_tol, nscan, nmatch, &supp, do_clear);

        binvec_free(&foundBins); flatvec_free(&foundFlats);
        binvec_free(&sciBins);   flatvec_free(&sciFlats);

        if(opt.once) break;

        bool quit=false;
        sleep_or_key(opt.refresh_sec, &quit, enable_keys);
        if(quit) break;

        first_loop=false;
    }

    term_restore();
    binvec_free(&reqBins);
    flatvec_free(&reqFlats);
    return 0;
}
