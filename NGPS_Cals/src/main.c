// ngps_cals_status_v3.c
// Terminal status dashboard for NGPS calibration completeness (multi-extension NGPS FITS).
//
// v3 updates (Jan 2026):
//  - Robust CSV parsing (handles empty fields ",,", quoted fields, and BINSPECT column name)
//  - Science counting: treat any non-cal IMGTYPE as SCI, and DO NOT apply DBIAS gating to SCI
//  - DBIAS gating applies ONLY to calibrations (THAR/FEAR/BIAS/DOMEFLAT)
//  - U/G calibration validity requires R & I detectors OFF (per-extension DBIAS)
//  - If requirements from --csv (or SCI inference) are empty, fall back to displaying detected setups
//  - Adds --debug to print diagnostics about CSV ingestion and scan grouping
//
// Build:
//   gcc -O2 -Wall -Wextra -std=c11 -o ngps_cals_status ngps_cals_status_v3.c -lm
//
// Examples:
//   ./ngps_cals_status --dir /data/latest
//   ./ngps_cals_status --dir /data/latest --csv ngps_20260128.csv --night 20260128
//   ./ngps_cals_status --dir /data/latest --csv ngps_20260128.csv --debug --once

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
static const char *C_YELL  = "\033[33m";
static const char *C_RED   = "\033[31m";
static const char *C_DIM   = "\033[2m";

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
// Night labeling (Palomar local time)
// ------------------------------
static bool parse_date_obs_utc(const char *s, time_t *out_utc){
    if(!s || !*s) return false;
    int Y=0,M=0,D=0,h=0,m=0;
    double sec=0.0;
    int n = sscanf(s, "%d-%d-%dT%d:%d:%lf", &Y,&M,&D,&h,&m,&sec);
    if(n<3) n = sscanf(s, "%d-%d-%d %d:%d:%lf", &Y,&M,&D,&h,&m,&sec);
    if(n<3) return false;
    if(n==3){ h=0; m=0; sec=0.0; }
    struct tm t = {0};
    t.tm_year = Y-1900; t.tm_mon = M-1; t.tm_mday = D;
    t.tm_hour = h; t.tm_min = m; t.tm_sec = (int)floor(sec+1e-9);
#ifdef __USE_GNU
    time_t tt = timegm(&t);
#else
    char *old = getenv("TZ");
    setenv("TZ","UTC",1); tzset();
    time_t tt = mktime(&t);
    if(old) setenv("TZ", old, 1); else unsetenv("TZ");
    tzset();
#endif
    if(tt==(time_t)-1) return false;
    *out_utc = tt;
    return true;
}

static int yyyymmdd_from_local_night(time_t utc){
    struct tm lt;
    localtime_r(&utc, &lt);
    if(lt.tm_hour < 12){
        utc -= 86400;
        localtime_r(&utc, &lt);
    }
    int y = lt.tm_year + 1900;
    int mo = lt.tm_mon + 1;
    int d = lt.tm_mday;
    return y*10000 + mo*100 + d;
}

static void fmt_date_yyyymmdd(int night_id, char out[16]){
    int y = night_id/10000;
    int m = (night_id/100)%100;
    int d = night_id%100;
    snprintf(out,16,"%04d-%02d-%02d",y,m,d);
}

// ------------------------------
// FITS header parser (header-only)
// ------------------------------
typedef struct {
    // keys we care about
    char IMGTYPE[32];
    char DATEOBS[64];
    int BINSPAT;
    int BINSPEC;
    double SLITW;
    char SPEC_ID[32];
    double DBIAS;

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
    h->DBIAS = NAN;
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
    if(*val=='\''){ // quoted
        val++;
        char tmp[256]={0};
        size_t i=0;
        while(*val && *val!='\'' && i<sizeof(tmp)-1) tmp[i++]=*val++;
        tmp[i]=0;
        trim(tmp);
        snprintf(out,outsz,"%s",tmp);
    } else {
        char tmp[256]={0};
        snprintf(tmp,sizeof(tmp),"%s",val);
        trim(tmp);
        snprintf(out,outsz,"%s",tmp);
    }
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
    } else if(str_ieq(key,"DATE-OBS") || str_ieq(key,"DATEOBS")){
        parse_value_string(valbuf, h->DATEOBS, sizeof(h->DATEOBS));
    } else if(str_ieq(key,"BINSPAT")){
        h->BINSPAT = (int)parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"BINSPEC")){
        h->BINSPEC = (int)parse_value_i64(valbuf,&ok);
    } else if(str_ieq(key,"SLITW") || str_ieq(key,"SLITWIDTH") || str_ieq(key,"SLITWDTH")){
        h->SLITW = parse_value_double(valbuf,&ok);
    } else if(str_ieq(key,"SPEC_ID")){
        parse_value_string(valbuf, h->SPEC_ID, sizeof(h->SPEC_ID));
    } else if(str_ieq(key,"DBIAS")){
        h->DBIAS = parse_value_double(valbuf,&ok);
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

static bool header_is_image_like(const FitsHdr *h){
    if(h->NAXIS < 2) return false;
    if(h->XTENSION[0]==0) return true;
    if(str_ieq(h->XTENSION,"IMAGE")) return true;
    return false;
}

// ------------------------------
// IMGTYPE normalization
// - Cal types are explicit
// - Anything else is SCI (per your request)
// ------------------------------
static void normalize_imgtype(const char *in, char out[16]){
    char tmp[64]={0};
    snprintf(tmp,sizeof(tmp),"%s", in?in:"");
    trim(tmp);
    strtoupper_inplace(tmp);

    if(str_icontains(tmp,"THAR")) { strncpy(out,"THAR",16); return; }
    if(str_icontains(tmp,"FEAR")) { strncpy(out,"FEAR",16); return; }
    if(str_icontains(tmp,"BIAS")) { strncpy(out,"BIAS",16); return; }
    if(str_icontains(tmp,"DOMEFLAT") || (str_icontains(tmp,"DOME") && str_icontains(tmp,"FLAT"))) {
        strncpy(out,"DOMEFLAT",16); return;
    }
    // Treat everything else as science for now
    strncpy(out,"SCI",16);
}

static bool is_cal_type(const char *imgtype){
    return (strcmp(imgtype,"THAR")==0 || strcmp(imgtype,"FEAR")==0 || strcmp(imgtype,"BIAS")==0 || strcmp(imgtype,"DOMEFLAT")==0);
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
    double dbias;
    bool det_on;
    char imgtype[16];
} ChanMeta;

typedef struct {
    bool ok;
    int night_id; // local night label

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
    c->dbias=NAN;
    c->det_on=true;
    strncpy(c->imgtype,"SCI",sizeof(c->imgtype));
}

static FileMeta scan_fits_file_multi(const char *path){
    FileMeta out;
    memset(&out,0,sizeof(out));
    out.ok=false;
    out.night_id=0;
    strncpy(out.base_imgtype,"SCI",sizeof(out.base_imgtype));
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

        // Primary HDU
        if(hdu==0){
            if(hdr.DATEOBS[0]){
                time_t utc;
                if(parse_date_obs_utc(hdr.DATEOBS,&utc)) out.night_id = yyyymmdd_from_local_night(utc);
            }
            if(hdr.IMGTYPE[0]) normalize_imgtype(hdr.IMGTYPE, out.base_imgtype);
            if(hdr.BINSPAT>0) out.base_binspat = hdr.BINSPAT;
            if(hdr.BINSPEC>0) out.base_binspec = hdr.BINSPEC;
            if(isfinite(hdr.SLITW)) out.base_slitw = hdr.SLITW;
        }

        // Image-like extensions are per channel
        if(hdu>0 && header_is_image_like(&hdr)){
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

                // dbias
                cm->dbias = hdr.DBIAS;

                // detector on/off from DBIAS: missing => assume ON; else DBIAS>0 => ON
                if(isfinite(cm->dbias)) cm->det_on = (cm->dbias > 0.0);
                else cm->det_on = true;
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
// Night list
// ------------------------------
typedef struct { int night_id; int count; } NightCount;

typedef struct { NightCount *v; int n, cap; } NightVec;

static void nightvec_free(NightVec *a){ free(a->v); a->v=NULL; a->n=a->cap=0; }

static void nightvec_add(NightVec *a, int night_id){
    for(int i=0;i<a->n;i++) if(a->v[i].night_id==night_id){ a->v[i].count++; return; }
    if(a->n==a->cap){
        a->cap = a->cap? a->cap*2 : 16;
        a->v = (NightCount*)realloc(a->v, (size_t)a->cap*sizeof(NightCount));
        if(!a->v){ perror("realloc"); exit(2);}
    }
    a->v[a->n].night_id = night_id;
    a->v[a->n].count = 1;
    a->n++;
}

static int nightvec_pick_mode(const NightVec *a){
    int best_id=0, best_c=0;
    for(int i=0;i<a->n;i++) if(a->v[i].count > best_c){ best_c=a->v[i].count; best_id=a->v[i].night_id; }
    return best_id;
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
static void scan_dir_collect_nights(const char *dirPath, NightVec *nights){
    DIR *dp = opendir(dirPath);
    if(!dp) return;
    struct dirent *de;
    while((de=readdir(dp))){
        if(de->d_name[0]=='.') continue;
        if(!is_fits_name(de->d_name)) continue;
        char full[4096];
        snprintf(full,sizeof(full),"%s/%s",dirPath,de->d_name);
        FileMeta m = scan_fits_file_multi(full);
        if(m.night_id>0) nightvec_add(nights, m.night_id);
    }
    closedir(dp);
}

typedef struct {
    int ug_suppressed[2]; // [U,G] cal channel-frames skipped due to R/I not both OFF
} SuppressStats;

typedef struct {
    int files_ok;
    int type_counts[CH_N][6];
    // type idx: 0 THAR,1 FEAR,2 BIAS,3 DOMEFLAT,4 SCI,5 OTHER(unused)
    int ch_present[CH_N];
    int ch_det_on[CH_N];
} ScanStats;

static int type_index(const char *imgtype){
    if(strcmp(imgtype,"THAR")==0) return 0;
    if(strcmp(imgtype,"FEAR")==0) return 1;
    if(strcmp(imgtype,"BIAS")==0) return 2;
    if(strcmp(imgtype,"DOMEFLAT")==0) return 3;
    if(strcmp(imgtype,"SCI")==0) return 4;
    return 5;
}

static void scan_dir_counts(
    const char *dirPath,
    int night_id_filter,
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

        if(night_id_filter>0 && m.night_id!=night_id_filter) continue;
        if(nFilesMatched) (*nFilesMatched)++;

        bool ri_off = (m.ch[CH_R].present && !m.ch[CH_R].det_on) && (m.ch[CH_I].present && !m.ch[CH_I].det_on);

        for(int ch=0; ch<CH_N; ch++){
            ChanMeta *cm = &m.ch[ch];
            if(!cm->present) continue;
            if(cm->binspat<=0 || cm->binspec<=0) continue;

            if(scanStats){
                scanStats->ch_present[ch]++;
                if(cm->det_on) scanStats->ch_det_on[ch]++;
                int ti = type_index(cm->imgtype);
                if(ti>=0 && ti<6) scanStats->type_counts[ch][ti]++;
            }

            bool is_cal = is_cal_type(cm->imgtype);

            // SCI handling: ignore DBIAS and ignore R/I-off constraints
            if(!is_cal){
                int bi = binvec_find_or_add(foundBins, cm->binspat, cm->binspec);
                foundBins->v[bi].sci[ch]++;

                int sbi = binvec_find_or_add(sciBins, cm->binspat, cm->binspec);
                sciBins->v[sbi].sci[ch]++;

                if(isfinite(cm->slitw)) (void)flatvec_find_or_add(sciFlats, cm->binspat, cm->binspec, cm->slitw, slit_tol);
                continue;
            }

            // CAL handling: apply DBIAS gating and U/G R&I-off requirement
            if(!cm->det_on) continue;

            bool need_ri_off = (ch==CH_U || ch==CH_G);
            if(need_ri_off && !ri_off){
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

static void print_count_cell(int have, int req, bool tty){
    if(have >= req) printf("%s%2d/%-2d%s", tty?C_GREEN:"", have, req, tty?C_RESET:"");
    else if(have > 0) printf("%s%2d/%-2d%s", tty?C_YELL:"", have, req, tty?C_RESET:"");
    else printf("%s%2d/%-2d%s", tty?C_RED:"", have, req, tty?C_RESET:"");
}

static void render_dashboard(
    const char *dirPath,
    int night_id,
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
    bool tty = is_tty_stdout();
    if(do_clear) clear_screen();

    time_t now=time(NULL);
    struct tm lt; localtime_r(&now,&lt);
    char tbuf[64]; strftime(tbuf,sizeof(tbuf),"%Y-%m-%d %H:%M:%S %Z",&lt);

    char nbuf[16]; fmt_date_yyyymmdd(night_id, nbuf);

    printf("NGPS calibration status (multi-ext)  %s\n", tbuf);
    printf("Directory: %s\n", dirPath);
    printf("Night label: %s   (files scanned: %d, matched night: %d)\n", nbuf, nscan, nmatch);
    printf("Requirements per setup & per channel: THAR=%d FEAR=%d BIAS=%d DOMEFLAT=%d\n", REQ_THAR, REQ_FEAR, REQ_BIAS, REQ_DOMEFLAT);
    printf("U/G cal counts only include cal frames where R & I detectors are OFF (R.DBias<=0 AND I.DBias<=0).\n");
    printf("Flat slit match tolerance: %.2f\"\n", slit_tol);

    if(csvPath){
        printf("CSV: %s  [%s]\n", csvPath, csv_ok?"ok":"FAILED");
    } else {
        printf("CSV: (none)\n");
    }

    if(inferred_from_sci) printf("Required setups: inferred from SCI frames\n");
    if(using_detected_fallback) printf("Required setups: showing detected setups (no CSV/inference setups found)\n");

    if(supp){
        printf("%sSuppressed U/G cal channel-frames (IMGTYPE ok but R/I not both OFF): U=%d, G=%d%s\n",
               tty?C_DIM:"", supp->ug_suppressed[0], supp->ug_suppressed[1], tty?C_RESET:"");
    }
    printf("\n");

    // ---- Arcs/Bias by binning ----
    printf("== Arcs/Bias by binning (BINSPAT x BINSPEC) ==\n");
    printf("%-8s %-4s  %-16s  %-16s  %-16s  %-6s\n", "Binning", "Ch", "THAR", "FEAR", "BIAS", "SCI");
    printf("-------- ----  ----------------  ----------------  ----------------  ------\n");

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

            if(ch==0) printf("%2dx%-5d ", bs, bc);
            else      printf("%8s ", "");

            printf("%-4s  ", CH_NAME[ch]);

            print_count_cell(have_thar, REQ_THAR, tty);
            printf("%s(%d<=2\")%s  ", tty?C_DIM:"", good_thar, tty?C_RESET:"");

            print_count_cell(have_fear, REQ_FEAR, tty);
            printf("%s(%d<=2\")%s  ", tty?C_DIM:"", good_fear, tty?C_RESET:"");

            print_count_cell(have_bias, REQ_BIAS, tty);
            printf("  ");

            printf("%d", have_sci);
            printf("\n");
        }
        printf("\n");
    }

    if(reqBins->n==0){
        printf("%s(no required binnings found)%s\n\n", tty?C_DIM:"", tty?C_RESET:"");
    }

    // ---- Flats by setup ----
    printf("== Dome flats by setup (BINSPAT x BINSPEC, SLITW) ==\n");
    printf("%-16s %-4s  %-16s\n", "Setup", "Ch", "DOMEFLAT");
    printf("---------------- ----  ----------------\n");

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

            char label[64];
            snprintf(label,sizeof(label),"%dx%d slit %.2f\"",bs,bc,sw);

            if(ch==0) printf("%-16s ", label);
            else      printf("%16s ", "");

            printf("%-4s  ", CH_NAME[ch]);
            print_count_cell(have_flat, REQ_DOMEFLAT, tty);
            printf("\n");
        }
        printf("\n");
    }

    if(reqFlats->n==0){
        printf("%s(no required dome-flat setups found)%s\n\n", tty?C_DIM:"", tty?C_RESET:"");
    }

    printf("Summary (complete setups / required setups):\n");
    for(int ch=0; ch<CH_N; ch++){
        printf("  %s: arcs/bias %d/%d, domeflats %d/%d\n", CH_NAME[ch], complete_by_ch_bins[ch], reqBins->n, complete_by_ch_flats[ch], reqFlats->n);
    }

    printf("\nKeys: q=quit  r=refresh now\n");
    fflush(stdout);
}

// ------------------------------
// Options
// ------------------------------
typedef struct {
    const char *dirPath;
    const char *csvPath;
    int night_id;
    int refresh_sec;
    bool once;
    double slit_tol;
    double default_slitw;
    bool infer_from_sci_if_no_csv;
    bool debug;
} Options;

static void usage(const char *argv0){
    printf("Usage: %s [options]\n\n", argv0);
    printf("Options:\n");
    printf("  --dir PATH              Directory to scan (default: /data/latest)\n");
    printf("  --night YYYYMMDD         Night label (local). If omitted, auto-picks mode night in dir\n");
    printf("  --csv FILE.csv           Observing plan CSV with BINSPAT,(BINSPEC|BINSPECT)[,SLITW|SLITWIDTH]\n");
    printf("  --refresh N              Refresh every N seconds (default: 5)\n");
    printf("  --once                   Print once and exit\n");
    printf("  --slit-tol X             Slit match tolerance in arcsec (default: 0.05)\n");
    printf("  --default-slit X         If CSV has no slit column, assume this slit (default: 1.50)\n");
    printf("  --no-infer-sci           If no CSV (or CSV fails), do not infer required setups from SCI frames\n");
    printf("  --debug                  Print debug diagnostics (CSV columns, row parsing, scan stats)\n");
    printf("  -h, --help               Show this help\n");
}

static Options parse_args(int argc, char **argv){
    Options o={0};
    o.dirPath = "/data/latest";
    o.csvPath = NULL;
    o.night_id = 0;
    o.refresh_sec = 5;
    o.once = false;
    o.slit_tol = 0.05;
    o.default_slitw = 1.50;
    o.infer_from_sci_if_no_csv = true;
    o.debug = false;

    for(int i=1;i<argc;i++){
        const char *a=argv[i];
        if(strcmp(a,"--dir")==0 && i+1<argc){ o.dirPath=argv[++i]; continue; }
        if(strcmp(a,"--csv")==0 && i+1<argc){ o.csvPath=argv[++i]; continue; }
        if(strcmp(a,"--night")==0 && i+1<argc){ o.night_id=atoi(argv[++i]); continue; }
        if(strcmp(a,"--refresh")==0 && i+1<argc){ o.refresh_sec=atoi(argv[++i]); continue; }
        if(strcmp(a,"--once")==0){ o.once=true; continue; }
        if(strcmp(a,"--slit-tol")==0 && i+1<argc){ o.slit_tol=atof(argv[++i]); continue; }
        if(strcmp(a,"--default-slit")==0 && i+1<argc){ o.default_slitw=atof(argv[++i]); continue; }
        if(strcmp(a,"--no-infer-sci")==0){ o.infer_from_sci_if_no_csv=false; continue; }
        if(strcmp(a,"--debug")==0){ o.debug=true; continue; }
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
    fprintf(stderr,"[debug] Scan ok files: %d\n", ss->files_ok);
    for(int ch=0; ch<CH_N; ch++){
        fprintf(stderr,"[debug]  %s: present=%d det_on=%d  types: THAR=%d FEAR=%d BIAS=%d DOMEFLAT=%d SCI=%d\n",
                CH_NAME[ch], ss->ch_present[ch], ss->ch_det_on[ch],
                ss->type_counts[ch][0], ss->type_counts[ch][1], ss->type_counts[ch][2], ss->type_counts[ch][3], ss->type_counts[ch][4]);
    }
}

int main(int argc, char **argv){
    // Ensure Palomar local time
    setenv("TZ","America/Los_Angeles",1);
    tzset();

    Options opt = parse_args(argc, argv);

    // Auto-pick night if needed
    NightVec nights={0};
    if(opt.night_id==0){
        scan_dir_collect_nights(opt.dirPath, &nights);
        opt.night_id = nightvec_pick_mode(&nights);
    }

    // Read requirements from CSV (if given)
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

        scan_dir_counts(opt.dirPath, opt.night_id, &foundBins, &foundFlats, &sciBins, &sciFlats,
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

        if(reqBins.n>1) qsort(reqBins.v,(size_t)reqBins.n,sizeof(BinGroup),cmp_bin_group);
        if(reqFlats.n>1) qsort(reqFlats.v,(size_t)reqFlats.n,sizeof(FlatGroup),cmp_flat_group);

        render_dashboard(opt.dirPath, opt.night_id, opt.csvPath, csv_ok, inferred_from_sci, using_detected_fallback,
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
    nightvec_free(&nights);
    binvec_free(&reqBins);
    flatvec_free(&reqFlats);
    return 0;
}
