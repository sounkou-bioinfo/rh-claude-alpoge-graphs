/*
 * rhgraph: dependency graph of a lean4export 3.x NDJSON stream.
 *
 * Reads the export on stdin, keeps the expression DAG in memory, and writes to
 * OUTDIR:
 *   names.tsv    name_id, full name, kind      (every declared name and every
 *                                               name referenced in the closure)
 *   closure.tsv  name_id of each declaration block in the closure of ROOT
 *   edges.tsv    decl_name_id, dep_name_id    (constants occurring directly in
 *                                               the type/value/rules of decl)
 *   projs.tsv    decl_name_id, struct_name_id, field_idx
 *   stats.txt    counts
 *
 * The closure walks from the ROOT declarations through constant references. Referencing any
 * name of an inductive block (type, constructor, recursor) pulls in the whole
 * block, which over-approximates what the kernel needs.
 *
 * Usage: zstd -dc --long=31 solution.ndjson.zst | rhgraph OUTDIR ROOT...
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define MAXE (1ULL << 31)

enum { K_NONE, K_LEAF, K_APP, K_BIND, K_LET, K_CONST, K_PROJ, K_MDATA };

static uint8_t *ekind;
static uint32_t *ec0, *ec1;
static uint64_t emax;

typedef struct { uint32_t *v; size_t n, cap; } vec32;
static void vpush(vec32 *a, uint32_t x)
{
    if (a->n == a->cap) {
        a->cap = a->cap ? a->cap * 2 : 1024;
        a->v = realloc(a->v, a->cap * sizeof(uint32_t));
        if (!a->v) { perror("realloc"); exit(1); }
    }
    a->v[a->n++] = x;
}

static vec32 let_id, let_val;           /* letE value child, ids increasing */
static vec32 proj_tn, proj_idx;         /* proj side table, indexed by ec1 */

/* names */
static uint32_t *npre, *nnum;
static uint64_t *nstr;                  /* offset+1 into strbuf, 0 = numeric */
static uint8_t *nisnum;
static size_t ncap;
static char *strbuf; static size_t strlen_, strcap;

/* declarations */
typedef struct { uint32_t name; uint8_t kind; uint32_t r0, rn; } decl_t;
static decl_t *decls; static size_t ndecl, declcap;
static vec32 roots;
static uint32_t *declof;                /* name id -> decl index + 1 */

static const char *kindname[] = { "?", "axiom", "def", "thm", "opaque", "quot", "inductive" };

static void name_grow(uint64_t id)
{
    if (id < ncap) return;
    size_t nc = ncap ? ncap : 1 << 20;
    while (nc <= id) nc *= 2;
    npre = realloc(npre, nc * sizeof *npre);
    nnum = realloc(nnum, nc * sizeof *nnum);
    nstr = realloc(nstr, nc * sizeof *nstr);
    nisnum = realloc(nisnum, nc);
    declof = realloc(declof, nc * sizeof *declof);
    if (!npre || !nnum || !nstr || !nisnum || !declof) { perror("realloc"); exit(1); }
    memset(npre + ncap, 0, (nc - ncap) * sizeof *npre);
    memset(nstr + ncap, 0, (nc - ncap) * sizeof *nstr);
    memset(nisnum + ncap, 0, nc - ncap);
    memset(declof + ncap, 0, (nc - ncap) * sizeof *declof);
    ncap = nc;
}

static uint64_t num_after(const char *s, const char *key)
{
    const char *p = strstr(s, key);
    if (!p) { fprintf(stderr, "missing %s in: %.200s\n", key, s); exit(2); }
    return strtoull(p + strlen(key), NULL, 10);
}

static void set_expr(uint64_t id, uint8_t k, uint32_t a, uint32_t b)
{
    if (id >= MAXE) { fprintf(stderr, "expr id %llu over capacity\n", (unsigned long long)id); exit(3); }
    ekind[id] = k; ec0[id] = a; ec1[id] = b;
    if (id + 1 > emax) emax = id + 1;
}

static void add_name_str(uint64_t id, uint32_t pre, const char *q)
{
    name_grow(id);
    npre[id] = pre;
    const char *e = q;
    while (*e && !(*e == '"' && e[-1] != '\\')) e++;
    size_t len = (size_t)(e - q);
    if (strlen_ + len + 1 > strcap) {
        strcap = (strcap ? strcap : 1 << 24);
        while (strlen_ + len + 1 > strcap) strcap *= 2;
        strbuf = realloc(strbuf, strcap);
        if (!strbuf) { perror("realloc"); exit(1); }
    }
    memcpy(strbuf + strlen_, q, len);
    strbuf[strlen_ + len] = 0;
    nstr[id] = strlen_ + 1;
    strlen_ += len + 1;
}

static void scan_all(const char *s, const char *key, vec32 *out)
{
    size_t kl = strlen(key);
    for (const char *p = strstr(s, key); p; p = strstr(p + kl, key))
        vpush(out, (uint32_t)strtoull(p + kl, NULL, 10));
}

static void add_decl(uint8_t kind, const char *line)
{
    vec32 nm = {0}, rt = {0};
    if (kind == 6) {
        scan_all(line, "\"name\":", &nm);
        scan_all(line, "\"type\":", &rt);
        scan_all(line, "\"rhs\":", &rt);
    } else {
        vpush(&nm, (uint32_t)num_after(line, "\"name\":"));
        vpush(&rt, (uint32_t)num_after(line, "\"type\":"));
        if (kind == 2 || kind == 3 || kind == 4)
            vpush(&rt, (uint32_t)num_after(line, "\"value\":"));
    }
    if (ndecl == declcap) {
        declcap = declcap ? declcap * 2 : 1 << 16;
        decls = realloc(decls, declcap * sizeof *decls);
    }
    uint32_t primary = nm.v[0];
    if (kind == 6) {
        const char *t = strstr(line, "\"types\":[");
        if (!t) { fprintf(stderr, "inductive without types: %.200s\n", line); exit(2); }
        primary = (uint32_t)num_after(t, "\"name\":");
    }
    decl_t *d = &decls[ndecl];
    d->name = primary; d->kind = kind; d->r0 = (uint32_t)roots.n; d->rn = (uint32_t)rt.n;
    for (size_t i = 0; i < rt.n; i++) vpush(&roots, rt.v[i]);
    for (size_t i = 0; i < nm.n; i++) {
        name_grow(nm.v[i]);
        declof[nm.v[i]] = (uint32_t)(ndecl + 1);
    }
    ndecl++;
    free(nm.v); free(rt.v);
}

static uint32_t let_value(uint32_t id)
{
    size_t lo = 0, hi = let_id.n;
    while (lo < hi) {
        size_t m = (lo + hi) / 2;
        if (let_id.v[m] < id) lo = m + 1; else hi = m;
    }
    if (lo == let_id.n || let_id.v[lo] != id) { fprintf(stderr, "letE %u missing\n", id); exit(4); }
    return let_val.v[lo];
}

static void parse_line(char *s)
{
    if (s[0] != '{' || s[1] != '"') { fprintf(stderr, "bad line: %.200s\n", s); exit(2); }
    const char *k = s + 2;
#define IS(lit) (strncmp(k, lit, sizeof(lit) - 1) == 0)
    if (IS("ie\":")) {
        uint64_t id = strtoull(k + 4, NULL, 10);
        const char *q = strchr(k, ',');
        if (!q) return;
        q += 2;
        if (!strncmp(q, "lam\"", 4)) {
            set_expr(id, K_BIND, (uint32_t)num_after(q, "\"type\":"), (uint32_t)num_after(q, "\"body\":"));
        } else if (!strncmp(q, "letE\"", 5)) {
            set_expr(id, K_LET, (uint32_t)num_after(q, "\"type\":"), (uint32_t)num_after(q, "\"body\":"));
            if (let_id.n && let_id.v[let_id.n - 1] >= id) { fprintf(stderr, "letE ids not increasing\n"); exit(4); }
            vpush(&let_id, (uint32_t)id);
            vpush(&let_val, (uint32_t)num_after(q, "\"value\":"));
        } else if (!strncmp(q, "proj\"", 5)) {
            vpush(&proj_tn, (uint32_t)num_after(q, "\"typeName\":"));
            vpush(&proj_idx, (uint32_t)num_after(q, "\"idx\":"));
            set_expr(id, K_PROJ, (uint32_t)num_after(q, "\"struct\":"), (uint32_t)(proj_tn.n - 1));
        } else if (!strncmp(q, "mdata\"", 6)) {
            const char *p = NULL, *t;
            for (t = strstr(q, "\"expr\":"); t; t = strstr(t + 7, "\"expr\":")) p = t;
            if (!p) { fprintf(stderr, "mdata without expr: %.200s\n", s); exit(2); }
            set_expr(id, K_MDATA, (uint32_t)strtoull(p + 7, NULL, 10), 0);
        } else {
            set_expr(id, K_LEAF, 0, 0);     /* natVal, sort, strVal */
        }
    } else if (IS("app\":")) {
        set_expr(num_after(s, "\"ie\":"), K_APP, (uint32_t)num_after(s, "\"fn\":"), (uint32_t)num_after(s, "\"arg\":"));
    } else if (IS("forallE\":")) {
        const char *p = strrchr(s, '}');
        (void)p;
        const char *ie = strstr(s, "},\"ie\":");
        if (!ie) { fprintf(stderr, "forallE ie: %.200s\n", s); exit(2); }
        set_expr(strtoull(ie + 7, NULL, 10), K_BIND, (uint32_t)num_after(s, "\"type\":"), (uint32_t)num_after(s, "\"body\":"));
    } else if (IS("const\":")) {
        set_expr(num_after(s, "\"ie\":"), K_CONST, (uint32_t)num_after(s, "\"name\":"), 0);
    } else if (IS("bvar\":")) {
        set_expr(num_after(s, "\"ie\":"), K_LEAF, 0, 0);
    } else if (IS("in\":")) {
        uint64_t id = strtoull(k + 4, NULL, 10);
        if (strstr(s, ",\"num\":")) {
            name_grow(id);
            npre[id] = (uint32_t)num_after(s, "\"pre\":");
            nnum[id] = (uint32_t)num_after(s, "\"i\":");
            nisnum[id] = 1;
        } else {
            const char *p = strstr(s, "\"pre\":");
            uint32_t pre = (uint32_t)strtoull(p + 6, NULL, 10);
            const char *q = strstr(p, "\"str\":\"");
            if (!q) { fprintf(stderr, "name: %.200s\n", s); exit(2); }
            add_name_str(id, pre, q + 7);
        }
    } else if (IS("il\":") || IS("meta\":")) {
        return;
    } else if (IS("def\":")) add_decl(2, s);
    else if (IS("thm\":")) add_decl(3, s);
    else if (IS("opaque\":")) add_decl(4, s);
    else if (IS("axiom\":")) add_decl(1, s);
    else if (IS("quot\":")) add_decl(5, s);
    else if (IS("inductive\":")) add_decl(6, s);
    else { fprintf(stderr, "unknown record: %.200s\n", s); exit(2); }
#undef IS
}

static void fullname(uint32_t id, char *buf, size_t cap)
{
    uint32_t chain[256]; int n = 0;
    while (id && n < 256) { chain[n++] = id; id = npre[id]; }
    size_t len = 0;
    buf[0] = 0;
    for (int i = n - 1; i >= 0; i--) {
        uint32_t c = chain[i];
        char part[32];
        const char *t = nisnum[c] ? (snprintf(part, sizeof part, "%u", nnum[c]), part)
                                  : (nstr[c] ? strbuf + nstr[c] - 1 : "?");
        int w = snprintf(buf + len, cap - len, "%s%s", len ? "." : "", t);
        if (w < 0 || (size_t)w >= cap - len) { buf[cap - 1] = 0; return; }
        len += (size_t)w;
    }
}

/* epoch-stamped DAG walk collecting const names and projections */
static uint32_t *seen, epoch;
static vec32 stack;

static void walk(uint32_t r, vec32 *consts, vec32 *projs)
{
    stack.n = 0;
    vpush(&stack, r);
    while (stack.n) {
        uint32_t e = stack.v[--stack.n];
        if (seen[e] == epoch) continue;
        seen[e] = epoch;
        switch (ekind[e]) {
        case K_APP: case K_BIND: vpush(&stack, ec0[e]); vpush(&stack, ec1[e]); break;
        case K_LET: vpush(&stack, ec0[e]); vpush(&stack, ec1[e]); vpush(&stack, let_value(e)); break;
        case K_MDATA: vpush(&stack, ec0[e]); break;
        case K_PROJ: vpush(&stack, ec0[e]); if (projs) vpush(projs, ec1[e]); break;
        case K_CONST: vpush(consts, ec0[e]); break;
        case K_LEAF: break;
        default: fprintf(stderr, "expr %u undefined\n", e); exit(5);
        }
    }
}

int main(int argc, char **argv)
{
    if (argc < 3) { fprintf(stderr, "usage: rhgraph OUTDIR ROOT...\n"); return 1; }
    const char *out = argv[1];
    ekind = mmap(NULL, MAXE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    ec0 = mmap(NULL, MAXE * 4, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    ec1 = mmap(NULL, MAXE * 4, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (ekind == MAP_FAILED || ec0 == MAP_FAILED || ec1 == MAP_FAILED) { perror("mmap"); return 1; }

    char *line = NULL; size_t lcap = 0; ssize_t len; uint64_t nlines = 0;
    while ((len = getline(&line, &lcap, stdin)) > 0) {
        parse_line(line);
        if (++nlines % 100000000 == 0) fprintf(stderr, "lines %llu exprs %llu decls %zu\n",
            (unsigned long long)nlines, (unsigned long long)emax, ndecl);
    }
    fprintf(stderr, "parsed: lines %llu exprs %llu decls %zu names %zu\n",
            (unsigned long long)nlines, (unsigned long long)emax, ndecl, ncap);

    /* resolve roots */
    static char buf[4096];
    int nroots = argc - 2;
    uint32_t *rootdecl = calloc((size_t)nroots, sizeof *rootdecl);
    for (size_t i = 0; i < ndecl; i++) {
        fullname(decls[i].name, buf, sizeof buf);
        for (int r = 0; r < nroots; r++)
            if (!strcmp(buf, argv[2 + r])) rootdecl[r] = (uint32_t)(i + 1);
    }
    for (int r = 0; r < nroots; r++)
        if (!rootdecl[r]) { fprintf(stderr, "root %s not found\n", argv[2 + r]); return 6; }

    seen = mmap(NULL, MAXE * 4, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (seen == MAP_FAILED) { perror("mmap"); return 1; }

    /* closure over declaration blocks */
    uint8_t *inclos = calloc(ndecl + 1, 1);
    uint8_t *nameref = calloc(ncap, 1);
    vec32 queue = {0}, consts = {0};
    for (int r = 0; r < nroots; r++)
        if (!inclos[rootdecl[r]]) { inclos[rootdecl[r]] = 1; vpush(&queue, rootdecl[r]); }
    epoch = 1;                                   /* one global epoch: shared nodes visited once */
    for (size_t qi = 0; qi < queue.n; qi++) {
        decl_t *d = &decls[queue.v[qi] - 1];
        for (uint32_t i = 0; i < d->rn; i++) {
            consts.n = 0;
            walk(roots.v[d->r0 + i], &consts, NULL);
            for (size_t j = 0; j < consts.n; j++) {
                uint32_t nm = consts.v[j];
                nameref[nm] = 1;
                uint32_t di = nm < ncap ? declof[nm] : 0;
                if (!di) { fprintf(stderr, "const name %u has no declaration\n", nm); return 7; }
                if (!inclos[di]) { inclos[di] = 1; vpush(&queue, di); }
            }
        }
    }
    fprintf(stderr, "closure: %zu declaration blocks\n", queue.n);

    char path[1024];
    snprintf(path, sizeof path, "%s/closure.tsv", out);
    FILE *fc = fopen(path, "w");
    snprintf(path, sizeof path, "%s/edges.tsv", out);
    FILE *fe = fopen(path, "w");
    snprintf(path, sizeof path, "%s/projs.tsv", out);
    FILE *fp = fopen(path, "w");
    if (!fc || !fe || !fp) { perror("fopen"); return 1; }

    /* direct dependencies per declaration in the closure */
    uint32_t *lastdep = calloc(ncap, sizeof(uint32_t));
    vec32 projs = {0};
    uint64_t nedges = 0, nproj = 0;
    for (size_t qi = 0; qi < queue.n; qi++) {
        uint32_t di = queue.v[qi];
        decl_t *d = &decls[di - 1];
        fprintf(fc, "%u\n", d->name);
        epoch++;
        if (epoch == 0) { memset(seen, 0, emax * 4); epoch = 1; }
        consts.n = 0; projs.n = 0;
        for (uint32_t i = 0; i < d->rn; i++) walk(roots.v[d->r0 + i], &consts, &projs);
        for (size_t j = 0; j < consts.n; j++) {
            uint32_t nm = consts.v[j];
            if (lastdep[nm] == di) continue;
            lastdep[nm] = di;
            fprintf(fe, "%u\t%u\n", d->name, nm);
            nedges++;
        }
        for (size_t j = 0; j < projs.n; j++) {
            fprintf(fp, "%u\t%u\t%u\n", d->name, proj_tn.v[projs.v[j]], proj_idx.v[projs.v[j]]);
            nproj++;
        }
    }
    fclose(fc); fclose(fe); fclose(fp);

    /* names: every declared name, plus referenced ones */
    snprintf(path, sizeof path, "%s/names.tsv", out);
    FILE *fn = fopen(path, "w");
    for (size_t id = 1; id < ncap; id++) {
        uint32_t di = declof[id];
        if (!di && !nameref[id]) continue;
        fullname((uint32_t)id, buf, sizeof buf);
        for (char *c = buf; *c; c++) if (*c == '\t' || *c == '\n') *c = ' ';
        fprintf(fn, "%zu\t%s\t%s\t%d\n", id, buf, di ? kindname[decls[di - 1].kind] : "", di ? decls[di - 1].name == id : 0);
    }
    fclose(fn);

    snprintf(path, sizeof path, "%s/stats.txt", out);
    FILE *fs = fopen(path, "w");
    size_t kinds[7] = {0};
    for (size_t i = 0; i < ndecl; i++) kinds[decls[i].kind]++;
    fprintf(fs, "lines\t%llu\nexprs\t%llu\ndecl_blocks\t%zu\nclosure_blocks\t%zu\nedges\t%llu\nproj_uses\t%llu\n",
            (unsigned long long)nlines, (unsigned long long)emax, ndecl, queue.n,
            (unsigned long long)nedges, (unsigned long long)nproj);
    for (int k = 1; k < 7; k++) fprintf(fs, "blocks_%s\t%zu\n", kindname[k], kinds[k]);
    fclose(fs);
    fprintf(stderr, "done: edges %llu projs %llu\n", (unsigned long long)nedges, (unsigned long long)nproj);
    return 0;
}
