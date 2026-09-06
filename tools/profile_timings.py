#!/usr/bin/env python3
"""Rank the slowest commands of the Sigmoid_Universal_Approximation build.

Isabelle stores the timing of every command above `build_timing_threshold`
(default 0.1s) in the session database, so an ordinary build refreshes the data
and no instrumented rebuild is needed. This reads that blob, decompresses it
(zstd), maps each Isabelle *symbol* offset back to a line number -- `\\<alpha>`
counts as one symbol, not as its bytes -- and attributes each command to the
enclosing declaration.

Usage:  python3 tools/profile_timings.py
Needs:  python3-zstandard
"""
import sqlite3, zstandard, re, os, collections, sys

DB="/home/dusty/.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux/log/Sigmoid_Universal_Approximation.db"
PROJ="/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation"

blob=sqlite3.connect(DB).execute("SELECT command_timings FROM isabelle_session_info").fetchone()[0]
data=zstandard.ZstdDecompressor().decompress(blob, max_output_size=50_000_000).decode("utf-8","replace")

recs=[]
for m in re.finditer(r'elapsed=([0-9.]+)\x06name=([^\x05\x06]*)\x06offset=(\d+)\x06file=([^\x05\x06]*)', data):
    recs.append((float(m.group(1)), m.group(2), int(m.group(3)), m.group(4)))

SYM=re.compile(r'\\<\^?[A-Za-z0-9_\']+>')
_cache={}
def line_of(path, off):
    """Isabelle symbol offset (1-based) -> line number."""
    if path not in _cache:
        txt=open(path, encoding="utf-8", errors="replace").read()
        starts=[]           # symbol index at which each line starts
        i=0; sym=0
        starts.append(0)
        while i < len(txt):
            m=SYM.match(txt, i)
            if m: i=m.end()
            else:
                if txt[i]=="\n": starts.append(sym+1)
                i+=1
            sym+=1
        _cache[path]=starts
    starts=_cache[path]
    lo,hi=0,len(starts)-1
    while lo<hi:
        mid=(lo+hi+1)//2
        if starts[mid] <= off-1: lo=mid
        else: hi=mid-1
    return lo+1

DECL=re.compile(r'^(definition|lemma|theorem|corollary|proposition|fun|primrec|instantiation|instance)\s+([A-Za-z][A-Za-z0-9_\']*)?')
_decls={}
def enclosing(path, line):
    if path not in _decls:
        ds=[]
        for i,l in enumerate(open(path,encoding="utf-8",errors="replace").read().split("\n"),1):
            m=DECL.match(l)
            if m: ds.append((i, m.group(2) or m.group(1)))
        _decls[path]=ds
    best=("(preamble)",0)
    for i,n in _decls[path]:
        if i<=line: best=(n,i)
        else: break
    return best

rows=[]
for elapsed,name,off,f in recs:
    p=f.replace("~/", "/home/dusty/")
    if not p.startswith(PROJ): continue
    if not os.path.exists(p): continue
    ln=line_of(p,off)
    dname,dline=enclosing(p,ln)
    rows.append((elapsed,name,os.path.basename(p),ln,dname,dline))

print("project command-timing records: %d, total %.1fs\n" % (len(rows), sum(r[0] for r in rows)))
print("="*96)
print("SLOWEST INDIVIDUAL COMMANDS")
print("="*96)
print("%8s  %-10s %-40s %-30s" % ("elapsed","command","file:line","enclosing declaration"))
for e,n,f,ln,d,dl in sorted(rows, reverse=True)[:30]:
    print("%7.2fs  %-10s %-40s %-30s" % (e, n, "%s:%d"%(f,ln), d))

agg=collections.defaultdict(float); where={}
for e,n,f,ln,d,dl in rows:
    if n=="theory": continue
    agg[(f,d)]+=e; where[(f,d)]=dl
print()
print("="*96)
print("SLOWEST DECLARATIONS (summing all commands inside)")
print("="*96)
print("%8s  %-46s %-34s" % ("total","declaration","file:line"))
for (f,d),e in sorted(agg.items(), key=lambda kv:-kv[1])[:30]:
    print("%7.2fs  %-46s %s:%d" % (e, d, f, where[(f,d)]))

# --- tactic text at each slow site, and tactic-kind distribution ---
print()
print("="*96)
print("TACTIC TEXT AT THE 22 SLOWEST 'by/apply' SITES")
print("="*96)
import textwrap
byrows=[r for r in rows if r[1] in ("by","apply","proof","ML","value")]
for e,n,f,ln,d,dl in sorted(byrows, reverse=True)[:22]:
    p=os.path.join(PROJ,f)
    L=open(p,encoding="utf-8",errors="replace").read().split("\n")
    txt=" ".join(x.strip() for x in L[ln-1:ln+1])[:150]
    print("%6.2fs %-34s %s" % (e, "%s:%d"%(f[:24],ln), txt))

print()
print("="*96)
print("WHERE THE TIME GOES BY TACTIC KIND (commands > 0.1s)")
print("="*96)
kinds=collections.Counter(); ktime=collections.Counter()
pat=re.compile(r'\b(smt|metis|sledgehammer|auto|force|fastforce|blast|simp|linarith|presburger|arith|argo|meson|nlinarith|induction|induct|eval|normalization)\b')
for e,n,f,ln,d,dl in rows:
    if n not in ("by","apply"): 
        kinds["<%s>"%n]+=1; ktime["<%s>"%n]+=e; continue
    p=os.path.join(PROJ,f); L=open(p,encoding="utf-8",errors="replace").read().split("\n")
    txt=" ".join(x.strip() for x in L[ln-1:ln+2])
    ms=pat.findall(txt)
    k=ms[0] if ms else "other"
    kinds[k]+=1; ktime[k]+=e
print("%-16s %6s %9s" % ("kind","count","total"))
for k,t in ktime.most_common(18):
    print("%-16s %6d %8.2fs" % (k, kinds[k], t))
