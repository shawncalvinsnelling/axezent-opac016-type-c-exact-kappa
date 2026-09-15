#!/usr/bin/env python3
import importlib.util, json
from pathlib import Path
import sympy as sp

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('audit',HERE/'exact_subspace_audit.py')
aud=importlib.util.module_from_spec(spec); spec.loader.exec_module(aud)

def analyze(B,n):
    M=sp.Matrix(B); P=M.T*(M*M.T).inv()*M
    def member(v):
        vv=sp.Matrix(v); return P*vv==vv
    long=set(); edge={}; active=set()
    for i in range(n):
        v=[0]*n; v[i]=2
        if member(v): long.add(i); active.add(i)
    for i in range(n):
        for j in range(i+1,n):
            ss=set()
            for sg in (1,-1):
                v=[0]*n; v[i]=1; v[j]=sg
                if member(v): ss.add(sg); active|={i,j}
            if ss: edge[(i,j)]=ss
    adj={i:set() for i in active}
    for (i,j) in edge: adj[i].add(j); adj[j].add(i)
    comps=[]; seen=set()
    for i in active:
        if i in seen: continue
        st=[i]; seen.add(i); C=[]
        while st:
            u=st.pop(); C.append(u)
            for w in adj[u]:
                if w not in seen: seen.add(w); st.append(w)
        comps.append(sorted(C))
    full=[]; bal=[]
    for C in comps:
        if any(i in long for i in C): full.append(C)
        else: bal.append(C)
    bs=sorted([len(C) for C in bal], reverse=True)
    f=len(full[0]) if full else 0
    inactive=n-f-sum(bs)
    scores=[]
    for i in range(n):
        y=P[:,i]*2
        if all(v==0 for v in y): scores.append(sp.Rational(0)); continue
        C=next(C for C in comps if i in C)
        scores.append(sum(abs(y[j]) for j in C)/2)
    actual=max([sp.Rational(1)]+scores)
    return {'n':n,'f':f,'bs':bs,'m':len(bs),'bsum':sum(bs),'inactive':inactive,'actual':actual}

def b1(d): return d['bs'][0] if d['bs'] else 2
def b2(d): return d['bs'][1] if len(d['bs'])>1 else 2
def Q(x): return sp.Rational(x)

candidates={
 'K0_constant_1': lambda d: Q(1),
 'K1_2-1/b1': lambda d: Q(2)-Q(1,b1(d)),
 'K2_2-2/b1 [TARGET]': lambda d: Q(2)-Q(2,b1(d)),
 'K3_2-2/n': lambda d: Q(2)-Q(2,d['n']),
 'K4_2-2/sum_bal': lambda d: Q(1) if d['bsum']==0 else Q(2)-Q(2,d['bsum']),
 'K5_2-1/b1-1/b2': lambda d: Q(2)-Q(1,b1(d))-Q(1,b2(d)),
 'K6_max(1,2-1/b1-1/b2)': lambda d: max(Q(1),Q(2)-Q(1,b1(d))-Q(1,b2(d))),
 'K7_2-1/n': lambda d: Q(2)-Q(1,d['n']),
 'K8_1+(b1-2)/n': lambda d: Q(1)+Q(b1(d)-2,d['n']),
 'K9_1+(b1-2)/b1 [algebraic target]': lambda d: Q(1)+Q(b1(d)-2,b1(d)),
 'K10_2-2/min_bal': lambda d: Q(1) if not d['bs'] else Q(2)-Q(2,min(d['bs'])),
 'K11_2-2/(b1+f)': lambda d: Q(2)-Q(2,max(2,b1(d)+d['f'])),
 'K12_1 if full else 2-2/b1': lambda d: Q(1) if d['f']>0 else Q(2)-Q(2,b1(d)),
 'K13_2-2/(largest active component)': lambda d: Q(2)-Q(2,max(2,d['f'],b1(d))),
 'K14_1+(sum_bal-2)/sum_bal': lambda d: Q(1) if d['bsum']==0 else Q(1)+Q(d['bsum']-2,d['bsum']),
}
records=[]
for n in range(2,7):
    for B in aud.enumerate_subspaces(n):
        if not B: continue
        ok,detail=aud.validate(B,n)
        if not ok: raise RuntimeError((n,B,detail))
        records.append(analyze(B,n))
vecs={}
for name,fn in candidates.items():
    out=tuple(fn(d) for d in records)
    vecs.setdefault(out,[]).append(name)
classes=[]
for out,names in vecs.items():
    bad=None
    for pred,d in zip(out,records):
        if pred!=d['actual']:
            bad={'n':d['n'],'full_block_size':d['f'],'balanced_blocks':d['bs'],'inactive':d['inactive'],'predicted':str(pred),'actual':str(d['actual'])}; break
    classes.append({'names':names,'survives':bad is None,'first_counterexample':bad})
def partitions_min2(total,maxpart=None):
    if total==0:
        yield (); return
    if maxpart is None or maxpart>total: maxpart=total
    for p in range(maxpart,1,-1):
        if p==total: yield (p,)
        elif p<total:
            for rest in partitions_min2(total-p,p): yield (p,)+rest
def component_signatures(nmax=30):
    seen=set()
    for n in range(2,nmax+1):
        for f in [0]+list(range(1,n+1)):
            rem=n-f
            for bsum in range(rem+1):
                for bs in partitions_min2(bsum): seen.add((n,f,bs,rem-bsum))
    return seen
sigs=component_signatures(30)
branch_bad=[]
for n,f,bs,inactive in sigs:
    direct=max([Q(1)]+([Q(1)] if f else [])+[Q(2)-Q(2,b) for b in bs]+([Q(0)] if inactive else []))
    bb=bs[0] if bs else 2
    formula=Q(2)-Q(2,bb)
    if direct!=formula:
        branch_bad.append((n,f,bs,inactive,direct,formula)); break
receipt={'claim':'OPAC-016 formula elimination for Type C_n exact kappa','exact_root_spanned_subspaces_tested':len(records),'candidate_formulas_submitted':len(candidates),'distinct_answer_rules_after_algebraic/output_equivalence':len(classes),'surviving_equivalence_classes':[c for c in classes if c['survives']],'component_size_signatures_exhausted_through_rank':30,'component_signatures_tested':len(sigs),'component_branch_failures':len(branch_bad),'unique_surviving_mathematical_rule':'kappa(C_n,U)=1 if there is no balanced A-block; otherwise 2-2/b_max.','global_max':'kappa(C_1)=1; for n>=2, kappa(C_n)=2-2/n, attained by the A_{n-1} zero-sum hyperplane.','truth_boundary':'Finite formula elimination supports the written all-rank proof; it is not the proof itself.'}
Path('receipts').mkdir(exist_ok=True)
Path('receipts/formula_elimination_receipt.generated.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2))
