#!/usr/bin/env python3
import argparse, hashlib, importlib.util, json, platform
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
def Q(numerator, denominator=1): return sp.Rational(numerator, denominator)

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
                for bs in partitions_min2(bsum):
                    if f or bs: seen.add((n,f,bs,rem-bsum))
    return seen

def classify(records):
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
    return classes

def run(max_rank=6, signature_rank=30):
    if max_rank < 2 or signature_rank < 2:
        raise ValueError("rank limits must be at least 2")
    records=[]; rows=[]
    for n in range(2,max_rank+1):
        subspaces=sorted(aud.enumerate_subspaces(n))
        count=0
        for B in subspaces:
            if not B: continue
            ok,detail=aud.validate(B,n)
            if not ok: raise RuntimeError((n,B,detail))
            records.append(analyze(B,n)); count+=1
        rows.append({'rank':n,'nonzero_subspaces':count})
        print(f"Completed C{n}: {count} nonzero subspaces",flush=True)
    classes=classify(records)
    sigs=component_signatures(signature_rank)
    failures=[]
    for n,f,bs,inactive in sorted(sigs):
        direct=max([Q(1)]+[Q(2)-Q(2,b) for b in bs])
        formula=Q(2)-Q(2,bs[0]) if bs else Q(1)
        if direct!=formula:
            failures.append({'n':n,'f':f,'bs':bs,'inactive':inactive})
    target=next(c for c in classes if 'K2_2-2/b1 [TARGET]' in c['names'])
    if not target['survives'] or failures:
        raise RuntimeError('Target audit failed')
    receipt={
        'claim':'Bounded Type-C formula comparison; not proof by elimination of all formulas',
        'status':'PASS',
        'exact_rank_limit':max_rank,
        'exact_subspace_rows':rows,
        'exact_root_spanned_subspaces_tested':len(records),
        'candidate_formulas_submitted':len(candidates),
        'candidate_names':list(candidates),
        'distinct_output_classes_on_tested_domain':len(classes),
        'rejected_output_classes':sum(not c['survives'] for c in classes),
        'surviving_output_classes':[c for c in classes if c['survives']],
        'all_output_classes':classes,
        'component_signature_rank_limit':signature_rank,
        'nonzero_component_signatures_tested':len(sigs),
        'zero_subspaces_excluded':True,
        'component_branch_failures':failures,
        'python_version':platform.python_version(),
        'sympy_version':sp.__version__,
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__), HERE/'exact_subspace_audit.py')},
        'truth_boundary':'Finite output agreement is not algebraic equivalence or universal uniqueness. Geometry gauge identification uses the written proof; the audit checks exact projectors and scalar scores.'
    }
    return receipt

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-rank',type=int,default=6)
    parser.add_argument('--signature-rank',type=int,default=30)
    parser.add_argument('--output',type=Path,default=Path('receipts/formula_elimination_receipt.generated.json'))
    args=parser.parse_args()
    receipt=run(args.max_rank,args.signature_rank)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
