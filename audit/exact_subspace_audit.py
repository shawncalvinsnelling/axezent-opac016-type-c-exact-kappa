#!/usr/bin/env python3
"""AXZ-OPAC-016 / superseding Type-C exact-kappa audit.

Exact rational counterexample search for every distinct root-spanned subspace
of C_n for n=2..6. This is a bounded audit, not the all-rank proof.
Requires: sympy.
"""
import itertools, collections, json
import sympy as sp


def canon(vectors,n):
    if not vectors: return ()
    M=sp.Matrix(vectors); R,_=M.rref()
    return tuple(tuple(sp.Rational(R[i,j]) for j in range(n))
                 for i in range(R.rows) if any(R[i,j]!=0 for j in range(n)))

def root_dirs(n):
    rr=[]
    for i in range(n):
        v=[0]*n; v[i]=2; rr.append(tuple(v))
    for i in range(n):
        for j in range(i+1,n):
            for s in (1,-1):
                v=[0]*n; v[i]=1; v[j]=s; rr.append(tuple(v))
    return rr

def enumerate_subspaces(n):
    rr=root_dirs(n); seen={()}; q=collections.deque([()])
    while q:
        B=q.popleft()
        if len(B)==n: continue
        for r in rr:
            C=canon(list(B)+[r],n)
            if len(C)>len(B) and C not in seen:
                seen.add(C); q.append(C)
    return seen


def validate(B,n):
    M=sp.Matrix(B); P=M.T*(M*M.T).inv()*M
    def member(v):
        vv=sp.Matrix(v)
        return P*vv == vv
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
        stack=[i]; seen.add(i); C=[]
        while stack:
            u=stack.pop(); C.append(u)
            for w in adj[u]:
                if w not in seen: seen.add(w); stack.append(w)
        comps.append(sorted(C))
    full=[]; balanced=[]
    for i in range(n):
        if i not in active and any((P[:,i]*2)[j]!=0 for j in range(n)):
            return False,"inactive projection"
    for C in comps:
        b=len(C); hasloop=any(i in long for i in C)
        for i in C:
            col=P[:,i]
            if any(col[j]!=0 for j in range(n) if j not in C):
                return False,"cross-component projection"
        if hasloop:
            full.append(C)
            for i in C:
                if i not in long: return False,"full block missing long root"
                for j in C:
                    if P[j,i] != (1 if i==j else 0): return False,"full projection != identity"
            for i,j in itertools.combinations(C,2):
                if edge.get((i,j),set()) != {1,-1}: return False,"full block missing short root"
        else:
            balanced.append(C)
            if b<2: return False,"balanced singleton"
            Q=sp.eye(b)-P.extract(C,C)
            if Q.rank()!=1: return False,"balanced complement rank !=1"
            for a in range(b):
                for c in range(b):
                    if abs(Q[a,c]) != sp.Rational(1,b): return False,"wrong switched A-block projector"
            for i,j in itertools.combinations(C,2):
                if len(edge.get((i,j),set()))!=1: return False,"balanced pair not exactly one sign"
            for i in C:
                y=P[:,i]*2
                if sum(abs(y[j]) for j in C) != 4*sp.Rational(b-1,b):
                    return False,"wrong balanced long-axis projection"
    if len(full)>1: return False,"multiple full C blocks"
    bs=sorted((len(C) for C in balanced),reverse=True)
    predicted=sp.Rational(1) if not bs else max(sp.Rational(1),sp.Rational(2)-sp.Rational(2,bs[0]))
    scores=[]
    for i in range(n):
        y=P[:,i]*2
        if all(v==0 for v in y): scores.append(sp.Rational(0)); continue
        C=next(C for C in comps if i in C)
        scores.append(sum(abs(y[j]) for j in C)/2)
    actual=max([sp.Rational(1)]+scores)
    if actual!=predicted: return False,"kappa mismatch"
    return True,str(predicted)

def main():
    from pathlib import Path
    rows=[]; total_nonzero=0; failures=[]
    for n in range(2,7):
        S=enumerate_subspaces(n); nonzero=0
        for B in S:
            if not B: continue
            nonzero+=1; ok,detail=validate(B,n)
            if not ok: failures.append({"n":n,"basis":str(B),"failure":detail}); break
        total_nonzero+=nonzero
        rows.append({"rank":n,"all_subspaces_including_zero":len(S),"nonzero_tested":nonzero})
    receipt={"claim":"Type-C root-spanned subspaces have one optional full C block plus balanced A blocks, with kappa=max(1,2-2/b_max)","scope":"bounded exact rational counterexample audit only; all-rank theorem requires written proof","rows":rows,"nonzero_total":total_nonzero,"failures":failures,"status":"PASS" if not failures else "FAIL"}
    print(json.dumps(receipt,indent=2))
    out=Path('receipts/exact_subspace_audit_receipt.json')
    out.parent.mkdir(exist_ok=True)
    with out.open('w') as f: json.dump(receipt,f,indent=2)
    if failures: raise SystemExit(1)

if __name__=='__main__': main()
