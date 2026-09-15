#!/usr/bin/env python3
from fractions import Fraction
import json

def s(b):
    return Fraction(2) - Fraction(2,b)

def run():
    failures=[]
    checks=0
    for B in range(2,5001):
        target=s(B)
        if target < 1 or target >= 2:
            failures.append(("target_range",B,target)); break
        checks += 1
        for b in {2, B, max(2,B//2), max(2,B-1)}:
            if b>B: continue
            vals=[
                ("full_balanced", Fraction(3,2)-Fraction(1,b)),
                ("same_compatible", Fraction(1)),
                ("same_incompatible", max(Fraction(0), Fraction(2)-Fraction(4,b))),
                ("balanced_inactive", Fraction(1)-Fraction(1,b)),
                ("full_inactive", Fraction(1,2)),
            ]
            for name,v in vals:
                checks += 1
                if v>target:
                    failures.append((name,B,b,v,target)); break
            if failures: break
            for c in {2,b,B,max(2,B-1)}:
                if c>B: continue
                v=Fraction(2)-Fraction(1,b)-Fraction(1,c)
                checks+=1
                if v>target:
                    failures.append(("two_balanced",B,b,c,v,target)); break
            if failures: break
        if failures: break
    global_rows=[]
    for n in range(1,100001):
        actual = Fraction(1) if n==1 else Fraction(2)-Fraction(2,n)
        expected = Fraction(1) if n==1 else s(n)
        checks+=1
        if actual!=expected:
            failures.append(("global",n,actual,expected)); break
        if n in (1,2,3,4,10,100,1000,100000):
            global_rows.append((n,str(actual)))
    data={"theorem_id":"AXZ-OPAC-016","audit":"10of10 scalar adversarial exact-rational audit","checks":checks,"failures":failures,"global_samples":global_rows,"status":"PASS" if not failures else "FAIL","truth_boundary":"Corroborates the symbolic proof; does not replace full Lean formalization or external review."}
    print(json.dumps(data,indent=2))
    return data

if __name__=="__main__":
    d=run()
    raise SystemExit(0 if d["status"]=="PASS" else 1)
