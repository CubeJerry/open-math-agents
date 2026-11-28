"""Exact continuous verifier: no floating point and no optimization solver.
A finite rational line arrangement certifies the entire two-variable domain.
"""
from fractions import Fraction as F
from pathlib import Path
import json

def verify(p,q,w):
 b=1/(2*p);h=(1-w)/(p+q)
 ct=(2-2*w-q)/(2*(p+q))
 # Crossings of the affine pieces are exact rational numbers.
 vt=(q/2-w)/(p+q)
 mt=(2-p-w-q/2)/(p+q)
 assert 0<mt<vt<ct<F(1,4)<b<h<F(1,2)
 def low(s):return p*s,min(w+q*s,1-p*s)
 def up(t):
  U=1-2*p*t;P=min(U,2*w+q-1+2*q*t)
  V=min(1-2*w-2*q*t,1-w-q/2+(p-q)*t)
  M=min(V,p-1+2*p*t)
  return P,U,V,M
 ab=[F(0),h,F(1,2)];tb=[F(0),mt,vt,ct,b]
 count=0;slack=None
 def check(lhs,rhs,tag):
  nonlocal count,slack
  assert lhs<=rhs,(tag,lhs,rhs)
  count+=1
  d=rhs-lhs
  slack=d if slack is None else min(slack,d)
 for s in ab:
  L,W=low(s)
  for x in [L,W]:check(0,x,'nonnegative');check(x,1,'cap')
  check(L+W,1,'lower-slice')
 for t in tb:
  P,U,V,M=up(t)
  for x in [P,U,V,M]:check(0,x,'nonnegative');check(x,1,'cap')
  check(P+U+2*V,2,'upper-slice-V');check(P+U+2*M,2,'upper-slice-M')
 def vertices(xs,zs,sums):
  out={(x,z) for x in xs for z in zs}
  out|={(x,s-x) for x in xs for s in sums}
  out|={(s-z,z) for z in zs for s in sums}
  return out
 ll=vertices(ab,ab,[2*t for t in tb])
 for a,c in sorted(ll):
  t=(a+c)/2
  if not(0<=a<=F(1,2) and 0<=c<=F(1,2) and 0<=t<=b):continue
  La,Wa=low(a);Lc,Wc=low(c);P,U,V,M=up(t)
  for z in [U,P]:check(La+Lc+z,1,('LL-left',a,c))
  for z in [V,M]:check(Wa+Wc+z,1,('LL-right',a,c))
 lh=vertices(ab,tb,[2*t-F(1,2) for t in tb])
 for a,c in sorted(lh):
  t=F(1,4)+(a+c)/2
  if not(0<=a<=F(1,2) and 0<=c<=b and 0<=t<=b):continue
  La,Wa=low(a);Pc,Uc,Vc,Mc=up(c);P,U,V,M=up(t)
  for z in [V,M]:check(Pc+2*Wa+2*z,1,('LH-right',a,c))
  for z in [U,P]:check(Mc+2*La+2*z,1,('LH-left',a,c))
 def integral(xs,fn):return sum((r-l)*(fn(l)+fn(r))/2 for l,r in zip(xs,xs[1:]))
 lower=integral(ab,lambda s:sum(low(s))/2)
 upper=integral(tb,lambda s:sum(up(s))/4)
 area=lower+upper
 return {'p':str(p),'q':str(q),'w':str(w),'cutoff':str(b),'lower_crossing':str(h),'upper_breakpoints':[str(t) for t in tb],'area':str(area),'area_decimal':float(area),'excess_over_prior_claim':str(area-F(25541,84000)),'exact_vertex_inequalities':count,'minimum_slack':str(slack)}

if __name__=='__main__':
 out=[verify(F(6,5),F(9,10),F(17,140)),verify(F(241,200),F(903,1000),F(121,1000)),verify(F(603,500),F(903,1000),F(1207,10000)),verify(F(211,175),F(158,175),F(6242,51695)),verify(F(1125,932),F(710,787),F(162359479,1353277980))]
 for x in out:print(json.dumps(x))
 Path(__file__).with_name('continuous-certificates.json').write_text(json.dumps(out,indent=2)+'\n')
