from fractions import Fraction as F
from pathlib import Path
import json,math
p,q,w=F(6,5),F(9,10),F(17,140)
b=1/(2*p)
def profile(s,upper=False):
 if not upper:return {'L':p*s,'W':min(w+q*s,1-p*s)}
 U=1-2*p*s;P0=2*w+q-1+2*q*s
 V=min(1-2*w-2*q*s,(2-U-P0)/2)
 return {'P':min(U,P0),'U':U,'V':V,'M':min(V,p-1+2*p*s)}
def build(D):
 assert D%12==0
 K=int(b*D); n=D//2
 arrays={k:[] for k in ['L','W','P','U','V','M']}
 for upper,N in [(False,n),(True,K)]:
  for i in range(N):
   aa,bb=profile(F(i,D),upper),profile(F(i+1,D),upper)
   for f in aa:arrays[f].append(min(aa[f],bb[f]))
 checks=0
 def check(v,bound):
  nonlocal checks
  assert v<=bound,(v,bound)
  checks+=1
 for f,seq in arrays.items():
  for x in seq:check(-x,0);check(x,1)
 L,W,P,U,V,M=[arrays[k] for k in ['L','W','P','U','V','M']]
 for i in range(n):check(L[i]+W[i],1)
 for j in range(K):check(P[j]+U[j]+2*max(V[j],M[j]),2)
 for i in range(n):
  for j in range(n):
   for t in set([(i+j)//2,(i+j+1)//2]):
    if t<K:
     check(L[i]+L[j]+max(U[t],P[t]),1)
     check(W[i]+W[j]+max(V[t],M[t]),1)
 for i in range(n):
  for j in range(K):
   for t in set([D//4+(i+j)//2,D//4+(i+j+1)//2]):
    if t<K:
     check(P[j]+2*W[i]+2*max(V[t],M[t]),1)
     check(M[j]+2*L[i]+2*max(U[t],P[t]),1)
 area=(sum(L+W)/2+sum(P+U+V+M)/4)/D
 den=math.lcm(*(v.denominator for seq in arrays.values() for v in seq))
 return {'D':D,'K':K,'p':str(p),'q':str(q),'w':str(w),'area':str(area),'area_float':float(area),'denominator':den,'arrays':{k:[int(v*den) for v in seq] for k,seq in arrays.items()},'exact_checks':checks}
if __name__=='__main__':
 out=[]
 for D in [24,36,48,60,72,84,96,120,192,288]:
  v=build(D);out.append(v);print({k:x for k,x in v.items() if k!='arrays'})
 Path(__file__).with_name('exact-six-width-step-profiles.json').write_text(json.dumps(out,indent=2)+'\n')
