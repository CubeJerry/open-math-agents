"""Full signed-width LP on rational nonuniform knots.

Every vertex of the relevant two-dimensional line arrangements is checked.
The output is exploratory; unlike signed_width_lp.py this script currently
does not rationalize its solution into a feasible exact profile.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from bisect import bisect_right
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def solve(p,q,w,n=0):
    h=(1-w)/(p+q)
    mt=(2-p-w-q/2)/(p+q);vt=(q/2-w)/(p+q);ct=(1-q/2-w)/(p+q)
    xs=sorted({F(0),h,F(1,2)}|({F(i,2*n) for i in range(n+1)}if n else set()))
    ts=sorted({F(0),mt,vt,ct,h}|({h*F(i,n)for i in range(n+1)}if n else set()))
    assert 0<mt<vt<ct<h<F(1,2)
    nx,nt=len(xs),len(ts)
    offsets={'L':0,'W':nx,'P':2*nx,'U':2*nx+nt,'V':2*nx+2*nt,'M':2*nx+3*nt}
    total=2*nx+4*nt;rs=[];cs=[];vs=[];rhs=[]
    def add(c,f,x,value):
        grid=xs if f in ['L','W'] else ts
        i=min(len(grid)-2,bisect_right(grid,x)-1)
        r=(x-grid[i])/(grid[i+1]-grid[i])
        for j,v in [(i,value*(1-r)),(i+1,value*r)]:
            k=offsets[f]+j;c[k]=c.get(k,F(0))+v
    def row(c,bound):
        i=len(rhs)
        for k,v in c.items():
            if v:rs.append(i);cs.append(k);vs.append(float(v))
        rhs.append(float(bound))
    for x in xs:
        c={};add(c,'L',x,1);add(c,'W',x,1);row(c,1);row({k:-v for k,v in c.items()},0)
    for t in ts:
        for f in ['V','M']:
            c={};add(c,'P',t,1);add(c,'U',t,1);add(c,f,t,2);row(c,2)
        for f,g in [('P','V'),('U','M')]:
            c={};add(c,f,t,-1);add(c,g,t,-1);row(c,0)
    def vertices(a,b,sums):
        out=set(product(a,b))
        out|={(x,s-x)for x in a for s in sums}
        out|={(s-z,z)for z in b for s in sums}
        return sorted(out)
    for a,c in vertices(xs,xs,[2*t for t in ts]):
        t=(a+c)/2
        if not(0<=a<=F(1,2) and 0<=c<=F(1,2) and 0<=t<=h):continue
        for lo,up in [('L','U'),('L','P'),('W','V'),('W','M')]:
            co={};add(co,lo,a,1);add(co,lo,c,1);add(co,up,t,1);row(co,1)
    for a,c in vertices(xs,ts,[2*t-F(1,2)for t in ts]):
        t=F(1,4)+(a+c)/2
        if not(0<=a<=F(1,2) and 0<=c<=h and 0<=t<=h):continue
        for up,lo,target in [('P','W','V'),('P','W','M'),('M','L','U'),('M','L','P')]:
            co={};add(co,up,c,1);add(co,lo,a,2);add(co,target,t,2);row(co,1)
    obj=np.zeros(total)
    for f,off in offsets.items():
        grid=xs if f in ['L','W'] else ts;fac=2 if f in ['L','W'] else 4
        for j in range(len(grid)-1):
            val=float((grid[j+1]-grid[j])/(2*fac));obj[off+j]+=val;obj[off+j+1]+=val
    A=coo_matrix((vs,(rs,cs)),shape=(len(rhs),total)).tocsr()
    res=linprog(-obj,A_ub=A,b_ub=rhs,bounds=[(-1,1)]*total,method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    if not res.success:return {'status':res.message}
    return {'grid_subdivisions':n,'area':float(-res.fun),'variables':total,'constraints':len(rhs),
            'lower_knots':[str(x)for x in xs],'upper_knots':[str(t)for t in ts],
            'profiles':{f:res.x[off:off+(nx if f in ['L','W']else nt)].tolist()for f,off in offsets.items()}}


if __name__=='__main__':
    import math
    candidates=[('simple',F(69,56),F(25,28),F(3,28)),
      ('near_algebraic',F((15*math.sqrt(2)-4)/14).limit_denominator(10**8),
       F((3*math.sqrt(2)+2)/7).limit_denominator(10**8),
       F((5-3*math.sqrt(2))/7).limit_denominator(10**8))]
    out=[]
    for name,p,q,w in candidates:
        for n in [0,8,16,32]:
            z=solve(p,q,w,n);z['candidate']=name;out.append(z)
            print({k:v for k,v in z.items()if k not in ['profiles','lower_knots','upper_knots']},flush=True)
    Path(__file__).with_name('nonuniform-signed-lp-results.json').write_text(json.dumps(out,indent=2)+'\n')
