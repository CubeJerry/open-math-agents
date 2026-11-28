"""Exploratory polygon geometry for non-height-dominated block extensions.

All basic polygon operations use fractions. Search scores are diagnostics,
not claims of a valid construction.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import math


def cross(a, b):
    return a[0]*b[1]-a[1]*b[0]


def sub(a, b):
    return a[0]-b[0], a[1]-b[1]


def hull(points):
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts
    def half(seq):
        out = []
        for p in seq:
            while len(out) >= 2 and cross(sub(out[-1], out[-2]), sub(p,out[-1])) <= 0:
                out.pop()
            out.append(p)
        return out
    return half(pts)[:-1]+half(pts[::-1])[:-1]


def clip(poly, a, b, c):
    """Intersect with a*x+b*y <= c, including the boundary."""
    if not poly:
        return []
    out = []
    for p,q in zip(poly,poly[1:]+poly[:1]):
        vp=a*p[0]+b*p[1]-c
        vq=a*q[0]+b*q[1]-c
        if vp<=0:
            out.append(p)
        if (vp<0<vq) or (vq<0<vp):
            r=vp/(vp-vq)
            out.append((p[0]+r*(q[0]-p[0]),p[1]+r*(q[1]-p[1])))
    return hull(out)


def area(poly):
    return sum(cross(p,q) for p,q in zip(poly,poly[1:]+poly[:1]))/2


def minkowski(a,b):
    return hull([(p[0]+q[0],p[1]+q[1]) for p in a for q in b])


def shift(poly,x,y):
    return [(p[0]+x,p[1]+y) for p in poly]


def scale(poly,r):
    return [(p[0]*r,p[1]*r) for p in poly]


def inside(poly,p,strict=False):
    vals=[cross(sub(b,a),sub(p,a)) for a,b in zip(poly,poly[1:]+poly[:1])]
    return all(v>0 if strict else v>=0 for v in vals)


def intersection(a,b):
    out=a[:]
    for p,q in zip(b,b[1:]+b[:1]):
        d=sub(q,p)
        out=clip(out,d[1],-d[0],d[1]*p[0]-d[0]*p[1])
    return out


def difference(a,b):
    """Partition a convex polygon minus another into convex polygons.

    Boundaries may be shared; this is a measure partition and all positive
    interiors are exactly disjoint from the removed closed polygon.
    """
    remaining=a[:]
    out=[]
    for p,q in zip(b,b[1:]+b[:1]):
        d=sub(q,p)
        aa,bb,cc=d[1],-d[0],d[1]*p[0]-d[0]*p[1]
        outside=clip(remaining,-aa,-bb,-cc)
        if len(outside)>=3 and area(outside)>0:
            out.append(outside)
        remaining=clip(remaining,aa,bb,cc)
        if len(remaining)<3 or area(remaining)==0:
            break
    return out


def uncovered_in(region, sums):
    pieces=[region]
    for *_,poly in sums:
        pieces=[v for r in pieces for v in difference(r,poly)]
    return pieces


def six_width(p=F(6,5),q=F(9,10),w=F(17,140)):
    b=1/(2*p)
    lo=[(F(0),-F(1,2)),(F(1,2),-F(1,2)),(F(1,2),F(1,2)),(F(0),F(1,2))]
    # a >= -p*s/2; a <= (w+q*s)/2; a <= (1-p*s)/2.
    lo=clip(lo,-p,-2,F(0))
    lo=clip(lo,-q,2,w)
    lo=clip(lo,p,2,F(1))
    # Work in t=s-1/2 for upper pieces.
    base=[(F(0),-F(1,2)),(b,-F(1,2)),(b,F(1,2)),(F(0),F(1,2))]
    pos=base[:]
    # P <= U=1-2pt and P0=2w+q-1+2qt.
    pos=clip(pos,2*p,4,2)
    pos=clip(pos,-2*q,4,2*w+q)
    # V <= V1=1-2w-2qt; V0=1-w-q/2+(p-q)t.
    pos=clip(pos,2*q,-4,-2*w)
    pos=clip(pos,q-p,-4,-w-q/2)
    neg=base[:]
    # U controls right edge: a <= -1/4+U/4 = -p*t/2.
    neg=clip(neg,2*p,4,0)
    # M=min(V1,V0,p-1+2pt) controls left edge.
    neg=clip(neg,2*q,-4,2-2*w)
    neg=clip(neg,q-p,-4,2-w-q/2)
    neg=clip(neg,-2*p,-4,p)
    return [lo,shift(pos,F(1,2),0),shift(neg,F(1,2),0)]


def segment_intersection(a,b,c,d):
    u,v=sub(b,a),sub(d,c)
    den=cross(u,v)
    if den==0:
        return None
    t=cross(sub(c,a),v)/den
    s=cross(sub(c,a),u)/den
    if 0<=t<=1 and 0<=s<=1:
        return a[0]+t*u[0],a[1]+t*u[1]
    return None


def torus_sums(parts):
    box=[(F(0),-F(1,2)),(F(1),-F(1,2)),(F(1),F(1,2)),(F(0),F(1,2))]
    out=[]
    for i in range(len(parts)):
        for j in range(i,len(parts)):
            sums=minkowski(parts[i],parts[j])
            for x,y in product(range(-2,2),repeat=2):
                pp=intersection(shift(sums,x,y),box)
                if len(pp)>=3 and area(pp)>0:
                    out.append((i,j,x,y,shift(sums,x,y)))
    return out


def hole_triangle(p,q,w):
    b=1/(2*p)
    h=(1-w)/(p+q)
    return hull([(2*b,F(1,2)),(2*b,w+q*b),(2*h,1-p*h)])


def barycentric_patch(tri):
    """Closed hexagon; mathematical construction uses its interior."""
    assert len(tri)==3
    weights=sorted(set(__import__('itertools').permutations([F(3,13),F(4,13),F(6,13)])))
    return hull([tuple(sum(lam[i]*tri[i][j] for i in range(3)) for j in range(2)) for lam in weights])


def facet_patch(tri,epsilon=F(1,1000)):
    """One active facet: lambda_0>epsilon and safe lambda_1,lambda_2."""
    r=1-epsilon
    # At epsilon=0 the barycentric pairs (lambda_1,lambda_2) form a square
    # [2/7,4/7]^2 with its top-right corner cut off by lambda_1+lambda_2<=1.
    pairs=[(F(2,7),F(2,7)),(F(4,7),F(2,7)),(F(4,7),F(3,7)),
           (F(3,7),F(4,7)),(F(2,7),F(4,7))]
    weights=[(epsilon+r*(1-a-b),r*a,r*b) for a,b in pairs]
    return hull([tuple(sum(lam[i]*tri[i][j] for i in range(3)) for j in range(2)) for lam in weights])


def doubling_preimages(poly):
    # All patches lie in [0,1) x [-1/2,1/2).
    return [shift(scale(poly,F(1,2)),s,a) for s,a in product([F(0),F(1,2)],[F(0),-F(1,2)])]


def verify_extension(p,q,w):
    parts=six_width(p,q,w)
    H=hole_triangle(p,q,w)
    K=barycentric_patch(H)
    W=doubling_preimages(K)
    checks=[]
    for i,j,x,y,poly in torus_sums(parts):
        intr=intersection(H,poly)
        assert area(intr)==0,(i,j,x,y,intr)
        checks.append({'pair':[i,j],'translation':[x,y],'intersection_vertices':[[str(a),str(b)] for a,b in intr]})
    assert area(K)*13==area(H)
    k21=minkowski(scale(K,2),scale(K,-1))
    assert all(inside(H,v) for v in k21)
    assert area(intersection(K,H))==area(K)
    assert all(max(v[j] for v in K)-min(v[j] for v in K)<F(1,2) for j in range(2))
    assert sum(map(area,W))==area(K)
    for i in range(len(parts)):
        for u in W:
            for sx,sy in product(range(-1,2),repeat=2):
                assert area(intersection(parts[i],shift(u,sx,sy)))==0
    old_area=sum(map(area,parts))
    return {'parameters':{'p':str(p),'q':str(q),'w':str(w)},
            'old_area':str(old_area),'hole_area':str(area(H)),'patch_area':str(area(K)),
            'augmented_area':str(old_area+area(K)),'augmented_area_decimal':float(old_area+area(K)),
            'hole_vertices':[[str(x),str(y)] for x,y in H],
            'patch_vertices':[[str(x),str(y)] for x,y in K],
            'minkowski_checks':checks}


def seam_vertices(parts):
    sums=torus_sums(parts)
    points=set(p for *_,poly in sums for p in poly if 0<=p[0]<=1 and -F(1,2)<=p[1]<=F(1,2))
    edges=[(p,q) for *_,poly in sums for p,q in zip(poly,poly[1:]+poly[:1])]
    for a,b in combinations(edges,2):
        p=segment_intersection(*a,*b)
        if p is not None and 0<=p[0]<=1 and -F(1,2)<=p[1]<=F(1,2):
            points.add(p)
    uncovered=[p for p in points if not any(inside(poly,p,True) for *_,poly in sums)]
    return sums,sorted(uncovered)


if __name__=='__main__':
    parts=six_width()
    print('parts', [[tuple(map(str,v)) for v in poly] for poly in parts])
    print('area',sum(map(area,parts)))
    sums,pts=seam_vertices(parts)
    print('sum polygons',len(sums))
    print('seam vertices',[(str(x),str(y)) for x,y in pts])
    out={'parts':[[[str(x),str(y)] for x,y in poly] for poly in parts], 'seam_vertices':[[str(x),str(y)] for x,y in pts]}
    Path(__file__).with_name('six-width-geometry.json').write_text(json.dumps(out,indent=2)+'\n')
