"""Reproduce every exact rational geometry/area checkpoint for the hole route.

Run from any directory: python /path/to/verify_augmentations.py
No numerical optimizer is used. The separate analytic proof supplies the
bounded-potential arguments and conversion of the old profile to layers.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

from polygon_extension import (
    area, barycentric_patch, doubling_preimages, facet_patch, hole_triangle,
    inside, intersection, minkowski, scale, shift, six_width, torus_sums,
    upper_patch, upper_preimages,
)


def vertices(poly):
    return [[str(x),str(y)] for x,y in poly]


def verify(name,p,q,w,kind,epsilon=F(1,1000)):
    b=1/(2*p);h=(1-w)/(p+q);delta=h-b;S0=F(1,2)+b
    assert 1<p<2 and b<h<F(1,2) and w+q*b>F(1,4)
    T=six_width(p,q,w);H=hole_triangle(p,q,w)
    hole_checks=[]
    for i,j,s,a,poly in torus_sums(T):
        common=intersection(H,poly)
        assert area(common)==0
        hole_checks.append({'summands':[i,j],'translation':[s,a],
                            'intersection':vertices(common)})
    assert len(hole_checks)==15
    assert area(H)==(p+q)*delta**2
    if kind=='offset':
        K=barycentric_patch(H);W=doubling_preimages(K);gamma=F(1,13)
        assert area(K)==area(H)/13
        assert all(inside(H,v) for v in minkowski(scale(K,2),scale(K,-1)))
    elif kind=='facet':
        K=facet_patch(H,epsilon);W=doubling_preimages(K);gamma=F(1,7)
        assert area(K)==(1-epsilon)**2*area(H)/7
    elif kind=='upper':
        K=upper_patch(H,p,q,w,epsilon);W=upper_preimages(K);gamma=F(1,2)
        assert area(K)==(1-epsilon)**2*area(H)
        assert 0<S0-delta and S0+2*delta<1
        assert min(v[0] for poly in W for v in poly)==S0+epsilon*delta
    else:
        raise ValueError(kind)
    assert all(max(v[j] for v in K)-min(v[j] for v in K)<F(1,2) for j in range(2))
    assert all(0<=x<1 and -F(1,2)<=y<F(1,2) for poly in W for x,y in poly)
    for old in T:
        for new in W:
            for sx,sy in product(range(-1,2),repeat=2):
                assert area(intersection(old,shift(new,sx,sy)))==0
    for i in range(len(W)):
        for j in range(i+1,len(W)):
            assert area(intersection(W[i],W[j]))==0
    added=sum(map(area,W));base=sum(map(area,T));limit=base+gamma*area(H)
    assert added==area(K)*F(len(W),4)
    return {'name':name,'kind':kind,'parameters':{'p':str(p),'q':str(q),'w':str(w)},
            'b':str(b),'h':str(h),'delta':str(delta),
            'old_area':str(base),'hole_area':str(area(H)),'epsilon':str(epsilon),
            'actual_patch_area':str(added),'ideal_old_plus_actual_patch':str(base+added),
            'ideal_old_plus_actual_patch_decimal':float(base+added),
            'limiting_ideal_area':str(limit),'limiting_ideal_area_decimal':float(limit),
            'old_max_height':str(S0),'raw_mixed_height_interval':[str(S0-delta),str(S0+2*delta)],
            'hole_vertices':vertices(H),'patch_vertices':vertices(K),
            'new_component_vertices':[vertices(poly) for poly in W],
            'exact_hole_checks':hole_checks}


def main():
    cases=[
        ('simple_offset',F(6,5),F(9,10),F(17,140),'offset'),
        ('optimized_rational_offset',F(345,286),F(250,277),F(4201393,34900338),'offset'),
        ('optimized_rational_facet',F(1125,932),F(710,787),F(162359479,1353277980),'facet'),
        ('simple_signed_continuation',F(69,56),F(25,28),F(3,28),'upper'),
    ]
    results=[verify(*case) for case in cases]
    expected=[F(260315,856128),F(424074534852967,1394685492338424),
              F(190982127009695893,628094878940430000),F(579,1904)]
    for v,e in zip(results,expected):
        assert F(v['limiting_ideal_area'])==e
        print(v['name'],v['limiting_ideal_area'],v['limiting_ideal_area_decimal'],
              '15 exact Minkowski exclusions passed')
    out={'status':'Exact geometry and area only; analytic potential proof is separate.',
         'results':results}
    Path(__file__).with_name('augmentation-certificates.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':
    main()
