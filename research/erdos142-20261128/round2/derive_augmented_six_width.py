"""Exact symbolic area optimization for triangular-hole extensions.

The geometry and potential hypotheses are separate from this symbolic algebra.
Stationary points below are numerical, not global maximum certificates.
"""
import sympy as S

p,q,w=S.symbols('p q w',positive=True)
b=1/(2*p)
h=(1-w)/(p+q)
A=-(4*p**4+4*p**3*q+8*p**3*w-24*p**3+5*p**2*q**2+4*p**2*q*w-24*p**2*q+28*p**2*w**2-32*p**2*w+20*p**2+16*p*q*w-8*p*q+4*q**2)/(32*p**2*(p+q))
H=S.factor((p+q)*(h-b)**2)
for gamma in [S.Rational(2,27),S.Rational(1,13),S.Rational(1,7)]:
    E=S.factor(A+gamma*H)
    ws=S.solve(S.diff(E,w),w)[0]
    Es=S.factor(E.subs(w,ws))
    stationary=S.nsolve([S.diff(Es,p),S.diff(Es,q)],(p,q),(1.206,.903),prec=45)
    pp,qq=stationary
    ww=ws.subs({p:pp,q:qq})
    print('patch_fraction=',gamma)
    print('optimized_intercept=',ws)
    print('optimized_area_formula=',Es)
    print('stationary_parameters=',pp,qq,ww)
    print('stationary_area=',E.subs({p:pp,q:qq,w:ww}).evalf(30))
    for pp,qq in [(S.Rational(6,5),S.Rational(9,10)),(S.Rational(str(float(pp))).limit_denominator(1000),S.Rational(str(float(qq))).limit_denominator(1000))]:
        ww=S.factor(ws.subs({p:pp,q:qq}))
        params={p:pp,q:qq,w:ww}
        print('rational_parameters=',pp,qq,ww)
        print('base_area=',S.factor(A.subs(params)))
        print('hole_area=',S.factor(H.subs(params)))
        print('limiting_augmented_area=',S.factor(E.subs(params)),float(E.subs(params)))
        cuts=[(2-p-q/2-w)/(p+q),(q/2-w)/(p+q),(1-q/2-w)/(p+q),b,h,S.Rational(1,2)]
        exact_cuts=[S.factor(t.subs(params)) for t in cuts]
        assert all(a<bb for a,bb in zip(exact_cuts,exact_cuts[1:]))
        print('ordered_switches=',exact_cuts)
