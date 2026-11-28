"""Exact integration and square completion for signed six-width profiles.

This file checks symbolic algebra only. The all-height geometric argument is
in signed-six-width-continuation.md and is independent of these calculations.
"""
import sympy as S

p,q,w=S.symbols('p q w',positive=True)
t=S.symbols('t')
r=p+q
h=(1-w)/r
b=1/(2*p)
U=1-2*p*t
P0=2*w+q-1+2*q*t
V0=(2-U-P0)/2
V1=1-2*w-2*q*t
M0=p-1+2*p*t
m=(2-p-q/2-w)/r
v=(q/2-w)/r
c=(1-q/2-w)/r
lower=S.Rational(1,4)-(1-w)**2/(4*r)
upper=(S.integrate(U,(t,0,h))
       +S.integrate(P0,(t,0,c))+S.integrate(U,(t,c,h))
       +S.integrate(V0,(t,0,v))+S.integrate(V1,(t,v,h))
       +S.integrate(M0,(t,0,m))+S.integrate(V0,(t,m,v))
       +S.integrate(V1,(t,v,h)))/4
E=S.factor(lower+upper)
simple=(24*r+16*w-16-4*p*p-4*p*q-5*q*q-8*p*w-4*q*w-12*w*w)/(32*r)
assert S.factor(E-simple)==0
maximum=(17-6*S.sqrt(2))/28
squares=maximum-(S.sqrt(2)*r-3)**2/(28*r)-(7*q-2*r-2)**2/(336*r)-(2*p+q+6*w-4)**2/(96*r)
assert S.simplify(E-squares)==0
opt={p:(15*S.sqrt(2)-4)/14,q:(3*S.sqrt(2)+2)/7,w:(5-3*S.sqrt(2))/7}
assert S.simplify(E.subs(opt)-maximum)==0
benchmark={p:S.Rational(69,56),q:S.Rational(25,28),w:S.Rational(3,28)}
assert S.factor(E.subs(benchmark))==S.Rational(579,1904)
cuts=[S.factor(f.subs(benchmark)) for f in [0*p,m,v,c,b,h,S.Rational(1,2)]]
assert all(a<bb for a,bb in zip(cuts,cuts[1:]))
assert benchmark[p]>1 and benchmark[p]<2
assert 0<benchmark[q]<benchmark[p]
assert benchmark[w]>0 and 2*benchmark[w]+benchmark[q]-1>=0
print('direct_integral_area=',E)
print('completed_square_identity=PASS')
print('exact_optimum=',maximum)
print('exact_optimum_decimal=',maximum.evalf(30))
print('rational_benchmark=',S.Rational(579,1904))
print('rational_switches=',cuts)
print('irrational_switches=',[S.simplify(f.subs(opt)) for f in [m,v,c,b,h]])
