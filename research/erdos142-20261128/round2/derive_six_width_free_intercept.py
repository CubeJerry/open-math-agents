import sympy as S
p,q,w=S.symbols('p q w',positive=True);t=S.symbols('t');b=1/(2*p);h=(1-w)/(p+q)
U=1-2*p*t;P0=2*w+q-1+2*q*t;V0=(2-U-P0)/2;V1=1-2*w-2*q*t;M0=p-1+2*p*t
ct=S.solve(U-P0,t)[0];vt=S.solve(V0-V1,t)[0];mt=S.solve(V0-M0,t)[0]
AL=S.Rational(1,4)-(1-w)**2/(4*(p+q))
AU=(S.integrate(U,(t,0,b))+S.integrate(P0,(t,0,ct))+S.integrate(U,(t,ct,b))+S.integrate(V0,(t,0,vt))+S.integrate(V1,(t,vt,b))+S.integrate(M0,(t,0,mt))+S.integrate(V0,(t,mt,vt))+S.integrate(V1,(t,vt,b)))/4
A=S.factor(AL+AU)
print('cuts:',ct,vt,mt,'lower_cross:',h)
print('area:',A)
print('d_w:',S.factor(S.diff(A,w)))
wstar=S.solve(S.diff(A,w),w)[0]
print('wstar:',wstar)
Aw=S.factor(A.subs(w,wstar));print('Aw:',Aw)
print('derivatives:',S.factor(S.diff(Aw,p)),S.factor(S.diff(Aw,q)))
sol=S.nsolve([S.diff(Aw,p),S.diff(Aw,q)],(p,q),(1.2,.9),prec=40)
pv,qv=sol;wv=wstar.subs({p:pv,q:qv});print('opt:',pv,qv,wv,'area=',A.subs({p:pv,q:qv,w:wv}).evalf(30))
print('6/5,9/10:',wstar.subs({p:S.Rational(6,5),q:S.Rational(9,10)}),Aw.subs({p:S.Rational(6,5),q:S.Rational(9,10)}))
print('validity cuts opt:',[v.subs({p:pv,q:qv,w:wv}).evalf() for v in [mt,vt,ct,b,h]])
