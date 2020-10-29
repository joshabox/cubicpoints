//X_0(61). Load searchDiv2, reduce, modeqns
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(61,1); //Takes a minute or 3.
X;
assert Genus(X) eq 4;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
M:=al[1];
row:=[&+[RowSequence(M)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]];
w:=iso<X->X | row,row>; //The A-L involution w_{61}.

infcusp:=X![1,0,0,0]; 
assert 1/j(infcusp) eq 0; 
cusp2:=X![1,0,1,1];//
assert 1/j(cusp2) eq 0; //Indeed both are cusps.
assert cusp2 eq w(infcusp); //w acts on the cusps
Dtor:=Divisor(cusp2)-Divisor(infcusp);
assert not IsPrincipal(Dtor); //Sanity check
cusps:=[cusp2,infcusp];
assert IsPrincipal(5*Dtor); //So J_0(43)(\Q)_{tor} \simeq Z/5Z.

//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w]));
E,h:=EllipticCurve(C,projC(infcusp));
XtoE:=Expand(projC*h);
E;
assert Conductor(E) eq 61;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([0])); //Shows MWE is free of rank 1
seqQE:=[QQ : QQ in [phi(MWE.1),phi(-MWE.1)] | QQ eq E![-1,1,1]];
QE:=seqQE[1]; //QE is the claimed point.

//We use this generator to find the free generator of J_0(43)(\Q)
D:=Pullback(XtoE,Place(QE));
D1:=D-1*Place(infcusp)-1*Place(cusp2);
K7<r>:=QuadraticField(-3);
assert r^2 eq -3;
PP:=(X(K7)![ 0, 1/2*(r - 1), 1, 1 ]);
assert Place(PP) eq D; //This shows the generator is as claimed.
bp1:=Place(infcusp);
bp2:=bp1+Place(cusp2);
bp:=2*Place(infcusp)+Place(cusp2);

deg3pb:=[<Place(cusp2),Place(cusp2)+Place(infcusp)>,<Place(infcusp),Place(infcusp)+Place(cusp2)>] cat [<Place(pt),Pullback(XtoE,Place(n*QE))> : pt in cusps, n in [-24..24]];
//For the current implementation of the sieve, it's important that the combinations of cusps come first. It's okay if they occur twice.
deg3npb:=[3*Place(cusp2),3*Place(infcusp)];
excDs := [];
for nn in [[1,-1],[1,2]] do
V,phi:=RiemannRochSpace(bp+nn[1]*D1+nn[2]*Dtor);
Append(~deg3npb,Divisor(phi(V.1))+bp+nn[1]*D1+nn[2]*Dtor);
Append(~excDs,Divisor(phi(V.1))+bp+nn[1]*D1+nn[2]*Dtor);
assert #Decomposition(deg3npb[#deg3npb]) eq 1;
end for;

R<t> := PolynomialRing(Rationals());
K<a> := NumberField(R![-20, -2, 0, 1]); ///cubic field with discriminant = -4*673

// We now express all representatives of all degree 3 points.
for DDD in excDs do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
Factorisation(Integers()!Norm(phi(j(Pt))));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));
end for;


//Finally, we do the sieve.
A:=AbelianGroup([0,5]);
divs:=[D1,Dtor];
genusC:=Genus(C);
rationalpts:=[Place(cusp) : cusp in cusps];
auts:=[al[1]];
I:=2;
load "Cubicsieve.m";
badpts:=[false : i in deg3npb];

smallprimes:=[31,19,53,23];
primes:=[];
assert &and[not IsSingular(ChangeRing(X,GF(p))) : p in smallprimes];

MWSieve(deg3pb,deg3npb,badpts,smallprimes,X,A,divs,auts,genusC,I,bp);

