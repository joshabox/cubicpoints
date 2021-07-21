//The following function computes the expansion of a differential 
//om around the uniformizer tQ of a point Q, up to the (n+1)th coefficient a_n.
ExpandDifferential:=function(om,Q,tQ,n)
assert n ge 0;
dt:=Differential(tQ);
f:=om/dt;
FF:=Parent(f);
K:=Parent(Eltseq(Q)[1]);
XK:=ChangeRing(X,K);
Qpt:=XK!Eltseq(Q);
CRK<[xK]>:=CoordinateRing(AmbientSpace(XK));
FK:=FunctionField(XK);
f:=FK!(Evaluate(Numerator(ProjectiveFunction(f)),xK)/Evaluate(Denominator(ProjectiveFunction(f)),xK));
tQ:=FK!(Evaluate(Numerator(ProjectiveFunction(tQ)),xK)/Evaluate(Denominator(ProjectiveFunction(tQ)),xK));
alist:=[Evaluate(f,Qpt)];
if n gt 0 then
flist:=[(f-(Evaluate(f,Qpt)))/tQ];
for i in [1..n] do
    Append(~alist,flist[i](Qpt));
    Append(~flist,(flist[i]-alist[i+1])/tQ);
end for;
end if;
return alist;
end function;

IsLonely:=function(QQ,X,Xp,p,auts,genusC,omegas)
if p le 13 then return false; end if; //Part of first condition in Theorem
d:=4; //Just there to emphasize that we work on X^{(d)} for d=4.
Fp:=BaseRing(Xp);
Rp<[u]>:=CoordinateRing(AmbientSpace(Xp));
n:=Dimension(AmbientSpace(X)); //Assuming X is given in projective space
matrixseq:=[];
dec:=Decomposition(reduce(X,Xp,QQ));
Fq:=GF(p^(LCM([Degree(ResidueClassField(dd[1])) : dd in dec])));
//Thm 3.2 of Samir also works with (a0,a1/2) when Q_1 neq Q_2 but Q1tilde = Q2tilde.
for i in [1..#dec] do
    Qtilde:=dec[i][1]; 
    m:=dec[i][2];
    Kp:=ResidueClassField(Qtilde);
    Embed(Kp,Fq);
    Qtildept:=Eltseq(RepresentativePoint(Qtilde));
    if Degree(Kp) eq 1 then frobs:=[IdentityHomomorphism(Kp)];
    else
    frob:=hom< Kp->Kp | (Kp.1)^p >;
    frobs:=[frob];
    for j in [1..Degree(Kp)-1] do
        Append(~frobs,frob*frobs[#frobs]);
    end for;
    end if;
    assert #frobs eq Degree(Kp);
    Qtildes:=[Xp(Kp)![fr(a) : a in Qtildept] : fr in frobs];// the above was just a process to list all the points in a place
    tQtildes:=[UniformizingParameter(Qtilde) : Qtilde in Qtildes];
    for k in [1..#tQtildes] do
        omlist:=[ExpandDifferential(om,Qtildes[k],tQtildes[k],m-1) : om in omegas];
        for jj in [1..m] do
        Append(~matrixseq,[Fq!om[jj]/jj : om in omlist]);
        end for;
    end for;
end for;
Atilde:=Matrix(matrixseq);
if Rank(Atilde) eq d then return true;
else return false, Rank(Atilde);
end if;
end function;

/////////////////////////////////////////////////////////////////////////

ALMap := function(X,auts)
R<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X)); //Assuming X is given in projective space
row:=[&+[RowSequence(auts[1])[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]]; 
//Note that this function is only called upon for N \neq 57 so #auts = 1
return iso<X -> X | row,row>;
end function;
eta:=ALMap(X,auts);

//////////////////////////////////////////////////////////////////////////
rationalpts:=[Place(cusp) : cusp in cusps];
//////////////////////////////////////////////////////////////////////////
/// I should just check I don't need to bring in any additional cases in the below.


IsOnlyWithFamily:=function(pb,X,Xp,p,auts,genusC,omegas)
Fp:=BaseRing(Xp); Fq:=GF(p^12);
p:=Characteristic(Fp); // Don't need to input p really I guess?
Embed(Fp,Fq);
if p lt 14 then return false;
 end if;
 dec := [];


// The function is written so that it can accept two different types of points on X^(4)(QQ) which should belong to an infinite family
//  - those of the form pullback from C^2(QQ) and those which are the sum of a pullback from C(QQ) and an element of X^(2)(QQ)

if Type(pb) eq DivCrvElt then
  dec := Decomposition(reduce(X,Xp,pb)); // in this case we have a "quartic pullback". These ones are given as divisors and are known to be a pullbacks from C^(2)(QQ)
  rankcondition := 2;
else 
  rankcondition := pb[3]; // if pb[1] isn't a pullback, then pb[3] = 3, else pb[3]=2. pbb[2] is always a pullback
  decomps := [Decomposition(reduce(X,Xp,pb[i])) : i in [1,2]];
  predec := &cat decomps;// decomposing divisors of large degree is costly, so we use this as a work around
  places := {predec[i][1]: i in {1..#predec}};
  for Pl in places do
    Plm :=0;
	for PD in predec do
	 if Pl eq PD[1] then
	  Plm+:= PD[2];
	 end if;
	end for;
	Append(~dec,<Pl,Plm>);
  end for;
  dec := Setseq(Seqset(dec));//to get rid of multiple entries.
end if;



//We now remove anything which could lead A to have an unjustly large rank, and also pick the points allowed by the main theorem which lead A to have the greatest possible rank
if rankcondition eq 2 then
	if dec[1][2] gt 2 then
		dec := [<dec[1][1],2>]; // If the reduction is of the form 3P+Q, then the main theorem would allow us to choose 2P or P+Q, and choosing P+Q would prevent A from having rank 2
	elif #dec eq 1 then
		dec := [<dec[1][1],1>];
	elif dec[2][2] eq 3  then
		dec := [<dec[2][1],2>];

	// We now deal with the 2P+2Q case
	elif #dec eq 2 and Type(pb) ne DivCrvElt then 
		dec := [<decomps[1][1][1],1>,<decomps[1][1][1] eq decomps[2][1][1] select decomps[2][1][1] else decomps[2][2][1],1>];
	elif #dec eq 2 and Type(pb) eq DivCrvElt then
		dec := [<dec[1][1],1>,<dec[2][1],1>];//Not perfect, but with the sieve this shouldn't cause too much of a problem (we're having to choose P+Q here, where we'd rather choose 2P or 2Q)
	
	//Finally we treat the 2P + Q + R case
	elif (dec[1][2] eq 2 or dec[2][2] eq 2 or dec[3][2] eq 2) and Type(pb) ne DivCrvElt then
		//need to check whether reduction of one pullback is twice a point
		if decomps[1][1][2] eq 2 then
			dec := [<decomps[1][1][1],1>,<decomps[2][1][1],1>];
		elif decomps[2][1][2] eq 2 then
			dec := [<decomps[1][1][1],1>,<decomps[2][1][1],1>];// We don't immediately define dec in this way, because if the reduction looks like 2*P+Q+R and 2*P isn't the reduction of one of the pullbacks then we should consider the "2P" matrix
		end if;
	elif (dec[1][2] eq 2 or dec[2][2] eq 2 or dec[3][2] eq 2) and Type(pb) eq DivCrvElt then
		dec := [<dec[1][1],1>,<dec[2][1],1>,<dec[3][1],1>];//Again, not perfect, but shouldn't be a problem
	end if;
end if;


if rankcondition eq 3 and decomps[2][1][2] eq 2 then
dec := decomps[1] cat [<decomps[2][1][1],1>];// again we want to stop a double point in the reduction coming from a pullback, but allow there to be double points, if they don't come from pullbacks.
end if;


// we calculate A.
matrixseq:=[];

predec := dec;
dec := [];

  Multiplicities := [Multiplicity(predec, predec[i]): i in [1 .. #predec]];

  for i in [1 .. #predec] do
    Append(~dec, <predec[i][1],predec[i][2]*Multiplicities[i]>);
  end for;
  dec := Setseq(Seqset(dec));//to get rid of multiple entries.


for i in [1..#dec] do
    Qtilde:=dec[i][1]; 
    m:=dec[i][2];
    Kp:=ResidueClassField(Qtilde);
    Embed(Kp,Fq);
    Qtildept:=Eltseq(RepresentativePoint(Qtilde));
    if Degree(Kp) eq 1 then frobs:=[IdentityHomomorphism(Kp)];
    else
    frob:=hom< Kp->Kp | (Kp.1)^p >;
    frobs:=[frob];
    for j in [1..Degree(Kp)-1] do
        Append(~frobs,frob*frobs[#frobs]);
    end for;
    end if;
    assert #frobs eq Degree(Kp);
    Qtildes:=[Xp(Kp)![fr(a) : a in Qtildept] : fr in frobs];// the above was just a process to list all the points in a place
    tQtildes:=[UniformizingParameter(Qtilde) : Qtilde in Qtildes];
    for k in [1..#tQtildes] do
        omlist:=[ExpandDifferential(om,Qtildes[k],tQtildes[k],m-1) : om in omegas];
        for jj in [1..m] do
        Append(~matrixseq,[Fq!om[jj]/jj : om in omlist]);
        end for;
    end for;
end for;
Atilde:=Matrix(matrixseq);
if Rank(Atilde) eq 4 then
Atilde;
dec;
Pt := RepresentativePoint(Decomposition(pb[1])[1][1]);
Degree(Place(projC(Pt)));
"This point appears to lonely";
end if;
if Rank(Atilde) ge rankcondition then return true,Rank(Atilde),rankcondition;
else return false;
end if;
end function;



//////////////////////////////////////////////////////////




ChabautyInfo:=function(LpbQuad,LpbQuartic,Lnpb,p,X,auts,genusC,A,B,iA,W,divs,I,bp,bp2)
Fp:=GF(p); Fp2:=GF(p^2);
Xp:=ChangeRing(X,Fp);
Rp<xp,yp,zp>:=CoordinateRing(AmbientSpace(Xp));
Cp:=ChangeRing(C,Fp);
CCC,phi,psi:=ClassGroup(Xp);
Z:=FreeAbelianGroup(1);
degr:=hom<CCC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CCC)]>;
JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
divsp:=[reduce(X,Xp,divi) : divi in divs];
bpp:=reduce(X,Xp,bp); //We reduce the divisors and the basepoint
//bpp1:=reduce(X,Xp,bp1);
bpp2:=reduce(X,Xp,bp2);
assert Degree(bpp2) eq 2;
h:=hom<A -> JFp | [JFp!psi(divp) : divp in divsp]>; //The map A --> J_X(\F_p).

Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>;
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
WW:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)];
mI:=hom<JFp -> JFp | [I*g : g in OrderedGenerators(JFp)]>;
imW:={h(x) : x in WW | h(x) in Image(mI)}; //The possible images in JFp of unknown rat. pts., (before mult. by n.)
K:=Kernel(mI);

//JFp often contains factors Z/qZ with q a large prime. If there is no (or few) other prime p' such that JFp' also contains a Z/qZ factor, then this mod q information is (almost) useless. This is likely to happen for large q. Hence we choose only to consider the mod q information for q le 23. This speeds up computations, as the index of B in A remains small.
fact:=Factorisation(#JFp);
n:=&*([1] cat [pp[1]^(pp[2]) : pp in fact | pp[1] gt 23]);
mn:=hom<JFp -> JFp | [n*g : g in OrderedGenerators(JFp)]>; 

// Compute ann. differentials of trace zero
dim:=Dimension(AmbientSpace(X)); //Assuming X is given in projective space
ws:=[]; //The set of mod p Atkin-Lehner involution(s)
for M in auts do
    row:=[&+[RowSequence(M)[i][j]*u[j] : j in [1..dim+1]] : i in [1..dim+1]];
    Append(~ws,iso<Xp->Xp | row,row>);
end for;
VV,phii:=SpaceOfDifferentialsFirstKind(Xp);
ts:=[hom<VV->VV | [ (Pullback(wp,phii(VV.i)))@@phii -VV.i  : i in [1..Genus(X)] ]> : wp in ws];
T:=&+[Image(t): t in ts]; //The space of vanishing differentials
if not p eq 2 then assert Dimension(T) eq Genus(X) - genusC; end if; //cf Remark 3.7.
omegas:=[phii(T.i) : i in [1..Dimension(T)]]; //A basis of vanishing differentials

redL1pbQuad:=[<reduce(X,Xp,DD[1]),reduce(X,Xp,DD[2])> : DD in LpbQuad];
assert &and[[Degree(DD[1]),Degree(DD[2])] eq [2,2] : DD in redL1pbQuad];
redL1pbQuartic:=[reduce(X,Xp,DD) : DD in LpbQuartic];
redL1npb:=[reduce(X,Xp,DD) : DD in Lnpb];
redLpbQuad:=[<JFp!psi(DD[1]-bpp2),JFp!psi(DD[2]-bpp2)> : DD in redL1pbQuad]; 
redLpbQuadsum:=[DD[1]+DD[2] : DD in redLpbQuad];
redLpbQuartic:=[JFp!psi(DD-bpp) : DD in redL1pbQuartic];
redLnpb:=[JFp!psi(DD-bpp) : DD in redL1npb];
mnjposP:=[];

for x in imW do
    if not mn(x) in mnjposP then //This if statement is usually not satisfied,thus saving us from a lot of unnecessary work.
    z:=x@@mI; //We reconstruct possible mod p points from their image in JFp, by first taking inverse images under mI.
    if &or[Dimension(phi(z+k)+bpp) gt 0
	and ( (p in [3,7,11,13]) 
	or (not (z+k) in redLnpb cat redLpbQuartic cat redLpbQuadsum)
	or ((z+k) in redLnpb and not IsLonely(Lnpb[Index(redLnpb,z+k)],X,Xp,p,auts,genusC,omegas)) 
	or ((z+k) in redLpbQuartic and not IsOnlyWithFamily(LpbQuartic[Index(redLpbQuartic,z+k)],X,Xp,p,auts,genusC,omegas))
	or ((z+k) in redLpbQuadsum and not IsOnlyWithFamily(LpbQuad[Index(redLpbQuadsum,z+k)],X,Xp,p,auts,genusC,omegas))
	) : k in K] then
        Append(~mnjposP,mn(x)); //Finally we only store the information multiplied by n.
    end if;
    end if;
end for;

print "The nr of pts in mnjposP is"; #mnjposP;
h:=h*mn;
Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>;
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
W:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)];
B:=newB; iA:=newiA;
W:=[x : x in W | h(x) in mnjposP];
return W,B,iA; 
end function;

MWSieve:=function(LpbQuad, LpbQuartic,Lnpb,smallprimes,X,A,divs,auts,genusC,I,bp,bp2)
print "Welcome to our sieve.";
print "If I return true then all points are known.";

// We now set up the sieve.
B,iA:=sub<A|A>; // This subgroup will shrink as we consider more primes. 
W:={0*A.1}; // This will be our set of possible B-cosets in A. Will grow.
// Together, B+W \subset A consists of the possible images of unknown (rational)
// points in A. The map X(\Q) \to A is composition of X(\Q) \to J(X)(\Q) and
// multiplication by integer I such that I*J(X)(\Q) \subset A.
for p in smallprimes do
print "We consider the prime"; p;
W,B,iA:=ChabautyInfo(LpbQuad, LpbQuartic,Lnpb,p,X,auts,genusC,A,B,iA,W,divs,I,bp,bp2);
print "The number of cosets in J(X)(Q) where unknown points can land is"; #W;
smallsols:=[w : w in W | &+[AbsoluteValue(Integers()!a) : a in Eltseq(w)] lt 100];
if #smallsols gt 0 then smallsols; end if;
if W eq [] then 
print "Wait, did I say 0? I guess I did, didn't I? That must mean that there aren't any unknown points then, hurray!";
return true; end if;
end for;

return W,B,iA;
end function;
