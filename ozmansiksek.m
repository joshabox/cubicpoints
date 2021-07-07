//This code was written by Ozman and Siksek, except for the function searchDiv3, which was added by Box.
//---------------------------------------------------------
//
// Function for writing down equations for X_0(N)
// and the j-map.
//
//-------------------------------------------------------- 


// Let N be a positive integer and n be a proper divisor.
// Suppose X_0(N) has genus \ge 3 and is not hyperelliptic.
// It is assumed that X_0(n) is in the Small Modular Curves database (n=1 is allowed).
// The function returns
// X,Z,phi,j, al, <num,denom>.
// X is the modular curve X_0(N)
// Z is the modular curve X_0(n) (exactly the same model as given by the Small Modular Curve package).
// \phi : X_0(N) \rightarrow X_0(n) is the degeneracy map.
// j is the j-function on X_0(N) as an element of its function field.
// al is a list of matrices whose action on the ambient projective space
// correspond to Atkin-Lehner involutions on X.
// num and denom are elements of the coordinate ring of the ambient
// space of X, such that num/denom restricted to X is the j-map.
modeqns:=function(N,n);
	assert IsDivisibleBy(N,n);
	gen0:=[1..10] cat [12, 13, 16, 18, 25]; // Values of N for which X_0(N) has genus 0.
	gen1:=[11, 14, 15, 17, 19, 20, 21, 24, 27, 32, 36, 49]; // Values of N for which X_0(N) has genus 1.
	hyp:=[37] cat [40,48] cat [22,23,26,28,29,30,31,33,35,39,41,46,47,50,59,71]; // Values of N for which X_0(N) is hyperelliptic.
	// These values are taken from Ogg's paper, "Hyperelliptic Modular Curves", Bull. Soc. math. France, 102, 1974, p. 449-462.
	assert #gen0 eq 15;
	assert #gen1 eq 12;
	assert #hyp eq 19;
	assert N in (gen0 cat gen1 cat hyp) eq false;
	// Thus X_0(N) has genus \ge 3 and is non-hyperelliptic, so the canonical map is an embedding.
	// We use this to construct the equations for X_0(N).
	prec:=500;
	L<q> := LaurentSeriesRing(Rationals(),prec);
	S:=CuspForms(N);
	dim:=Dimension(S);
	if dim eq 3 then
		R<x_0,x_1,x_2>:=PolynomialRing(Rationals(),dim);
	elif dim eq 4 then 
		R<x_0,x_1,x_2,x_3>:=PolynomialRing(Rationals(),dim);
	elif dim eq 5 then
		R<x_0,x_1,x_2,x_3,x_4>:=PolynomialRing(Rationals(),dim);
	else
		R<[x]>:=PolynomialRing(Rationals(),dim);
	end if;
	Bexp:=[L!qExpansion(S.i,prec) : i in [1..dim]];
	eqns:=[R | ];
	d:=1;
	tf:=false;
	while tf eq false do
		d:=d+1;
		mons:=MonomialsOfDegree(R,d);
		monsq:=[Evaluate(mon,Bexp) : mon in mons];
		V:=VectorSpace(Rationals(),#mons);
		W:=VectorSpace(Rationals(),prec-10);
		h:=hom<V->W | [W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]]>;
		K:=Kernel(h);
		eqns:=eqns cat [ &+[Eltseq(V!k)[j]*mons[j] : j in [1..#mons] ] : k in Basis(K)  ];
		X:=Scheme(ProjectiveSpace(R),eqns);
		if Dimension(X) eq 1 then
			if IsSingular(X) eq false then
				X:=Curve(ProjectiveSpace(R),eqns);
				if Genus(X) eq dim then
					tf:=true;
				end if;
			end if;
		end if;
	end while;
	eqns:=GroebnerBasis(ideal<R | eqns>); // Simplifying the equations.
	tf:=true;
	repeat
		t:=#eqns;
		tf:=(eqns[t] in ideal<R | eqns[1..(t-1)]>);
		if tf then 
			Exclude(~eqns,eqns[t]);
		end if;
	until tf eq false;
	t:=0;
	repeat
		t:=t+1;
		tf:=(eqns[t] in ideal<R | Exclude(eqns,eqns[t])>);	
		if tf then
			Exclude(~eqns,eqns[t]);
			t:=0;
		end if;
	until tf eq false and t eq #eqns;
	X:=Curve(ProjectiveSpace(R),eqns); // Our model for X_0(N) discovered via the canonical embedding.
	assert Genus(X) eq dim;
	assert IsSingular(X) eq false;
	// We now check the equations for X rigorously, i.e.
	// up to the Sturm bound.
	indexGam:=N*&*[Rationals() | 1+1/p : p in PrimeDivisors(N)];	
	indexGam:=Integers()!indexGam; // Index of Gamma_0(N) in SL_2(Z)
	for eqn in eqns do
		eqnScaled:=LCM([Denominator(c) : c in Coefficients(eqn)])*eqn;
		wt:=2*Degree(eqn); // Weight of eqn as a cuspform.
		hecke:=Ceiling(indexGam*wt/12);  // Hecke=Sturm bound.
										// See Stein's book, Thm 9.18.
		Bexp1:=[qExpansion(S.i,hecke+10) : i in [1..dim]]; // q-expansions
                        // of basis for S 
                        // up to precision hecke+10.
		assert Valuation(Evaluate(eqnScaled,Bexp1)) gt hecke+1;
	end for; // We have now checked the correctness of the equations for X.
	Z:=SmallModularCurve(n); 
	KZ:=FunctionField(Z);
	qEZ:=qExpansionsOfGenerators(n,L,prec); // This gives gives qExpansions of the generators
						// of the function field of Z=X_0(n) as Laurent series in q. 
	KX:=FunctionField(X);
	KXgens:=[KX!(R.i/R.dim) : i in [1..(dim-1)]] cat [KX!1]; // The functions x_i/x_dim as elements of the function field of X.
	coords:=[]; // This will contain the generators of the function field of Z as element of the function of X.
	for u in qEZ do
		//We want to express u as an element of the function field of X=X_0(N).
		Su:={};
		d:=0;
		while #Su eq 0 do
			d:=d+1;
			mons:=MonomialsOfDegree(R,d);
			monsq:=[Evaluate(mon,Bexp) : mon in mons];
			V:=VectorSpace(Rationals(),2*#mons);
			W:=VectorSpace(Rationals(),prec-10);
			h:=hom<V->W | 
				[W![Coefficient(monsq[i],j) : j in [1..(prec-10)]] : i in [1..#mons]] 
				cat  [ W![Coefficient(-u*monsq[i],j) : j in [1..(prec-10)]  ]  : i in [1..#mons] ]>;
			K:=Kernel(h);
			for a in [1..Dimension(K)] do
				num:=&+[Eltseq(V!K.a)[j]*mons[j] : j in [1..#mons] ];
				denom:=&+[Eltseq(V!K.a)[j+#mons]*mons[j] : j in [1..#mons] ];
				numK:=Evaluate(num,KXgens); 
				denomK:=Evaluate(denom,KXgens);
				if numK ne KX!0 and denomK ne KX!0 then
					Su:=Su join {numK/denomK};
				end if;
			end for;
		end while;
		assert #Su eq 1;
		coords:=coords cat SetToSequence(Su);
	end for;
	phi:=map<X -> Z | coords cat [1]>;
	jd:=Pullback(phi,jFunction(Z,n));
		P:=AmbientSpace(X);
		R:=CoordinateRing(P);
		assert Rank(R) eq dim;
		num:=Numerator(FunctionField(P)!jd);
		denom:=Denominator(FunctionField(P)!jd);
		num:=Evaluate(num,[R.i : i in [1..(dim-1)]]);
		denom:=Evaluate(denom,[R.i : i in [1..(dim-1)]]);
		deg:=Max([Degree(num),Degree(denom)]);
		num:=Homogenization(num,R.dim,deg);
		denom:=Homogenization(denom,R.dim,deg);
		assert Evaluate(num,KXgens)/Evaluate(denom,KXgens) eq jd;	
		// We compute the degree of j : X_0(N) --> X(1) using the formula
		// in Diamond and Shurman, pages 106--107.
		assert N gt 2;
		dN:=(1/2)*N^3*&*[Rationals() | 1-1/p^2 : p in PrimeDivisors(N)];
		dN:=Integers()!dN;
		degj:=(2*dN)/(N*EulerPhi(N));
		degj:=Integers()!degj; // Degree j : X_0(N)-->X(1)
		degjd:=&+[-Valuation(jd,P)*Degree(P) : P in Poles(jd)];
		assert degj eq degjd;
		// Now if j \ne jd then the the difference j-jd is a rational
		// function of degree at most 2*degj (think about the poles).
		// Hence to prove that j=jd all we have to check is that their
		// q-Expansions agree up to 2*degj+1.
		jdExpansion:=Evaluate(num,Bexp)/Evaluate(denom,Bexp);
		jdiff:=jdExpansion-jInvariant(q);
		assert Valuation(jdiff) ge 2*degj+1; // We have proven the corrections of the
										// j-map jd on X_0(N).
	// Next we want to write down the matrices for the Atkin-Lehner
	// operators on X_0(N)
	alindices:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];
	al:=[AtkinLehnerOperator(S,m) : m in alindices];
	return X, Z, phi, jd, al, <num,denom>;
end function;

// Search for divisors of degree 2
// Given a curve X/\Q as before, and a bound bd and a true/false tf
// this function returns
// deg2,pls1,pls2,plsbig
// Here pls1 is a set of places of degree 1
// pls2 is a set of places of degree 2 and
// plsbig is a set of places of degree at least 3 but less than genus.
// pls1 are found by a search for rational points on X
// pls2, plsbig are found by intersecting hyperplanes with X.
// deg 2 are the known degree 2 effective divisors: sums of pairs of
// elements of pls1, and elements of pls2.
// If tf=true then the automorphism group of X is used
// to enlarge the sets pls1 and pls2 (if possible).

searchDiv2:=function(X,bd,tf);
	g:=Genus(X);
	//
	// First we find degree 1 points
	pts:=PointSearch(X , 1000);
	pls1:={Place(P) : P in pts};
	pls2:={};
	plsbig:={};
	R:=CoordinateRing(AmbientSpace(X));
	n:=Rank(R);
	// Next we intersect X with hyperplanes with coefficients bounded by bd
	// and see what divisors we obtain.
	C:=CartesianPower([-bd..bd],n);
	ctr:=0;
	for a in C do
		ctr:=ctr+1;
		//print #C,ctr,#pls1, #pls2,#plsbig;
		b:=[a[i] : i in [1..n]];
		if &or[b[i] ne 0 : i in [1..n]] then
			if GCD(b) eq 1 and b[1] ge 0 then
				f:=&+[b[i]*R.i : i in [1..n]];
				D:=Divisor(X,ideal<R | f>);
				decomp:=Decomposition(D);
				for pr in decomp do
					P:=pr[1];
					if Degree(P) eq 1 then
						pls1:=pls1 join {P};
					else
						if Degree(P) eq 2 then
							pls2:=pls2 join {P};
						else
							if Degree(P) le g then
								plsbig:=plsbig join {P};
							end if;
						end if;
					end if;
				end for;
			end if;
		end if;
	end for;
	if tf then
		A:=Automorphisms(X); // We will use the automorphisms of X
						// to enlarge the sets pls1, pls2.
		for phi in A do
			for P in pls1 do
				D:=Pullback(phi,P);
				pls1:=pls1 join {Decomposition(D)[1,1]};
			end for;
			for P in pls2 do
				D:=Pullback(phi,P);
				pls2:=pls2 join {Decomposition(D)[1,1]};
			end for;
		end for;
	end if;
	pls1:=SetToSequence(pls1);
	pls2:=SetToSequence(pls2);
	plsbig:=SetToSequence(plsbig);
	deg2:=[];
	for i,j in [1..#pls1] do
		if i le j then
			Append(~deg2,1*pls1[i]+1*pls1[j]);
		end if;
	end for;
	deg2:=deg2 cat [1*P : P in pls2];
	return deg2,pls1,pls2,plsbig;
end function;



// X is a projective curve over rationals,
// p prime of good reduction,
// D divisor on X,
// This reduces to a divisor on X/F_p.

reduce:=function(X,Xp,D);
	if Type(D) eq DivCrvElt then
		decomp:=Decomposition(D);
		return &+[ pr[2]*$$(X,Xp,pr[1]) : pr in decomp]; // Reduce the problem to reducing places.
	end if;
	assert Type(D) eq PlcCrvElt;
	if  Degree(D) eq 1 then
		P:=D;
		R<[x]>:=CoordinateRing(AmbientSpace(X));
		m:=Rank(R);
		KX:=FunctionField(X);
		inds:=[i : i in [1..m] | &and[Valuation(KX!(x[j]/x[i]),P) ge 0 : j in [1..m]]];	
		assert #inds ne 0;
		i:=inds[1];
		PP:=[Evaluate(KX!(x[j]/x[i]),P) : j in [1..m]];
		denom:=LCM([Denominator(d) : d in PP]);
		PP:=[Integers()!(denom*d) : d in PP];
		g:=GCD(PP);
		PP:=[d div g : d in PP];
		Fp:=BaseRing(Xp);
		PP:=Xp![Fp!d : d in PP];
		return Place(PP);	
	end if;
	I:=Ideal(D);
	Fp:=BaseRing(Xp);
	p:=Characteristic(Fp);
	B:=Basis(I) cat DefiningEquations(X);
	m:=Rank(CoordinateRing(X));
	assert Rank(CoordinateRing(Xp)) eq m;
	R:=PolynomialRing(Integers(),m);
	BR:=[];
	for f in B do
		g:=f*p^-(Minimum([Valuation(c,p) : c in Coefficients(f)]));
		g:=g*LCM([Denominator(c) : c in Coefficients(g)]);
		Append(~BR,g);
	end for;
	J:=ideal<R | BR>;
	J:=Saturation(J,R!p);
	BR:=Basis(J);
	Rp:=CoordinateRing(AmbientSpace(Xp));
	assert Rank(Rp) eq m;
	BRp:=[Evaluate(f,[Rp.i : i in [1..m]]) : f in BR];
	Jp:=ideal<Rp| BRp>;
	Dp:=Divisor(Xp,Jp);
	return Dp;
end function;
