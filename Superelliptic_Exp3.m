// Attach relevant code from Molin--Neurohr package
AttachSpec("/PATH/TO/spec");
load "PATH/TO/se_periods/se_symplectic_basis.m";

N:=100000; // compute for primes <= N, may need to be increased for larger conductors
primes:=[p : p in [1..N] | IsPrime(p)];

_<b>:=PolynomialRing(Rationals());
K<z>:=CyclotomicField(3);
R<t>:=PolynomialRing(K);
A<x,y>:=AffineSpace(K,2);

// declare the curve here via quartic polynomial in t
f:=t^4+t^3+(z)*t^2-z-2;
bad_primes:={3}join{p[1] : p in Factorisation(Integers()!Norm(Discriminant(f)))};
cond:=3^12*7^2*13; //conductor if known!

C:=Curve(A, y^3 - Evaluate(f,x));
g:=Genus(C); assert g eq 3;
// to reconstruct over the finite fields
poly_coeffs:=[Eltseq(coeff) : coeff in Coefficients(f)];
// bodge because Magma begins Coefficients with the lowest degree term of f (sometimes, maybe?)
while #poly_coeffs lt 1+Degree(f) do
	poly_coeffs:=[[0,0]]cat poly_coeffs;
end while;

// initialise Euler factors
euler_factors:=AssociativeArray(Integers());

// Newton identities function for later
function Newton_ids(pow_sums);
	num:=#pow_sums;
	if num eq 1 then
		return pow_sums[1];
	else if num eq 2 then
		return (pow_sums[1]^2-pow_sums[2])/2; 
	else if num eq 3 then 
		return (1/2*pow_sums[1]^3-3/2*pow_sums[1]*pow_sums[2]+pow_sums[3])/3;
	else if num eq 4 then
		return (pow_sums[1]^4/6-pow_sums[1]^2*pow_sums[2]+4/3*pow_sums[1]*pow_sums[3]+pow_sums[2]^2/2-pow_sums[4])/4;
	end if; end if; end if; end if;
end function;

// The curve C has an automorphism alpha of order 3 (that sends y to z y) and we compute the fixed points of the composition of this automorphism with Frobenius. The fixed points correspond to points on the `twisted' curve u*y^3 = f(x).
// poly_finder returns the (truncated) local polynomial at one of the isotypic pieces of the Tate module of the curve.

function poly_finder(F,zeta,pow);	
	// Sanity checks
	assert zeta in F;
	assert zeta^3 eq One(F);	
	// Recover the characteristic and the size of the field
	p := Characteristic(F);
	q := #F;

	// start your engines...
	printf "Computing p=%o, q=%o, ... ", p, q;

	// Create the curve
	AA<xx,yy>:=AffineSpace(F,2);
	// reconstruct y^3 = f over F
	F_coeffs:=[coeff[1]+zeta*coeff[2] : coeff in poly_coeffs];
	f_F:=Evaluate(Polynomial(F_coeffs),xx);
	CF:=ProjectiveClosure(Curve(AA, yy^3 - f_F));

	// obtain traces for later
	C_traces:=[1+#F^ii - #Points(BaseChange(CF,ext<F|ii>)) : ii in [1..pow]];

	// aa will hold the trace of successive powers of alpha*Frob
	aa:=[];
	for jj in [1..2] do
		cput := Cputime();

		// Build the auxiliary curve over F
		// Compute u such that u*yy^3 = f_F is the eqn of a curve on which Frobenius acts as zeta*Frob does on C
		GG,m:=MultiplicativeGroup(F);
		u:=m(GG.1);
		while not u^Integers()!((#F-1)/3) eq zeta^(-jj) do
			u:=u^2;
		end while;
		
		// Twisted curve
		CC:=ProjectiveClosure(Curve(AA,u*yy^3-f_F));
		
		// Count the points
		ind := pow;
		if pow gt 2 then ind:=2; end if;
		aa cat:=[1+#F^ii - #Points(BaseChange(CC,ext<F|ii>)) : ii  in [1..ind] ];
	end for;

	if pow eq 3 then 
		for jj in [1..2] do
			FF:=ext<F|3>;
			GG,m:=MultiplicativeGroup(FF);
			u:=m(GG.1);
			while not u^Integers()!((#FF-1)/3) eq zeta^(-jj) do
				u:=u^2;
			end while;
		
			AA<xx,yy>:=AffineSpace(FF,2);
			CC:=ProjectiveClosure(Curve(AA,u*yy^3-Evaluate(f_F,[xx,yy])));
			aa cat:=[1+#FF - #Points(CC)];
		end for;
		aa:=[aa[1],aa[2],aa[5],aa[3],aa[4],aa[6]];
	end if;

	traces:=[ 1/3*(C_traces[ii] + (z^(1+(ii mod 2)))*aa[ii] + (z^(1+((1+ii) mod 2)))*aa[pow + ii]) : ii in [1..pow] ];

	poly:=1-traces[1]*t;
	for ii in [2..pow] do
		poly +:=(-t)^ii*Newton_ids([traces[jj] : jj in [1..ii]]);
	end for;
	printf "done (%os)\n", Cputime(cput);
	return Evaluate(poly,t^Round(Log(p,q)));
end function;

for ii in [ii : ii in [1..#primes] | not primes[ii] eq 3 ] do
	p:=primes[ii];
	try 
		already := euler_factors[p];
	catch e
		pp_s := Factorisation(ideal<RingOfIntegers(K)|p>);
	
		euler_factors[p]:=R!1;
	
		pp:=pp_s[1][1];
		if Norm(pp) eq p then
			F:=GF(p);
			pow:=Floor(Log(p,N));
			if pow gt 3 then pow:=3; end if;
			_<x>:=PolynomialRing(F);
			for zeta in Roots(x^2+x+1) do 
			// each choice of zeta corresponds to one of the (conjugate) primes above p
				euler_factors[p]*:=poly_finder(F,zeta[1],pow);			
			end for;
		end if;
	
		if Norm(pp) eq p^2 then
			F:=GF(p^2);
			_<x>:=PolynomialRing(F);
			// choice of zeta doesn't matter in this case
			zeta:=Roots(x^2+x+1)[1][1];
			pow:=Floor(Log(p^2,N));
			if pow eq 0 then continue; end if;
			if pow gt 3 then pow:=3; end if;
			euler_factors[p]*:=poly_finder(F,zeta,pow);				
		end if;
	end try;
end for;

// set up complexes for the L-functions
CC:=ComplexField();
S<X>:=PolynomialRing(CC);
Zeta_CC:=CC!z;

exact2complex := function(poly); // convert exact polynomial to one with complex coefficients for the L-series
	comp_poly:=S!0;
	coeffs:=Coefficients(poly);                                                                                                
	for ii in [1..#coeffs] do
		for jj in [1..#Eltseq(coeffs[ii])] do
			comp_poly +:= CC!(Eltseq(coeffs[ii])[jj])*Zeta_CC^(jj-1)*X^(ii-1);
		end for;
	end for;
	return comp_poly;
end function;

exact2conj := function(poly); // convert exact polynomial to one with complex coefficients for the L-series
	comp_poly:=S!0;
	coeffs:=Coefficients(poly);                                                                                                
	for ii in [1..#coeffs] do
		for jj in [1..#Eltseq(coeffs[ii])] do
			comp_poly +:= ComplexConjugate(CC!(Eltseq(coeffs[ii])[jj])*Zeta_CC^(jj-1))*X^(ii-1);
		end for;
	end for;
	return comp_poly;
end function;

euler_factors[3]:=R!1;

factors:=function(p);
	try
		return euler_factors[p];
	catch e
		return R!1;
	end try;
end function;

Z := LSeries(2, [0,0,0,1,1,1], cond, 0 : Precision:=12);
LSetCoefficients(Z, func<p,d | exact2complex(factors(p)) >);
"Checking functional equation: ", CFENew(Z);
Lval:=Evaluate(Z,1);

MCC:=MatrixAlgebra(CC,6);
S:=SE_Curve(Polynomial([CC!coeff : coeff in Coefficients(f)]),3:Prec:=30);
BPM:=KMatrixSpace(CC,3,6)!S`BigPeriodMatrix;
SM:= MCC!SymplecticBasis(S`IntersectionMatrix);

//period matrix computed by Molin--Neurohr after undoing change to Symplectic basis 
BMat:=BPM*SM^(-1);
BMat2:=MCC![[BMat[1][ii] : ii in [1..6]],[ComplexConjugate(BMat[1][ii]) : ii in [1..6]],[BMat[2][ii] : ii in [1..6]],
[ComplexConjugate(BMat[2][ii]) : ii in [1..6]],[BMat[3][ii] : ii in [1..6]],[ComplexConjugate(BMat[3][ii]) : ii in [1..6]]];

rows:=MCC![1,0,0,0,0,0, 0,0,0,1,0,0, 0,0,0,0,0,1, 0,0,0,0,0,0, 0,0,0,0,0,0, 0,0,0,0,0,0];
penulti_mat:=rows*BMat2;
final_mat:=KMatrixSpace(CC,3,3)![[penulti_mat[ii][jj] : jj in [1,3,5]] : ii in [1..3]];

per:=Determinant(final_mat);

C12:=ComplexField(12);
//L-value over period:
C12!Lval/per;
// (zeta_3-1)/81:
C12!(z-1)/81;
