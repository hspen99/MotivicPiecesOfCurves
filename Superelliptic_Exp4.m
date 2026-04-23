// Attach relevant code from Molin--Neurohr package
AttachSpec("PATH/TO/spec");
load "PATH/TO/se_periods/se_symplectic_basis.m";

N:=15000; // compute for primes <= N, may need to be increased for larger conductors
primes:=[p : p in [1..N] | IsPrime(p)];

_<b>:=PolynomialRing(Rationals());
K<z>:=CyclotomicField(4);
R<t>:=PolynomialRing(K);
A<x,y>:=AffineSpace(K,2);

// declare the curve here via quartic polynomial in t
f:=t^3+z*t^2-(1-z)*t;
//also input conductor, assuming it's known
cond:=2^17*5;

C:=Curve(A, y^4 - Evaluate(f,x));
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

// The curve C has an automorphism alpha of order 4 (that sends y to z y) and we compute the fixed points of the composition of this automorphism with Frobenius. The fixed points correspond to points on the `twisted' curve u*y^3 = f(x).
// poly_finder returns the (truncated) local polynomial at one of the isotypic pieces of the Tate module of the curve.

function poly_finder(F,zeta,pow);	
	// Sanity checks
	assert zeta in F;
	assert zeta^2 eq -One(F);	
	// Recover the characteristic and the size of the field
	p := Characteristic(F);
	q := #F;

	// start your engines...
	printf "Computing p=%o, q=%o, ... ", p, q;
	cput := Cputime();

	// Create the curve
	AA<xx,yy>:=AffineSpace(F,2);
	// reconstruct y^4 = f over F
	F_coeffs:=[coeff[1]+zeta*coeff[2] : coeff in poly_coeffs];
	f_F:=Evaluate(Polynomial(F_coeffs),xx);
	CF:=ProjectiveClosure(Curve(AA, yy^4 - f_F));

	// obtain traces for later
	C_traces:=[(1+#F^ii - #Points(BaseChange(CF,ext<F|ii>))) : ii in [1..pow]];

	// aa will hold the trace of successive powers of alpha*Frob
	aa:=[];
	
	for jj in [1..3] do
		// Build the auxiliary curve over F
		// Compute u such that u*yy^4 = f_F is the eqn of a curve on which Frobenius acts as zeta*Frob does on C
		GG,m:=MultiplicativeGroup(F);
		u:=m(GG.1);
		u0:=u;
		while not u0^Integers()!((#F-1)/4) eq zeta^(-jj) do
			u0*:=u;
		end while;
		
		// Twisted curve
		CC:=ProjectiveClosure(Curve(AA,u0*yy^4-f_F));
		
		// Count the points
		aa cat:=[1+#F - #Points(CC)];
	end for;

	if pow eq 2 then
		for jj in [1..3] do
			FF:=ext<F|2>;
			// Build the auxiliary curve over FF
			// Compute u such that u*yy^4 = f_FF is the eqn of a curve on which Frobenius acts as zeta*Frob does on C
			GG,m:=MultiplicativeGroup(FF);
			u:=m(GG.1);
			u0:=u;
			while not u0^Integers()!((#FF-1)/4) eq zeta^(-jj) do
				u0*:=u;
			end while;
		
			// Twisted curve
			AA<xx,yy>:=AffineSpace(FF,2);
			CC:=ProjectiveClosure(Curve(AA,u0*yy^4-Evaluate(f_F,[xx,0])));
		
			// Count the points
			aa cat:=[1+#FF - #Points(CC)];
		end for;
	end if;

	traces:=[ 1/4*(C_traces[1] + z*aa[1] - aa[2] - z*aa[3])];
	
	if pow eq 2 then
		traces cat:=[ 1/4*(C_traces[2] + z*aa[4] - aa[5] - z*aa[6])];
	end if;

	poly:=1-traces[1]*t;
	if pow eq 2 then
		poly +:=t^2*Newton_ids([traces[jj] : jj in [1..2]]);
	end if;

	printf "done (%os)\n", Cputime(cput);
	return Evaluate(poly,t^Round(Log(p,q)));
end function;

// Now actually compute (truncated) Euler factors away from 2 (where we assume Euler factor is 1)

for ii in [ii : ii in [1..#primes] | not primes[ii] eq 2 ] do
	p:=primes[ii];
	pp_s := Factorisation(ideal<RingOfIntegers(K)|p>);
	
	euler_factors[p]:=R!1;
	
	pp:=pp_s[1][1];
	if Norm(pp) eq p then
		F:=GF(p);
		pow:=Floor(Log(p,N));
		if pow gt 2 then pow:=2; end if;
		_<x>:=PolynomialRing(F);
		for zeta in Roots(x^2+1) do 
		// each choice of zeta corresponds to one of the (conjugate) primes above p
			euler_factors[p]*:=poly_finder(F,zeta[1],pow);			
		end for;
	end if;

    if Norm(pp) eq p^2 then
		F:=GF(p^2);
		_<x>:=PolynomialRing(F);
    	// choice of zeta doesn't matter in this case
		zeta:=Roots(x^2+1)[1][1];
		pow:=Floor(Log(p^2,N));
		if pow eq 0 then continue; end if;
		if pow gt 2 then pow:=2; end if;
		euler_factors[p]*:=poly_finder(F,zeta,pow);				
    end if;
end for;

// set up complexes for the L-functions
CC<I_CC>:=ComplexField();
S<X>:=PolynomialRing(CC);

exact2complex := function(poly); // convert exact polynomial to one with complex coefficients for the L-series
	comp_poly:=S!0;
	coeffs:=Coefficients(poly);                                                                                                
	for ii in [1..#coeffs] do
		for jj in [1..#Eltseq(coeffs[ii])] do
			comp_poly +:= CC!(Eltseq(coeffs[ii])[jj])*I_CC^(jj-1)*X^(ii-1);
		end for;
	end for;
	return comp_poly;
end function;

euler_factors[2]:=R!1; // as assumed

factors:=function(p); // in case LSeries tries to take Euler factors at primes too large for our comp
	try
		return euler_factors[p];
	catch e
		return R!1;
	end try;
end function;

// define L-function and set coeffs:
Z := LSeries(2, [0,0,1,1], cond, 0 : Precision:=15);
LSetCoefficients(Z, func<p,d | exact2complex(factors(p)) >);

"Check functional equation: ", CFENew(Z); //should be very small!
// compute L(C^\tau,1)
L_val:=Evaluate(Z,1);

MCC:=MatrixAlgebra(CC,6);
S:=SE_Curve(Polynomial([CC!coeff : coeff in Coefficients(f)]),4:Prec:=30);
BPM:=KMatrixSpace(CC,3,6)!S`BigPeriodMatrix;
SM:= MCC!SymplecticBasis(S`IntersectionMatrix);

//period matrix computed by Molin--Neurohr after undoing change to Symplectic basis 
BMat:=BPM*Transpose(SM)^(-1);

BMat2:=MCC![[BMat[1][ii] : ii in [1..6]],[ComplexConjugate(BMat[1][ii]) : ii in [1..6]],[BMat[2][ii] : ii in [1..6]],
[ComplexConjugate(BMat[2][ii]) : ii in [1..6]],[BMat[3][ii] : ii in [1..6]],[ComplexConjugate(BMat[3][ii]) : ii in [1..6]]];
rows:=MCC![0,0,1,0,0,0, 0,0,0,0,1,0, 0,0,0,0,0,0, 0,0,0,0,0,0, 0,0,0,0,0,0, 0,0,0,0,0,0];
penulti_mat:=rows*BMat2;

// this is the matrix as in (5.7)
final_mat:=KMatrixSpace(CC,2,2)![[penulti_mat[ii][jj] : jj in {1,4}] : ii in [1..2]];
per:=Determinant(final_mat);

// Now spit out something that should visibly be in Q(i)!
C15<I_>:=ComplexField(15);           
"L-value divided by period: ", C15!L_val/per; 

