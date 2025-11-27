N:=10000; // compute for primes <= N
primes:=[p : p in [1..N] | IsPrime(p)];

K<rt5>:=QuadraticField(5);
S<t>:=PolynomialRing(K);

R<x,b>:=PolynomialRing(Rationals(),2);
A:=AffineSpace(R);

// LMFDB curve 529.a.529.1
a:=2;
f:=x^5 + b*x^4 + a*x^3 + (-2*a+b^2+3*b+5)*x^2 + (a+b)*x + b+3;
C:=Curve(A, f);

// initialise Euler factors
euler_factors:=AssociativeArray(Integers());

// bad primes and primes dividing 10
euler_factors_Q[2] := 2*t^2 + (1+rt5)/2*t +1;
euler_factors_Q[5] := 5*t^2 + (rt5 + 1)*t + 1;
euler_factors_Q[23]:=1-t;

function MF_trace_1mod5(p);
	// basic set-up
	k:=GF(p);
    q:=#k;
    a_mod:=k!a;
	_<tt>:=PolynomialRing(k);
    RR<xx,bb>:=PolynomialRing(k,2);
    AA:=AffineSpace(RR);
             
	// reduced equation for f, get C over finite field and compute Euler factor
    f_mod := xx^5 + bb*xx^4 + a_mod*xx^3 + (-2*a_mod+bb^2+3*bb+5)*xx^2 + (a_mod+bb)*xx + bb+3;
	C_mod:=ProjectiveClosure(Curve(AA,f_mod));

	// also get D, needed later
    D_mod:=ProjectiveClosure(Curve(AA,xx^2+(4*a_mod^3 - a_mod^2*bb^2 + 36*a_mod^2*bb + 80*a_mod^2 - 26*a_mod*bb^3 - 122*a_mod*bb^2 - 270*a_mod*bb - 300*a_mod + 4*bb^5 + 31*bb^4 + 118*bb^3 + 245*bb^2 + 350*bb + 375)));

	// corrections to point count
	RR<T_power> := PowerSeriesRing(Rationals(), 20);
	ZetaCorrection_C:=ZetaFunctionOfCurveModel(C_mod: Zfn:=FieldOfFractions(S)!1);
	ZetaCorrection_D:=ZetaFunctionOfCurveModel(D_mod: Zfn:=FieldOfFractions(S)!1);

    zeta:=Roots(tt^4+tt^3+tt^2+tt+1)[1][1];
		
	A2<d,tt>:=AffineSpace(k,2);
	A3<x,bb,G>:=AffineSpace(k,3);
		
	// equations for defining genus 6 curves
	D_poly:=d^2+(4*a_mod^3 - a_mod^2*tt^2 + 36*a_mod^2*tt + 80*a_mod^2 - 26*a_mod*tt^3 - 122*a_mod*tt^2 - 270*a_mod*tt - 300*a_mod + 4*tt^5 + 31*tt^4 + 118*tt^3 + 245*tt^2 + 350*tt + 375);
		
	Kummer_generator:=1/2*(-25*zeta^3 - 25*zeta^2)*a_mod^2*bb + (-75*zeta^3 - 75*zeta^2 + 25)*a_mod^2 + 1/2*(5*zeta^3 + 5*zeta^2 - 10)*a_mod*bb^3 + 1/2*(25*zeta^3 + 25*zeta^2 - 
    225)*a_mod*bb^2 + 1/2*(-150*zeta^3 - 150*zeta^2 - 825)*a_mod*bb + 1/2*(5*zeta^3 + 15*zeta^2 + 20*zeta + 10)*a_mod*G + 1/2*(-125*zeta^3 - 125*zeta^2 - 
    1000)*a_mod + bb^5 + 1/2*(15*zeta^3 + 15*zeta^2 + 70)*bb^4 + 1/2*(125*zeta^3 + 125*zeta^2 + 425)*bb^3 + 1/2*(5*zeta^3 - 5*zeta^2)*bb^2*G + 
    (200*zeta^3 + 200*zeta^2 + 600)*bb^2 + 1/2*(40*zeta^3 - 30*zeta^2 + 10*zeta + 5)*bb*G + 1/2*(875*zeta^3 + 875*zeta^2 + 2000)*bb + 
    1/2*(75*zeta^3 - 25*zeta^2 + 50*zeta + 25)*G + 1/2*(625*zeta^3 + 625*zeta^2 + 1875);

	_<y0>:=PolynomialRing(k);
	power:=Integers()!((#k-1)/5);

	traces:=[];
	
	// for each jj we are computing trace of Frob composed with zeta^jj on top curve
	for jj in [1..2] do
		// appropriate twist
		GG,m:=MultiplicativeGroup(k);
		u:=m(GG.1);
		while not u^Integers()!((#k-1)/5) eq zeta^(-jj) do
			u:=u^2;
		end while;

		// equation of the twisted curve
		X:=Curve(A3,[u*x^5-Kummer_generator,Evaluate(D_poly,[G,bb])]);
		
		// get plane model for quicker point counting
		I := Ideal(X);
		E := EliminationIdeal(I, {x, bb});

		gens := GroebnerBasis(E);

		A<xx,b_>:=AffineSpace(k,2);
		X2:=Curve(A,Evaluate(gens[1],[xx,b_,0]));
		
		// Correction factor in the zeta function due to singularities & points @ infinity
		RR<T_power> := PowerSeriesRing(Rationals(), 20);
		ZetaCorrection:=ZetaFunctionOfCurveModel(ProjectiveClosure(X2) : Zfn:=FieldOfFractions(S)!1);
		count := #Points(X2)-Coefficient(Derivative(Log(RR!ZetaCorrection)),0);
		traces cat:=[1+#k-count];
	end for;
	
	// trace of Frobenius on whole Jacobian 
	Xtrace := 3*(1+#k)-2*(#Points(C_mod)-Coefficient(Derivative(Log(RR!ZetaCorrection_C)),0))-(#Points(D_mod)-Coefficient(Derivative(Log(RR!ZetaCorrection_D)),0));
	
    // trace on rho-piece: need to choose conjugates here properly!!
    trace:=1/10*(2*Xtrace + (-1-rt5)*traces[1] +  (-1+rt5)*traces[2]);
	return trace;
end function;

function MF_trace_4mod5(p);
	// basic set-up
	k:=GF(p);
    q:=#k;
    a_mod:=k!a;
	_<tt>:=PolynomialRing(k);
    root5:=Roots(tt^2-5)[1][1];
    RR<xx,bb>:=PolynomialRing(k,2);
    AA:=AffineSpace(RR);
             
	// reduced equation for f, get C over finite field and compute Euler factor
    f_mod := xx^5 + bb*xx^4 + a_mod*xx^3 + (-2*a_mod+bb^2+3*bb+5)*xx^2 + (a_mod+bb)*xx + bb+3;
	C_mod:=ProjectiveClosure(Curve(AA,f_mod));

	// also get D, needed later
    D_mod:=ProjectiveClosure(Curve(AA,xx^2+(4*a_mod^3 - a_mod^2*bb^2 + 36*a_mod^2*bb + 80*a_mod^2 - 26*a_mod*bb^3 - 122*a_mod*bb^2 - 270*a_mod*bb - 300*a_mod + 4*bb^5 + 31*bb^4 + 118*bb^3 + 245*bb^2 + 350*bb + 375)));

	// corrections to point count
	RR<T_power> := PowerSeriesRing(Rationals(), 20);
	ZetaCorrection_C:=ZetaFunctionOfCurveModel(C_mod: Zfn:=FieldOfFractions(S)!1);
	ZetaCorrection_D:=ZetaFunctionOfCurveModel(D_mod: Zfn:=FieldOfFractions(S)!1);

	FF<zeta>:=ext<k|tt^2+(1-root5)/2*tt+1>;

	power:=Integers()!((#FF-1)/5);
	traces:=[];

	// for each jj we are computing trace of Frob composed with zeta^jj on top curve
	for jj in [1..2] do

		A2<d,tt>:=AffineSpace(FF,2);
		R3<x,bb,G>:=PolynomialRing(FF,3);
		A3:=AffineSpace(R3);
		
		// equations for defining genus 6 curves
		D_poly:=d^2+(4*a_mod^3 - a_mod^2*tt^2 + 36*a_mod^2*tt + 80*a_mod^2 - 26*a_mod*tt^3 - 122*a_mod*tt^2 - 270*a_mod*tt - 300*a_mod + 4*tt^5 + 31*tt^4 + 118*tt^3 + 245*tt^2 + 350*tt + 375);
		
		Kummer_generator:=1/2*(-25*zeta^3 - 25*zeta^2)*a_mod^2*bb + (-75*zeta^3 - 75*zeta^2 + 25)*a_mod^2 + 1/2*(5*zeta^3 + 5*zeta^2 - 10)*a_mod*bb^3 + 1/2*(25*zeta^3 + 25*zeta^2 - 
    225)*a_mod*bb^2 + 1/2*(-150*zeta^3 - 150*zeta^2 - 825)*a_mod*bb + 1/2*(5*zeta^3 + 15*zeta^2 + 20*zeta + 10)*a_mod*G + 1/2*(-125*zeta^3 - 125*zeta^2 - 
    1000)*a_mod + bb^5 + 1/2*(15*zeta^3 + 15*zeta^2 + 70)*bb^4 + 1/2*(125*zeta^3 + 125*zeta^2 + 425)*bb^3 + 1/2*(5*zeta^3 - 5*zeta^2)*bb^2*G + 
    (200*zeta^3 + 200*zeta^2 + 600)*bb^2 + 1/2*(40*zeta^3 - 30*zeta^2 + 10*zeta + 5)*bb*G + 1/2*(875*zeta^3 + 875*zeta^2 + 2000)*bb + 
    1/2*(75*zeta^3 - 25*zeta^2 + 50*zeta + 25)*G + 1/2*(625*zeta^3 + 625*zeta^2 + 1875);

		//to do: simplify this expression:
		R2:=-25/2*zeta^12*a_mod^2*bb - 75*zeta^12*a_mod^2 + 5/2*zeta^12*a_mod*bb^3 + 25/2*zeta^12*a_mod*bb^2 - 75*zeta^12*a_mod*bb + 5/2*zeta^12*a_mod*G 
    - 125/2*zeta^12*a_mod + 15/2*zeta^12*bb^4 + 125/2*zeta^12*bb^3 + 5/2*zeta^12*bb^2*G + 200*zeta^12*bb^2 + 20*zeta^12*bb*G + 
    875/2*zeta^12*bb + 75/2*zeta^12*G + 625/2*zeta^12 - 25/2*zeta^8*a_mod^2*bb - 75*zeta^8*a_mod^2 + 5/2*zeta^8*a_mod*bb^3 + 
    25/2*zeta^8*a_mod*bb^2 - 75*zeta^8*a_mod*bb + 15/2*zeta^8*a_mod*G - 125/2*zeta^8*a_mod + 15/2*zeta^8*bb^4 + 125/2*zeta^8*bb^3 - 
    5/2*zeta^8*bb^2*G + 200*zeta^8*bb^2 - 15*zeta^8*bb*G + 875/2*zeta^8*bb - 25/2*zeta^8*G + 625/2*zeta^8 + 10*zeta^4*a_mod*G + 5*zeta^4*bb*G
    + 25*zeta^4*G + 25*a_mod^2 - 5*a_mod*bb^3 - 225/2*a_mod*bb^2 - 825/2*a_mod*bb + 5*a_mod*G - 500*a_mod + bb^5 + 35*bb^4 + 425/2*bb^3 + 
    600*bb^2 + 5/2*bb*G + 1000*bb + 25/2*G + 1875/2;

		// appropriate twist
		GG,m:=MultiplicativeGroup(FF);
		u:=m(GG.1);
		while not u^power eq zeta^(-jj) do
			u:=u^2;
		end while;

		elts_u:=Eltseq(u);
		u2:=elts_u[1]+elts_u[2]*zeta^-1;

		// equation of the twisted curve over FF; we extract equation over F
		X:=Curve(A3,[u*x^5-Kummer_generator,Evaluate(D_poly,[G,bb])]);
		KX:=FunctionField(X);

		_<TX>:=PolynomialRing(KX);
		roots2:=[root[1] : root in Roots(TX^5-KX!Evaluate(R2/u2,[0,bb,G]))];

		DD:=Curve(A2,[D_poly]);
		KD:=FunctionField(DD);

		V:=VectorSpace(KD,5);

		for root in roots2 do
    		powers:= [V![1,0,0,0,0]];
    		root_trace:=KX!x+root;

    		for ii in [1..5] do
				pow:=KX!(root_trace^(ii));
        		powers cat:= [V!([ KD!Evaluate(Coefficients(Numerator(pow),x)[ll],[0,tt,d])/KD!Evaluate(Denominator(pow),[0,tt,d]) : ll in [1..Degree(Numerator(pow),x)+1] ]cat[ KD!0 : ll in [1..4-Degree(Numerator(pow),x)]])];
    		end for;

    		VV:=VectorSpaceWithBasis([powers[ii]: ii in [1..5]]);
    		coeffs:=Coordinates(VV,VV!powers[6]);

    		check:=true;
    		for coeff in coeffs do
        		coeffs_2:=Coefficients(Numerator(coeff));
				assert Denominator(coeff) eq 1;
        		for coeff_2 in coeffs_2 do
            		if not coeff_2 in k then
                		check:=false;
            		end if;
        		end for;
    		end for;

    		if check then 
        		RD<x>:=PolynomialRing(KD);
        		min_poly:=x^5-&+[x^ii*coeffs[ii+1] : ii in [0..4] ];
        		break;
    		end if;
		end for;

		// Define new polynomial ring over k with same number of variables and names
		RD<xx,dd,ttt> := PolynomialRing(k, 3);
		AR:=AffineSpace(RD);

        coeffs:=Coefficients(min_poly);

		F_poly:=RD!0;
		for ll in [1..#coeffs] do
			coeffs2,mons:=CoefficientsAndMonomials(coeffs[ll]);
			coeff_over_F:=RD!0;
			for mm in [1..#coeffs2] do
				coeff2:=coeffs2[mm];
				coeffs3:=Coefficients(Numerator(coeff2));
				coeff_over_F +:= &+[ k!coeffs3[jj]*ttt^(jj-1) : jj in [1..#coeffs3] ]*dd^(Integers()!(Degree(mons[mm])/5));
			end for;
			F_poly +:=coeff_over_F*xx^(ll-1);
		end for;

		D_poly:=dd^2+(4*a_mod^3 - a_mod^2*ttt^2 + 36*a_mod^2*ttt + 80*a_mod^2 - 26*a_mod*ttt^3 - 122*a_mod*ttt^2 - 270*a_mod*ttt - 300*a_mod + 4*ttt^5 + 31*ttt^4 + 118*ttt^3 + 245*ttt^2 + 350*ttt + 375);
		Xk:=Curve(AR,[D_poly,F_poly]);

		// get plane model for quicker point counting
		I := Ideal(Xk);
		E := EliminationIdeal(I, {xx, ttt});

		gens := GroebnerBasis(E);

		A<x_,b_>:=AffineSpace(k,2);
		X2:=Curve(A,Evaluate(gens[1],[x_,0,b_]));

		RR<T_power> := PowerSeriesRing(Rationals(), 20);
		ZetaCorrection:=ZetaFunctionOfCurveModel(ProjectiveClosure(X2) : Zfn:=FieldOfFractions(S)!1);
		count := #Points(ProjectiveClosure(X2))-Coefficient(Derivative(Log(RR!ZetaCorrection)),0);

		traces cat:=[1+#k-count];
	end for;
	
	// trace of Frobenius on whole Jacobian 
	Xtrace := 3*(1+#k)-2*(#Points(C_mod)-Coefficient(Derivative(Log(RR!ZetaCorrection_C)),0))-(#Points(D_mod)-Coefficient(Derivative(Log(RR!ZetaCorrection_D)),0));
    
	// trace on rho-piece: need to choose conjugates here properly!!
    trace:=1/10*(2*Xtrace + (-1+rt5)*traces[1] +  (-1-rt5)*traces[2]); //this conjugate because we need (g*Frob)^2 for FF
	return trace;
end function;

function MF_trace_else(p);
    // basic set-up
	k:=GF(p);
    q:=#k;
    a_mod:=k!a;
	_<tt>:=PolynomialRing(k);
    RR<xx,bb>:=PolynomialRing(k,2);
    AA:=AffineSpace(RR);
             
	// reduced equation for f, get C over finite field and compute Euler factor
    f_mod := xx^5 + bb*xx^4 + a_mod*xx^3 + (-2*a_mod+bb^2+3*bb+5)*xx^2 + (a_mod+bb)*xx + bb+3;
	C_mod:=ProjectiveClosure(Curve(AA,f_mod));

	// also get D, needed later
    D_mod:=ProjectiveClosure(Curve(AA,xx^2+(4*a_mod^3 - a_mod^2*bb^2 + 36*a_mod^2*bb + 80*a_mod^2 - 26*a_mod*bb^3 - 122*a_mod*bb^2 - 270*a_mod*bb - 300*a_mod + 4*bb^5 + 31*bb^4 + 118*bb^3 + 245*bb^2 + 350*bb + 375)));

	// corrections to point count
	RR<T_power> := PowerSeriesRing(Rationals(), 20);
	ZetaCorrection_C:=ZetaFunctionOfCurveModel(C_mod: Zfn:=FieldOfFractions(S)!1);
	ZetaCorrection_D:=ZetaFunctionOfCurveModel(D_mod: Zfn:=FieldOfFractions(S)!1);

	FF<zeta>:=ext<k|tt^4+tt^3+tt^2+tt+1>;

	power:=Integers()!((#FF-1)/5);
	traces:=[];

	// for each jj we are computing trace of Frob composed with zeta^jj on top curve
	for jj in [1..2] do

		A2<d,tt>:=AffineSpace(FF,2);
		R3<x,bb,G>:=PolynomialRing(FF,3);
		A3:=AffineSpace(R3);
		
		// equations for defining genus 6 curves
		D_poly:=d^2+(4*a_mod^3 - a_mod^2*tt^2 + 36*a_mod^2*tt + 80*a_mod^2 - 26*a_mod*tt^3 - 122*a_mod*tt^2 - 270*a_mod*tt - 300*a_mod + 4*tt^5 + 31*tt^4 + 118*tt^3 + 245*tt^2 + 350*tt + 375);
		
		Kummer_generator:=1/2*(-25*zeta^3 - 25*zeta^2)*a_mod^2*bb + (-75*zeta^3 - 75*zeta^2 + 25)*a_mod^2 + 1/2*(5*zeta^3 + 5*zeta^2 - 10)*a_mod*bb^3 + 1/2*(25*zeta^3 + 25*zeta^2 - 
    225)*a_mod*bb^2 + 1/2*(-150*zeta^3 - 150*zeta^2 - 825)*a_mod*bb + 1/2*(5*zeta^3 + 15*zeta^2 + 20*zeta + 10)*a_mod*G + 1/2*(-125*zeta^3 - 125*zeta^2 - 
    1000)*a_mod + bb^5 + 1/2*(15*zeta^3 + 15*zeta^2 + 70)*bb^4 + 1/2*(125*zeta^3 + 125*zeta^2 + 425)*bb^3 + 1/2*(5*zeta^3 - 5*zeta^2)*bb^2*G + 
    (200*zeta^3 + 200*zeta^2 + 600)*bb^2 + 1/2*(40*zeta^3 - 30*zeta^2 + 10*zeta + 5)*bb*G + 1/2*(875*zeta^3 + 875*zeta^2 + 2000)*bb + 
    1/2*(75*zeta^3 - 25*zeta^2 + 50*zeta + 25)*G + 1/2*(625*zeta^3 + 625*zeta^2 + 1875);

		//to do: simplify these expressions:
        R2:=-25/2*zeta^6*a_mod^2*bb - 75*zeta^6*a_mod^2 + 5/2*zeta^6*a_mod*bb^3 + 25/2*zeta^6*a_mod*bb^2 - 75*zeta^6*a_mod*bb + 5/2*zeta^6*a_mod*G - 
    125/2*zeta^6*a_mod + 15/2*zeta^6*bb^4 + 125/2*zeta^6*bb^3 + 5/2*zeta^6*bb^2*G + 200*zeta^6*bb^2 + 20*zeta^6*bb*G + 875/2*zeta^6*bb + 
    75/2*zeta^6*G + 625/2*zeta^6 - 25/2*zeta^4*a_mod^2*bb - 75*zeta^4*a_mod^2 + 5/2*zeta^4*a_mod*bb^3 + 25/2*zeta^4*a_mod*bb^2 - 
    75*zeta^4*a_mod*bb + 15/2*zeta^4*a_mod*G - 125/2*zeta^4*a_mod + 15/2*zeta^4*bb^4 + 125/2*zeta^4*bb^3 - 5/2*zeta^4*bb^2*G + 
    200*zeta^4*bb^2 - 15*zeta^4*bb*G + 875/2*zeta^4*bb - 25/2*zeta^4*G + 625/2*zeta^4 + 10*zeta^2*a_mod*G + 5*zeta^2*bb*G + 25*zeta^2*G + 
    25*a_mod^2 - 5*a_mod*bb^3 - 225/2*a_mod*bb^2 - 825/2*a_mod*bb + 5*a_mod*G - 500*a_mod + bb^5 + 35*bb^4 + 425/2*bb^3 + 600*bb^2 + 5/2*bb*G
    + 1000*bb + 25/2*G + 1875/2;

        R3:=-25/2*zeta^9*a_mod^2*bb - 75*zeta^9*a_mod^2 + 5/2*zeta^9*a_mod*bb^3 + 25/2*zeta^9*a_mod*bb^2 - 75*zeta^9*a_mod*bb + 5/2*zeta^9*a_mod*G - 
    125/2*zeta^9*a_mod + 15/2*zeta^9*bb^4 + 125/2*zeta^9*bb^3 + 5/2*zeta^9*bb^2*G + 200*zeta^9*bb^2 + 20*zeta^9*bb*G + 875/2*zeta^9*bb + 
    75/2*zeta^9*G + 625/2*zeta^9 - 25/2*zeta^6*a_mod^2*bb - 75*zeta^6*a_mod^2 + 5/2*zeta^6*a_mod*bb^3 + 25/2*zeta^6*a_mod*bb^2 - 
    75*zeta^6*a_mod*bb + 15/2*zeta^6*a_mod*G - 125/2*zeta^6*a_mod + 15/2*zeta^6*bb^4 + 125/2*zeta^6*bb^3 - 5/2*zeta^6*bb^2*G + 
    200*zeta^6*bb^2 - 15*zeta^6*bb*G + 875/2*zeta^6*bb - 25/2*zeta^6*G + 625/2*zeta^6 + 10*zeta^3*a_mod*G + 5*zeta^3*bb*G + 25*zeta^3*G + 
    25*a_mod^2 - 5*a_mod*bb^3 - 225/2*a_mod*bb^2 - 825/2*a_mod*bb + 5*a_mod*G - 500*a_mod + bb^5 + 35*bb^4 + 425/2*bb^3 + 600*bb^2 + 5/2*bb*G
    + 1000*bb + 25/2*G + 1875/2;

        R4:=-25/2*zeta^12*a_mod^2*bb - 75*zeta^12*a_mod^2 + 5/2*zeta^12*a_mod*bb^3 + 25/2*zeta^12*a_mod*bb^2 - 75*zeta^12*a_mod*bb + 5/2*zeta^12*a_mod*G 
    - 125/2*zeta^12*a_mod + 15/2*zeta^12*bb^4 + 125/2*zeta^12*bb^3 + 5/2*zeta^12*bb^2*G + 200*zeta^12*bb^2 + 20*zeta^12*bb*G + 
    875/2*zeta^12*bb + 75/2*zeta^12*G + 625/2*zeta^12 - 25/2*zeta^8*a_mod^2*bb - 75*zeta^8*a_mod^2 + 5/2*zeta^8*a_mod*bb^3 + 
    25/2*zeta^8*a_mod*bb^2 - 75*zeta^8*a_mod*bb + 15/2*zeta^8*a_mod*G - 125/2*zeta^8*a_mod + 15/2*zeta^8*bb^4 + 125/2*zeta^8*bb^3 - 
    5/2*zeta^8*bb^2*G + 200*zeta^8*bb^2 - 15*zeta^8*bb*G + 875/2*zeta^8*bb - 25/2*zeta^8*G + 625/2*zeta^8 + 10*zeta^4*a_mod*G + 5*zeta^4*bb*G
    + 25*zeta^4*G + 25*a_mod^2 - 5*a_mod*bb^3 - 225/2*a_mod*bb^2 - 825/2*a_mod*bb + 5*a_mod*G - 500*a_mod + bb^5 + 35*bb^4 + 425/2*bb^3 + 
    600*bb^2 + 5/2*bb*G + 1000*bb + 25/2*G + 1875/2;

		// appropriate twist
		GG,m:=MultiplicativeGroup(FF);
		u:=m(GG.1);
		while not u^power eq zeta^(-jj) do
			u:=u^2;
		end while;

		elts_u:=Eltseq(u);
        u2:=elts_u[1]+elts_u[2]*zeta^2+elts_u[3]*zeta^4+elts_u[4]*zeta;
        u3:=elts_u[1]+elts_u[2]*zeta^3+elts_u[3]*zeta + elts_u[4]*zeta^4;
		u4:=elts_u[1]+elts_u[2]*zeta^4+elts_u[3]*zeta^3+elts_u[4]*zeta^2;

		// equation of the twisted curve over FF; we extract equation over F
		X:=Curve(A3,[u*x^5-Kummer_generator,Evaluate(D_poly,[G,bb])]);
		KX:=FunctionField(X);

		_<TX>:=PolynomialRing(KX);
		roots2:=[root[1] : root in Roots(TX^5-KX!Evaluate(R2/u2,[0,bb,G]))];
		roots3:=[root[1] : root in Roots(TX^5-KX!Evaluate(R3/u3,[0,bb,G]))];
		roots4:=[root[1] : root in Roots(TX^5-KX!Evaluate(R4/u4,[0,bb,G]))];

		DD:=Curve(A2,[D_poly]);
		KD:=FunctionField(DD);

		V:=VectorSpace(KD,5);

		for root in CartesianProduct([roots2,roots3,roots4]) do
    		powers:= [V![1,0,0,0,0]];
    		root_trace:=KX!x+root[1]+root[2]+root[3];

    		for ii in [1..5] do
				pow:=KX!(root_trace^(ii));
        		powers cat:= [V!([ KD!Evaluate(Coefficients(Numerator(pow),x)[ll],[0,tt,d])/KD!Evaluate(Denominator(pow),[0,tt,d]) : ll in [1..Degree(Numerator(pow),x)+1] ]cat[ KD!0 : ll in [1..4-Degree(Numerator(pow),x)]])];
    		end for;

    		VV:=VectorSpaceWithBasis([powers[ii]: ii in [1..5]]);
    		coeffs:=Coordinates(VV,VV!powers[6]);

    		check:=true;
    		for coeff in coeffs do
        		coeffs_2:=Coefficients(Numerator(coeff));
				assert Denominator(coeff) eq 1;
        		for coeff_2 in coeffs_2 do
            		if not coeff_2 in k then
                		check:=false;
            		end if;
        		end for;
    		end for;

    		if check then 
        		RD<x>:=PolynomialRing(KD);
        		min_poly:=x^5-&+[x^ii*coeffs[ii+1] : ii in [0..4] ];
        		break;
    		end if;
		end for;

		// Define new polynomial ring over k with same number of variables and names
		RD<xx,dd,ttt> := PolynomialRing(k, 3);
		AR:=AffineSpace(RD);

        coeffs:=Coefficients(min_poly);

		F_poly:=RD!0;
		for ll in [1..#coeffs] do
			coeffs2,mons:=CoefficientsAndMonomials(coeffs[ll]);
			coeff_over_F:=RD!0;
			for mm in [1..#coeffs2] do
				coeff2:=coeffs2[mm];
				coeffs3:=Coefficients(Numerator(coeff2));
				coeff_over_F +:= &+[ k!coeffs3[jj]*ttt^(jj-1) : jj in [1..#coeffs3] ]*dd^(Integers()!(Degree(mons[mm])/5));
			end for;
			F_poly +:=coeff_over_F*xx^(ll-1);
		end for;

		D_poly:=dd^2+(4*a_mod^3 - a_mod^2*ttt^2 + 36*a_mod^2*ttt + 80*a_mod^2 - 26*a_mod*ttt^3 - 122*a_mod*ttt^2 - 270*a_mod*ttt - 300*a_mod + 4*ttt^5 + 31*ttt^4 + 118*ttt^3 + 245*ttt^2 + 350*ttt + 375);
		Xk:=Curve(AR,[D_poly,F_poly]);

		// get plane model for quicker point counting
		I := Ideal(Xk);
		E := EliminationIdeal(I, {xx, ttt});

		gens := GroebnerBasis(E);

		A<x_,b_>:=AffineSpace(k,2);
		X2:=Curve(A,Evaluate(gens[1],[x_,0,b_]));

		RR<T_power> := PowerSeriesRing(Rationals(), 20);
		ZetaCorrection:=ZetaFunctionOfCurveModel(ProjectiveClosure(X2) : Zfn:=FieldOfFractions(S)!1);
		count := #Points(ProjectiveClosure(X2))-Coefficient(Derivative(Log(RR!ZetaCorrection)),0);

		traces cat:=[1+#k-count];
	end for;
	
	// trace of Frobenius on whole Jacobian 
	Xtrace := 3*(1+#k)-2*(#Points(C_mod)-Coefficient(Derivative(Log(RR!ZetaCorrection_C)),0))-(#Points(D_mod)-Coefficient(Derivative(Log(RR!ZetaCorrection_D)),0));
    
	// trace on rho-piece: need to choose conjugates here properly!!
    trace:=1/10*(2*Xtrace + (-1-rt5)*traces[1] +  (-1+rt5)*traces[2]); //this conjugate because we need (g*Frob)^2 for FF	
	return trace;
end function;

function MF_trace(p);
	if p mod 5 eq 1 then
		return MF_trace_1mod5(p);
	else if p mod 5 eq 4 then
		return MF_trace_4mod5(p);
    else
        return MF_trace_else(p);
    end if; end if;
end function;

CC:=ComplexField();
Nf:=Newforms(CuspForms(23,2));
f:=ComplexEmbeddings(Nf[1][1])[1][1];
Lf:=LSeries(f); // L-series of the corresponding newform

// Go through prime-by-prime and check if traces (hence Euler factors) are the same
for p in [p : p in primes | not p in {2,5,23}] do
	printf "Checking p=%o ...", p;
	cput := Cputime();
	cmplx_trace:=-Coefficient(EulerFactor(Lf,p),1);
	exact_trace:=MF_trace(p);
	assert AbsoluteValue(cmplx_trace-(Eltseq(exact_trace)[1]+CC!rt5*Eltseq(exact_trace)[2])) lt 10^(-20);
	printf " Good. (%os)\n", Cputime(cput);
end for;

