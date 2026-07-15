// This file's code is from the repository https://github.com/oana-adascalitei/MWSieveForDatabase

PP<x> := PolynomialRing(Rationals());
ellproj := function(P:JacHypPt)
  a := []; b := [];
  p := P[1]; q := P[2];
  assert p in PP and q in PP;
  J := Parent(P);
  C := Curve(J);
  f,_ := HyperellipticPolynomials(C);
  coeffs := Coefficients(f);
  a0 := coeffs[1]; a2 := coeffs[3]; a4 := coeffs[5]; a6 := coeffs[7];
  E1 := EllipticCurve(x^3+a4*x^2+a2*a6*x+a0*a6^2);
  E2 := EllipticCurve(x^3 +a2*x^2 + a4*a0*x + a6*a0^2);
  F<x1,y> := FunctionField(C);
  CtoE1 := map<C -> E1 |[a6*x1^2,a6*y,1]>;
  CtoE2 := map<C -> E2 | [a0/x1^2,a0*y/x1^3,1]>;
  //difference of the two points at infinity
  if p eq 1 and Degree(q) eq 3 and IsSquare(a6) then
    sq := Integers()!SquareRoot(a6);
    if P eq J![C![1,sq,0],C![1,-sq,0]] then
      P1 := C![1,sq,0]; P2 := C![1,-sq,0];
    else P1 := C![1,-sq,0]; P2 := C![1,sq,0];
    end if;
  assert J![P1,P2] eq P;
  a := CtoE1(P1)-CtoE1(P2);
  b := CtoE2(P1)-CtoE2(P2);
  end if;
  //the first polynomial is the square of a linear polynomial
  if Degree(p) eq 2 and IsSquare(p) then
    r := Roots(p)[1][1];
    P1 := C![r,Evaluate(q,r)]; P2 := C![r,-Evaluate(q,r)];
    assert J![P1,P2] eq P;
    a := E1!(CtoE1(P1)-CtoE1(P2)); b := E2!(CtoE2(P1)-CtoE2(P2));
  end if;
  //first polynomial has degree 2, but is not a square
  if Degree(p) eq 2 and IsSquare(p) eq false then
  //we first establish the field of definition for the divisor
    if IsIrreducible(P[1]) then
      K := NumberField(P[1]);
    else K := Rationals();
    end if;
    _<z> := PolynomialRing(K); 
    C := HyperellipticCurve(f);
    J := Jacobian(C);
    E1 := EllipticCurve([0,a4,0,a2*a6,a0*a6^2]);
    E2 := EllipticCurve([0,a2,0,a4*a0,a6*a0^2]);
    CK := ChangeRing(C,K);
    F<x1,y> := FunctionField(CK);
    JK := Jacobian(CK);
    CtoE1 := map<CK -> E1 |[a6*x1^2,a6*y,1]>;
    CtoE2 := map<CK -> E2 | [a0/x1^2,a0*y/x1^3,1]>;
    r1 := Roots(p,K)[1][1]; r2 := Roots(p,K)[2][1];
    P1 := CK![r1,Evaluate(q,r1)];
    P2 := CK![r2,-Evaluate(q,r2)];
    assert J!(JK![P1,P2]) eq P;
    a := E1!(CtoE1(P1)-CtoE1(P2)); b := E2!(CtoE2(P1)-CtoE2(P2));
  end if;
  //first polynomial is linear, we use its root and attempt to subtract a point at infinity
  if Degree(P[1]) eq 1 and #PointsAtInfinity(C) eq 2  then
    r1 := Roots(p)[1][1];
    P1 := C![r1,Evaluate(q,r1)];
    if J![P1,PointsAtInfinity(C)[1]] eq P then
      P2 := PointsAtInfinity(C)[1];
      a := E1!(CtoE1(P1)-CtoE1(P2)); b := E2!(CtoE2(P1)-CtoE2(P2));
    end if;
    if J![P1,PointsAtInfinity(C)[2]] eq P then
      P2 := PointsAtInfinity(C)[2];
      a := E1!(CtoE1(P1)-CtoE1(P2)); b := E2!(CtoE2(P1)-CtoE2(P2));
    end if;
  end if;
return [a,b];
end function;

//Example
// X := HyperellipticCurve(x^6 + x^4 + 6*x^2 + 1);
// J := Jacobian(X);
// P := J![x^2,1];
// ellproj(P);

///////////////////////////////////

//BiellipticModel
//input: genus 2 bielliptic curve 
//output: bielliptic model y^2 = f(x^2)

BiellipticModel := function(X:CrvHyp)
  M,_ := SimplifiedModel(X);
  p := HyperellipticPolynomials(M);
  if Evaluate(p,x) eq Evaluate(p,-x) then
    c := Coefficients(p);
    a6 := c[7]; a4 := c[5]; a2 := c[3]; a0 := c[1];
    E1 := EllipticCurve([0, a4, 0, a2*a6, a0*a6^2]);
    E2 := EllipticCurve([0, a2, 0, a0*a4, a0^2*a6]);  
  else
    R := RichelotIsogenousSurfaces(M); 
    j := 1;
    while Type(R[j]) ne SetCart do
      j :=j+1;
    end while;
    R1 := R[j][1]; R2 := R[j][2];
    a2 := aInvariants(R1)[2]; a1 := aInvariants(R2)[2]; 
    if a2 eq 0 then
      a3 := aInvariants(R1)[4]/a1;
      a0 := aInvariants(R2)[5]/aInvariants(R1)[5]*a3;
    elif a1 eq 0 then
      a0 := aInvariants(R2)[4]/a2;
      a3 := aInvariants(R2)[5]/a0^2;
    else 
      a3 := aInvariants(R1)[4]/a1;
      a0 := aInvariants(R2)[4]/a2;
    end if;
  H,_ := IntegralModel(HyperellipticCurve(a0*x^6+a1*x^4+a2*x^2+a3));
  p,_ := HyperellipticPolynomials(H);
  end if;
Y := HyperellipticCurve(p);
assert IsIsomorphic(X,Y);
return Y;
end function;

// X := HyperellipticCurve(-x^5 + x^4 + x^2 - x ,x^3 + 1);
// BiellipticModel(X);

/////////////////////////

//SimplifyPolynomial
//input: bielliptic model y^2 = f(x^2) of bielliptic genus 2 curve 
//output: bielliptic model y^2 = f(x^2) 
//where unnecessary factors and powers have been removed
//monic if possible

PP<x> := PolynomialRing(Rationals());
  SimplifyPolynomial := function(f : RngUPolElt)
  assert f in PP;
  X := HyperellipticCurve(f);
  coeffs := Coefficients(f);
  a0 := Integers()!coeffs[1]; a2 := Integers()!coeffs[3]; 
  a4 := Integers()!coeffs[5]; a6 := Integers()!coeffs[7];
  for p in PrimeDivisors(a6) do
    if  Valuation(a6,p) ge 6 and Valuation(a4,p) ge 4 and Valuation(a2,p) ge 2 then
      f := Evaluate(f,x/p);
    end if;
  end for;

  for p in PrimeDivisors(a6) do
    if  Valuation(a6,p) in [4,5] and Valuation(a4,p) ge 2 then
    f := p^2*Evaluate(f,x/p);
    end if;
  end for;

  for p in PrimeDivisors(a0) do
    if  Valuation(a0,p) ge 6 and Valuation(a2,p) ge 4 and Valuation(a4,p) ge 2 then
      f := Evaluate(f,x*p)/p^6;
    end if;
  end for;

  for p in PrimeDivisors(a0) do
    if  Valuation(a0,p) in [4,5] and Valuation(a2,p) ge 2 then
      f := f/p^4;
      f := Evaluate(f,x*p);
    end if;
  end for;

  for p in PrimeDivisors(GCD(a0,a6)) do
    if  Valuation(a0,p) ge 2 and Valuation(a2,p) ge 2 and Valuation(a4,p) ge 2 and Valuation(a6,p) ge 2 then
      f := f/p^2;
    end if;
  end for;

  coeffs := Coefficients(f);
  a0 := Integers()!coeffs[1]; a2 := Integers()!coeffs[3]; 
  a4 := Integers()!coeffs[5]; a6 := Integers()!coeffs[7];

  if (AbsoluteValue(a6) gt AbsoluteValue(a0)) or (a6 ne 1 and a0 eq 1) then
    f := Polynomial(Reverse(Coefficients(f)));
  end if;

  Y := HyperellipticCurve(f);
  assert IsIsomorphic(X,Y);

return f;
end function;

//Example
//f := 2^6*x^6+2^4*x^4+4*6*x^2+1;
//SimplifyPolynomial(f);