r"""
Code to perform Quadratic Chabauty on a genus 2, rank 2 bielliptic curve.

The main function is `quadratic_chabauty_bielliptic(f, p, n)`. 

!!NB!!: If the function returns a SageMath error, it could be because the `p`-adic precision `n` is too small.
        Try increasing it. 


Modified version of the following files:
https://github.com/bianchifrancesca/quadratic_chabauty/blob/master/quadratic_chabauty_bielliptic.sage
https://github.com/bianchifrancesca/QC_bielliptic/blob/main/qc_g2_bielliptic.sage

Some differences to previous version:

- we use a simpler function, at the expense of working with logarithmic terms in some residue discs (these cancel out).
  See Sections 2 and 3 of [BP22].

- works in higher generality: works for any bi-elliptic curve of the form `y^2 = a_6*x^6 + a_4*x^4 + a_2*x^2 + a_0`, with `a_i\in \ZZ`,
  such that the two corresponding elliptic curves each have rank 1.

- several Coleman integration computations of differentials of the first and second kind are replaced by computations
  using the formal group, and division polynomials. See for example `int_w1_b`for integrals of the second kind on elliptic curves.
  This may be of independent interest as it works in bad reduction too. We check it in bad reduction against an example in [Kay22].


EXAMPLES::
    sage: R.<x> = PolynomialRing(Rationals())
    sage: f = x^6 - 2*x^4 - 7*x^2 + 4 #LMFDB label: 322624.b.322624.1
    sage: rat_points, other_points = quadratic_chabauty_bielliptic(f,3,20)
    Number of elements in Omega = 3
    sage: rat_points
    [(-9/4 : -439/64 : 1), (-9/4 : 439/64 : 1), (0 : -2 : 1), (0 : 1 : 0), (0 : 2 : 1), (9/4 : -439/64 : 1), (9/4 : 439/64 : 1)]
    sage: other_points
    []
    Since `other_points` is an empty list, in this case the quadratic Chabauty computation suffices to determine the
    rational points on `X: y^2 = f(x)` (NB: the SageMath point (0 : 1 : 0) actually corresponds to two points at infinity).

    sage: R.<x> = PolynomialRing(Rationals())
    sage: f = -x^6 + 11*x^4 - 19*x^2 + 25 #LMFDB label: 24025.a.600625.1
    sage: rat_points, other_points = quadratic_chabauty_bielliptic(f,3,20)
    using potential good reduction at 2
    Number of elements in Omega = 6
    sage: rat_points
    [(-3 : -4 : 1), (-3 : 4 : 1), (-1 : -4 : 1), (-1 : 4 : 1), (0 : -5 : 1), (0 : 5 : 1), (1 : -4 : 1), (1 : 4 : 1), (3 : -4 : 1), (3 : 4 : 1)]
    sage: len(other_points)
    16
    In this case, `other_points` is not an empty list, so need more work to determine the rational points.

    This is an example over a quadratic imaginary field. Note that rat_points is still strictly the `\QQ`-rational points on the curve.
    sage: R.<x> = PolynomialRing(Rationals())
    sage: f = -x^6 -9*x^4 - 11*x^2 + 37
    sage: K.<a> = QuadraticField(-1)
    sage: rat_points, other_points = quadratic_chabauty_bielliptic(f,13,20, F = K)
    sage: rat_points
    [(-1 : -4 : 1), (-1 : 4 : 1), (0 : 1 : 0), (1 : -4 : 1), (1 : 4 : 1)]
    sage: len(other_points)
    28
    In this case, the recovered `\QQ(i)`-rational points are in the set other_points.

See the function description for more information and examples.

REFERENCES:
- [BBCF+19] \J.S. Balakrishnan, F. Bianchi, V. Cantoral-Farfán, M. Çiperiani, and A. Etropolski,
  "Chabauty–Coleman experiments for genus 3 hyperelliptic curves", In Research Directions in Number Theory,
  Springer, 2019.
- [BBM16] \J.S. Balakrishnan, A. Besser, and J.S. Müller, "Quadratic Chabauty:
  p-adic heights and integral points on hyperelliptic curves", J. Reine Angew. Math., 2016.
- [BD18] \J.S. Balakrishnan and N. Dogra, "Quadratic Chabauty and
  rational points I: p-adic heights", Duke Math. J, 2018.
- [Bia20] \F. Bianchi, "Quadratic Chabauty for (bi)elliptic curves
  and Kim's conjecture", ANT, 2020.
- [BP22] \F. Bianchi and O. Padurariu, "Rational points on rank 2 genus 2 
  bielliptic curves in the LMFDB", 2022.
- [Kay22] \E. Kaya, "Explicit Vologodsky integration for hyperelliptic curves",
  Math. Comp., 2022.
  
AUTHORS:
- Francesca Bianchi (main code repository)
- Jennifer Balakrishnan (small edits, indicated by JB2023)
- Kate Finnerty (small edits, indicated by KF2025)
"""
############## AUXILIARY FUNCTIONS ##############

import itertools

def embeddings(K,p,prec):
    r"""
    The embedding(s) `$K=\Q(\sqrt(D)) \into \Q_p$`.

    Added to the forked repo, JB2023.
    """
    Q = Qp(p,prec)
    OK = K.maximal_order()
    pOK = factor(p*OK)
    if (len(pOK) == 2 and pOK[0][1] == 1):
        R = Q['x']
        r1, r2 = R(K.defining_polynomial()).roots()
        psi1 = K.hom([r1[0]])
        psi2 = K.hom([r2[0]])
        return [psi1, psi2]
    else:
        F = Q.extension(K.defining_polynomial(),names='a')
        a = F.gen()
        psi = self._psis = [K.hom([a])]
        return psi


def cyc_padic_height_quad(E,K,P,p):
    r"""
    The cyclotomic `p`-adic height of `P` on the elliptic curve `E`, where `P` is defined
    over the quadratic field `K`.

    Added to the forked repo, JB2023.
    """
    psi1,psi2 = embeddings(K,p,20)
    m0 = prod(E.tamagawa_numbers())
    K = E.base_field()
    Kdeg = K.degree()
    A = m0*P
    if A == E(0,1,0):
        return 0
    if A[0] in QQ:
        A0 = QQ(A[0])
        deg = 1
    else:
        A0 = A[0]
        deg = 2
    if deg == 2:
        MP = A0.minpoly()
        if MP[0] in ZZ and MP[1] in ZZ and MP[2] in ZZ:
            minpol = MP
        else:
            minpol = (MP[0].denominator())*MP
            gminpoly = gcd([x for x in minpol.list()])
            if gminpoly == 1:
                minpol = ZZ['x'](minpol)
            else:
                minpol = ZZ['x'](minpol/gminpoly)
    else:
        minpol = algdep(A0,deg)
    bP = (minpol[deg]).prime_to_m_part(p)
    calD = bP^(Kdeg/(2*deg))
    F = Qp(p,20)
    EF = E.change_ring(QQ).change_ring(F)
    Ep = E.change_ring(QQ).change_ring(GF(p))
    sig = E.change_ring(QQ).padic_sigma(p)
    sigmavals = []
    divpolyvals = []
    if len(factor(p*K)) == 2:
        A1 = EF(psi1(A[0]), psi1(A[1]))
        A2 = EF(psi2(A[0]), psi2(A[1]))
        if A1[0].valuation() < 0:
            m1 = 1
        else:
            m1 = Ep(A1).additive_order()
        if A2[0].valuation() < 0:
            m2 = 1
        else:
            m2 = Ep(A2).additive_order()
        m = max(m1,m2)
        for Q in [A1,A2]:
            P = Q
            Q = m*Q
            val_for_sig = -Q[0]/Q[1]
            sval = sig(val_for_sig)
            if m%2 == 0:
                fn = E.change_ring(QQ).division_polynomial(m,two_torsion_multiplicity=1)
                fnval = fn(P[0],P[1])
            else:
                fn = E.change_ring(QQ).division_polynomial(m)
                fnval = fn(P[0])
            sigmavals = sigmavals + [sval.norm()]
            divpolyvals = divpolyvals + [fnval.norm()]
    ord = m*m0
    return ZZ(1)/ZZ(p*ord**2)*(log(prod(sigmavals)/prod(divpolyvals),0)-m**2*log(F(calD)))

def has_potential_good_reduction(H, p):
    r"""
    Return `True` if `H` has potential good reduction at `p` and `False` otherwise.
    INPUT:
    - ``H`` -- a hyperelliptic curve over `\QQ` of genus `2`.
    - ``p`` -- a prime.
    OUTPUT: Boolean.
    EXAMPLES:
    The modular curve `X_0(91)^+`::
        sage: R.<x> = PolynomialRing(QQ)
        sage: f = x^6 - 3*x^4 + 19*x^2 - 1 #LMFDB label: 8281.a.8281.1
        sage: H = HyperellipticCurve(f)
        sage: f.discriminant().factor()
        2^22 * 7^2 * 13^2
        sage: has_potential_good_reduction(H,2)
        True
        sage: has_potential_good_reduction(H,7)
        False
        sage: has_potential_good_reduction(H,13)
        False
    """
    pol_0, pol_1 = H.hyperelliptic_polynomials()
    R = genus2reduction(pol_1, pol_0)
    try:
        if '(I)' in R.local_data[p]:
            return True
        else:
            return False
    except KeyError:
        return True


def non_archimedean_local_height(P, v, p, prec, weighted=False, is_minimal=None):
    r"""
    Return the local `p`-adic height of `P` at the place `v`.
    This is a modified version of the built-in function `non_archimedean_local_height`:
    the symbolic logarithm (or real logarithm) is replaced by the `p`-adic logarithm.
    INPUT:
    - ``P`` -- a point on an elliptic curve over a number field `K`.
    - ``v`` -- a non-archimedean place of `K`` or `None`.
    - ``p`` -- an odd prime.
    - ``prec`` -- integer. The precision of the computation.
    - ``weighted`` -- boolean. If False (default), the height is
      normalised to be invariant under extension of `K`. If True,
      return this normalised height multiplied by the local degree.
    OUTPUT:
    A p-adic number: the `v`-adic component of the `p`-adic height of `P`
    if `v` is a place; the sum of the components away from `p` of the
    `p`-adic height of `P` if `v` is `None`.

    Added reduction type comments, KF2025
    """
    #Note the following is not checked in the original
    #sage code, but I think it is assumed in some places.
    assert P.curve().integral_model() == P.curve(), "You need to input a point wrt to an integral model."

    if v is None:
        D = P.curve().discriminant()
        K = P.curve().base_ring()
        if K is QQ:
            factorD = D.factor()
            if P[0] == 0:
                c = 1
            else:
                c = P[0].denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True, is_minimal=(e < 12))
                       for q,e in factorD if not q.divides(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True)
                       - c.valuation(q) * log(Qp(p, prec)(q))
                       for q,e in factorD if e >= 12 and q.divides(c)))
        else:
            factorD = K.factor(D)
            if P[0] == 0:
                c = K.ideal(1)
            else:
                c = K.ideal(P[0]).denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c.norm()))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True, is_minimal=(e < 12))
                       for v,e in factorD if not v.divides(c))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True)
                       - c.valuation(v) * log(Qp(p, prec)(v.norm()))
                       for v,e in factorD if e >= 12 and v.divides(c)))
            if not weighted:
                h /= K.degree()
        return h

    if is_minimal:
        E = P.curve()
        offset = ZZ.zero()
        Pmin = P
    else:
        E = P.curve().local_minimal_model(v)
        Pmin = P.curve().isomorphism_to(E)(P)
        # Silverman's normalization is not invariant under change of model,
        # but it all cancels out in the global height.
        offset = (P.curve().discriminant()/E.discriminant()).valuation(v)

    a1, a2, a3, a4, a6 = E.a_invariants()
    b2, b4, b6, b8 = E.b_invariants()
    c4 = E.c4()
    x, y = Pmin.xy()
    D = E.discriminant()
    N = D.valuation(v)
    A = (3*x**2 + 2*a2*x + a4 - a1*y).valuation(v)
    B = (2*y+a1*x+a3).valuation(v)
    C = (3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8).valuation(v)
    if A <= 0 or B <= 0: #good reduction
        r = max(0, -x.valuation(v))
    elif c4.valuation(v) == 0: #multiplicative reduction
        n = min(B, N/2)
        r = -n*(N-n)/N
    elif C >= 3*B: #additive reduction of type IV or IV*
        r = -2*B/3
    else: #additive reduction of type III, III*, or I*M 
        r = -C/4
    r -= offset/6
    if not r:
        return Qp(p,prec)(0)
    else:
        if E.base_ring() is QQ:
            Nv = Integer(v)
        else:
            Nv = v.norm()
            if not weighted:
                r = r / (v.ramification_index() * v.residue_class_degree())
        return r * log(Qp(p,prec)(Nv))


def Q_lift(CK, Q, p):
    r"""
    Compute a point lifting a given affine point over `GF(p)`.
    INPUT:
    - ``CK`` -- a hyperelliptic curve over `\QQ_p`,
      given by an equation of the form `y^2 = f(x)`,
      with good reduction at `p`.
    - ``Q`` -- a point in `CK(GF(p))`.
    - ``p`` -- the prime of the first two input items.
    OUTPUT: The point `P` on `CK` lifting `Q` and such that
    `x(P)\in \ZZ`,`0 <= x(P) <= p-1` if `y(Q) != 0`,
    and `y(P) = 0` if `y(Q) = 0`.
    """
    pol1, pol2 = CK.hyperelliptic_polynomials()
    assert pol2 == 0, "Need CK in the form y^2 = f(x)"
    xQ = Integers()(Q[0])
    yQ = Integers()(Q[1])
    if yQ == 0:
        r = pol1.roots()
        Q_lift = CK(exists(r, lambda a : (Integers()(a[0])-xQ) % p == 0)[1][0],0)
    else:
        K = CK.base_ring()
        xQ = K(xQ)
        lifts = CK.lift_x(xQ, all=True)
        for i in range(len(lifts)):
            if (Integers()(lifts[i][1])-yQ) % p == 0:
                Q_lift = lifts[i]
    return Q_lift


def f7(seq):
    r"""
    Remove duplicates from a list while preserving order (unlike list(Set()))
    Code taken from:
    https://stackoverflow.com/questions/480214/how-do-you-remove-duplicates-from-a-list-whilst-preserving-order
    """
    seen = set()
    seen_add = seen.add
    return [x for x in seq if not (x in seen or seen_add(x))]


############## Functions from [BD18] ##############

r""""
The following functions (until specified) are from the github code for [BD18]:
https://github.com/jbalakrishnan/QCI/blob/master/Ex1.sage
with some changes. The bielliptic curve there is assumed to have `a0 = 1` and `a6 = 1`;
here we allow for arbitrary `a0` and `a6`.
"""

def X_to_E1map(Xpt, E1, a6):
    if Xpt[2] == 0 or Xpt == 'inf+' or Xpt == 'inf-':
        return E1(0,1,0)
    else:
        x, y, _ = Xpt
        return E1(a6*x^2, a6*y)


def X_to_E2map(Xpt, E2, a0, a6):
    if Xpt[2] == 0:
        return E2(0, a0*a6.sqrt())
    elif Xpt == 'inf+' or Xpt == 'inf-':
        #only for curves over Q
        sqr = a6.sqrt()
        if (sqr > 0 and Xpt == 'inf+') or (sqr < 0 and Xpt == 'inf-'):
            return E2(0, sqr*a0)
        else:
             return E2(0,-sqr*a0)
    else:
        x,y,_ = Xpt
        if x != 0:
            return E2(a0*x^-2, a0*y*x^-3)
        else:
            return E2(0, 1, 0)


def param_f1(x, y, a6):
    r"""
    Return the coordinates of `f_1(z)` in terms of the local coordinate with respect
    to which `z = (x,y)`.
    """
    return a6*x^2, a6*y


def param_f2(x, y, a0):
    r"""
    Return the coordinates of `f_2(z)` in terms of the local coordinate with respect
    to which `z = (x,y)`.
    """
    return a0*x^-2, a0*y*x^-3

############## End of functions from [BD18] ##############


def local_coordinates_at_infinity_g2_even(H, prec = 20, name = 't'):
    r"""
    Return local coordinates at one of the points at infinity on
     `H`, given by `y^2 = f(x)` where `deg f` is even.
    """
    pols = H.hyperelliptic_polynomials()
    assert pols[1] == 0,  "Need H in the form y^2 = f(x)"
    pol = pols[0]
    K = LaurentSeriesRing(H.base_ring(), name, prec+2)
    t = K.gen()
    x = t**(-1)
    y = (pol(x))^(1/2)
    return x + O(t**(prec+2)), y + O(t**(prec+2))


def local_heights_at_bad_primes_new(E, Enonmin, K):
    r"""
    Compute the set of primes `q` at which `W_q` is larger than `\{0\}`
    for `Enonmin` and `W_q` for such primes (up to a translation).
    See Lemma 6.4 of [Bia20].
    INPUT:
    - ``E`` -- a minimal model for `Enonmin` over `\QQ`.
    - ``Enonmin`` -- an integral model for an elliptic curve over `\QQ`.
    - ``K`` -- a `p`-adic field, where `Enonmin` has good reduction
      at `p`.
    OUTPUT:
    A tuple consisting of:
    - A list `L` of all the primes `q\neq p` at which the local heights on
      `q`-adically integral points of `Enonmin` can be different from `0`.
    - A list of lists: the `i^th` list is `W_{L[i]} - 1/6* log|\Delta_{Enonmin}/\Delta_{E}|_q`.
    """
    assert E == E.integral_model(), "E should be given by an integral model"
    bad_primes = E.base_ring()(E.discriminant()).support()
    delta = Enonmin.discriminant()/E.discriminant()
    factors_delta = [f[0] for f in delta.factor()]
    W = []
    bad_primes_new = []
    for q in bad_primes:
        if E.tamagawa_number(q) == 1:
            continue
        bad_primes_new.append(q)
        ks = E.kodaira_symbol(q)
        if E.has_additive_reduction(q):
            if ks == KodairaSymbol(3): #III
                W.append([-1/2*(K(q)).log()])
            elif ks == KodairaSymbol(4): #IV
                W.append([-2/3*K(q).log()])
            elif ks == KodairaSymbol(-1): #I0*
                W.append([-K(q).log()])
            elif ks == KodairaSymbol(-4): #IV*
                W.append([-(4/3)*K(q).log()])
            elif ks == KodairaSymbol(-3): #III*
                W.append([-(3/2)*K(q).log()])
            else: #Im*
                if E.tamagawa_number(q) == 2:
                    W.append([-K(q).log()])
                else:
                    n = -5
                    while ks != KodairaSymbol(n):
                        n = n-1
                    m = -n-4
                    W.append([-K(q).log(), -(m+4)/4*K(q).log()])
        else: #multiplicative
            n = 5
            while ks != KodairaSymbol(n):
                n = n+1
            m = n-4
            if E.tamagawa_number(q) == 2:
                W.append([-m/4*K(q).log()])
            else:
                W.append([-i*(m-i)/m*(K(q)).log() for i in range(1, (m/2).floor() + 1)])

    for j in range(len(W)):
        q = bad_primes_new[j]
        if q == 2:
            if E.has_split_multiplicative_reduction(q):
                continue
        W[j] = [0] + W[j]
        if delta.valuation(q) > 0:
            W[j] = f7(W[j] + [2*k*K(q).log() for k in range(1, ZZ(delta.valuation(q)/12) + 1)])

    bad_primes_new_new = bad_primes_new
    for q in factors_delta:
        if q not in bad_primes_new:
            if (q == 2 and E.Np(2) == 1) or (q == 3 and E.Np(3) == 1):
                W.append([2*k*K(q).log() for k in range(1, ZZ(delta.valuation(q)/12) + 1)])
            else:
                W.append([2*k*K(q).log() for k in range(0, ZZ(delta.valuation(q)/12) + 1)])
            bad_primes_new_new.append(q)
    return bad_primes_new_new, W

def adjusted_prec_Log(n, p):
    r"""
    Compute sufficient `t`-adic precision so
    that the formal group logarithm on an elliptic curve
    returns currect results modulo `p^n`.
    For `n <= p^p-p`, uses proof of [Proposition 3.11, BBCF+19].
    """
    if n <= p^p -p:
        M = n
        r = n
        while r % p != 0:
            r += 1
        if r - r.valuation(p) < n:
            M = r + 1
    else:
        M = n
        while M - RR(log(M)/log(p)).floor() < n:
            M += 1
        # m-ord_p(m) >= m-(log_p(m)).floor()
        # the RHS is increasing as (log_p(m+1)).floor() <= (log_p(m)).floor() + 1
        # so suffices to find the smallest M for which M-(log_p(M)).floor() >= n.
    return M


def Dpol(pol, E):
    r"""
    Given an elliptic curve E and a polynomial pol in x or x,y,
    return the image of pol under the invariant
    derivation dual to `dx/(2*y + E.a1()*x + E.a3())`
    It also returns the polynomial pol as a polynomial in x,y.
    """
    R.<x,y> = PolynomialRing(pol.base_ring())
    pol = R(pol)
    f = x^3 + E.a2()*x^2 + E.a4()*x + E.a6()
    return pol.derivative(x)*(2*y + E.a1()*x + E.a3()) + pol.derivative(y)*(f.derivative(x) - E.a1()*y), pol


def int_w1_b(E, P, p, m, prec, fm = False, Dfm = False):
    r"""
    Given an elliptic curve E (over `\QQ` or `\QQ_p`for some `p`)
    and a non-torsion point `P` in `E(\QQ_p)`, return the integral of
    `x*dx/(2*y + E.a1()*x + E.a3())` from a tangential base point at
    infinity to `P`.
    NB: this does not use Coleman integration, but only
    transformation properties under group law and formal group integrals;
    `p` need not be of good reduction.
    INPUT:
    - ``E`` -- an elliptic curve over `\QQ` or `\QQ_p'.
    - ``P`` -- a point on ``E`` over `\QQ_p`.
    - ``p`` -- the prime of the first two input items.
    - ``m`` -- an integer such that `mP` lies in the formal group at `p`.
    - ``prec`` -- the desired absolute precision of the output
      (NB:the output could be returned at lower precision
      if P is not known at high enough precision).
    - ``fm`` -- the `m`-th division polynomial for `E` or `False`.
      If `False`, the `m`-th division polynomial is computed.
    - ``Dfm`` -- the image of `fm` under the invariant
      derivation dual to `dx/(2*y + E.a1()*x + E.a3())` or `False`.
      If `False`, `Dfm` is computed.
    OUTPUT:
    A `p`-adic number: `\int_b^P (x*dx/(2*y + E.a1()*x + E.a3()))`
    EXAMPLES:
        sage: E = EllipticCurve("37.a1")
        sage: p = 5
        sage: P = E(0,-1)
        sage: E.change_ring(GF(p))(P).order()
        8
        sage: int_w1_b(E, P, p, 8, 10)
        4*5 + 3*5^3 + 3*5^5 + 3*5^6 + 3*5^9 + O(5^10)
        sage: int_w1_b(E, P, p, 8, 10) ==  int_w1_b(E, P, p, 16, 10)
        True
    Comparing with the Coleman integration algorithm:
        sage: Eshort = E.short_weierstrass_model()
        sage: EshortK = Eshort.change_ring(Qp(p,22))
        sage: phi = E.isomorphism_to(Eshort)
        sage: EshortK.coleman_integrals_on_basis(EshortK(0,1,0), EshortK(phi(P)))[1]
        3*5 + 5^2 + 5^3 + 5^4 + 5^5 + 2*5^6 + 5^7 + 5^9 + 5^10 + 3*5^11 + 5^12 + 2*5^13 + 5^14 + 5^15 + 2*5^16 + 3*5^17 + 5^18 + 2*5^19 + 5^20 + 4*5^21 + 5^22 + O(5^23)
        sage: int_w1_b(Eshort, phi(P), p, 8, 22) #not comparing the 5^22-digit as it's not correct in the Coleman integration algorithm (try increasing prec and see it changes.)
        3*5 + 5^2 + 5^3 + 5^4 + 5^5 + 2*5^6 + 5^7 + 5^9 + 5^10 + 3*5^11 + 5^12 + 2*5^13 + 5^14 + 5^15 + 2*5^16 + 3*5^17 + 5^18 + 2*5^19 + 5^20 + 4*5^21 + O(5^22)
    An example in bad reduction: the final output of this
    computation should match the integral between `-R` and `R`
    in Example 7.1 of [Kay22]. Indeed it does.
        sage: E = EllipticCurve([-1351755,555015942]) #LMFDB label: 6622.i3
        sage: R = E(219,16416)
        sage: p = 43
        sage: E.has_split_multiplicative_reduction(p)
        True
        sage: E.tamagawa_number(43)
        1
        sage: 2*int_w1_b(E, R, p, 42, 6)
        40 + 8*43 + 34*43^2 + 26*43^3 + 25*43^4 + 34*43^5 + O(43^6)
    """
    if fm == False:
        if m % 2 == 1:
            fm = E.division_polynomial(m)
        else:
            fm = E.division_polynomial(m, two_torsion_multiplicity = 1)
    else:
        R.<x,y> = PolynomialRing(fm.base_ring())
        fm = R(fm)
    if Dfm == False:
        Dfm, fm = Dpol(fm, E)
    else:
        R.<x,y> = PolynomialRing(fm.base_ring())
        Dfm = R(Dfm)
    fmP = fm(P[0],P[1])
    DfmP = Dfm(P[0],P[1])
    mP = m*P
    tmP = -mP[0]/mP[1]
    assert tmP % p == 0, "mP is not in the formal group."
    Ef = E.formal_group()
    des_prec = prec + m.valuation(p)
    adj_prec = adjusted_prec_Log(des_prec, p)
    xinf = Ef.x(prec = adj_prec)
    omegainf = Ef.differential(prec = adj_prec + 2)
    omega1 = xinf*omegainf
    t = omega1.parent().gens()[0]
    intmP = (omega1.integral()+t^(-1)).power_series().truncate()(tmP) - tmP^(-1) + E.a1()/2
    #note: E.a1()/2 is the needed constant of integration to guarantee that the integral is odd.
    out = 1/m*(intmP + 1/m*DfmP/fmP) + O(p^prec)
    prec_rel = out.precision_relative()
    return Qp(p, prec_rel)(out)


def coefficients_mod_pN(f, points, divisors, base_pt, splitting_indices, p, N, k=5):
    r"""
    Compute the coefficients modulo `p^N` in `J(\QQ)/tors` of the images of `points`
    under the embedding in the Jacobian with respect to `base_pt`.
    INPUT:
    - ``f`` --  a polynomial over `\QQ` of the form `a_6*x^6 + a_4*x^4 + a_2*x^2 + a_0`,
      `a_i \in \ZZ`.
    - ``points`` -- a list of rational or p-adic points on `H: y^2 = f(x)`.
    - ``divisors`` -- a list of two lists of the form `[P_1,P_2]`, where `P_i`
      is a point in `H(\QQ)` or `H(\QQ_p)` (`inf+` or `inf-` allowed),
      such that `P_1 - P_2`is a \QQ-rational divisor.
      These should generate a subgroup of finite index in `J(\QQ)`.
    - ``base_pt`` -- a point in `H(\QQ)` (`inf+` or `inf-` allowed).
    - ``splitting_indices`` - a list of two lists. Each of the latter lists is a pair of integers.
      these should  be such that `divisors[i] - (splitting_indices[i][0]*B1 + splitting_indices[i][1]*B2) \in J(\QQ)_{tors}`
      for a fixed basis B_1, B_2 for `J(\QQ)/torsion`.
    - ``p`` -- an odd prime (the same one as above)
    - ``N`` -- an integer.
    - ``k`` -- an integer (default  5).
    OUTPUT: a list of length `len(points)`. The i-th element in the list is a pair
    `[a,b]` of p-adic numbers to absolute precision `p^N` with the following property:
    if `Q = [points[i] - base_pt]\in J(\QQ)` and `Q - (A*B1 + B*B2) \in J(\QQ)_{tors}
    then `A = a mod p^N` and `B = b mod p^N`.
    .. NOTE::
       If the output is returned at lower precision, either the points are known at too low
       precision, or try increasing k.
    EXAMPLES:
    Coefficients with respect to [B1, B2]  = [ (x^2 + 1/3, -4/3*x, 2), (x^2 + 2/5*x + 1/5, 8/5*x + 4/5, 2) ]
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = 25*x^6 - 3*x^4 - 5*x^2 - 1 #LMFDB label: 9245.a.46225.1
        sage: H = HyperellipticCurve(f)
        sage: divisors = [[H(-1,-4), 'inf-'], [H(1,4), H(-1,-4)]]
        sage: splitting_indices = [[1, -1], [1, 2]]
        sage: base_pt = H(1,4)
        sage: p = 11
        sage: N = 5
        sage: coefficients_mod_pN(f,[H(1,-4)], divisors, base_pt, splitting_indices, p, N)
        [[1 + O(11^5), 9 + 10*11 + 10*11^2 + 10*11^3 + 10*11^4 + O(11^5)]]
        #you can check that B1 - 2*B2 = [H(1,-4) - H(1,4)].
    """
    K = Qp(p,N+k)
    a6 = f[6]
    a4 = f[4]
    a2 = f[2]
    a0 = f[0]
    E1 = EllipticCurve([0, a4, 0, a2*a6, a0*a6^2])
    E2 = EllipticCurve([0, a2, 0, a0*a4, a0^2*a6])
    M1 = E1.change_ring(GF(p)).abelian_group().exponent()
    M2 = E2.change_ring(GF(p)).abelian_group().exponent()
    adj_prec_1 = adjusted_prec_Log(N + k + M1.valuation(p),p)
    adj_prec_2 = adjusted_prec_Log(N + k + M2.valuation(p),p)
    Log1 = E1.formal_group().log(adj_prec_1).truncate()
    Log2 = E2.formal_group().log(adj_prec_2).truncate()
    E1K = E1.change_ring(K)
    E2K = E2.change_ring(K)

    basis_integrals_w1 = []
    for D in divisors:
        phi1D = [X_to_E1map(D[0], E1, a6), X_to_E1map(D[1], E1, a6)]
        M1phi1D0 = M1*phi1D[0]
        M1phi1D1 = M1*phi1D[1]
        Log10 = Log1(-M1phi1D0[0]/M1phi1D0[1])/M1
        Log11 = Log1(-M1phi1D1[0]/M1phi1D1[1])/M1
        basis_integrals_w1.append(1/2*(Log10-Log11))
    basis_integrals_w0 = []
    for D in divisors:
        phi2D = [X_to_E2map(D[0], E2, a0, a6), X_to_E2map(D[1], E2, a0, a6)]
        M2phi2D0 = M2*phi2D[0]
        M2phi2D1 = M2*phi2D[1]
        Log20 = Log2(-M2phi2D0[0]/M2phi2D0[1])/M2
        Log21 = Log2(-M2phi2D1[0]/M2phi2D1[1])/M2
        basis_integrals_w0.append(-1/2*(Log20-Log21))

    adj = max([a.valuation(p) for a in basis_integrals_w0 + basis_integrals_w1 if a!=0])
    M = (Matrix(Qp(p,N+k - adj),[basis_integrals_w0, basis_integrals_w1]))^(-1)
    index_matrix = Matrix(splitting_indices).transpose()
    M1phi1base_pt = M1*X_to_E1map(base_pt, E1,a6)
    M2phi2base_pt = M2*X_to_E2map(base_pt, E2, a0, a6)
    Log1base_pt = 1/M1*Log1(K(-M1phi1base_pt[0]/M1phi1base_pt[1])) + O(p^(N+k))
    Log2base_pt = 1/M2*Log2(K(-M2phi2base_pt[0]/M2phi2base_pt[1])) + O(p^(N+k))

    coeffs = []
    for P in points:
        M1phi1P = M1*X_to_E1map(P, E1K,a6)
        M2phi2P = M2*X_to_E2map(P, E2K, a0, a6)
        Log1P = 1/M1*Log1(K(-M1phi1P[0]/M1phi1P[1])) + O(p^(N+k))
        Log2P = 1/M2*Log2(K(-M2phi2P[0]/M2phi2P[1])) + O(p^(N+k))

        coeffsP = index_matrix*M*Matrix(2,1,[-1/2*(Log2P -Log2base_pt), 1/2*(Log1P -Log1base_pt)])
        coeffs.append([coeffsP[0][0] + O(p^N),coeffsP[1][0] + O(p^N)])
    return coeffs


def coefficients_mod_pN_v2(f, points, im_divisors, base_pt, p, N, k=5):
    r"""
    Compute the coefficients modulo `p^N` in `J(\QQ)/tors` of the images of `points`
    under the embedding in the Jacobian with respect to `base_pt`.
    Differently from `coefficients_mod_pN`, the coefficients are computed from knowledge
    of the pushforward of generators of `J(\QQ)/tors` to the two elliptic curves.
    INPUT:
    - ``f`` --  a polynomial over `\QQ` of the form `a_6*x^6 + a_4*x^4 + a_2*x^2 + a_0`,
      `a_i \in \ZZ`.
    - ``points`` -- a list of rational or p-adic points on `H: y^2 = f(x)`.
    - ``im_divisors`` -- a list of two lists. Each list contains a point
      on `E_1: y^2 = x^3 + a4*x^2 + a2*a6*x + a0*a6^2` and one on
      `E_2: y^2 = x^3 + a2*x^2 + a0*a4*x + a0^2*a6`.
      The points are pushforwards under the appropriate quotient map of generators `B_1, B_2` of `J(\QQ)/tors`.
      The first list corresponds to `B_1`, the second one to `B_2`.
    - ``base_pt`` -- a point in `H(\QQ)` (`inf+` or `inf-` allowed).
    - ``p`` -- an odd prime (the same one as above)
    - ``N`` -- an integer.
    - ``k`` -- an integer (default  5).
    OUTPUT: a list of length `len(points)`. The i-th element in the list is a pair
    `[a,b]` of p-adic numbers to absolute precision `p^N` with the following property:
    if `Q = [points[i] - base_pt]\in J(\QQ)` and `Q - (A*B1 + B*B2) \in J(\QQ)_{tors}
    then `A = a mod p^N` and `B = b mod p^N`.
    .. NOTE::
       If the output is returned at lower precision, either the points are known at too low
       precision, or try increasing k.
    EXAMPLES:
    Coefficients with respect to [B1, B2]  = [ (x^2 + 1/3, -4/3*x, 2), (x^2 + 2/5*x + 1/5, 8/5*x + 4/5, 2) ]
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = 25*x^6 - 3*x^4 - 5*x^2 - 1 #LMFDB label: 9245.a.46225.1
        sage: H = HyperellipticCurve(f)
        sage: im_divisors = [[ (0, 1, 0), (-1, 4, 1) ], [ (25, 100, 1), (3, 4, 1) ]]
        sage: base_pt = H(1,4)
        sage: p = 11
        sage: N = 5
        sage: coefficients_mod_pN_v2(f,[H(1,-4)], im_divisors, base_pt, p, N)
        [[1 + O(11^5), 9 + 10*11 + 10*11^2 + 10*11^3 + 10*11^4 + O(11^5)]]
        #you can check that B1 - 2*B2 = [H(1,-4) - H(1,4)].
    """
    K = Qp(p,N+k)
    a6 = f[6]
    a4 = f[4]
    a2 = f[2]
    a0 = f[0]
    E1 = EllipticCurve([0, a4, 0, a2*a6, a0*a6^2])
    E2 = EllipticCurve([0, a2, 0, a0*a4, a0^2*a6])
    M1 = E1.change_ring(GF(p)).abelian_group().exponent()
    M2 = E2.change_ring(GF(p)).abelian_group().exponent()
    adj_prec_1 = adjusted_prec_Log(N + k + M1.valuation(p),p)
    adj_prec_2 = adjusted_prec_Log(N + k + M2.valuation(p),p)
    Log1 = E1.formal_group().log(adj_prec_1).truncate()
    Log2 = E2.formal_group().log(adj_prec_2).truncate()
    E1K = E1.change_ring(K)
    E2K = E2.change_ring(K)

    basis_integrals_w1 = []
    for D in im_divisors:
        phi1D = E1(D[0])
        M1phi1D0 = M1*phi1D
        Log10 = Log1(-M1phi1D0[0]/M1phi1D0[1])/M1
        basis_integrals_w1.append(1/2*Log10)
    basis_integrals_w0 = []
    for D in im_divisors:
        phi2D = E2(D[1])
        M2phi2D0 = M2*phi2D
        Log20 = Log2(-M2phi2D0[0]/M2phi2D0[1])/M2
        basis_integrals_w0.append(-1/2*Log20)

    adj = max([a.valuation(p) for a in basis_integrals_w0 + basis_integrals_w1 if a!=0])
    M = (Matrix(Qp(p,N+k - adj),[basis_integrals_w0, basis_integrals_w1]))^(-1)
    M1phi1base_pt = M1*X_to_E1map(base_pt, E1,a6)
    M2phi2base_pt = M2*X_to_E2map(base_pt, E2, a0, a6)
    Log1base_pt = 1/M1*Log1(K(-M1phi1base_pt[0]/M1phi1base_pt[1])) + O(p^(N+k))
    Log2base_pt = 1/M2*Log2(K(-M2phi2base_pt[0]/M2phi2base_pt[1])) + O(p^(N+k))
    coeffs = []

    for P in points:
        M1phi1P = M1*X_to_E1map(P, E1K,a6)
        M2phi2P = M2*X_to_E2map(P, E2K, a0, a6)
        Log1P = 1/M1*Log1(K(-M1phi1P[0]/M1phi1P[1])) + O(p^(N+k))
        Log2P = 1/M2*Log2(K(-M2phi2P[0]/M2phi2P[1])) + O(p^(N+k))

        coeffsP = M*Matrix(2,1,[-1/2*(Log2P -Log2base_pt), 1/2*(Log1P -Log1base_pt)])
        coeffs.append([coeffsP[0][0] + O(p^N),coeffsP[1][0] + O(p^N)])
    return coeffs


def Omega_set(f, p, n,  Es = None, Emins = None, potential_good_primes = True):
    r"""
    Compute a finite set containing Omega
    INPUT:
    - ``f`` -- a polynomial over `\QQ` of the form `a_6*x^6 + a_4*x^4 + a_2*x^2 + a_0`,
      `a_i \in \ZZ`.
    - ``p`` -- an odd prime such that `E_1: y^2 = x^3 + a_4*x^2 + a_2*a_6*x + a_0*a_6^2`
      and `E_2: y^2 = x^3 + a_2*x^2 + a0*a4*x + a_0^2*a_6` have good reduction at `p`.
    - ``n`` -- working `p`-adic precision.
    - ``Es`` -- `[E_1, E_2]` or `None`. If `None`, `E_1` and `E_2` are computed.
    - ``Emins`` -- `[E_1,min, E_2,min]` where `E_i,min` is a global minimal model for `E_i`,
      or `None`. If `None`, `E_1,min` and `E_2,min` are computed.
    - ``potential_good_primes`` -- True/False (default True): if True, and ``Omega`
      is not provided, it uses the fact that there is only one contribution
      at the primes of potential good reduction for `y^2 = f(x)`.
    OUTPUT: A list of `p`-adic numbers.
    """
    a0 = f[0]
    a6 = f[6]
    H = HyperellipticCurve(f)
    if Es == None:
        a4 = f[4]
        a2 = f[2]
        E1 = EllipticCurve([0, a4, 0, a2*a6, a0*a6^2])
        E2 = EllipticCurve([0, a2, 0, a0*a4, a0^2*a6])
    else:
        E1 = Es[0]
        E2 = Es[1]
    if Emins == None:
        E1min = E1.minimal_model()
        E2min = E2.minimal_model()
    else:
        E1min = Emins[0]
        E2min = Emins[1]
    K = Qp(p,n)
    bad_primes_1, W1 = local_heights_at_bad_primes_new(E1min, E1, K)
    bad_primes_2, W2 = local_heights_at_bad_primes_new(E2min, E2, K)
    bad_primes_3 = f7(ZZ(a0).prime_factors() + ZZ(a6).prime_factors())
    bad_primes = f7(bad_primes_1 + bad_primes_2 + bad_primes_3)
    Wqprimelist = []
    for q in bad_primes:
        if potential_good_primes == True:
            if has_potential_good_reduction(H, q) == True:
                ###edits below to check for the existence of a point, KF2025
                instring = "R<x>:=PolynomialRing(Rationals());X:=HyperellipticCurve("+str(f)+");IsLocallySolvable(X,"+str(q)+");"
                haspoint = magma_free(instring)
                #print(haspoint)
                if haspoint[0:4] == 'true':
                    #print("using potential good reduction at", q)
                    phi1 = E1.isomorphism_to(E1min)
                    phi2 = E2.isomorphism_to(E2min)
                    Hq = H.change_ring(Qp(q,n))
                    for xq in [1,..,q, q^(-1),q^(-2),q^(-3),q^(-4)]:
                        try:
                            Pq = Hq.lift_x(xq)
                            f1Pq = X_to_E1map(Pq, E1.change_ring(Qp(q,n)), a6)
                            f2Pq = X_to_E2map(Pq, E2.change_ring(Qp(q,n)), a0, a6)
                            break
                        except ValueError:
                            pass
                    try:
                        lambdaqf1P_min = non_archimedean_local_height(phi1(f1Pq), q, p, n,is_minimal=True)
                        lambdaqf2P_min = non_archimedean_local_height(phi2(f2Pq), q, p, n,is_minimal=True)
                        Wqprime = [-lambdaqf1P_min + lambdaqf2P_min - 2*(Pq[0].valuation(q))*log(K(q))]
                        Wqprimelist.append(Wqprime)
                        continue
                    except TypeError:
                        pass

        if q in bad_primes_1:
            WE1q = W1[bad_primes_1.index(q)]
        else:
            if q == 2 and E1.Np(2) == 1:
                WE1q = []
            elif q == 3 and E1.Np(3) == 1:
                WE1q = []
            elif q == 2 and E1.has_split_multiplicative_reduction(2) == True and E1.kodaira_symbol(2) == KodairaSymbol(5):
                WE1q = []
            else:
                WE1q = [0]
        if q in bad_primes_2:
            WE2q = W2[bad_primes_2.index(q)]
        else:
            if q == 2 and E2.Np(2) == 1:
                WE2q = []
            elif q == 3 and E2.Np(3) == 1:
                WE2q = []
            elif q == 2 and E2.has_split_multiplicative_reduction(2) == True and E2.kodaira_symbol(2) == KodairaSymbol(5):
                WE2q = []
            else:
                WE2q = [0]

        evenq = [2*i for i in range(((-(a6).valuation(q))/2).ceil(), ((a0).valuation(q)/2).floor()+1)]
        W1W2evenq = [WE1q, WE2q, evenq]
        Wqprime = f7([-w1 - a0.valuation(q)*log(K(q)) + O(p^n) for w1 in WE1q] +
                             [-w1w2n[0] + w1w2n[1] - w1w2n[2]*log(K(q)) + O(p^n) for w1w2n in itertools.product(*W1W2evenq)] +
                             [w2 + a6.valuation(q)*log(K(q)) + O(p^n) for w2 in WE2q])
        Wqprimelist.append(Wqprime)

    Wlist = list(itertools.product(*Wqprimelist))
    Omega = []
    for i in Wlist:
        Omega.append(sum(list(i)))
    Omega = f7(Omega)
    return Omega


############## MAIN FUNCTION ###############
def smallpol(polynomial):
    return all(abs(coef) < 1000 for coef in polynomial.coefficients())


def quadratic_chabauty_bielliptic(f, p, n, Omega=[], potential_good_primes = True, up_to_auto = False, omega_info = False, F = QQ):
    r"""
    Do quadratic Chabauty on a genus `2` bielliptic curve of rank `2`.
    INPUT:
    - ``f`` -- a polynomial over `\QQ` of the form `a_6*x^6 + a_4*x^4 + a_2*x^2 + a_0`,
      `a_i \in \ZZ`. The two elliptic curves `E_1: y^2 = x^3 + a_4*x^2 + a_2*a_6*x + a_0*a_6^2`
      and `E_2: y^2 = x^3 + a_2*x^2 + a0*a4*x + a_0^2*a_6` should have rank `1` over `\QQ`, or in the case when
    - ``F`` -- default is `\QQ` but in the case when the curve is `X_0(37)`, it can be `\QQ(i)` [JB2023]  
    - ``p`` -- an odd prime not equal to 3 such that `E_1` and `E_2` have good ordinary reduction at`p`.
    - ``n`` -- working `p`-adic precision.
    - ``Omega`` -- list of the values in `Omega` from [BP22],
      but with respect to minimal models for the elliptic curves (i.e. they equal the ones of [BP22] only up to a translation).
      This is because in this code the heights are computed wrt minimal models (due to a bug in Sage for heights on non-minimal models).
      If not provided, a finite set containing `Omega` is calculated (see [BP22]), in such a way that
      the order is compatible if we vary the prime p.
    - ``potential_good_primes`` -- True/False (default True): if True, and ``Omega`
      is not provided, it uses the fact that there is only one contribution
      at the primes of potential good reduction for `H`.
    - ``up_to_auto`` -- True/False (default False): if True, the points in the output
      items are returned up to the automorphisms `(x,y) \mapsto (\pm x,\pm y)`
    - ``omega_info`` -- True/False (default False): if True, the output is partitioned
      according to elements in `Omega`.

    OUTPUT: If `omega_info` is False: A tuple consisting of:
    - A sorted list of rational points on `H`.
    - A sorted list of `p`-adic points on `H` which have not been recognised as rational points.
      The precision of these depends on `n` but is, in general, smaller than `n`.
      If this list is empty, then the former list is equal to the list of rational points on `H`.

            If `omega_info` is True: A tuple consisting of:
    - A list of sorted lists of rational points on `H`. The points in the `i`-th list
      are zeros of the function corresponding to the `i`-th element in `Omega`.
    - A list of sorted lists of `p`-adic points on `H` which have not been recognised as rational points.
      The precision of these depends on `n` but is, in general, smaller than `n`.
      The points in the `i`-th list are zeros of the function corresponding to the `i`-th element in Omega.
      If all lists are empty, then all the rational  points of `H` are in the previous list.
    .. NOTE::
        If `Omega` is not provided, the size of the computed `Omega` is printed.
    EXAMPLES:
    An example where quadratic Chabauty suffices to compute the rational points:
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^6 + 22*x^4 - 19*x^2 + 4 #LMFDB label: 99856.b.99856.1
        sage: rat_points,other_points = quadratic_chabauty_bielliptic(f,3,20)
        Number of elements in Omega = 3
        sage: rat_points
        [(-3/4 : -43/64 : 1), (-3/4 : 43/64 : 1), (0 : -2 : 1), (0 : 1 : 0), (0 : 2 : 1), (3/4 : -43/64 : 1), (3/4 : 43/64 : 1)]
        sage: other_points
        []
    Same example, but computing points up to automorphism:
        sage: quadratic_chabauty_bielliptic(f,3,20,up_to_auto = True)
        Number of elements in Omega = 3
        ([(0 : 1 : 0), (0 : 2 : 1), (3/4 : -43/64 : 1)], [])
    For the same curve quadratic Chabauty with p = 5 would not suffice to determine the rational points:
        sage: rat_points,other_points = quadratic_chabauty_bielliptic(f,5,20)
        Number of elements in Omega = 3
        sage: rat_points
        [(-3/4 : -43/64 : 1), (-3/4 : 43/64 : 1), (0 : -2 : 1), (0 : 1 : 0), (0 : 2 : 1), (3/4 : -43/64 : 1), (3/4 : 43/64 : 1)]
        sage: len(other_points)
        8
    Omega info: we can sometimes determine the set of rational points by using more than one prime and
    comparing only extra points corresponding to compatible elements in Omega, as in the following example:
        sage: R.<x> = PolynomialRing(Rationals())
        sage: f = x^6 - 4*x^4 - 4*x^2 - 4 #LMFDB label: 274576.a.274576.1
        sage: rat_points_3,other_points_3 = quadratic_chabauty_bielliptic(f,3,20,omega_info=True)
        Number of elements in Omega = 3
        sage: rat_points_3
        [[], [(0 : 1 : 0)], []]
        sage: rat_points_7,other_points_7 = quadratic_chabauty_bielliptic(f,7,20,omega_info=True)
        Number of elements in Omega = 3
        sage: rat_points_7
        [[], [(0 : 1 : 0)], []]
        sage: print([len(other_points_3[i]) for i in range(3)])
        [0, 0, 12]
        sage: print([len(other_points_7[i]) for i in range(3)])
        [20, 16, 0]
    """
    H = HyperellipticCurve(f)
    a6 = f[6]
    a4 = f[4]
    a2 = f[2]
    a0 = f[0]
    E1 = EllipticCurve([0, a4, 0, a2*a6, a0*a6^2])
    E2 = EllipticCurve([0, a2, 0, a0*a4, a0^2*a6])
    assert E1.has_good_reduction(p) and E2.has_good_reduction(p), "p needs to be a prime of good reduction for the given model."
    assert E1.is_ordinary(p) and E2.is_ordinary(p), "Currently implemented only for ordinary primes (precision analysis is easier)."
    assert p != 3, "p cannot be 3"
    K = Qp(p, n)

    #Step 1: computing minimimal models of E1, E2 and isomorphisms to and from them,
    #generators of the free parts of E1(Q), E2(Q) and their heights:
    #Note: the code for p-adic heights has a bug which sometimes produces a wrong answer
    #when the model is not minimal. That's why we switch to minimal models here.
    #Example of the bug on SageMath version 9.6
    #sage: E = EllipticCurve([0,1,1,-2,0])
    #sage: Eshort = E.short_weierstrass_model()
    #sage: P = E.gens()[0]
    #sage: phi = E.isomorphism_to(Eshort)
    #sage: Eshort.padic_height(5)(2*phi(P)) - 4*Eshort.padic_height(5)(phi(P)) #should be 0
    #5 + 4*5^2 + 4*5^3 + 2*5^5 + 5^7 + 5^8 + 2*5^9 + 5^10 + 4*5^11 + 3*5^12 + 5^13 + 5^16 + 5^18 + O(5^20)
    #JB2023 edits below
    E1m = E1.minimal_model()
    E2m = E2.minimal_model()
    delta1 = E1.discriminant()/E1m.discriminant()
    delta2 = E2.discriminant()/E2m.discriminant()
    S = F
    E1mS = E1m.change_ring(S)
    E2mS = E2m.change_ring(S)
    h1 = E1m.padic_height(p, n)
    h2 = E2m.padic_height(p, n)
    P1m = E1mS.gens()[0]
    P2m = E2mS.gens()[0]
    E1S = E1.change_ring(S)
    E2S = E2.change_ring(S)
    psi1 = E1mS.isomorphism_to(E1S)
    psi2 = E2mS.isomorphism_to(E2S)
    D = S.discriminant()
    #check D != 1
    if D != 1:
        hP1 = cyc_padic_height_quad(E1mS, S, P1m, p)
        hP2 = cyc_padic_height_quad(E2mS, S, P2m, p)
    else:
        hP1 = E1mS.padic_height(p,n)(P1m)
        hP2 = E2mS.padic_height(p,n)(P2m)
    P1 = psi1(P1m)
    P2 = psi2(P2m)
    #JB2023 edits end

    HK = H.change_ring(K)
    E1K = E1.change_ring(K)
    E2K = E2.change_ring(K)
    E1p = E1.change_ring(GF(p))
    E2p = E2.change_ring(GF(p))
    m1 = E1p.abelian_group().exponent()
    m2 = E2p.abelian_group().exponent()

    E2_p_1 = E1.padic_E2(p, n + p.valuation(3), check_hypotheses=False) #n-2 would suffice for sigma (at least if p>=5)
    E2_p_2 = E2.padic_E2(p, n + p.valuation(3), check_hypotheses=False)
    try:
        sigma1 = E1.padic_sigma(p, n, E2 = E2_p_1).truncate()
    except ValueError:
        E2_p_1 = E1.padic_E2(p, n + p.valuation(3) + 5, check_hypotheses=False)
        sigma1 =  E1.padic_sigma(p, n, E2 = E2_p_1).truncate()
    try:
        sigma2 = E2.padic_sigma(p, n, E2 = E2_p_2).truncate()
    except ValueError:
        E2_p_2 = E2.padic_E2(p, n + p.valuation(3) + 5, check_hypotheses=False)
        sigma2 = E2.padic_sigma(p, n, E2 = E2_p_2).truncate()
    c1 = (E1.a1()^2 + 4*E1.a2() - E2_p_1)/12
    c2 = (E2.a1()^2 + 4*E2.a2() - E2_p_2)/12

    Log_prec = adjusted_prec_Log(n + max([m1.valuation(p), m2.valuation(p)]), p)
    Log1 = E1.formal_group().log(prec=Log_prec).truncate()
    Log2 = E2.formal_group().log(prec=Log_prec).truncate()

    #JB2023 edits below
    if D != 1:
        frakp = factor(p*S)
        frakp0 = frakp[0][0]
        ordP1 = P1.reduction(frakp0).order()
    else:
        ordP1 = E1p(P1).order()
    mP1 = ordP1*P1
    if D!= 1:
        ordP2 = P2.reduction(frakp0).order()
    else:
        ordP2 = E2p(P2).order()
    mP2 = ordP2*P2
    if D!= 1:
        #now need to fix an embedding: take S_frakp0 into Qp
        emb2, emb1 = embeddings(S,p,n)
        Log1P1 = 1/ordP1*Log1(K(-emb1(mP1[0]/mP1[1]))) + O(p^n)
        Log2P2 = 1/ordP2*Log2(K(-emb1(mP2[0]/mP2[1]))) + O(p^n)
    else:
        Log1P1 = 1/ordP1*Log1(K(-(mP1[0]/mP1[1]))) + O(p^n)
        Log2P2 = 1/ordP2*Log2(K(-(mP2[0]/mP2[1]))) + O(p^n)
    #JB2023 edits end

    Log1P1 = Qp(p, n-Log1P1.valuation())(Log1P1)
    Log2P2 = Qp(p, n-Log2P2.valuation())(Log2P2)

    if D!= 1:                     #JB2023
        alpha1 = -p* hP1/Log1P1^2 #JB2023
        alpha2 = -p* hP2/Log2P2^2 #JB2023
    else:
        alpha1 = hP1/Log1P1^2
        alpha2 = hP2/Log2P2^2

    #Discs
    Hp = H.change_ring(GF(p))
    Hppoints = Hp.points()
    D = Hppoints[:]
    if GF(p)(a6).is_square() == False:
        D.remove(Hp(0,1,0))
    #Modding out by automorphisms
    Dnew = []
    for P in D:
        if Hp(P[0],-P[1],P[2]) in Dnew or Hp(-P[0],P[1],P[2]) in Dnew or Hp(-P[0],-P[1],P[2]) in Dnew:
            continue
        Dnew.append(P)
    D = Dnew

    if m1 % 2 != 0:
        fm1 = E1.division_polynomial(m1)
    else:
        fm1 = E1.division_polynomial(m1, two_torsion_multiplicity=1)
    Dfm1, fm1 = Dpol(fm1, E1)

    if m2 % 2 != 0:
        fm2 = E2.division_polynomial(m2)
    else:
        fm2 = E2.division_polynomial(m2, two_torsion_multiplicity=1)
    Dfm2, fm2 = Dpol(fm2, E2)

    #Computing Omega if not provided
    if Omega == []:
        Omega = Omega_set(f, p, n,  Es = [E1,E2], Emins = [E1m, E2m], potential_good_primes = potential_good_primes)
        size_Omega = len(Omega)
        print("Number of elements in Omega =", size_Omega);
    else:
        size_Omega = len(Omega)

    points = [[] for i in range(size_Omega)]
    rho_list = []

    for P in D:
        if P[2] != 0:
            Q = Q_lift(HK, P, p)
            f1 = X_to_E1map(Q, E1K, a6)
            f2 = X_to_E2map(Q, E2K, a0, a6)
            xx, yy = HK.local_coord(Q, prec = n)
        else:
            Q = HK(0, 1, 0)
            f1 = X_to_E1map(Q, E1K, a6)
            if a6.is_square() == False:
                f2 = X_to_E2map(Q, E2K, a0, K(a6))
            else:
                f2 = X_to_E2map(Q, E2K, a0, a6)
            xx, yy = local_coordinates_at_infinity_g2_even(HK, prec = n)

        #Constants
        if f1[2] == 0:
            Logf1 = 0
            int_w1_b_f1 = 0
            hf1 = 0
        elif m1*f1 == E1K(0,1,0):
            Logf1 = 0
            try:
                int_w1_b_f1 = H1K.coleman_integrals_on_basis(H1K(-f1), H1K(f1))[1]*(1/2) ### KF2025
            except NameError:
                H1K = HyperellipticCurve(E1K.hyperelliptic_polynomials()[0])
                int_w1_b_f1 = H1K.coleman_integrals_on_basis(H1K(-f1), H1K(f1))[1]*(1/2) ### KF2025
            if f1[1] != 0:
                f1alg_x = QQ(f1[0])
                try:
                    f1alg = E1.lift_x(f1alg_x)
                except ValueError:
                    polE1 = E1.defining_polynomial()
                    x1,y1,z1 = polE1.parent().gens()
                    polval = polE1(f1alg_x,y1,1)
                    L.<f1alg_y> = NumberField(PolynomialRing(QQ,"x")(polval[0,0,0] + x^2*polval[0,2,0]))
                    E1L = E1.change_ring(L)
                    f1alg = E1L.lift_x(f1alg_x)
                hf1 = -non_archimedean_local_height(f1alg, None, p, n)
            else:
                hf1 = 1/2*log(K(3*f1[0]^2 + 2*E1.a2()*f1[0] + E1.a4())) #by [BBM16, Lemma 4.1]
        else:
            mf1 = m1*f1
            Logf1 = 1/m1*Log1(-K(mf1[0]/mf1[1]))
            int_w1_b_f1 = int_w1_b(E1, f1, p, m1, n, fm = fm1, Dfm = Dfm1)
            hf1 = -2/m1^2*log(sigma1(-mf1[0]/mf1[1])/fm1(f1[0],f1[1]))
        if f2[2] == 0:
            Logf2 = 0
            int_w1_b_f2 = 0
            hf2 = 0
        elif m2*f2 == E2K(0,1,0):
            Logf2 = 0
            try:
                int_w1_b_f2 = H2K.coleman_integrals_on_basis(H2K(-f2), H2K(f2))[1]*(1/2) ### KF2025
            except NameError:
                H2K = HyperellipticCurve(E2K.hyperelliptic_polynomials()[0])
                int_w1_b_f2 = H2K.coleman_integrals_on_basis(H2K(f2), H2K(f2))[1]*(1/2) ### KF2025
            if f2[1] != 0:
                f2alg_x = QQ(f2[0])
                try:
                    f2alg = E2.lift_x(f2alg_x)
                except ValueError:
                    polE2 = E2.defining_polynomial()
                    x2,y2,z2 = polE2.parent().gens()
                    polval = polE2(f2alg_x,y2,1)
                    L.<f2alg_y> = NumberField(PolynomialRing(QQ,"x")(polval[0,0,0] + x^2*polval[0,2,0]))
                    E2L = E2.change_ring(L)
                    f2alg = E2L.lift_x(f2alg_x)
                hf2 = -non_archimedean_local_height(f2alg, None, p, n)
            else:
                hf2 = 1/2*log(K(3*f2[0]^2 + 2*E2.a2()*f2[0] + E2.a4())) #by [BBM16, Lemma 4.1]
        else:
            mf2 = m2*f2
            Logf2 = 1/m2*Log2(-K(mf2[0]/mf2[1]))
            int_w1_b_f2 = int_w1_b(E2, f2, p, m2, n, fm = fm2, Dfm = Dfm2)
            hf2 = -2/m2^2*log(sigma2(-mf2[0]/mf2[1])/fm2(f2[0],f2[1]))
        int_w1bar_b_f1 = int_w1_b_f1 + c1*Logf1
        int_w1bar_b_f2 = int_w1_b_f2 + c2*Logf2

        #Series expansions of functions on E1
        x_in_disk_of_f1, y_in_disk_of_f1 = param_f1(xx, yy, a6)
        t = x_in_disk_of_f1.parent().gens()[0]
        x_f1_new = x_in_disk_of_f1(p*t)
        y_f1_new = y_in_disk_of_f1(p*t)
        w0_1 = x_f1_new.derivative()/(2*y_f1_new)
        w1_1 = x_f1_new*w0_1
        w0_1_int = w0_1.integral()
        log_near_f1 = Logf1 + w0_1_int
        w1_1_int = w1_1.integral()
        if f1[2] == 0:
            double1  = (w0_1*w1_1_int + t^(-1)).integral() + log(K(a6))/2 #last term to take into account
            #we are working with a non-normalised parameter; note: +t^(-1) before integrating equivalent to
            #ignoring -2*log(t) in h_nearf1.
        else:
            double1 = (w0_1*w1_1_int).integral()
        twice_double_int_near_f1 = c1*w0_1_int^2 + 2*double1
        h_nearf1 = hf1  + twice_double_int_near_f1  + 2*int_w1bar_b_f1*w0_1_int

        #Series expansions of functions on E2
        x_in_disk_of_f2, y_in_disk_of_f2 = param_f2(xx, yy, a0)
        if P[2] == 0:
            if f2[1] != y_in_disk_of_f2(0):
                y_in_disk_of_f2 = - y_in_disk_of_f2
                assert y_in_disk_of_f2(0) - f2[1] == 0, "Something is wrong in mapping the disk at infinity to E2"

        x_f2_new = x_in_disk_of_f2(p*t)
        y_f2_new = y_in_disk_of_f2(p*t)
        w0_2 = x_f2_new.derivative()/(2*y_f2_new)
        w1_2 = x_f2_new*w0_2
        w0_2_int = w0_2.integral()
        log_near_f2 = Logf2 + w0_2_int
        w1_2_int = w1_2.integral()
        if f2[2] == 0:
            double2  = (w0_2*w1_2_int + t^(-1)).integral() + log(K(a0))/2 #last term to take into account
            #we are working with a non-normalised parameter; note: +t^(-1) before integrating equivalent to
            #ignoring -2*log(t) in h_nearf2.
        else:
            double2 = (w0_2*w1_2_int).integral()
        twice_double_int_near_f2 = c2*w0_2_int^2 + 2*double2
        h_nearf2 = hf2 + twice_double_int_near_f2  + 2*int_w1bar_b_f2*w0_2_int

        #So on the minimal models:
        h_nearf1 = h_nearf1 - 1/6*log(K(delta1))
        h_nearf2 = h_nearf2 - 1/6*log(K(delta2))

        if f1[2] != 0 and f2[2] != 0:
            rho = h_nearf1 - h_nearf2 - 2*log(xx(p*t)/xx[0]) -2*log(xx[0]) - alpha1*log_near_f1^2 + alpha2*log_near_f2^2
        else:
            assert (f1[2] == 0 and xx == t^-1) or (f2[2] == 0 and  xx == t)
            rho = h_nearf1 - h_nearf2 - alpha1*log_near_f1^2 + alpha2*log_near_f2^2

        try:
            rho = rho.power_series()
        except AttributeError:
            pass

        rho_list.append(rho)

        M = rho.prec()
        epsilon = min([alpha1.valuation(),-2*m1.valuation(p), alpha2.valuation(), -2*m2.valuation(p)])
        N = M - RR(log(M)/log(p)).floor() - RR(log(M-1)/log(p)).floor() + epsilon

        for l in range(size_Omega):
            omega = Omega[l]
            rhoomega = rho - omega
            k = min(rhoomega[i].valuation(p) for i in range(M))
            rhoomega = (p^(-k)*rhoomega).truncate()
            rhoomega_new = 0
            deg = rhoomega.degree()
            if deg < M - 1:
                M = deg + 1
                N = M - RR(log(M)/log(p)).floor() - RR(log(M-1)/log(p)).floor() + epsilon
            for j in range(M):
                if rhoomega[j].valuation() >= N-k:
                    continue
                rhoomega_new += (rhoomega[j] + O(p^(N-k)))*t^j
            rhoomega = rhoomega_new
            NNk = min([rhoomega[i].precision_absolute() for i in range(rhoomega.degree())])
            if NNk < N-k:
                #print(D.index(P))
                #print("hmm, interesting loss of precision", N, k)
                N = NNk + k
            rhoomega_val = rhoomega.valuation()

            if rhoomega_val > 0:
                if rhoomega_val > 1:
                    assert rhoomega_val == 2, "A root of multiplicity > 2."
                    assert Q[0] == 0 or Q[1] == 0 or Q[2] == 0, "A double root at a point not fixed by automorphisms."
                    points[l].append(Q)
                else:
                    #val_rho = rhoomega(O(p^(N - k))).valuation()
                    val_rho = N - k
                    val_der = rhoomega.derivative()(O(p^(N - k))).valuation()
                    assert val_der < (val_rho/2).ceil(), "Hensel not applicable."
                    points[l].append(HK(xx(O(p^(val_rho - val_der + 1))), yy(O(p^(val_rho - val_der + 1)))))

            roots = list(gp.polrootspadic(rhoomega/(rhoomega.parent().0^rhoomega_val), p, 1))

            roots = [p*r + O(p^(N-k+1)) for r in roots if r.valuation(p) >= 0]
            for r in roots:
                val_rho = min([rhoomega(K(sage_eval('%s'%r))/p).valuation(), N-k])
                val_der = (rhoomega.derivative()(K(sage_eval('%s'%r))/p)).valuation()
                assert val_der < (val_rho/2).ceil(), "Hensel not applicable."
                roots[roots.index(r)] = r + O(p^(val_rho - val_der + 1))

            new_points = [HK(xx(K(sage_eval('%s'%t0))), yy(K(sage_eval('%s'%t0)))) for t0 in roots]
            points[l].extend(new_points)

    rational_points = [[] for i in range(size_Omega)]
    other_points = [[] for i in range(size_Omega)]
    for l in range(size_Omega):
        for P in points[l]:
            if P == H(0, 1, 0) or P == HK(0, 1, 0):
                rational_points[l].append(H(0, 1, 0))
                continue
            try:
                RP = H.lift_x(QQ(P[0]))
                if RP[1] - P[1] == 0:
                    rational_points[l].append(RP)
                elif RP[1] + P[1] == 0:
                    RP = H(RP[0], -RP[1])
                    rational_points[l].append(RP)
                else:
                    other_points[l].append(P)
            except ValueError:
                pol = algdep(P[0], 1)
                pol = PolynomialRing(QQ, "x")(pol)
                try:
                    RP = H.lift_x(pol.roots()[0][0])
                    if RP[1] - P[1] == 0:
                        rational_points[l].append(RP)
                    elif RP[1] + P[1] == 0:
                        RP = H(RP[0], -RP[1])
                        rational_points[l].append(RP)
                    else:
                        other_points[l].append(P)
                except ValueError:
                        other_points[l].append(P)

        assert(len(list(Set(rational_points[l])))) == len(rational_points[l])
        assert(len(list(Set(other_points[l])))) == len(other_points[l])

        if up_to_auto == False:
            rational_points_complete = []
            for P in rational_points[l]:
                rational_points_complete.extend([P,H(P[0],-P[1], P[2]), H(-P[0],P[1],P[2]),H(-P[0],-P[1],P[2])])
            other_points_complete = []
            for P in other_points[l]:
                other_points_complete.extend([P,HK(P[0],-P[1], P[2]), HK(-P[0],P[1],P[2]),HK(-P[0],-P[1],P[2])])
            rational_points[l] = list(Set(rational_points_complete))
            other_points[l] = list(Set(other_points_complete))
            ### added check for low-degree relations, KF2025. Change the second input to algdep to change degree.
            for P in other_points[l]:
                try:
                    F = algdep(P[0],2)
                    G = algdep(P[1],2)
                    Kb.<b> = NumberField(F)
                    Lc.<c> = NumberField(G)
                    if Kb.is_isomorphic(Lc) or (smallpol(F) and smallpol(G)):
                        print(F,G)
                        print("Found something?")
                except:
                    pass
        else:
            rational_points_auto = []
            for P in rational_points[l]:
                if H(P[0], -P[1], P[2]) in rational_points_auto or H(-P[0], P[1], P[2]) in rational_points_auto or H(-P[0], -P[1], P[2]) in rational_points_auto:
                    continue
                rational_points_auto.append(P)
            other_points_auto = []
            for P in other_points[l]:
                if HK(P[0], -P[1], P[2]) in other_points_auto or HK(-P[0], P[1], P[2]) in other_points_auto or HK(-P[0], -P[1], P[2]) in other_points_auto:
                    continue
                other_points_auto.append(P)
            rational_points[l] = list(Set(rational_points_auto))
            other_points[l] = list(Set(other_points_auto))
        rational_points[l].sort()
        other_points[l].sort()

    rational_points_new = list(set().union(*rational_points))
    other_points_new = list(set().union(*other_points))
    assert len(rational_points_new) == sum([len(rational_points[j]) for j in range(size_Omega)]), "Probably different omegas gave the same point because the precision is too low."
    assert len(other_points_new) == sum([len(other_points[j]) for j in range(size_Omega)]), "Probably different omegas gave the same point because the precision is too low."
    if omega_info == True:
        return rational_points, other_points
    else:
        rational_points_new.sort()
        other_points_new.sort()
        return rational_points_new, other_points_new