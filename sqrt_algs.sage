def eulers_criterion(n, p):
    if n % p == 0:  # Trivial case
        return True
    else:
        return pow(n, (p - 1)//2, p) == 1


def CMOV(a, b, c):
    """
    If c is False, CMOV returns a, otherwise it returns b.

    Used by the definition of constant-time Tonelli Shanks in [0].

    [0] https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/

    TODO: needs to be constant time too
    """
    if not c:
        return a
    else: 
        return b



def precompute_ts(p):
    """
    Precompute step taken from [0]
    
    [0] https://github.com/cfrg/draft-irtf-cfrg-hash-to-curve/commit/a47caf6a541e59e5e636fedd6fa0d45230bc09a1
    """

    c1 = 0
    c2 = p - 1
    while c2 % 2 == 0:
        c2 = c2 // 2
        c1 += 1
    
    c3 = (c2 - 1) / 2
    c4 = 1
    while eulers_criterion(c4, p):
        c4 += 1
    
    c5 = pow(c4, c2, p)

    print('QNR found: ', c4)

    return (c1, c2, c3, c4, c5)


def ct_sqrt_tonelli_shanks(x, p):
    """
    Constant time Tonelli-Shanks. Finds the square root of a quadratic residue x
    for a finite field of characteristic p and order q = p^m [0].

    [0] Appendix I.4 https://datatracker.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/
    """

    # Define constants. This precompute step should be done and the resulting constants
    # hardcoded for each curve.
    c1, c2, c3, c4, c5 = precompute_ts(p)

    # Procedure.
    z = pow(x, c3, p)
    t = z * z
    t = t * x
    z = z * x
    b = t
    c = c5
    for i in reversed(range(2, c1+1)):
        for j in range(1, i-2 + 1):
            b = b * b

        e = b == 1
        zt = z * c
        z = CMOV(zt, z, e)
        c = c * c
        tt = t * c
        t = CMOV(tt, t, e)
        b = t

    return z


def sqrt_tonelli_shanks(n, p):
    """
    Find square root of n mod p for prime p == 1 % 4
    (if p == 3 % 4 there is an explicit formula and this algorithm is not needed).
    """
    if n % p == 0:  # Trivial case
        return 0
    
    # Check if n is a quadratic residue, only proceed if it is
    if not eulers_criterion(n, p):
        return None

    # Step 1: Factor out powers of 2 to find Q and S such that p - 1 = Q2^S with Q odd
    Q = p - 1
    S = 0
    while Q % 2 == 0:
        S += 1
        Q //= 2

    # Step 2: Find a z in Fp which is a quadratic residue
    z = 2
    while eulers_criterion(z, p):
        z += 1

    # Step 3: Define M, c, t, R
    M = S
    c = pow(z, Q, p)
    t = pow(n, Q, p)
    R = pow(n, (Q + 1)//2, p)

    # Step 4: Loop until we find a solution
    while t != 1:
        if t == 0:
            return 0

        if t == 1:
            return R

        # Use repeated squaring to find the least i, 0 < i < M such that
        # t^(2^i) == 1
        i = 0
        lhs = t**(2**i)  # i.e. t since i=0
        while lhs != 1:
            i += 1
            lhs = (lhs ** 2) % p

        exponent = 2 ** (M - i - 1)
        b = pow(c, exponent, p)
        M = i
        c = (b**2) % p
        t = (t * b**2) % p
        R = (R * b) % p

    return R


def findSqRoot_sarkar(u, p, z):
    """findSqRoot from Algorithm 1 in https://eprint.iacr.org/2020/1407.pdf"""

    # Setup for our choice of p

    # First, solve p - 1 = 2**n * m where n >= 1 and m odd
    m = 1
    n = 1
    while  p - 1 != 2 ** n * m:
        m += 2  # Since m must be odd
        if p - 1 == 2 ** n * m:
            break
        n += 1

    # Next, solve g = z^m where z is a quadratic non-residue in Fp
    # TODO: Determine best choice of qnr here
    g = pow(z, m, p)

    # Finally, define l_0... l_{k-1} > 0 such that l_0 + .. + l_{k-1} = n-1
    l = []
    while sum(l) != n - 1:
        l.append(1)  # Check this
    k = len(l)

    # Line 1 in the algorithm begins here
    v = pow(u, (m - 1)//2, p)

    if n == 1:
        y = u * v
        return y
    
    x = u * pow(v, 2, p)  # Such that x = u**m

    # Lookup table creation, step 5
    x_lookup = []
    i = 0
    for i in range(k):
        exponent = 2 ** (n - 1 - (sum(l[:i+1])))
        x_lookup.append(pow(x, exponent, p))

    s = 0
    t = 0
    for i in range(0, k):
        t = (s+t) // 2**l[i]
        gamma = pow(g, t, p)
        alpha = x_lookup[i] * gamma
        s = eval_sarkar(alpha, n, g, p)

    t = s + t

    gamma = pow(g, t//2, p)
    y = u * v * gamma
    return y
       

def eval_sarkar(alpha, n, g, p):
    """eval from Algorithm 1 in https://eprint.iacr.org/2020/1407.pdf"""
    delta = alpha
    s = 0

    while delta != 1:
        i = find_sarkar(delta, p)
        s = s + pow(2, n - 1 - i, p)
        
        if i > 0:
            exponent = 2 ** (n - 1 - i)
            delta *= pow(g, exponent, p)
        else:
            delta *= -1

    return s


def find_sarkar(delta, p):
    """find from Algorithm 1 in https://eprint.iacr.org/2020/1407.pdf"""
    mu = delta
    i = 0

    while mu != -1:
        mu = pow(mu, 2, p)
        i += 1
    
    return i


def test_sqrt():
    assert sqrt_tonelli_shanks(5, 41) == 28
    # 3 is a QNR for F41
    assert findSqRoot_sarkar(5, 41, 3) == 28
    # The constant-time variant derives a QNR
    assert ct_sqrt_tonelli_shanks(5, 41) == 28

    # BLS12-377
    p_bls12_377 = 8444461749428370424248824938781546531375899335154063827935233455917409239041
    assert ct_sqrt_tonelli_shanks(1, p_bls12_377) == 1


test_sqrt()