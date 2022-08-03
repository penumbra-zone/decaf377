p = 8444461749428370424248824938781546531375899335154063827935233455917409239041
F = GF(p)
z = F(2841681278031794617739547238867782961338435681360110683443920362658525667816)
# First, solve p - 1 = 2**n * m where n >= 1 and m odd
n = 47
m = (p - 1) / 2**n

# Next, compute g = z^m where z is a quadratic non-residue in Fp
g = z ** m

# Finally, define l_0... l_{k-1} > 0 such that l_0 + .. + l_{k-1} = n-1
k = 6
l = [7, 7, 8, 8, 8, 8]
w = 8

# g powers lookup table: Indexed by power of two, then nu
powers_needed_for_t_i = [0, 8, 16, 24, 32]
powers_needed_for_t_k_over_2 = [40]
# This is Table 1 and 2 from Sarkar 2020 (combined)
gtab = {}
for power_of_two in powers_needed_for_t_i + powers_needed_for_t_k_over_2:
    gtab_i = []
    for nu in range(0, 2**w):
        exponent = nu * F(2) ** power_of_two
        gtab_i.append(g**exponent)
    gtab[power_of_two] = gtab_i

# s lookup table: Indexed by g^{\nu * 2^{n-l}}
# This is Table 3 from Sarkar 2020
s_lookup_table = {}
for nu in range(0, 2**w):
    s_lookup_table[g**(-1 * nu * 2**(n-w))] = nu


def sqrt_ratio(num, den):
    s = den**(2**n - 1)
    t = s**2 * den
    w = (num * t)**((m-1)/2) * s

    v = w * den;
    uv = w * num;

    assert v == (num / den)**((m - 1) / 2)
    assert uv == (num / den)**((m + 1) / 2)

    return table_based_findSqRoot_sarkar(uv, v)


def table_based_findSqRoot_sarkar(uv, v):
    """Implements decaf377 Sarkar 2020 based method"""
    x = uv * v  # Such that x = u**m

    x5 = x
    x4 = x5 ** (2**l[5])
    x3 = x4 ** (2**l[4])
    x2 = x3 ** (2**l[3])
    x1 = x2 ** (2**l[2])
    x0 = x1 ** (2**l[1])

    # i = 0
    # Here we want to look up s_0 = q_0 * g**{n-7}, but our table has
    # powers of g**{n-8}, so we're actually looking up q_prime = 2*q_0.
    q_0_prime = s_lookup_table[x0]  # Since x0 = alpha0
    t = q_0_prime

    # i = 1
    alpha_1 = x1 * gtab[32][t]
    #breakpoint()
    q_1_prime = s_lookup_table[alpha_1]
    # The left shift values come from the final expression for t:
    # t_6 = q_0_prime + q_1_prime * 2^7 + ... + q_5 * 2^39
    t += q_1_prime << 7

    # i = 2
    alpha_2 = x2 * gtab[24][t & 0xFF] * gtab[32][t >> 8]
    assert (t >> 8) & 0xFF == q_1_prime // 2
    q_2 = s_lookup_table[alpha_2]
    t += q_2 << 15

    # i = 3
    alpha_3 = x3 * gtab[16][t & 0xFF] * gtab[24][(t >> 8) & 0xFF] * gtab[32][(t >> 16) & 0xFF]
    assert (t >> 16) & 0xFF == q_2 // 2
    q_3 = s_lookup_table[alpha_3]
    t += q_3 << 23

    # i = 4
    alpha_4 = x4 * gtab[8][t & 0xFF] * gtab[16][(t >> 8) & 0xFF] * gtab[24][(t >> 16) & 0xFF] * gtab[32][(t >> 24) & 0xFF]
    assert (t >> 24) & 0xFF == q_3 // 2
    q_4 = s_lookup_table[alpha_4]
    t += q_4 << 31

    # i = 5
    alpha_5 = x5 * gtab[0][t & 0xFF] * gtab[8][(t >> 8) & 0xFF] * gtab[16][(t >> 16) & 0xFF] * gtab[24][(t >> 24) & 0xFF] * gtab[32][(t >> 32) & 0xFF]
    assert (t >> 32) & 0xFF == q_4 // 2
    q_5 = s_lookup_table[alpha_5]
    t += q_5 << 39

    assert t == q_0_prime + q_1_prime * 2**7 + q_2 * 2**15 + q_3 * 2**23 + q_4 * 2**31 + q_5 * 2**39  # Lemma 4 assertion

    t = (t + 1) >> 1;

    # Take 8 bits at a time, e.g. (t & 0xFF) is taking the last 8 bits of t to yield a value from 0-255, which are the allowed values in each g lookup table
    gamma = gtab[0][t & 0xFF] * gtab[8][(t >> 8) & 0xFF] * gtab[16][(t >> 16) & 0xFF] * gtab[24][(t >> 24) & 0xFF] * gtab[32][(t >> 32) & 0xFF] * gtab[40][(t >> 40)]
    y = uv * gamma

    if q_0_prime % 2 != 0:
        y *= z**((1-m) / 2)

    return y


def test_sqrt(n):
    for _ in range(n):
        num = F.random_element()
        den = F(1)
        u = num / den

        res = sqrt_ratio(num, den)
        if u.is_square():
            assert res**2 == u
        else:
            assert res**2 == u * z


#test_sqrt(10000)
test_sqrt(100)