p = 8444461749428370424248824938781546531375899335154063827935233455917409239041
F = GF(p)
z = F(2841681278031794617739547238867782961338435681360110683443920362658525667816)

def table_based_findSqRoot_sarkar(u):
    """Implements decaf377 Sarkar 2020 based method"""

    if u % p == 1:  # Trivial case
        return 1

    # Euler's criterion. If u does not have a square, then we run the
    # algorithm on z * u
    if pow(u, (p - 1)//2 , p) != 1:
        u *= z 

    # First, solve p - 1 = 2**n * m where n >= 1 and m odd
    n = 47
    m = (p - 1) // 2**n

    # Next, compute g = z^m where z is a quadratic non-residue in Fp
    g = z ** m

    # Finally, define l_0... l_{k-1} > 0 such that l_0 + .. + l_{k-1} = n-1
    k = 6
    l = [7, 7, 8, 8, 8, 8]

    # g powers lookup table: Indexed by exponent
    g_lookup_table = {}
    powers_needed_for_t_i = [1, 8, 9, 16, 17, 23, 24, 25, 31, 32, 33, 39, 40]
    powers_needed_for_t_k_over_2 = [0, 7, 14, 22, 30, 38]
    for power_of_two in powers_needed_for_t_i + powers_needed_for_t_k_over_2:
        for nu in range (0, 2**8 - 1):
            exponent = nu * F(2) ** power_of_two
            g_lookup_table.update({exponent: g**exponent})

    # s lookup tables: Indexed by g^{\nu * 2^{n-l}}
    s_2345_lookup_table = {}
    exponent = n - l[2]
    for nu in range(0, 2**8 - 1):
        s_2345_lookup_table.update({g**(-1 * nu * 2**exponent): nu})

    s_01_lookup_table = {}
    exponent = n - l[0]
    for nu in range(0, 2**8 - 1):
        s_01_lookup_table.update({g**(-1 * nu * 2**exponent): nu})

    v = u**((m - 1)//2)

    x = u * v * v  # Such that x = u**m

    x5 = x
    x4 = x5 ** (2**8)
    x3 = x4 ** (2**8)
    x2 = x3 ** (2**8)
    x1 = x2 ** (2**8)
    x0 = x1 ** (2**7)

    # i = 0
    t_0 = 0
    gamma_0 = F(1)  # Since g^0 = 1
    alpha_0 = x0 * gamma_0
    q_0 = s_01_lookup_table[alpha_0]
    s_0 = q_0 * F(2) ** (n - l[0])

    # i = 1
    t_1 = s_0 // 2**7

    gamma_1 = g_lookup_table[t_1]
    alpha_1 = x1 * gamma_1
    q_1 = s_01_lookup_table[alpha_1]
    s_1 = q_1 * F(2) ** (n - l[1])

    # i = 2
    a_1 = s_1 // 2**8
    b_1 = t_1 // 2**8
    t_2 = a_1 + b_1
    gamma_2 = g_lookup_table[a_1] * g_lookup_table[b_1]
    alpha_2 = x2 * gamma_2
    s_2 = s_2345_lookup_table[alpha_2] * 2**(n-l[2])

    # i = 3
    a_2 = s_2 // 2**8
    # t_2 was defined as (a_1 + b_1)
    # We split t_2 into two components b_2 and c_2
    # such that we can do the lookups in the g table
    b_2 = a_1 // 2**8
    c_2 = b_1 // 2**8
    t_3 = a_2 + b_2 + c_2
    gamma_3 = g_lookup_table[a_2] * g_lookup_table[b_2] * g_lookup_table[c_2]
    alpha_3 = x3 * gamma_3
    s_3 = s_2345_lookup_table[alpha_3] * 2**(n-l[3])

    # i = 4
    a_3 = s_3 // 2**8
    # t_3 was defined as (a_2 + b_2 + c_3) so we split into components as above
    b_3 = a_2 // 2**8
    c_3 = b_2 // 2**8
    d_3 = c_2 // 2**8
    t_4 = a_3 + b_3 + c_3 + d_3
    gamma_4 = g_lookup_table[a_3] * g_lookup_table[b_3] * g_lookup_table[c_3] * g_lookup_table[d_3]
    alpha_4 = x4 * gamma_4
    s_4 = s_2345_lookup_table[alpha_4] * 2**(n-l[4])

    # i = 5
    a_4 = s_4 // 2**8
    # t_4 was defined as (a_3 + b_3 + c_3 + d_3)
    b_4 = a_3 // 2**8
    c_4 = b_3 // 2**8
    d_4 = c_3 // 2**8
    e_4 = d_3 // 2**8
    t_5 = a_4 + b_4 + c_4 + d_4 + e_4
    gamma_5 = g_lookup_table[a_4] * g_lookup_table[b_4] * g_lookup_table[c_4] * g_lookup_table[d_4] * g_lookup_table[e_4]
    alpha_5 = x5 * gamma_5
    s_5 = s_2345_lookup_table[alpha_5] * 2**(n-l[5])

    t = s_5 + t_5
    # Break t up so we can do k lookups into g table, i.e.: t = s_5 + (a_4 + b_4 + c_4 + d_4 + e_4)
    # Computes $g^{t//2}$
    gamma = g_lookup_table[s_5//2] * g_lookup_table[a_4//2] * g_lookup_table[b_4//2] * g_lookup_table[c_4//2] * g_lookup_table[d_4//2] * g_lookup_table[e_4//2]
    y = u * v * gamma
    return y


# If a square root exists, the algorithm must return sqrt(x)
for quadratic_residue in [F(1), F(4), F(10), F(83), F(94)]:
    res = table_based_findSqRoot_sarkar(quadratic_residue)
    assert res**2 == quadratic_residue

# If a square root does not exist, the algorithm must return sqrt(z * x)
for quadratic_non_residue in [F(11), F(17), F(51), F(99)]:
    res = table_based_findSqRoot_sarkar(quadratic_non_residue)
    assert res**2 == quadratic_non_residue * z
