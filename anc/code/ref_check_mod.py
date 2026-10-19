# Referee re-implementation.
# Definitions taken from arXiv:2609.11806v1, Section 6:
#   T_n Chebyshev 1st kind; S linear, S(x^j) = T_{2j}(x);
#   i_m = 1 if 4|m, 2 if m = 2 mod 4;  P_{i_m-1} = x^{m/4} or T_{m/2};
#   P_{i+1} = S(P_i);  R_i = (P_i - P_{i-1})/(x-1)  (i >= i_m);
#   nu(F) = min 2-adic valuation of coefficients in the MONOMIAL basis.
# Arithmetic is done in (Z/2^64)[x] with numpy uint64 (wrap-around = reduction mod 2^64);
# all valuations that matter are < 64, which is checked (a value 64 means "unknown / >= 64").
import sys
import numpy as np

K = 64
U64 = np.uint64

def nu_int(c):
    c = int(c)
    if c == 0:
        return K
    return (c & -c).bit_length() - 1

def nu_vec(a):
    a = a[a != 0]
    if a.size == 0:
        return K
    low = a & (~a + U64(1))          # lowest set bit
    return int(np.log2(low.astype(np.float64)).min().round())

def even_cheb_matrix(J):
    """E[j, k] = coefficient of x^(2k) in T_{2j}(x) (mod 2^64), 0 <= j,k <= J.
    Built from the plain recurrence T_{n+1} = 2x T_n - T_{n-1}, keeping only even n:
    we carry T_{2j} and T_{2j+1} as full x-polynomials of length 2J+2 (mod 2^64)."""
    E = np.zeros((J + 1, J + 1), dtype=U64)
    L = 2 * J + 2
    a = np.zeros(L, dtype=U64); a[0] = 1             # T_0
    b = np.zeros(L, dtype=U64); b[1] = 1             # T_1
    two = U64(2)
    E[0, :] = a[0::2][:J + 1]
    n = 1
    while n < 2 * J:
        # T_{n+1} = 2x T_n - T_{n-1}
        c = np.zeros(L, dtype=U64)
        c[1:] = two * b[:-1]
        c = c - a
        a, b = b, c
        n += 1
        if n % 2 == 0:
            assert not np.any(b[1::2]), "odd coefficient in even Chebyshev"
            E[n // 2, :] = b[0::2][:J + 1]
    return E

def S_apply(P, E):
    """P = coefficient vector in x (index = power). Returns S(P) as x-vector."""
    J = len(P) - 1
    # memory-friendly matrix-vector product mod 2^64
    s = np.zeros(J + 1, dtype=U64)
    for j in range(J + 1):
        if P[j]:
            s += P[j] * E[j, :J + 1]
    out = np.zeros(2 * J + 1, dtype=U64)
    out[0::2] = s
    return out

def div_xm1(D):
    """exact division of D by (x-1) in (Z/2^64)[x]: q_k = sum_{l>k} d_l."""
    assert int(D.sum(dtype=U64)) == 0, "not divisible by x-1"
    rev = np.cumsum(D[::-1], dtype=U64)[::-1]   # rev[k] = sum_{l>=k} d_l
    return rev[1:].copy()

def sub(a, b):
    n = max(len(a), len(b))
    r = np.zeros(n, dtype=U64)
    r[:len(a)] += a
    r[:len(b)] -= b
    return r

def start_poly(m, E):
    if m % 4 == 0:
        P = np.zeros(m // 4 + 1, dtype=U64); P[m // 4] = 1
        return 1, P
    # T_{m/2}: read from plain recurrence directly
    n = m // 2
    a = np.zeros(n + 2, dtype=U64); a[0] = 1
    b = np.zeros(n + 2, dtype=U64); b[1] = 1
    if n == 1:
        return 2, b[:2].copy()
    for _ in range(n - 1):
        c = np.zeros(n + 2, dtype=U64); c[1:] = U64(2) * b[:-1]; c = c - a
        a, b = b, c
    return 2, b[:n + 1].copy()

def run(m, imax, E):
    im, Pprev = start_poly(m, E)
    rows = []
    for i in range(im, imax + 1):
        P = S_apply(Pprev, E)
        R = div_xm1(sub(P, Pprev))
        v = nu_vec(R)
        r0 = int(R.sum(dtype=U64))
        r1 = int((R * np.arange(len(R), dtype=U64)).sum(dtype=U64))
        rows.append((i, v, nu_int(r1), nu_int(r0)))
        Pprev = P
    return im, rows

def nu2(n):
    return (n & -n).bit_length() - 1

def predicted(m, i):
    if m % 4 == 2:
        return 3 * i - 8
    return 3 * i + 2 * nu2(m) - 9

if __name__ == "__main__":
    mmax = int(sys.argv[1]); extra = int(sys.argv[2]); degcap = int(sys.argv[3])
    # choose imax per m so that the largest degree of P_{imax-1} <= degcap
    plans = []
    Jneed = 0
    for m in range(2, mmax + 1, 2):
        im = 1 if m % 4 == 0 else 2
        d0 = m // 4 if m % 4 == 0 else m // 2          # deg P_{im-1}
        imax = im + extra
        while imax > im + 2 and d0 * 2 ** (imax - im) > degcap:
            imax -= 1
        plans.append((m, imax))
        Jneed = max(Jneed, d0 * 2 ** (imax - im))
    print("building even-Chebyshev matrix, J =", Jneed, flush=True)
    E = even_cheb_matrix(Jneed)
    tot = bad = 0
    for m, imax in plans:
        im, rows = run(m, imax, E)
        for k, (i, v, n1, n0) in enumerate(rows):
            if i > im:
                ok = (v < K - 4) and n1 == v and n0 == v + 1 and v == predicted(m, i)
                if k + 1 < len(rows):
                    ok = ok and rows[k + 1][1] == v + 3
                tot += 1
                if not ok:
                    bad += 1
                    print("FAIL", m, rows[k], rows[k + 1] if k + 1 < len(rows) else None, "pred", predicted(m, i))
        if m <= 20 or m % 40 == 0 or m in (64, 128, 192):
            print("m=%d i_m=%d [i, v_i, nu(R'(1)), nu(R(1))]:" % (m, im), rows, flush=True)
    print("checked (m,i) pairs with i > i_m:", tot, " failures:", bad)
