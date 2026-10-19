# Exact (big-integer) cross-check with python-flint, independent of ref_check_mod.py:
#  - T_n from flint's fmpz_poly.chebyshev_t (cross-checked against the 3-term recurrence),
#  - S(P) = sum_j p_j T_{2j} summed literally,
#  - nu in the monomial basis, no modular reduction anywhere.
# Also checks the proof's lemmas symbolically: closed forms for Theta~(t^k), part (a),
# the low-order table (b), base cases B1/B2.
import sys
from flint import fmpz_poly, fmpz

X = fmpz_poly([0, 1])

def nu_int(c):
    c = int(c)
    if c == 0:
        return 10**9
    return (c & -c).bit_length() - 1

def nu_poly(F):
    return min((nu_int(c) for c in F.coeffs() if int(c) != 0), default=10**9)

_T = {}
def T(n):
    if n not in _T:
        _T[n] = fmpz_poly.chebyshev_t(n)
    return _T[n]

# cross-check flint's chebyshev_t against the defining recurrence for n <= 300
a, b = fmpz_poly([1]), X
assert T(0) == a and T(1) == b
for n in range(2, 301):
    a, b = b, 2 * X * b - a
    assert T(n) == b, n
print("T_n (flint) == recurrence for n <= 300")

def S(P):
    r = fmpz_poly([0])
    for j, c in enumerate(P.coeffs()):
        if int(c) != 0:
            r += c * T(2 * j)
    return r

XM1 = fmpz_poly([-1, 1])

def exdiv(A, B):
    q, r = divmod(A, B)
    assert r == 0
    return q

def Theta(R):
    return exdiv(S(XM1 * R), XM1)

def shift(F):
    """F(1+t) as fmpz_poly in t"""
    return F(fmpz_poly([1, 1]))

def run(m, imax):
    im = 1 if m % 4 == 0 else 2
    Pprev = X ** (m // 4) if m % 4 == 0 else T(m // 2)
    rows = []
    Rprev = None
    for i in range(im, imax + 1):
        P = S(Pprev)
        R = exdiv(P - Pprev, XM1)
        if Rprev is not None:
            assert R == Theta(Rprev)          # Lemma 6.1 recursion (exact)
        rows.append((i, nu_poly(R), nu_int(R.derivative()(1)), nu_int(R(1))))
        Pprev, Rprev = P, R
    return im, rows

def nu2(n):
    return (n & -n).bit_length() - 1

def predicted(m, i):
    return 3 * i - 8 if m % 4 == 2 else 3 * i + 2 * nu2(m) - 9

if __name__ == "__main__":
    mmax = int(sys.argv[1]); extra = int(sys.argv[2])
    # ---------- the conjecture, exactly ----------
    tot = bad = 0
    for m in range(2, mmax + 1, 2):
        im, rows = run(m, (1 if m % 4 == 0 else 2) + extra)
        for k, (i, v, n1, n0) in enumerate(rows):
            if i > im:
                tot += 1
                ok = n1 == v and n0 == v + 1 and v == predicted(m, i)
                if k + 1 < len(rows):
                    ok = ok and rows[k + 1][1] == v + 3
                if not ok:
                    bad += 1; print("FAIL", m, rows)
        if m <= 12 or m in (16, 32, 48, 64):
            print(m, rows, flush=True)
    print("EXACT: checked (m,i) pairs:", tot, "failures:", bad)

    # ---------- lemma: closed forms for Theta~(t^k) ----------
    t = fmpz_poly([0, 1])
    two_plus_t = fmpz_poly([2, 1])
    Upoly = 2 * t * two_plus_t                      # U = 2t(2+t)
    onepU = 1 + Upoly
    bad_l = 0
    KMAX = 60
    for k in range(0, KMAX + 1):
        lhs = shift(Theta(XM1 ** k))                # Theta~(t^k) written in t
        if k % 2 == 1:
            l = (k + 1) // 2
            rhs = 4 ** l * t ** (l - 1) * two_plus_t ** l * T(l)(onepU)
        else:
            l = k // 2
            D = T(l + 1)(onepU) - T(l)(onepU)       # (T_{l+1}-T_l)(1+U), divisible by U
            Wq = exdiv(D, Upoly)
            rhs = 2 * 4 ** l * t ** l * two_plus_t ** (l + 1) * Wq
        if lhs != rhs:
            bad_l += 1; print("closed form fails k=", k)
        if nu_poly(lhs) < k + 1:
            bad_l += 1; print("(a) fails k=", k)
        c = lhs.coeffs() + [0, 0]
        exp01 = {0: (4, 2), 1: (8, 36), 2: (0, 96), 3: (0, 64)}.get(k, (0, 0))
        if (int(c[0]), int(c[1])) != exp01:
            bad_l += 1; print("(b) fails k=", k, c[:2])
    print("Theta~(t^k): closed forms, (a), (b) checked for k <=", KMAX, " failures:", bad_l)
    print("Theta~(t) =", shift(Theta(XM1)))

    # ---------- (T_{l+1}-T_l)(1+u) in u Z[u] ----------
    u = fmpz_poly([0, 1])
    assert all(int((T(l + 1)(1 + u) - T(l)(1 + u))(0)) == 0 for l in range(0, 200))
    print("(T_{l+1}-T_l)(1+u) has zero constant term for l < 200")

    # ---------- base cases ----------
    bad_b = 0
    for m in range(2, 4 * 600 + 1, 2):
        if m % 4 == 2:
            n = m // 2
            R2_1 = 4 * n * n * (n * n + 2) // 3 - n * n      # predicted R_2(1)
            if m <= 400:
                im, rows = None, None
                P1 = T(n); P2 = S(P1); R2 = exdiv(P2 - P1, XM1)
                if int(R2(1)) != R2_1: bad_b += 1; print("R_2(1) formula fails", m)
            if R2_1 % 2 == 0: bad_b += 1; print("B1 parity fails", m)
        elif m % 8 == 4:
            n = m // 4
            if (n * (4 * n - 1)) % 2 == 0: bad_b += 1
            if m <= 400:
                R1 = exdiv(T(2 * n) - X ** n, XM1)
                if int(R1(1)) != n * (4 * n - 1): bad_b += 1; print("R_1(1) fails", m)
        else:  # 8 | m
            n = m // 4
            if m > 1200: continue
            Q = exdiv(T(2 * n) - 1, XM1)
            v = 2 * nu2(n) + 1
            Qt = shift(Q).coeffs()
            q0, q1 = int(Qt[0]), int(Qt[1])
            okQ = nu_poly(Q) == v and nu_int(q1) == v and nu_int(q0) == v + 1 \
                and ((q0 >> (v + 1)) + (q1 >> v)) % 4 == 2
            if m <= 600:
                R1 = exdiv(T(2 * n) - X ** n, XM1)
                R2 = Theta(R1)
                okR = R2 == Theta(Q) - Q
                R2t = shift(R2).coeffs()
                r0, r1 = int(R2t[0]), int(R2t[1])
                okR = okR and nu_poly(R2) == v and nu_int(r1) == v and nu_int(r0) == v + 1 \
                    and ((r0 >> (v + 1)) + (r1 >> v)) % 4 == 2
            else:
                okR = True
            if not (okQ and okR):
                bad_b += 1; print("B2 fails m=", m, okQ, okR)
    print("base cases B1 (m=2 mod 4 up to 2400, m=4 mod 8), B2 (8|m up to 1200 for Q, 600 for R_2): failures", bad_b)
