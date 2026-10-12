"""Prototype: arccos rounded to nearest using only IEEE +,-,*,/ (no fused multiply-add, no libm in the result)."""
import math

_SPLIT = 134217729.0  # 2**27 + 1
# pi/2 as three doubles (hi + mid + lo), from the binary expansion of pi.
_PIO2_1 = 1.5707963267948966
_PIO2_2 = 6.123233995736766e-17
_PIO2_3 = -1.4973849048591698e-33
_PI_1 = 3.141592653589793
_PI_2 = 1.2246467991473532e-16


def two_sum(a, b):
    s = a + b
    bb = s - a
    return s, (a - (s - bb)) + (b - bb)


def two_prod(a, b):
    p = a * b
    c = _SPLIT * a
    ah = c - (c - a)
    al = a - ah
    c = _SPLIT * b
    bh = c - (c - b)
    bl = b - bh
    return p, ((ah * bh - p) + ah * bl + al * bh) + al * bl


def dd_add(ah, al, bh, bl):
    s, e = two_sum(ah, bh)
    e += al + bl
    return two_sum(s, e)


def dd_mul(ah, al, bh, bl):
    p, e = two_prod(ah, bh)
    e += ah * bl + al * bh
    return two_sum(p, e)


def dd_div(ah, al, bh, bl):
    q1 = ah / bh
    ph, pl = dd_mul(bh, bl, q1, 0.0)
    rh, rl = dd_add(ah, al, -ph, -pl)
    q2 = rh / bh
    ph, pl = dd_mul(bh, bl, q2, 0.0)
    rh, rl = dd_add(rh, rl, -ph, -pl)
    q3 = rh / bh
    qh, ql = two_sum(q1, q2)
    return dd_add(qh, ql, q3, 0.0)


def sin_cos_dd(y):
    """sin(y), cos(y) as double-doubles for a double y in [0, pi]."""
    k = 0 if y < 0.7853981633974483 else (1 if y < 2.356194490192345 else 2)
    rh, rl = two_sum(y, -k * _PIO2_1)
    rh, rl = dd_add(rh, rl, -k * _PIO2_2, -k * _PIO2_3)
    r2h, r2l = dd_mul(rh, rl, rh, rl)
    # Taylor series in r, |r| <= pi/4
    sh, sl = rh, rl
    th, tl = rh, rl
    ch, cl = 1.0, 0.0
    uh, ul = 1.0, 0.0
    for n in range(1, 16):
        uh, ul = dd_mul(uh, ul, r2h, r2l)
        uh, ul = dd_div(uh, ul, -float((2 * n - 1) * (2 * n)), 0.0)
        ch, cl = dd_add(ch, cl, uh, ul)
        th, tl = dd_mul(th, tl, r2h, r2l)
        th, tl = dd_div(th, tl, -float((2 * n) * (2 * n + 1)), 0.0)
        sh, sl = dd_add(sh, sl, th, tl)
    if k == 0:
        return sh, sl, ch, cl
    if k == 1:  # sin(r + pi/2) = cos r ; cos(r + pi/2) = -sin r
        return ch, cl, -sh, -sl
    return -sh, -sl, -ch, -cl


def acos_rn(x, seed=None):
    if x >= 1.0:
        return 0.0
    if x <= -1.0:
        return _PI_1
    y = math.acos(x) if seed is None else seed
    for _ in range(8):
        sh, sl, ch, cl = sin_cos_dd(y)
        fh, fl = dd_add(ch, cl, -x, 0.0)
        qh, ql = dd_div(fh, fl, sh, sl)
        y_next, low = two_sum(y, qh)
        y_next, low = two_sum(y_next, low + ql)
        if y_next == y:
            break
        y = y_next
    return y


if __name__ == "__main__":
    import random
    import sys

    import mpmath

    mpmath.mp.prec = 400
    rng = random.Random(0)
    n = int(sys.argv[1])
    xs = [rng.uniform(-1, 1) for _ in range(n)] + [1 - rng.random() * 10.0 ** -rng.uniform(1, 15) for _ in range(n // 4)] + [-1 + rng.random() * 10.0 ** -rng.uniform(1, 15) for _ in range(n // 4)] + [rng.uniform(-1e-3, 1e-3) for _ in range(n // 4)]
    bad = bad_libm = seed_dep = 0
    for x in xs:
        exact = float(mpmath.acos(mpmath.mpf(x)))
        got = acos_rn(x)
        bad += got != exact
        bad_libm += math.acos(x) != exact
        wrong_seed = math.nextafter(math.acos(x), 0.0 if rng.random() < 0.5 else 4.0)
        seed_dep += acos_rn(x, wrong_seed) != exact
        seed_dep += acos_rn(x, math.acos(x) * (1 + 1e-9)) != exact
    print(f"inputs {len(xs)}: acos_rn wrong {bad}; wrong from a perturbed seed {seed_dep}; this libm's acos not correctly rounded {bad_libm}")
