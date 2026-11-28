#!/usr/bin/env python3
"""Reproducible checks on the analytic countermodel; not a proof of its theorems.

The rational constant comparisons and dyadic ceiling values use exact integers.
The random continuous checks and finite general-integer checks use floating point
or mpmath and are expressly only smoke checks. The analytic proof is in the
accompanying Markdown file. Python 3 and mpmath are required.
"""

from __future__ import annotations

import math
import random

import mpmath as mp


def h_float(t: float) -> float:
    n = math.isqrt(int(t))
    return n + min(t - n * n, 1.0)


def f_mp(n: int) -> mp.mpf:
    if n == 0:
        return mp.mpf(0)
    t = mp.log(n, 2)
    j = int(mp.floor(mp.sqrt(t)))
    h = j + min(t - j * j, mp.mpf(1))
    return mp.mpf(n) * mp.power(2, -h / 16)


def dyadic_g_exact(t: int) -> int:
    """Return G(2**t) using exact integer arithmetic, t >= 0."""
    j = math.isqrt(t)
    h = j + (j * j != t)
    sixteenth_power = 1 << (16 * t - h)
    root = sixteenth_power
    for _ in range(4):
        root = math.isqrt(root)
    return root + (root**16 < sixteenth_power)


def main() -> None:
    mp.mp.dps = 70
    comparisons = {
        "4^(1/16) < 5/4": 4**17 < 5**16,
        "5^(15/16) > 4": 5**15 > 4**16,
        "2^(15/16) > 25/16": 2**15 * 16**16 > 25**16,
        "(5/3)^(15/16) > 25/16": 5**15 * 16**16 > 3**15 * 25**16,
        "3^(15/16) > 5/2": 3**15 * 2**16 > 5**16,
    }
    assert all(comparisons.values())
    print("All five rational-power constant comparisons checked exactly.")

    rng = random.Random(142)
    for _ in range(30000):
        a = rng.random() * 1e5
        b = rng.random() * 1e5
        assert h_float(a + b) <= h_float(a) + h_float(b) + 1e-9
        lo, hi = sorted((a, b))
        assert -1e-9 <= h_float(hi) - h_float(lo) <= hi - lo + 1e-9
    print("30000 random floating-point h checks passed (not a proof).")

    upper = 18000
    values = [0] + [int(mp.ceil(f_mp(n))) for n in range(1, upper + 1)]
    for n in range(upper):
        assert values[n + 1] - values[n] in (0, 1)
    tested = 0
    for m in range(1, 90):
        for span in range(1, 90):
            n = (2 * m - 1) * span
            assert values[n] >= values[m] * values[span]
            assert values[m] * (values[n + span] - values[n]) <= values[n]
            assert values[2 * m * span] >= values[m] * values[span]
            tested += 1
    print(f"{tested} finite high-precision local-modulus and product checks passed.")
    print("These general-integer values were computed numerically, not formally certified.")

    print("Exact integer dyadic evaluations; ratios displayed to 14 places:")
    for j in (2, 3, 4, 6, 8, 12):
        t = j * j
        g0 = dyadic_g_exact(t)
        g1 = dyadic_g_exact(t + 1)
        g2 = dyadic_g_exact(t + 2)
        print(f"j={j:2d}: ramp={g1 / g0:.14f}; plateau={g2 / g1:.14f}")
    print(f"Analytic ramp limit 2^(15/16) = {2 ** (15 / 16):.14f}")
    print(f"Analytic plateau limit = 2")
    print(f"Persistent profile defect = {(2 ** (1 / 16) - 1) / 2:.14f}")
    assert values[3] == 3
    print("Scope check: G(3)=3, whereas r_3(3)=2; G is a structural surrogate.")


if __name__ == "__main__":
    main()
