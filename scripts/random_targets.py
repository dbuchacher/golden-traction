"""Random-target control for the address form  O = phi^(p + q*phi + s1/phi^n1 + s2/phi^n2).

Fits log-uniform random numbers with the same form and reports the error, so the precision on real
observables can be compared against what the form gives any number. The depth set approximates Null
Theory's B-span: non-negative combinations of {2,3,4,5,7,8,11,13,23} up to 30, plus unit shifts. It does
not apply the KFP selection rules, which narrow the choices; running the real pipeline on random targets
is the test that settles it.
"""
import bisect
import math
import random

phi = (1 + 5 ** 0.5) / 2
lp = math.log(phi)

B = [2, 3, 4, 5, 7, 8, 11, 13, 23]
span = {0}
for _ in range(6):
    span |= {a + b for a in span for b in B if a + b <= 30}
span |= {n + 1 for n in span if n + 1 <= 30}
depths = sorted(n for n in span if n >= 2)
atoms = sorted({s / phi ** n for n in depths for s in (1, -1)})
corrections = sorted({a + b for a in atoms for b in atoms if abs(a + b) < 1} | set(atoms) | {0.0})


def best_error(x, qmax):
    """Smallest |log_phi O - address| over |q| <= qmax, as a fractional error in O."""
    err = math.inf
    for q in range(-qmax, qmax + 1):
        r0 = x - q * phi
        p = round(r0)
        for pp in (p - 1, p, p + 1):
            r = r0 - pp
            i = bisect.bisect_left(corrections, r)
            for j in (i - 1, i):
                if 0 <= j < len(corrections):
                    err = min(err, abs(r - corrections[j]))
    return err * lp


random.seed(1)
for qmax in (2, 5, 10):
    errs = [best_error(math.log(10 ** random.uniform(-6, 6)) / lp, qmax) for _ in range(300)]
    rms = math.sqrt(sum(e * e for e in errs) / len(errs))
    hits = sum(e < 6.3e-4 for e in errs)
    print(f"|q| <= {qmax:2d}: RMS {100 * rms:.4f}%, worst {100 * max(errs):.4f}%, within 0.063%: {hits}/300")
