"""Theorem C solver: optimal probabilistic frontrunning against a LUCID sealed transaction.

Model (INFERRED, see draft_v3 Section "Theorem C"):
  victim ST has ToB fee f and cap m on preceding commitments.
  attacker posts k <= m commitments, each with ToB fee f (infimum needed to precede victim).
  revealed commitment pays f/F, unrevealed pays f (EIP-8184: 1/F kept on reveal, full fee forfeited otherwise).
  victim plaintext lies in one of N guess classes with probabilities p (sorted descending).
  executing the pattern aimed at the true class gains G; any other execution gains 0 (assumption: misses are harmless).
  attacker learns the class before choosing which commitments to reveal (worst case selective reveal).

Attacker classes:
  'general'  : every nonempty reveal set can carry an arbitrary program (relaxation, upper bound on any attacker).
               Abort = any reveal set (empty set, or a nonempty set given a no-op program, which uses up a slot).
  'selector' : EIP-8184 selector strategy. k-1 selectors + 1 executor; attack patterns are the 2^(k-1) reveal
               sets containing the executor. Abort = any reveal set without the executor.

For fixed (k, abort, assignment) the profit is G*P_A - f*kappa, linear in f, so the attacker is deterred
iff f >= f_star = G * max P_A / kappa. Profit is monotone decreasing in f, so we find f_star by bisection on
the greedy optimum, and cross-check against exhaustive search on small instances.
"""
from itertools import combinations
from math import comb


def level_counts(k, cls):
    """Return list of (j_unrevealed, number_of_attack_slots) and list of abort levels with flag 'uses_slot'."""
    if cls == "general":
        slots = [(j, comb(k, j)) for j in range(0, k)]          # nonempty sets: j unrevealed, j<k
        aborts = [(k, False)] + [(j, True) for j in range(0, k)]  # empty set, or a nonempty no-op set
    elif cls == "selector":
        # executor revealed; j = number of unrevealed selectors among k-1
        slots = [(j, comb(k - 1, j)) for j in range(0, k)]
        # abort: executor unrevealed, j' selectors unrevealed -> total unrevealed j'+1
        aborts = [(jp + 1, False) for jp in range(0, k)] + [(j, True) for j in range(0, k)]
    else:
        raise ValueError(cls)
    return slots, aborts


def cost(j, k, f, F):
    return f * (j + (k - j) / F)


def best_profit(p, G, f, F, m, cls):
    """Greedy optimum over k<=m, abort choice, assignment of classes to slots. Returns (profit, k)."""
    best = (0.0, 0)  # k = 0: do nothing
    for k in range(1, m + 1):
        slots, aborts = level_counts(k, cls)
        for (ja, uses_slot) in aborts:
            ca = cost(ja, k, f, F)
            slot_costs = []
            used = False
            for (j, n) in slots:
                n_eff = n
                if uses_slot and j == ja and not used:
                    n_eff -= 1
                    used = True
                slot_costs += [cost(j, k, f, F)] * n_eff
            slot_costs.sort()
            prof = -ca
            for pt, c in zip(p, slot_costs):
                gain = pt * (G - c + ca)
                if gain > 0:
                    prof += gain
            if prof > best[0]:
                best = (prof, k)
    return best


def f_star(p, G, F, m, cls, tol=1e-12):
    lo, hi = 0.0, G * F * 4 + 1.0
    if best_profit(p, G, hi, F, m, cls)[0] > 0:
        raise RuntimeError("upper bracket too small")
    while hi - lo > tol * max(1.0, hi):
        mid = (lo + hi) / 2
        if best_profit(p, G, mid, F, m, cls)[0] > 0:
            lo = mid
        else:
            hi = mid
    return hi


def exhaustive_profit(p, G, f, F, m, cls):
    """Brute force over every subset assignment (small cases only) to validate the greedy."""
    best = 0.0
    N = len(p)
    for k in range(1, m + 1):
        slots, aborts = level_counts(k, cls)
        slot_list = [j for (j, n) in slots for _ in range(n)]
        for (ja, uses_slot) in aborts:
            ca = cost(ja, k, f, F)
            avail = list(slot_list)
            if uses_slot:
                avail.remove(ja)
            # choose an injective assignment of a subset of classes to slots
            from itertools import permutations
            for r in range(0, min(N, len(avail)) + 1):
                for classes in combinations(range(N), r):
                    for sl in permutations(range(len(avail)), r):
                        prof = -ca
                        for t, s in zip(classes, sl):
                            prof += p[t] * (G - cost(avail[s], k, f, F) + ca)
                        best = max(best, prof)
    return best


if __name__ == "__main__":
    import random
    random.seed(7)
    # 1) validation of greedy against exhaustive search
    for trial in range(300):
        N = random.randint(1, 5)
        w = sorted([random.random() for _ in range(N)], reverse=True)
        s = sum(w) * random.uniform(1.0, 2.0)   # leftover mass = classes the attacker cannot cover
        p = [x / s for x in w]
        G, F = 1.0, random.choice([2, 4, 128])
        m = random.randint(1, 3)
        f = random.uniform(0, 2)
        for cls in ("general", "selector"):
            a = best_profit(p, G, f, F, m, cls)[0]
            b = exhaustive_profit(p, G, f, F, m, cls)
            assert abs(a - b) < 1e-9, (cls, p, f, F, m, a, b)
    print("greedy == exhaustive on 300 random small instances (both attacker classes)")

    # 2) m = 1 reduces to LUCID's formula for both classes
    F = 128
    for pv in (0.1, 0.3, 0.5, 0.9):
        p = [pv]
        lucid = pv * 1.0 / ((1 - pv) + pv / F)
        for cls in ("general", "selector"):
            fs = f_star(p, 1.0, F, 1, cls)
            assert abs(fs - lucid) < 1e-8, (cls, pv, fs, lucid)
    print("m = 1: f_star equals LUCID pG/((1-p)+p/F) for both classes")
