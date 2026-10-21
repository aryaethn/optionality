"""Phase 5 calibration: the sender's exogenous reveal option in LUCID, priced with the Bachelier formula.

Model (INFERRED): a sender whose sealed transaction is a price-sensitive trade of notional N. Over the reveal
window Delta (seconds) the price return is Gaussian with annualized vol sigma (square-root-of-time scaling;
Mazorra et al. note short-horizon scaling lies between sqrt and linear, so sqrt is the conservative choice).
Withholding instead of revealing costs the extra forfeit K = f (1 - 1/F) (EIP-8184: reveal pays f/F, withhold f).
The sender withholds when the adverse move exceeds K. Gain from withholding D ~ N(0, s^2), s = N sigma sqrt(Delta/yr).
Option value V(K) = s phi(K/s) - K (1 - Phi(K/s)); exercise probability = 1 - Phi(K/s).
"""
from statistics import NormalDist
import math, json
N01 = NormalDist()
YEAR = 365.25 * 24 * 3600
F = 128

def s_per_notional(sigma, delta):
    return sigma * math.sqrt(delta / YEAR)

def option_value(K, s):
    if s == 0: return max(-K, 0.0)
    z = K / s
    return s * N01.pdf(z) - K * (1 - N01.cdf(z))

def fee_for_exercise_prob(alpha, s):
    """ToB fee f such that the withholding probability is alpha."""
    K = s * N01.inv_cdf(1 - alpha)
    return K / (1 - 1 / F)

rows = []
for sigma in (0.51, 1.00, 1.50):
    for delta in (4, 8, 12, 16):
        s = s_per_notional(sigma, delta)
        v0 = option_value(0, s)
        f1 = fee_for_exercise_prob(0.01, s)
        f01 = fee_for_exercise_prob(0.001, s)
        rows.append(dict(sigma=sigma, delta=delta, s_bps=s * 1e4, V0_bps=v0 * 1e4,
                         fee_1pct_bps=f1 * 1e4, burn_1pct_bps=f1 / F * 1e4,
                         fee_01pct_bps=f01 * 1e4, residual_V_1pct_bps=option_value(f1 * (1 - 1 / F), s) * 1e4))
print(f"{'sigma':>5} {'Delta':>5} | {'s (bp)':>7} {'V(0) (bp)':>9} | {'fee@1% (bp)':>11} {'burn (bp)':>9} {'resid V':>8} | {'fee@0.1% (bp)':>13}")
for r in rows:
    print(f"{r['sigma']:5.2f} {r['delta']:5d} | {r['s_bps']:7.2f} {r['V0_bps']:9.2f} | {r['fee_1pct_bps']:11.2f} {r['burn_1pct_bps']:9.3f} {r['residual_V_1pct_bps']:8.4f} | {r['fee_01pct_bps']:13.2f}")
json.dump(rows, open("/home/claude/calib/calibration.json", "w"), indent=1)

# Dollar example at the base case
N = 1_000_000
s = s_per_notional(0.51, 8) * N
print(f"\nBase case sigma=51%, Delta=8s, N=$1M: V(0)=${option_value(0, s):.0f}, "
      f"fee for 1% withholding=${fee_for_exercise_prob(0.01, s):.0f} (burned if revealed: ${fee_for_exercise_prob(0.01, s)/F:.2f})")

# Cross-check Bachelier formula by Monte Carlo
import random
random.seed(0)
K, s1 = 1.3, 1.0
mc = sum(max(random.gauss(0, s1) - K, 0) for _ in range(400000)) / 400000
assert abs(mc - option_value(K, s1)) < 3e-3, (mc, option_value(K, s1))
print("Bachelier formula matches Monte Carlo (K=1.3 s): ", round(mc, 4), round(option_value(K, s1), 4))
