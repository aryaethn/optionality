import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from calibrate import s_per_notional, option_value, F
from statistics import NormalDist
N01 = NormalDist()
fig, ax = plt.subplots(figsize=(5.2, 3.4))
alphas = [10 ** (-x / 20) for x in range(10, 81)]   # 0.32 .. 1e-4
for sigma, ls in ((0.51, "-"), (1.0, "--"), (1.5, ":")):
    s = s_per_notional(sigma, 8)
    fees = [s * N01.inv_cdf(1 - a) / (1 - 1 / F) * 1e4 for a in alphas]
    ax.plot([a * 100 for a in alphas], fees, ls, color="black", lw=1.4, label=f"$\\sigma$ = {int(sigma*100)}%")
for G in (10, 50):
    ax.axhline(G * 0.502, color="0.55", lw=0.9)
    ax.text(28, G * 0.502 * 1.07, f"Thm C lower bound, $G$ = {G} bp, $p_1$ = 1/64", fontsize=7, color="0.35")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("withholding probability (%)"); ax.set_ylabel("ToB fee (bp of notional)")
ax.set_title("Fee to suppress the exogenous option, window 8 s", fontsize=9)
ax.legend(fontsize=7, frameon=False, loc="lower right"); ax.invert_xaxis()
from matplotlib.ticker import ScalarFormatter
for a in (ax.xaxis, ax.yaxis):
    a.set_major_formatter(ScalarFormatter())
from matplotlib.ticker import NullFormatter
ax.yaxis.set_minor_formatter(NullFormatter()); ax.xaxis.set_minor_formatter(NullFormatter())
ax.set_yticks([2, 5, 10, 20, 30]); ax.set_xticks([10, 1, 0.1, 0.01])
ax.set_xticklabels(["10", "1", "0.1", "0.01"])
fig.tight_layout(); fig.savefig("/home/claude/calib_fee.pdf"); print("saved")
