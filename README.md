# optionality

Lean 4 + Mathlib formalization, and numerical scripts, accompanying the paper

> Reveal Optionality in Encrypted Mempools
>
> Separation, Pricing, and Blind Simultaneous Release with Post-Quantum Time-Locks

The paper ([Reveal-Optionality-BSR.pdf](Reveal-Optionality-BSR.pdf)) measures the free option that arises when someone can decide, after an encrypted mempool has fixed the
ordering, whether a committed transaction is opened. This repository machine-checks the core statements of its five
theorems and their corollaries, and contains the scripts behind its numerical tables and figure.

## Status

| | |
|---|---|
| Audited theorems | **116** (`Optionality/Audit.lean`, output in [`AXIOMS.txt`](AXIOMS.txt)) |
| `sorry` / `admit` / new `axiom` | none |
| Axioms used | only `propext`, `Classical.choice`, `Quot.sound` |
| Lean | `v4.34.1` (see `lean-toolchain`) |
| Mathlib | `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |

The development was built and audited against exactly that Mathlib commit. Detailed per-phase results, every
deviation from the formalization briefs, and the issues found in the paper's prose along the way are in
[`REPORT.md`](REPORT.md).

## Setting and conventions

Everything is stated on **finite probability spaces with full support** (`FinProb`: every outcome has positive mass).
This makes conditional expectation an explicit weighted average over the cells of a partition, and turns "positive
probability" into "some outcome exists", so the strictness criteria become existential statements.

* an *information structure* is a labelling `π : Ω → ι`; outcomes with the same label are indistinguishable
  (`Meas`, `Refines`);
* `cond P π Z` is the conditional expectation (cell average); `pos x = max x 0`;
* `val`, `Vendo`, `Vexo`, `Vtot` are the option values of a party with binary control (paper Theorem 1(b));
* the speed ratio `γ = νa / νh` between adversary and honest solver appears only as a parameter. **Nothing here
  models or bounds hardware speed**: that is an explicit assumption of the paper.

## What is formalized

Paper numbering: Theorem 1 Separation, Theorem 2 Timing feasibility, Theorem 3 Fee inversion, Theorem 4 Option
migration, Theorem 5 Blind simultaneous release (the working drafts called Theorems 1 to 4 "A to D").

| File | Content | Paper |
|---|---|---|
| `Basic` | `FinProb`, `ex`, `Meas`, `Refines`, `cond`, `pos` | Model |
| `Block1` | conditional expectation: measurability, tower property, pull-out, refinement | tools |
| `Block2` | optimal binary choice, bound and attainment | Lemma 1 |
| `Block3` | strict conditional Jensen for `x⁺`, with the exact (non-strict-side) criterion | Lemma 2 |
| `Block4` | exact value of the endogenous option, nonnegativity, positivity criterion, timing criterion | Theorem 1(b), Cor. 1 |
| `Block5` | upper bound under forced opening (finite, bounded payoff) | Theorem 1(a) |
| `Block6` | hybrid factor `(1 − q)` on an explicit product space | Cor. 2 |
| `Block7` | counterexample to the v0 strictness criterion; single-commitment LUCID identity | §4, Theorem 3 base |
| `Block8` | two-event (union bound, factor 2) form of Theorem 1(a) | Theorem 1(a) |
| `Block9` | window feasibility `γ ≤ γmax`, closed forms, monotonicity, wait threshold, table entries | Theorem 2 |
| `Block10` | thresholds `f1`, `finv` (real arithmetic) | Theorem 3 |
| `Block11` | attack-plan model; (a) exactly for one commitment, (b) selector plan, (c) upper bound | Theorem 3 |
| `Block12` | committee combinatorics: blocking size, reconstruction, minimal harmful coalition | Theorem 4(a),(c) |
| `Block13` | penalized option, deterrence, hybrid without independence, covariance bound, induced outage | Theorem 4(b),(d), Cor. 3 |
| `Block14` | blind-release window `γ ≤ Ω/ω` as an instance of Theorem 2(a); margins; pad length | §8 |
| `Block15` | escrow model; zero option before the deadline, penalized option after; threshold arithmetic | Theorem 5 |
| `Block16` | fee bound for a fixed reveal set; counting behind the deposit condition | Theorem 5(b),(c) |
| `Block17` | ceilings as a function of the host window `W`, monotonicity, ticket-first and six-second values, pad lengths; sender-side time-lock ceiling in a ticket-first design | §8, App. A, §5 |
| `Stretch` | non-strict Lemmas 1 and 2 over general probability spaces (`MeasureTheory.condExp`) | Lemmas 1, 2 |
| `Audit` | `#print axioms` for every theorem above | |

### Not formalized

* the `L^p` form of Theorem 1(a); strictness criteria without full support; independence-based statements in
  their abstract form (Cor. 2 is proved on an explicit product space); the atomless statement of Cor. 3;
* the strategy/mechanism layer of Definition 1 (the value is identified with the maximum over measurable choices);
* the timing assumptions D1 and D2 and the step from them to binary control; the Gaussian closed form (Lemma 3);
* for Theorem 5: hiding and binding of escrows, determinism and sequentiality of the hash-chain pads, solver
  parity, consensus on the escrow set, the execution rule, that the executed reveal set is fixed at the deadline
  with the same pattern in every class, and the informal bound on the gain from changing the executed set;
* the extremal fee `f*_m` itself (only the plan-level statements that bound it), assumptions A1 to A3, and the numerics.

## Building

```sh
# install elan (https://github.com/leanprover/elan), then:
git clone <this repository> && cd optionality
lake update        # fetches Mathlib v4.34.1 and its prebuilt cache
lake build         # builds everything and prints the axiom audit
```

Every file that imports Mathlib pays a large load cost on a cold machine (the full build took 10 to 35 minutes on
the author's laptop, almost all of it I/O); the proofs themselves elaborate in seconds. To check only the audit:

```sh
lake build Optionality.Audit
```

`lakefile.toml` requires Mathlib from git at the tag `v4.34.1`. The author developed against an already-built local
Mathlib checkout instead, by replacing that `[[require]]` block with `path` requires for `mathlib` and its
dependencies (`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`);
that machine-specific configuration is deliberately not committed. The committed git-based configuration has not
been re-verified from a clean clone.

## Numerical scripts (`python/`)

These are the scripts behind the paper's numerical material. They are **not** part of the Lean development and are
not machine-checked.

| Script | Produces |
|---|---|
| `solver.py` | the attack-plan optimizer behind the fee-inversion numerics (general and selector classes); its `__main__` validates the greedy optimum against exhaustive search on 300 random instances and checks that `m = 1` reproduces LUCID's `f1` |
| `calibrate.py` | the exogenous-option calibration table (Bachelier pricing of the sender's option; `F = 128`) and the dollar example, with a Monte Carlo cross-check |
| `figure.py` | the calibration figure (fee that caps the exercise probability, against the fee-inversion lower bound) |
| `bsr_params.py` | the blind-release window table: host window `W`, opening window `Θ`, ceiling `γ_max = (W − ω)/ω` and pad length for the ticket-first instantiation (twelve- and six-second slots), and the sender-side time-lock ceiling; writes `bsr_params.json` to the current directory |

Run them from inside `python/` (`figure.py` imports `calibrate.py`; `figure.py` needs `matplotlib`). Two output paths are
hard-coded from the original sandbox and must be edited first: the `json.dump(...)` target in `calibrate.py`
(`/home/claude/calib/calibration.json`) and the `savefig(...)` target in `figure.py` (`/home/claude/calib_fee.pdf`).
The scripts are kept exactly as used for the paper; the figure's annotation text uses the earlier notation
(`G`, "Thm C") for the attacker's gain and the fee-inversion theorem, which the paper writes `Λ` and Theorem 3.

## Findings from the formalization

Machine-checking caught several statements that were false or overclaimed in earlier drafts or briefs, all recorded
with counterexamples in [`REPORT.md`](REPORT.md) and corrected in the paper:

* the v0 strictness criterion for a positive endogenous option fails when the exogenous conditional payoff is `0`;
* the LUCID single-commitment identity needs `p ≤ 1` (false for `p > 1`), and the blind-plan fee bound needs `p1 ≤ 1`;
* the claim `finv ≥ Λ/2 ⇔ p1 ≥ 2/(F+1)` needs `Λ > 0`;
* "at most half the committee" is off by one for odd `n` (the bound is `(n+1)/2`); blind release is strictly better
  than every threshold without it exactly when `n = 2` or `n ≥ 4`;
* Theorem 5 needed an explicit deposit condition for informed blocking, a corrected time index in part (a), and the
  calibration conclusion depends on the single-commitment form of assumption A2.

## Development note

The formalization was developed with Claude Code (Anthropic) from precise per-block specifications; every claim above
about proof status is established by `lake build` and the axiom audit, not by the prose.
