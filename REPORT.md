# Report: Lean 4 formalization of phase1_v1 (reveal optionality)

## Result
All 19 requested theorems (Blocks 1-7) are proven. `lake build` succeeds (8935 jobs) with no `sorry`,
`admit` or new `axiom` anywhere in the sources (grep-checked). `#print axioms` for every theorem
(`Optionality/Audit.lean`, output in `AXIOMS.txt`) shows only `propext`, `Classical.choice`, `Quot.sound`.
No theorem statement was found to be false or ill-typed. The optional measure-theoretic stretch goal
was also completed (see below).

## Versions
- Lean 4.34.1 (`leanprover/lean4:v4.34.1`), Lake 5.0.0
- Mathlib `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Mathlib is not vendored here. The audited builds in this report were run against an already-built local Mathlib checkout
  (`path` requires for `mathlib` and its dependencies; Reservoir was unreachable on the build machine). The committed `lakefile.toml`
  instead requires Mathlib from git at tag `v4.34.1` (the same commit); that git-based configuration has not been re-verified from a clean clone.

## Build time
- Full `lake build` (cold page cache, all 8 blocks + Audit): 36 min wall-clock.
- Final `lake build` after adding Stretch to the audit: 8 min.
- Almost all of this is I/O: every file pays ~4 min to load `import Mathlib` on this machine
  (a trivial `import Mathlib` file takes 4:15; a narrow import takes 1:00). The proofs themselves elaborate in seconds.

## Theorems (all PROVEN)
| # | Name | File |
|---|------|------|
| 1 | `cond_meas` | Block1 |
| 2 | `ex_cond` | Block1 |
| 3 | `ex_mul_cond` | Block1 |
| 4 | `cond_cond_of_refines` | Block1 |
| 5 | `cond_mul_meas` | Block1 |
| 6 | `choice_le` | Block2 |
| 7 | `choice_attained` | Block2 |
| 8 | `jensen_pos` | Block3 |
| 9 | `jensen_pos_strict_iff` | Block3 |
| 10 | `thmA_b_value` | Block4 |
| 11 | `thmA_b_endo_nonneg` | Block4 |
| 12 | `thmA_b_endo_formula` | Block4 |
| 13 | `thmA_b_endo_pos_iff` | Block4 |
| 14 | `cor_timing` | Block4 |
| 15 | `thmA_a` | Block5 |
| 16 | `hybrid_endo` | Block6 |
| 17 | `hybrid_tot` | Block6 |
| 18 | `erratum_example` | Block7 |
| 19 | `lucid_m1_deterrence` | Block7 |

Extras (not requested): `erratum_example_corrected` (the corrected `≤`/`≥` criterion does fire on the
erratum example), helper lemmas (`cell`, `mass`, `ex_ind`, `jensen_gap`, `term_pos_iff`,
`exists_pos_of_cond_zero`, `cond_prodInfo`, ...), and the Stretch file.

## Deviations from the prompt (none change a mathematical statement)
1. **`[DecidableEq Ω]` dropped** from the section variables. It is never used (only `DecidableEq ι` for labels is).
2. **Extra file `Basic.lean`** holds the prompt's setup block; helper defs `cell`, `mass`, `ZR`, `val`,
   `Vtot`, `Vexo`, `Vendo`, `prodProb`, `prodR`, `prodD`, `prodInfo`, `prodInfo0` were added.
3. **`thmA_b_value` (10) is stated for an arbitrary information structure `π`**, not for `π ∈ {πG, πF, π0}`:
   the three have different label types, so a set-membership statement is ill-typed. The generic statement
   instantiates to all three.
4. **Hypotheses made explicit.** 11/13 take `Refines πF πG`; 12/13 take `hR : Meas πG (fun ω => if R ω then 1 else 0)`
   (the "πG-measurable 0/1 function" condition); 14 takes both `Refines πF πG` and `Refines πG πF`.
   `Refines πG π0` from the Block 4 setup is not needed by any statement and is not assumed.
   12 is stated as a conjunction (πF and πG).
5. **15 (`thmA_a`)** adds `[DecidablePred Γ]` (needed for the `filter`) and 0/1-valuedness of `X`, `Xp`
   as hypotheses (`hX`, `hXp`); `D` is an explicit argument.
6. **Hybrid (16/17):** `R' = fun _ => True`, `D'` arbitrary, `0 < q < 1`. No refinement hypotheses are needed.
   `Vendo'`/`Vtot'` are the same `Vendo`/`Vtot` defs applied on `Ω'`.
7. **19 (`lucid_m1_deterrence`)**: hypotheses `0 < p`, `p < 1`, `1 < F` are all used; only `0 ≤ f` is unused
   (named `_hf`). **Correction (Phase 3):** this entry originally said `p < 1` was also unused. That was wrong:
   `p < 1` is what makes `(1 - p) + p / F > 0` (the proof's `linarith` uses it despite the `_hp1` name), and
   the equivalence is false without it (`p = 3, F = 2, f = 1`: left side `0.5 ≤ 0` fails, right side `f1 = 0 ≤ 1`
   holds). Statement unchanged.
8. **Linters:** `linter.deprecated`, `unusedSectionVars`, `unusedDecidableInType`, `unusedFintypeInType`
   are switched off per file (`if_pos`/`push_neg` are deprecated in this Mathlib but behave identically).
   Remaining build warnings are Mathlib style-linter notes (module docstring, copyright header, line length),
   not `sorry` warnings.
9. **Full support** (`P.pos`) is a deliberate simplification, as instructed: "positive probability" becomes
   "some outcome exists", so strictness criteria (9, 13) are existential statements about points. The paper's
   general (non-full-support) version is not covered by the finite results.

## What the formalization does and does not cover (honest scope)
- **Covered:** conditional-expectation basics; Lemma 1; Lemma 2 including the corrected strictness criterion
  (with `≤`/`≥` on the πG side; the v0 criterion is refuted by `erratum_example`); the Theorem A(b)
  value identity (via 10), nonnegativity, formula, strictness criterion and timing corollary; the finite
  Theorem A(a) bound; the hybrid factor `(1 - q)` on an explicit product space.
- **Theorem A(a) is the finite, bounded-`D` version only.** The statement takes a single event `Γ` with
  `X = Xp` on `Γ` and bounds the gap by `B * Pr[¬Γ]`. The paper's `L^p`/Hölder version is not formalized, and the
  coupling question the paper leaves open (it takes `Γ = Γ_σ ∩ Γ_pass`, which gives `2ε` unless failures are
  properties of the run) is here an assumption about how `Γ` is chosen, not something proved.
- **Vtot/Vexo/Vendo are defined as differences of `val`.** Their identification with the `sup`-over-strategies
  definition of `V^K` (Definition 1) goes through 10 (`val π` = max of `E[Y·ZR]` over π-measurable 0/1 `Y`);
  the strategy/mechanism layer of Definition 1 is not itself modelled.
- **Corollary 2 is proved for the explicit product construction** (availability independent of `ω'` by construction,
  `D` and `π'` depending only on `ω'`). The paper's general independence hypothesis is not formalized;
  Remark 2 (failure of independence) is out of scope.
- Lemma 3 (Gaussian closed form), Theorems B-D, and the STFO definition itself are not formalized.

## Stretch goal (done): `Optionality/Stretch.lean`
Over `MeasureTheory.condExp` on a probability space, using no new axioms:
- `condExp_pos_le`: `E[W|C]⁺ ≤ E[W⁺|C]` a.e. (`condExp_mono` on `W ≤ W⁺`, `condExp_nonneg` on `0 ≤ W⁺`, then `max_le`).
- `integral_condExp_pos_le`: `E[(E[W|C])⁺] ≤ E[W⁺]` (`integral_mono_ae`, `integral_condExp`, `Integrable.pos_part`).
- `integral_mul_le_condExp_pos`: Lemma 1 upper bound `E[YZ] ≤ E[(E[Z|C])⁺]` for C-measurable 0/1 `Y`
  (`condExp_mul_of_stronglyMeasurable_left`, `Integrable.bdd_mul`, `integral_condExp`).
The strict part and the attainment half of Lemma 1 are not done in the general setting.

## Files
`Optionality/{Basic,Block1..Block7,Stretch,Audit}.lean`, `Optionality.lean`, `lakefile.toml`, `AXIOMS.txt`.

---

# Phase 2 (draft_v2.tex): Blocks 8 and 9

## Result
All 14 requested theorems (items 20-33) are proven. Full `lake build` succeeds (8937 jobs); no `sorry`, `admit`
or `axiom` in the sources (grep-checked). `AXIOMS.txt` now holds `#print axioms` for all 37 audited theorems
(Phase 1: 23, Phase 2: 14); every one depends only on `propext`, `Classical.choice`, `Quot.sound`.
No statement was false or ill-typed, and none was weakened.

## Theorems (all PROVEN)
| # | Name | File |
|---|------|------|
| 20 | `mass_not_and_le` | Block8 |
| 21 | `thmA_a_two_events` | Block8 |
| 22 | `thmA_a_same_event` | Block8 |
| 23 | `thmB_iff` | Block9 |
| 24 | `thmB_b_pess` | Block9 |
| 25 | `thmB_b_opt` | Block9 |
| 26 | `gmaxPess_strictAnti` | Block9 |
| 27 | `gmaxOpt_strictAnti` | Block9 |
| 28 | `gmaxOpt_tendsto_one` | Block9 |
| 29 | `thmB_wait_threshold` | Block9 |
| 30 | `gmaxOpt_lt_two` | Block9 |
| 31 | `frontier_early_antitone` | Block9 |
| 32 | `frontier_late_monotone` | Block9 |
| 33 | `table_checks` | Block9 |

## Build time
Full `lake build` for this phase: 15 min wall-clock (cold cache). Per file: `Block8` 293 s (imports `Mathlib`
through `Block5`), `Block9` 115 s (narrow imports: `Mathlib.Tactic`, `Mathlib.Analysis.SpecificLimits.Basic`,
`Mathlib.Order.Monotone.Basic`; no full `import Mathlib`), `Audit` 292 s. Block 9 on its own checks in about 70 s.

## Deviations (none changes a mathematical statement)
1. **22 (`thmA_a_same_event`)** is stated in the two-event form with a common `Γ` (hypotheses `X = Xbar` and
   `Xp = Xbar` on `Γ`) and concludes `B * mass(¬Γ)`, as the prompt says. It is proved by reducing to Phase 1's
   `thmA_a`, which remains available (it assumes `X = Xp` on `Γ` directly).
2. **21/22:** `Xbar` is assumed 0/1-valued as in the prompt, but the proof never uses it (hypothesis named `_hXbar`).
   `[DecidablePred Γσ]`, `[DecidablePred Γp]` are added for the `filter`; "mass of ¬Γ" is written as the filter sum.
3. **24/25** take the substitution as equation hypotheses (`tpub = t0 - w`, `t1 = t0 + δ`, `t2 = t0 + δ + Δ`,
   and `th = t0` resp. `th = tpub`) rather than writing the substituted expressions, so the statement mirrors
   the paper's definitions of `t_pub`, `t_1`, `t_2`, `t_h`.
4. **28** takes `Δ` explicitly and `0 < δ` as an unused hypothesis (`_hδ`); the limit holds without it.
5. **23:** no relation between `th` and `tpub` is needed (only `tpub < t1`, `0 < γ`). If `t2 ≤ th` the right-hand
   side is `≤ 0 < γ` and the equivalence correctly reports infeasible.
6. **31/32** take `G`, `H` merely `Monotone` (a distribution function is a special case). The identification
   `p_early(x) = 1 - G(x/c)` with a probability is a modelling step and is not formalized; only the monotonicity
   in `x` is.
7. `Private`/`Timely`/`gmaxPess`/`gmaxOpt` are as specified; the defs sit in a `noncomputable section`
   (real division).

## Observations on draft_v2.tex (checked while formalizing; no Lean statement depends on these)
- **Table values.** All 36 entries of Table 1 recompute correctly to the printed rounding (checked by hand; the five
  entries asked for in `table_checks` are machine-checked). `gmaxOpt 4 8 60 = 72/64 = 1.125` is printed as 1.12;
  round-half-even, harmless.
- **Remark, consequence 2 is inaccurate as worded.** It says `γ_max ∈ [3, 13]` is "at or below the `A_max ≈ 10`
  and `20×` reference points". The row `(δ, Δ) = (1, 12)` has `γ_max = 13 > 10`, so against `A_max ≈ 10` that
  configuration is feasible (since feasibility is `γ ≤ γ_max`); only the rows with `γ_max ∈ {3, 4, 5, 7, 9}`
  are at or below 10. Against `20×` all rows are below. Suggest restating per row.
- **Theorem B(b), "both are strictly decreasing in `w`"** needs `δ > 0` and `Δ > 0` (formalized as `hδ`, `hΔ`).
  With `Δ = 0`, `gmaxOpt ≡ 1`. The draft states neither hypothesis. The limit statement (28) holds for any `Δ`.
- **Threshold in B(b)** `w > (δ + Δ - γδ)/(γ - 1)` is correct for the second (`t_h = t_pub`) formula and
  is proved as `thmB_wait_threshold` (needs `γ > 1`, `δ > 0`, `w ≥ 0`). It is not the threshold for the first
  formula.
- **B(c)'s use of Theorem A(a).** `V^tot ≤ B p_late(x)` follows from the same-event bound (22) once one identifies
  `mass(¬Γ)` with `p_late(x)`. That identification (and the L^p/Hölder form) is outside the finite formalization.

## Suggested update to draft_v2.tex §"Machine-checked results"
Add: finite two-event form of Theorem A(a) (union bound, factor 2) and its same-event specialization;
Theorem B(a), the two closed forms in B(b), strict monotonicity in `w`, the `w → ∞` limit, the wait threshold,
the "below 2 after one slot" bound, monotonicity of the early/late frontiers in B(c), and the table spot checks.
Still not machine-checked: the probabilistic identification of `p_early`, `p_late` with distribution functions,
and the L^p form of Theorem A(a).

---

# Phase 3 (draft_v3.tex): Blocks 10 and 11, Theorem C

## Result
All 11 requested theorems (items 34-44) are proven. Full `lake build` succeeds (8939 jobs); no `sorry`, `admit`
or `axiom` in the sources (grep-checked). `AXIOMS.txt` now holds `#print axioms` for all 48 audited theorems
(Phase 1: 23, Phase 2: 14, Phase 3: 11); every one depends only on `propext`, `Classical.choice`, `Quot.sound`.

**One requested statement was false as written (item 34) and was fixed minimally; see Deviation 1.**
I also found that a Phase 1 report entry was wrong; it is corrected in place (Phase 1, deviation 7).

## Theorems (all PROVEN)
| # | Name | File | Note |
|---|------|------|------|
| 34 | `lucid_m1_iff_f1` | Block10 | needs added hypothesis `p ≤ 1` |
| 35 | `selector_profit_pos_iff` | Block10 | |
| 36 | `finv_ge_half_iff` | Block10 | |
| 37 | `upper_eq_f1_div` | Block10 | |
| 38 | `table_C` | Block10 | |
| 39 | `cost_ge_f_of_lt` | Block11 | |
| 40 | `cost_univ` | Block11 | |
| 41 | `thmC_c_upper` | Block11 | Theorem C(c) |
| 42 | `thmC_b_selector` | Block11 | Theorem C(b); plan + positivity, as a conjunction |
| 43 | `thmC_b_any_m` | Block11 | |
| 44 | `thmC_a_exact` | Block11 | Theorem C(a), `k = 1` |

## Build time
Full `lake build`: 9 min 15 s wall-clock (cold cache). Per file: `Block10` 87 s and `Block11` 96 s (both with narrow
imports, no `import Mathlib`), `Audit` 215 s (goes through `import Mathlib`). Each file also checks in about 70 s with
`lake env lean`.

## Deviations
1. **Item 34 is false as stated; added hypothesis `p ≤ 1`.** The prompt has only `0 < p`, `1 < F`. Counterexample:
   `p = 3, F = 2, G = 0, f = 1`. Then `(1 - p) + p / F = -1/2 < 0`, the left side
   `p (G - f/F) - (1 - p) f = 0.5 ≤ 0` is false, but `f1 = p G / (...) = 0 ≤ 1 = f` is true. The equivalence needs a
   positive denominator, which `0 < p ≤ 1`, `F > 0` gives. `p ≤ 1` is the minimal fix (Phase 1's theorem 19 had `p < 1`).
   Nothing downstream is affected: items 41-44 call it with `0 < p1 < 1`.
2. **34 is re-proved in Block 10, not reused from Block 7.** Phase 1's `lucid_m1_deterrence` carries an extra
   (unused) `0 ≤ f` and `p < 1`, and importing Block 7 would pull in full `import Mathlib` (about 4 min per file)
   into the narrow-import Block 10. The proof is the same six lines.
3. **Argument style.** 34-37 take `(p G F f)` explicitly, as Phase 1's 19 did. 36 needs only `0 < F` (not `1 < F`).
4. **41 (`thmC_c_upper`):** all standing hypotheses are present, `0 ≤ p1` is genuinely used (to get
   `(1 - p1) + p1/F ≤ 1`, hence `f ≥ G`), and the conclusion is stated as `∀ P : Plan ι k, profit ... ≤ 0` as asked.
   It needs `[Fintype ι] [DecidableEq ι]` (for `∑ t, p t ≤ 1` and `Finset.erase`).
5. **42 (`thmC_b_selector`)** is one theorem, a conjunction: (i) `∃ P : Plan ι 2` with
   `profit = p1 (G - f (1 + 1/F)) - (1 - p1)(2 f / F)`, and (ii) `f < finv G F p1 → ∃ P : Plan ι 2, 0 < profit p G F f P`.
   The plan is the definition `selectorPlan` (`A = {t1}`, `σ _ = {1}`, `a = univ`). Hypotheses: `p t1 = p1`,
   `0 < p1 ≤ 1`, `0 < F`.
6. **43** has the same hypotheses as 42 plus `2 ≤ m`.
7. **44 (`thmC_a_exact`)** needs only the hypotheses listed in the prompt: no `0 ≤ p t` or `∑ p ≤ 1`.
   It is about `k = 1` only. (A `k = 0` plan has `A = ∅` and profit `0`, so it never beats `k = 1`; this is not
   a separate theorem.) The profitable witness plan (`σ = univ`, `a = ∅`) lies in the selector class too, so the
   threshold `f1` is the same for both classes, as the draft says.
8. **`Plan.inj`** is `Set.InjOn σ ↑A` (coercion of the `Finset`); `cost`, `profit` are verbatim from the prompt.
9. **Added helper lemmas** (not requested): `cost_eq_mul`, `cost_nonneg`, `profit_eq` (`profit = G·PA - f·κ`),
   `selectorPlan`, `profit_selectorPlan`, `exactPlan`, `profit_exactPlan`, `cost_one_empty`, `cost_one_univ`, `fin1_cases`.

## What is and is not formalized
- **Formalized:** the arithmetic thresholds `f1`, `finv`; the model (`cost`, `Plan`, `profit`) in the *general* class
  (every nonempty reveal set may carry any program); Theorem C(c) for every `k ≥ 1` and every plan; C(b) as an
  explicit profitable plan for `f < finv` under any cap `m ≥ 2`; C(a) exactly for `k = 1`; C(d) as 36.
- **Not formalized:** the extremal quantity `f*_m` itself ("least fee such that no plan with `k ≤ m` is profitable")
  and the combined statements `f*_m ≥ max{f1, finv}`, `f*_m ≤ f1/p1` (they follow from 41-44 but are not stated
  as such); assumptions A1-A3, in particular that the selector plan is implementable under A3 and that the
  general class over-approximates sequential programs; the numerics section (greedy vs exhaustive search, the 3000
  random priors, the uniform-prior table beyond the spot checks below).

## Observations on draft_v3.tex (none changes a Lean statement)
- **Table 2 (fees).** All five rows recompute to the printed rounding; row `p1 = 1/64` is machine-checked in 38
  (`finv = 128/255`, `f1 = 128/8065`, ratio `8065/255 ≈ 31.6`).
- **Numerics table.** I brute-forced the *general* class (all injective assignments of nonempty reveal sets, all abort sets)
  independently of Lean for uniform priors, `F = 128`: `N = 4`: .332 / .977 / 1.303 and `N = 16`: .067 / .895 / .895
  for `m = 1, 2, 3`. These match the draft. I did not recheck `N = 64, 256`, `m > 3`, the selector columns,
  or the random-instance claims.
- **Remark 1, "jumps to roughly G as soon as `p1 ≥ 2/(F+1)`", overstates what is proved.** 36 gives
  `finv ≥ G/2` exactly when `p1 ≥ 2/(F+1)`, with equality at the threshold. At `p1 = 1/64` the table has `finv = 0.502 G`, i.e.
  about half of `G`. `finv → G` only as `p1 F → ∞`. Suggested wording: "to at least `G/2`, approaching `G` once `p1 F ≫ 1`".
  The "`32×`" jump at `p1 = 1/64` is correct (`f1 → finv`, ratio 31.6).
- **Remark 2 ("barely depends on either") is a numerics claim, not a theorem.** The proved window for `m ≥ 2` is
  `[finv, f1/p1]`, which at `p1 = 1/64` is `[0.502, 1.016] G`, a factor of about 2. The text calls the upper end
  `G/(1-p1)`; the proved bound is the tighter `f1/p1 = G/((1-p1) + p1/F) ≤ G/(1-p1)`.
- **Proof of C(c) in the draft** omits the case "`a ≠ [k]` and no class uses `[k]`" (then `κ ≥ 1 ≥ (1-p1)+p1/F`) and the step
  `1 - p_{t0}(1 - k/F) ≥ 1 - p1(1 - 1/F)`, which uses `k ≥ 1`, `p_{t0} ≤ p1` and `1 - 1/F ≥ 0` (needs `F ≥ 1`). The formal
  proof covers both; the standing assumptions `F ≥ 1`, `G ≥ 0` should be stated in the theorem.

## Suggested update to draft_v3.tex §"Machine-checked results"
Add: Theorem C(a) at `k = 1`, C(b) (explicit selector plan and its profit, valid for every `m ≥ 2`), C(c) for all `k ≥ 1`
over the general plan class, C(d), and the single-row table check, all over finite plan structures with real
arithmetic. Not machine-checked: `f*_m` as an extremum, assumptions A1-A3, the numerics, and the "C5 is false" reading of the bounds.

---

# Phase 4 (draft_v4.tex): Blocks 12 and 13, Theorem D

## Result
All 14 requested theorems (items 45-58) are proven. Full `lake build` succeeds (8941 jobs); no `sorry`, `admit` or
`axiom` in the sources (grep-checked). `AXIOMS.txt` now holds `#print axioms` for all 66 audited theorems
(Phase 1: 23, Phase 2: 14, Phase 3: 11, Phase 4: 14 requested + 4 extras). The only axioms appearing anywhere are
`propext`, `Classical.choice`, `Quot.sound` (the `omega`-based Block 12 proofs use a subset: `propext`, `Quot.sound`).

No requested statement was false or ill-typed. One hypothesis in the prompt (item 52) is stronger than what the paper
needs; I proved it as asked and added the paper's version (Deviation 3). Observations on `draft_v4.tex` are below,
including one statement in the draft that is false at a boundary value (Theorem C(d) at `G = 0`).

## Theorems (all PROVEN)
| # | Name | File | Note |
|---|------|------|------|
| 45 | `blocking_iff` | Block12 | plus `blocking_size_iff` (`n + 1 ≤ t + w` form) |
| 46 | `nonblocking_forces_execution` | Block12 | |
| 47 | `last_mover_reconstructs` | Block12 | |
| 48 | `min_harm_le` | Block12 | |
| 49 | `min_harm_eq_iff` | Block12 | |
| 50 | `min_harm_odd` | Block12 | |
| 51 | `min_harm_even` | Block12 | |
| 52 | `deterrence_zero` | Block13 | plus `deterrence_Vendo_zero`, `deterrence_zero_of_cond_le` |
| 53 | `deterrence_strict` | Block13 | |
| 54 | `hybrid_dep_formula` | Block13 | with def `Zopt` |
| 55 | `hybrid_dep_Z_nonneg` | Block13 | |
| 56 | `hybrid_dep_bounds` | Block13 | |
| 57 | `hybrid_dep_cov` | Block13 | stated for arbitrary `Z`, `R` |
| 58 | `induced_unavailability` | Block13 | plus `induced_unavailability_of_meas` |

## Build time
Full `lake build`: 11 min 27 s wall-clock (cold cache). Per file: `Block12` 98 s (narrow import `Mathlib.Tactic`),
`Block13` 235 s (imports `Block6`, hence full `Mathlib`), `Audit` 225 s.

## Deviations (none weakens a statement)
1. **45** has the unused hypothesis `1 ≤ t` (named `_ht1`): the equivalence holds for `t = 0` as well. I added
   `blocking_size_iff : t ≤ n → (n - t + 1 ≤ w ↔ n + 1 ≤ t + w)` for the subtraction-free form.
   **48/51:** `1 ≤ t` and `1 ≤ k` are likewise unused (51 is vacuous for `n = 0`).
2. **Block 13 imports `Block6`**, not just `Block4`, to reuse `ZR_true` (`ZR (fun _ => True) D = D`). No cost: both
   already load full `Mathlib`.
3. **52 (`deterrence_zero`) is split in two and has a paper-form companion.**
   - `deterrence_zero`: as in the prompt (`∀ ω, D ω ≤ pen` gives `ex (pos (cond π (D - pen))) = 0` for every `π`).
   - `deterrence_Vendo_zero`: the stated consequence, `Vendo` for `D - pen` with `R = univ` is `0`.
   - **`deterrence_zero_of_cond_le` (extra):** the hypothesis `D ≤ pen` is stronger than the paper's D(d), which only needs
     `pen ≥ ess sup D^F` (a bound on the *conditional* payoff). This theorem proves `Vendo = 0` under
     `∀ ω, cond P πF D ω ≤ pen` (with `Refines πF πG`), which is exactly the draft's statement.
4. **53** takes `Refines πF πG` (needed by `thmA_b_endo_pos_iff`); `cond_sub_const` is proved as a lemma.
5. **54-56** use the definition `Zopt P πF πG D := cond P πG (fun ω => pos (cond P πF D ω) - pos (cond P πG D ω))`, which is
   exactly the prompt's `Z`. They need `Refines πF πG` and `hR : Meas πG (indicator of R)`.
6. **57 is stated for an arbitrary `Z : Ω → ℝ`** (and arbitrary decidable `R`; no measurability needed), which is strictly
   stronger; `Zopt` is an instance. `qR` is written out as `ex P (indicator of R)`.
7. **58:** `induced_unavailability_of_meas` proves the claim for any `π`-measurable `Z`; `induced_unavailability` is the
   instance `Z = Zopt`, `π = πG` (measurability from `cond_meas`). Stated, as in Block 2, as an upper bound plus an attaining `Y`.
8. **Helper lemmas added** (not requested): `cond_sub`, `cond_const`, `cond_sub_const`, `cond_of_meas`, `cond_mono`,
   `cond_nonneg`, `cond_nonpos`, `ex_pos_of_nonpos`, `ex_add`, `ex_sub`, `ex_smul`, `ex_const`, `abs_ex_mul_le`
   (Cauchy-Schwarz for the weighted expectation, via `Finset.sum_mul_sq_le_sq_mul_sq`).

## What is and is not formalized
- **Formalized:** the committee combinatorics of D(a) and D(c), including the odd/even dichotomy; that the last mover holds
  `t ≤ h + w` shares (D(b)'s reconstruction step); the exact value and strictness criterion of the endogenous option for the
  penalized payoff `D - pen` (D(b), D(d)); the hybrid formula `V = E[1_R Z]`, `Z ≥ 0`, `0 ≤ V ≤ E[Z]`, the covariance
  bound, and the induced-unavailability value `E[(Z - c)⁺]` (Corollary 4 items 1 and 3).
- **Not formalized:** the committee *timing* assumptions D1/D2 and the claim that they give the coalition "binary control on
  Ω with mechanism information" (the model-to-theorem step in D(b)'s proof; only the combinatorics (45-47) and the value
  identity (52-54) are checked); Corollary 4 item 2 (the bathtub/top-quantile statement; see observation 4 below); the
  numerical claims of Remark 4 and the external citations (Lin et al., SoK, Mazorra et al., Herold's post).

## Observations on draft_v4.tex (none changes a Lean statement)
1. **Theorem C(d) is false at `G = 0`.** The theorem's standing assumption is `G ≥ 0`, but `f_inv(p1) ≥ G/2 ⇔ p1 ≥ 2/(F+1)`
   needs `G > 0` (item 36 assumes `0 < G`). At `G = 0`, `f_inv = 0 ≥ 0 = G/2` holds for every `p1`, while
   `p1 ≥ 2/(F+1)` fails for small `p1`. Suggest `G > 0` in the standing assumptions (or in (d) only).
   Related, minor: (a) is proved (item 44) for `F > 1`; the draft assumes `F ≥ 1`. At `F = 1` the statement is also true
   (no refund, `f1 = p1 G`) but is not covered by the formal proof.
2. **Remark 2, "any threshold leaves one of the two at most half the committee", is off by one for odd `n`.** Items 48-51
   give `min(t, n - t + 1) ≤ (n+1)/2`, with equality exactly at `t = (n+1)/2` for odd `n`. E.g. `n = 3`, `t = 2`: a coalition
   of 2 out of 3 is the smallest harmful one, which is more than half. For even `n` the bound is `≤ n/2` (item 51).
   Suggest "at most `⌈n/2⌉`" or "at most `(n+1)/2` members". Theorem D(c) itself states this correctly.
3. **Theorem D(d) vs. the converse.** The condition `pen ≥ ess sup D^F` is proved sufficient (`deterrence_zero_of_cond_le`).
   The stated "converse" (`Pr[D^F > pen ≥ D^G] > 0` implies the option is positive) is the first disjunct of the exact
   criterion (53); the iff has a second disjunct (`D^F < pen ≤ D^G`), so it is a sufficient condition, not a true converse.
4. **Corollary 4, item 2** ("on an atomless space") needs `R` restricted to `G_{t*}`-measurable sets and atomlessness of
   `G_{t*}`; a finite full-support space has atoms, so this cannot be stated in the finite setting. Not formalized.
5. **Corollary 4, item 1.** Formal 54-57 confirm `V = E[1_R Z]`, `0 ≤ V ≤ E[Z]` and the covariance identity/bound. The draft's
   `q` is `1 - Pr[R]`; the bound uses `q(1-q) = Pr[R](1 - Pr[R])`, which is symmetric, so the statement is unaffected.
6. **Remark 4 numbers.** For lognormal `Z` with `σ = 2` the share captured by the top fraction `q` of probability mass is
   `Φ(σ - z_{1-q})`: 37.2% at `q = 1%` and 63.9% at `q = 5%`, matching the draft's 37% and 64% (computed outside Lean).
   The ePBS claim (seven blocks carrying half the day's option value on 5 August 2024) is an external citation I did not check.
7. **D(a)/D(b) consistency.** "The sender's option is 0 whenever the honest members alone reach `t`" is `h ≥ t ⇔ |W| ≤ n - t`,
   i.e. item 46's non-blocking case. "`n = t = 1` makes the provider a blocking coalition" is item 45 at `n = t = w = 1`.

## Suggested update to draft_v4.tex §"Machine-checked results"
Add: Theorem D(a) and D(c) (committee combinatorics, including the odd/even case), the reconstruction step of D(b), the exact
value and strictness criterion for the penalized option together with the sufficient deterrence condition (both forms),
Corollary 4 items 1 and 3 (formula, nonnegativity, bounds, covariance bound, induced unavailability), all over finite
full-support spaces. Change "In total 48 theorems" to 66 (48 + 14 requested + 4 helpers/variants), and replace
"Theorem D is in the Phase 4 prompt". Not machine-checked: D1/D2 as timing assumptions, Corollary 4 item 2, the numerics and citations.

---

# Phase 5 (paper.tex, Section 8): Blocks 14 and 15, blind simultaneous release

## Result
All 17 requested items (59-75, 19 theorem statements counting the two-part items 61 and 73) are proven. Full `lake build` succeeds
(8943 jobs); no `sorry`, `admit` or `axiom` in the sources (grep-checked). `AXIOMS.txt` now holds `#print axioms` for all 91 audited
theorems (Phases 1-4: 66, Phase 5: 19 requested + 6 helpers). The only axioms appearing anywhere are `propext`, `Classical.choice`,
`Quot.sound` (the 9 purely arithmetic proofs use a subset, without `Classical.choice`). No requested statement was false or ill-typed.

## Theorems (all PROVEN)
| # | Name | File | Note |
|---|------|------|------|
| 59 | `bsr_window_iff` | Block14 | |
| 60 | `bsr_window_of_thmB` | Block14 | via `thmB_iff`; helpers `bsr_private_iff`, `bsr_timely_iff`, `bsr_ceiling` |
| 61 | `gmaxBSR_strictAnti`, `gmaxBSR_values` | Block14 | |
| 62 | `pad_length_example` | Block14 | |
| 63 | `consistent_no_control` | Block15 | |
| 64 | `inconsistent_withhold_costs` | Block15 | |
| 65 | `thmBSR_a_pre` | Block15 | = `cor_timing` |
| 66 | `thmBSR_a_post` | Block15 | = `deterrence_zero_of_cond_le` |
| 67 | `bsr_no_profitable_deviation` | Block15 | |
| 68 | `bsr_blind_profit_eq` | Block15 | |
| 69 | `tBSR_ceil` | Block15 | |
| 70 | `tBSR_le` | Block15 | |
| 71 | `tBSR_ge_minharm` | Block15 | uses Block 12's `min_harm_le` |
| 72 | `tBSR_gt_minharm` | Block15 | |
| 73 | `tBSR_blocking_only_range`, `tBSR_blocking_only_range_three` | Block15 | plus `tBSR_blocking_range_iff` |
| 74 | `below_threshold_cannot_decrypt` | Block15 | |
| 75 | `thmBSR_d` | Block15 | strengthened (Deviation 9); helpers `cond_eq_of_equiv`, `Zopt_zero_of_equiv` |

## Build time
Full `lake build`: 12 min 10 s wall-clock (cold cache). Per file: `Block14` 106 s (imports `Block9`, narrow), `Block15` 245 s
(imports Blocks 12 and 13, hence full `Mathlib`), `Audit` 221 s.

## Deviations (none weakens a statement)
1. **59** has the unused hypothesis `0 < Ω` (named `_hΩ`): if `Ω ≤ 0` both sides are false, so the equivalence holds anyway.
2. **60** is the same statement as 59 but proved through Phase 2's `thmB_iff`, with exactly the substitution in the prompt
   (`tpub := t1`, `t1 := t1 + ω`, `th := t1 + ω`, `t2 := t1 + ω + Ω`, `γ := νa/νh`, `x := L/νh`). It takes the base time `t1` as an
   explicit real (any value works). The bijection `x ↔ L = x·νh` handles `∃ x > 0` versus `∃ L > 0`; helper lemmas show `Private` becomes
   `ω ≤ L/νa`, `Timely` becomes `L/νh ≤ Ω`, and the ceiling becomes `Ω/ω`. No different mapping was needed.
3. **61** `gmaxBSR_strictAnti` needs `0 < T` (used in the proof); the four values are proved as one conjunction.
4. **62** is stated via `padLength Ω νh := Ω * νh` and `10 ^ (-9 : ℤ)`; `norm_num` evaluates the `zpow` directly.
5. **63/64** write `Action.reveal` / `Action.withhold` in full instead of dot-notation.
6. **65** carries the unused hypothesis `Meas πG (indicator of R)` (`cor_timing` does not need it); **66** renames the bound sample
   point to `ω'` (the paper's `ω` is the escrow window) and is `deterrence_zero_of_cond_le` with `pen := S`.
7. **67** is stated with `Fintype ι`; `S` links `g ≤ c` and is otherwise unused. It proves that deviation is never *strictly* profitable.
8. **72** keeps the prompt's `4 ≤ n`. The improvement is in fact strict also at `n = 2` (`1 < 2`) and fails exactly at `n = 1, 3`
   (checked by brute force for `n ≤ 12`; not a separate theorem). **73** has the prompt's two statements plus the iff
   `tBSR_blocking_range_iff : n - tBSR n + 1 < tBSR n ↔ n = 2 ∨ 4 ≤ n` (true for every `n`).
9. **75 is not a pure alias.** `thmBSR_d` states (i) `Zopt = 0` pointwise when `πF`, `πG` carry the same information, and (ii) `Vendo = 0`
   for *every* outage event `R` (second conjunct is `thmBSR_a_pre`). (i) is what makes the paper's "whatever the correlation" precise:
   `V = E[1_R Z]` with `Z ≡ 0`.
10. **Block 15 imports Blocks 12 and 13** (and, through them, Blocks 4 and 6).

## What is and is not formalized (Theorem 5)
- **Formalized:** the feasibility window of the pad length as an instance of Theorem 2(a) (59, 60); the four margins and the pad length
  (61, 62); the post-deadline control of a releaser: none if consistent (63), non-execution at cost `S` if inconsistent (64); the
  zero-option statements for a decision taken with no mechanism information (65, 75) and the `S`-penalized option (66); the arithmetic
  of "deviation never pays" (67, 68); the threshold comparison and boundary cases (69-74).
- **Not formalized:** hiding of escrows and binding/hiding of the commitment; determinism and sequentiality of the pads (and the
  post-quantum claim); the solver-parity assumption itself (only the ratio `νa/νh` appears); consensus on the escrow set `E`; the
  execution rule; that "no information is released before `d`" holds in the protocol (it is the hypothesis `πF ≈ πG`); the informal
  bound "gain from changing the executed set ≤ Λ + largest misdirected loss"; and the claim that the attacker's profit under BSR
  is at most that of a blind strategy (68 only records that with no deviation the payoff is the fixed-set payoff).

## Observations on Section 8 of paper.tex (none changes a Lean statement)
1. **Theorem 5(c), "at most ⌈n/2⌉ for any threshold without blind release" (items 71, 72).** The upper bound is correct:
   `max_t' min(t', n-t'+1) = ⌈n/2⌉` (proved `≤` by item 48/71, attained by 50; brute-forced for `n ≤ 12`). But blind release with
   `t = ⌈2n/3⌉` is **never worse** (71) and **strictly better only for `n = 2` and `n ≥ 4`** (72 for `n ≥ 4`):

   | n | 1 | 2 | 3 | 4 | 5 | 6 | 9 | 12 |
   |---|---|---|---|---|---|---|---|---|
   | ⌈n/2⌉ (best without BSR) | 1 | 1 | 2 | 2 | 3 | 3 | 5 | 6 |
   | ⌈2n/3⌉ (with BSR) | 1 | 2 | 2 | 3 | 4 | 4 | 6 | 8 |

   At `n = 3` both are `2`, so "two thirds against at most half" is not an improvement there (nor at `n = 1`). Suggest "never less, and strictly
   more unless `n ∈ {1, 3}`". The sentence "a coalition with `n - t + 1 ≤ |W| < t` can block only blind" is **vacuous for `n ∈ {0, 1, 3}`** (73):
   at `n = 3`, `t = 2`, `n - t + 1 = 2 = t`. It is nonempty exactly for `n = 2` and `n ≥ 4`; the paper does not claim otherwise.
2. **Parameters paragraph (items 61, 62).** The margins `11, 5, 5, 2` are correct (`gmaxBSR`). `L = Ω·νh` with `νh = 1/(70 ns)` and `Ω = 10 s` is
   `1.43 × 10^8`, so "`≈ 1.4 × 10^8`" is right (62 proves `(1.4, 1.5) × 10^8`) and one pad is `10 s` of one core by construction. Two small points:
   `Ω = 10 s` is the `ω = 2 s` case (`T = 12`); for `ω = 1 s` it is `Ω = 11 s` and `L ≈ 1.57 × 10^8`. And the cited attestation latencies
   (median 830 ms, 95th percentile 1.96 s) make `ω = 2 s` the setting that covers the 95th percentile, while `ω = 1 s` (the `11×` end) sits between the median and the
   95th percentile; the "5 to 11" range therefore mixes a conservative and an aggressive escrow window. The abstract's "5 to 11" is for 12-second slots only
   (6-second slots give 2 to 5, as the paragraph says). The SHA-256 figure checks out (`146 / 2.1 GHz = 69.5 ns`).
3. **Theorem 5(b) vs item 67.** The hypotheses match exactly: `g ≤ S` ("`S` at least the largest gain") and `S ≤ c` ("changing the executed set costs at least `S`").
   What 67 proves is that deviation is never strictly profitable. Two parts of the paper's text are not derived from it: "this gain is at most `Λ` plus the
   largest loss of a misdirected execution" (an informal bound on `g`), and "its profit is at most that of an unconditional, blind frontrunning strategy".
   For the latter, note that Section 6's `Π` lets the attacker abort on a miss, so it does not apply to a blind plan; the paper never states the fee that
   deters blind plans. A simple upper bound is profit `≤ p1 Λ - f/F` (the same set is revealed in every class, at cost `≥ f/F`), so `f ≥ F p1 Λ` suffices; this is
   only a sufficient fee, because A2's misdirected-execution loss is not quantified. Section 10's statement that deterring probabilistic frontrunning is the binding
   constraint is computed for the non-BSR designs.
4. **Theorem 5(a)'s displayed option uses the wrong time index.** It writes `E[(D^F_d - S)^+] - E[(D^G_d - S)^+]`, but the theorem's own hypothesis (no information
   about release values before `d`) gives `F_d = G_d`, so as written the difference is identically `0` for every `S` (item 65) and the condition
   `S ≥ ess sup D^F_d` would be vacuous. The post-deadline decision is taken at some `t* > d`, after fast reveals; the formula should read `D^F_{t*}`, `D^G_{t*}`.
   Item 66 is stated for the decision-time information and is correct as such.
5. **Theorem 5(c), 5(d) and the "blind blocking" paragraph need the deposit condition.** After `d` the honest members reveal in the clear, so a coalition with
   `n - t + 1 ≤ |W| < t` holds all `n` shares and can read the plaintexts; with an inconsistent escrow it can then still block at cost `S`
   (items 63, 64), i.e. *informed* blocking priced by `S`. So "content-dependent harm requires `|W| ≥ t`", "can block only blind", "zero whatever the correlation"
   (5(d)) and "its option is the exogenous one" hold only if `S ≥ ess sup D^F_{t*}` (as in 5(a)); otherwise the residual option is the `S`-priced one of item 66.
   Items 74 and 75 are the pre-`d` statements and are unaffected. Suggest adding the deposit condition to (c), (d) and to the limits paragraph.
6. **Counts.** The abstract, introduction and Section 9 say 66 statements; the development now audits 91 (66 + 19 requested + 6 helpers). Table 5 should add
   rows for Section 8: window feasibility as an instance of Theorem 2(a); the escrow-model lemmas; the zero-option, no-profitable-deviation and threshold arithmetic.

## Suggested update to the Lean section
Add Theorem 5 to Table 5: (a) the pre-`d` zero option and the `S`-penalized post-`d` option; (b) the no-profitable-deviation arithmetic; (c) the threshold
arithmetic with its `n = 1, 3` boundary cases; (d) `Z = 0` for equal information; and the window condition `γ ≤ Ω/ω` as an instance of Theorem 2(a). State explicitly that
hiding, pad determinism and sequentiality, solver parity, the escrow-set consensus and the execution rule are not formalized.

---

# Phase 5b (revised Theorem 5): Block 16

## Result
All 9 requested items (76-84) are proven. Full `lake build` succeeds (8944 jobs); no `sorry`, `admit` or `axiom` in the sources
(grep-checked). `AXIOMS.txt` now holds `#print axioms` for all 107 audited theorems (Phases 1-5: 91; Phase 5b: 9 requested + 7 extras).
The only axioms appearing anywhere are `propext`, `Classical.choice`, `Quot.sound` (11 purely arithmetic proofs use a subset).

**One requested statement was false as written (item 79) and was fixed minimally; see Deviation 1.**

## Imports (as asked: which I chose)
`Block16` imports `Optionality.Block11` (which brings `f1`, `cost`, `lucid_m1_iff_f1` from Blocks 10 and 11) and `Optionality.Block14`
(for `padLength`, used only by one extra). Both are narrow (no full `import Mathlib`), so `Block16` builds in 66 s.

## Theorems (all PROVEN)
| # | Name | Note |
|---|------|------|
| 76 | `cost_ge_of_nonempty` | |
| 77 | `cost_empty` | |
| 78 | `blind_profit_le` | |
| 79 | `blind_fee_naive` | **needs added hypothesis `p1 ≤ 1`**; `blind_fee_naive_needs_p1_le_one` is the checked counterexample |
| 80 | `blind_fee_f1` | via `lucid_m1_iff_f1` (item 34) and monotonicity in `pt` |
| 81 | `blind_plan_unprofitable` | def `blindProfit`; helper `blindProfit_empty` |
| 82 | `bsr_fail_needs_blocking_size` | helper `bsr_fail_iff` (the two forms of "fails") |
| 83 | `bsr_post_deadline_needs_one` | helper `bsr_cost_ge_S` (`k ≥ 1` withheld escrows cost `≥ S`) |
| 84 | `bsr_single_withhold_tight` | |

Extras (not requested): `ceil_two_thirds_strict_iff`, `pad_length_example_eleven`, `calib_f1_example`, plus the helpers above.

## Build time
Full `lake build`: 9 min 10 s wall-clock (cold cache). `Block16` 66 s; `Audit` 250 s.

## Deviations
1. **Item 79 is false without `p1 ≤ 1`; added.** The prompt lists `0 ≤ pt ≤ p1`, `0 ≤ Λ`, `0 ≤ ℓ`, `c ≥ f/F`, `F p1 Λ ≤ f` but not an upper bound on `p1`.
   Counterexample (all other hypotheses hold): `F = 2`, `pt = p1 = 2`, `Λ = 0`, `ℓ = 1`, `f = c = 0`: then `pt Λ - (1 - pt) ℓ - c = 1 > 0`.
   The failure is that `(1 - pt) ℓ` is negative when `pt > 1`. Added `p1 ≤ 1` (so `pt ≤ 1`); machine-checked as
   `blind_fee_naive_needs_p1_le_one`. Items 80 and 81 already have `p1 < 1`. In the paper this is automatic (the `p_t` are probabilities).
2. **78 and 80 carry the unused hypothesis `0 ≤ pt`** (named `_hpt0`): not needed, kept to match the prompt.
3. **81** uses a def `blindProfit k F f pt ℓ Λ R := if R = ∅ then -(k * f) else pt * Λ - (1 - pt) * ℓ - cost k F f R`
   (exactly the prompt's description); `blindProfit_empty` shows the `R = ∅` branch equals `-cost k F f ∅` via item 77.
4. **84** states `j = n - t`, `k = 1` as hypotheses (`hj`, `hk`) rather than substituting; `1 ≤ t` is unused (`_ht1`).
5. **82-84** are in natural-number form (`n < t + j + k`, `n + 1 ≤ t + w`); `bsr_fail_iff` proves the equivalence with
   `n - j - k < t` under `j + k ≤ n`, as requested.

## What is and is not formalized
- **Formalized:** the fee bound for a blind plan with a fixed reveal set (76-81), including both the naive bound `f ≥ F p1 Λ` and
  the `f1` bound under `ℓ ≥ f (1 - 1/F)`; the counting behind the deposit condition (82-84); that withholding `k ≥ 1` inconsistent
  escrows costs at least `S`; the strict/non-strict comparison of `⌈2n/3⌉` with the best threshold without blind release.
- **Not formalized:** that the executed reveal set is fixed at `d` and that the pattern is the same in every class (A3 and the
  protocol); the informal bound on the gain `g`; hiding, binding, determinism and sequentiality of pads; solver parity; consensus on
  the escrow set; the execution rule. The hardware latency gap remains an assumption (only the ratio `γ` appears).

## Observations on the revised Section 8 of paper.tex
1. **(i) Theorem 5(b) follows from items 76-81 together with item 67 (and item 64), up to the protocol facts above.**
   - "No deviation after `d` is profitable" is item 67 with `g ≤ S ≤ c`: `g ≤ S` is the hypothesis `S ≥ g`; `c ≥ S` comes from item 64
     (each withheld inconsistent escrow costs `S`) and item 83 (changing the executed set after `d` withholds at least one, `bsr_cost_ge_S`).
     67 proves deviation is never *strictly* profitable, which is what "no such change is profitable" needs.
   - "Same reveal set in every class" is the protocol fact (not formalized); the `R = ∅` case `-kf ≤ 0` is items 77, 81.
   - The `ℓ = 0` bound `Π ≤ p1 Λ - f/F`, hence `f ≥ F p1 Λ` suffices, is items 76, 78, 79. The step "`-ℓ - f/F ≤ -f` gives `ℓ ≥ f(1 - 1/F)`"
     is the hypothesis of item 80, and the chain `Π ≤ pt Λ - f((1 - pt) + pt/F)`, increasing in `pt`, non-positive iff `f ≥ f1(p1)`, is item 80 as proved
     (coefficient `Λ + f(1 - 1/F) ≥ 0`). All matches the paper's text step by step.
   - Informally, the general A2 ("a misdirected execution loses at least the fees it would save") already implies the single-commitment form:
     `ℓ ≥ |R| f (1 - 1/F) ≥ f (1 - 1/F)` for `|R| ≥ 1`; the paper may want to say so.
   - The needed `pt ≤ 1` is automatic in the paper (probabilities), so Theorem 5(b) itself is correct; only the prompt's item 79 lacked it.
2. **(ii) The proof of 5(c) matches items 82-84, and the theorem nowhere claims a cost above `S`.**
   Item 82 is "failure requires `|W| ≥ n - t + 1`"; item 83 is "if not already blocked at `d`, blocking after `d` has `k ≥ 1`, so cost `≥ S`";
   item 84 is the closing remark that `S` cannot be raised to `(n - t + 1) S` (with `j = n - t`, one withheld inconsistent escrow already blocks).
   I checked every place that states a cost: Theorem 5(a) ("at cost `S`"), 5(b) ("`S ≥ g`"), 5(c) ("cost at least `S`"), the limits paragraph ("the largest single gain"),
   the introduction ("sized to the largest single gain"), the abstract and the conclusion. None claims more than `S`.
   - **One small gap in the counting.** The proof defines `j` as the members of `W` with no escrow in `E`. But the proof of 5(a) also says that a *committed
     invalid value* is fixed as `⊥` at `d`, which is equally a blind choice at `d`. Suggest: "`j` members of `W` whose release value is already unavailable at `d`
     (no escrow in `E`, or an invalid committed value)". The counting (82-84) is unchanged.
   - The comparison sentence is exactly right: `ceil_two_thirds_strict_iff` proves that `⌈2n/3⌉` exceeds the harm size of *every* threshold without blind release iff `n = 2` or
     `n ≥ 4` (for `1 ≤ n`), and item 71 gives "never smaller"; equality is only at `n ∈ {1, 3}`.
3. **(iii) The revised Parameters paragraph is correct.** Margins `γmax = 5` (`ω = 2 s`, `Ω = 10 s`) and `11` (`ω = 1 s`, `Ω = 11 s`) for twelve-second slots, `2` and `5` for six-second
   slots, are `gmaxBSR_values` (item 61). `L = Ω νh` with `70 ns` is `1.43 × 10^8` for `Ω = 10 s` (item 62: in `(1.4, 1.5) × 10^8`) and `1.57 × 10^8` for `Ω = 11 s`
   (`pad_length_example_eleven`: in `(1.55, 1.6) × 10^8`, so "`1.6 × 10^8`" is right); "preparing one pad takes `Ω` seconds of one core" holds by definition of `L`. The 95th-percentile
   (`1.96 s < 2 s`) and median (`0.83 s < 1 s`, `> 1 s` fails the 95th) statements are consistent with the cited numbers (I did not check the citation itself). The abstract's "5 / 11" now matches.
4. **(iv) The new calibration sentence is arithmetically right but its conclusion needs the A2 assumption.** `f1(1/64) · 50 = 1280/1613 = 0.794` basis points with `F = 128`
   (`calib_f1_example`: in `(0.79, 0.8)`), which is below every exogenous fee in the table (smallest `f_{1%}` is `4.26` bp). I also recomputed the whole calibration table
   (all five rows: `s`, `V(0)`, `f_{1%}`, `f_{1%}/F`, `f_{0.1%}`, and the `$102` / `$4.70` figures) and it matches exactly.
   **But** `f1` is the bound only under the single-commitment form of A2 (`ℓ ≥ f(1 - 1/F)`). Without it the available bound is `F p1 Λ = 128 · 50/64 = 100` bp, which is *above*
   every exogenous fee in the table (largest `17.71` bp). So "the exogenous option becomes the binding constraint" holds under that assumption but is not established without it.
   The same applies to the abstract's "restores the single-commitment fee against probabilistic frontrunning for every cap", which Theorem 5(b) states conditionally. Suggest saying
   "under A2 with a single commitment" in the abstract and in the Calibration paragraph, or stating that without it the bound is `F p1 Λ`.
5. **Lean section.** It now says "91 theorems"; the development audits 107. It lists "the fee bound for fixed reveal sets in (b) and the counting argument behind the deposit condition in (c)" as
   not formalized; both are now formalized (items 76-84). Suggested replacement: add to the Theorem 5 row of Table 5 "fee bound for a fixed reveal set under both forms of A2 (`F p1 Λ` and `f1`);
   the counting `j + k ≤ w`, `n < t + j + k` behind the deposit condition and its tightness; strict comparison of `⌈2n/3⌉` with the best threshold (iff `n = 2` or `n ≥ 4`)"; and shorten the
   "not formalized" list to: hiding, binding, pad determinism and sequentiality, solver parity, escrow-set consensus, the execution rule, that the executed set is fixed at `d`
   with the same pattern in every class, and the informal bound on `g`.
