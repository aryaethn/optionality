import Optionality.Block12
import Optionality.Block13

/-!
Block 15: the escrow model and the formal guarantees of Theorem 5 (blind simultaneous release).

Formalized here: what a releaser can still control after the deadline (items 63, 64), the
zero-option statements (65, 66, 75), the no-profitable-deviation arithmetic (67, 68) and the
committee-threshold arithmetic (69 to 74). Not formalized: hiding of escrows, determinism and
sequentiality of pads, the solver-parity assumption, consensus on the escrow set, the execution rule.
-/

open Finset BigOperators

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Optionality

/-! ### Escrow model -/

inductive Action
  | reveal
  | withhold
  deriving DecidableEq

/-- What the commitment binds (`com`) and what forced opening of the pad yields (`pad`). -/
structure Escrow (V : Type*) where
  com : V
  pad : V

/-- Outcome of a releaser's post-deadline action: the value used (`none` = not executed) and the
penalty paid. Revealing must match the commitment (binding). Withholding triggers forced opening:
a consistent pad yields the committed value; an inconsistent pad is detected by recomputation,
slashed, and yields `none`. -/
def outcome {V : Type*} [DecidableEq V] (e : Escrow V) (a : Action) (S : ℝ) : Option V × ℝ :=
  match a with
  | .reveal => (some e.com, 0)
  | .withhold => if e.pad = e.com then (some e.com, 0) else (none, S)

/-- Block 15, item 63: a consistent releaser has no post-deadline control. -/
theorem consistent_no_control {V : Type*} [DecidableEq V] (e : Escrow V) (S : ℝ)
    (h : e.pad = e.com) :
    outcome e Action.reveal S = outcome e Action.withhold S := by
  simp [outcome, h]

/-- Block 15, item 64: the only post-deadline control of an inconsistent releaser is
non-execution at cost `S`. -/
theorem inconsistent_withhold_costs {V : Type*} [DecidableEq V] (e : Escrow V) (S : ℝ)
    (h : e.pad ≠ e.com) :
    outcome e Action.withhold S = (none, S) ∧ outcome e Action.reveal S = (some e.com, 0) := by
  simp [outcome, h]

/-! ### Theorem 5(a) and 5(d): zero options -/

variable {Ω : Type*} [Fintype Ω]
variable (P : FinProb Ω)
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Block 15, item 65: when the mechanism has released nothing at the decision time
(`πF` and `πG` carry the same information), the endogenous option is zero for every event `R`.
This is `cor_timing`. -/
theorem thmBSR_a_pre {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG) (hGF : Refines πG πF)
    {R : Ω → Prop} [DecidablePred R]
    (_hR : Meas πG (fun ω => if R ω then (1 : ℝ) else 0)) (D : Ω → ℝ) :
    Vendo P R D πF πG = 0 :=
  cor_timing P hFG hGF R D

/-- Block 15, item 66: the post-deadline option of a releaser with an inconsistent escrow is the
penalized option of Block 13 (penalty `S`); it vanishes if `S` bounds the conditional payoff
`D^F` (`πF` is the information at the *post-deadline* decision time). -/
theorem thmBSR_a_post {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG) {D : Ω → ℝ} {S : ℝ}
    (hD : ∀ ω', cond P πF D ω' ≤ S) :
    Vendo P (fun _ : Ω => True) (fun ω' => D ω' - S) πF πG = 0 :=
  deterrence_zero_of_cond_le P hFG hD

/-- With mutually refining information the conditional expectations coincide. -/
theorem cond_eq_of_equiv {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    (hGF : Refines πG πF) (D : Ω → ℝ) : cond P πF D = cond P πG D := by
  have h1 := cond_cond_of_refines P hFG D
  have h2 : cond P πG (cond P πF D) = cond P πF D :=
    cond_of_meas P (meas_of_refines hGF (cond_meas P πF D))
  exact h2.symm.trans h1

/-- With equal information the conditional endogenous option `Z` of Corollary 4 vanishes. -/
theorem Zopt_zero_of_equiv {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    (hGF : Refines πG πF) (D : Ω → ℝ) : ∀ ω, Zopt P πF πG D ω = 0 := by
  intro ω
  unfold Zopt
  rw [cond_eq_of_equiv P hFG hGF D]
  have : (fun ω => pos (cond P πG D ω) - pos (cond P πG D ω)) = fun _ => (0 : ℝ) := by
    funext ω; ring
  rw [this, congr_fun (cond_const P πG 0) ω]

/-- Block 15, item 75 (fallback key escrowed in the same window): `Z = 0`, hence the hybrid
endogenous option is zero for *every* outage event `R`, whatever its correlation with the value.
(`thmBSR_a_pre` is the second conjunct for one fixed `R`; this adds the statement about `Z`.) -/
theorem thmBSR_d {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG) (hGF : Refines πG πF)
    (D : Ω → ℝ) :
    (∀ ω, Zopt P πF πG D ω = 0) ∧
    ∀ (R : Ω → Prop) [DecidablePred R],
      Meas πG (fun ω => if R ω then (1 : ℝ) else 0) → Vendo P R D πF πG = 0 :=
  ⟨Zopt_zero_of_equiv P hFG hGF D, fun R _ hR => thmBSR_a_pre P hFG hGF hR D⟩

/-! ### Theorem 5(b): no profitable deviation after the deadline -/

/-- Block 15, item 67: if the deposit `S` covers every gain from changing the executed set and
every deviation costs at least `S`, deviating never raises the expected payoff. -/
theorem bsr_no_profitable_deviation {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    (base g c : ι → ℝ) (dev : ι → Bool) (S : ℝ)
    (h : ∀ t, dev t = true → g t ≤ S ∧ S ≤ c t) :
    ∑ t, p t * (if dev t then base t + g t - c t else base t) ≤ ∑ t, p t * base t := by
  refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (hp t)
  by_cases hd : dev t = true
  · rw [if_pos hd]
    obtain ⟨h1, h2⟩ := h t hd
    linarith
  · rw [if_neg hd]

/-- Block 15, item 68: with no deviation the expected payoff is that of the executed set fixed at
the deadline (`base`), which does not depend on the realized class. -/
theorem bsr_blind_profit_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (base g c : ι → ℝ)
    (dev : ι → Bool) (hdev : ∀ t, dev t = false) :
    ∑ t, p t * (if dev t then base t + g t - c t else base t) = ∑ t, p t * base t := by
  simp [hdev]

/-! ### Theorem 5(c): threshold comparison -/

/-- `⌈2n/3⌉`. -/
def tBSR (n : ℕ) : ℕ := (2 * n + 2) / 3

/-- Block 15, item 69. -/
theorem tBSR_ceil (n : ℕ) : 2 * n ≤ 3 * tBSR n ∧ 3 * tBSR n < 2 * n + 3 := by
  unfold tBSR; omega

/-- Block 15, item 70. -/
theorem tBSR_le {n : ℕ} (hn : 1 ≤ n) : 1 ≤ tBSR n ∧ tBSR n ≤ n := by
  unfold tBSR; omega

/-- Block 15, item 71: blind release with threshold `⌈2n/3⌉` never does worse than any threshold
without blind release. -/
theorem tBSR_ge_minharm {n t' : ℕ} (ht1 : 1 ≤ t') (htn : t' ≤ n) :
    min t' (n - t' + 1) ≤ tBSR n := by
  have := min_harm_le ht1 htn
  unfold tBSR; omega

/-- Block 15, item 72: strictly better from `n = 4` on (at `n = 3` both equal `2`). -/
theorem tBSR_gt_minharm {n t' : ℕ} (hn : 4 ≤ n) (ht1 : 1 ≤ t') (htn : t' ≤ n) :
    min t' (n - t' + 1) < tBSR n := by
  have := min_harm_le ht1 htn
  unfold tBSR; omega

/-- Block 15, item 73: coalition sizes that can block but, under blind release, only blindly. -/
theorem tBSR_blocking_only_range {n : ℕ} (hn : n = 2 ∨ 4 ≤ n) :
    n - tBSR n + 1 < tBSR n := by
  unfold tBSR; omega

/-- Block 15, item 73 (boundary): at `n = 3` the range is empty. -/
theorem tBSR_blocking_only_range_three : 3 - tBSR 3 + 1 = tBSR 3 ∧ tBSR 3 = 2 := by
  unfold tBSR; omega

/-- The range `n - t + 1 ≤ |W| < t` for `t = tBSR n` is nonempty exactly for `n = 2` and `n ≥ 4`
(empty for `n = 0, 1, 3`). -/
theorem tBSR_blocking_range_iff (n : ℕ) :
    n - tBSR n + 1 < tBSR n ↔ (n = 2 ∨ 4 ≤ n) := by
  unfold tBSR; omega

/-- Block 15, item 74: a coalition holding only its own `w < t` shares before the deadline
(honest shares are escrowed and unopened) cannot reconstruct. -/
theorem below_threshold_cannot_decrypt {t w held : ℕ} (hheld : held = w) (hw : w < t) :
    ¬ t ≤ held := by
  omega

end Optionality
