import Optionality.Block11
import Optionality.Block14

/-!
Block 16: the two arguments added to Theorem 5 of the revised Section 8.

Part 1 (Theorem 5(b)): the fee bound for a blind plan, whose executed reveal set is fixed at the
deadline and targets at most one class. Part 2 (Theorem 5(c)): the counting behind the deposit
condition. Imports are narrow: `Block11` (which brings `f1`, `cost`, `lucid_m1_iff_f1`) and
`Block14` (for `padLength`); neither loads full `Mathlib`.
-/

noncomputable section

set_option linter.deprecated false

namespace Optionality

/-! ### Theorem 5(b): fee bound for a fixed reveal set -/

/-- Block 16, item 76: any nonempty reveal set costs at least `f / F`. -/
theorem cost_ge_of_nonempty {k : ℕ} {F f : ℝ} (hF : 1 ≤ F) (hf : 0 ≤ f)
    {R : Finset (Fin k)} (hR : R.Nonempty) : f / F ≤ cost k F f R := by
  have hF0 : 0 < F := by linarith
  have h1 : 1 ≤ R.card := Finset.card_pos.2 hR
  have h2 : R.card ≤ k := by simpa using Finset.card_le_univ R
  have h1' : (1 : ℝ) ≤ R.card := by exact_mod_cast h1
  have h2' : (R.card : ℝ) ≤ k := by exact_mod_cast h2
  have h3 : 1 / F ≤ (R.card : ℝ) / F := div_le_div_of_nonneg_right h1' hF0.le
  have h4 : 1 / F ≤ ((k : ℝ) - R.card) + R.card / F := by linarith
  unfold cost
  calc f / F = f * (1 / F) := by ring
    _ ≤ f * (((k : ℝ) - R.card) + R.card / F) := mul_le_mul_of_nonneg_left h4 hf

/-- Block 16, item 77. -/
theorem cost_empty (k : ℕ) (F f : ℝ) : cost k F f ∅ = k * f := by
  unfold cost
  rw [Finset.card_empty]
  push_cast
  ring

/-- Block 16, item 78. -/
theorem blind_profit_le {pt ℓ Λ f F c : ℝ} (_hpt0 : 0 ≤ pt) (hpt1 : pt ≤ 1) (hℓ : 0 ≤ ℓ)
    (hc : f / F ≤ c) : pt * Λ - (1 - pt) * ℓ - c ≤ pt * Λ - f / F := by
  have := mul_nonneg (sub_nonneg.2 hpt1) hℓ
  linarith

/-- Block 16, item 79: without the misdirected-execution loss, `f ≥ F p1 Λ` suffices.
Needs `p1 ≤ 1`: for `p1 = pt = 2`, `Λ = 0`, `ℓ = 1`, `f = c = 0` the left side is `1 > 0`. -/
theorem blind_fee_naive {pt p1 ℓ Λ f F c : ℝ} (hF : 1 < F) (hp1 : p1 ≤ 1) (hpt0 : 0 ≤ pt)
    (hpt : pt ≤ p1) (hΛ : 0 ≤ Λ) (hℓ : 0 ≤ ℓ) (hc : f / F ≤ c) (hf : F * p1 * Λ ≤ f) :
    pt * Λ - (1 - pt) * ℓ - c ≤ 0 := by
  have hF0 : 0 < F := by linarith
  have h1 := blind_profit_le hpt0 (hpt.trans hp1) hℓ hc (Λ := Λ)
  have h2 : pt * Λ ≤ p1 * Λ := mul_le_mul_of_nonneg_right hpt hΛ
  have h3 : p1 * Λ ≤ f / F := by
    rw [le_div_iff₀ hF0]
    linarith
  linarith

/-- Machine-checked counterexample showing that item 79 needs `p1 ≤ 1`: all other hypotheses hold
for `F = 2`, `pt = p1 = 2`, `Λ = 0`, `ℓ = 1`, `f = c = 0`, yet the profit is `1 > 0`. -/
theorem blind_fee_naive_needs_p1_le_one :
    ∃ (pt p1 ℓ Λ f F c : ℝ), 1 < F ∧ 0 ≤ pt ∧ pt ≤ p1 ∧ 0 ≤ Λ ∧ 0 ≤ ℓ ∧ f / F ≤ c ∧
      F * p1 * Λ ≤ f ∧ ¬ (pt * Λ - (1 - pt) * ℓ - c ≤ 0) :=
  ⟨2, 2, 1, 0, 0, 2, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

/-- Block 16, item 80: with `ℓ ≥ f (1 - 1/F)` (A2 with a single commitment), `f ≥ f1(p1)` suffices. -/
theorem blind_fee_f1 {pt p1 ℓ Λ f F c : ℝ} (hF : 1 < F) (hp0 : 0 < p1) (hp1 : p1 < 1)
    (_hpt0 : 0 ≤ pt) (hpt : pt ≤ p1) (hΛ : 0 ≤ Λ) (hf0 : 0 ≤ f)
    (hℓ : f * (1 - 1 / F) ≤ ℓ) (hc : f / F ≤ c) (hf : f1 Λ F p1 ≤ f) :
    pt * Λ - (1 - pt) * ℓ - c ≤ 0 := by
  have hF0 : 0 < F := by linarith
  have hpt1 : pt ≤ 1 := hpt.trans hp1.le
  have hinv : 1 / F ≤ 1 := by rw [div_le_one hF0]; exact hF.le
  have h1 : (1 - pt) * (f * (1 - 1 / F)) ≤ (1 - pt) * ℓ :=
    mul_le_mul_of_nonneg_left hℓ (by linarith)
  have hlu := (lucid_m1_iff_f1 p1 Λ F f hp0 hp1.le hF).2 hf
  have hcoef : 0 ≤ Λ + f * (1 - 1 / F) := add_nonneg hΛ (mul_nonneg hf0 (by linarith))
  have h2 := mul_nonneg (sub_nonneg.2 hpt) hcoef
  simp only [div_eq_mul_inv] at h1 h2 hlu hc hℓ hinv ⊢
  nlinarith [h1, h2, hlu, hc]

/-- Profit of a blind plan whose executed reveal set is `R`: nothing executes if `R = ∅`;
otherwise gross `Λ` on the targeted class (probability `pt`), `-ℓ` on every other class,
minus the fee cost. -/
def blindProfit (k : ℕ) (F f pt ℓ Λ : ℝ) (R : Finset (Fin k)) : ℝ :=
  if R = ∅ then -((k : ℝ) * f) else pt * Λ - (1 - pt) * ℓ - cost k F f R

/-- For `R = ∅` the profit is minus the fee cost (item 77 ties the two descriptions together). -/
theorem blindProfit_empty (k : ℕ) (F f pt ℓ Λ : ℝ) :
    blindProfit k F f pt ℓ Λ ∅ = -cost k F f ∅ := by
  unfold blindProfit
  rw [if_pos rfl, cost_empty]

/-- Block 16, item 81: every blind plan is unprofitable once `f ≥ f1(p1)`, for every cap. -/
theorem blind_plan_unprofitable {k : ℕ} (R : Finset (Fin k)) {pt p1 ℓ Λ f F : ℝ} (hF : 1 < F)
    (hp0 : 0 < p1) (hp1 : p1 < 1) (hpt0 : 0 ≤ pt) (hpt : pt ≤ p1) (hΛ : 0 ≤ Λ) (hf0 : 0 ≤ f)
    (hℓ : f * (1 - 1 / F) ≤ ℓ) (hf : f1 Λ F p1 ≤ f) :
    blindProfit k F f pt ℓ Λ R ≤ 0 := by
  unfold blindProfit
  split_ifs with h
  · exact neg_nonpos.2 (mul_nonneg (Nat.cast_nonneg _) hf0)
  · exact blind_fee_f1 hF hp0 hp1 hpt0 hpt hΛ hf0 hℓ
      (cost_ge_of_nonempty hF.le hf0 (Finset.nonempty_iff_ne_empty.2 h)) hf

/-! ### Theorem 5(c): counting behind the deposit condition -/

/-- Execution fails iff `n - j - k < t`; the subtraction-free form is `n < t + j + k`. -/
theorem bsr_fail_iff {n t j k : ℕ} (h : j + k ≤ n) : n - j - k < t ↔ n < t + j + k := by
  omega

/-- Block 16, item 82: failure needs `|W| ≥ n - t + 1` (stated as `n + 1 ≤ t + w`). -/
theorem bsr_fail_needs_blocking_size {n t j k w : ℕ} (hjk : j + k ≤ w) (hfail : n < t + j + k) :
    n + 1 ≤ t + w := by
  omega

/-- Block 16, item 83: if the batch was not already blocked at the deadline, blocking after it
withholds at least one inconsistent escrow. -/
theorem bsr_post_deadline_needs_one {n t j k : ℕ} (hpre : t + j ≤ n) (hfail : n < t + j + k) :
    1 ≤ k := by
  omega

/-- Withholding `k ≥ 1` inconsistent escrows costs at least `S` (each costs `S`; item 64). -/
theorem bsr_cost_ge_S {k : ℕ} {S : ℝ} (hk : 1 ≤ k) (hS : 0 ≤ S) : S ≤ (k : ℝ) * S := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Block 16, item 84: a single withheld inconsistent escrow already blocks (so the cost bound `S`
cannot be raised to `(n - t + 1) * S`). -/
theorem bsr_single_withhold_tight {n t w j k : ℕ} (_ht1 : 1 ≤ t) (htn : t ≤ n)
    (hw : n + 1 ≤ t + w) (hj : j = n - t) (hk : k = 1) :
    j + k ≤ w ∧ t + j ≤ n ∧ n < t + j + k := by
  omega

/-! ### Supporting arithmetic for the revised text -/

/-- The threshold comparison in the revised 5(c): `⌈2n/3⌉ = (2n+2)/3` is strictly larger than the
smallest harmful coalition `min t' (n - t' + 1)` of *every* threshold `t'` exactly when `n = 2` or
`n ≥ 4` (for `1 ≤ n`). -/
theorem ceil_two_thirds_strict_iff {n : ℕ} (hn : 1 ≤ n) :
    (∀ t', 1 ≤ t' → t' ≤ n → min t' (n - t' + 1) < (2 * n + 2) / 3) ↔ (n = 2 ∨ 4 ≤ n) := by
  constructor
  · intro h
    by_contra hne
    have h13 : n = 1 ∨ n = 3 := by omega
    rcases h13 with rfl | rfl
    · have := h 1 le_rfl le_rfl
      omega
    · have := h 2 (by norm_num) (by norm_num)
      omega
  · rintro hn' t' h1 h2
    omega

/-- Revised Parameters paragraph: `70 ns` per step and `Ω = 11 s` give `L ≈ 1.6 × 10^8`
(the case `Ω = 10 s` is `pad_length_example`). -/
theorem pad_length_example_eleven :
    1.55 * 10 ^ 8 < padLength 11 (1 / (70 * 10 ^ (-9 : ℤ))) ∧
    padLength 11 (1 / (70 * 10 ^ (-9 : ℤ))) < 1.6 * 10 ^ 8 := by
  unfold padLength
  constructor <;> norm_num

/-- Revised calibration sentence: with `F = 128`, `p1 = 1/64` and `Λ = 50` basis points,
`f1 = 1280/1613 ≈ 0.79`, i.e. about `0.8` basis points. -/
theorem calib_f1_example :
    f1 50 128 (1 / 64) = 1280 / 1613 ∧ 0.79 < f1 50 128 (1 / 64) ∧
    f1 50 128 (1 / 64) < 0.8 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [f1]

end Optionality
