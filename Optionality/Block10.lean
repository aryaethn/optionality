import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Block 10: real arithmetic behind Theorem C (multi-commitment deterrence in LUCID).
-/

noncomputable section

set_option linter.deprecated false

namespace Optionality

/-- LUCID's single-commitment threshold, f_1(p) = p G / ((1 - p) + p / F). -/
def f1 (G F p : ℝ) : ℝ := p * G / ((1 - p) + p / F)

/-- Selector (fee-inversion) threshold, f_inv(p) = p G / (p (1 + 1/F) + 2 (1 - p) / F). -/
def finv (G F p : ℝ) : ℝ := p * G / (p * (1 + 1 / F) + 2 * (1 - p) / F)

/-- Block 10, item 34. Needs `p ≤ 1` (see REPORT: false for `p > 1`). -/
theorem lucid_m1_iff_f1 (p G F f : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hF : 1 < F) :
    p * (G - f / F) - (1 - p) * f ≤ 0 ↔ f1 G F p ≤ f := by
  have hF0 : 0 < F := by linarith
  have hd : 0 < (1 - p) + p / F := by
    have : 0 < p / F := div_pos hp hF0
    linarith
  unfold f1
  rw [div_le_iff₀ hd]
  have e : p * (G - f / F) - (1 - p) * f = p * G - f * ((1 - p) + p / F) := by ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- Block 10, item 35. -/
theorem selector_profit_pos_iff (p G F f : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hF : 0 < F) :
    0 < p * (G - f * (1 + 1 / F)) - (1 - p) * (2 * f / F) ↔ f < finv G F p := by
  have he : 0 < p * (1 + 1 / F) + 2 * (1 - p) / F := by
    have h1 : 0 < p * (1 + 1 / F) := by positivity
    have h2 : 0 ≤ 2 * (1 - p) / F := div_nonneg (by linarith) hF.le
    linarith
  unfold finv
  rw [lt_div_iff₀ he]
  have e : p * (G - f * (1 + 1 / F)) - (1 - p) * (2 * f / F)
      = p * G - f * (p * (1 + 1 / F) + 2 * (1 - p) / F) := by ring
  rw [e]
  constructor <;> intro h <;> linarith

/-- Block 10, item 36. -/
theorem finv_ge_half_iff (G F p : ℝ) (hG : 0 < G) (hF : 0 < F) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    G / 2 ≤ finv G F p ↔ 2 / (F + 1) ≤ p := by
  have heq : p * (1 + 1 / F) + 2 * (1 - p) / F = p + (2 - p) / F := by ring
  have h2p : 0 < (2 - p) / F := div_pos (by linarith) hF
  have he : 0 < p * (1 + 1 / F) + 2 * (1 - p) / F := by rw [heq]; linarith
  unfold finv
  rw [le_div_iff₀ he, div_le_iff₀ (by linarith : 0 < F + 1), heq]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have h3 : p < (2 - p) / F := by
      rw [lt_div_iff₀ hF]; nlinarith
    nlinarith [mul_pos hG (sub_pos.2 h3)]
  · intro h
    have h3 : (2 - p) / F ≤ p := by
      rw [div_le_iff₀ hF]; nlinarith
    nlinarith [mul_nonneg hG.le (sub_nonneg.2 h3)]

/-- Block 10, item 37. -/
theorem upper_eq_f1_div (p G F : ℝ) (hp : 0 < p) :
    G / ((1 - p) + p / F) = f1 G F p / p := by
  unfold f1
  rw [div_div, mul_comm ((1 - p) + p / F) p, mul_div_mul_left _ _ hp.ne']

/-- Block 10, item 38. -/
theorem table_C :
    finv 1 128 (1 / 64) = 128 / 255 ∧ f1 1 128 (1 / 64) = 128 / 8065 ∧
    finv 1 128 (1 / 64) / f1 1 128 (1 / 64) = 8065 / 255 ∧ 1 / 2 < finv 1 128 (1 / 64) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [finv, f1]

end Optionality
