import Optionality.Block1

open Finset BigOperators

noncomputable section

set_option linter.deprecated false

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Optionality

variable {Ω : Type*} [Fintype Ω]
variable (P : FinProb Ω)
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- Block 2, item 6 (Lemma 1, upper bound). -/
theorem choice_le {π : Ω → ι} {Y : Ω → ℝ} (hY : Meas π Y) (h01 : ∀ ω, Y ω = 0 ∨ Y ω = 1)
    (Z : Ω → ℝ) :
    ex P (fun ω => Y ω * Z ω) ≤ ex P (fun ω => pos (cond P π Z ω)) := by
  rw [ex_mul_cond P hY Z]
  unfold ex
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (P.pos ω).le
  beta_reduce
  unfold pos
  rcases h01 ω with h | h
  · rw [h, zero_mul]; exact le_max_right _ _
  · rw [h, one_mul]; exact le_max_left _ _

/-- Block 2, item 7 (Lemma 1, attainment). -/
theorem choice_attained (π : Ω → ι) (Z : Ω → ℝ) :
    Meas π (fun ω => if 0 < cond P π Z ω then (1 : ℝ) else 0) ∧
    (∀ ω, (if 0 < cond P π Z ω then (1 : ℝ) else 0) = 0 ∨
          (if 0 < cond P π Z ω then (1 : ℝ) else 0) = 1) ∧
    ex P (fun ω => (if 0 < cond P π Z ω then (1 : ℝ) else 0) * Z ω)
      = ex P (fun ω => pos (cond P π Z ω)) := by
  have hm : Meas π (fun ω => if 0 < cond P π Z ω then (1 : ℝ) else 0) := by
    intro a b h
    simp only [cond_meas P π Z a b h]
  refine ⟨hm, fun ω => ?_, ?_⟩
  · by_cases h : 0 < cond P π Z ω
    · right; exact if_pos h
    · left; exact if_neg h
  · rw [ex_mul_cond P hm Z]
    unfold ex
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    beta_reduce
    unfold pos
    by_cases h : 0 < cond P π Z ω
    · rw [if_pos h, one_mul]; exact (max_eq_left h.le).symm
    · rw [if_neg h, zero_mul]; exact (max_eq_right (not_lt.1 h)).symm

end Optionality
