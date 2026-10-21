import Optionality.Basic

open Finset BigOperators

noncomputable section

set_option linter.deprecated false

namespace Optionality

variable {Ω : Type*} [Fintype Ω]
variable (P : FinProb Ω)

/-- Block 5, item 15 (Theorem A(a), finite version). -/
theorem thmA_a (X Xp : Ω → ℝ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (hXp : ∀ ω, Xp ω = 0 ∨ Xp ω = 1)
    (Γ : Ω → Prop) [DecidablePred Γ] (D : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hD : ∀ ω, |D ω| ≤ B) (hΓ : ∀ ω, Γ ω → X ω = Xp ω) :
    ex P (fun ω => (1 - X ω) * D ω) - ex P (fun ω => (1 - Xp ω) * D ω)
      ≤ B * ∑ ω ∈ univ.filter (fun ω => ¬ Γ ω), P.μ ω := by
  unfold ex
  rw [← Finset.sum_sub_distrib, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hg : Γ ω
  · simp [hg, hΓ ω hg]
  · rw [if_pos hg]
    have hμ := (P.pos ω).le
    have hDω := abs_le.1 (hD ω)
    have h1 := mul_le_mul_of_nonneg_left hDω.2 hμ
    have h2 := mul_le_mul_of_nonneg_left hDω.1 hμ
    have h3 := mul_nonneg hB hμ
    show P.μ ω * ((1 - X ω) * D ω) - P.μ ω * ((1 - Xp ω) * D ω) ≤ B * P.μ ω
    rcases hX ω with h | h <;> rcases hXp ω with h' | h' <;> rw [h, h'] <;> nlinarith

end Optionality
