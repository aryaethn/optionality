import Optionality.Block5

open Finset BigOperators

noncomputable section

set_option linter.deprecated false

namespace Optionality

variable {Ω : Type*} [Fintype Ω]
variable (P : FinProb Ω)

/-- Block 8, item 20 (union bound on the failure masses). -/
theorem mass_not_and_le (Γ₁ Γ₂ : Ω → Prop) [DecidablePred Γ₁] [DecidablePred Γ₂] :
    ∑ ω ∈ univ.filter (fun ω => ¬ (Γ₁ ω ∧ Γ₂ ω)), P.μ ω ≤
      (∑ ω ∈ univ.filter (fun ω => ¬ Γ₁ ω), P.μ ω) +
        ∑ ω ∈ univ.filter (fun ω => ¬ Γ₂ ω), P.μ ω := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h := (P.pos ω).le
  by_cases ha : Γ₁ ω <;> by_cases hb : Γ₂ ω <;> simp [ha, hb] <;> linarith

/-- Block 8, item 21 (Theorem A(a), finite version, two good events). -/
theorem thmA_a_two_events (X Xp Xbar : Ω → ℝ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1)
    (hXp : ∀ ω, Xp ω = 0 ∨ Xp ω = 1) (_hXbar : ∀ ω, Xbar ω = 0 ∨ Xbar ω = 1)
    (Γσ Γp : Ω → Prop) [DecidablePred Γσ] [DecidablePred Γp] (D : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hD : ∀ ω, |D ω| ≤ B) (hσ : ∀ ω, Γσ ω → X ω = Xbar ω) (hp : ∀ ω, Γp ω → Xp ω = Xbar ω) :
    ex P (fun ω => (1 - X ω) * D ω) - ex P (fun ω => (1 - Xp ω) * D ω)
      ≤ B * ((∑ ω ∈ univ.filter (fun ω => ¬ Γσ ω), P.μ ω) +
              ∑ ω ∈ univ.filter (fun ω => ¬ Γp ω), P.μ ω) := by
  have h := thmA_a P X Xp hX hXp (fun ω => Γσ ω ∧ Γp ω) D B hB hD
    (fun ω hω => (hσ ω hω.1).trans (hp ω hω.2).symm)
  exact h.trans (mul_le_mul_of_nonneg_left (mass_not_and_le P Γσ Γp) hB)

/-- Block 8, item 22: the special case `Γσ = Γp = Γ`; no factor 2. -/
theorem thmA_a_same_event (X Xp Xbar : Ω → ℝ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1)
    (hXp : ∀ ω, Xp ω = 0 ∨ Xp ω = 1) (_hXbar : ∀ ω, Xbar ω = 0 ∨ Xbar ω = 1)
    (Γ : Ω → Prop) [DecidablePred Γ] (D : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hD : ∀ ω, |D ω| ≤ B) (hσ : ∀ ω, Γ ω → X ω = Xbar ω) (hp : ∀ ω, Γ ω → Xp ω = Xbar ω) :
    ex P (fun ω => (1 - X ω) * D ω) - ex P (fun ω => (1 - Xp ω) * D ω)
      ≤ B * ∑ ω ∈ univ.filter (fun ω => ¬ Γ ω), P.μ ω :=
  thmA_a P X Xp hX hXp Γ D B hB hD (fun ω hω => (hσ ω hω).trans (hp ω hω).symm)

end Optionality
