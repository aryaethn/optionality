import Optionality.Block6

open Finset BigOperators

noncomputable section

set_option linter.deprecated false

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Optionality

/-- Two outcomes, mass `1/2` each. -/
def P2 : FinProb Bool where
  μ _ := 1 / 2
  pos _ := by norm_num
  sum_one := by simp [Fintype.sum_bool]

/-- `D = ±1`. -/
def D2 : Bool → ℝ := fun b => if b then 1 else -1

/-- `πG` constant. -/
def πG2 : Bool → Unit := fun _ => ()

/-- `πF = D`. -/
def πF2 : Bool → ℝ := D2

theorem cond_G2 (ω : Bool) : cond P2 πG2 D2 ω = 0 := by
  simp [cond, πG2, P2, D2]

theorem cell_F2 (ω : Bool) : cell πF2 ω = {ω} := by
  ext x
  rw [mem_cell, Finset.mem_singleton]
  cases x <;> cases ω <;> norm_num [πF2, D2]

theorem cond_F2 (ω : Bool) : cond P2 πF2 D2 ω = D2 ω := by
  rw [cond_eq]
  unfold mass
  rw [cell_F2, Finset.sum_singleton, Finset.sum_singleton]
  show (1 / 2 * D2 ω) / (1 / 2) = D2 ω
  ring

/-- Block 7, item 18. -/
theorem erratum_example :
    Vendo P2 (fun _ : Bool => True) D2 πF2 πG2 = 1 / 2 ∧
    ¬ ∃ ω, (0 < cond P2 πF2 D2 ω ∧ cond P2 πG2 D2 ω < 0) ∨
           (cond P2 πF2 D2 ω < 0 ∧ 0 < cond P2 πG2 D2 ω) := by
  refine ⟨?_, ?_⟩
  · unfold Vendo val
    rw [ZR_true]
    simp only [cond_F2, cond_G2]
    simp [ex, P2, D2, pos]
  · rintro ⟨ω, h⟩
    rw [cond_F2, cond_G2] at h
    rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd h (lt_irrefl 0)

/-- The corrected criterion (non-strict on the `πG` side) does fire on the same example. -/
theorem erratum_example_corrected :
    ∃ ω, (0 < cond P2 πF2 D2 ω ∧ cond P2 πG2 D2 ω ≤ 0) ∨
         (cond P2 πF2 D2 ω < 0 ∧ 0 ≤ cond P2 πG2 D2 ω) :=
  ⟨true, Or.inl ⟨by rw [cond_F2]; simp [D2], by rw [cond_G2]⟩⟩

/-- Block 7, item 19. -/
theorem lucid_m1_deterrence (p G F f : ℝ) (hp0 : 0 < p) (_hp1 : p < 1) (hF : 1 < F)
    (_hf : 0 ≤ f) :
    p * (G - f / F) - (1 - p) * f ≤ 0 ↔ p * G / ((1 - p) + p / F) ≤ f := by
  have hF0 : 0 < F := by linarith
  have hd : 0 < (1 - p) + p / F := by
    have : 0 < p / F := div_pos hp0 hF0
    linarith
  rw [div_le_iff₀ hd]
  have e : p * (G - f / F) - (1 - p) * f = p * G - f * ((1 - p) + p / F) := by ring
  rw [e]
  constructor <;> intro h <;> linarith

end Optionality
