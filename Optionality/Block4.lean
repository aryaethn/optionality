import Optionality.Block3

open Finset BigOperators

noncomputable section

set_option linter.deprecated false

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Optionality

variable {Ω : Type*} [Fintype Ω]
variable (P : FinProb Ω)
variable {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

/-- `ZR ω = 1_R(ω) * D ω`. -/
def ZR (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) : Ω → ℝ :=
  fun ω => (if R ω then (1 : ℝ) else 0) * D ω

/-- Value of acting on information `π`. -/
def val (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) (π : Ω → ι) : ℝ :=
  ex P (fun ω => pos (cond P π (ZR R D) ω))

def Vtot (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) (πF : Ω → ι) (π0 : Ω → ν) : ℝ :=
  val P R D πF - val P R D π0

def Vexo (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) (πG : Ω → κ) (π0 : Ω → ν) : ℝ :=
  val P R D πG - val P R D π0

def Vendo (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) (πF : Ω → ι) (πG : Ω → κ) : ℝ :=
  val P R D πF - val P R D πG

/-- Block 4, item 10. Stated for an arbitrary information structure `π`, so it applies to each of
`πG`, `πF`, `π0` (which live on different label types). -/
theorem thmA_b_value (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) (π : Ω → ι) :
    (∀ Y : Ω → ℝ, Meas π Y → (∀ ω, Y ω = 0 ∨ Y ω = 1) →
        ex P (fun ω => Y ω * ZR R D ω) ≤ val P R D π) ∧
    ∃ Y : Ω → ℝ, Meas π Y ∧ (∀ ω, Y ω = 0 ∨ Y ω = 1) ∧
        ex P (fun ω => Y ω * ZR R D ω) = val P R D π := by
  refine ⟨fun Y hY h01 => choice_le P hY h01 (ZR R D), ?_⟩
  obtain ⟨hm, h01, heq⟩ := choice_attained P π (ZR R D)
  exact ⟨_, hm, h01, heq⟩

/-- Block 4, item 11. -/
theorem thmA_b_endo_nonneg {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) :
    0 ≤ Vendo P R D πF πG :=
  sub_nonneg.2 (jensen_pos P hFG (ZR R D))

/-- Block 4, item 12. -/
theorem thmA_b_endo_formula {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    {R : Ω → Prop} [DecidablePred R] (hR : Meas πG (fun ω => if R ω then (1 : ℝ) else 0))
    (D : Ω → ℝ) :
    cond P πF (ZR R D) = (fun ω => (if R ω then (1 : ℝ) else 0) * cond P πF D ω) ∧
    cond P πG (ZR R D) = (fun ω => (if R ω then (1 : ℝ) else 0) * cond P πG D ω) :=
  ⟨cond_mul_meas P (meas_of_refines hFG hR) D, cond_mul_meas P hR D⟩

/-- Block 4, item 13. -/
theorem thmA_b_endo_pos_iff {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    {R : Ω → Prop} [DecidablePred R] (hR : Meas πG (fun ω => if R ω then (1 : ℝ) else 0))
    (D : Ω → ℝ) :
    0 < Vendo P R D πF πG ↔
      ∃ ω, R ω ∧ ((0 < cond P πF D ω ∧ cond P πG D ω ≤ 0) ∨
                  (cond P πF D ω < 0 ∧ 0 ≤ cond P πG D ω)) := by
  obtain ⟨hF, hG⟩ := thmA_b_endo_formula P hFG hR D
  have hFω : ∀ ω, cond P πF (ZR R D) ω = (if R ω then (1 : ℝ) else 0) * cond P πF D ω :=
    fun ω => congr_fun hF ω
  have hGω : ∀ ω, cond P πG (ZR R D) ω = (if R ω then (1 : ℝ) else 0) * cond P πG D ω :=
    fun ω => congr_fun hG ω
  unfold Vendo val
  rw [sub_pos, jensen_pos_strict_iff P hFG (ZR R D)]
  constructor
  · rintro ⟨ω, h⟩
    rw [hFω ω, hGω ω] at h
    by_cases hr : R ω
    · simp only [if_pos hr, one_mul] at h
      exact ⟨ω, hr, h⟩
    · simp [hr] at h
  · rintro ⟨ω, hr, h⟩
    refine ⟨ω, ?_⟩
    rw [hFω ω, hGω ω]
    simpa [hr] using h

/-- Block 4, item 14 (timing criterion). -/
theorem cor_timing {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG) (hGF : Refines πG πF)
    (R : Ω → Prop) [DecidablePred R] (D : Ω → ℝ) :
    Vendo P R D πF πG = 0 := by
  have h1 := jensen_pos P hFG (ZR R D)
  have h2 := jensen_pos P hGF (ZR R D)
  unfold Vendo val
  linarith

end Optionality
