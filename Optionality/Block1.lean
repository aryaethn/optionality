import Optionality.Basic

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

/-- The cell of the partition induced by `π` containing `ω`. -/
def cell (π : Ω → ι) (ω : Ω) : Finset Ω := univ.filter (fun ω' => π ω' = π ω)

/-- Probability mass of a cell. -/
def mass (π : Ω → ι) (ω : Ω) : ℝ := ∑ x ∈ cell π ω, P.μ x

theorem mem_cell {π : Ω → ι} {ω ω' : Ω} : ω' ∈ cell π ω ↔ π ω' = π ω := by
  simp [cell]

theorem self_mem_cell {π : Ω → ι} (ω : Ω) : ω ∈ cell π ω := mem_cell.2 rfl

theorem cell_congr {π : Ω → ι} {ω ω₁ : Ω} (h : π ω = π ω₁) : cell π ω = cell π ω₁ := by
  ext x; simp [mem_cell, h]

theorem mass_pos (π : Ω → ι) (ω : Ω) : 0 < mass P π ω :=
  Finset.sum_pos (fun x _ => P.pos x) ⟨ω, self_mem_cell ω⟩

theorem mass_congr {π : Ω → ι} {ω ω₁ : Ω} (h : π ω = π ω₁) : mass P π ω = mass P π ω₁ := by
  simp only [mass, cell_congr h]

theorem cond_eq (π : Ω → ι) (Z : Ω → ℝ) (ω : Ω) :
    cond P π Z ω = (∑ ω' ∈ cell π ω, P.μ ω' * Z ω') / mass P π ω := rfl

theorem sum_cell_swap (π : Ω → ι) (g : Ω → Ω → ℝ) :
    ∑ ω, ∑ ω' ∈ cell π ω, g ω ω' = ∑ ω', ∑ ω ∈ cell π ω', g ω ω' := by
  simp only [cell, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω' _ => Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : π ω = π ω'
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun e => h e.symm)]

/-- Sum over a cell as an expectation of an indicator. -/
theorem ex_ind (π : Ω → ι) (ω₀ : Ω) (f : Ω → ℝ) :
    ex P (fun x => (if π x = π ω₀ then (1 : ℝ) else 0) * f x) = ∑ x ∈ cell π ω₀, P.μ x * f x := by
  simp only [ex, cell, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : π x = π ω₀ <;> simp [h]

theorem meas_ind (π : Ω → ι) (ω₀ : Ω) :
    Meas π (fun x => if π x = π ω₀ then (1 : ℝ) else 0) := by
  intro a b h
  simp [h]

theorem meas_of_refines {πF : Ω → ι} {πG : Ω → κ} {Y : Ω → ℝ} (h : Refines πF πG)
    (hY : Meas πG Y) : Meas πF Y :=
  fun a b hab => hY a b (h a b hab)

/-! ### Block 1 -/

/-- Block 1, item 1. -/
theorem cond_meas (π : Ω → ι) (Z : Ω → ℝ) : Meas π (cond P π Z) := by
  intro ω ω' h
  simp only [cond_eq, cell_congr h, mass_congr P h]

/-- Block 1, item 3. -/
theorem ex_mul_cond {π : Ω → ι} {Y : Ω → ℝ} (hY : Meas π Y) (Z : Ω → ℝ) :
    ex P (fun ω => Y ω * Z ω) = ex P (fun ω => Y ω * cond P π Z ω) := by
  have h1 : ∀ ω, P.μ ω * (Y ω * cond P π Z ω)
      = ∑ ω' ∈ cell π ω, (P.μ ω * Y ω / mass P π ω) * (P.μ ω' * Z ω') := by
    intro ω
    rw [← Finset.mul_sum, cond_eq]
    ring
  have h2 : ∀ ω', ∑ ω ∈ cell π ω', (P.μ ω * Y ω / mass P π ω) * (P.μ ω' * Z ω')
      = P.μ ω' * (Y ω' * Z ω') := by
    intro ω'
    have hM : mass P π ω' ≠ 0 := (mass_pos P π ω').ne'
    have h3 : ∀ ω ∈ cell π ω', (P.μ ω * Y ω / mass P π ω) * (P.μ ω' * Z ω')
        = P.μ ω * ((Y ω' / mass P π ω') * (P.μ ω' * Z ω')) := by
      intro ω hω
      have hπ := mem_cell.1 hω
      rw [hY ω ω' hπ, mass_congr P hπ]
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_mul]
    have : ∑ ω ∈ cell π ω', P.μ ω = mass P π ω' := rfl
    rw [this]
    field_simp
  calc ex P (fun ω => Y ω * Z ω)
      = ∑ ω', P.μ ω' * (Y ω' * Z ω') := rfl
    _ = ∑ ω', ∑ ω ∈ cell π ω', (P.μ ω * Y ω / mass P π ω) * (P.μ ω' * Z ω') :=
        Finset.sum_congr rfl fun ω' _ => (h2 ω').symm
    _ = ∑ ω, ∑ ω' ∈ cell π ω, (P.μ ω * Y ω / mass P π ω) * (P.μ ω' * Z ω') :=
        (sum_cell_swap π _).symm
    _ = ex P (fun ω => Y ω * cond P π Z ω) :=
        Finset.sum_congr rfl fun ω _ => (h1 ω).symm

/-- Block 1, item 2 (tower property). -/
theorem ex_cond (π : Ω → ι) (Z : Ω → ℝ) : ex P (cond P π Z) = ex P Z := by
  have := ex_mul_cond P (π := π) (Y := fun _ => 1) (fun _ _ _ => rfl) Z
  simpa using this.symm

/-- Block 1, item 4. -/
theorem cond_cond_of_refines {πF : Ω → ι} {πG : Ω → κ} (h : Refines πF πG) (Z : Ω → ℝ) :
    cond P πG (cond P πF Z) = cond P πG Z := by
  funext ω
  have key := ex_mul_cond P (π := πF)
    (meas_of_refines h (meas_ind πG ω)) Z
  rw [ex_ind, ex_ind] at key
  rw [cond_eq P πG (cond P πF Z) ω, cond_eq P πG Z ω, ← key]

/-- Block 1, item 5. -/
theorem cond_mul_meas {π : Ω → ι} {Y : Ω → ℝ} (hY : Meas π Y) (Z : Ω → ℝ) :
    cond P π (fun ω => Y ω * Z ω) = fun ω => Y ω * cond P π Z ω := by
  funext ω
  simp only [cond_eq]
  have : ∑ ω' ∈ cell π ω, P.μ ω' * (Y ω' * Z ω') = Y ω * ∑ ω' ∈ cell π ω, P.μ ω' * Z ω' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' hω' => ?_
    rw [hY ω' ω (mem_cell.1 hω')]
    ring
  rw [this, mul_div_assoc]

end Optionality
