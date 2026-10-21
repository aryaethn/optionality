import Optionality.Block2

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

/-- Block 3, item 8 (Lemma 2, non-strict part). -/
theorem jensen_pos {πF : Ω → ι} {πG : Ω → κ} (h : Refines πF πG) (Z : Ω → ℝ) :
    ex P (fun ω => pos (cond P πG Z ω)) ≤ ex P (fun ω => pos (cond P πF Z ω)) := by
  obtain ⟨hm, h01, heq⟩ := choice_attained P πG Z
  rw [← heq]
  exact choice_le P (meas_of_refines h hm) h01 Z

/-- The pointwise gap of Lemma 2. -/
theorem jensen_gap {πF : Ω → ι} {πG : Ω → κ} (h : Refines πF πG) (Z : Ω → ℝ) :
    ex P (fun ω => pos (cond P πF Z ω)) - ex P (fun ω => pos (cond P πG Z ω))
      = ∑ ω, P.μ ω * (pos (cond P πF Z ω)
          - (if 0 < cond P πG Z ω then (1 : ℝ) else 0) * cond P πF Z ω) := by
  obtain ⟨hmeas, h01, heq⟩ := choice_attained P πG Z
  have hex : ex P (fun ω => pos (cond P πG Z ω))
      = ex P (fun ω => (if 0 < cond P πG Z ω then (1 : ℝ) else 0) * cond P πF Z ω) := by
    rw [← heq]
    exact ex_mul_cond P (meas_of_refines h hmeas) Z
  rw [hex]
  unfold ex
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem term_nonneg (m W : ℝ) :
    0 ≤ pos W - (if 0 < m then (1 : ℝ) else 0) * W := by
  unfold pos
  by_cases hm : 0 < m
  · rw [if_pos hm, one_mul]; linarith [le_max_left W 0]
  · rw [if_neg hm, zero_mul, sub_zero]; exact le_max_right _ _

theorem term_pos_iff (m W : ℝ) :
    0 < pos W - (if 0 < m then (1 : ℝ) else 0) * W ↔ (0 < m ∧ W < 0) ∨ (m ≤ 0 ∧ 0 < W) := by
  unfold pos
  by_cases hm : 0 < m
  · rw [if_pos hm, one_mul]
    have hm' : ¬ m ≤ 0 := not_le.2 hm
    constructor
    · intro h
      left
      refine ⟨hm, ?_⟩
      by_contra hW
      push_neg at hW
      rw [max_eq_left hW] at h
      linarith
    · rintro (⟨_, hW⟩ | ⟨hm2, _⟩)
      · rw [max_eq_right hW.le]; linarith
      · exact absurd hm2 hm'
  · rw [if_neg hm, zero_mul, sub_zero]
    have hm' : m ≤ 0 := not_lt.1 hm
    constructor
    · intro h
      right
      refine ⟨hm', ?_⟩
      by_contra hW
      push_neg at hW
      rw [max_eq_right hW] at h
      linarith
    · rintro (⟨hm2, _⟩ | ⟨_, hW⟩)
      · exact absurd hm2 hm
      · rw [max_eq_left hW.le]; exact hW

/-- If the conditional mean is `0` and `W` is negative somewhere in the cell, then `W` is
positive somewhere in the cell. -/
theorem exists_pos_of_cond_zero {π : Ω → ι} {W : Ω → ℝ} {ω₀ : Ω}
    (h0 : cond P π W ω₀ = 0) (hneg : W ω₀ < 0) :
    ∃ ω', π ω' = π ω₀ ∧ 0 < W ω' := by
  by_contra hc
  push_neg at hc
  rw [cond_eq, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have hlt : ∑ ω' ∈ cell π ω₀, P.μ ω' * W ω' < ∑ ω' ∈ cell π ω₀, (0 : ℝ) := by
      refine Finset.sum_lt_sum (fun ω' hω' => ?_) ⟨ω₀, self_mem_cell ω₀, ?_⟩
      · exact mul_nonpos_of_nonneg_of_nonpos (P.pos _).le (hc ω' (mem_cell.1 hω'))
      · exact mul_neg_of_pos_of_neg (P.pos _) hneg
    rw [Finset.sum_const_zero] at hlt
    linarith
  · exact absurd h0 (mass_pos P π ω₀).ne'

/-- Block 3, item 9 (Lemma 2, strictness criterion). -/
theorem jensen_pos_strict_iff {πF : Ω → ι} {πG : Ω → κ} (h : Refines πF πG) (Z : Ω → ℝ) :
    ex P (fun ω => pos (cond P πG Z ω)) < ex P (fun ω => pos (cond P πF Z ω)) ↔
    ∃ ω, (0 < cond P πF Z ω ∧ cond P πG Z ω ≤ 0) ∨
         (cond P πF Z ω < 0 ∧ 0 ≤ cond P πG Z ω) := by
  rw [← sub_pos, jensen_gap P h Z]
  have hnn : ∀ ω, 0 ≤ P.μ ω * (pos (cond P πF Z ω)
      - (if 0 < cond P πG Z ω then (1 : ℝ) else 0) * cond P πF Z ω) :=
    fun ω => mul_nonneg (P.pos ω).le (term_nonneg _ _)
  constructor
  · intro hs
    have hex : ∃ ω, 0 < pos (cond P πF Z ω)
        - (if 0 < cond P πG Z ω then (1 : ℝ) else 0) * cond P πF Z ω := by
      by_contra hc
      push_neg at hc
      have := Finset.sum_nonpos (s := univ) (fun ω _ =>
        mul_nonpos_of_nonneg_of_nonpos (P.pos ω).le (hc ω))
      linarith
    obtain ⟨ω, hω⟩ := hex
    rw [term_pos_iff] at hω
    refine ⟨ω, ?_⟩
    rcases hω with ⟨a, b⟩ | ⟨a, b⟩
    · right; exact ⟨b, a.le⟩
    · left; exact ⟨b, a⟩
  · rintro ⟨ω, hω⟩
    have key : ∃ ω', 0 < pos (cond P πF Z ω')
        - (if 0 < cond P πG Z ω' then (1 : ℝ) else 0) * cond P πF Z ω' := by
      rcases hω with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨ω, (term_pos_iff _ _).2 (Or.inr ⟨b, a⟩)⟩
      · by_cases hm : 0 < cond P πG Z ω
        · exact ⟨ω, (term_pos_iff _ _).2 (Or.inl ⟨hm, a⟩)⟩
        · have hm0 : cond P πG Z ω = 0 := le_antisymm (not_lt.1 hm) b
          have hc : cond P πG (cond P πF Z) ω = 0 := by
            rw [cond_cond_of_refines P h Z]; exact hm0
          obtain ⟨ω', hπ, hpos⟩ := exists_pos_of_cond_zero P hc a
          have hm' : cond P πG Z ω' = cond P πG Z ω := cond_meas P πG Z ω' ω hπ
          exact ⟨ω', (term_pos_iff _ _).2 (Or.inr ⟨by rw [hm', hm0], hpos⟩)⟩
    obtain ⟨ω', hω'⟩ := key
    refine Finset.sum_pos' (fun ω _ => hnn ω) ⟨ω', mem_univ _, ?_⟩
    exact mul_pos (P.pos ω') hω'

end Optionality
