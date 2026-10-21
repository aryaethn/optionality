import Optionality.Block4

open Finset BigOperators

noncomputable section

set_option linter.deprecated false

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace Optionality

variable {Ω' : Type*} [Fintype Ω']
variable {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

/-- Product space `Ω' × Bool` with `μ (ω', b) = μ' ω' * (if b then q else 1 - q)`;
`b = true` means the committee is available. -/
def prodProb (P' : FinProb Ω') (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : FinProb (Ω' × Bool) where
  μ x := P'.μ x.1 * (if x.2 then q else 1 - q)
  pos x := by
    refine mul_pos (P'.pos _) ?_
    by_cases h : x.2 = true
    · rw [if_pos h]; exact hq0
    · rw [if_neg h]; linarith
  sum_one := by
    rw [Fintype.sum_prod_type]
    have : ∀ ω' : Ω', ∑ b : Bool, P'.μ ω' * (if b then q else 1 - q) = P'.μ ω' := by
      intro ω'
      rw [Fintype.sum_bool]
      simp only [if_true]
      simp only [Bool.false_eq_true, if_false]
      ring
    simp only [this]
    exact P'.sum_one

/-- `R (ω', b) := b = false` (committee unavailable). -/
def prodR (Ω' : Type*) : Ω' × Bool → Prop := fun x => x.2 = false

instance (Ω' : Type*) : DecidablePred (prodR Ω') :=
  fun x => inferInstanceAs (Decidable (x.2 = false))

/-- `D (ω', b) := D' ω'`. -/
def prodD (D' : Ω' → ℝ) : Ω' × Bool → ℝ := fun x => D' x.1

/-- Information that includes availability. -/
def prodInfo (π' : Ω' → ι) : Ω' × Bool → ι × Bool := fun x => (π' x.1, x.2)

/-- Information that does not include availability (commitment time). -/
def prodInfo0 (π' : Ω' → ι) : Ω' × Bool → ι := fun x => π' x.1

section lemmas

variable (P' : FinProb Ω') (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)

theorem ZR_true (D : Ω' → ℝ) : ZR (fun _ : Ω' => True) D = D := by
  funext ω; simp [ZR]

theorem sum_cell_prodInfo (π' : Ω' → ι) (f : Ω' × Bool → ℝ) (ω' : Ω') (b : Bool) :
    ∑ x ∈ cell (prodInfo π') (ω', b), f x = ∑ ω'' ∈ cell π' ω', f (ω'', b) := by
  simp only [cell, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω'' _ => ?_
  rw [Fintype.sum_eq_single b (fun b'' hb => by simp [prodInfo, hb])]
  simp [prodInfo]

theorem sum_cell_prodInfo0 (π' : Ω' → ι) (f : Ω' × Bool → ℝ) (ω' : Ω') (b : Bool) :
    ∑ x ∈ cell (prodInfo0 π') (ω', b), f x = ∑ ω'' ∈ cell π' ω', ∑ b'', f (ω'', b'') := by
  simp only [cell, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω'' _ => ?_
  by_cases h : π' ω'' = π' ω' <;> simp [prodInfo0, h]

theorem pos_mul_left (c : ℝ) (hc : 0 ≤ c) (x : ℝ) : pos (c * x) = c * pos x := by
  unfold pos
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

theorem cond_prodInfo (π' : Ω' → ι) (D' : Ω' → ℝ) (ω' : Ω') (b : Bool) :
    cond (prodProb P' q hq0 hq1) (prodInfo π') (ZR (prodR Ω') (prodD D')) (ω', b)
      = if b = false then cond P' π' D' ω' else 0 := by
  rw [cond_eq]
  unfold mass
  rw [sum_cell_prodInfo, sum_cell_prodInfo]
  have hq : (1 - q) ≠ 0 := by linarith
  by_cases hb : b = false
  · subst hb
    simp only [prodProb, ZR, prodD, prodR, if_true, Bool.false_eq_true, if_false, one_mul,
      cond_eq]
    have hN : ∑ ω'' ∈ cell π' ω', P'.μ ω'' * (1 - q) * D' ω''
        = (1 - q) * ∑ ω'' ∈ cell π' ω', P'.μ ω'' * D' ω'' := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have hM' : ∑ ω'' ∈ cell π' ω', P'.μ ω'' * (1 - q)
        = (1 - q) * ∑ ω'' ∈ cell π' ω', P'.μ ω'' := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    unfold mass
    rw [hN, hM']
    exact mul_div_mul_left _ _ hq
  · have hb' : b = true := by simpa using hb
    subst hb'
    simp [ZR, prodR, prodD]

theorem cond_prodInfo0 (π' : Ω' → ι) (D' : Ω' → ℝ) (ω' : Ω') (b : Bool) :
    cond (prodProb P' q hq0 hq1) (prodInfo0 π') (ZR (prodR Ω') (prodD D')) (ω', b)
      = (1 - q) * cond P' π' D' ω' := by
  rw [cond_eq]
  unfold mass
  rw [sum_cell_prodInfo0, sum_cell_prodInfo0]
  simp only [Fintype.sum_bool, prodProb, ZR, prodD, prodR, if_true, Bool.false_eq_true, if_false,
    one_mul, zero_mul, mul_zero, add_zero, zero_add, cond_eq, Bool.true_eq_false]
  have hN : ∑ ω'' ∈ cell π' ω', P'.μ ω'' * (1 - q) * D' ω''
      = (1 - q) * ∑ ω'' ∈ cell π' ω', P'.μ ω'' * D' ω'' := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hM' : ∑ ω'' ∈ cell π' ω', (P'.μ ω'' * q + P'.μ ω'' * (1 - q))
      = ∑ ω'' ∈ cell π' ω', P'.μ ω'' :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [hN, hM']
  unfold mass
  exact mul_div_assoc _ _ _

theorem val_prodInfo (π' : Ω' → ι) (D' : Ω' → ℝ) :
    val (prodProb P' q hq0 hq1) (prodR Ω') (prodD D') (prodInfo π')
      = (1 - q) * val P' (fun _ : Ω' => True) D' π' := by
  unfold val
  rw [ZR_true]
  unfold ex
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  beta_reduce
  rw [Fintype.sum_bool, cond_prodInfo P' q hq0 hq1 π' D' ω' true,
    cond_prodInfo P' q hq0 hq1 π' D' ω' false]
  simp [pos, prodProb]
  ring

theorem val_prodInfo0 (π' : Ω' → ι) (D' : Ω' → ℝ) :
    val (prodProb P' q hq0 hq1) (prodR Ω') (prodD D') (prodInfo0 π')
      = (1 - q) * val P' (fun _ : Ω' => True) D' π' := by
  unfold val
  rw [ZR_true]
  unfold ex
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  beta_reduce
  rw [Fintype.sum_bool, cond_prodInfo0 P' q hq0 hq1 π' D' ω' true,
    cond_prodInfo0 P' q hq0 hq1 π' D' ω' false,
    pos_mul_left _ (by linarith)]
  simp only [prodProb, if_true, Bool.false_eq_true, if_false]
  ring

end lemmas

/-- Block 6, item 16. -/
theorem hybrid_endo (P' : FinProb Ω') (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (D' : Ω' → ℝ)
    (πF' : Ω' → ι) (πG' : Ω' → κ) :
    Vendo (prodProb P' q hq0 hq1) (prodR Ω') (prodD D') (prodInfo πF') (prodInfo πG')
      = (1 - q) * Vendo P' (fun _ : Ω' => True) D' πF' πG' := by
  unfold Vendo
  rw [val_prodInfo, val_prodInfo]
  ring

/-- Block 6, item 17. -/
theorem hybrid_tot (P' : FinProb Ω') (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (D' : Ω' → ℝ)
    (πF' : Ω' → ι) (π0' : Ω' → ν) :
    Vtot (prodProb P' q hq0 hq1) (prodR Ω') (prodD D') (prodInfo πF') (prodInfo0 π0')
      = (1 - q) * Vtot P' (fun _ : Ω' => True) D' πF' π0' := by
  unfold Vtot
  rw [val_prodInfo, val_prodInfo0]
  ring

end Optionality
