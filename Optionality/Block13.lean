import Optionality.Block6

/-!
Block 13: option values for Theorem D(b), D(d) and Corollary 4 (hybrid designs without
independence), on finite probability spaces with full support (Blocks 1 to 4, `ZR_true` from Block 6).
The penalty is called `pen` to avoid a clash with the probability `P`.
-/

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

/-! ### Conditional expectation: linearity, monotonicity, constants -/

theorem cond_sub (π : Ω → ι) (f g : Ω → ℝ) :
    cond P π (fun ω => f ω - g ω) = fun ω => cond P π f ω - cond P π g ω := by
  funext ω
  simp only [cond_eq, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem cond_const (π : Ω → ι) (c : ℝ) : cond P π (fun _ => c) = fun _ => c := by
  funext ω
  rw [cond_eq, ← Finset.sum_mul]
  have : ∑ ω' ∈ cell π ω, P.μ ω' = mass P π ω := rfl
  rw [this]
  exact mul_div_cancel_left₀ c (mass_pos P π ω).ne'

theorem cond_sub_const (π : Ω → ι) (D : Ω → ℝ) (pen : ℝ) :
    cond P π (fun ω => D ω - pen) = fun ω => cond P π D ω - pen := by
  funext ω
  calc cond P π (fun ω => D ω - pen) ω
      = cond P π D ω - cond P π (fun _ => pen) ω :=
        congr_fun (cond_sub P π D (fun _ => pen)) ω
    _ = cond P π D ω - pen := by rw [congr_fun (cond_const P π pen) ω]

theorem cond_of_meas {π : Ω → ι} {Y : Ω → ℝ} (hY : Meas π Y) : cond P π Y = Y := by
  funext ω
  rw [cond_eq]
  have : ∑ ω' ∈ cell π ω, P.μ ω' * Y ω' = Y ω * mass P π ω := by
    unfold mass
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω' hω' => by rw [hY ω' ω (mem_cell.1 hω')]; ring
  rw [this]
  exact mul_div_cancel_right₀ _ (mass_pos P π ω).ne'

theorem cond_mono (π : Ω → ι) {f g : Ω → ℝ} (hle : ∀ ω, f ω ≤ g ω) (ω : Ω) :
    cond P π f ω ≤ cond P π g ω := by
  rw [cond_eq, cond_eq]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left (hle ω') (P.pos ω').le)
    (mass_pos P π ω).le

theorem cond_nonneg (π : Ω → ι) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (ω : Ω) :
    0 ≤ cond P π f ω := by
  rw [cond_eq]
  exact div_nonneg (Finset.sum_nonneg fun ω' _ => mul_nonneg (P.pos ω').le (hf ω'))
    (mass_pos P π ω).le

theorem cond_nonpos (π : Ω → ι) {f : Ω → ℝ} (hf : ∀ ω, f ω ≤ 0) (ω : Ω) :
    cond P π f ω ≤ 0 := by
  rw [cond_eq]
  exact div_nonpos_of_nonpos_of_nonneg
    (Finset.sum_nonpos fun ω' _ => mul_nonpos_of_nonneg_of_nonpos (P.pos ω').le (hf ω'))
    (mass_pos P π ω).le

theorem ex_pos_of_nonpos {f : Ω → ℝ} (hf : ∀ ω, f ω ≤ 0) :
    ex P (fun ω => pos (f ω)) = 0 := by
  unfold ex
  refine Finset.sum_eq_zero fun ω _ => ?_
  show P.μ ω * pos (f ω) = 0
  unfold pos
  rw [max_eq_right (hf ω), mul_zero]

/-! ### Deterrence (Theorem D(d)) -/

/-- Block 13, item 52. -/
theorem deterrence_zero {D : Ω → ℝ} {pen : ℝ} (hD : ∀ ω, D ω ≤ pen) (π : Ω → ι) :
    ex P (fun ω => pos (cond P π (fun ω => D ω - pen) ω)) = 0 :=
  ex_pos_of_nonpos P (cond_nonpos P π fun ω => by linarith [hD ω])

/-- Block 13, item 52 (consequence): the endogenous option for `D - pen` with `R = univ` vanishes. -/
theorem deterrence_Vendo_zero {πF : Ω → ι} {πG : Ω → κ} {D : Ω → ℝ} {pen : ℝ}
    (hD : ∀ ω, D ω ≤ pen) :
    Vendo P (fun _ : Ω => True) (fun ω => D ω - pen) πF πG = 0 := by
  unfold Vendo val
  rw [ZR_true, deterrence_zero P hD πF, deterrence_zero P hD πG]
  ring

/-- The paper's form of Theorem D(d): it suffices that the *conditional* payoff
`D^F` is at most `pen` (the draft says `pen ≥ ess sup D^F`); `D ≤ pen` is not needed. -/
theorem deterrence_zero_of_cond_le {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    {D : Ω → ℝ} {pen : ℝ} (hD : ∀ ω, cond P πF D ω ≤ pen) :
    Vendo P (fun _ : Ω => True) (fun ω => D ω - pen) πF πG = 0 := by
  have hF : ∀ ω, cond P πF (fun ω => D ω - pen) ω ≤ 0 := by
    intro ω
    rw [congr_fun (cond_sub_const P πF D pen) ω]
    linarith [hD ω]
  have hG : ∀ ω, cond P πG (fun ω => D ω - pen) ω ≤ 0 := by
    intro ω
    rw [← congr_fun (cond_cond_of_refines P hFG (fun ω => D ω - pen)) ω]
    exact cond_nonpos P πG hF ω
  unfold Vendo val
  rw [ZR_true, ex_pos_of_nonpos P hF, ex_pos_of_nonpos P hG]
  ring

/-- Block 13, item 53. -/
theorem deterrence_strict {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG) (D : Ω → ℝ)
    (pen : ℝ) :
    0 < Vendo P (fun _ : Ω => True) (fun ω => D ω - pen) πF πG ↔
      ∃ ω, (0 < cond P πF D ω - pen ∧ cond P πG D ω - pen ≤ 0) ∨
           (cond P πF D ω - pen < 0 ∧ 0 ≤ cond P πG D ω - pen) := by
  have hR : Meas πG (fun ω => if (fun _ : Ω => True) ω then (1 : ℝ) else 0) :=
    fun _ _ _ => rfl
  rw [thmA_b_endo_pos_iff P hFG hR (fun ω => D ω - pen), cond_sub_const P πF D pen,
    cond_sub_const P πG D pen]
  constructor
  · rintro ⟨ω, -, h⟩
    exact ⟨ω, h⟩
  · rintro ⟨ω, h⟩
    exact ⟨ω, trivial, h⟩

/-! ### Hybrid designs without independence (Corollary 4) -/

/-- The conditional endogenous option `Z = E[(D^F)⁺ - (D^G)⁺ | G]`. -/
def Zopt (πF : Ω → ι) (πG : Ω → κ) (D : Ω → ℝ) : Ω → ℝ :=
  cond P πG (fun ω => pos (cond P πF D ω) - pos (cond P πG D ω))

/-- Block 13, item 54. -/
theorem hybrid_dep_formula {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    {R : Ω → Prop} [DecidablePred R] (hR : Meas πG (fun ω => if R ω then (1 : ℝ) else 0))
    (D : Ω → ℝ) :
    Vendo P R D πF πG = ex P (fun ω => (if R ω then (1 : ℝ) else 0) * Zopt P πF πG D ω) := by
  obtain ⟨hF, hG⟩ := thmA_b_endo_formula P hFG hR D
  have hFω : ∀ ω, cond P πF (ZR R D) ω = (if R ω then (1 : ℝ) else 0) * cond P πF D ω :=
    fun ω => congr_fun hF ω
  have hGω : ∀ ω, cond P πG (ZR R D) ω = (if R ω then (1 : ℝ) else 0) * cond P πG D ω :=
    fun ω => congr_fun hG ω
  have key : ∀ ω, pos (cond P πF (ZR R D) ω) - pos (cond P πG (ZR R D) ω)
      = (if R ω then (1 : ℝ) else 0) * (pos (cond P πF D ω) - pos (cond P πG D ω)) := by
    intro ω
    by_cases hr : R ω <;> simp [hFω ω, hGω ω, hr, pos]
  have hdiff : ex P (fun ω => pos (cond P πF (ZR R D) ω))
        - ex P (fun ω => pos (cond P πG (ZR R D) ω))
      = ex P (fun ω => (if R ω then (1 : ℝ) else 0)
          * (pos (cond P πF D ω) - pos (cond P πG D ω))) := by
    unfold ex
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    show P.μ ω * pos (cond P πF (ZR R D) ω) - P.μ ω * pos (cond P πG (ZR R D) ω)
      = P.μ ω * ((if R ω then (1 : ℝ) else 0)
          * (pos (cond P πF D ω) - pos (cond P πG D ω)))
    rw [← key ω]
    ring
  unfold Vendo val
  rw [hdiff]
  exact ex_mul_cond P hR (fun ω => pos (cond P πF D ω) - pos (cond P πG D ω))

/-- Block 13, item 55 (conditional Jensen, pointwise). -/
theorem hybrid_dep_Z_nonneg {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG) (D : Ω → ℝ) :
    ∀ ω, 0 ≤ Zopt P πF πG D ω := by
  intro ω
  have hmeas : Meas πG (fun ω => pos (cond P πG D ω)) := by
    intro a b h
    show pos (cond P πG D a) = pos (cond P πG D b)
    rw [cond_meas P πG D a b h]
  have hZ : Zopt P πF πG D ω
      = cond P πG (fun ω => pos (cond P πF D ω)) ω - pos (cond P πG D ω) := by
    unfold Zopt
    rw [congr_fun (cond_sub P πG (fun ω => pos (cond P πF D ω))
        (fun ω => pos (cond P πG D ω))) ω,
      congr_fun (cond_of_meas P hmeas) ω]
  have h1 : cond P πG D ω ≤ cond P πG (fun ω => pos (cond P πF D ω)) ω := by
    have := cond_mono P πG (f := cond P πF D) (g := fun ω => pos (cond P πF D ω))
      (fun ω => by unfold pos; exact le_max_left _ _) ω
    rwa [congr_fun (cond_cond_of_refines P hFG D) ω] at this
  have h2 : 0 ≤ cond P πG (fun ω => pos (cond P πF D ω)) ω :=
    cond_nonneg P πG (fun ω => by unfold pos; exact le_max_right _ _) ω
  have h3 : pos (cond P πG D ω) ≤ cond P πG (fun ω => pos (cond P πF D ω)) ω :=
    max_le h1 h2
  rw [hZ]
  linarith

/-- Block 13, item 56. -/
theorem hybrid_dep_bounds {πF : Ω → ι} {πG : Ω → κ} (hFG : Refines πF πG)
    {R : Ω → Prop} [DecidablePred R] (hR : Meas πG (fun ω => if R ω then (1 : ℝ) else 0))
    (D : Ω → ℝ) :
    0 ≤ Vendo P R D πF πG ∧ Vendo P R D πF πG ≤ ex P (Zopt P πF πG D) := by
  refine ⟨thmA_b_endo_nonneg P hFG R D, ?_⟩
  rw [hybrid_dep_formula P hFG hR D]
  unfold ex
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (P.pos ω).le
  show (if R ω then (1 : ℝ) else 0) * Zopt P πF πG D ω ≤ Zopt P πF πG D ω
  have hz := hybrid_dep_Z_nonneg P hFG D ω
  by_cases hr : R ω
  · rw [if_pos hr, one_mul]
  · rw [if_neg hr, zero_mul]
    exact hz

/-! ### Covariance bound -/

theorem ex_add (f g : Ω → ℝ) : ex P (fun ω => f ω + g ω) = ex P f + ex P g := by
  unfold ex
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ex_sub (f g : Ω → ℝ) : ex P (fun ω => f ω - g ω) = ex P f - ex P g := by
  unfold ex
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ex_smul (c : ℝ) (f : Ω → ℝ) : ex P (fun ω => c * f ω) = c * ex P f := by
  unfold ex
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem ex_const (c : ℝ) : ex P (fun _ => c) = c := by
  unfold ex
  rw [← Finset.sum_mul, P.sum_one, one_mul]

/-- Cauchy-Schwarz for the weighted expectation. -/
theorem abs_ex_mul_le (a b : Ω → ℝ) :
    |ex P (fun ω => a ω * b ω)|
      ≤ Real.sqrt (ex P (fun ω => a ω ^ 2)) * Real.sqrt (ex P (fun ω => b ω ^ 2)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
    (fun ω => Real.sqrt (P.μ ω) * a ω) (fun ω => Real.sqrt (P.μ ω) * b ω)
  have hs : ∀ ω, Real.sqrt (P.μ ω) * Real.sqrt (P.μ ω) = P.μ ω :=
    fun ω => Real.mul_self_sqrt (P.pos ω).le
  have e1 : ∑ ω, (Real.sqrt (P.μ ω) * a ω) * (Real.sqrt (P.μ ω) * b ω)
      = ex P (fun ω => a ω * b ω) := by
    unfold ex
    refine Finset.sum_congr rfl fun ω _ => ?_
    calc (Real.sqrt (P.μ ω) * a ω) * (Real.sqrt (P.μ ω) * b ω)
        = (Real.sqrt (P.μ ω) * Real.sqrt (P.μ ω)) * (a ω * b ω) := by ring
      _ = P.μ ω * (a ω * b ω) := by rw [hs ω]
  have e2 : ∀ c : Ω → ℝ, ∑ ω, (Real.sqrt (P.μ ω) * c ω) ^ 2 = ex P (fun ω => c ω ^ 2) := by
    intro c
    unfold ex
    refine Finset.sum_congr rfl fun ω _ => ?_
    calc (Real.sqrt (P.μ ω) * c ω) ^ 2
        = (Real.sqrt (P.μ ω) * Real.sqrt (P.μ ω)) * c ω ^ 2 := by ring
      _ = P.μ ω * c ω ^ 2 := by rw [hs ω]
  rw [e1, e2 a, e2 b] at hcs
  have hA : 0 ≤ ex P (fun ω => a ω ^ 2) :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (P.pos ω).le (sq_nonneg _)
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt hcs

/-- Block 13, item 57. Stated for an arbitrary function `Z` (in particular `Zopt`) and an
arbitrary event `R`; `qR = ex P 1_R = Pr[R]`. -/
theorem hybrid_dep_cov (R : Ω → Prop) [DecidablePred R] (Z : Ω → ℝ) :
    |ex P (fun ω => (if R ω then (1 : ℝ) else 0) * Z ω)
        - ex P (fun ω => if R ω then (1 : ℝ) else 0) * ex P Z|
      ≤ Real.sqrt (ex P (fun ω => if R ω then (1 : ℝ) else 0)
            * (1 - ex P (fun ω => if R ω then (1 : ℝ) else 0)))
        * Real.sqrt (ex P (fun ω => (Z ω - ex P Z) ^ 2)) := by
  obtain ⟨q, hq⟩ : ∃ q, q = ex P (fun ω => if R ω then (1 : ℝ) else 0) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = ex P Z := ⟨_, rfl⟩
  rw [← hq, ← hm]
  have hcs := abs_ex_mul_le P (fun ω => (if R ω then (1 : ℝ) else 0) - q) (fun ω => Z ω - m)
  have hcov : ex P (fun ω => ((if R ω then (1 : ℝ) else 0) - q) * (Z ω - m))
      = ex P (fun ω => (if R ω then (1 : ℝ) else 0) * Z ω) - q * m := by
    have e : (fun ω => ((if R ω then (1 : ℝ) else 0) - q) * (Z ω - m))
        = fun ω => ((((if R ω then (1 : ℝ) else 0) * Z ω)
            - m * (if R ω then (1 : ℝ) else 0)) - q * Z ω) + q * m := by
      funext ω; ring
    rw [e, ex_add, ex_sub, ex_sub, ex_smul, ex_smul, ex_const, ← hq, ← hm]
    ring
  have hvar : ex P (fun ω => ((if R ω then (1 : ℝ) else 0) - q) ^ 2) = q * (1 - q) := by
    have e : (fun ω => ((if R ω then (1 : ℝ) else 0) - q) ^ 2)
        = fun ω => (1 - 2 * q) * (if R ω then (1 : ℝ) else 0) + q ^ 2 := by
      funext ω
      split_ifs <;> ring
    rw [e, ex_add, ex_smul, ex_const, ← hq]
    ring
  rw [hcov, hvar] at hcs
  exact hcs

/-! ### Induced unavailability -/

/-- Block 13, item 58 (general form): for a `π`-measurable `Z`, the best `π`-measurable
0/1 trigger earns `E[(Z - c)⁺]`. -/
theorem induced_unavailability_of_meas {π : Ω → ι} {Z : Ω → ℝ} (hZ : Meas π Z) (c : ℝ) :
    (∀ Y : Ω → ℝ, Meas π Y → (∀ ω, Y ω = 0 ∨ Y ω = 1) →
        ex P (fun ω => Y ω * (Z ω - c)) ≤ ex P (fun ω => pos (Z ω - c))) ∧
    ∃ Y : Ω → ℝ, Meas π Y ∧ (∀ ω, Y ω = 0 ∨ Y ω = 1) ∧
        ex P (fun ω => Y ω * (Z ω - c)) = ex P (fun ω => pos (Z ω - c)) := by
  have hmeas : Meas π (fun ω => Z ω - c) := fun a b h => by simp only [hZ a b h]
  have hc : cond P π (fun ω => Z ω - c) = fun ω => Z ω - c := cond_of_meas P hmeas
  refine ⟨fun Y hY h01 => ?_, ?_⟩
  · have := choice_le P hY h01 (fun ω => Z ω - c)
    rwa [hc] at this
  · obtain ⟨hm, h01, heq⟩ := choice_attained P π (fun ω => Z ω - c)
    rw [hc] at hm h01 heq
    exact ⟨_, hm, h01, heq⟩

/-- Block 13, item 58, for `Z = Zopt` and `π = πG`. -/
theorem induced_unavailability (πF : Ω → ι) (πG : Ω → κ) (D : Ω → ℝ) (c : ℝ) :
    (∀ Y : Ω → ℝ, Meas πG Y → (∀ ω, Y ω = 0 ∨ Y ω = 1) →
        ex P (fun ω => Y ω * (Zopt P πF πG D ω - c))
          ≤ ex P (fun ω => pos (Zopt P πF πG D ω - c))) ∧
    ∃ Y : Ω → ℝ, Meas πG Y ∧ (∀ ω, Y ω = 0 ∨ Y ω = 1) ∧
        ex P (fun ω => Y ω * (Zopt P πF πG D ω - c))
          = ex P (fun ω => pos (Zopt P πF πG D ω - c)) :=
  induced_unavailability_of_meas P (cond_meas P πG _) c

end Optionality
