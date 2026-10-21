import Mathlib

/-!
Optional stretch goal: measure-theoretic version of the non-strict part of Lemma 2 and of the
upper bound in Lemma 1, via `MeasureTheory.condExp`.
-/

open MeasureTheory

noncomputable section

namespace Optionality

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- `E[W | C]⁺ ≤ E[W⁺ | C]` almost everywhere. -/
theorem condExp_pos_le {m : MeasurableSpace Ω} {W : Ω → ℝ} (hW : Integrable W μ) :
    (fun ω => max (μ[W | m] ω) 0) ≤ᵐ[μ] μ[fun ω => max (W ω) 0 | m] := by
  have hWp : Integrable (fun ω => max (W ω) 0) μ := hW.pos_part
  have h1 : μ[W | m] ≤ᵐ[μ] μ[fun ω => max (W ω) 0 | m] :=
    condExp_mono hW hWp (Filter.Eventually.of_forall fun ω => le_max_left _ _)
  have h2 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => max (W ω) 0 | m] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => le_max_right _ _)
  filter_upwards [h1, h2] with ω a b using max_le a b

/-- Lemma 2, non-strict part: `E[(E[W | C])⁺] ≤ E[W⁺]`. -/
theorem integral_condExp_pos_le {m : MeasurableSpace Ω} (hm : m ≤ m0) {W : Ω → ℝ}
    (hW : Integrable W μ) :
    ∫ ω, max (μ[W | m] ω) 0 ∂μ ≤ ∫ ω, max (W ω) 0 ∂μ := by
  calc ∫ ω, max (μ[W | m] ω) 0 ∂μ
      ≤ ∫ ω, μ[fun ω => max (W ω) 0 | m] ω ∂μ :=
        integral_mono_ae integrable_condExp.pos_part integrable_condExp (condExp_pos_le hW)
    _ = ∫ ω, max (W ω) 0 ∂μ := integral_condExp hm

/-- Lemma 1, upper bound: `E[Y Z] ≤ E[(E[Z | C])⁺]` for `C`-measurable `{0,1}`-valued `Y`. -/
theorem integral_mul_le_condExp_pos {m : MeasurableSpace Ω} (hm : m ≤ m0) {Y Z : Ω → ℝ}
    (hYm : StronglyMeasurable[m] Y) (hY01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) (hZ : Integrable Z μ) :
    ∫ ω, Y ω * Z ω ∂μ ≤ ∫ ω, max (μ[Z | m] ω) 0 ∂μ := by
  have hYb : ∀ ω, ‖Y ω‖ ≤ 1 := fun ω => by rcases hY01 ω with h | h <;> simp [h]
  have hYZ : Integrable (fun ω => Y ω * Z ω) μ :=
    hZ.bdd_mul (hYm.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hYb)
  have hce : μ[fun ω => Y ω * Z ω | m] =ᵐ[μ] fun ω => Y ω * μ[Z | m] ω :=
    condExp_mul_of_stronglyMeasurable_left hYm hYZ hZ
  calc ∫ ω, Y ω * Z ω ∂μ = ∫ ω, μ[fun ω => Y ω * Z ω | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, Y ω * μ[Z | m] ω ∂μ := integral_congr_ae hce
    _ ≤ ∫ ω, max (μ[Z | m] ω) 0 ∂μ := by
        refine integral_mono_ae ?_ integrable_condExp.pos_part
          (Filter.Eventually.of_forall fun ω => ?_)
        · exact (integrable_condExp (m := m) (f := Z)).bdd_mul
            (hYm.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hYb)
        · rcases hY01 ω with h | h
          · simp [h]
          · simp [h]

end Optionality
