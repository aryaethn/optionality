import Mathlib

open Finset BigOperators

noncomputable section

namespace Optionality

/-- A probability mass function with full support. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  μ : Ω → ℝ
  pos : ∀ ω, 0 < μ ω
  sum_one : ∑ ω, μ ω = 1

variable {Ω : Type*} [Fintype Ω]
variable (P : FinProb Ω)

/-- Expectation. -/
def ex (Z : Ω → ℝ) : ℝ := ∑ ω, P.μ ω * Z ω

/-- An information structure is a labelling of outcomes; outcomes with the same label are
indistinguishable. -/
def Meas {ι : Type*} (π : Ω → ι) (Y : Ω → ℝ) : Prop :=
  ∀ ω ω', π ω = π ω' → Y ω = Y ω'

/-- πF refines πG: πF carries at least the information of πG. -/
def Refines {ι κ : Type*} (πF : Ω → ι) (πG : Ω → κ) : Prop :=
  ∀ ω ω', πF ω = πF ω' → πG ω = πG ω'

/-- Conditional expectation given the partition induced by π. -/
def cond {ι : Type*} [DecidableEq ι] (π : Ω → ι) (Z : Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ ω' ∈ univ.filter (fun ω' => π ω' = π ω), P.μ ω' * Z ω') /
  (∑ ω' ∈ univ.filter (fun ω' => π ω' = π ω), P.μ ω')

def pos (x : ℝ) : ℝ := max x 0

end Optionality
