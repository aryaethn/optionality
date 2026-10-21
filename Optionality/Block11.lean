import Optionality.Block10
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
Block 11: the attack-plan model of Theorem C (general class of reveal patterns).
-/

open Finset BigOperators

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace Optionality

/-- Cost of revealing exactly the commitments in S out of k, each with ToB fee f:
unrevealed ones forfeit f, revealed ones pay f / F (EIP-8184). -/
def cost (k : ℕ) (F f : ℝ) (S : Finset (Fin k)) : ℝ :=
  f * (((k : ℝ) - S.card) + S.card / F)

/-- An attack plan with k commitments against a victim whose plaintext lies in a guess class
`t : ι`. -/
structure Plan (ι : Type*) (k : ℕ) where
  A : Finset ι                     -- targeted classes
  σ : ι → Finset (Fin k)           -- reveal set used when the class is t
  inj : Set.InjOn σ A              -- distinct classes need distinct reveal patterns
  nonempty : ∀ t ∈ A, (σ t).Nonempty   -- the empty reveal set executes nothing
  a : Finset (Fin k)               -- reveal set used on a miss
  abort_fresh : ∀ t ∈ A, σ t ≠ a

/-- Expected profit: gain G on a hit, nothing on a miss (assumption A2), fees as in `cost`. -/
def profit {ι : Type*} {k : ℕ} (p : ι → ℝ) (G F f : ℝ) (P : Plan ι k) : ℝ :=
  ∑ t ∈ P.A, p t * (G - cost k F f (P.σ t)) - (1 - ∑ t ∈ P.A, p t) * cost k F f P.a

theorem cost_eq_mul (k : ℕ) (F f : ℝ) (S : Finset (Fin k)) :
    cost k F f S = f * cost k F 1 S := by
  unfold cost; ring

theorem cost_nonneg {k : ℕ} {F f : ℝ} (hf : 0 ≤ f) (hF : 0 < F) (S : Finset (Fin k)) :
    0 ≤ cost k F f S := by
  unfold cost
  have h1 : S.card ≤ k := by simpa using Finset.card_le_univ S
  have h2 : (S.card : ℝ) ≤ k := by exact_mod_cast h1
  have h3 : 0 ≤ (S.card : ℝ) / F := div_nonneg (Nat.cast_nonneg _) hF.le
  exact mul_nonneg hf (by linarith)

/-- Block 11, item 39. -/
theorem cost_ge_f_of_lt {k : ℕ} {F f : ℝ} (hf : 0 ≤ f) (hF : 0 < F) {S : Finset (Fin k)}
    (h : S.card < k) : f ≤ cost k F f S := by
  unfold cost
  have h1 : (S.card : ℝ) + 1 ≤ k := by exact_mod_cast Nat.add_one_le_iff.2 h
  have h2 : 0 ≤ (S.card : ℝ) / F := div_nonneg (Nat.cast_nonneg _) hF.le
  exact le_mul_of_one_le_right hf (by linarith)

/-- Block 11, item 40. -/
theorem cost_univ (k : ℕ) (F f : ℝ) : cost k F f Finset.univ = f * (k / F) := by
  unfold cost
  simp

theorem profit_eq {ι : Type*} {k : ℕ} (p : ι → ℝ) (G F f : ℝ) (P : Plan ι k) :
    profit p G F f P = G * ∑ t ∈ P.A, p t
      - f * (∑ t ∈ P.A, p t * cost k F 1 (P.σ t)
              + (1 - ∑ t ∈ P.A, p t) * cost k F 1 P.a) := by
  unfold profit
  have h : ∀ S : Finset (Fin k), cost k F f S = f * cost k F 1 S := fun S => cost_eq_mul k F f S
  simp only [h]
  have h1 : ∑ t ∈ P.A, p t * (G - f * cost k F 1 (P.σ t))
      = G * ∑ t ∈ P.A, p t - f * ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [h1]; ring

/-- Block 11, item 41 (Theorem C(c)). -/
theorem thmC_c_upper {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (hk : 1 ≤ k)
    {p : ι → ℝ} {G F f p1 : ℝ} (hp0 : ∀ t, 0 ≤ p t) (hsum : ∑ t, p t ≤ 1)
    (hp1 : ∀ t, p t ≤ p1) (hp1_0 : 0 ≤ p1) (hp1_1 : p1 ≤ 1) (hF : 1 ≤ F) (hG : 0 ≤ G)
    (hf : G / ((1 - p1) + p1 / F) ≤ f) :
    ∀ P : Plan ι k, profit p G F f P ≤ 0 := by
  intro P
  have hF0 : 0 < F := by linarith
  have hinv : 1 / F ≤ 1 := by rw [div_le_one hF0]; exact hF
  have hden : 0 < (1 - p1) + p1 / F := by
    have h : (1 - p1) + p1 / F = 1 / F + (1 - p1) * (1 - 1 / F) := by ring
    have h1 : 0 ≤ (1 - p1) * (1 - 1 / F) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 < 1 / F := by positivity
    rw [h]; linarith
  have hden1 : (1 - p1) + p1 / F ≤ 1 := by
    have : p1 / F ≤ p1 := div_le_self hp1_0 hF
    linarith
  have hfden : G ≤ f * ((1 - p1) + p1 / F) := (div_le_iff₀ hden).1 hf
  have hf0 : 0 ≤ f := le_trans (div_nonneg hG hden.le) hf
  have hfG : G ≤ f := by
    have := mul_le_mul_of_nonneg_left hden1 hf0
    linarith
  rw [profit_eq]
  set PA := ∑ t ∈ P.A, p t with hPA
  have hPA0 : 0 ≤ PA := Finset.sum_nonneg fun t _ => hp0 t
  have hPA1 : PA ≤ 1 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun t _ _ => hp0 t) hsum
  have hc0low : ∀ S : Finset (Fin k), S ≠ Finset.univ → 1 ≤ cost k F 1 S := by
    intro S hS
    refine cost_ge_f_of_lt zero_le_one hF0 ?_
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)
    simpa using this
  have hc0nn : ∀ S : Finset (Fin k), 0 ≤ cost k F 1 S := fun S => cost_nonneg zero_le_one hF0 S
  by_cases ha : P.a = Finset.univ
  · -- Case 1: the abort set is everything; every attack set is a proper subset.
    have hσ : ∀ t ∈ P.A, 1 ≤ cost k F 1 (P.σ t) := fun t ht =>
      hc0low _ (fun h => P.abort_fresh t ht (h.trans ha.symm))
    have hsumge : PA ≤ ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) := by
      rw [hPA]
      exact Finset.sum_le_sum fun t ht => by
        have := mul_le_mul_of_nonneg_left (hσ t ht) (hp0 t)
        linarith
    have hc0a : 0 ≤ (1 - PA) * cost k F 1 P.a := mul_nonneg (by linarith) (hc0nn _)
    have hκ : PA ≤ ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) + (1 - PA) * cost k F 1 P.a := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hκ hf0, mul_nonneg hPA0 (sub_nonneg.2 hfG)]
  · have hca : 1 ≤ cost k F 1 P.a := hc0low _ ha
    have hca' : (1 - PA) * 1 ≤ (1 - PA) * cost k F 1 P.a :=
      mul_le_mul_of_nonneg_left hca (by linarith)
    by_cases hex : ∃ t0 ∈ P.A, P.σ t0 = Finset.univ
    · -- Case 2a: exactly one targeted class uses the full reveal set.
      obtain ⟨t0, ht0, hσ0⟩ := hex
      have hσne : ∀ t ∈ P.A.erase t0, 1 ≤ cost k F 1 (P.σ t) := by
        intro t ht
        refine hc0low _ fun h => ?_
        have htA := Finset.mem_of_mem_erase ht
        have : t = t0 :=
          P.inj (Finset.mem_coe.2 htA) (Finset.mem_coe.2 ht0) (h.trans hσ0.symm)
        exact (Finset.mem_erase.1 ht).1 this
      have e1 : p t0 * cost k F 1 (P.σ t0)
          + ∑ t ∈ P.A.erase t0, p t * cost k F 1 (P.σ t)
          = ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) :=
        Finset.add_sum_erase P.A (fun t => p t * cost k F 1 (P.σ t)) ht0
      have e2 : p t0 + ∑ t ∈ P.A.erase t0, p t = PA := Finset.add_sum_erase P.A p ht0
      have h3 : ∑ t ∈ P.A.erase t0, p t
          ≤ ∑ t ∈ P.A.erase t0, p t * cost k F 1 (P.σ t) :=
        Finset.sum_le_sum fun t ht => by
          have := mul_le_mul_of_nonneg_left (hσne t ht) (hp0 t)
          linarith
      have hcu : cost k F 1 (P.σ t0) = k / F := by rw [hσ0, cost_univ]; ring
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h4 : p t0 * (1 / F) ≤ p t0 * (k / F) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hk1 hF0.le) (hp0 t0)
      have h5 : 0 ≤ (p1 - p t0) * (1 - 1 / F) :=
        mul_nonneg (sub_nonneg.2 (hp1 t0)) (by linarith)
      rw [hcu] at e1
      have hκ : (1 - p1) + p1 / F
          ≤ ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) + (1 - PA) * cost k F 1 P.a := by
        simp only [div_eq_mul_inv] at h4 h5 e1 ⊢
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hκ hf0, mul_le_mul_of_nonneg_left hPA1 hG]
    · -- Case 2b: no targeted class uses the full reveal set.
      have hσ : ∀ t ∈ P.A, 1 ≤ cost k F 1 (P.σ t) := fun t ht =>
        hc0low _ (fun h => hex ⟨t, ht, h⟩)
      have hsumge : PA ≤ ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) := by
        rw [hPA]
        exact Finset.sum_le_sum fun t ht => by
          have := mul_le_mul_of_nonneg_left (hσ t ht) (hp0 t)
          linarith
      have hκ : 1 ≤ ∑ t ∈ P.A, p t * cost k F 1 (P.σ t) + (1 - PA) * cost k F 1 P.a := by
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hκ hf0, mul_le_mul_of_nonneg_left hPA1 hG]

/-- The selector plan: one selector and one executor; on a hit reveal only the executor
`(1 : Fin 2)`, on a miss reveal both. -/
def selectorPlan {ι : Type*} (t1 : ι) : Plan ι 2 where
  A := {t1}
  σ := fun _ => {1}
  inj := by
    intro x hx y hy _
    simp at hx hy
    rw [hx, hy]
  nonempty := fun _ _ => Finset.singleton_nonempty _
  a := Finset.univ
  abort_fresh := fun _ _ => by
    show ({1} : Finset (Fin 2)) ≠ Finset.univ
    decide

theorem profit_selectorPlan {ι : Type*} (p : ι → ℝ) (G F f : ℝ) (t1 : ι) :
    profit p G F f (selectorPlan t1)
      = p t1 * (G - f * (1 + 1 / F)) - (1 - p t1) * (2 * f / F) := by
  have c1 : cost 2 F f {1} = f * (1 + 1 / F) := by
    unfold cost
    rw [Finset.card_singleton]
    push_cast
    ring
  have c2 : cost 2 F f Finset.univ = 2 * f / F := by
    rw [cost_univ]
    push_cast
    ring
  unfold profit selectorPlan
  simp only [Finset.sum_singleton]
  rw [c1, c2]

/-- Block 11, item 42 (Theorem C(b)). -/
theorem thmC_b_selector {ι : Type*} {p : ι → ℝ} {G F f p1 : ℝ} (t1 : ι) (ht1 : p t1 = p1)
    (hp1 : 0 < p1) (hp1' : p1 ≤ 1) (hF : 0 < F) :
    (∃ P : Plan ι 2,
        profit p G F f P = p1 * (G - f * (1 + 1 / F)) - (1 - p1) * (2 * f / F)) ∧
    (f < finv G F p1 → ∃ P : Plan ι 2, 0 < profit p G F f P) := by
  have h := profit_selectorPlan p G F f t1
  rw [ht1] at h
  refine ⟨⟨selectorPlan t1, h⟩, fun hf => ⟨selectorPlan t1, ?_⟩⟩
  rw [h]
  exact (selector_profit_pos_iff p1 G F f hp1 hp1' hF).2 hf

/-- Block 11, item 43. -/
theorem thmC_b_any_m {ι : Type*} {p : ι → ℝ} {G F f p1 : ℝ} (t1 : ι) (ht1 : p t1 = p1)
    (hp1 : 0 < p1) (hp1' : p1 ≤ 1) (hF : 0 < F) {m : ℕ} (hm : 2 ≤ m) :
    f < finv G F p1 → ∃ k ≤ m, ∃ P : Plan ι k, 0 < profit p G F f P := by
  intro hf
  obtain ⟨P, hP⟩ := (thmC_b_selector (p := p) (G := G) (F := F) (f := f) t1 ht1 hp1 hp1' hF).2 hf
  exact ⟨2, hm, P, hP⟩

/-- The `k = 1` plan attacking class `t1` through the full reveal set and aborting through `∅`. -/
def exactPlan {ι : Type*} (t1 : ι) : Plan ι 1 where
  A := {t1}
  σ := fun _ => Finset.univ
  inj := by
    intro x hx y hy _
    simp at hx hy
    rw [hx, hy]
  nonempty := fun _ _ => Finset.univ_nonempty
  a := ∅
  abort_fresh := fun _ _ => Finset.univ_nonempty.ne_empty

theorem cost_one_empty (F f : ℝ) : cost 1 F f ∅ = f := by
  unfold cost; simp

theorem cost_one_univ (F f : ℝ) : cost 1 F f Finset.univ = f / F := by
  rw [cost_univ]; simp [div_eq_mul_inv]

theorem profit_exactPlan {ι : Type*} (p : ι → ℝ) (G F f : ℝ) (t1 : ι) :
    profit p G F f (exactPlan t1) = p t1 * (G - f / F) - (1 - p t1) * f := by
  unfold profit exactPlan
  simp only [Finset.sum_singleton]
  rw [cost_one_univ, cost_one_empty]

theorem fin1_cases (S : Finset (Fin 1)) : S = ∅ ∨ S = Finset.univ := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    ext y
    simp only [Finset.mem_univ, iff_true]
    have : y = x := Subsingleton.elim _ _
    rw [this]; exact hx

/-- Block 11, item 44 (Theorem C(a)). -/
theorem thmC_a_exact {ι : Type*} {p : ι → ℝ} {G F f p1 : ℝ} (t1 : ι) (ht1 : p t1 = p1)
    (hp1 : ∀ t, p t ≤ p1) (hp1pos : 0 < p1) (hp1lt : p1 < 1) (hF : 1 < F) (hG : 0 ≤ G)
    (hf : 0 ≤ f) :
    (∀ P : Plan ι 1, profit p G F f P ≤ 0) ↔ f1 G F p1 ≤ f := by
  have hF0 : 0 < F := by linarith
  have hlucid := lucid_m1_iff_f1 p1 G F f hp1pos hp1lt.le hF
  constructor
  · intro hall
    by_contra hlt
    have hpos : 0 < p1 * (G - f / F) - (1 - p1) * f := by
      by_contra hnn
      exact hlt (hlucid.1 (not_lt.1 hnn))
    have h := hall (exactPlan t1)
    rw [profit_exactPlan, ht1] at h
    linarith
  · intro hff P
    have hlu := hlucid.2 hff
    have hcoef : 0 ≤ G - f / F + f := by
      have : f / F ≤ f := div_le_self hf hF.le
      linarith
    rcases P.A.eq_empty_or_nonempty with hA | ⟨t, ht⟩
    · unfold profit
      rw [hA, Finset.sum_empty, Finset.sum_empty]
      have := cost_nonneg hf hF0 P.a
      linarith
    · have hσ : ∀ s ∈ P.A, P.σ s = Finset.univ := by
        intro s hs
        rcases fin1_cases (P.σ s) with h | h
        · exact absurd h (P.nonempty s hs).ne_empty
        · exact h
      have hσt := hσ t ht
      have ha : P.a = ∅ := by
        rcases fin1_cases P.a with h | h
        · exact h
        · exact absurd (hσt.trans h.symm) (P.abort_fresh t ht)
      have hA : P.A = {t} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨ht, fun t' ht' => ?_⟩
        exact P.inj (Finset.mem_coe.2 ht') (Finset.mem_coe.2 ht) ((hσ t' ht').trans hσt.symm)
      unfold profit
      rw [hA, ha, Finset.sum_singleton, Finset.sum_singleton, hσt, cost_one_univ,
        cost_one_empty]
      nlinarith [mul_nonneg (sub_nonneg.2 (hp1 t)) hcoef]

end Optionality
