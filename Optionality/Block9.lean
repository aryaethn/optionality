import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Monotone.Basic

/-!
Block 9: Theorem B (timing feasibility of forced opening by public computation).
Pure real analysis; no probability.
-/

noncomputable section

set_option linter.deprecated false

namespace Optionality

/-- Opening is not finished by an adversary of speedup `γ` before the ordering lock `t1`. -/
def Private (tpub t1 γ x : ℝ) : Prop := t1 ≤ tpub + x / γ

/-- The honest solver finishes by `t2`. -/
def Timely (th t2 x : ℝ) : Prop := th + x ≤ t2

/-- `γ_max` when honest solvers start at inclusion (`t_h = t_0`). -/
def gmaxPess (δ Δ w : ℝ) : ℝ := (δ + Δ) / (δ + w)

/-- `γ_max` when honest solvers start at broadcast (`t_h = t_pub`). -/
def gmaxOpt (δ Δ w : ℝ) : ℝ := (δ + Δ + w) / (δ + w)

/-- Block 9, item 23. No relation between `th` and `tpub` is needed. -/
theorem thmB_iff {tpub t1 γ th t2 : ℝ} (hlt : tpub < t1) (hγ : 0 < γ) :
    (∃ x > 0, Private tpub t1 γ x ∧ Timely th t2 x) ↔ γ ≤ (t2 - th) / (t1 - tpub) := by
  have hd : 0 < t1 - tpub := sub_pos.2 hlt
  rw [le_div_iff₀ hd]
  constructor
  · rintro ⟨x, _, hp, ht⟩
    unfold Private at hp
    unfold Timely at ht
    have h1 : t1 - tpub ≤ x / γ := by linarith
    rw [le_div_iff₀ hγ] at h1
    linarith
  · intro h
    refine ⟨γ * (t1 - tpub), mul_pos hγ hd, ?_, ?_⟩
    · unfold Private
      have : γ * (t1 - tpub) / γ = t1 - tpub := by field_simp
      rw [this]; linarith
    · unfold Timely; linarith

/-- Block 9, item 24. -/
theorem thmB_b_pess {t0 δ Δ w tpub t1 t2 th : ℝ} (htpub : tpub = t0 - w) (ht1 : t1 = t0 + δ)
    (ht2 : t2 = t0 + δ + Δ) (hth : th = t0) :
    (t2 - th) / (t1 - tpub) = gmaxPess δ Δ w := by
  rw [htpub, ht1, ht2, hth]
  unfold gmaxPess
  have e1 : t0 + δ + Δ - t0 = δ + Δ := by ring
  have e2 : t0 + δ - (t0 - w) = δ + w := by ring
  rw [e1, e2]

/-- Block 9, item 25. -/
theorem thmB_b_opt {t0 δ Δ w tpub t1 t2 th : ℝ} (htpub : tpub = t0 - w) (ht1 : t1 = t0 + δ)
    (ht2 : t2 = t0 + δ + Δ) (hth : th = tpub) :
    (t2 - th) / (t1 - tpub) = gmaxOpt δ Δ w := by
  rw [hth, htpub, ht1, ht2]
  unfold gmaxOpt
  have e1 : t0 + δ + Δ - (t0 - w) = δ + Δ + w := by ring
  have e2 : t0 + δ - (t0 - w) = δ + w := by ring
  rw [e1, e2]

/-- Block 9, item 26. -/
theorem gmaxPess_strictAnti {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) :
    StrictAntiOn (gmaxPess δ Δ) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  unfold gmaxPess
  rw [div_lt_div_iff₀ (by linarith [Set.mem_Ici.1 hb]) (by linarith)]
  nlinarith [mul_pos (by linarith : 0 < δ + Δ) (sub_pos.2 hab)]

/-- Block 9, item 27. -/
theorem gmaxOpt_strictAnti {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) :
    StrictAntiOn (gmaxOpt δ Δ) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  unfold gmaxOpt
  rw [div_lt_div_iff₀ (by linarith [Set.mem_Ici.1 hb]) (by linarith)]
  nlinarith [mul_pos hΔ (sub_pos.2 hab)]

/-- Block 9, item 28. -/
theorem gmaxOpt_tendsto_one {δ : ℝ} (Δ : ℝ) (_hδ : 0 < δ) :
    Filter.Tendsto (gmaxOpt δ Δ) Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun w : ℝ => δ + w) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ Filter.tendsto_id
  have h2 : Filter.Tendsto (fun w : ℝ => Δ / (δ + w)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h1
  have h3 : Filter.Tendsto (fun w : ℝ => 1 + Δ / (δ + w)) Filter.atTop (nhds 1) := by
    simpa using h2.const_add 1
  refine Filter.Tendsto.congr' ?_ h3
  filter_upwards [Filter.eventually_gt_atTop (-δ)] with w hw
  have hne : δ + w ≠ 0 := by linarith
  unfold gmaxOpt
  field_simp
  ring

/-- Block 9, item 29. -/
theorem thmB_wait_threshold {γ δ Δ w : ℝ} (hγ : 1 < γ) (hδ : 0 < δ) (hw : 0 ≤ w) :
    gmaxOpt δ Δ w < γ ↔ (δ + Δ - γ * δ) / (γ - 1) < w := by
  have hd : 0 < δ + w := by linarith
  unfold gmaxOpt
  rw [div_lt_iff₀ hd, div_lt_iff₀ (sub_pos.2 hγ)]
  constructor <;> intro h <;> nlinarith [h]

/-- Block 9, item 30. -/
theorem gmaxOpt_lt_two {δ Δ w : ℝ} (hδ : 0 < δ) (hw : 0 ≤ w) (hΔ : Δ < δ + w) :
    gmaxOpt δ Δ w < 2 := by
  have hd : 0 < δ + w := by linarith
  unfold gmaxOpt
  rw [div_lt_iff₀ hd]
  linarith

/-- Block 9, item 31. -/
theorem frontier_early_antitone {G : ℝ → ℝ} (hG : Monotone G) {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun x => 1 - G (x / c)) (Set.Ioi 0) := by
  intro x _ y _ hxy
  have := hG (div_le_div_of_nonneg_right hxy hc.le)
  simp only
  linarith

/-- Block 9, item 32. -/
theorem frontier_late_monotone {H : ℝ → ℝ} (hH : Monotone H) {d : ℝ} (hd : 0 < d) :
    MonotoneOn (fun x => 1 - H (d / x)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have := hH (div_le_div_of_nonneg_left hd.le hx' hxy)
  simp only
  linarith

/-- Block 9, item 33. -/
theorem table_checks :
    gmaxPess 1 8 0 = 9 ∧ gmaxPess 2 12 0 = 7 ∧ gmaxOpt 2 8 12 = 11 / 7 ∧
    gmaxPess 4 12 60 = 1 / 4 ∧ gmaxOpt 1 12 12 = 25 / 13 ∧ gmaxOpt 1 12 12 < 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [gmaxPess, gmaxOpt]

end Optionality
