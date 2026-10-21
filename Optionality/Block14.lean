import Optionality.Block9

/-!
Block 14: window feasibility and parameter arithmetic for blind simultaneous release (BSR).

Escrows are broadcast between `t1` and the escrow deadline `d = t1 + ω`; honest solvers have
sequential speed `νh`, the adversary `νa`; a pad has length `L` (sequential steps); the batch needs
values by `d + Ω`. The solver-speed ratio `νa / νh` is the parameter `γ`; no hardware claim is made.
-/

noncomputable section

set_option linter.deprecated false

namespace Optionality

/-- Block 14, item 59: a pad length exists iff the speed ratio is at most `Ω / ω`. -/
theorem bsr_window_iff {νh νa ω Ω : ℝ} (hνh : 0 < νh) (hνa : 0 < νa) (hω : 0 < ω)
    (_hΩ : 0 < Ω) :
    (∃ L > 0, L / νh ≤ Ω ∧ ω ≤ L / νa) ↔ νa / νh ≤ Ω / ω := by
  rw [div_le_div_iff₀ hνh hω]
  constructor
  · rintro ⟨L, _, h1, h2⟩
    rw [div_le_iff₀ hνh] at h1
    rw [le_div_iff₀ hνa] at h2
    linarith
  · intro h
    refine ⟨ω * νa, mul_pos hω hνa, ?_, ?_⟩
    · rw [div_le_iff₀ hνh]; linarith
    · rw [le_div_iff₀ hνa]

/-- Under the BSR substitution, `Private` is `ω ≤ L / νa`. -/
theorem bsr_private_iff {νh νa ω L : ℝ} (t1 : ℝ) (hνh : 0 < νh) (hνa : 0 < νa) :
    Private t1 (t1 + ω) (νa / νh) (L / νh) ↔ ω ≤ L / νa := by
  unfold Private
  have : (L / νh) / (νa / νh) = L / νa := by field_simp
  rw [this]
  constructor <;> intro h <;> linarith

/-- Under the BSR substitution, `Timely` is `L / νh ≤ Ω`. -/
theorem bsr_timely_iff {νh ω Ω L : ℝ} (t1 : ℝ) :
    Timely (t1 + ω) (t1 + ω + Ω) (L / νh) ↔ L / νh ≤ Ω := by
  unfold Timely
  constructor <;> intro h <;> linarith

/-- Under the BSR substitution, the ceiling `(t2 - th) / (t1 - tpub)` is `Ω / ω`. -/
theorem bsr_ceiling (t1 ω Ω : ℝ) :
    ((t1 + ω + Ω) - (t1 + ω)) / ((t1 + ω) - t1) = Ω / ω := by
  have e1 : (t1 + ω + Ω) - (t1 + ω) = Ω := by ring
  have e2 : (t1 + ω) - t1 = ω := by ring
  rw [e1, e2]

/-- Block 14, item 60: the BSR feasibility condition is an instance of `thmB_iff`
(Theorem 2(a)), with `tpub := t1`, `t1 := t1 + ω`, `th := t1 + ω`, `t2 := t1 + ω + Ω`,
`γ := νa / νh`, honest time `x := L / νh`. The bijection `x ↔ L = x * νh` matches the
quantifiers `∃ x > 0` and `∃ L > 0`. -/
theorem bsr_window_of_thmB {νh νa ω Ω : ℝ} (t1 : ℝ) (hνh : 0 < νh) (hνa : 0 < νa)
    (hω : 0 < ω) :
    (∃ L > 0, L / νh ≤ Ω ∧ ω ≤ L / νa) ↔ νa / νh ≤ Ω / ω := by
  have h := thmB_iff (tpub := t1) (t1 := t1 + ω) (γ := νa / νh) (th := t1 + ω)
    (t2 := t1 + ω + Ω) (by linarith) (div_pos hνa hνh)
  rw [bsr_ceiling] at h
  rw [← h]
  constructor
  · rintro ⟨L, hL, h1, h2⟩
    exact ⟨L / νh, div_pos hL hνh, (bsr_private_iff t1 hνh hνa).2 h2,
      (bsr_timely_iff t1).2 h1⟩
  · rintro ⟨x, hx, hp, ht⟩
    have e : x * νh / νh = x := by field_simp
    rw [← e] at hp ht
    exact ⟨x * νh, mul_pos hx hνh, (bsr_timely_iff t1).1 ht,
      (bsr_private_iff t1 hνh hνa).1 hp⟩

/-- Opening window equals slot length minus escrow window: `γ_max = (T - ω) / ω`. -/
def gmaxBSR (T ω : ℝ) : ℝ := (T - ω) / ω

/-- Block 14, item 61 (monotonicity). -/
theorem gmaxBSR_strictAnti {T : ℝ} (hT : 0 < T) :
    StrictAntiOn (gmaxBSR T) (Set.Ioo 0 T) := by
  intro a ha b hb hab
  obtain ⟨ha0, _⟩ := ha
  obtain ⟨hb0, _⟩ := hb
  unfold gmaxBSR
  rw [div_lt_div_iff₀ hb0 ha0]
  nlinarith [mul_pos hT (sub_pos.2 hab)]

/-- Block 14, item 61 (the paper's four margins). -/
theorem gmaxBSR_values :
    gmaxBSR 12 1 = 11 ∧ gmaxBSR 12 2 = 5 ∧ gmaxBSR 6 1 = 5 ∧ gmaxBSR 6 2 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gmaxBSR]

/-- Pad length `L = Ω * νh` (sequential steps the honest solver completes in the opening window). -/
def padLength (Ω νh : ℝ) : ℝ := Ω * νh

/-- Block 14, item 62: `70 ns` per step and `Ω = 10 s` give `L ≈ 1.4 × 10^8`. -/
theorem pad_length_example :
    1.4 * 10 ^ 8 < padLength 10 (1 / (70 * 10 ^ (-9 : ℤ))) ∧
    padLength 10 (1 / (70 * 10 ^ (-9 : ℤ))) < 1.5 * 10 ^ 8 := by
  unfold padLength
  constructor <;> norm_num

end Optionality
