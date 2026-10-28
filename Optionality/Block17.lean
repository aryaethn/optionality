import Optionality.Block14

/-!
Block 17: blind simultaneous release on a host design with window `W = t2 - t1`.

The window available to the escrow protocol is a property of the host design (for the ticket-first
threshold design: from fast confirmation of `B[n+1]` to the start of slot `n+2`), not the slot
length. Feasibility is `γ ≤ (W - ω) / ω = gmaxBSR W ω` (Block 14, `bsr_window_iff`). The numeric
inputs (when fast confirmation happens, the ePBS deadlines, how Herold's design maps onto `t1`,
`d`, `t2`) are modelling inputs, not theorems. Imports are narrow: `Block14` brings in `Block9`
(Theorem 2: `thmB_iff`, `thmB_b_opt`).
-/

noncomputable section

set_option linter.deprecated false

namespace Optionality

/-- Block 17, item 85: a shorter host window lowers the ceiling. -/
theorem gmaxBSR_strictMono_window {ω : ℝ} (hω : 0 < ω) :
    StrictMono (fun W => gmaxBSR W ω) := by
  intro a b hab
  show gmaxBSR a ω < gmaxBSR b ω
  unfold gmaxBSR
  rw [div_lt_div_iff₀ hω hω]
  nlinarith

/-- Block 17, item 86: ticket-first design, twelve-second slots (`W = 8` or `9`). -/
theorem gmaxBSR_values_ticketFirst :
    gmaxBSR 8 2 = 3 ∧ gmaxBSR 9 2 = 7 / 2 ∧ gmaxBSR 8 1 = 7 ∧ gmaxBSR 9 1 = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gmaxBSR]

/-- Block 17, item 87: ticket-first design, six-second slots (`W = 4` or `9/2`). -/
theorem gmaxBSR_values_six :
    gmaxBSR 4 2 = 1 ∧ gmaxBSR (9 / 2) 2 = 5 / 4 ∧ gmaxBSR 4 1 = 3 ∧ gmaxBSR (9 / 2) 1 = 7 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [gmaxBSR]

/-- Block 17, item 88: the whole range `8 ≤ W ≤ 9`. -/
theorem gmaxBSR_range_ticketFirst {W : ℝ} (h8 : 8 ≤ W) (h9 : W ≤ 9) :
    3 ≤ gmaxBSR W 2 ∧ gmaxBSR W 2 ≤ 7 / 2 ∧ 7 ≤ gmaxBSR W 1 ∧ gmaxBSR W 1 ≤ 8 := by
  unfold gmaxBSR
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Block 17, item 89: pad lengths `L = Θ · νh` at `70 ns` per step for `Θ = 6, 7, 11` s
(`Θ = W - ω`; Lean's `padLength` calls its first argument `Ω`). -/
theorem pad_length_examples :
    (8.5 * 10 ^ 7 < padLength 6 (1 / (70 * 10 ^ (-9 : ℤ))) ∧
      padLength 6 (1 / (70 * 10 ^ (-9 : ℤ))) < 8.6 * 10 ^ 7) ∧
    padLength 7 (1 / (70 * 10 ^ (-9 : ℤ))) = 10 ^ 8 ∧
    (1.5 * 10 ^ 8 < padLength 11 (1 / (70 * 10 ^ (-9 : ℤ))) ∧
      padLength 11 (1 / (70 * 10 ^ (-9 : ℤ))) < 1.6 * 10 ^ 8) := by
  unfold padLength
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩ <;> norm_num

/-- The second closed form of Theorem 2(b): `γ_max = 1 + Δ / (δ + w)` (honest solvers start at
broadcast). -/
theorem gmaxOpt_eq_one_add {δ Δ w : ℝ} (h : δ + w ≠ 0) :
    gmaxOpt δ Δ w = 1 + Δ / (δ + w) := by
  unfold gmaxOpt
  rw [one_add_div h]
  congr 1
  ring

/-- Block 17, item 90: the sender-side time-lock ceiling of the ticket-first design. This is
Theorem 2(b) (`thmB_b_opt`, honest solvers starting at broadcast) with `w = 0` and `δ = Δ > 0`:
`γ_max = 1 + Δ/δ = 2`. -/
theorem ticketFirst_sender_ceiling {t0 δ Δ w tpub t1 t2 th : ℝ} (hδ : 0 < δ) (hΔ : Δ = δ)
    (hw : w = 0) (htpub : tpub = t0 - w) (ht1 : t1 = t0 + δ) (ht2 : t2 = t0 + δ + Δ)
    (hth : th = tpub) :
    (t2 - th) / (t1 - tpub) = 2 := by
  rw [thmB_b_opt htpub ht1 ht2 hth]
  unfold gmaxOpt
  rw [hΔ, hw, add_zero, add_zero, div_eq_iff hδ.ne']
  ring

/-- Block 17, item 90 (numeric instance): `tpub = 1/2`, `t1 = 12`, `th = tpub`, `t2 = 24` is
Theorem 2(b) with `t0 = tpub`, `w = 0`, `δ = 23/2`, `Δ = 12`; the ceiling is `47/23 ≈ 2.04`. -/
theorem ticketFirst_numeric_ceiling {tpub t1 th t2 : ℝ} (htpub : tpub = 1 / 2) (ht1 : t1 = 12)
    (hth : th = tpub) (ht2 : t2 = 24) :
    (t2 - th) / (t1 - tpub) = 47 / 23 ∧ 2 < (t2 - th) / (t1 - tpub) ∧
      (t2 - th) / (t1 - tpub) < 2.05 := by
  have h : (t2 - th) / (t1 - tpub) = gmaxOpt (23 / 2) 12 0 :=
    thmB_b_opt (t0 := 1 / 2) (δ := 23 / 2) (Δ := 12) (w := 0)
      (by rw [htpub]; norm_num) (by rw [ht1]; norm_num) (by rw [ht2]; norm_num) hth
  have h2 : gmaxOpt (23 / 2) 12 0 = 47 / 23 := by
    unfold gmaxOpt; norm_num
  rw [h, h2]
  refine ⟨rfl, ?_, ?_⟩ <;> norm_num

/-- The same instance through Theorem 2(a): some difficulty is feasible iff `γ ≤ 47/23`. -/
theorem ticketFirst_sender_feasible_iff {γ : ℝ} (hγ : 0 < γ) :
    (∃ x > 0, Private (1 / 2) 12 γ x ∧ Timely (1 / 2) 24 x) ↔ γ ≤ 47 / 23 := by
  have h := thmB_iff (tpub := 1 / 2) (t1 := 12) (th := 1 / 2) (t2 := 24) (γ := γ)
    (by norm_num) hγ
  rw [h]
  norm_num

end Optionality
