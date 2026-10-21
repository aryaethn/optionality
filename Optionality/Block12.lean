import Mathlib.Tactic

/-!
Block 12: committee combinatorics for Theorem D (control, reconstruction, minimal harmful
coalition). Natural-number arithmetic only.

Committee of `n` members, threshold `t`, a coalition of size `w`, `h` honest members with
`h + w = n`. The coalition publishes `r ≤ w` of its shares; the batch executes iff `h + r ≥ t`.
-/

namespace Optionality

/-- `n - t + 1 ≤ w` and `n + 1 ≤ t + w` agree when `t ≤ n` (natural subtraction is safe). -/
theorem blocking_size_iff {n t w : ℕ} (htn : t ≤ n) : n - t + 1 ≤ w ↔ n + 1 ≤ t + w := by
  omega

/-- Block 12, item 45 (Theorem D(a), control): the coalition can force both outcomes iff
`|W| ≥ n - t + 1`. -/
theorem blocking_iff {n t h w : ℕ} (_ht1 : 1 ≤ t) (htn : t ≤ n) (hn : h + w = n) :
    ((∃ r ≤ w, h + r < t) ∧ (∃ r ≤ w, t ≤ h + r)) ↔ n - t + 1 ≤ w := by
  constructor
  · rintro ⟨⟨r, hr, h1⟩, _⟩
    omega
  · intro hw
    exact ⟨⟨0, Nat.zero_le _, by omega⟩, ⟨w, le_rfl, by omega⟩⟩

/-- Block 12, item 46 (Theorem D(a)): a non-blocking coalition cannot prevent execution. -/
theorem nonblocking_forces_execution {n t h w : ℕ} (hn : h + w = n) (hwt : w + t ≤ n) :
    ∀ r ≤ w, t ≤ h + r := by
  intro r hr
  omega

/-- Block 12, item 47 (Theorem D(b)): the last mover holds enough shares to reconstruct. -/
theorem last_mover_reconstructs {n t h w : ℕ} (hn : h + w = n) (htn : t ≤ n) :
    t ≤ h + w := by
  omega

/-- Block 12, item 48 (Theorem D(c)). -/
theorem min_harm_le {n t : ℕ} (_ht1 : 1 ≤ t) (htn : t ≤ n) :
    2 * min t (n - t + 1) ≤ n + 1 := by
  omega

/-- Block 12, item 49. -/
theorem min_harm_eq_iff {n t : ℕ} (_ht1 : 1 ≤ t) (htn : t ≤ n) :
    2 * min t (n - t + 1) = n + 1 ↔ 2 * t = n + 1 := by
  omega

/-- Block 12, item 50: equality is attained for odd `n`, at the majority threshold. -/
theorem min_harm_odd {n k t : ℕ} (hn : n = 2 * k + 1) (ht : t = k + 1) :
    2 * min t (n - t + 1) = n + 1 := by
  omega

/-- Block 12, item 51: for even `n` equality is never attained. -/
theorem min_harm_even {n k : ℕ} (hn : n = 2 * k) (_hk : 1 ≤ k) :
    ∀ t, 1 ≤ t → t ≤ n → 2 * min t (n - t + 1) ≤ n := by
  intro t ht1 htn
  omega

end Optionality
