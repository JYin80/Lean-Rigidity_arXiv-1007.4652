import Mathlib

/-!
# Bounds for the complex logarithm near `1`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `‖ζ‖ ≤ 1/2` the principal logarithm satisfies the three Taylor remainder bounds (L1)–(L3) of
Section 11.3: `‖Log(1+ζ)‖ ≤ 2‖ζ‖`, and the remainders after the terms of degree `2` and `3`
are at most `2/3 ‖ζ‖³` and `1/2 ‖ζ‖⁴`.  They are the instances `n = 0, 2, 3` of the remainder bound
`‖ζ‖^(n+1) (1 - ‖ζ‖)⁻¹ / (n+1)`, using `(1 - ‖ζ‖)⁻¹ ≤ 2`.
-/

open Real

namespace Rigidity

/-- The remainder bound `‖log (1 + ζ) - logTaylor (n+1) ζ‖ ≤ 2 ‖ζ‖^(n+1) / (n+1)` on the disc
`‖ζ‖ ≤ 1/2`. -/
private lemma logBounds_remainder (n : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖Complex.log (1 + ζ) - Complex.logTaylor (n + 1) ζ‖ ≤ 2 * ‖ζ‖ ^ (n + 1) / (n + 1) := by
  have h1 : ‖ζ‖ < 1 := by linarith
  refine (Complex.norm_log_sub_logTaylor_le n h1).trans ?_
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hinv : (1 - ‖ζ‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  rw [div_le_div_iff_of_pos_right hpos]
  have := pow_nonneg (norm_nonneg ζ) (n + 1)
  nlinarith

/-- (L1). -/
theorem norm_clog_one_add_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) : ‖Complex.log (1 + ζ)‖ ≤ 2 * ‖ζ‖ := by
  have h := logBounds_remainder 0 hζ
  simpa [Complex.logTaylor_succ, Complex.logTaylor_zero] using h

/-- (L2). -/
theorem norm_clog_one_add_sub_two_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2‖ ≤ 2 / 3 * ‖ζ‖ ^ 3 := by
  have h := logBounds_remainder 2 hζ
  have e : Complex.logTaylor (2 + 1) ζ = ζ - ζ ^ 2 / 2 := by
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring
  rw [e] at h
  have e2 : Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2 = Complex.log (1 + ζ) - (ζ - ζ ^ 2 / 2) := by ring
  rw [e2]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- (L3). -/
theorem norm_clog_one_add_sub_three_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2 - ζ ^ 3 / 3‖ ≤ 1 / 2 * ‖ζ‖ ^ 4 := by
  have h := logBounds_remainder 3 hζ
  have e : Complex.logTaylor (3 + 1) ζ = ζ - ζ ^ 2 / 2 + ζ ^ 3 / 3 := by
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring
  rw [e] at h
  have e2 : Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2 - ζ ^ 3 / 3 =
      Complex.log (1 + ζ) - (ζ - ζ ^ 2 / 2 + ζ ^ 3 / 3) := by ring
  rw [e2]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Rigidity
