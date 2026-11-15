import Rigidity.Semicircle.Basic

/-!
# Algebra of the Stieltjes transform of the semicircle law

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `Im z > 0`, `m = msc z` and `w = √(z-2) √(z+2)` (so `w = z + 2m`), this file proves the
factorisation `1 - m² = -m w` with its norm form (Lemma 3.1 (d)), the formulas for `Im w`,
`Im m` and the quantities `P`, `Q` (Lemma 3.1 (e)), the bounds for `|Re z| ≥ 4` (Lemma 3.1 (g)),
the reflection `m(-z̄) = -conj m(z)` (Lemma 3.1 (h)), and holomorphy of `msc` on the upper half
plane (Lemma 3.1 (i)).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The norm of a principal square root is the square root of the norm. -/
private lemma semicircle_norm_sqrt (ζ : ℂ) : ‖Complex.sqrt ζ‖ = Real.sqrt ‖ζ‖ := by
  have h : ‖Complex.sqrt ζ‖ ^ 2 = ‖ζ‖ := by
    rw [← norm_pow]
    simp only [Complex.sqrt, Complex.cpow_ofNat_inv_pow]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- `w = z + 2m` for `w = √(z-2) √(z+2)` and `m = msc z`. -/
private lemma semicircle_w_eq (z : ℂ) :
    Complex.sqrt (z - 2) * Complex.sqrt (z + 2) = 2 * msc z + z := by
  unfold msc
  ring

/-- `w² = z² - 4` for `w = √(z-2) √(z+2)`. -/
private lemma semicircle_w_sq (z : ℂ) :
    (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) ^ 2 = z ^ 2 - 4 := by
  have h : ∀ ζ : ℂ, Complex.sqrt ζ ^ 2 = ζ := fun ζ => by
    simp only [Complex.sqrt, Complex.cpow_ofNat_inv_pow]
  rw [mul_pow, h, h]
  ring

/-- Lemma 3.1 (d). -/
theorem one_sub_msc_sq {z : ℂ} (hz : 0 < z.im) :
    1 - msc z ^ 2 = -msc z * (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) ∧
      ‖1 - msc z ^ 2‖ = ‖msc z‖ * Real.sqrt ‖z - 2‖ * Real.sqrt ‖z + 2‖ := by
  have h := msc_sq_add hz
  have h1 : 1 - msc z ^ 2 = -msc z * (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) := by
    rw [semicircle_w_eq]
    linear_combination h
  refine ⟨h1, ?_⟩
  rw [h1, norm_mul, norm_neg, norm_mul, semicircle_norm_sqrt, semicircle_norm_sqrt]
  ring

/-- Lemma 3.1 (e). -/
theorem msc_im_eq_P {z : ℂ} (hz : 0 < z.im) :
    let P := ‖z - 2‖ * ‖z + 2‖ - ‖z‖ ^ 2 + 4
    let Q := ‖z - 2‖ * ‖z + 2‖ + ‖z‖ ^ 2 - 4
    let w := Complex.sqrt (z - 2) * Complex.sqrt (z + 2)
    w.im ^ 2 = z.im ^ 2 + P / 2 ∧ (msc z).im = P / (4 * (w.im + z.im)) ∧
      P * Q = 16 * z.im ^ 2 ∧ 0 < P ∧ 0 < Q := by
  intro P Q w
  have hm := msc_im_pos hz
  have hw : w = 2 * msc z + z := semicircle_w_eq z
  have hwim : w.im = 2 * (msc z).im + z.im := by
    rw [hw]; simp
  have hbz : z.im < w.im := by linarith
  have hw2 : w ^ 2 = z ^ 2 - 4 := semicircle_w_sq z
  -- norms
  have hA : ‖z - 2‖ ^ 2 = (z.re - 2) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hB : ‖z + 2‖ ^ 2 = (z.re + 2) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hN : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hR : (‖z - 2‖ * ‖z + 2‖) ^ 2 =
      ((z.re - 2) ^ 2 + z.im ^ 2) * ((z.re + 2) ^ 2 + z.im ^ 2) := by
    rw [mul_pow, hA, hB]
  have hwn : ‖w‖ ^ 2 = ‖z - 2‖ * ‖z + 2‖ := by
    have : ‖w‖ = Real.sqrt ‖z - 2‖ * Real.sqrt ‖z + 2‖ := by
      simp only [w, norm_mul, semicircle_norm_sqrt]
    rw [this, mul_pow, Real.sq_sqrt (norm_nonneg _), Real.sq_sqrt (norm_nonneg _)]
  have hwn' : w.re ^ 2 + w.im ^ 2 = ‖z - 2‖ * ‖z + 2‖ := by
    rw [← hwn, Complex.sq_norm, Complex.normSq_apply]; ring
  have hre := congrArg Complex.re hw2
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.re_ofNat] at hre
  have hP : P = 2 * (w.im ^ 2 - z.im ^ 2) := by
    simp only [P]
    nlinarith
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hPQ : P * Q = 16 * z.im ^ 2 := by
    simp only [P, Q]
    nlinarith
  refine ⟨by rw [hP]; ring, ?_, hPQ, hPpos, ?_⟩
  · have hpos : 0 < 4 * (w.im + z.im) := by linarith
    rw [eq_div_iff hpos.ne', hP, hwim]
    ring
  · by_contra hQ
    have hQ := not_lt.mp hQ
    nlinarith [mul_nonneg hPpos.le (neg_nonneg.mpr hQ), sq_pos_of_pos hz]

/-- Lemma 3.1 (g). -/
theorem msc_far {z : ℂ} (hz : 0 < z.im) (hE : 4 ≤ |z.re|) :
    ‖msc z‖ ≤ 1 / 3 ∧ (msc z).im ≤ z.im / 8 ∧ 8 / 9 ≤ ‖1 - msc z ^ 2‖ := by
  have h := msc_sq_add hz
  have hm := msc_im_pos hz
  have hn := norm_msc_lt_one hz
  have hmul : msc z * (z + msc z) = -1 := by linear_combination h
  have hnm : ‖msc z‖ * ‖z + msc z‖ = 1 := by
    rw [← norm_mul, hmul]; simp
  have hzre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hS : 3 ≤ ‖z + msc z‖ := by
    have h1 : ‖z‖ - ‖msc z‖ ≤ ‖z + msc z‖ := by
      have := norm_sub_norm_le z (-msc z)
      simpa [sub_eq_add_neg] using this
    linarith
  have hn0 : 0 ≤ ‖msc z‖ := norm_nonneg _
  have h1 : ‖msc z‖ ≤ 1 / 3 := by nlinarith
  refine ⟨h1, ?_, ?_⟩
  · have hI := (msc_im_mul hz).1
    nlinarith [mul_le_mul_of_nonneg_left (show (8 : ℝ) ≤ ‖z + msc z‖ ^ 2 - 1 by nlinarith) hm.le]
  · have h2 := norm_sub_norm_le (1 : ℂ) (msc z ^ 2)
    rw [norm_one, norm_pow] at h2
    nlinarith

/-- Lemma 3.1 (i). -/
theorem differentiableOn_msc : DifferentiableOn ℂ msc {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz : 0 < z.im := hz
  have hp : z - 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hz.ne'
  have hq : z + 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hz.ne'
  have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z - 2)) z :=
    (Complex.differentiableAt_sqrt hp).comp z (differentiableAt_id.sub_const 2)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (z + 2)) z :=
    (Complex.differentiableAt_sqrt hq).comp z (differentiableAt_id.add_const 2)
  have : DifferentiableAt ℂ msc z := by
    unfold msc
    exact ((differentiableAt_id.neg).add (h1.mul h2)).div_const 2
  exact this.differentiableWithinAt

end Rigidity
