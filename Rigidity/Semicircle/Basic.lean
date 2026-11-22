module

public import Mathlib
public import Rigidity.MainDefs

@[expose] public section

/-!
# The Stieltjes transform of the semicircle law

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

`msc z = (-z + √(z-2) √(z+2)) / 2`, with principal square roots, is the Stieltjes transform
of the semicircle law on the upper half plane `Im z > 0` (NP v1.1 §3.1, Lemma 3.1; [EYY, (2.12),
(2.13)]).  This file proves, for `Im z > 0` and `m = msc z`: the quadratic equation
`m² + z m + 1 = 0` (Lemma 3.1 (a)), `Im m > 0` and `m + 1/(z + m) = 0` ([EYY, (2.12)]), the
identities of Lemma 3.1 (b), `|m| < 1` ([EYY, (3.12)]), the bounds of Lemma 3.1 (c), and the
Lipschitz bound of Lemma 3.1 (f).

The proofs use the first-quadrant property (S1) of NP v1.1 §3.1 for the principal square root of
a number in the upper half plane, and `Im (√(z-2) √(z+2)) > Im z` (proof of Lemma 3.1 (a)).
-/

open MeasureTheory Real
open scoped ENNReal

namespace Rigidity

/-- The principal square root squares back: `(√ζ)² = ζ`. -/
private lemma semicircle_sqrt_sq (ζ : ℂ) : Complex.sqrt ζ ^ 2 = ζ := by
  simp only [Complex.sqrt, Complex.cpow_ofNat_inv_pow]

/-- (S1) of NP v1.1 §3.1: for `Im ζ > 0` the principal square root of `ζ` has positive real
and imaginary parts. -/
private lemma semicircle_sqrt_quadrant {ζ : ℂ} (h : 0 < ζ.im) :
    0 < (Complex.sqrt ζ).re ∧ 0 < (Complex.sqrt ζ).im := by
  have h2 := semicircle_sqrt_sq ζ
  have him : 2 * ((Complex.sqrt ζ).re * (Complex.sqrt ζ).im) = ζ.im := by
    have := congrArg Complex.im h2
    simp only [pow_two, Complex.mul_im] at this
    linarith
  have hre : 0 ≤ (Complex.sqrt ζ).re := by
    unfold Complex.sqrt
    rw [Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hne : (Complex.sqrt ζ).re ≠ 0 := by
    intro h0
    rw [h0] at him
    linarith
  have hpos : 0 < (Complex.sqrt ζ).re := lt_of_le_of_ne hre (Ne.symm hne)
  refine ⟨hpos, ?_⟩
  by_contra hb
  have hb := not_lt.mp hb
  nlinarith [mul_nonneg hpos.le (neg_nonneg.mpr hb)]

/-- With `w = √(z-2) √(z+2)`: `w² = z² - 4` and `Im w > Im z` (proof of Lemma 3.1 (a)). -/
private lemma semicircle_prod_facts {z : ℂ} (hz : 0 < z.im) :
    (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) ^ 2 = z ^ 2 - 4 ∧
      z.im < (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)).im := by
  have hp : 0 < (z - 2 : ℂ).im := by simpa using hz
  have hq : 0 < (z + 2 : ℂ).im := by simpa using hz
  obtain ⟨hp1, hp2⟩ := semicircle_sqrt_quadrant hp
  obtain ⟨hq1, hq2⟩ := semicircle_sqrt_quadrant hq
  have hw2 : (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) ^ 2 = z ^ 2 - 4 := by
    rw [mul_pow, semicircle_sqrt_sq, semicircle_sqrt_sq]
    ring
  refine ⟨hw2, ?_⟩
  set w := Complex.sqrt (z - 2) * Complex.sqrt (z + 2) with hw
  have hwim : 0 < w.im := by
    rw [hw, Complex.mul_im]
    nlinarith [mul_pos hp1 hq2, mul_pos hp2 hq1]
  have hre := congrArg Complex.re hw2
  have him := congrArg Complex.im hw2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] at hre him
  norm_num at hre him
  by_contra hle
  have hle := not_lt.mp hle
  have hab : w.re * w.im = z.re * z.im := by linarith
  have hsq : w.re ^ 2 - w.im ^ 2 = z.re ^ 2 - z.im ^ 2 - 4 := by nlinarith
  have hb2 : w.im ^ 2 ≤ z.im ^ 2 := by nlinarith
  have h1 : (w.re * w.im) ^ 2 = (z.re * z.im) ^ 2 := by rw [hab]
  have h2 : w.re ^ 2 * w.im ^ 2 ≤ w.re ^ 2 * z.im ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
  have h3 : z.re ^ 2 * z.im ^ 2 ≤ w.re ^ 2 * z.im ^ 2 := by nlinarith
  have h4 : z.re ^ 2 ≤ w.re ^ 2 := le_of_mul_le_mul_right h3 (by positivity)
  linarith

/-- A root `m` of `X² + zX + 1` satisfies `m (z + m) = -1`. -/
private lemma semicircle_mul {z m : ℂ} (h : m ^ 2 + z * m + 1 = 0) : m * (z + m) = -1 := by
  linear_combination h

/-- `z + m ≠ 0` for a root `m` of `X² + zX + 1`. -/
private lemma semicircle_add_ne {z m : ℂ} (h : m ^ 2 + z * m + 1 = 0) : z + m ≠ 0 := by
  intro h0
  have h1 := semicircle_mul h
  rw [h0, mul_zero] at h1
  norm_num at h1

/-- `m = -1 / (z + m)` for a root `m` of `X² + zX + 1`. -/
private lemma semicircle_inv {z m : ℂ} (h : m ^ 2 + z * m + 1 = 0) : 1 / (z + m) = -m := by
  rw [div_eq_iff (semicircle_add_ne h)]
  linear_combination h

/-- `|m| |z + m| = 1` for a root `m` of `X² + zX + 1`. -/
private lemma semicircle_norm_mul {z m : ℂ} (h : m ^ 2 + z * m + 1 = 0) :
    ‖m‖ * ‖z + m‖ = 1 := by
  rw [← norm_mul, semicircle_mul h]
  simp

/-- The first identity of Lemma 3.1 (b), for any root of `X² + zX + 1`. -/
private lemma semicircle_im_mul {z m : ℂ} (h : m ^ 2 + z * m + 1 = 0) :
    m.im * (‖z + m‖ ^ 2 - 1) = z.im := by
  have h1 := congrArg Complex.re (semicircle_mul h)
  have h2 := congrArg Complex.im (semicircle_mul h)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im] at h1 h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im]
  linear_combination (z.re + m.re) * h2 - (z.im + m.im) * h1

/-- The second identity of Lemma 3.1 (b), cleared of denominators. -/
private lemma semicircle_norm_sq {z m : ℂ} (h : m ^ 2 + z * m + 1 = 0) :
    ‖m‖ ^ 2 * (m.im + z.im) = m.im := by
  have hI := semicircle_im_mul h
  have hab : ‖m‖ ^ 2 * ‖z + m‖ ^ 2 = 1 := by
    rw [← mul_pow, semicircle_norm_mul h]
    norm_num
  linear_combination (-‖m‖ ^ 2) * hI + m.im * hab

/-- `|z + m| > 1`, from the first identity of Lemma 3.1 (b). -/
private lemma semicircle_one_lt_norm {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im)
    (h : m ^ 2 + z * m + 1 = 0) : 1 < ‖z + m‖ := by
  have hI := semicircle_im_mul h
  have h1 : 0 < ‖z + m‖ ^ 2 - 1 := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith [mul_nonneg hm.le (neg_nonneg.mpr hc)]
  by_contra hc
  have hc := not_lt.mp hc
  nlinarith [norm_nonneg (z + m)]

/-- `|m| = 1 / |z + m| < 1`, as in the proof of Lemma 3.1 (b). -/
private lemma semicircle_norm_lt_one {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im)
    (h : m ^ 2 + z * m + 1 = 0) : ‖m‖ < 1 := by
  have h1 := semicircle_norm_mul h
  have h2 := semicircle_one_lt_norm hz hm h
  by_contra hc
  have hc := not_lt.mp hc
  nlinarith [norm_nonneg m]

/-- Lemma 3.1 (a): `m_sc` is a root of `X² + zX + 1`. -/
private lemma semicircle_msc_sq_add {z : ℂ} (hz : 0 < z.im) :
    msc z ^ 2 + z * msc z + 1 = 0 := by
  obtain ⟨hw2, -⟩ := semicircle_prod_facts hz
  unfold msc
  linear_combination (1 / 4 : ℂ) * hw2

/-- `Im m_sc(z) = (Im w - Im z) / 2 > 0`, proof of Lemma 3.1 (a). -/
private lemma semicircle_msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im := by
  obtain ⟨-, hw⟩ := semicircle_prod_facts hz
  unfold msc
  have h : ((-z + Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) / 2).im =
      ((Complex.sqrt (z - 2) * Complex.sqrt (z + 2)).im - z.im) / 2 := by
    simp [Complex.div_ofNat_im]
    ring
  rw [h]
  linarith

/-- Lower bound on `1 - |m_sc|²` on `{Im ≥ η₀}`, as in the proof of Lemma 3.1 (f). -/
private lemma semicircle_lower {z : ℂ} {η₀ : ℝ} (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) :
    η₀ ≤ (1 - ‖msc z‖ ^ 2) * (η₀ + 1) := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη₀ hz
  have h := semicircle_msc_sq_add hz0
  have hm := semicircle_msc_im_pos hz0
  have hn := semicircle_norm_lt_one hz0 hm h
  have hs := semicircle_norm_sq h
  have him : (msc z).im ≤ 1 := le_trans (Complex.im_le_norm _) hn.le
  have ht0 : 0 ≤ 1 - ‖msc z‖ ^ 2 := by nlinarith [norm_nonneg (msc z)]
  have ht1 : 1 - ‖msc z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖msc z‖]
  have h1 : z.im ≤ (1 - ‖msc z‖ ^ 2) * (1 + z.im) := by
    nlinarith [mul_le_mul_of_nonneg_left him ht0]
  nlinarith [mul_nonneg (sub_nonneg.2 hz) (sub_nonneg.2 ht1)]

/-- (2.12). -/
theorem msc_add_inv {z : ℂ} (hz : 0 < z.im) : msc z + 1 / (z + msc z) = 0 := by
  rw [semicircle_inv (semicircle_msc_sq_add hz)]
  ring

theorem msc_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (msc z).im :=
  semicircle_msc_im_pos hz

/-- (3.12), in strict form. -/
theorem norm_msc_lt_one {z : ℂ} (hz : 0 < z.im) : ‖msc z‖ < 1 :=
  semicircle_norm_lt_one hz (semicircle_msc_im_pos hz) (semicircle_msc_sq_add hz)

/-- Lemma 3.1 (f): Lipschitz bound on `{Im ≥ η₀}`. -/
theorem norm_msc_sub_le {z w : ℂ} {η₀ : ℝ} (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖msc z - msc w‖ ≤ (η₀ + 1) / η₀ * ‖z - w‖ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη₀ hz
  have hw0 : 0 < w.im := lt_of_lt_of_le hη₀ hw
  have h1 := semicircle_msc_sq_add hz0
  have h2 := semicircle_msc_sq_add hw0
  have hnm := norm_msc_lt_one hz0
  have hnm' := norm_msc_lt_one hw0
  have hl1 := semicircle_lower hη₀ hz
  have hl2 := semicircle_lower hη₀ hw
  set m := msc z with hm
  set m' := msc w with hm'
  have hid : (m - m') * (1 - m * m') = (z - w) * (m * m') := by
    linear_combination (-m') * h1 + m * h2
  have a1 : 1 - ‖m‖ * ‖m'‖ ≤ ‖1 - m * m'‖ := by
    have := norm_sub_norm_le (1 : ℂ) (m * m')
    rwa [norm_one, norm_mul] at this
  have hη1 : 0 ≤ η₀ + 1 := by linarith
  have hD : η₀ ≤ ‖1 - m * m'‖ * (η₀ + 1) := by
    have a2 : η₀ ≤ (1 - ‖m‖ * ‖m'‖) * (η₀ + 1) := by
      nlinarith [mul_nonneg (sq_nonneg (‖m‖ - ‖m'‖)) hη1]
    exact le_trans a2 (mul_le_mul_of_nonneg_right a1 hη1)
  have hmm : ‖m‖ * ‖m'‖ ≤ 1 := by
    nlinarith [norm_nonneg m, norm_nonneg m']
  have hnorm : ‖m - m'‖ * ‖1 - m * m'‖ ≤ ‖z - w‖ := by
    have := congrArg norm hid
    rw [norm_mul, norm_mul, norm_mul] at this
    rw [this]
    calc ‖z - w‖ * (‖m‖ * ‖m'‖) ≤ ‖z - w‖ * 1 :=
          mul_le_mul_of_nonneg_left hmm (norm_nonneg _)
      _ = ‖z - w‖ := mul_one _
  rw [div_mul_eq_mul_div, le_div_iff₀ hη₀]
  calc ‖m - m'‖ * η₀ ≤ ‖m - m'‖ * (‖1 - m * m'‖ * (η₀ + 1)) :=
        mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = (‖m - m'‖ * ‖1 - m * m'‖) * (η₀ + 1) := by ring
    _ ≤ ‖z - w‖ * (η₀ + 1) := mul_le_mul_of_nonneg_right hnorm hη1
    _ = (η₀ + 1) * ‖z - w‖ := by ring

/-- Lemma 3.1 (a). -/
theorem msc_sq_add {z : ℂ} (hz : 0 < z.im) : msc z ^ 2 + z * msc z + 1 = 0 :=
  semicircle_msc_sq_add hz

/-- Lemma 3.1 (b). -/
theorem msc_im_mul {z : ℂ} (hz : 0 < z.im) :
    (msc z).im * (‖z + msc z‖ ^ 2 - 1) = z.im ∧
      ‖msc z‖ ^ 2 = (msc z).im / ((msc z).im + z.im) ∧
      1 - ‖msc z‖ ^ 2 = z.im / ((msc z).im + z.im) := by
  have h := semicircle_msc_sq_add hz
  have hm := semicircle_msc_im_pos hz
  have hs := semicircle_norm_sq h
  have hpos : 0 < (msc z).im + z.im := by linarith
  refine ⟨semicircle_im_mul h, ?_, ?_⟩
  · rw [eq_div_iff hpos.ne']
    exact hs
  · rw [eq_div_iff hpos.ne']
    linarith

/-- Lemma 3.1 (c). -/
theorem msc_bounds {z : ℂ} (hz : 0 < z.im) :
    1 / (‖z‖ + 1) ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ 1 ∧ z.im / (‖z‖ + 1) ^ 2 ≤ (msc z).im := by
  have h := semicircle_msc_sq_add hz
  have hm := semicircle_msc_im_pos hz
  have hn := semicircle_norm_lt_one hz hm h
  have h1 := semicircle_norm_mul h
  have hI := semicircle_im_mul h
  have hs : ‖z + msc z‖ ≤ ‖z‖ + 1 := by
    calc ‖z + msc z‖ ≤ ‖z‖ + ‖msc z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by linarith
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  refine ⟨?_, hn.le, ?_⟩
  · rw [div_le_iff₀ hz1]
    nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg (msc z))]
  · rw [div_le_iff₀ (by positivity)]
    have hs0 : 0 ≤ ‖z + msc z‖ := norm_nonneg _
    have hs2 : ‖z + msc z‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs2 hm.le]

end Rigidity
