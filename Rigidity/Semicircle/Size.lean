module

public import Rigidity.Semicircle.Algebra

@[expose] public section

/-!
# Size of the Stieltjes transform of the semicircle law

Numbers in this file refer to the blueprint NP v1.1 (the original paper, Erdős–Yau–Yin,
arXiv:1007.4652, is cited as [EYY, …] where it has a counterpart).

For `z = E + iη` with `|E| ≤ 5` and `0 < η ≤ 10`, put `κ = ||E| - 2|` and `ϰ = √(κ + η)`
(Convention 1.3).  This file proves Lemma 3.2: `1/13 ≤ |m_sc| ≤ 1` and
`|1 - m_sc²| ≍ ϰ` (3.3); `Im m_sc ≍ ϰ` if `|E| ≤ 2` or `κ ≤ η`, and `Im m_sc ≍ η/ϰ` if
`|E| > 2` and `η ≤ κ` (3.4), with the constants `c_* = 1/150` and `C_* = 4`; and the chain
`c_* η ≤ Im m_sc ≤ ϰ ≤ c_*⁻¹ |1 - m_sc²|`.

The proofs follow Lemma 3.1 (d), (e): with `y = Im m_sc`, `R = |z - 2| |z + 2|` and
`S = |z|² - 4`, one has `R² = S² + 16 η²` and `R - S = 8 y (y + η)`.  Every estimate is derived
from two-sided bounds on `P = R - S` in the three regimes, by monotonicity of `y ↦ y (y + η)`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `κ = ||E| - 2|` (Convention 1.3). -/
noncomputable def kappaE (E : ℝ) : ℝ := |(|E| - 2)|

/-- `ϰ = √(κ + η)` (Convention 1.3). -/
noncomputable def varkappa (z : ℂ) : ℝ := Real.sqrt (kappaE z.re + z.im)

/-- The real data of Lemma 3.1 (d), (e) for `z` in the upper half plane, with `a = |Re z|`:
`y = Im m_sc > 0`, `R = |z - 2| |z + 2| ≥ 0`, `R² = S² + 16 η²` and `R - S = 8 y (y + η)` for
`S = a² + η² - 4`. -/
private lemma size_data {z : ℂ} (hz : 0 < z.im) :
    0 < (msc z).im ∧ 0 ≤ ‖z - 2‖ * ‖z + 2‖ ∧
      (‖z - 2‖ * ‖z + 2‖) ^ 2 = (|z.re| ^ 2 + z.im ^ 2 - 4) ^ 2 + 16 * z.im ^ 2 ∧
      ‖z - 2‖ * ‖z + 2‖ - (|z.re| ^ 2 + z.im ^ 2 - 4) =
        8 * (msc z).im * ((msc z).im + z.im) := by
  obtain ⟨hw, -, hPQ, -, -⟩ := msc_im_eq_P hz
  have hm := msc_im_pos hz
  have hN : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hwdef : Complex.sqrt (z - 2) * Complex.sqrt (z + 2) = 2 * msc z + z := by
    unfold msc; ring
  have hwim : (Complex.sqrt (z - 2) * Complex.sqrt (z + 2)).im = 2 * (msc z).im + z.im := by
    rw [hwdef]; simp
  rw [hwim, hN] at hw
  rw [hN] at hPQ
  rw [sq_abs]
  refine ⟨hm, by positivity, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- A real number whose square is at most `c²` is at most `c`, for `c ≥ 0`. -/
private lemma size_le_of_sq {v c : ℝ} (hc : 0 ≤ c) (h : v ^ 2 ≤ c ^ 2) : v ≤ c :=
  le_trans (le_abs_self v) (abs_le_of_sq_le_sq h hc)

/-- Elementary consequences of `R ≥ 0` and `R² = S² + 16 η²` (as in the proof of Lemma 3.2):
`|S| ≤ R`, `4 η ≤ R` and `R ≤ |S| + 4 η`. -/
private lemma size_R_basic {S η R : ℝ} (hη : 0 < η) (hR0 : 0 ≤ R)
    (hR2 : R ^ 2 = S ^ 2 + 16 * η ^ 2) :
    S ≤ R ∧ -S ≤ R ∧ 4 * η ≤ R ∧ (0 ≤ S → R ≤ S + 4 * η) ∧ (S ≤ 0 → R ≤ -S + 4 * η) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra h
    replace h := not_le.mp h
    nlinarith [mul_pos (sub_pos.2 h) (show 0 < S + R by linarith)]
  · by_contra h
    replace h := not_le.mp h
    nlinarith [mul_pos (sub_pos.2 h) (show 0 < -S + R by linarith)]
  · by_contra h
    replace h := not_le.mp h
    nlinarith [mul_pos (sub_pos.2 h) (show 0 < 4 * η + R by linarith)]
  · intro hS
    by_contra h
    replace h := not_le.mp h
    nlinarith [mul_pos (sub_pos.2 h) (show 0 < R + (S + 4 * η) by linarith)]
  · intro hS
    by_contra h
    replace h := not_le.mp h
    nlinarith [mul_pos (sub_pos.2 h) (show 0 < R + (-S + 4 * η) by linarith)]

/-- Upper bound `P = R - S ≤ 8 ϰ²` for `0 ≤ a` and `0 < η`, in all three regimes. -/
private lemma size_P_le {a η R S : ℝ} (ha0 : 0 ≤ a) (hη : 0 < η)
    (hS : S = a ^ 2 + η ^ 2 - 4) (hR0 : 0 ≤ R) (hR2 : R ^ 2 = S ^ 2 + 16 * η ^ 2) :
    R - S ≤ 8 * (|a - 2| + η) := by
  obtain ⟨-, -, -, h4, h5⟩ := size_R_basic hη hR0 hR2
  rcases le_or_gt a 2 with h2 | h2
  · rw [abs_of_nonpos (by linarith)]
    rcases le_total 0 S with hS0 | hS0
    · have := h4 hS0
      nlinarith
    · have := h5 hS0
      nlinarith
  · rw [abs_of_pos (by linarith)]
    have hS0 : 0 ≤ S := by rw [hS]; nlinarith
    have := h4 hS0
    nlinarith

/-- Two-sided bound `ϰ² ≤ 2 R` and `R ≤ 14 ϰ²` (for `a = |Re z| ≤ 5`, `0 < η ≤ 10`). -/
private lemma size_R_range {a η R S : ℝ} (ha0 : 0 ≤ a) (ha5 : a ≤ 5) (hη : 0 < η)
    (hη10 : η ≤ 10) (hS : S = a ^ 2 + η ^ 2 - 4) (hR0 : 0 ≤ R)
    (hR2 : R ^ 2 = S ^ 2 + 16 * η ^ 2) :
    |a - 2| + η ≤ 2 * R ∧ R ≤ 14 * (|a - 2| + η) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := size_R_basic hη hR0 hR2
  have hη2 : η ^ 2 ≤ 10 * η := by nlinarith
  rcases le_or_gt a 2 with ha2 | ha2
  · rw [abs_of_nonpos (by linarith)]
    have hκ : 2 * (2 - a) ≤ 4 - a ^ 2 := by nlinarith
    have hκ' : 4 - a ^ 2 ≤ 4 * (2 - a) := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    rcases le_total 0 S with hS0 | hS0
    · have := h4 hS0
      nlinarith
    · have := h5 hS0
      nlinarith
  · rw [abs_of_pos (by linarith)]
    have hS0 : 0 ≤ S := by rw [hS]; nlinarith
    have := h4 hS0
    have hκ : 4 * (a - 2) ≤ a ^ 2 - 4 := by nlinarith
    have hκ' : a ^ 2 - 4 ≤ 7 * (a - 2) := by nlinarith
    refine ⟨by nlinarith, by nlinarith⟩

/-- Case A of Lemma 3.2 (`E > 2`, `η ≤ κ`): `ϰ⁻¹ η / 150 ≤ y ≤ 4 η ϰ⁻¹`. -/
private lemma size_caseA {a η R S y v : ℝ} (ha2 : 2 < a) (ha5 : a ≤ 5) (hη : 0 < η)
    (hηκ : η ≤ a - 2) (hS : S = a ^ 2 + η ^ 2 - 4) (hR0 : 0 ≤ R)
    (hR2 : R ^ 2 = S ^ 2 + 16 * η ^ 2) (hy : 0 < y) (hP : R - S = 8 * y * (y + η))
    (hv : 0 < v) (hv2 : v ^ 2 = a - 2 + η) :
    1 / 150 * (η / v) ≤ y ∧ y ≤ 4 * (η / v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := size_R_basic hη hR0 hR2
  have hS0 : 0 ≤ S := by rw [hS]; nlinarith
  have hRS := h4 hS0
  have hS4 : 4 * (a - 2) ≤ S := by rw [hS]; nlinarith [sq_nonneg (a - 2), sq_nonneg η]
  have hS10 : S ≤ 10 * (a - 2) := by
    rw [hS]
    nlinarith [mul_nonneg (sub_nonneg.2 ha2.le) (sub_nonneg.2 ha5),
      mul_le_mul_of_nonneg_left hηκ hη.le]
  have hPpos : 0 < R - S := by rw [hP]; positivity
  have hPQ : (R - S) * (R + S) = 16 * η ^ 2 := by linear_combination hR2
  have hQlo : 8 * (a - 2) ≤ R + S := by linarith
  have hQhi : R + S ≤ 24 * (a - 2) := by linarith
  have hPκ1 : (R - S) * (a - 2) ≤ 2 * η ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hQlo hPpos.le]
  have hPκ2 : 2 * η ^ 2 ≤ 3 * (a - 2) * (R - S) := by
    nlinarith [mul_le_mul_of_nonneg_left hQhi hPpos.le]
  obtain ⟨t, ht⟩ : ∃ t, t = η / v := ⟨_, rfl⟩
  rw [← ht]
  have ht0 : 0 < t := by rw [ht]; positivity
  have htv : η = t * v := by rw [ht]; field_simp
  have hv3 : v ≤ 3 := size_le_of_sq (by norm_num) (by linarith)
  have hP1 : R - S ≤ 4 * t ^ 2 := by
    have : (R - S) * v ^ 2 ≤ 4 * t ^ 2 * v ^ 2 := by
      have e : 4 * t ^ 2 * v ^ 2 = 4 * η ^ 2 := by rw [htv]; ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left (show v ^ 2 ≤ 2 * (a - 2) by linarith) hPpos.le]
    exact le_of_mul_le_mul_right this (by positivity)
  have hP2 : 2 / 3 * t ^ 2 ≤ R - S := by
    have : 2 / 3 * t ^ 2 * v ^ 2 ≤ (R - S) * v ^ 2 := by
      have e : 2 / 3 * t ^ 2 * v ^ 2 = 2 / 3 * η ^ 2 := by rw [htv]; ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left (show a - 2 ≤ v ^ 2 by linarith) hPpos.le]
    exact le_of_mul_le_mul_right this (by positivity)
  constructor
  · by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : y * (y + η) < (t / 150) * (t / 150 + η) :=
      mul_lt_mul'' (show y < t / 150 by linarith) (by linarith) hy.le (by linarith)
    have h2 : (t / 150) * (t / 150 + η) = t ^ 2 * (1 / 22500 + v / 150) := by
      rw [htv]; ring
    have h3 : t ^ 2 * (1 / 22500 + v / 150) ≤ t ^ 2 * (1 / 22500 + 3 / 150) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
    nlinarith [sq_nonneg t]
  · by_contra hgt
    replace hgt := not_le.mp hgt
    have h1 : 4 * t * (4 * t + η) < y * (y + η) :=
      mul_lt_mul'' hgt (by linarith) (by positivity) (by positivity)
    nlinarith [mul_pos ht0 hη, sq_nonneg t]

/-- `ϰ > 0` and `ϰ² = κ + η` for `η > 0`. -/
private lemma size_varkappa_sq {z : ℂ} (hη : 0 < z.im) :
    0 < varkappa z ∧ varkappa z ^ 2 = |(|z.re| - 2)| + z.im := by
  have h : 0 < kappaE z.re + z.im := by
    unfold kappaE; positivity
  refine ⟨Real.sqrt_pos.2 h, ?_⟩
  unfold varkappa
  rw [Real.sq_sqrt h.le]
  rfl

/-- `‖z‖ ≤ 56 / 5` for `|Re z| ≤ 5` and `0 < Im z ≤ 10` (so that `‖z‖² ≤ 125 < (56 / 5)²`). -/
private lemma size_norm_le {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη' : z.im ≤ 10) :
    ‖z‖ ≤ 56 / 5 := by
  apply size_le_of_sq (by norm_num)
  have hN : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : z.re ^ 2 ≤ 25 := by
    have := sq_abs z.re
    nlinarith [abs_nonneg z.re]
  nlinarith

/-- Lemma 3.2, (3.3): size of `m_sc` and `1 - m_sc²`. -/
theorem msc_size {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη' : z.im ≤ 10) :
    1 / 13 ≤ ‖msc z‖ ∧ ‖msc z‖ ≤ 1 ∧ 1 / 150 * varkappa z ≤ ‖1 - msc z ^ 2‖ ∧
      ‖1 - msc z ^ 2‖ ≤ 4 * varkappa z := by
  obtain ⟨hy, hR0, hR2, hP⟩ := size_data hη
  obtain ⟨hv, hv2⟩ := size_varkappa_sq hη
  have hb := msc_bounds hη
  have hzn := size_norm_le hE hη hη'
  have hm1 : 1 / 13 ≤ ‖msc z‖ := by
    refine le_trans ?_ hb.1
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨hR1, hR14⟩ := size_R_range (abs_nonneg z.re) hE hη hη' rfl hR0 hR2
  have hnorm : ‖1 - msc z ^ 2‖ = ‖msc z‖ * Real.sqrt (‖z - 2‖ * ‖z + 2‖) := by
    rw [(one_sub_msc_sq hη).2, mul_assoc, ← Real.sqrt_mul (norm_nonneg _)]
  have hr0 : 0 ≤ Real.sqrt (‖z - 2‖ * ‖z + 2‖) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (‖z - 2‖ * ‖z + 2‖) ^ 2 = ‖z - 2‖ * ‖z + 2‖ := Real.sq_sqrt hR0
  set r := Real.sqrt (‖z - 2‖ * ‖z + 2‖) with hr
  have hrv : r ≤ 4 * varkappa z := size_le_of_sq (by positivity) (by nlinarith)
  have hvr : varkappa z ≤ 2 * r := size_le_of_sq (by positivity) (by nlinarith)
  refine ⟨hm1, hb.2.1, ?_, ?_⟩
  · rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_right hm1 hr0]
  · rw [hnorm]
    nlinarith [mul_le_mul_of_nonneg_right hb.2.1 hr0]

/-- Lemma 3.2, (3.4), second case. -/
theorem msc_im_size_edge {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη' : z.im ≤ 10)
    (h₁ : 2 < |z.re|) (h₂ : z.im ≤ kappaE z.re) :
    1 / 150 * (z.im / varkappa z) ≤ (msc z).im ∧ (msc z).im ≤ 4 * (z.im / varkappa z) := by
  obtain ⟨hy, hR0, hR2, hP⟩ := size_data hη
  obtain ⟨hv, hv2⟩ := size_varkappa_sq hη
  unfold kappaE at h₂
  rw [abs_of_pos (by linarith : 0 < |z.re| - 2)] at h₂ hv2
  exact size_caseA h₁ hE hη h₂ rfl hR0 hR2 hy hP hv (by linarith)

/-- Lemma 3.2, the "in particular" chain. -/
theorem msc_im_chain {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη' : z.im ≤ 10) :
    1 / 150 * z.im ≤ (msc z).im ∧ (msc z).im ≤ varkappa z ∧
      varkappa z ≤ 150 * ‖1 - msc z ^ 2‖ := by
  obtain ⟨hy, hR0, hR2, hP⟩ := size_data hη
  obtain ⟨hv, hv2⟩ := size_varkappa_sq hη
  have hzn := size_norm_le hE hη hη'
  refine ⟨?_, ?_, ?_⟩
  · have h := (msc_bounds hη).2.2
    refine le_trans ?_ h
    have h150 : (‖z‖ + 1) ^ 2 ≤ 150 := by nlinarith [norm_nonneg z]
    calc 1 / 150 * z.im = z.im / 150 := by ring
      _ ≤ z.im / (‖z‖ + 1) ^ 2 := div_le_div_of_nonneg_left hη.le (by positivity) h150
  · have h := size_P_le (abs_nonneg z.re) hη (a := |z.re|) rfl hR0 hR2
    apply size_le_of_sq hv.le
    nlinarith [sq_nonneg (msc z).im, mul_pos hy hη]
  · have h := (msc_size hE hη hη').2.2.1
    linarith

end Rigidity
