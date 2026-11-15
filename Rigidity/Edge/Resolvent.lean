import Mathlib

/-!
# The complex resolvent of a hermitian matrix

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a complex square matrix `A` and `z : ℂ`, `resolventMat A z = (A - z)⁻¹`.  For hermitian `A`
and `Im z ≠ 0` the matrix `A - z` is invertible, the resolvent identity of Lemma 3.5 (h) holds,
`Im G_aa > 0` on the upper half plane, and the `ℓ²` operator norm satisfies
`‖G_A(z)‖ ≤ (Im z)⁻¹` (Lemma 3.5 (a)).  All proofs go through the quadratic form
`x ↦ x* (A - z) x`, whose imaginary part is `-Im z · ‖x‖²`.
-/

open Real

namespace Rigidity

/-- The resolvent `(A - z)⁻¹` of a complex square matrix. -/
noncomputable def resolventMat {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (z : ℂ) : Matrix n n ℂ :=
  (A - z • (1 : Matrix n n ℂ))⁻¹

section ResolventC
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped ComplexOrder in
omit [DecidableEq n] in
/-- A nonzero vector has positive squared norm. -/
private lemma resolvent_re_self_pos {x : n → ℂ} (hx : x ≠ 0) : 0 < (star x ⬝ᵥ x).re :=
  (Complex.pos_iff.mp (Matrix.dotProduct_star_self_pos_iff.mpr hx)).1

open scoped Matrix in
/-- The imaginary part of the quadratic form of `A - z`, for hermitian `A`. -/
private lemma resolvent_im_form {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) (x : n → ℂ) :
    (star x ⬝ᵥ (A - z • (1 : Matrix n n ℂ)) *ᵥ x).im = -z.im * (star x ⬝ᵥ x).re := by
  have h1 : (star x ⬝ᵥ A *ᵥ x).im = 0 := hA.im_star_dotProduct_mulVec_self x
  have h2 : (star x ⬝ᵥ x).im = 0 := by
    simpa using (Matrix.isHermitian_one (n := n) (α := ℂ)).im_star_dotProduct_mulVec_self x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    Complex.sub_im, h1, smul_eq_mul, Complex.mul_im, h2]
  ring

theorem det_sub_smul_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (A - z • (1 : Matrix n n ℂ)).det ≠ 0 := by
  intro h
  obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 := resolvent_im_form hA z x
  rw [hMx] at h1
  have h2 := resolvent_re_self_pos hx
  simp only [dotProduct_zero, Complex.zero_im] at h1
  have h3 : z.im * (star x ⬝ᵥ x).re = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact hz h4
  · exact h2.ne' h4

private lemma resolvent_isUnit_det {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (A - z • (1 : Matrix n n ℂ)).det :=
  isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hA hz)

private lemma resolvent_mul_self {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : resolventMat A z * (A - z • (1 : Matrix n n ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _ (resolvent_isUnit_det hA hz)

private lemma resolvent_self_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : (A - z • (1 : Matrix n n ℂ)) * resolventMat A z = 1 :=
  Matrix.mul_nonsing_inv _ (resolvent_isUnit_det hA hz)

/-- Lemma 3.5 (h): `G_A - G_B = G_A (B - A) G_B`. -/
theorem resolventMat_sub_resolventMat {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    resolventMat A z - resolventMat B z = resolventMat A z * (B - A) * resolventMat B z := by
  have hBA : B - A = (B - z • (1 : Matrix n n ℂ)) - (A - z • (1 : Matrix n n ℂ)) := by abel
  have h1 := resolvent_self_mul hB hz
  have h2 := resolvent_mul_self hA hz
  rw [hBA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc _ (B - z • (1 : Matrix n n ℂ)),
    h1, Matrix.mul_one, h2, Matrix.one_mul]

open scoped Matrix in
/-- For hermitian `A`, `Im z > 0` and `w ≠ 0`, the quadratic form `w* G_A(z) w` has positive
imaginary part. -/
lemma Resolvent.im_form_pos {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {w : n → ℂ} (hw : w ≠ 0) :
    0 < (star w ⬝ᵥ resolventMat A z *ᵥ w).im := by
  set u : n → ℂ := resolventMat A z *ᵥ w with hu
  have huw : (A - z • (1 : Matrix n n ℂ)) *ᵥ u = w := by
    rw [hu, Matrix.mulVec_mulVec, resolvent_self_mul hA hz.ne', Matrix.one_mulVec]
  have hu0 : u ≠ 0 := by
    intro h0
    apply hw
    rw [← huw, h0, Matrix.mulVec_zero]
  have h1 := resolvent_im_form hA z u
  rw [huw] at h1
  have h2 := resolvent_re_self_pos hu0
  have h3 : star w ⬝ᵥ u = star (star u ⬝ᵥ w) := Matrix.star_dotProduct _ _
  rw [h3, Complex.star_def, Complex.conj_im, h1]
  nlinarith

/-- `Im G_aa > 0` on `ℂ₊`. -/
theorem im_resolventMat_diag_pos {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (a : n) : 0 < (resolventMat A z a a).im := by
  have h := Resolvent.im_form_pos hA hz (w := Pi.single a 1) (by simp)
  simpa [Matrix.mulVec_single_one] using h

open scoped Matrix.Norms.L2Operator in
/-- Lemma 3.5 (a): `‖G_A(z)‖ ≤ (Im z)⁻¹`. -/
theorem norm_resolventMat_le {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    ‖resolventMat A z‖ ≤ 1 / z.im := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro y
  set x : EuclideanSpace ℂ n := Matrix.toEuclideanLin (resolventMat A z) y with hx
  have hxo : x.ofLp = Matrix.mulVec (resolventMat A z) y.ofLp := by simp [hx]
  have hyx : Matrix.mulVec (A - z • (1 : Matrix n n ℂ)) x.ofLp = y.ofLp := by
    rw [hxo, Matrix.mulVec_mulVec, resolvent_self_mul hA hz.ne', Matrix.one_mulVec]
  have h1 := resolvent_im_form hA z x.ofLp
  rw [hyx] at h1
  have hS : star x.ofLp ⬝ᵥ x.ofLp = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    rw [h]; push_cast; rfl
  have hin : star x.ofLp ⬝ᵥ y.ofLp = inner ℂ x y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hin, hS, Complex.ofReal_re] at h1
  have h2 : |(inner ℂ x y).im| ≤ ‖x‖ * ‖y‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm x y)
  rw [h1, abs_mul, abs_neg, abs_of_pos hz, abs_of_nonneg (by positivity)] at h2
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  have h3 : z.im * ‖x‖ ≤ ‖y‖ := by
    rcases hx0.eq_or_lt with h | h
    · rw [← h]; simp
    · nlinarith
  change ‖x‖ ≤ 1 / z.im * ‖y‖
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hz]
  linarith

end ResolventC

end Rigidity
