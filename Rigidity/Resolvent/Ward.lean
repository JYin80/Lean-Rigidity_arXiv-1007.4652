import Rigidity.Resolvent.Basic

/-!
# Entry bounds, symmetry, the Ward identity and resolvent identities

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `H` over `ℝ` or `ℂ` (a field `𝕜` with `RCLike 𝕜`), `η = Im z > 0` and the
Green function `G(z) = (H - z)⁻¹` (2.8), this file proves items of Lemma 3.5:
* (a): the entry bound `|G_ij| ≤ η⁻¹`, positivity of `Im G_ii`, and the adjoint `G(z)* = G(z̄)`;
* (b): the Ward identity `∑_j |G_ij|² = Im G_ii / η`, in its row and column forms.

The norm on matrices is the `ℓ²` operator norm.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `(i, j)` entry of a complex matrix is bounded by its `ℓ²` operator norm. -/
private theorem ward_norm_apply_le_l2_opNorm (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ n)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M *ᵥ (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ n))) i
  simpa [Matrix.mulVec_single_one] using this

/-- The resolvent identity `G(z) - G(w) = (z - w) G(z) G(w)` for `Im z ≠ 0` and `Im w ≠ 0`. -/
private theorem ward_green_sub_green {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    green A z - green A w = (z - w) • (green A z * green A w) := by
  have hB := isHermitian_map_toC hA
  have h1 : green A z * (A.map toC - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hB hz))
  have h2 := green_mul hA hw
  have h3 : green A z *
      ((A.map toC - w • (1 : Matrix n n ℂ)) - (A.map toC - z • (1 : Matrix n n ℂ))) *
        green A w = (z - w) • (green A z * green A w) := by
    have : (A.map toC - w • (1 : Matrix n n ℂ)) - (A.map toC - z • (1 : Matrix n n ℂ)) =
        (z - w) • (1 : Matrix n n ℂ) := by
      rw [sub_smul]; abel
    rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [← h3, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul,
    Matrix.mul_assoc _ (A.map toC - w • (1 : Matrix n n ℂ)), h2, Matrix.mul_one]

/-- The resolvent identity with the factors in the other order. -/
private theorem ward_green_sub_green' {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    green A z - green A w = (z - w) • (green A w * green A z) := by
  have h := ward_green_sub_green hA hw hz
  rw [← neg_sub (green A w) (green A z), h, ← neg_smul, neg_sub]

/-- Lemma 3.5 (a): `‖G_ij‖ ≤ η⁻¹`. -/
theorem norm_green_apply_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (i j : n) : ‖green A z i j‖ ≤ 1 / z.im := by
  exact (ward_norm_apply_le_l2_opNorm _ i j).trans (norm_green_le hA hz)

/-- Lemma 3.5 (a): `Im G_ii > 0`. -/
theorem green_im_diag_pos {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (i : n) : 0 < (green A z i i).im := by
  exact im_resolventMat_diag_pos (isHermitian_map_toC hA) hz i

/-- Lemma 3.5 (a): `G(z)* = G(z̄)`. -/
theorem green_conjTranspose {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    (green A z)ᴴ = green A (starRingEnd ℂ z) := by
  have _ := hz
  have hB : (A.map toC)ᴴ = A.map toC := isHermitian_map_toC hA
  unfold green
  rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hB]
  rfl

/-- Lemma 3.5 (b): the Ward identity. -/
theorem ward {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : n) :
    ∑ j, ‖green A z i j‖ ^ 2 = (green A z i i).im / z.im ∧
      ∑ j, ‖green A z j i‖ ^ 2 = (green A z i i).im / z.im := by
  have hc := green_conjTranspose hA hz
  have hzc : (starRingEnd ℂ z).im ≠ 0 := by simpa using hz.ne'
  have key : ∀ S : ℝ, (green A z i i - green A (starRingEnd ℂ z) i i =
      (z - starRingEnd ℂ z) * (S : ℂ)) → S = (green A z i i).im / z.im := by
    intro S h
    have e1 : green A z i i - green A (starRingEnd ℂ z) i i =
        ((2 * (green A z i i).im : ℝ) : ℂ) * Complex.I := by
      rw [← hc, Matrix.conjTranspose_apply]
      exact Complex.sub_conj _
    rw [e1, Complex.sub_conj] at h
    have := congrArg Complex.im h
    simp at this
    field_simp
    linarith
  constructor
  · apply key
    have h1 := congrFun (congrFun (ward_green_sub_green hA hz.ne' hzc) i) i
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul] at h1
    rw [h1, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc, Matrix.conjTranspose_apply]
    simpa using Complex.mul_conj' (green A z i j)
  · apply key
    have h1 := congrFun (congrFun (ward_green_sub_green' hA hz.ne' hzc) i) i
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul] at h1
    rw [h1, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc, Matrix.conjTranspose_apply]
    simpa [mul_comm] using Complex.mul_conj' (green A z j i)

end Resolvent

end Rigidity
