module

public import Rigidity.Edge.EntryDet
public import Rigidity.Edge.Resolvent
public import Rigidity.Edge.SmoothCount

@[expose] public section

/-!
# The functional `X` for a minor

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `Q`, `Im z > 0` and an index `a`, let `Q^{(a)}` be the minor with row and
column `a` removed.  Lemma 3.6 (I6) gives `det (Q - z) G_aa = det (Q^{(a)} - z)`, and (I2) gives the
off-diagonal resolvent entries `G_cd = -G_cc ∑_{j ≠ c} Q_cj G^{(c)}_jd` through the minor.  With
the logarithm formula of Lemma 11.9 (ii), this yields the exact formula of Corollary 11.11 (ii),
`X(Q) - X(Q^{(a)}) = π⁻¹ Im [Log (-G_aa)]`, and the bound `2/π (|G_aa(z₁) + 1| + |G_aa(z₂) + 1|)`
when both endpoint values are within `1/2` of `-1`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section MinorC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A sum over `n` splits into the term at `c` and the sum over the minor index set. -/
private lemma minor_sum_split (f : n → ℂ) (c : n) :
    ∑ k, f k = f c + ∑ j : {i // i ∉ ({c} : Finset n)}, f j := by
  rw [← (Equiv.sumCompl (fun i => i ∈ ({c} : Finset n))).sum_comp, Fintype.sum_sum_type]
  simp

/-- Lemma 3.6 (I6): `det(Q - z) G_aa = det(Q^{(a)} - z)`. -/
theorem det_sub_mul_resolventMat {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (a : n) :
    (Q - z • (1 : Matrix n n ℂ)).det * resolventMat Q z a a =
      (Q.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n) Subtype.val -
        z • (1 : Matrix {i // i ∉ ({a} : Finset n)} {i // i ∉ ({a} : Finset n)} ℂ)).det := by
  set A : Matrix n n ℂ := Q - z • (1 : Matrix n n ℂ) with hA
  have hdet : A.det ≠ 0 := det_sub_smul_ne_zero hQ hz.ne'
  have h1 : A.det * resolventMat Q z a a = A.adjugate a a := by
    have : resolventMat Q z = (A.det)⁻¹ • A.adjugate := by
      unfold resolventMat
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hdet, one_mul]
  rw [h1, Matrix.adjugate_apply]
  let e := Equiv.sumCompl (fun i => i ∈ ({a} : Finset n))
  rw [← Matrix.det_submatrix_equiv_self e (A.updateRow a (Pi.single a 1))]
  have hS : A.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n) Subtype.val =
      Q.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n) Subtype.val -
        z • (1 : Matrix {i // i ∉ ({a} : Finset n)} {i // i ∉ ({a} : Finset n)} ℂ) := by
    ext i j
    simp [hA, Matrix.one_apply, Subtype.ext_iff]
  have hblock : (A.updateRow a (Pi.single a 1)).submatrix e e =
      Matrix.fromBlocks 1 0 (A.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n)
        (Subtype.val : {i // i ∈ ({a} : Finset n)} → n))
        (A.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n) Subtype.val) := by
    ext (i | i) (j | j)
    · have hi : (i : n) = a := Finset.mem_singleton.mp i.2
      have hj : (j : n) = a := Finset.mem_singleton.mp j.2
      have hij : i = j := Subtype.ext (hi.trans hj.symm)
      simp only [e, Equiv.sumCompl_apply_inl, Matrix.submatrix_apply, hj,
        Matrix.updateRow_self, Pi.single_eq_same, hij, Matrix.fromBlocks_apply₁₁,
        Matrix.one_apply_eq]
    · have hi : (i : n) = a := Finset.mem_singleton.mp i.2
      have hj : (j : n) ≠ a := fun h => j.2 (Finset.mem_singleton.mpr h)
      simp only [e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Matrix.submatrix_apply,
        hi, Matrix.updateRow_self, Pi.single_eq_of_ne hj, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
    · have hi : (i : n) ≠ a := fun h => i.2 (Finset.mem_singleton.mpr h)
      simp only [e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, Matrix.submatrix_apply,
        Matrix.updateRow_ne hi, Matrix.fromBlocks_apply₂₁]
    · have hi : (i : n) ≠ a := fun h => i.2 (Finset.mem_singleton.mpr h)
      simp only [e, Equiv.sumCompl_apply_inr, Matrix.submatrix_apply,
        Matrix.updateRow_ne hi, Matrix.fromBlocks_apply₂₂]
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, hS]

/-- Lemma 3.6 (I2): `G_cd = -G_cc ∑_{j ≠ c} Q_cj G^{(c)}_jd` for `c ≠ d`. -/
theorem resolventMat_offDiag {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    {c d : n} (hcd : c ≠ d) :
    resolventMat Q z c d = -resolventMat Q z c c *
      ∑ j : {i // i ∉ ({c} : Finset n)}, Q c j *
        resolventMat (Q.submatrix (Subtype.val : {i // i ∉ ({c} : Finset n)} → n) Subtype.val) z
          j ⟨d, by simpa using hcd.symm⟩ := by
  set A : Matrix n n ℂ := Q - z • (1 : Matrix n n ℂ) with hA
  set Qc : Matrix _ _ ℂ := Q.submatrix (Subtype.val : {i // i ∉ ({c} : Finset n)} → n)
    Subtype.val with hQc
  set S : Matrix {i // i ∉ ({c} : Finset n)} {i // i ∉ ({c} : Finset n)} ℂ :=
    Qc - z • (1 : Matrix {i // i ∉ ({c} : Finset n)} {i // i ∉ ({c} : Finset n)} ℂ) with hS
  have hQcH : Qc.IsHermitian := hQ.submatrix _
  have hGA : resolventMat Q z * A = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hQ hz.ne'))
  have hSinv : S * resolventMat Qc z = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hQcH hz.ne'))
  have hAS : ∀ i j : {i // i ∉ ({c} : Finset n)}, A i.val j.val = S i j := by
    intro i j
    simp [hA, hS, hQc, Matrix.one_apply, Subtype.ext_iff]
  have hAc : ∀ j : {i // i ∉ ({c} : Finset n)}, A c j.val = Q c j.val := by
    intro j
    have hj : c ≠ (j : n) := fun h => j.2 (Finset.mem_singleton.mpr h.symm)
    simp [hA, hj]
  have hrow : Matrix.vecMul (fun j : {i // i ∉ ({c} : Finset n)} => resolventMat Q z c j.val) S =
      -resolventMat Q z c c • fun j : {i // i ∉ ({c} : Finset n)} => Q c j.val := by
    ext d'
    have h := congrFun (congrFun hGA c) d'.val
    have hne : c ≠ d'.val := fun h => d'.2 (Finset.mem_singleton.mpr h.symm)
    rw [Matrix.mul_apply, minor_sum_split (fun k => resolventMat Q z c k * A k d'.val) c,
      Matrix.one_apply_ne hne] at h
    simp only [hAS, hAc] at h
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
    linear_combination h
  have h2 : (fun j : {i // i ∉ ({c} : Finset n)} => resolventMat Q z c j.val) =
      Matrix.vecMul (-resolventMat Q z c c • fun j : {i // i ∉ ({c} : Finset n)} => Q c j.val)
        (resolventMat Qc z) := by
    rw [← hrow, Matrix.vecMul_vecMul, hSinv, Matrix.vecMul_one]
  have h3 := congrFun h2 ⟨d, by simpa using hcd.symm⟩
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h3
  refine h3.trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Corollary 11.11 (ii), bound. -/
theorem abs_smoothCount_sub_minor_le {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {E₁ E₂ η : ℝ}
    (hη : 0 < η) (hE : E₁ ≤ E₂) (a : n) (h₁ : ‖resolventMat Q ⟨E₁, η⟩ a a + 1‖ ≤ 1 / 2)
    (h₂ : ‖resolventMat Q ⟨E₂, η⟩ a a + 1‖ ≤ 1 / 2) :
    |smoothCount E₁ E₂ η Q -
        smoothCount E₁ E₂ η (Q.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n)
          Subtype.val)| ≤
      2 / π * (‖resolventMat Q ⟨E₁, η⟩ a a + 1‖ + ‖resolventMat Q ⟨E₂, η⟩ a a + 1‖) := by
  have hn : ∀ w : ℂ, ‖-w - 1‖ = ‖w + 1‖ := fun w => by
    rw [← norm_neg]
    congr 1
    ring
  have h := abs_smoothCount_sub_le_of_log
    (hQ.submatrix (Subtype.val : {i // i ∉ ({a} : Finset n)} → n))
    hQ hη hE (fun y => -resolventMat Q ⟨y, η⟩ a a) (-1) (by norm_num)
    (fun y _ => by
      rw [neg_mul, neg_one_mul, neg_inj, mul_comm]
      exact det_sub_mul_resolventMat hQ (z := ⟨y, η⟩) hη a)
    (fun y _ => neg_resolventMat_mem_slitPlane hQ (z := ⟨y, η⟩) hη a)
    (by simpa only [hn] using h₁) (by simpa only [hn] using h₂)
  rw [abs_sub_comm]
  simpa only [hn] using h

end MinorC

end Rigidity
