module

public import Rigidity.Ensemble.Basic
public import Rigidity.MainDefs

@[expose] public section

/-!
# Ordered eigenvalues, the operator norm, Weyl's inequality, reflection

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `A`, `eigAsc hA k` is the `(k+1)`-st smallest eigenvalue of `A`, counted
with multiplicity: the `λ_{k+1}(A)` of §2 (2.5).  This file proves, for every hermitian
matrix over `ℝ` or `ℂ` and with `‖·‖` the `ℓ²` operator norm, the three parts of Lemma 3.13:
(a) the identity `‖A‖ = max(λ_N, -λ_1)`;
(b) Weyl's inequality `|λ_k(A) - λ_k(B)| ≤ ‖A - B‖`;
(c) the reflection `λ_k(-A) = -λ_{N+1-k}(A)`.
The proofs use an orthonormal eigenbasis listed in nondecreasing order of the eigenvalues, and
the min-max characterisation (MM) in the proof of Lemma 3.13 (b): `λ_{k+1} ≤ t` if and only if
some `(k+1)`-dimensional subspace has `⟨x, A x⟩ ≤ t |x|²` on it.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 3. Ordered eigenvalues -/

theorem eigAsc_monotone {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    Monotone (eigAsc hA) := by
  intro a b hab
  exact hA.eigenvalues₀_antitone (by simpa [Fin.le_iff_val_le_val] using Fin.rev_le_rev.mpr hab)

/-! ### Spectral expansion and the min-max characterisation

The quadratic form `x ↦ re ⟨x, A x⟩` is computed on `EuclideanSpace 𝕜 (Fin N)` in an orthonormal
eigenbasis listed in nondecreasing order of the eigenvalues, as in the proof of Lemma 3.13. -/

/-- The real part of the quadratic form `⟨X, A X⟩` on `EuclideanSpace 𝕜 (Fin N)`. -/
private noncomputable def qf {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (X : EuclideanSpace 𝕜 (Fin N)) : ℝ :=
  RCLike.re (inner 𝕜 X (Matrix.toEuclideanLin A X))

/-- An orthonormal eigenbasis of `A`, with the eigenvalues in nondecreasing order. -/
private structure AscEigen {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) where
  vec : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N))
  val : Fin N → ℝ
  mono : Monotone val
  eq : ∀ k, A *ᵥ (vec k).ofLp = val k • (vec k).ofLp

/-- The bijection of `Fin N` sending `k` to the index, in `hA.eigenvalues`, of the `(k+1)`-st
smallest eigenvalue. -/
private noncomputable def ascPerm (N : ℕ) : Equiv.Perm (Fin N) :=
  Fin.revPerm.trans ((finCongr (Fintype.card_fin N).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)))

private theorem eigenvalues_ascPerm {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (k : Fin N) : hA.eigenvalues (ascPerm N k) = eigAsc hA k := by
  simp [ascPerm, Matrix.IsHermitian.eigenvalues, eigAsc]

/-- The eigenbasis of a hermitian matrix, reindexed so that the eigenvalues are `eigAsc hA`. -/
private noncomputable def AscEigen.ofHerm {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) : AscEigen A where
  vec := hA.eigenvectorBasis.reindex (ascPerm N).symm
  val := eigAsc hA
  mono := eigAsc_monotone hA
  eq k := by
    simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    rw [← eigenvalues_ascPerm hA k]
    exact hA.mulVec_eigenvectorBasis _

/-- The same eigenbasis in reversed order is an ascending eigenbasis of `-A`. -/
private noncomputable def AscEigen.neg {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (d : AscEigen A) :
    AscEigen (-A) where
  vec := d.vec.reindex Fin.revPerm
  val k := -d.val k.rev
  mono a b hab := neg_le_neg (d.mono (Fin.rev_le_rev.mpr hab))
  eq k := by
    simp only [OrthonormalBasis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply,
      Matrix.neg_mulVec, d.eq, neg_smul]

private theorem norm_lin_le {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (X : EuclideanSpace 𝕜 (Fin N)) : ‖Matrix.toEuclideanLin M X‖ ≤ ‖M‖ * ‖X‖ := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) M) X

/-- `|⟨X, M X⟩| ≤ ‖M‖ |X|²` for the `ℓ²` operator norm. -/
private theorem abs_qf_le {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (X : EuclideanSpace 𝕜 (Fin N)) : |qf M X| ≤ ‖M‖ * ‖X‖ ^ 2 := by
  unfold qf
  calc |RCLike.re (inner 𝕜 X (Matrix.toEuclideanLin M X))|
      ≤ ‖inner 𝕜 X (Matrix.toEuclideanLin M X)‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖X‖ * ‖Matrix.toEuclideanLin M X‖ := norm_inner_le_norm _ _
    _ ≤ ‖X‖ * (‖M‖ * ‖X‖) := by gcongr; exact norm_lin_le M X
    _ = ‖M‖ * ‖X‖ ^ 2 := by ring

private theorem qf_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) 𝕜) (X : EuclideanSpace 𝕜 (Fin N)) :
    qf (B - A) X = qf B X - qf A X := by
  unfold qf
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub]

namespace AscEigen

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (d : AscEigen A)

private theorem lin_vec (k : Fin N) :
    Matrix.toEuclideanLin A (d.vec k) = ((d.val k : ℝ) : 𝕜) • d.vec k := by
  apply (WithLp.ofLp_injective 2)
  have := d.eq k
  simpa [RCLike.real_smul_eq_coe_smul] using this

private theorem inner_vec_lin (hA : A.IsHermitian) (k : Fin N) (X : EuclideanSpace 𝕜 (Fin N)) :
    inner 𝕜 (d.vec k) (Matrix.toEuclideanLin A X) =
      ((d.val k : ℝ) : 𝕜) * inner 𝕜 (d.vec k) X := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [← hT (d.vec k) X, d.lin_vec k, inner_smul_left]
  simp

/-- `re ⟨X, A X⟩ = ∑ₖ λₖ |⟨uₖ, X⟩|²` in the eigenbasis. -/
private theorem qf_eq (hA : A.IsHermitian) (X : EuclideanSpace 𝕜 (Fin N)) :
    qf A X = ∑ k, d.val k * ‖inner 𝕜 (d.vec k) X‖ ^ 2 := by
  unfold qf
  rw [← d.vec.sum_inner_mul_inner X (Matrix.toEuclideanLin A X), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [d.inner_vec_lin hA, ← inner_conj_symm X (d.vec k)]
  have h : (starRingEnd 𝕜) (inner 𝕜 (d.vec k) X) *
      (((d.val k : ℝ) : 𝕜) * inner 𝕜 (d.vec k) X) =
      ((d.val k * ‖inner 𝕜 (d.vec k) X‖ ^ 2 : ℝ) : 𝕜) := by
    rw [mul_left_comm, RCLike.conj_mul]; push_cast; ring
  rw [h, RCLike.ofReal_re]

/-- Parseval: `|X|² = ∑ₖ |⟨uₖ, X⟩|²`. -/
private theorem norm_sq_eq (X : EuclideanSpace 𝕜 (Fin N)) :
    ‖X‖ ^ 2 = ∑ k, ‖inner 𝕜 (d.vec k) X‖ ^ 2 :=
  (d.vec.sum_sq_norm_inner_right X).symm

/-- `|A X|² = ∑ₖ λₖ² |⟨uₖ, X⟩|²` in the eigenbasis. -/
private theorem norm_lin_sq (hA : A.IsHermitian) (X : EuclideanSpace 𝕜 (Fin N)) :
    ‖Matrix.toEuclideanLin A X‖ ^ 2 = ∑ k, d.val k ^ 2 * ‖inner 𝕜 (d.vec k) X‖ ^ 2 := by
  rw [← d.vec.sum_sq_norm_inner_right (Matrix.toEuclideanLin A X)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [d.inner_vec_lin hA, norm_mul]
  simp [mul_pow]

/-- Rayleigh upper bound on vectors orthogonal to the eigenvectors above index `k`. -/
private theorem qf_le (hA : A.IsHermitian) (k : Fin N) (X : EuclideanSpace 𝕜 (Fin N))
    (h : ∀ j, k < j → inner 𝕜 (d.vec j) X = 0) : qf A X ≤ d.val k * ‖X‖ ^ 2 := by
  rw [d.qf_eq hA, d.norm_sq_eq X, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j k with hj | hj
  · exact mul_le_mul_of_nonneg_right (d.mono hj) (by positivity)
  · rw [h j hj]; simp

/-- Rayleigh lower bound on vectors orthogonal to the eigenvectors below index `k`. -/
private theorem le_qf (hA : A.IsHermitian) (k : Fin N) (X : EuclideanSpace 𝕜 (Fin N))
    (h : ∀ j, j < k → inner 𝕜 (d.vec j) X = 0) : d.val k * ‖X‖ ^ 2 ≤ qf A X := by
  rw [d.qf_eq hA, d.norm_sq_eq X, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt k j with hj | hj
  · exact mul_le_mul_of_nonneg_right (d.mono hj) (by positivity)
  · rw [h j hj]; simp

/-- The span of the eigenvectors with index in `S`. -/
private noncomputable def spanOf (S : Finset (Fin N)) : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)) :=
  Submodule.span 𝕜 (Set.range fun j : S => d.vec j)

private theorem finrank_spanOf (S : Finset (Fin N)) :
    Module.finrank 𝕜 (d.spanOf S) = S.card := by
  unfold spanOf
  rw [finrank_span_eq_card, Fintype.card_coe]
  exact (d.vec.orthonormal.comp (fun j : S => (j : Fin N)) Subtype.val_injective).linearIndependent

private theorem inner_eq_zero_of_mem_spanOf (S : Finset (Fin N)) {X : EuclideanSpace 𝕜 (Fin N)}
    (hX : X ∈ d.spanOf S) {j : Fin N} (hj : j ∉ S) : inner 𝕜 (d.vec j) X = 0 := by
  have : d.spanOf S ≤ LinearMap.ker (innerₛₗ 𝕜 (d.vec j)) := by
    unfold spanOf
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have hij : (i : Fin N) ≠ j := fun h => hj (h ▸ i.2)
    simp [d.vec.orthonormal.inner_eq_zero hij.symm]
  simpa using this hX

/-- The min-max characterisation (MM) in the proof of Lemma 3.13 (b), with `k` in place of
`k - 1`: `λ_{k+1} ≤ t` if and only if some `(k+1)`-dimensional subspace has `⟨x, A x⟩ ≤ t |x|²`
on it. -/
private theorem mm_le (hA : A.IsHermitian) (k : Fin N) (t : ℝ) :
    d.val k ≤ t ↔ ∃ V : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)), Module.finrank 𝕜 V = k + 1 ∧
      ∀ X ∈ V, qf A X ≤ t * ‖X‖ ^ 2 := by
  constructor
  · intro ht
    refine ⟨d.spanOf (Finset.Iic k), by rw [d.finrank_spanOf, Fin.card_Iic], fun X hX => ?_⟩
    refine (d.qf_le hA k X fun j hj => d.inner_eq_zero_of_mem_spanOf _ hX ?_).trans
      (mul_le_mul_of_nonneg_right ht (by positivity))
    simpa using hj
  · rintro ⟨V, hV, hq⟩
    have hW := d.finrank_spanOf (Finset.Ici k)
    rw [Fin.card_Ici] at hW
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq V (d.spanOf (Finset.Ici k))
    have h2 : Module.finrank 𝕜 ↥(V ⊔ d.spanOf (Finset.Ici k)) ≤ N := by
      simpa using Submodule.finrank_le (V ⊔ d.spanOf (Finset.Ici k))
    have h3 : 0 < Module.finrank 𝕜 ↥(V ⊓ d.spanOf (Finset.Ici k)) := by
      have := k.isLt; omega
    obtain ⟨⟨X, hXV, hXW⟩, hX0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
    have hX0' : X ≠ 0 := fun h => hX0 (Subtype.ext h)
    have hlow := d.le_qf hA k X fun j hj => d.inner_eq_zero_of_mem_spanOf _ hXW (by simpa using hj)
    have hpos : 0 < ‖X‖ ^ 2 := by positivity
    exact le_of_mul_le_mul_right (hlow.trans (hq X hXV)) hpos

/-- Two ascending eigenbases of the same hermitian matrix have the same eigenvalue list. -/
private theorem val_eq (hA : A.IsHermitian) (d' : AscEigen A) : d.val = d'.val := by
  funext k
  refine le_antisymm ?_ ?_
  · exact (d.mm_le hA k _).mpr ((d'.mm_le hA k _).mp le_rfl)
  · exact (d'.mm_le hA k _).mpr ((d.mm_le hA k _).mp le_rfl)

/-- Each eigenvalue is at most `‖A‖` in absolute value. -/
private theorem abs_val_le_norm (k : Fin N) : |d.val k| ≤ ‖A‖ := by
  have h := norm_lin_le A (d.vec k)
  rw [d.lin_vec k, norm_smul, d.vec.orthonormal.1 k] at h
  simpa using h

end AscEigen

/-- One half of Weyl's inequality: `λ_k(B) ≤ λ_k(A) + ‖A - B‖`. -/
private theorem eigAsc_le_add {N : ℕ} {A B : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin N) : eigAsc hB k ≤ eigAsc hA k + ‖A - B‖ := by
  obtain ⟨V, hV, hq⟩ := ((AscEigen.ofHerm hA).mm_le hA k (eigAsc hA k)).mp le_rfl
  refine ((AscEigen.ofHerm hB).mm_le hB k _).mpr ⟨V, hV, fun X hX => ?_⟩
  have h1 := hq X hX
  have h2 := abs_qf_le (B - A) X
  rw [norm_sub_rev, qf_sub] at h2
  have h3 := (abs_le.mp h2).2
  nlinarith [h1, h3]

/-- Weyl's inequality, operator norm. -/
theorem abs_eigAsc_sub_le {N : ℕ} {A B : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin N) : |eigAsc hA k - eigAsc hB k| ≤ ‖A - B‖ := by
  have h1 := eigAsc_le_add hA hB k
  have h2 := eigAsc_le_add hB hA k
  rw [norm_sub_rev] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Lemma 3.13 (a): `‖A‖ = max(λ_n, -λ_1)`. -/
theorem norm_eq_max_eigAsc {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (hN : 0 < N) : ‖A‖ = max (eigAsc hA ⟨N - 1, by omega⟩) (-eigAsc hA ⟨0, hN⟩) := by
  set d := AscEigen.ofHerm hA with hd
  have e0 : eigAsc hA ⟨0, hN⟩ = d.val ⟨0, hN⟩ := rfl
  have e1 : eigAsc hA ⟨N - 1, by omega⟩ = d.val ⟨N - 1, by omega⟩ := rfl
  set ρ := max (eigAsc hA ⟨N - 1, by omega⟩) (-eigAsc hA ⟨0, hN⟩) with hρdef
  have m1 : eigAsc hA ⟨N - 1, by omega⟩ ≤ ρ := le_max_left _ _
  have m2 : -eigAsc hA ⟨0, hN⟩ ≤ ρ := le_max_right _ _
  have hρ : ∀ k, |d.val k| ≤ ρ := fun k => by
    have h1 : d.val k ≤ d.val ⟨N - 1, by omega⟩ := d.mono (by simp [Fin.le_def]; omega)
    have h2 : d.val ⟨0, hN⟩ ≤ d.val k := d.mono (by simp [Fin.le_def])
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (hρ ⟨0, hN⟩)
  refine le_antisymm ?_ (max_le ((le_abs_self _).trans (d.abs_val_le_norm _))
    ((neg_le_abs _).trans (d.abs_val_le_norm _)))
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hρ0 fun X => ?_
  change ‖Matrix.toEuclideanLin A X‖ ≤ ρ * ‖X‖
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, d.norm_lin_sq hA X, d.norm_sq_eq X,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have : d.val k ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hρ k) 2
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- Lemma 3.13 (c): reflection, `λ_k(-A) = -λ_{n+1-k}(A)`. -/
theorem eigAsc_neg {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) (k : Fin N) :
    eigAsc hA.neg k = -eigAsc hA k.rev := by
  exact (congrFun ((AscEigen.ofHerm hA).neg.val_eq hA.neg (AscEigen.ofHerm hA.neg)) k).symm

end Rigidity
