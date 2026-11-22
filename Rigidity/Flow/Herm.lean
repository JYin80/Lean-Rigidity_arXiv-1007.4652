module

public import Rigidity.Ensemble.Basic
public import Rigidity.Spectrum.Continuity
public import Rigidity.Spectrum.Eigenvalues
public import Rigidity.MainDefs

@[expose] public section

/-!
# The space of hermitian matrices as a Euclidean space, and the eigenvalue vector

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `𝕜 = ℝ` or `ℂ`, `Herm 𝕜 N` is the real inner product space `𝓗` of §12.1 of self-adjoint
`N × N` matrices over `𝕜`, realised as a subspace of `ℝ^{N × N × 2}` through the real and imaginary
parts of the entries, with `⟨X, Y⟩ = Tr(XY)` and `|X|² = ∑_{i,j} |x_ij|²`.  The file proves:
* §14.2: `dim_ℝ 𝓗 = N + β N (N - 1) / 2` with `β = dim_ℝ 𝕜`;
* the formulas for the inner product and the norm of §12.1, and that `Herm.ofPair`,
  `Herm.toMatrix` and `Herm.ofMatrix` are inverse to each other on self-adjoint data;
* Lemma 15.1 (a): the ordered eigenvalue vector `λ(H)` satisfies `λ(U H U*) = λ(H)` for unitary
  `U`, `λ(diag x) = x` for nondecreasing `x`, `|λ(H)| = |H|` and
  `|λ_k(H) - λ_k(H')| ≤ |H - H'|`; and every `H` equals `U diag(λ(H)) U*` for a unitary `U`;
* Lemma 13.1 (c): `λ(c H) = c λ(H)` for `c > 0`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

namespace Herm

variable {N : ℕ}


/-- The element of `𝓗` with the upper triangle of `A` (equal to `A` if `A` is self-adjoint). -/
noncomputable def ofMatrix (A : Matrix (Fin N) (Fin N) 𝕜) : Herm 𝕜 N :=
  ofPair fun p => A p.1.1 p.1.2

/-- `diag x` (§12.1). -/
noncomputable def diag (x : Fin N → ℝ) : Herm 𝕜 N :=
  ofPair fun p => if p.1.1 = p.1.2 then ((x p.1.1 : ℝ) : 𝕜) else 0

/-- The conjugation `𝒪_U(H) = U H U*` (§15). -/
noncomputable def conj (U : Matrix (Fin N) (Fin N) 𝕜) (H : Herm 𝕜 N) : Herm 𝕜 N :=
  ofMatrix (U * H.toMatrix * star U)

/-- `Φ` is invariant: `Φ(U H U*) = Φ(H)` for all `U ∈ U_β(N)` (§12.1). -/
def IsInvariant {α : Type*} (Φ : Herm 𝕜 N → α) : Prop :=
  ∀ U ∈ Matrix.unitaryGroup (Fin N) 𝕜, ∀ H, Φ (conj U H) = Φ H

end Herm

/-! ### 1. Entries and real coordinates of `H ∈ 𝓗` -/

section Entries

variable {N : ℕ}

private theorem mk'_of_le {i j : Fin N} (h : i ≤ j) : Pair.mk' i j = ⟨(i, j), h⟩ := by
  simp [Pair.mk', h]

private theorem mk'_of_gt {i j : Fin N} (h : j < i) : Pair.mk' i j = ⟨(j, i), h.le⟩ := by
  simp [Pair.mk', not_le.mpr h]

private theorem herm_prop (H : Herm 𝕜 N) (i j : Fin N) :
    H.coord (j, i, 0) = H.coord (i, j, 0) ∧ H.coord (j, i, 1) = -H.coord (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → H.coord (i, j, 1) = 0) :=
  (H : hermSub 𝕜 N).2 i j

private theorem coord_diag_im (H : Herm 𝕜 N) (i : Fin N) : H.coord (i, i, 1) = 0 := by
  have := (herm_prop H i i).2.1
  linarith

/-- The entries of `H` in terms of its real coordinates: `h_ij = Re h_ij + Im h_ij · I`. -/
private theorem toMatrix_apply (H : Herm 𝕜 N) (i j : Fin N) :
    H.toMatrix i j = ((H.coord (i, j, 0) : ℝ) : 𝕜) + ((H.coord (i, j, 1) : ℝ) : 𝕜) * RCLike.I := by
  unfold Herm.toMatrix Rigidity.toMatrix
  simp only [Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have e : Pair.mk' i j = ⟨(i, j), h.le⟩ := mk'_of_le h.le
    simp [h, e, Herm.toPair]
  · have e : Pair.mk' i i = ⟨(i, i), le_rfl⟩ := mk'_of_le le_rfl
    simp [e, Herm.toPair, coord_diag_im]
  · have e : Pair.mk' i j = ⟨(j, i), h.le⟩ := mk'_of_gt h
    have h1 := (herm_prop H j i).1
    have h2 := (herm_prop H j i).2.1
    rw [h1, h2]
    simp [not_lt.mpr h.le, h, e, Herm.toPair, RCLike.star_def, RCLike.conj_I]

private theorem re_toMatrix (H : Herm 𝕜 N) (i j : Fin N) :
    RCLike.re (H.toMatrix i j) = H.coord (i, j, 0) := by
  rw [toMatrix_apply]
  simp

private theorem im_toMatrix (H : Herm 𝕜 N) (i j : Fin N) :
    RCLike.im (H.toMatrix i j) = H.coord (i, j, 1) := by
  rw [toMatrix_apply]
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · simp [h, (herm_prop H i j).2.2 h]
  · simp [h]

/-- An element of `𝓗` is determined by its matrix. -/
private theorem herm_ext {X Y : Herm 𝕜 N} (h : X.toMatrix = Y.toMatrix) : X = Y := by
  have hc : ∀ q, X.coord q = Y.coord q := by
    rintro ⟨i, j, k⟩
    revert k
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [← re_toMatrix X, ← re_toMatrix Y, h]
    · rw [← im_toMatrix X, ← im_toMatrix Y, h]
  apply Subtype.ext
  ext q
  exact hc q

private theorem coord_ofPair (x : Pair N → 𝕜) (i j : Fin N) :
    (Herm.ofPair x).coord (i, j, 0) = RCLike.re (Rigidity.toMatrix x i j) ∧
      (Herm.ofPair x).coord (i, j, 1) = RCLike.im (Rigidity.toMatrix x i j) := by
  constructor <;> simp [Herm.coord, Herm.ofPair]

private theorem toMatrix_ofPair_aux (x : Pair N → 𝕜) :
    (Herm.ofPair x).toMatrix = Rigidity.toMatrix x := by
  ext i j
  rw [toMatrix_apply, (coord_ofPair x i j).1, (coord_ofPair x i j).2, RCLike.re_add_im]

private theorem toMatrix_add (X Y : Herm 𝕜 N) : (X + Y).toMatrix = X.toMatrix + Y.toMatrix := by
  ext i j
  rw [toMatrix_apply, Matrix.add_apply, toMatrix_apply, toMatrix_apply]
  have h0 : (X + Y).coord (i, j, 0) = X.coord (i, j, 0) + Y.coord (i, j, 0) := rfl
  have h1 : (X + Y).coord (i, j, 1) = X.coord (i, j, 1) + Y.coord (i, j, 1) := rfl
  rw [h0, h1]
  push_cast
  ring

private theorem toMatrix_sub (X Y : Herm 𝕜 N) : (X - Y).toMatrix = X.toMatrix - Y.toMatrix := by
  ext i j
  rw [toMatrix_apply, Matrix.sub_apply, toMatrix_apply, toMatrix_apply]
  have h0 : (X - Y).coord (i, j, 0) = X.coord (i, j, 0) - Y.coord (i, j, 0) := rfl
  have h1 : (X - Y).coord (i, j, 1) = X.coord (i, j, 1) - Y.coord (i, j, 1) := rfl
  rw [h0, h1]
  push_cast
  ring

private theorem toMatrix_smul (c : ℝ) (X : Herm 𝕜 N) : (c • X).toMatrix = c • X.toMatrix := by
  ext i j
  rw [toMatrix_apply, Matrix.smul_apply, toMatrix_apply]
  have h0 : (c • X).coord (i, j, 0) = c * X.coord (i, j, 0) := rfl
  have h1 : (c • X).coord (i, j, 1) = c * X.coord (i, j, 1) := rfl
  rw [h0, h1, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

/-- The matrix with upper triangle `A` is `A` when `A` is self-adjoint. -/
private theorem toMatrix_upper {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    Rigidity.toMatrix (fun p : Pair N => A p.1.1 p.1.2) = A := by
  ext i j
  simp only [Rigidity.toMatrix, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have e : Pair.mk' i j = ⟨(i, j), h.le⟩ := mk'_of_le h.le
    simp [h, e]
  · have e : Pair.mk' i i = ⟨(i, i), le_rfl⟩ := mk'_of_le le_rfl
    simpa [e] using hA.coe_re_apply_self i
  · have e : Pair.mk' i j = ⟨(j, i), h.le⟩ := mk'_of_gt h
    simpa [not_lt.mpr h.le, h, e] using hA.apply i j

private theorem toMatrix_ofMatrix {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    (Herm.ofMatrix A).toMatrix = A := by
  unfold Herm.ofMatrix
  rw [toMatrix_ofPair_aux]
  exact toMatrix_upper hA

private theorem toMatrix_conj (U : Matrix (Fin N) (Fin N) 𝕜) (H : Herm 𝕜 N) :
    (H.conj U).toMatrix = U * H.toMatrix * star U :=
  toMatrix_ofMatrix (Matrix.isHermitian_mul_mul_conjTranspose U H.isHermitian)

private theorem toMatrix_diag (x : Fin N → ℝ) :
    (Herm.diag (𝕜 := 𝕜) x).toMatrix = Matrix.diagonal fun k => ((x k : ℝ) : 𝕜) := by
  unfold Herm.diag
  rw [toMatrix_ofPair_aux]
  ext i j
  simp only [Rigidity.toMatrix, Matrix.of_apply, Matrix.diagonal_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have e : Pair.mk' i j = ⟨(i, j), h.le⟩ := mk'_of_le h.le
    simp [h, h.ne, e]
  · have e : Pair.mk' i i = ⟨(i, i), le_rfl⟩ := mk'_of_le le_rfl
    simp [e]
  · have e : Pair.mk' i j = ⟨(j, i), h.le⟩ := mk'_of_gt h
    simp [not_lt.mpr h.le, h, h.ne, h.ne', e]

end Entries

/-! ### 2. The spectral decomposition in ascending order -/

section Spectral

variable {N : ℕ}

/-- The permutation of `Fin N` relating the ascending order of `eigAsc` to the indexing of
`Matrix.IsHermitian.eigenvalues`. -/
private noncomputable def sigmaPerm (N : ℕ) : Fin N ≃ Fin N :=
  Fin.revPerm.trans ((finCongr (Fintype.card_fin N).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)))

private theorem eigAsc_eq_eigenvalues {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (k : Fin N) : eigAsc hA k = hA.eigenvalues (sigmaPerm N k) := by
  simp [eigAsc, Matrix.IsHermitian.eigenvalues, sigmaPerm]

/-- Spectral theorem with the eigenvalues in ascending order: `A = U diag(λ(A)) U*`. -/
private theorem exists_spectral {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      A = U * Matrix.diagonal (fun k => ((eigAsc hA k : ℝ) : 𝕜)) * star U := by
  set V : Matrix (Fin N) (Fin N) 𝕜 := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) 𝕜) with hV
  have hVu : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  set D : Matrix (Fin N) (Fin N) 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hspec : A = V * D * star V := by
    have := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  refine ⟨V.submatrix id (sigmaPerm N), ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
    have e : Vᴴ.submatrix (sigmaPerm N) id * V.submatrix id (sigmaPerm N) =
        (Vᴴ * V).submatrix (sigmaPerm N) (sigmaPerm N) :=
      Matrix.submatrix_mul_equiv Vᴴ V (sigmaPerm N) (Equiv.refl _) (sigmaPerm N)
    rw [e, ← Matrix.star_eq_conjTranspose, hVu, Matrix.submatrix_one_equiv]
  · have hd : Matrix.diagonal (fun k => ((eigAsc hA k : ℝ) : 𝕜)) =
        D.submatrix (sigmaPerm N) (sigmaPerm N) := by
      rw [hD, Matrix.submatrix_diagonal_equiv]
      congr 1
      funext k
      simp [eigAsc_eq_eigenvalues hA k]
    have e1 : V.submatrix id (sigmaPerm N) * D.submatrix (sigmaPerm N) (sigmaPerm N) =
        (V * D).submatrix id (sigmaPerm N) :=
      Matrix.submatrix_mul_equiv V D id (sigmaPerm N) (sigmaPerm N)
    have e2 : (V * D).submatrix id (sigmaPerm N) * Vᴴ.submatrix (sigmaPerm N) id =
        (V * D * Vᴴ).submatrix id id :=
      Matrix.submatrix_mul_equiv (V * D) Vᴴ id (sigmaPerm N) id
    rw [hd, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, e1, e2,
      Matrix.submatrix_id_id, ← Matrix.star_eq_conjTranspose]
    exact hspec

private theorem charpoly_conj {U : Matrix (Fin N) (Fin N) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) (z : Fin N → ℝ) :
    (U * Matrix.diagonal (fun k => ((z k : ℝ) : 𝕜)) * star U).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C ((z k : ℝ) : 𝕜)) := by
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.charpoly_diagonal]

private theorem roots_prod_X_sub_C (f : Fin N → 𝕜) :
    (∏ k, (Polynomial.X - Polynomial.C (f k))).roots = Finset.univ.val.map f := by
  have h := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map f)
  rw [Multiset.map_map] at h
  rw [Finset.prod_eq_multiset_prod]
  exact h

/-- If `A = U diag(y) U*` with `U` unitary and `y` nondecreasing, then `y = λ(A)`. -/
private theorem eigAsc_eq_of_conj {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {U : Matrix (Fin N) (Fin N) 𝕜} (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) {y : Fin N → ℝ}
    (hy : Monotone y) (h : A = U * Matrix.diagonal (fun k => ((y k : ℝ) : 𝕜)) * star U) :
    eigAsc hA = y := by
  obtain ⟨V, hV, hAV⟩ := exists_spectral hA
  have h1 := charpoly_conj hU y
  have h2 := charpoly_conj hV (eigAsc hA)
  rw [← h] at h1
  rw [← hAV] at h2
  have h4 := congrArg Polynomial.roots (h1.symm.trans h2)
  rw [roots_prod_X_sub_C, roots_prod_X_sub_C] at h4
  have h5 : Finset.univ.val.map y = Finset.univ.val.map (eigAsc hA) := by
    have hm : ∀ g : Fin N → ℝ, Finset.univ.val.map (fun k => ((g k : ℝ) : 𝕜)) =
        (Finset.univ.val.map g).map (fun r : ℝ => (r : 𝕜)) := fun g =>
      (Multiset.map_map _ _ _).symm
    rw [hm, hm] at h4
    exact Multiset.map_injective RCLike.ofReal_injective h4
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at h5
  exact List.ofFn_injective (List.Perm.eq_of_sortedLE
    (List.sortedLE_ofFn_iff.mpr (eigAsc_monotone hA)) (List.sortedLE_ofFn_iff.mpr hy) h5.symm)

private theorem exists_conj_diag_aux (H : Herm 𝕜 N) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) 𝕜,
      H.toMatrix = U * Matrix.diagonal (fun k => ((eigVec H k : ℝ) : 𝕜)) * star U :=
  exists_spectral H.isHermitian

end Spectral

/-! ### 3. The dimension of `𝓗` -/

section Dimension

variable {N : ℕ}

/-- The strictly upper-triangular index pairs. -/
private abbrev UpperIdx (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

/-- The real-linear map `H ↦ ((Re h_ii)_i, (h_ij)_{i<j})` from `𝓗` to `ℝ^N × 𝕜^{N(N-1)/2}`. -/
private noncomputable def hermSplit (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) :
    Herm 𝕜 N →ₗ[ℝ] (Fin N → ℝ) × (UpperIdx N → 𝕜) where
  toFun H := (fun i => H.coord (i, i, 0), fun p => H.toMatrix p.1.1 p.1.2)
  map_add' X Y := by
    refine Prod.ext (funext fun i => rfl) (funext fun p => ?_)
    simp [toMatrix_add]
  map_smul' c X := by
    refine Prod.ext (funext fun i => rfl) (funext fun p => ?_)
    simp [toMatrix_smul]

private theorem hermSplit_injective : Function.Injective (hermSplit 𝕜 N) := by
  intro X Y h
  have h1 : ∀ i, X.coord (i, i, 0) = Y.coord (i, i, 0) := fun i => congrFun (congrArg Prod.fst h) i
  have h2 : ∀ p : UpperIdx N, X.toMatrix p.1.1 p.1.2 = Y.toMatrix p.1.1 p.1.2 := fun p =>
    congrFun (congrArg Prod.snd h) p
  apply herm_ext
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h2 ⟨(i, j), hij⟩
  · rw [toMatrix_apply, toMatrix_apply, coord_diag_im, coord_diag_im, h1]
  · have := h2 ⟨(j, i), hij⟩
    rw [← X.isHermitian.apply i j, ← Y.isHermitian.apply i j]
    simp only at this
    rw [this]

private theorem hermSplit_surjective : Function.Surjective (hermSplit 𝕜 N) := by
  rintro ⟨d, s⟩
  let x : Pair N → 𝕜 := fun p =>
    if h : p.1.1 < p.1.2 then s ⟨p.1, h⟩ else ((d p.1.1 : ℝ) : 𝕜)
  refine ⟨Herm.ofPair x, Prod.ext (funext fun i => ?_) (funext fun p => ?_)⟩
  · change (Herm.ofPair x).coord (i, i, 0) = d i
    rw [← re_toMatrix, toMatrix_ofPair_aux]
    simp [Rigidity.toMatrix, mk'_of_le (le_refl i), x]
  · change (Herm.ofPair x).toMatrix p.1.1 p.1.2 = s p
    rw [toMatrix_ofPair_aux]
    obtain ⟨⟨i, j⟩, hij⟩ := p
    simp [Rigidity.toMatrix, hij, mk'_of_le hij.le, x]

private theorem card_upperIdx (N : ℕ) : Fintype.card (UpperIdx N) = N.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using Fintype.card_product_filter_lt (α := Fin N)

end Dimension

/-- §14.2: `dim 𝓗 = N + βN(N-1)/2`. -/
theorem finrank_herm (N : ℕ) :
    (Module.finrank ℝ (Herm 𝕜 N) : ℝ) = N + betaF 𝕜 * N * (N - 1) / 2 := by
  have e := (LinearEquiv.ofBijective (hermSplit 𝕜 N)
    ⟨hermSplit_injective, hermSplit_surjective⟩).finrank_eq
  rw [e, Module.finrank_prod, Module.finrank_pi, Module.finrank_pi_fintype]
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, card_upperIdx, smul_eq_mul]
  push_cast
  rw [Nat.cast_choose_two]
  simp only [betaF]
  ring

/-- §12.1: `⟨X, Y⟩ = Tr(XY)`. -/
theorem Herm.inner_eq_trace {N : ℕ} (X Y : Herm 𝕜 N) :
    inner ℝ X Y = RCLike.re (X.toMatrix * Y.toMatrix).trace := by
  have h1 : inner ℝ X Y = ∑ q : Fin N × Fin N × Fin 2, X.coord q * Y.coord q := by
    change inner ℝ (X : hermSub 𝕜 N).1 (Y : hermSub 𝕜 N).1 = _
    rw [PiLp.inner_apply]
    simp [Herm.coord, mul_comm]
  have h2 : ∀ i j : Fin N, RCLike.re (X.toMatrix i j * Y.toMatrix j i) =
      X.coord (i, j, 0) * Y.coord (i, j, 0) + X.coord (i, j, 1) * Y.coord (i, j, 1) := by
    intro i j
    rw [RCLike.mul_re, re_toMatrix, re_toMatrix, im_toMatrix, im_toMatrix, (herm_prop Y i j).1,
      (herm_prop Y i j).2.1]
    ring
  rw [h1, Fintype.sum_prod_type]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two, h2]

/-- §12.1: `|X|² = ∑_{i,j} |x_ij|²`. -/
theorem Herm.norm_sq_eq {N : ℕ} (X : Herm 𝕜 N) : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X.toMatrix i j‖ ^ 2 := by
  have h1 : ‖X‖ ^ 2 = ∑ q : Fin N × Fin N × Fin 2, X.coord q ^ 2 := by
    change ‖(X : hermSub 𝕜 N).1‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
    simp [Herm.coord]
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two, RCLike.norm_sq_eq_def, re_toMatrix, im_toMatrix]
  ring

theorem Herm.toMatrix_ofPair {N : ℕ} (x : Pair N → 𝕜) : (Herm.ofPair x).toMatrix = Rigidity.toMatrix x := by
  exact toMatrix_ofPair_aux x

theorem Herm.ofMatrix_toMatrix {N : ℕ} (X : Herm 𝕜 N) : Herm.ofMatrix X.toMatrix = X := by
  apply herm_ext
  rw [toMatrix_ofMatrix X.isHermitian]

/-! ### 4. Lemma 15.1 (a): norm and Lipschitz bound of the eigenvalue vector -/

section EigVec

variable {N : ℕ}

private theorem sum_sq_eigVec_aux (H : Herm 𝕜 N) : ∑ k, eigVec H k ^ 2 = ‖H‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Herm.inner_eq_trace]
  obtain ⟨U, hU, hH⟩ := exists_conj_diag_aux H
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  set D : Matrix (Fin N) (Fin N) 𝕜 := Matrix.diagonal fun k => ((eigVec H k : ℝ) : 𝕜) with hD
  have h2 : H.toMatrix * H.toMatrix = U * (D * D) * star U := by
    rw [hH]
    calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by
          rw [hUU, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, hD,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [sq]

private theorem abs_eigVec_sub_le_aux (H H' : Herm 𝕜 N) (k : Fin N) :
    |eigVec H k - eigVec H' k| ≤ ‖H - H'‖ := by
  have hW := abs_eigAsc_sub_le H.isHermitian H'.isHermitian k
  have hN : 0 < N := Fin.pos k
  refine le_trans hW ?_
  rw [← toMatrix_sub, norm_eq_max_eigAsc (H - H').isHermitian hN]
  have hsq := sum_sq_eigVec_aux (H - H')
  have hb : ∀ j, |eigVec (H - H') j| ≤ ‖H - H'‖ := fun j => by
    have h1 : eigVec (H - H') j ^ 2 ≤ ‖H - H'‖ ^ 2 := by
      rw [← hsq]
      exact Finset.single_le_sum (f := fun k => eigVec (H - H') k ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
    exact abs_le_of_sq_le_sq h1 (norm_nonneg _)
  exact max_le ((le_abs_self _).trans (hb _)) ((neg_le_abs _).trans (hb _))

end EigVec

theorem continuous_eigVec (N : ℕ) : Continuous (eigVec : Herm 𝕜 N → Fin N → ℝ) := by
  refine continuous_pi fun k => ?_
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun H H' => ?_).continuous
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  exact abs_eigVec_sub_le_aux H H' k

theorem Herm.measurable_ofPair (N : ℕ) : Measurable (Herm.ofPair : (Pair N → 𝕜) → Herm 𝕜 N) := by
  refine Continuous.measurable ?_
  have hc : ∀ i j : Fin N, Continuous fun x : Pair N → 𝕜 => Rigidity.toMatrix x i j := by
    intro i j
    simp only [Rigidity.toMatrix, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_star.comp (continuous_apply _)
    · exact RCLike.continuous_ofReal.comp (RCLike.continuous_re.comp (continuous_apply _))
  refine Continuous.subtype_mk ?_ _
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun q => ?_)
  by_cases h : q.2.2 = 0
  · simp only [h, ↓reduceIte]
    exact RCLike.continuous_re.comp (hc _ _)
  · simp only [h, ↓reduceIte]
    exact RCLike.continuous_im.comp (hc _ _)

/-- Lemma 15.1(a): `λ(UHU*) = λ(H)`. -/
theorem eigVec_conj {N : ℕ} {U : Matrix (Fin N) (Fin N) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) (H : Herm 𝕜 N) : eigVec (H.conj U) = eigVec H := by
  obtain ⟨V, hV, hH⟩ := exists_conj_diag_aux H
  refine eigAsc_eq_of_conj (H.conj U).isHermitian (U := U * V) (Submonoid.mul_mem _ hU hV)
    (y := eigVec H) (eigAsc_monotone H.isHermitian) ?_
  rw [toMatrix_conj, hH, star_mul]
  simp only [Matrix.mul_assoc]

/-- Lemma 15.1(a): `λ(diag x) = x` on the closed chamber. -/
theorem eigVec_diag {N : ℕ} {x : Fin N → ℝ} (hx : Monotone x) :
    eigVec (Herm.diag (𝕜 := 𝕜) x) = x := by
  refine eigAsc_eq_of_conj (Herm.diag (𝕜 := 𝕜) x).isHermitian (U := 1) (Submonoid.one_mem _) hx ?_
  rw [toMatrix_diag, star_one, Matrix.one_mul, Matrix.mul_one]

/-- Lemma 15.1(a): `|λ(H)| = |H|`. -/
theorem sum_sq_eigVec {N : ℕ} (H : Herm 𝕜 N) : ∑ k, eigVec H k ^ 2 = ‖H‖ ^ 2 := by
  exact sum_sq_eigVec_aux H

/-- Lemma 13.1 (c): `λ(cH) = c λ(H)` for `c > 0`. -/
theorem eigVec_smul {N : ℕ} {c : ℝ} (hc : 0 < c) (H : Herm 𝕜 N) : eigVec (c • H) = c • eigVec H := by
  obtain ⟨U, hU, hH⟩ := exists_conj_diag_aux H
  have hmono : Monotone (c • eigVec H) := fun a b hab =>
    mul_le_mul_of_nonneg_left (eigAsc_monotone H.isHermitian hab) hc.le
  refine eigAsc_eq_of_conj (c • H).isHermitian hU hmono ?_
  have hD : Matrix.diagonal (fun k => (((c • eigVec H) k : ℝ) : 𝕜)) =
      c • Matrix.diagonal (fun k => ((eigVec H k : ℝ) : 𝕜)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, RCLike.real_smul_eq_coe_mul]
  rw [toMatrix_smul, hH, hD, Matrix.mul_smul, Matrix.smul_mul]

/-- Lemma 15.1 (a): every `H ∈ 𝓗` is `U diag(λ(H)) U*` for a unitary `U`, which is orthogonal when
`𝕜 = ℝ`. -/
theorem exists_unitary_eq_conj_diag {N : ℕ} (H : Herm 𝕜 N) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) 𝕜, H = Herm.conj U (Herm.diag (eigVec H)) := by
  obtain ⟨U, hU, hH⟩ := exists_conj_diag_aux H
  refine ⟨U, hU, herm_ext ?_⟩
  rw [toMatrix_conj, toMatrix_diag]
  exact hH

end Rigidity
