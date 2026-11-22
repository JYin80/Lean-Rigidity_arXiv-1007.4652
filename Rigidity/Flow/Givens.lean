module

public import Rigidity.Flow.Chamber
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.Herm
public import Rigidity.Flow.Invariant
public import Rigidity.Flow.MehlerSmooth

@[expose] public section

/-!
# The radial part of the Ornstein–Uhlenbeck generator (Lemma 15.2)

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Let `Φ : 𝓗 → ℝ` be invariant, `φ = Φ ∘ diag` and `D = diag x`.  The file proves Lemma 15.2:
* for every `x` and `Φ ∈ C¹(𝓗)`: `∂_TΦ(D) = 0` for every `T` with zero diagonal,
  `∇Φ(D) = diag(∇φ(x))`, `|∇Φ(D)| = |∇φ(x)|` and `⟨D, ∇Φ(D)⟩ = x · ∇φ(x)` (`gradient_diag`);
* for `x` with pairwise distinct coordinates and `Φ ∈ C²(𝓗)`, (15.2):
  `(AΦ)(D) = (Lφ)(x)` with `A` the generator (14.1) for the variance `σ² = 2/(βN)` and `L` the
  generator (15.2) (`ouGen_diag_eq_dysonGen`).  For `β = 1` the generator `L` is twice the
  `β = 1` generator [EYY, (2.32)] (Remark 15.3).

The proof follows Steps 1–4 of the proof of Lemma 15.2.  The off-diagonal directions are
`E_ij w + E_ji w̄`; conjugation by diagonal unitaries gives Step 1 (sign changes) and Step 3
(phases), and Step 2 differentiates `θ ↦ Φ(R_θ D R_θ*)` twice, with `R_θ` the rotation in the
`(i, j)`-plane and `R_θ D R_θ*` given by (15.3).  The Laplacian on `𝓗` is computed from the family
`E_ii`, `½ (E_ij w + E_ji w̄)` (`i ≠ j`, `w ∈ {1, i}`), which satisfies `∑_b ⟨v_b, u⟩ v_b = u`;
each pair `i < j` then contributes `β` directions of the basis `𝔅` of §14.2.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

section Toolkit

variable {N : ℕ}

private theorem toMatrix_add' (X Y : Herm 𝕜 N) : (X + Y).toMatrix = X.toMatrix + Y.toMatrix := by
  have h0 : ∀ q, (X + Y).coord q = X.coord q + Y.coord q := fun _ => rfl
  ext i j
  simp only [Herm.toMatrix, Rigidity.toMatrix, Herm.toPair, Matrix.of_apply, Matrix.add_apply, h0]
  split_ifs <;> simp only [map_add, star_add, add_mul] <;> ring

private theorem toMatrix_smul' (c : ℝ) (X : Herm 𝕜 N) : (c • X).toMatrix = c • X.toMatrix := by
  have h0 : ∀ q, (c • X).coord q = c * X.coord q := fun _ => rfl
  ext i j
  simp only [Herm.toMatrix, Rigidity.toMatrix, Herm.toPair, Matrix.of_apply, Matrix.smul_apply, h0]
  split_ifs <;> push_cast <;> simp [RCLike.real_smul_eq_coe_mul] <;> ring

private theorem toMatrix_inj {X Y : Herm 𝕜 N} (h : X.toMatrix = Y.toMatrix) : X = Y := by
  rw [← Herm.ofMatrix_toMatrix X, h, Herm.ofMatrix_toMatrix]

private theorem mk'_of_le {i j : Fin N} (h : i ≤ j) : Pair.mk' i j = ⟨(i, j), h⟩ := by
  simp [Pair.mk', h]

private theorem mk'_of_gt {i j : Fin N} (h : j < i) : Pair.mk' i j = ⟨(j, i), h.le⟩ := by
  simp [Pair.mk', not_le.mpr h]

private theorem toMatrix_ofMatrix {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    (Herm.ofMatrix A).toMatrix = A := by
  unfold Herm.ofMatrix
  rw [Herm.toMatrix_ofPair]
  ext i j
  simp only [Rigidity.toMatrix, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have e : Pair.mk' i j = ⟨(i, j), h.le⟩ := mk'_of_le h.le
    simp [h, e]
  · have e : Pair.mk' i i = ⟨(i, i), le_rfl⟩ := mk'_of_le le_rfl
    simpa [e] using hA.coe_re_apply_self i
  · have e : Pair.mk' i j = ⟨(j, i), h.le⟩ := mk'_of_gt h
    simpa [not_lt.mpr h.le, h, e] using hA.apply i j

private theorem toMatrix_conj (U : Matrix (Fin N) (Fin N) 𝕜) (H : Herm 𝕜 N) :
    (H.conj U).toMatrix = U * H.toMatrix * star U :=
  toMatrix_ofMatrix (Matrix.isHermitian_mul_mul_conjTranspose U H.isHermitian)

private theorem toMatrix_diag (x : Fin N → ℝ) :
    (Herm.diag (𝕜 := 𝕜) x).toMatrix = Matrix.diagonal fun k => ((x k : ℝ) : 𝕜) := by
  unfold Herm.diag
  rw [Herm.toMatrix_ofPair]
  ext i j
  simp only [Rigidity.toMatrix, Matrix.of_apply, Matrix.diagonal_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have e : Pair.mk' i j = ⟨(i, j), h.le⟩ := mk'_of_le h.le
    simp [h, h.ne, e]
  · have e : Pair.mk' i i = ⟨(i, i), le_rfl⟩ := mk'_of_le le_rfl
    simp [e]
  · have e : Pair.mk' i j = ⟨(j, i), h.le⟩ := mk'_of_gt h
    simp [not_lt.mpr h.le, h, h.ne, h.ne', e]

/-- `H ↦ H.toMatrix` as a real-linear map from `𝓗` to the matrices. -/
private noncomputable def toMatrixL : Herm 𝕜 N →ₗ[ℝ] Matrix (Fin N) (Fin N) 𝕜 where
  toFun := Herm.toMatrix
  map_add' := toMatrix_add'
  map_smul' := toMatrix_smul'

/-- `diag : ℝ^N → 𝓗` as a continuous linear map. -/
private noncomputable def diagCLM : (Fin N → ℝ) →L[ℝ] Herm 𝕜 N :=
  LinearMap.toContinuousLinearMap
    { toFun := Herm.diag
      map_add' := fun x y => toMatrix_inj (by
        rw [toMatrix_add', toMatrix_diag, toMatrix_diag, toMatrix_diag, Matrix.diagonal_add]
        congr 1
        funext k
        simp)
      map_smul' := fun c x => toMatrix_inj (by
        rw [RingHom.id_apply, toMatrix_smul', toMatrix_diag, toMatrix_diag]
        ext i j
        by_cases h : i = j <;> simp [h, RCLike.real_smul_eq_coe_mul]) }

private theorem diagCLM_apply (x : Fin N → ℝ) : diagCLM (𝕜 := 𝕜) x = Herm.diag x := rfl

/-- The conjugation `𝒪_U` as a real-linear map of `𝓗`. -/
private noncomputable def conjL (U : Matrix (Fin N) (Fin N) 𝕜) : Herm 𝕜 N →ₗ[ℝ] Herm 𝕜 N where
  toFun := Herm.conj U
  map_add' X Y := toMatrix_inj (by
    rw [toMatrix_add', toMatrix_conj, toMatrix_conj, toMatrix_conj, toMatrix_add', Matrix.mul_add,
      Matrix.add_mul])
  map_smul' c X := toMatrix_inj (by
    rw [RingHom.id_apply, toMatrix_smul', toMatrix_conj, toMatrix_conj, toMatrix_smul',
      Matrix.mul_smul, Matrix.smul_mul])

/-- For invariant `Φ ∈ C^k(𝓗)`, `j ≤ k` and unitary `U`,
`D^jΦ(U H U*)[U v₁ U*, …, U v_j U*] = D^jΦ(H)[v₁, …, v_j]`. -/
private theorem iteratedFDeriv_conj {Φ : Herm 𝕜 N → ℝ} (hΦ : Herm.IsInvariant Φ)
    {k : WithTop ℕ∞} (h : ContDiff ℝ k Φ) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ k)
    {U : Matrix (Fin N) (Fin N) 𝕜} (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) (H : Herm 𝕜 N)
    (v : Fin j → Herm 𝕜 N) :
    iteratedFDeriv ℝ j Φ (H.conj U) (fun l => (v l).conj U) = iteratedFDeriv ℝ j Φ H v := by
  set g : Herm 𝕜 N →L[ℝ] Herm 𝕜 N := LinearMap.toContinuousLinearMap (conjL U)
  have e := g.iteratedFDeriv_comp_right h H hj
  have hg : Φ ∘ g = Φ := funext fun H => hΦ U hU H
  rw [hg] at e
  rw [e]
  rfl

end Toolkit

/-! ### Off-diagonal directions and diagonal unitaries -/

section Directions

variable {N : ℕ}

/-- The matrix with entry `w` at `(i, j)` and `w̄` at `(j, i)`. -/
private noncomputable def offM (i j : Fin N) (w : 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.single i j w + Matrix.single j i (star w)

private theorem offM_isHermitian (i j : Fin N) (w : 𝕜) : (offM i j w).IsHermitian := by
  simp [Matrix.IsHermitian, offM, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

/-- The element of `𝓗` with entry `w` at `(i, j)` and `w̄` at `(j, i)`. -/
private noncomputable def offH (i j : Fin N) (w : 𝕜) : Herm 𝕜 N := Herm.ofMatrix (offM i j w)

private theorem toMatrix_offH (i j : Fin N) (w : 𝕜) : (offH i j w).toMatrix = offM i j w :=
  toMatrix_ofMatrix (offM_isHermitian i j w)

private theorem offH_ofReal_mul (i j : Fin N) (r : ℝ) (w : 𝕜) :
    offH i j ((r : 𝕜) * w) = r • offH i j w := by
  refine toMatrix_inj ?_
  rw [toMatrix_smul', toMatrix_offH, toMatrix_offH]
  ext a b
  simp only [offM, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  split_ifs <;> simp [RCLike.real_smul_eq_coe_mul, star_mul', mul_comm]

private theorem offH_neg (i j : Fin N) (w : 𝕜) : offH i j (-w) = -offH i j w := by
  have h := offH_ofReal_mul i j (-1) w
  simp only [RCLike.ofReal_neg, RCLike.ofReal_one, neg_mul, one_mul, neg_smul, one_smul] at h
  exact h

private theorem diagonal_mul_mul_star (d : Fin N → 𝕜) (M : Matrix (Fin N) (Fin N) 𝕜) :
    Matrix.diagonal d * M * star (Matrix.diagonal d) =
      Matrix.of fun a b => d a * M a b * star (d b) := by
  ext a b
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]

private theorem diagonal_mem_unitaryGroup {d : Fin N → 𝕜} (hd : ∀ k, d k * star (d k) = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  exact hd k

private theorem conj_diagonal_diag {d : Fin N → 𝕜} (hd : ∀ k, d k * star (d k) = 1)
    (x : Fin N → ℝ) : (Herm.diag (𝕜 := 𝕜) x).conj (Matrix.diagonal d) = Herm.diag x := by
  refine toMatrix_inj ?_
  rw [toMatrix_conj, diagonal_mul_mul_star, toMatrix_diag]
  ext a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.of_apply, Matrix.diagonal_apply_eq]
    rw [mul_comm (d a), mul_assoc, hd a, mul_one]
  · simp [Matrix.diagonal_apply_ne _ h]

private theorem conj_diagonal_offH {i j : Fin N} (hij : i ≠ j) (d : Fin N → 𝕜) (w : 𝕜) :
    (offH i j w).conj (Matrix.diagonal d) = offH i j (d i * w * star (d j)) := by
  refine toMatrix_inj ?_
  rw [toMatrix_conj, diagonal_mul_mul_star, toMatrix_offH, toMatrix_offH]
  ext a b
  simp only [Matrix.of_apply, offM, Matrix.add_apply, Matrix.single_apply]
  by_cases h1 : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hij, hij.symm]
  · by_cases h2 : j = a ∧ i = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hij, hij.symm, star_mul', mul_comm, mul_left_comm]
    · simp [h1, h2]

end Directions

/-! ### A Parseval frame of `𝓗` and the Laplacian -/

section Frame

variable {N : ℕ}

/-- `w ↦ offM i j w` is real-linear. -/
private noncomputable def offML (i j : Fin N) : 𝕜 →ₗ[ℝ] Matrix (Fin N) (Fin N) 𝕜 where
  toFun := offM i j
  map_add' v w := by
    ext a b
    simp only [offM, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> simp only [star_add, add_zero, zero_add, add_add_add_comm]
  map_smul' c w := by
    ext a b
    simp only [offM, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, RingHom.id_apply]
    split_ifs <;> simp [RCLike.real_smul_eq_coe_mul, star_mul']

private theorem offML_apply (i j : Fin N) (w : 𝕜) : offML i j w = offM i j w := rfl

/-- The real basis `1, i` of `𝕜` (with `i = 0` for `𝕜 = ℝ`). -/
private noncomputable def wk : Fin 2 → 𝕜 := ![1, RCLike.I]

/-- `z = Re z · 1 + Re(ī z) · i`. -/
private theorem sum_re_wk (z : 𝕜) : ∑ k, RCLike.re (star (wk k) * z) • wk k = z := by
  rw [Fin.sum_univ_two]
  simp only [wk, Matrix.cons_val_zero, Matrix.cons_val_one, star_one, one_mul,
    RCLike.real_smul_eq_coe_mul, mul_one]
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · simp only [h, mul_zero, add_zero]
    conv_rhs => rw [← RCLike.re_add_im z, RCLike.im_eq_zero h z]
    simp
  · have : RCLike.re (star (RCLike.I : 𝕜) * z) = RCLike.im z := by
      rw [RCLike.star_def, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, RCLike.I_re, h]
      ring
    rw [this, RCLike.re_add_im]

/-- The frame: `E_aa` and, for `i ≠ j`, `½ (E_ij w + E_ji w̄)` with `w ∈ {1, i}`. -/
private noncomputable def frame : Fin N ⊕ (Fin N × Fin N × Fin 2) → Herm 𝕜 N
  | Sum.inl a => Herm.diag (Pi.single a 1)
  | Sum.inr q => if q.1 = q.2.1 then 0 else (2⁻¹ : ℝ) • offH q.1 q.2.1 (wk q.2.2)

private theorem inner_diag_single (a : Fin N) (u : Herm 𝕜 N) :
    inner ℝ (Herm.diag (𝕜 := 𝕜) (Pi.single a 1)) u = RCLike.re (u.toMatrix a a) := by
  rw [Herm.inner_eq_trace, toMatrix_diag]
  simp [Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]

private theorem inner_offH (i j : Fin N) (w : 𝕜) (u : Herm 𝕜 N) :
    inner ℝ (offH i j w) u = RCLike.re (w * u.toMatrix j i + star w * u.toMatrix i j) := by
  rw [Herm.inner_eq_trace, toMatrix_offH]
  rw [offM, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul,
    smul_eq_mul, smul_eq_mul]

private theorem re_add_star_mul (w z : 𝕜) :
    RCLike.re (w * star z + star w * z) = 2 * RCLike.re (star w * z) := by
  simp only [map_add, RCLike.mul_re, RCLike.star_def, RCLike.conj_re, RCLike.conj_im]
  ring

private theorem frame_pair (u : Herm 𝕜 N) {i j : Fin N} (hij : i ≠ j) :
    ∑ k, inner ℝ (frame (Sum.inr (i, j, k))) u • (frame (𝕜 := 𝕜) (Sum.inr (i, j, k))).toMatrix =
      (2⁻¹ : ℝ) • offM i j (u.toMatrix i j) := by
  have hu : u.toMatrix j i = star (u.toMatrix i j) := (u.isHermitian.apply j i).symm
  calc ∑ k, inner ℝ (frame (Sum.inr (i, j, k))) u • (frame (𝕜 := 𝕜) (Sum.inr (i, j, k))).toMatrix
      = ∑ k, (2⁻¹ : ℝ) • offML i j (RCLike.re (star (wk k) * u.toMatrix i j) • wk k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [frame, hij, ite_false, real_inner_smul_left, inner_offH, hu, re_add_star_mul,
          toMatrix_smul', toMatrix_offH, map_smul, offML_apply, smul_smul]
        congr 1
        ring
    _ = (2⁻¹ : ℝ) • offML i j (∑ k, RCLike.re (star (wk k) * u.toMatrix i j) • wk k) := by
        rw [map_sum, Finset.smul_sum]
    _ = _ := by rw [sum_re_wk]; rfl

private theorem sum_sum_single_apply (f : Fin N → Fin N → 𝕜) (r s : Fin N) :
    ∑ x, ∑ c, Matrix.single x c (f x c) r s = f r s := by
  rw [Finset.sum_eq_single r, Finset.sum_eq_single s]
  · simp
  · intro c _ hc
    simp [hc]
  · simp
  · intro x _ hx
    exact Finset.sum_eq_zero fun c _ => by simp [hx]
  · simp

private theorem frame_parseval (u : Herm 𝕜 N) : ∑ b, inner ℝ (frame b) u • frame b = u := by
  refine toMatrix_inj ?_
  have hL : ∀ X : Herm 𝕜 N, X.toMatrix = toMatrixL X := fun _ => rfl
  rw [hL, map_sum]
  simp only [← hL, toMatrix_smul']
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hp : ∀ i j, ∑ k, inner ℝ (frame (Sum.inr (i, j, k))) u •
      (frame (𝕜 := 𝕜) (Sum.inr (i, j, k))).toMatrix =
        if i = j then 0 else (2⁻¹ : ℝ) • offM i j (u.toMatrix i j) := by
    intro i j
    by_cases hij : i = j
    · simp [frame, hij]
    · rw [frame_pair u hij]
      simp [hij]
  simp_rw [hp]
  ext r s
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, inner_diag_single, frame,
    toMatrix_diag, Matrix.diagonal_apply]
  by_cases hrs : r = s
  · subst hrs
    have h0 : ∀ x c : Fin N, (if x = c then (0 : Matrix (Fin N) (Fin N) 𝕜) else
        (2⁻¹ : ℝ) • offM x c (u.toMatrix x c)) r r = 0 := by
      intro x c
      split_ifs with h
      · rfl
      · rw [Matrix.smul_apply, offM, Matrix.add_apply, Matrix.single_apply_of_ne,
          Matrix.single_apply_of_ne, add_zero, smul_zero]
        · rintro ⟨rfl, rfl⟩
          exact h rfl
        · rintro ⟨rfl, rfl⟩
          exact h rfl
    simp only [h0, Finset.sum_const_zero, add_zero, ite_true]
    rw [Finset.sum_eq_single r (fun x _ hx => by simp [Ne.symm hx])
      (fun h => absurd (Finset.mem_univ r) h)]
    simp only [Pi.single_eq_same, RCLike.ofReal_one, RCLike.real_smul_eq_coe_mul, mul_one]
    exact u.isHermitian.coe_re_apply_self r
  · have h1 : ∀ x c : Fin N, (if x = c then (0 : Matrix (Fin N) (Fin N) 𝕜) else
        (2⁻¹ : ℝ) • offM x c (u.toMatrix x c)) r s =
          (2⁻¹ : ℝ) • (Matrix.single x c (u.toMatrix x c) r s +
            Matrix.single c x (star (u.toMatrix x c)) r s) := by
      intro x c
      split_ifs with h
      · subst h
        rw [Matrix.single_apply_of_ne, Matrix.single_apply_of_ne, add_zero, smul_zero]
        · rfl
        · rintro ⟨rfl, rfl⟩
          exact hrs rfl
        · rintro ⟨rfl, rfl⟩
          exact hrs rfl
      · rfl
    simp only [hrs, ite_false, smul_zero, Finset.sum_const_zero, zero_add, h1]
    simp only [← Finset.smul_sum, Finset.sum_add_distrib]
    have e1 : ∑ x, ∑ c, Matrix.single x c (u.toMatrix x c) r s = u.toMatrix r s :=
      sum_sum_single_apply (fun x c => u.toMatrix x c) r s
    have e2 : ∑ x, ∑ c, Matrix.single c x (star (u.toMatrix x c)) r s = star (u.toMatrix s r) := by
      rw [Finset.sum_comm]
      exact sum_sum_single_apply (fun c x => star (u.toMatrix x c)) r s
    rw [e1, e2, u.isHermitian.apply r s, ← two_smul ℝ, smul_smul]
    norm_num

/-- For a finite family with `∑_b ⟨v_b, u⟩ v_b = u` for all `u`, `Δf(y) = ∑_b D²f(y)[v_b, v_b]`. -/
private theorem laplacian_eq_sum_frame {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : ι → E)
    (hv : ∀ u, ∑ b, inner ℝ (v b) u • v b = u) (f : E → ℝ) (y : E) :
    Laplacian.laplacian f y = ∑ b, fderiv ℝ (fderiv ℝ f) y (v b) (v b) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  set e := stdOrthonormalBasis ℝ E
  set L := fderiv ℝ (fderiv ℝ f) y
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc ∑ c, L (e c) (e c) = ∑ c, L (∑ b, inner ℝ (v b) (e c) • v b) (e c) := by simp_rw [hv]
    _ = ∑ c, ∑ b, inner ℝ (e c) (v b) * L (v b) (e c) := by
        simp only [map_sum, map_smul, _root_.sum_apply,
          _root_.smul_apply, smul_eq_mul, real_inner_comm]
    _ = ∑ b, L (v b) (∑ c, inner ℝ (e c) (v b) • e c) := by
        rw [Finset.sum_comm]
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ b, L (v b) (v b) := by simp_rw [e.sum_repr']

/-- `β = |1|² + |i|²`: `β = 1` if `i = 0` (`𝕜 = ℝ`) and `β = 2` otherwise. -/
private theorem betaF_eq_sum_wk : betaF 𝕜 = ∑ k, ‖(wk k : 𝕜)‖ ^ 2 := by
  rw [Fin.sum_univ_two]
  simp only [wk, Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, one_pow, betaF]
  rcases eq_or_ne (RCLike.I : 𝕜) 0 with h | h
  · have h1 : Module.finrank ℝ 𝕜 = 1 := by
      refine (finrank_eq_one_iff_of_ne_zero' (1 : 𝕜) one_ne_zero).mpr fun w => ⟨RCLike.re w, ?_⟩
      conv_rhs => rw [← RCLike.re_add_im w, RCLike.im_eq_zero h w]
      simp [RCLike.real_smul_eq_coe_mul]
    rw [h1, h, norm_zero]
    norm_num
  · have hle := RCLike.finrank_le_two 𝕜
    have hge : 2 ≤ Module.finrank ℝ 𝕜 := by
      have hli : LinearIndependent ℝ ![(1 : 𝕜), RCLike.I] := by
        refine LinearIndependent.pair_iff.mpr fun a b hab => ?_
        have hre := congrArg RCLike.re hab
        have him := congrArg RCLike.im hab
        have hI : RCLike.im (RCLike.I : 𝕜) = 1 :=
          (RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)).resolve_left h
        simp only [RCLike.real_smul_eq_coe_mul, mul_one, map_add, RCLike.ofReal_re,
          RCLike.re_ofReal_mul, RCLike.I_re, mul_zero, add_zero, map_zero, RCLike.ofReal_im,
          RCLike.im_ofReal_mul, hI, zero_add] at hre him
        exact ⟨hre, him⟩
      simpa using hli.fintype_card_le_finrank
    rw [show Module.finrank ℝ 𝕜 = 2 by omega, RCLike.norm_I_of_ne_zero h]
    norm_num

end Frame

/-! ### Givens rotations -/

section Rotation

variable {N : ℕ}

/-- The rotation `R_θ` in the `(i, j)`-plane: `R_θ e_i = cos θ e_i + sin θ e_j`,
`R_θ e_j = -sin θ e_i + cos θ e_j`, `R_θ e_k = e_k` otherwise. -/
private noncomputable def rot (i j : Fin N) (θ : ℝ) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun k m =>
    if k = i then (if m = i then (cos θ : 𝕜) else 0) + (if m = j then -(sin θ : 𝕜) else 0)
    else if k = j then (if m = i then (sin θ : 𝕜) else 0) + (if m = j then (cos θ : 𝕜) else 0)
    else if m = k then 1 else 0

/-- (15.3): `R_θ diag(y) R_θ* = diag(y) + ς sin²θ (E_ii - E_jj) - ς sin θ cos θ (E_ij + E_ji)`
with `ς = y_j - y_i`. -/
private theorem rot_conj {i j : Fin N} (hij : i ≠ j) (θ : ℝ) (y : Fin N → ℝ) :
    rot i j θ * Matrix.diagonal (fun k => ((y k : ℝ) : 𝕜)) * star (rot i j θ) =
      Matrix.diagonal (fun k => ((y k : ℝ) : 𝕜)) +
        ((y j - y i) * sin θ ^ 2 : ℝ) •
          Matrix.diagonal (fun k => (((Pi.single i 1 - Pi.single j 1 : Fin N → ℝ) k : ℝ) : 𝕜)) +
        (-(y j - y i) * sin θ * cos θ : ℝ) • offM i j 1 := by
  have hsc : (sin θ : 𝕜) ^ 2 + (cos θ : 𝕜) ^ 2 = 1 := by
    exact_mod_cast sin_sq_add_cos_sq θ
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, offM, Matrix.single_apply, rot, Matrix.of_apply]
  have hji := hij.symm
  by_cases hk1 : k = i
  · by_cases hl1 : l = i
    · simp [hk1, hl1, hij, hji, Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq',
        RCLike.real_smul_eq_coe_mul]
      linear_combination (y i : 𝕜) * hsc
    · by_cases hl2 : l = j
      · simp [hk1, hl2, hij, hji, Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq',
          RCLike.real_smul_eq_coe_mul]
        ring
      · simp [hk1, hl1, hl2, hji, Ne.symm hl1, Ne.symm hl2, add_mul, ite_mul, Finset.sum_ite_eq']
  · by_cases hk2 : k = j
    · by_cases hl1 : l = i
      · simp [hk2, hl1, hij, hji, Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq',
          RCLike.real_smul_eq_coe_mul]
        ring
      · by_cases hl2 : l = j
        · simp [hk2, hl2, hij, hji, Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq',
            RCLike.real_smul_eq_coe_mul]
          linear_combination (y j : 𝕜) * hsc
        · simp [hk2, hl1, hl2, hij, Ne.symm hl1, Ne.symm hl2, add_mul, ite_mul,
            Finset.sum_ite_eq']
    · by_cases hl1 : l = i
      · simp [hk1, hk2, hl1, Ne.symm hk1, Ne.symm hk2, hji]
      · by_cases hl2 : l = j
        · simp [hk1, hk2, hl2, Ne.symm hk1, Ne.symm hk2, hij]
        · by_cases hkl : k = l
          · simp [hl1, hl2, hkl, Ne.symm hl1, Ne.symm hl2]
          · simp [hk1, hk2, hl1, hl2, hkl, Ne.symm hk1, Ne.symm hk2, Ne.symm hkl]

private theorem rot_mem {i j : Fin N} (hij : i ≠ j) (θ : ℝ) :
    rot (𝕜 := 𝕜) i j θ ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := rot_conj (𝕜 := 𝕜) hij θ (fun _ => 1)
  simp only [sub_self, zero_mul, neg_zero, zero_smul, add_zero, RCLike.ofReal_one,
    Matrix.diagonal_one, Matrix.mul_one] at h
  exact h

end Rotation

/-! ### Derivatives of invariant functions at diagonal matrices -/

section Derivatives

variable {N : ℕ} {Φ : Herm 𝕜 N → ℝ}

private theorem fderiv_diag {k : WithTop ℕ∞} (h : ContDiff ℝ k Φ) (hk : 1 ≤ k)
    (x v : Fin N → ℝ) :
    fderiv ℝ Φ (Herm.diag x) (Herm.diag v) = fderiv ℝ (fun y => Φ (Herm.diag y)) x v := by
  have e := invariant_iteratedFDeriv_comp_diag_apply h (j := 1) (by simpa using hk) x
    (fun _ => v)
  simpa [iteratedFDeriv_one_apply] using e.symm

private theorem fderiv2_diag {k : WithTop ℕ∞} (h : ContDiff ℝ k Φ) (hk : 2 ≤ k)
    (x u v : Fin N → ℝ) :
    fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (Herm.diag u) (Herm.diag v) =
      fderiv ℝ (fderiv ℝ (fun y => Φ (Herm.diag y))) x u v := by
  have e := invariant_iteratedFDeriv_comp_diag_apply h (j := 2) (by simpa using hk) x ![u, v]
  simp only [iteratedFDeriv_two_apply] at e
  simpa using e.symm

private theorem pderiv_pderiv_eq {φ : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (i : Fin N) :
    pderiv i (pderiv i φ) x = fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) := by
  unfold pderiv
  rw [fderiv_clm_apply hφ (differentiableAt_const _)]
  simp

private theorem fderiv_apply_self (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    fderiv ℝ φ x x = ∑ i, x i * pderiv i φ x := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℝ) : Fin N → ℝ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [show fderiv ℝ φ x x = fderiv ℝ φ x (∑ i, x i • Pi.single i 1) from
    congrArg (fderiv ℝ φ x) hx]
  simp [map_sum, pderiv]

/-- Step 1 of Lemma 15.2: `∂_ZΦ(diag x) = 0` for `Z = E_ij w + E_ji w̄`, `i ≠ j`. -/
private theorem fderiv_offH_eq_zero (hΦ : Herm.IsInvariant Φ) {k : WithTop ℕ∞}
    (h : ContDiff ℝ k Φ) (hk : 1 ≤ k) (x : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) (w : 𝕜) :
    fderiv ℝ Φ (Herm.diag x) (offH i j w) = 0 := by
  set d : Fin N → 𝕜 := fun l => if l = j then -1 else 1
  have hd : ∀ l, d l * star (d l) = 1 := fun l => by by_cases hl : l = j <;> simp [d, hl]
  have e := iteratedFDeriv_conj hΦ h (j := 1) (by simpa using hk) (diagonal_mem_unitaryGroup hd)
    (Herm.diag x) (fun _ => offH i j w)
  rw [conj_diagonal_diag hd, conj_diagonal_offH hij] at e
  simp only [d, hij, ite_true, ite_false, one_mul, star_neg, star_one, mul_neg, mul_one,
    offH_neg, iteratedFDeriv_one_apply, map_neg] at e
  linarith

/-- Step 3 of Lemma 15.2: `∂²_ZΦ(diag x)` is the same for all `Z = E_ij u + E_ji ū` with
`|u| = 1`. -/
private theorem fderiv2_offH_unit (hΦ : Herm.IsInvariant Φ) (h2 : ContDiff ℝ 2 Φ)
    (x : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) {u : 𝕜} (hu : ‖u‖ = 1) :
    fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (offH i j u) (offH i j u) =
      fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (offH i j 1) (offH i j 1) := by
  set d : Fin N → 𝕜 := fun l => if l = i then u else 1
  have hd : ∀ l, d l * star (d l) = 1 := fun l => by
    by_cases hl : l = i
    · simp only [d, hl, ite_true, RCLike.star_def, RCLike.mul_conj, hu]
      simp
    · simp [d, hl]
  have e := iteratedFDeriv_conj hΦ h2 (j := 2) (by norm_num) (diagonal_mem_unitaryGroup hd)
    (Herm.diag x) (fun _ => offH i j 1)
  rw [conj_diagonal_diag hd, conj_diagonal_offH hij] at e
  simp only [d, hij.symm, ite_true, ite_false, mul_one, star_one, iteratedFDeriv_two_apply] at e
  exact e

private theorem clm2_smul_smul (L : Herm 𝕜 N →L[ℝ] Herm 𝕜 N →L[ℝ] ℝ) (r : ℝ) (Z : Herm 𝕜 N) :
    L (r • Z) (r • Z) = r ^ 2 * L Z Z := by
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

private theorem offH_zero (i j : Fin N) : offH (𝕜 := 𝕜) i j 0 = 0 := by
  have h := offH_ofReal_mul (𝕜 := 𝕜) i j 0 1
  simpa using h

/-- `∂²_ZΦ(diag x) = |w|² ∂²_{Z₁}Φ(diag x)` for `Z = E_ij w + E_ji w̄`, `Z₁ = E_ij + E_ji`. -/
private theorem fderiv2_offH (hΦ : Herm.IsInvariant Φ) (h2 : ContDiff ℝ 2 Φ)
    (x : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) (w : 𝕜) :
    fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (offH i j w) (offH i j w) =
      ‖w‖ ^ 2 * fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (offH i j 1) (offH i j 1) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [offH_zero]
  · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    set u : 𝕜 := ((‖w‖⁻¹ : ℝ) : 𝕜) * w
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_mul, RCLike.norm_ofReal, abs_inv, abs_norm]
      exact inv_mul_cancel₀ hn
    have hwu : w = ((‖w‖ : ℝ) : 𝕜) * u := by
      simp only [u, ← mul_assoc, ← RCLike.ofReal_mul, mul_inv_cancel₀ hn, RCLike.ofReal_one,
        one_mul]
    conv_lhs => rw [hwu, offH_ofReal_mul, clm2_smul_smul, fderiv2_offH_unit hΦ h2 x hij hu]

/-- Step 2 of Lemma 15.2: for `x_i ≠ x_j`, `∂²_{Z₁}Φ(diag x) = 2 (∂_iφ - ∂_jφ)(x) / (x_i - x_j)`
with `Z₁ = E_ij + E_ji`, from `Φ(R_θ diag(x) R_θ*) = Φ(diag x)` and (15.3). -/
private theorem fderiv2_offH_one (hΦ : Herm.IsInvariant Φ) (h2 : ContDiff ℝ 2 Φ)
    {x : Fin N → ℝ} {i j : Fin N} (hij : i ≠ j) (hx : x i ≠ x j) :
    fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (offH i j 1) (offH i j 1) =
      2 * (pderiv i (fun y => Φ (Herm.diag y)) x - pderiv j (fun y => Φ (Herm.diag y)) x) /
        (x i - x j) := by
  set D : Herm 𝕜 N := Herm.diag x
  set A : Herm 𝕜 N := Herm.diag (Pi.single i 1 - Pi.single j 1)
  set B : Herm 𝕜 N := offH i j 1
  set ς : ℝ := x j - x i with hς
  set c : ℝ → Herm 𝕜 N := fun θ => D + ((ς * sin θ ^ 2) • A + (-ς * (sin θ * cos θ)) • B)
  set c' : ℝ → Herm 𝕜 N := fun θ =>
    (ς * (2 * sin θ * cos θ)) • A + (-ς * (cos θ * cos θ - sin θ * sin θ)) • B
  have hc_eq : ∀ θ, c θ = D.conj (rot i j θ) := by
    intro θ
    refine toMatrix_inj ?_
    rw [toMatrix_conj, toMatrix_diag, rot_conj hij]
    simp only [c, toMatrix_add', toMatrix_smul', toMatrix_diag, toMatrix_offH, D, A, B]
    rw [show -ς * (sin θ * cos θ) = -(x j - x i) * sin θ * cos θ by ring, add_assoc]
  have hconst : ∀ θ, Φ (c θ) = Φ D := fun θ => by
    rw [hc_eq]
    exact hΦ _ (rot_mem hij θ) D
  have hdiff : Differentiable ℝ Φ := h2.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (fderiv ℝ Φ) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc : ∀ θ, HasDerivAt c (c' θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ => ς * sin θ ^ 2) (ς * (2 * sin θ * cos θ)) θ := by
      convert ((hasDerivAt_sin θ).pow 2).const_mul ς using 1
      simp
    have h3 : HasDerivAt (fun θ => -ς * (sin θ * cos θ))
        (-ς * (cos θ * cos θ - sin θ * sin θ)) θ := by
      convert ((hasDerivAt_sin θ).mul (hasDerivAt_cos θ)).const_mul (-ς) using 1
      ring
    exact ((h1.smul_const A).add (h3.smul_const B)).const_add D
  have hfirst : ∀ θ, fderiv ℝ Φ (c θ) (c' θ) = 0 := by
    intro θ
    have hd := (hdiff (c θ)).hasFDerivAt.comp_hasDerivAt θ (hc θ)
    have hk : (Φ ∘ c) = fun _ => Φ D := funext hconst
    rw [hk] at hd
    exact hd.unique (hasDerivAt_const θ _)
  have hc'0 : HasDerivAt c' ((2 * ς) • A + (0 : ℝ) • B) 0 := by
    have h1 : HasDerivAt (fun θ => ς * (2 * sin θ * cos θ)) (2 * ς) 0 := by
      convert (((hasDerivAt_sin 0).const_mul 2).mul (hasDerivAt_cos 0)).const_mul ς using 1
      simp
      ring
    have h3 : HasDerivAt (fun θ => -ς * (cos θ * cos θ - sin θ * sin θ)) 0 0 := by
      convert (((hasDerivAt_cos 0).mul (hasDerivAt_cos 0)).sub
        ((hasDerivAt_sin 0).mul (hasDerivAt_sin 0))).const_mul (-ς) using 1
      simp
    exact (h1.smul_const A).add (h3.smul_const B)
  have hc0 : c 0 = D := by simp [c]
  have hc'0v : c' 0 = (-ς) • B := by simp [c']
  have hL : HasDerivAt (fun θ => fderiv ℝ Φ (c θ)) (fderiv ℝ (fderiv ℝ Φ) (c 0) (c' 0)) 0 :=
    (hdiff2 (c 0)).hasFDerivAt.comp_hasDerivAt 0 (hc 0)
  have hh := hL.clm_apply hc'0
  have hz : (fun θ => fderiv ℝ Φ (c θ) (c' θ)) = fun _ => 0 := funext hfirst
  rw [hz] at hh
  have key := hh.unique (hasDerivAt_const 0 0)
  rw [hc0, hc'0v] at key
  have hA : fderiv ℝ Φ D A =
      pderiv i (fun y => Φ (Herm.diag y)) x - pderiv j (fun y => Φ (Herm.diag y)) x := by
    rw [fderiv_diag h2 (by norm_num), map_sub]
    rfl
  simp only [map_smul, map_add, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, zero_mul,
    add_zero, hA] at key
  have hς0 : ς ≠ 0 := by
    rw [hς]
    exact sub_ne_zero.mpr (Ne.symm hx)
  have hxs : x i - x j = -ς := by rw [hς]; ring
  have hred : ς * (ς * fderiv ℝ (fderiv ℝ Φ) D B B + 2 * (pderiv i (fun y => Φ (Herm.diag y)) x -
      pderiv j (fun y => Φ (Herm.diag y)) x)) = 0 := by linear_combination key
  have hred' := (mul_eq_zero.mp hred).resolve_left hς0
  rw [hxs, eq_div_iff (neg_ne_zero.mpr hς0)]
  linear_combination -hred'

end Derivatives

/-! ### Lemma 15.2 -/

section Givens

variable {N : ℕ}

private theorem inner_diag (v : Fin N → ℝ) (u : Herm 𝕜 N) :
    inner ℝ (Herm.diag (𝕜 := 𝕜) v) u = ∑ a, v a * RCLike.re (u.toMatrix a a) := by
  rw [Herm.inner_eq_trace, toMatrix_diag]
  simp [Matrix.trace, Matrix.diagonal_mul, map_sum]

private theorem norm_sq_diag (v : Fin N → ℝ) : ‖Herm.diag (𝕜 := 𝕜) v‖ ^ 2 = ∑ a, v a ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_diag, toMatrix_diag]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [sq]

/-- `∑_{i ≠ j} (a_i - a_j)/(x_i - x_j) = 2 ∑_i a_i ∑_{j ≠ i} (x_i - x_j)⁻¹`. -/
private theorem sum_pairs (a x : Fin N → ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else (a i - a j) / (x i - x j)) =
      2 * ∑ i, a i * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ := by
  have herase : ∀ (g : Fin N → Fin N → ℝ) (i : Fin N),
      ∑ j, (if i = j then 0 else g i j) = ∑ j ∈ Finset.univ.erase i, g i j := by
    intro g i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [ite_true, zero_add]
    exact Finset.sum_congr rfl fun j hj => by simp [(Finset.ne_of_mem_erase hj).symm]
  have hsplit : ∀ i j, (if i = j then (0 : ℝ) else (a i - a j) / (x i - x j)) =
      (if i = j then 0 else a i * (x i - x j)⁻¹) + (if j = i then 0 else a j * (x j - x i)⁻¹) := by
    intro i j
    by_cases h : i = j
    · simp [h]
    · simp only [h, Ne.symm h, ite_false]
      rw [show x j - x i = -(x i - x j) by ring, inv_neg]
      ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j = i then (0 : ℝ) else a j * (x j - x i)⁻¹)]
  simp_rw [herase (fun i j => a i * (x i - x j)⁻¹), ← Finset.mul_sum]
  ring

/-- Step 4 of Lemma 15.2: `Δ_𝓗Φ(diag x) = Δφ(x) + β ∑_i ∂_iφ(x) ∑_{j ≠ i} (x_i - x_j)⁻¹`. -/
private theorem laplacian_diag {Φ : Herm 𝕜 N → ℝ} (hΦ : Herm.IsInvariant Φ)
    (h2 : ContDiff ℝ 2 Φ) {x : Fin N → ℝ} (hx : Function.Injective x) :
    Laplacian.laplacian Φ (Herm.diag x) =
      ∑ i, pderiv i (pderiv i (fun y => Φ (Herm.diag y))) x +
        betaF 𝕜 * ∑ i, pderiv i (fun y => Φ (Herm.diag y)) x *
          ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ := by
  set φ : (Fin N → ℝ) → ℝ := fun y => Φ (Herm.diag y)
  have hφ : ContDiff ℝ 2 φ := h2.comp (diagCLM (𝕜 := 𝕜)).contDiff
  have hφ' : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdiag : ∀ a, fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (frame (Sum.inl a)) (frame (Sum.inl a)) =
      pderiv a (pderiv a φ) x := by
    intro a
    simp only [frame]
    rw [fderiv2_diag h2 le_rfl, pderiv_pderiv_eq (hφ' x)]
  have hoff : ∀ i j, ∑ k, fderiv ℝ (fderiv ℝ Φ) (Herm.diag x) (frame (Sum.inr (i, j, k)))
      (frame (Sum.inr (i, j, k))) =
      betaF 𝕜 / 2 * (if i = j then 0 else (pderiv i φ x - pderiv j φ x) / (x i - x j)) := by
    intro i j
    by_cases hij : i = j
    · simp [frame, hij]
    · have hx' : x i ≠ x j := fun h => hij (hx h)
      simp only [frame, hij, ite_false, clm2_smul_smul]
      rw [betaF_eq_sum_wk, Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [fderiv2_offH hΦ h2 x hij, fderiv2_offH_one hΦ h2 hij hx']
      ring
  rw [laplacian_eq_sum_frame frame frame_parseval, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, hoff, hdiag, ← Finset.mul_sum, sum_pairs]
  ring

/-- Lemma 15.2, last sentence: for every `x ∈ ℝ^N` and every invariant `Φ ∈ C¹(𝓗)`, with
`φ = Φ ∘ diag`: `∂_TΦ(diag x) = 0` for every `T ∈ 𝓗` with zero diagonal (in particular for the
off-diagonal elements of the basis `𝔅`), `∇Φ(diag x) = ∑_i ∂_iφ(x) E_ii = diag(∇φ(x))`,
`|∇Φ(diag x)| = |∇φ(x)|` and `⟨diag x, ∇Φ(diag x)⟩ = x · ∇φ(x)`. -/
theorem gradient_diag {N : ℕ} {Φ : Herm 𝕜 N → ℝ} (hΦ : Herm.IsInvariant Φ)
    (h1 : ContDiff ℝ 1 Φ) (x : Fin N → ℝ) :
    (∀ T : Herm 𝕜 N, (∀ i, T.toMatrix i i = 0) → fderiv ℝ Φ (Herm.diag x) T = 0) ∧
      gradient Φ (Herm.diag x) = Herm.diag (fun i => pderiv i (fun y => Φ (Herm.diag y)) x) ∧
      ‖gradient Φ (Herm.diag x)‖ =
        Real.sqrt (∑ i, pderiv i (fun y => Φ (Herm.diag y)) x ^ 2) ∧
      inner ℝ (Herm.diag x) (gradient Φ (Herm.diag x)) =
        ∑ i, x i * pderiv i (fun y => Φ (Herm.diag y)) x := by
  set φ : (Fin N → ℝ) → ℝ := fun y => Φ (Herm.diag y)
  have hin : ∀ T, inner ℝ T (gradient Φ (Herm.diag x)) = fderiv ℝ Φ (Herm.diag x) T := fun T => by
    rw [real_inner_comm, inner_gradient_left]
  have hgrad : gradient Φ (Herm.diag x) = Herm.diag (fun i => pderiv i φ x) := by
    conv_lhs => rw [← frame_parseval (gradient Φ (Herm.diag x))]
    rw [Fintype.sum_sum_type]
    have hz : ∀ q : Fin N × Fin N × Fin 2,
        inner ℝ (frame (Sum.inr q)) (gradient Φ (Herm.diag x)) • frame (𝕜 := 𝕜) (Sum.inr q) =
          0 := by
      rintro ⟨i, j, k⟩
      by_cases hij : i = j
      · simp [frame, hij]
      · simp only [frame, hij, ite_false, hin, map_smul,
          fderiv_offH_eq_zero hΦ h1 le_rfl x hij, smul_zero, zero_smul]
    simp only [hz, Finset.sum_const_zero, add_zero]
    have hd : ∀ a, inner ℝ (frame (Sum.inl a)) (gradient Φ (Herm.diag x)) • frame (Sum.inl a) =
        diagCLM (𝕜 := 𝕜) (pderiv a φ x • Pi.single a 1) := fun a => by
      rw [map_smul, diagCLM_apply, hin, frame, fderiv_diag h1 le_rfl x _]
      rfl
    have hP : (fun i => pderiv i φ x) = ∑ a, pderiv a φ x • (Pi.single a 1 : Fin N → ℝ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hP, show Herm.diag (∑ a, pderiv a φ x • (Pi.single a 1 : Fin N → ℝ)) =
      diagCLM (𝕜 := 𝕜) (∑ a, pderiv a φ x • (Pi.single a 1 : Fin N → ℝ)) from rfl, map_sum]
    exact Finset.sum_congr rfl fun a _ => hd a
  refine ⟨fun T hT => ?_, hgrad, ?_, ?_⟩
  · rw [← hin, hgrad, real_inner_comm, inner_diag]
    simp [hT]
  · rw [hgrad, ← Real.sqrt_sq (norm_nonneg _), norm_sq_diag]
  · rw [hin, fderiv_diag h1 le_rfl, fderiv_apply_self]

/-- Lemma 15.2 (15.2): `(AΦ)(diag x) = (Lφ)(x)` for invariant `C²` `Φ`, `φ = Φ ∘ diag`, at
points with pairwise distinct coordinates. -/
theorem ouGen_diag_eq_dysonGen {N : ℕ} {Φ : Herm 𝕜 N → ℝ} (hΦ : Herm.IsInvariant Φ)
    (h2 : ContDiff ℝ 2 Φ) {x : Fin N → ℝ} (hx : Function.Injective x) :
    ouGen (gaussVar 𝕜 N) Φ (Herm.diag x) =
      dysonGen (betaF 𝕜) N (fun y => Φ (Herm.diag y)) x := by
  set φ : (Fin N → ℝ) → ℝ := fun y => Φ (Herm.diag y)
  have hβ : betaF 𝕜 ≠ 0 := by
    rw [betaF_eq_sum_wk, Fin.sum_univ_two]
    simp only [wk, Matrix.cons_val_zero, norm_one, one_pow]
    positivity
  have hin : inner ℝ (Herm.diag x) (gradient Φ (Herm.diag x)) = ∑ i, x i * pderiv i φ x :=
    (gradient_diag hΦ (h2.of_le (by norm_num)) x).2.2.2
  have hcoef : 2 / (betaF 𝕜 * N) / 2 * betaF 𝕜 = (N : ℝ)⁻¹ := by
    rw [show 2 / (betaF 𝕜 * N) / 2 * betaF 𝕜 = betaF 𝕜 * (betaF 𝕜)⁻¹ * (N : ℝ)⁻¹ by ring,
      mul_inv_cancel₀ hβ, one_mul]
  have hR : ∑ i, (-x i / 2 + (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) * pderiv i φ x =
      -1 / 2 * ∑ i, x i * pderiv i φ x +
        (N : ℝ)⁻¹ * ∑ i, pderiv i φ x * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [ouGen, laplacian_diag hΦ h2 hx, hin, gaussVar]
  unfold dysonGen
  rw [hR]
  linear_combination (∑ i, pderiv i φ x * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) * hcoef

end Givens

end Rigidity
