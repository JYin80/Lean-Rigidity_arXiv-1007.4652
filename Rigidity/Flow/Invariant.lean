import Rigidity.Flow.GaussEnsemble
import Rigidity.Flow.Herm
import Rigidity.Flow.Mehler

/-!
# Invariant functions on the hermitian matrices, and the eigenvalue flow

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Let `𝓗 = Herm 𝕜 N` and let `Φ : 𝓗 → α` be invariant, that is `Φ(U H U*) = Φ(H)` for every
unitary `U`.  The file contains:
* §12.1: the law `ν_t = λ_* ρ_t` of the eigenvalues of `H_t`;
* Lemma 15.1: `Φ = φ ∘ λ` with `φ = Φ ∘ diag`, and the Mehler semigroup `T_u` maps invariant
  `[0, ∞]`-valued measurable functions to invariant functions;
* Lemma 15.1 (b): if `Φ ∈ C^k(𝓗)` and `j ≤ k`, then `H ↦ ‖D^jΦ(H)‖` is invariant, and the
  derivatives of `φ = Φ ∘ diag` are the entries `D^jΦ(diag x)[diag v₁, …, diag v_j]`.  These are
  bounded by the operator norm of `D^jΦ(diag x)`: entrywise, for the gradient, and in the operator
  form on `ℝ^N` with the supremum norm, which carries the factor `(√N)^j`, the norm of
  `diag : (ℝ^N, ‖·‖_∞) → 𝓗`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The law of `λ(H_t)` for `H_0 ∼ ρ` (§12.1): `ν_t = λ_* ρ_t`. -/
noncomputable def eigFlow {N : ℕ} (ρ : Measure (Herm 𝕜 N)) (t : ℝ) : Measure (Fin N → ℝ) :=
  (ouLaw (gaussVar 𝕜 N) ρ t).map eigVec

/-- Lemma 15.1: an invariant `Φ` is `φ ∘ λ` with `φ = Φ ∘ diag`. -/
theorem Herm.IsInvariant.eq_comp_eigVec {N : ℕ} {α : Type*} {Φ : Herm 𝕜 N → α}
    (hΦ : Herm.IsInvariant Φ) (H : Herm 𝕜 N) : Φ H = Φ (Herm.diag (eigVec H)) := by
  obtain ⟨U, hU, hH⟩ := exists_unitary_eq_conj_diag H
  exact (congrArg Φ hH).trans (hΦ U hU _)

/-! ### 1. The conjugation `𝒪_U` as a linear isometry of `𝓗` and `diag` as a linear map -/

section Conj

variable {N : ℕ}

private theorem mk'_of_le {i j : Fin N} (h : i ≤ j) : Pair.mk' i j = ⟨(i, j), h⟩ := by
  simp [Pair.mk', h]

private theorem mk'_of_gt {i j : Fin N} (h : j < i) : Pair.mk' i j = ⟨(j, i), h.le⟩ := by
  simp [Pair.mk', not_le.mpr h]

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

private theorem toMatrix_conj (U : Matrix (Fin N) (Fin N) 𝕜) (H : Herm 𝕜 N) :
    (H.conj U).toMatrix = U * H.toMatrix * star U := by
  unfold Herm.conj Herm.ofMatrix
  rw [Herm.toMatrix_ofPair]
  exact toMatrix_upper (Matrix.isHermitian_mul_mul_conjTranspose U H.isHermitian)

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

/-- `⟨U H U*, T⟩ = ⟨H, U* T U⟩`. -/
private theorem inner_conj (U : Matrix (Fin N) (Fin N) 𝕜) (H T : Herm 𝕜 N) :
    inner ℝ (H.conj U) T = inner ℝ H (T.conj (star U)) := by
  rw [Herm.inner_eq_trace, Herm.inner_eq_trace, toMatrix_conj, toMatrix_conj, star_star]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm U]
  simp only [Matrix.mul_assoc]

/-- `𝒪_U` preserves the norm of `𝓗`, since `|H| = |λ(H)|` and `λ(U H U*) = λ(H)`. -/
private theorem norm_conj {U : Matrix (Fin N) (Fin N) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) (H : Herm 𝕜 N) : ‖H.conj U‖ = ‖H‖ := by
  have h2 : ‖H.conj U‖ ^ 2 = ‖H‖ ^ 2 := by
    rw [← sum_sq_eigVec, ← sum_sq_eigVec, eigVec_conj hU]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `𝒪_U : H ↦ U H U*` as a linear isometric equivalence of `𝓗` (§15). -/
private noncomputable def conjIso {U : Matrix (Fin N) (Fin N) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) : Herm 𝕜 N ≃ₗᵢ[ℝ] Herm 𝕜 N :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := Herm.conj U
      map_add' := fun X Y => ext_inner_right ℝ fun T => by
        rw [inner_conj, inner_add_left, inner_add_left, inner_conj, inner_conj]
      map_smul' := fun c X => ext_inner_right ℝ fun T => by
        rw [inner_conj, real_inner_smul_left, RingHom.id_apply, real_inner_smul_left, inner_conj]
      norm_map' := norm_conj hU } rfl

/-- `x ↦ diag x` as a real-linear map `ℝ^N → 𝓗`. -/
private noncomputable def diagL : (Fin N → ℝ) →ₗ[ℝ] Herm 𝕜 N where
  toFun := Herm.diag
  map_add' x y := ext_inner_right ℝ fun T => by
    rw [inner_add_left, Herm.inner_eq_trace, Herm.inner_eq_trace, Herm.inner_eq_trace,
      toMatrix_diag, toMatrix_diag, toMatrix_diag, ← map_add, ← Matrix.trace_add,
      ← Matrix.add_mul]
    congr 3
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c x := ext_inner_right ℝ fun T => by
    rw [real_inner_smul_left, RingHom.id_apply, Herm.inner_eq_trace, Herm.inner_eq_trace,
      toMatrix_diag, toMatrix_diag]
    have e : Matrix.diagonal (fun k => (((c • x) k : ℝ) : 𝕜)) =
        c • Matrix.diagonal (fun k => ((x k : ℝ) : 𝕜)) := by
      ext i j
      by_cases h : i = j <;> simp [h, RCLike.real_smul_eq_coe_mul]
    rw [e, Matrix.smul_mul, Matrix.trace_smul, RCLike.smul_re]

/-- `diag : ℝ^N → 𝓗` as a continuous linear map. -/
private noncomputable def diagCLM : (Fin N → ℝ) →L[ℝ] Herm 𝕜 N :=
  LinearMap.toContinuousLinearMap diagL

/-- §12.1: `|diag x|² = ∑ x_i²`. -/
private theorem norm_sq_diag (x : Fin N → ℝ) : ‖Herm.diag (𝕜 := 𝕜) x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [Herm.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toMatrix_diag, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- `‖diag x‖ ≤ √N ‖x‖_∞`. -/
private theorem norm_diag_le (x : Fin N → ℝ) : ‖Herm.diag (𝕜 := 𝕜) x‖ ≤ Real.sqrt N * ‖x‖ := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [norm_sq_diag, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin N, ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          rw [← sq_abs (x i)]
          exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm x i) 2
    _ = N * ‖x‖ ^ 2 := by simp

end Conj

/-- Lemma 15.1: `T_u` maps invariant functions to invariant functions. -/
theorem Herm.IsInvariant.mehlerL {N : ℕ} {Φ : Herm 𝕜 N → ℝ≥0∞} (hΦ : Herm.IsInvariant Φ)
    (hm : Measurable Φ) (u : ℝ) : Herm.IsInvariant (mehlerL (gaussVar 𝕜 N) u Φ) := by
  intro U hU H
  have h := mehlerL_comp_isometry (gaussVar 𝕜 N) u (conjIso hU) hm
  have hΦU : Φ ∘ conjIso hU = Φ := funext fun H => hΦ U hU H
  rw [hΦU] at h
  exact (congrFun h H).symm

/-! ### 2. Lemma 15.1 (b): derivatives of invariant functions -/

section Derivatives

variable {N : ℕ}

/-- Lemma 15.1 (b): for an invariant `Φ`, `H ↦ ‖D^jΦ(H)‖` is invariant. -/
theorem invariant_norm_iteratedFDeriv {Φ : Herm 𝕜 N → ℝ} (hΦ : Herm.IsInvariant Φ) (j : ℕ) :
    Herm.IsInvariant fun H => ‖iteratedFDeriv ℝ j Φ H‖ := by
  intro U hU H
  have hΦU : Φ ∘ conjIso hU = Φ := funext fun H => hΦ U hU H
  have h := (conjIso hU).norm_iteratedFDeriv_comp_right Φ H j
  rw [hΦU] at h
  exact h.symm

/-- Lemma 15.1 (b): the derivatives of `φ = Φ ∘ diag` are the entries of those of `Φ`,
`D^jφ(x)[v₁, …, v_j] = D^jΦ(diag x)[diag v₁, …, diag v_j]`, for `Φ ∈ C^k(𝓗)` and `j ≤ k`. -/
theorem invariant_iteratedFDeriv_comp_diag_apply {Φ : Herm 𝕜 N → ℝ} {k : WithTop ℕ∞}
    (hΦ : ContDiff ℝ k Φ) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ k) (x : Fin N → ℝ)
    (v : Fin j → Fin N → ℝ) :
    iteratedFDeriv ℝ j (fun y : Fin N → ℝ => Φ (Herm.diag y)) x v =
      iteratedFDeriv ℝ j Φ (Herm.diag x) fun l => Herm.diag (v l) := by
  have h : iteratedFDeriv ℝ j (fun y : Fin N → ℝ => Φ (Herm.diag y)) x =
      (iteratedFDeriv ℝ j Φ (Herm.diag x)).compContinuousLinearMap
        fun _ => (diagCLM (𝕜 := 𝕜) (N := N)) :=
    (diagCLM (𝕜 := 𝕜) (N := N)).iteratedFDeriv_comp_right hΦ x hj
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- Lemma 15.1 (b), gradient: for `Φ ∈ C^k(𝓗)` with `1 ≤ k` and `φ = Φ ∘ diag`,
`|∇φ(x)| ≤ ‖DΦ(diag x)‖`, where `|∇φ(x)|² = ∑ᵢ (∂ᵢφ(x))²`.  For `j = 1` the operator norm of
`DΦ(diag x)` is `|∇Φ(diag x)|`. -/
theorem invariant_norm_gradient_comp_diag_le {Φ : Herm 𝕜 N → ℝ} {k : WithTop ℕ∞}
    (hΦ : ContDiff ℝ k Φ) (hk : (1 : WithTop ℕ∞) ≤ k) (x : Fin N → ℝ) :
    Real.sqrt (∑ i, (fderiv ℝ (fun y : Fin N → ℝ => Φ (Herm.diag y)) x
        (Pi.single i (1 : ℝ))) ^ 2) ≤ ‖fderiv ℝ Φ (Herm.diag x)‖ := by
  set w : Fin N → ℝ := fun i =>
    fderiv ℝ (fun y : Fin N → ℝ => Φ (Herm.diag y)) x (Pi.single i (1 : ℝ)) with hw
  have hj : ((1 : ℕ) : WithTop ℕ∞) ≤ k := by simpa using hk
  have hsum : ∑ i, w i • (Pi.single i (1 : ℝ) : Fin N → ℝ) = w := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : fderiv ℝ (fun y : Fin N → ℝ => Φ (Herm.diag y)) x w = ∑ i, w i ^ 2 := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, sq]
  have h2 : fderiv ℝ (fun y : Fin N → ℝ => Φ (Herm.diag y)) x w =
      fderiv ℝ Φ (Herm.diag x) (Herm.diag w) := by
    have := invariant_iteratedFDeriv_comp_diag_apply hΦ hj x (fun _ : Fin 1 => w)
    simpa [iteratedFDeriv_one_apply] using this
  have hn : ‖Herm.diag (𝕜 := 𝕜) w‖ = Real.sqrt (∑ i, w i ^ 2) := by
    rw [← norm_sq_diag (𝕜 := 𝕜), Real.sqrt_sq (norm_nonneg _)]
  have h3 : ∑ i, w i ^ 2 ≤ ‖fderiv ℝ Φ (Herm.diag x)‖ * Real.sqrt (∑ i, w i ^ 2) :=
    calc ∑ i, w i ^ 2 = fderiv ℝ Φ (Herm.diag x) (Herm.diag w) := h1.symm.trans h2
      _ ≤ ‖fderiv ℝ Φ (Herm.diag x)‖ * ‖Herm.diag (𝕜 := 𝕜) w‖ :=
          (le_abs_self _).trans ((fderiv ℝ Φ (Herm.diag x)).le_opNorm _)
      _ = _ := by rw [hn]
  have hS : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases (Real.sqrt_nonneg (∑ i, w i ^ 2)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact norm_nonneg _
  · refine le_of_mul_le_mul_right ?_ hpos
    calc Real.sqrt (∑ i, w i ^ 2) * Real.sqrt (∑ i, w i ^ 2) = ∑ i, w i ^ 2 :=
          Real.mul_self_sqrt hS
      _ ≤ _ := h3

/-- Lemma 15.1 (b), operator form: for `Φ ∈ C^k(𝓗)` and `j ≤ k`, with `φ = Φ ∘ diag` and the
supremum norm on `ℝ^N`, `‖D^jφ(x)‖ ≤ (√N)^j ‖D^jΦ(diag x)‖`. -/
theorem norm_iteratedFDeriv_comp_diag_le {Φ : Herm 𝕜 N → ℝ} {k : WithTop ℕ∞}
    (hΦ : ContDiff ℝ k Φ) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ k) (x : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : Fin N → ℝ => Φ (Herm.diag y)) x‖ ≤
      Real.sqrt N ^ j * ‖iteratedFDeriv ℝ j Φ (Herm.diag x)‖ := by
  have h : iteratedFDeriv ℝ j (fun y : Fin N → ℝ => Φ (Herm.diag y)) x =
      (iteratedFDeriv ℝ j Φ (Herm.diag x)).compContinuousLinearMap
        fun _ => (diagCLM (𝕜 := 𝕜) (N := N)) :=
    (diagCLM (𝕜 := 𝕜) (N := N)).iteratedFDeriv_comp_right hΦ x hj
  rw [h]
  have hd : ‖(diagCLM (𝕜 := 𝕜) (N := N))‖ ≤ Real.sqrt N :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => norm_diag_le y
  refine ((iteratedFDeriv ℝ j Φ (Herm.diag x)).norm_compContinuousLinearMap_le _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hd j) (norm_nonneg _)

end Derivatives

end Rigidity
