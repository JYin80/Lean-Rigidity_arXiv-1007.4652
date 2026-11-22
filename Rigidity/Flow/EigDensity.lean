module

public import Rigidity.Flow.Chamber
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.Givens
public import Rigidity.Flow.Herm
public import Rigidity.Flow.Invariant
public import Rigidity.Flow.MehlerSmooth

@[expose] public section

/-!
# Smooth symmetric versions of the eigenvalue densities along the flow (Proposition 15.4)

Statement numbers refer to the blueprint NP v1.1; where the original paper (Erdős–Yau–Yin,
arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Let `H₀ ∼ ρ` have finite moments of every order, let `s > 0`, and let `ν_t = λ_* ρ_t` be the law of
the ordered eigenvalues along the Ornstein–Uhlenbeck flow, with `μ = λ_* 𝐆`.  Proposition 15.4
states that `ν_s ≪ μ` and that `f_t(x) = Φ_t(diag x)`, with `Φ_t = T_{t-s} Φ_s` and
`Φ_s = (dν_s/dμ) ∘ λ`, is a smooth, positive and symmetric version of `dν_t/dμ` for `t > s` which
solves `∂_t f_t = L f_t` off the walls and satisfies the bounds of 15.4 (iv).

The proof follows the proof of Proposition 15.4.  With `ρ' = Φ_s 𝐆`, a probability measure with
the same eigenvalue law as `ρ_s`, `Φ_t` is the density `Ψ'(t - s, ·)` of `ρ'_{t-s}` with respect to
`𝐆` (Lemma 14.1 (iv)), so that Lemma 14.2 applies to `ρ'`; `Φ_t` is invariant (Lemma 15.1), and
the equation off the walls is Lemma 15.2.  For the domination in 15.4 (iv), the bound of
Lemma 14.2 (iii) is transported to `ℝ^N` through the invariant majorant
`sup_{t ∈ [t₁, t₂]} ∑_{j ≤ 1, k ≤ 2} |D^k ∂_t^j Φ_t|` of the proof, which is continuous because
the joint derivatives of `Ψ'` are continuous.  The derivative norms on `ℝ^N` are operator norms for
the supremum norm, and the weight `(1 + |x|)^m` of 15.4 (iv) is written `(1 + |x|²)^m`; over all
`m ∈ ℕ` the two families of conditions are equivalent.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The conclusions of Proposition 15.4 (ii)–(iv) for a family `f` (`t > s`). -/
structure IsSmoothDensity {N : ℕ} (ρ : Measure (Herm 𝕜 N)) (s : ℝ)
    (f : ℝ → (Fin N → ℝ) → ℝ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin N → ℝ) => f p.1 p.2) (Set.Ioi s ×ˢ Set.univ)
  pos : ∀ t > s, ∀ x, 0 < f t x
  symm : ∀ t > s, ∀ x (σ : Equiv.Perm (Fin N)), f t (x ∘ σ) = f t x
  density : ∀ t > s, eigFlow ρ t = (gbeLaw 𝕜 N).withDensity fun x => ENNReal.ofReal (f t x)
  eqn : ∀ t > s, ∀ x, Function.Injective x →
    HasDerivAt (fun t' => f t' x) (dysonGen (betaF 𝕜) N (f t) x) t
  logBound : ∀ t₁ t₂, s < t₁ → t₁ < t₂ → ∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x,
    |Real.log (f t x)| ≤ C * (1 + ∑ i, x i ^ 2)
  dom : ∀ t₁ t₂, s < t₁ → t₁ < t₂ → ∃ 𝔪 : (Fin N → ℝ) → ℝ,
    (∀ m : ℕ, Integrable (fun x => 𝔪 x * (1 + ∑ i, x i ^ 2) ^ m) (gbeLaw 𝕜 N)) ∧
    ∀ t ∈ Set.Icc t₁ t₂, ∀ x, |f t x| + ‖fderiv ℝ (f t) x‖ + ‖iteratedFDeriv ℝ 2 (f t) x‖ +
      |deriv (fun t' => f t' x) t| + ‖fderiv ℝ (fun y => deriv (fun t' => f t' y) t) x‖ ≤ 𝔪 x
  fisher : ∀ t > s,
    ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i (f t) x ^ 2) / f t x) ∂gbeLaw 𝕜 N < ∞

/-! ### 1. Matrices of elements of `𝓗`, `diag` as a linear map, and permutations -/

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

private theorem continuous_diag : Continuous (Herm.diag : (Fin N → ℝ) → Herm 𝕜 N) :=
  (diagCLM (𝕜 := 𝕜) (N := N)).continuous

/-- §12.1: `|diag x|² = ∑ x_i²`. -/
private theorem norm_sq_diag (x : Fin N → ℝ) : ‖Herm.diag (𝕜 := 𝕜) x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [Herm.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toMatrix_diag, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- Lemma 15.1: `diag(x ∘ σ) = P diag(x) P*` for the permutation matrix `P` of `σ`, which lies in
`U_β(N)`. -/
private theorem diag_comp_perm (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) 𝕜, Herm.diag (𝕜 := 𝕜) (x ∘ σ) = (Herm.diag x).conj U := by
  have hstar : star (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) 𝕜) =
      σ.symm.toPEquiv.toMatrix := by
    ext i j
    simp only [Matrix.star_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, Equiv.symm_apply_eq]
    by_cases h : σ j = i
    · simp [h]
    · simp [h, Ne.symm h]
  refine ⟨(σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) 𝕜), ?_, toMatrix_inj ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, hstar, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
      Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [toMatrix_conj, toMatrix_diag, toMatrix_diag, hstar, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix, Equiv.symm_symm]
    exact (Matrix.submatrix_diagonal_equiv (fun k => ((x k : ℝ) : 𝕜)) σ).symm

end Toolkit

/-! ### 2. Eigenvalue laws and the flow -/

section Laws

variable {N : ℕ}

attribute [local instance] gaussE_isProbabilityMeasure

private theorem measurable_eigVec : Measurable (eigVec : Herm 𝕜 N → Fin N → ℝ) :=
  (continuous_eigVec N).measurable

private theorem gaussVar_nonneg' : 0 ≤ gaussVar 𝕜 N :=
  div_nonneg zero_le_two (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem gaussVar_pos' (hN : 0 < N) : 0 < gaussVar 𝕜 N := by
  have hβ : 0 < betaF 𝕜 := by
    unfold betaF
    exact Nat.cast_pos.2 Module.finrank_pos
  exact div_pos two_pos (mul_pos hβ (Nat.cast_pos.2 hN))

/-- Lemma 15.1 (a): every function of `λ(H)` is invariant. -/
private theorem isInvariant_comp_eigVec {α : Type*} (h : (Fin N → ℝ) → α) :
    Herm.IsInvariant (fun H : Herm 𝕜 N => h (eigVec H)) := fun U hU H => by
  simp only [eigVec_conj hU]

/-- `T_u Φ` is measurable for measurable `Φ`. -/
private theorem measurable_mehlerL' (v u : ℝ) {Φ : Herm 𝕜 N → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (mehlerL v u Φ) := by
  unfold mehlerL
  exact (hΦ.comp (by fun_prop : Measurable fun p : Herm 𝕜 N × Herm 𝕜 N =>
    ouA u • p.1 + Real.sqrt (ouS u) • p.2)).lintegral_prod_right'

private theorem isProbabilityMeasure_ouLaw' (v : ℝ) (ρ : Measure (Herm 𝕜 N))
    [IsProbabilityMeasure ρ] (u : ℝ) : IsProbabilityMeasure (ouLaw v ρ u) := by
  unfold ouLaw
  infer_instance

/-- The image-measure formula (proof of Proposition 15.4 (i)):
`λ_*(Φ 𝐆) = (λ_* 𝐆) h` for `Φ = h ∘ λ`. -/
private theorem map_withDensity_comp_eigVec (G : Measure (Herm 𝕜 N))
    {h : (Fin N → ℝ) → ℝ≥0∞} (hh : Measurable h) :
    (G.withDensity fun H => h (eigVec H)).map eigVec = (G.map eigVec).withDensity h := by
  ext B hB
  rw [Measure.map_apply measurable_eigVec hB, withDensity_apply _ (measurable_eigVec hB),
    withDensity_apply _ hB, setLIntegral_map hB hh measurable_eigVec]

/-- Two initial laws with the same eigenvalue law have the same eigenvalue law along the flow:
`∫ F(λ) dρ_u = ∫ T_u(F ∘ λ) dρ` and `T_u(F ∘ λ)` is invariant (Lemmas 14.1 (v) and 15.1). -/
private theorem map_ouLaw_eq {ρ₁ ρ₂ : Measure (Herm 𝕜 N)} [IsProbabilityMeasure ρ₁]
    [IsProbabilityMeasure ρ₂] (h : ρ₁.map eigVec = ρ₂.map eigVec) (u : ℝ) :
    (ouLaw (gaussVar 𝕜 N) ρ₁ u).map eigVec = (ouLaw (gaussVar 𝕜 N) ρ₂ u).map eigVec := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hFl : Measurable fun H : Herm 𝕜 N => F (eigVec H) := hF.comp measurable_eigVec
  rw [lintegral_map hF measurable_eigVec, lintegral_map hF measurable_eigVec,
    lintegral_ouLaw gaussVar_nonneg' _ hFl, lintegral_ouLaw gaussVar_nonneg' _ hFl]
  set Φ := mehlerL (gaussVar 𝕜 N) u fun H : Herm 𝕜 N => F (eigVec H)
  have hΦm : Measurable Φ := measurable_mehlerL' _ u hFl
  have hΦi : Herm.IsInvariant Φ := Herm.IsInvariant.mehlerL (isInvariant_comp_eigVec F) hFl u
  have key : ∀ ρ : Measure (Herm 𝕜 N),
      ∫⁻ H, Φ H ∂ρ = ∫⁻ x, Φ (Herm.diag x) ∂(ρ.map eigVec) := fun ρ => by
    rw [lintegral_map (f := fun x => Φ (Herm.diag x)) (hΦm.comp continuous_diag.measurable)
      measurable_eigVec]
    exact lintegral_congr fun H => hΦi.eq_comp_eigVec H
  rw [key ρ₁, key ρ₂, h]

/-- Moments transfer between initial laws with the same eigenvalue law (`|λ(H)| = |H|`). -/
private theorem integrable_norm_pow_of_map_eq {ρ₁ ρ₂ : Measure (Herm 𝕜 N)}
    (h : ρ₁.map eigVec = ρ₂.map eigVec) {m : ℕ} (h₁ : Integrable (fun H => ‖H‖ ^ m) ρ₁) :
    Integrable (fun H => ‖H‖ ^ m) ρ₂ := by
  set g : (Fin N → ℝ) → ℝ := fun x => Real.sqrt (∑ i, x i ^ 2) ^ m
  have hg : Continuous g := by fun_prop
  have hgl : (fun H : Herm 𝕜 N => ‖H‖ ^ m) = g ∘ eigVec := by
    funext H
    simp only [g, Function.comp_apply, sum_sq_eigVec, Real.sqrt_sq (norm_nonneg _)]
  rw [hgl] at h₁ ⊢
  rw [← integrable_map_measure hg.aestronglyMeasurable measurable_eigVec.aemeasurable] at h₁ ⊢
  rwa [← h]

/-- Lemma 14.1 (vi): `ρ_u` has finite moments of every order if `ρ` does. -/
private theorem integrable_norm_pow_ouLaw {v : ℝ} (hv : 0 ≤ v) {u : ℝ} (hu : 0 ≤ u)
    (ρ : Measure (Herm 𝕜 N)) [IsProbabilityMeasure ρ]
    (hρ : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ) (m : ℕ) :
    Integrable (fun H => ‖H‖ ^ m) (ouLaw v ρ u) := by
  have h1 : ∫⁻ w, ENNReal.ofReal (‖w‖ ^ (m : ℝ)) ∂ρ < ∞ := by
    simpa only [Real.rpow_natCast] using (hρ m).lintegral_lt_top
  have h2 := mehler_lintegral_norm_rpow_ouLaw_lt_top hv hu (Nat.cast_nonneg m) ρ h1
  simp only [Real.rpow_natCast] at h2
  exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (ae_of_all _ fun H => by positivity)).1 h2.ne

/-- The kernel formula (Lemma 14.E (b)): for `ρ' = φ 𝐆`, `Ψ'(u, y) = T_u φ(y)` for every `y`. -/
private theorem ofReal_ouDensity_withDensity {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u)
    {φ : Herm 𝕜 N → ℝ≥0∞} (hφ : Measurable φ)
    [IsFiniteMeasure ((gaussE (Herm 𝕜 N) v).withDensity φ)] (y : Herm 𝕜 N) :
    ENNReal.ofReal (ouDensity v ((gaussE (Herm 𝕜 N) v).withDensity φ) u y) =
      mehlerL v u φ y := by
  have hc : Continuous fun w : Herm 𝕜 N => mehlerKernel v u y w := by
    unfold mehlerKernel
    fun_prop
  have hint : Integrable (fun w => mehlerKernel v u y w) ((gaussE (Herm 𝕜 N) v).withDensity φ) :=
    Integrable.of_bound hc.aestronglyMeasurable
      (ouS u ^ (-(Module.finrank ℝ (Herm 𝕜 N) : ℝ) / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)))
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_of_pos (mehlerKernel_pos v hu y w)]
        exact mehlerKernel_le hv hu y w)
  rw [mehlerL_eq_lintegral_kernel hv hu hφ, ouDensity,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => (mehlerKernel_pos v hu y w).le),
    lintegral_withDensity_eq_lintegral_mul _ hφ
      (g := fun w => ENNReal.ofReal (mehlerKernel v u y w))
      (ENNReal.measurable_ofReal.comp hc.measurable)]
  rfl

end Laws

/-! ### 3. Slices of functions smooth on `(0, ∞) × E` -/

section Joint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem isOpen_Ioi_prod_univ : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) :=
  isOpen_Ioi.prod isOpen_univ

/-- For `P` smooth on `(0, ∞) × E` and `u > 0`, the `y`-derivatives of `P(u, ·)` are the joint
derivatives of `P` in the directions `(0, e)`. -/
private theorem iteratedFDeriv_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ℝ × E → F} (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) {u : ℝ} (hu : 0 < u) :
    ∀ k (y : E), iteratedFDeriv ℝ k (fun y' => P (u, y')) y =
      (iteratedFDeriv ℝ k P (u, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E)
  | 0, y => by ext m; simp
  | k + 1, y => by
    have hev : iteratedFDeriv ℝ k (fun y' => P (u, y')) = fun y' =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) (iteratedFDeriv ℝ k P (u, y')) :=
      funext fun y' => iteratedFDeriv_slice hP hu k y'
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k P) (u, y) :=
      (hP.contDiffAt (isOpen_Ioi_prod_univ.mem_nhds
        (show (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) from
          ⟨hu, trivial⟩))).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top k))
    have hd' : DifferentiableAt ℝ (fun y' => iteratedFDeriv ℝ k P (u, y')) y :=
      hd.comp y (hasFDerivAt_prodMk_right u y).differentiableAt
    ext m
    rw [iteratedFDeriv_succ_apply_left, hev]
    have h1 : fderiv ℝ (fun y' => (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) (iteratedFDeriv ℝ k P (u, y'))) y =
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)).comp
          (fderiv ℝ (fun y' => iteratedFDeriv ℝ k P (u, y')) y) :=
      ((ContinuousLinearMap.hasFDerivAt _).comp y hd'.hasFDerivAt).fderiv
    have h2 : fderiv ℝ (fun y' => iteratedFDeriv ℝ k P (u, y')) y =
        (fderiv ℝ (iteratedFDeriv ℝ k P) (u, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
      (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right u y)).fderiv
    rw [h1, h2]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_succ_apply_left]
    rfl

/-- `(u, y) ↦ ‖D_y^k P(u, y)‖` is continuous on `(0, ∞) × E` for `P` smooth there. -/
private theorem continuousOn_norm_iteratedFDeriv_slice {P : ℝ × E → ℝ}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) (k : ℕ) :
    ContinuousOn (fun p : ℝ × E => ‖iteratedFDeriv ℝ k (fun y => P (p.1, y)) p.2‖)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k P) (Set.Ioi 0 ×ˢ Set.univ) :=
    ContinuousOn.continuousOn_iteratedFDeriv hP isOpen_Ioi_prod_univ
      (WithTop.coe_le_coe.2 le_top)
  refine (((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp_continuousOn hc).norm).congr
    fun p hp => ?_
  simp only [Function.comp_apply]
  rw [iteratedFDeriv_slice hP hp.1 k p.2]
  rfl

/-- `∂_u P = DP(·)(1, 0)` is smooth on `(0, ∞) × E` for `P` smooth there. -/
private theorem contDiffOn_fderiv_apply {P : ℝ × E → ℝ}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ P p ((1 : ℝ), (0 : E))) (Set.Ioi 0 ×ˢ Set.univ) :=
  (hP.fderiv_of_isOpen isOpen_Ioi_prod_univ (by simp)).clm_apply contDiffOn_const

/-- `∂_u P(u, y) = DP(u, y)(1, 0)` for `u > 0`. -/
private theorem deriv_slice_eq {P : ℝ × E → ℝ}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) {u : ℝ} (hu : 0 < u) (y : E) :
    deriv (fun u' => P (u', y)) u = fderiv ℝ P (u, y) ((1 : ℝ), (0 : E)) := by
  have hd : DifferentiableAt ℝ P (u, y) :=
    (hP.contDiffAt (isOpen_Ioi_prod_univ.mem_nhds
      (show (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) from ⟨hu, trivial⟩))).differentiableAt
      (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u y))).deriv

/-- For `u > 0`, `P(u, ·)` is smooth on `E`. -/
private theorem contDiff_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ℝ × E → F} (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) {u : ℝ} (hu : 0 < u) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => P (u, y) :=
  contDiffOn_univ.1 (hP.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun _ _ => ⟨hu, trivial⟩)

end Joint

/-! ### 4. The family `f_t(x) = Ψ'(t - s, diag x)` for an initial law `ρ'` with invariant flow
densities -/

section Family

variable {N : ℕ}

attribute [local instance] gaussE_isProbabilityMeasure

/-- Proposition 15.4 (ii), smoothness: `(t, x) ↦ Ψ'(t - s, diag x)` is `C^∞` on `(s, ∞) × ℝ^N`. -/
private theorem fam_smooth {ρ' : Measure (Herm 𝕜 N)}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Herm 𝕜 N => ouDensity (gaussVar 𝕜 N) ρ' p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ)) (s : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin N → ℝ) => ouDensity (gaussVar 𝕜 N) ρ' (p.1 - s) (Herm.diag p.2))
      (Set.Ioi s ×ˢ Set.univ) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × (Fin N → ℝ) => (p.1 - s, diagCLM (𝕜 := 𝕜) p.2) :=
    (contDiff_fst.sub contDiff_const).prodMk ((diagCLM (𝕜 := 𝕜)).contDiff.comp contDiff_snd)
  exact hP.comp hφ.contDiffOn fun p hp => ⟨show (0 : ℝ) < p.1 - s from sub_pos.2 hp.1, trivial⟩

/-- Proposition 15.4 (ii), symmetry: `f_t(x ∘ σ) = f_t(x)`. -/
private theorem fam_symm {ρ' : Measure (Herm 𝕜 N)}
    (hinv : ∀ u > 0, Herm.IsInvariant (ouDensity (gaussVar 𝕜 N) ρ' u)) {u : ℝ} (hu : 0 < u)
    (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag (x ∘ σ)) =
      ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag x) := by
  obtain ⟨U, hU, e⟩ := diag_comp_perm (𝕜 := 𝕜) x σ
  rw [e]
  exact hinv u hu U hU _

/-- Proposition 15.4 (iii): `∂_t f_t(x) = (L f_t)(x)` for `x` with pairwise distinct coordinates
(Lemmas 14.2 (i) and 15.2). -/
private theorem fam_eqn (hN : 0 < N) {ρ' : Measure (Herm 𝕜 N)} [IsProbabilityMeasure ρ']
    (hρ' : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ')
    (hinv : ∀ u > 0, Herm.IsInvariant (ouDensity (gaussVar 𝕜 N) ρ' u)) {s t : ℝ} (ht : s < t)
    {x : Fin N → ℝ} (hx : Function.Injective x) :
    HasDerivAt (fun t' => ouDensity (gaussVar 𝕜 N) ρ' (t' - s) (Herm.diag x))
      (dysonGen (betaF 𝕜) N (fun y => ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag y)) x) t := by
  have hu : 0 < t - s := sub_pos.2 ht
  obtain ⟨hP, hd⟩ := ouDensity_smooth_and_eq (gaussVar_pos' (𝕜 := 𝕜) hN) ρ' hρ'
  have h2 : ContDiff ℝ 2 (ouDensity (gaussVar 𝕜 N) ρ' (t - s)) :=
    (contDiff_slice hP hu).of_le (WithTop.coe_le_coe.2 le_top)
  rw [← ouGen_diag_eq_dysonGen (hinv _ hu) h2 hx]
  exact (hd _ hu _).comp_sub_const t s

/-- Proposition 15.4 (iv), logarithm (Lemma 14.2 (ii) with `|diag x| = |x|`). -/
private theorem fam_logBound (hN : 0 < N) {ρ' : Measure (Herm 𝕜 N)} [IsProbabilityMeasure ρ']
    (hρ' : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ') {s t₁ t₂ : ℝ} (h₁ : s < t₁) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x : Fin N → ℝ,
      |Real.log (ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x))| ≤
        C * (1 + ∑ i, x i ^ 2) := by
  refine ⟨Real.log 2 + Module.finrank ℝ (Herm 𝕜 N) / 2 * Real.log (1 / ouS (t₁ - s)) +
    (1 + 2 * ∫ w, ‖w‖ ^ 2 ∂ρ') / (gaussVar 𝕜 N * ouS (t₁ - s)), fun t ht x => ?_⟩
  have h := abs_log_ouDensity_le (gaussVar_pos' (𝕜 := 𝕜) hN) ρ' hρ' (sub_pos.2 h₁) (u := t - s)
    (by linarith [ht.1]) (Herm.diag (𝕜 := 𝕜) x)
  rwa [norm_sq_diag] at h

/-- Proposition 15.4 (iv), Fisher information: `∫ |∇f_t|² / f_t dμ < ∞` (Lemma 14.2 (iv), with
`|∇f_t(x)| = |∇Φ_t(diag x)|` from Lemma 15.2 and the invariance of `|∇Φ_t|²/Φ_t`). -/
private theorem fam_fisher (hN : 0 < N) {ρ' : Measure (Herm 𝕜 N)} [IsProbabilityMeasure ρ']
    (hρ' : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ')
    (hinv : ∀ u > 0, Herm.IsInvariant (ouDensity (gaussVar 𝕜 N) ρ' u)) {u : ℝ} (hu : 0 < u) :
    ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i (fun y => ouDensity (gaussVar 𝕜 N) ρ' u
        (Herm.diag y)) x ^ 2) / ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag x)) ∂gbeLaw 𝕜 N < ∞ := by
  obtain ⟨hP, -⟩ := ouDensity_smooth_and_eq (gaussVar_pos' (𝕜 := 𝕜) hN) ρ' hρ'
  have hΦ1 : ContDiff ℝ 1 (ouDensity (gaussVar 𝕜 N) ρ' u) :=
    (contDiff_slice hP hu).of_le (WithTop.coe_le_coe.2 le_top)
  have hΦi := hinv u hu
  have hgrad : ∀ H, ‖gradient (ouDensity (gaussVar 𝕜 N) ρ' u) H‖ =
      ‖iteratedFDeriv ℝ 1 (ouDensity (gaussVar 𝕜 N) ρ' u) H‖ := fun H => by
    rw [norm_iteratedFDeriv_one, ← toDual_gradient, LinearIsometryEquiv.norm_map]
  have hpt : ∀ H : Herm 𝕜 N,
      ENNReal.ofReal ((∑ i, pderiv i (fun y => ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag y))
        (eigVec H) ^ 2) / ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag (eigVec H))) =
      ENNReal.ofReal (‖gradient (ouDensity (gaussVar 𝕜 N) ρ' u) H‖ ^ 2 /
        ouDensity (gaussVar 𝕜 N) ρ' u H) := fun H => by
    have h1 := (gradient_diag hΦi hΦ1 (eigVec H)).2.2.1
    have h2 : ‖gradient (ouDensity (gaussVar 𝕜 N) ρ' u) (Herm.diag (eigVec H))‖ =
        ‖gradient (ouDensity (gaussVar 𝕜 N) ρ' u) H‖ := by
      rw [hgrad, hgrad]
      exact ((invariant_norm_iteratedFDeriv hΦi 1).eq_comp_eigVec H).symm
    rw [← hΦi.eq_comp_eigVec H, ← h2, h1,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc _ ≤ ∫⁻ H, ENNReal.ofReal ((∑ i, pderiv i (fun y => ouDensity (gaussVar 𝕜 N) ρ' u
          (Herm.diag y)) (eigVec H) ^ 2) /
          ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag (eigVec H))) ∂gaussH 𝕜 N :=
        lintegral_map_le (fun x => ENNReal.ofReal ((∑ i, pderiv i (fun y =>
          ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag y)) x ^ 2) /
          ouDensity (gaussVar 𝕜 N) ρ' u (Herm.diag x))) measurable_eigVec.aemeasurable
    _ = ∫⁻ H, ENNReal.ofReal (‖gradient (ouDensity (gaussVar 𝕜 N) ρ' u) H‖ ^ 2 /
          ouDensity (gaussVar 𝕜 N) ρ' u H) ∂gaussE (Herm 𝕜 N) (gaussVar 𝕜 N) :=
        lintegral_congr hpt
    _ < ∞ := (lintegral_fisher_ouDensity_lt_top (gaussVar_pos' (𝕜 := 𝕜) hN) ρ' hρ' hu).2

/-- Proposition 15.4 (iv), domination.  With `Φ_t = Ψ'(t - s, ·)`, the function
`B(u, H) = ∑_{k ≤ 2} |D^k Ψ'(u, ·)(H)| + ∑_{k ≤ 1} |D^k ∂_u Ψ'(u, ·)(H)|` is continuous and
invariant in `H`, dominates the derivatives of `f_t` at `x` through `diag x` (Lemma 15.1 (b)),
and is at most `5 𝔐(H)` with `𝔐` from Lemma 14.2 (iii); the dominating function is
`𝔪(x) = (1 + N) sup_{u ∈ [t₁ - s, t₂ - s]} B(u, diag x)`. -/
private theorem fam_dom (hN : 0 < N) {ρ' : Measure (Herm 𝕜 N)} [IsProbabilityMeasure ρ']
    (hρ' : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ')
    (hinv : ∀ u > 0, Herm.IsInvariant (ouDensity (gaussVar 𝕜 N) ρ' u)) {s : ℝ}
    (f : ℝ → (Fin N → ℝ) → ℝ)
    (hf : f = fun t x => ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x)) {t₁ t₂ : ℝ}
    (h₁ : s < t₁) (h₁₂ : t₁ < t₂) :
    ∃ 𝔪 : (Fin N → ℝ) → ℝ,
      (∀ m : ℕ, Integrable (fun x => 𝔪 x * (1 + ∑ i, x i ^ 2) ^ m) (gbeLaw 𝕜 N)) ∧
      ∀ t ∈ Set.Icc t₁ t₂, ∀ x, |f t x| + ‖fderiv ℝ (f t) x‖ + ‖iteratedFDeriv ℝ 2 (f t) x‖ +
        |deriv (fun t' => f t' x) t| + ‖fderiv ℝ (fun y => deriv (fun t' => f t' y) t) x‖ ≤
          𝔪 x := by
  subst hf
  have hv := gaussVar_pos' (𝕜 := 𝕜) hN
  obtain ⟨hP, -⟩ := ouDensity_smooth_and_eq hv ρ' hρ'
  have hu₁ : 0 < t₁ - s := sub_pos.2 h₁
  have hu₁₂ : t₁ - s ≤ t₂ - s := by linarith
  -- `∂_u Ψ'`
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × Herm 𝕜 N → ℝ, G = fun p =>
      fderiv ℝ (fun q : ℝ × Herm 𝕜 N => ouDensity (gaussVar 𝕜 N) ρ' q.1 q.2) p
        ((1 : ℝ), (0 : Herm 𝕜 N)) := ⟨_, rfl⟩
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G (Set.Ioi 0 ×ˢ Set.univ) := hGdef ▸ contDiffOn_fderiv_apply hP
  have hderiv : ∀ u > 0, ∀ H, deriv (fun u' => ouDensity (gaussVar 𝕜 N) ρ' u' H) u = G (u, H) := by
    intro u hu H
    rw [hGdef]
    exact deriv_slice_eq hP hu H
  have hGinv : ∀ u > 0, Herm.IsInvariant fun H => G (u, H) := by
    intro u hu U hU H
    simp only
    rw [← hderiv u hu, ← hderiv u hu]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hu] with u' hu'
    exact hinv u' hu' U hU H
  -- the invariant majorant
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ × Herm 𝕜 N → ℝ, B = fun p =>
      ‖iteratedFDeriv ℝ 0 (ouDensity (gaussVar 𝕜 N) ρ' p.1) p.2‖ +
        ‖iteratedFDeriv ℝ 1 (ouDensity (gaussVar 𝕜 N) ρ' p.1) p.2‖ +
        ‖iteratedFDeriv ℝ 2 (ouDensity (gaussVar 𝕜 N) ρ' p.1) p.2‖ +
        ‖iteratedFDeriv ℝ 0 (fun H => G (p.1, H)) p.2‖ +
        ‖iteratedFDeriv ℝ 1 (fun H => G (p.1, H)) p.2‖ := ⟨_, rfl⟩
  have hBc : ContinuousOn B (Set.Ioi 0 ×ˢ Set.univ) := by
    have A : ∀ k, ContinuousOn (fun p : ℝ × Herm 𝕜 N =>
        ‖iteratedFDeriv ℝ k (ouDensity (gaussVar 𝕜 N) ρ' p.1) p.2‖) (Set.Ioi 0 ×ˢ Set.univ) :=
      fun k => continuousOn_norm_iteratedFDeriv_slice hP k
    have C : ∀ k, ContinuousOn (fun p : ℝ × Herm 𝕜 N =>
        ‖iteratedFDeriv ℝ k (fun H => G (p.1, H)) p.2‖) (Set.Ioi 0 ×ˢ Set.univ) :=
      fun k => continuousOn_norm_iteratedFDeriv_slice hG k
    rw [hBdef]
    exact ((((A 0).add (A 1)).add (A 2)).add (C 0)).add (C 1)
  have hB0 : ∀ p, 0 ≤ B p := fun p => by rw [hBdef]; positivity
  have hBinv : ∀ u > 0, ∀ H, B (u, Herm.diag (eigVec H)) = B (u, H) := by
    intro u hu H
    have e1 := fun k => ((invariant_norm_iteratedFDeriv (hinv u hu) k).eq_comp_eigVec H).symm
    have e2 := fun k => ((invariant_norm_iteratedFDeriv (hGinv u hu) k).eq_comp_eigVec H).symm
    rw [hBdef]
    simp only
    rw [e1 0, e1 1, e1 2, e2 0, e2 1]
  obtain ⟨𝔐, h𝔐i, h𝔐b⟩ := integrable_sup_derivs_ouDensity hv ρ' hρ' hu₁
  have h𝔐0 : ∀ H, 0 ≤ 𝔐 H := fun H =>
    (norm_nonneg _).trans (h𝔐b _ le_rfl H 0 (by norm_num) 0 (by norm_num))
  have hBle : ∀ u, t₁ - s ≤ u → ∀ H, B (u, H) ≤ 5 * 𝔐 H := by
    intro u hu H
    have hu0 : 0 < u := hu₁.trans_le hu
    have a : ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (ouDensity (gaussVar 𝕜 N) ρ' u) H‖ ≤ 𝔐 H := by
      intro k hk
      have h := h𝔐b u hu H 0 (by norm_num) k hk
      simpa only [iteratedDeriv_zero] using h
    have c : ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (fun H' => G (u, H')) H‖ ≤ 𝔐 H := by
      intro k hk
      have h := h𝔐b u hu H 1 le_rfl k hk
      simp only [iteratedDeriv_one] at h
      rwa [funext fun y => hderiv u hu0 y] at h
    rw [hBdef]
    simp only
    linarith [a 0 (by norm_num), a 1 (by norm_num), a 2 (by norm_num), c 0 (by norm_num),
      c 1 (by norm_num)]
  -- the dominating function
  have hBc' : Continuous fun q : (Fin N → ℝ) × ℝ => B (max q.2 (t₁ - s), Herm.diag q.1) :=
    hBc.comp_continuous ((continuous_snd.max continuous_const).prodMk
      (continuous_diag.comp continuous_fst))
      fun q => ⟨show (0 : ℝ) < max q.2 (t₁ - s) from hu₁.trans_le (le_max_right _ _), trivial⟩
  have hbdd : ∀ x : Fin N → ℝ, BddAbove
      ((fun τ => B (max τ (t₁ - s), Herm.diag x)) '' Set.Icc (t₁ - s) (t₂ - s)) := fun x =>
    (isCompact_Icc.image (hBc'.comp (continuous_const.prodMk continuous_id))).bddAbove
  set 𝔪 : (Fin N → ℝ) → ℝ := fun x =>
    (1 + N) * sSup ((fun τ => B (max τ (t₁ - s), Herm.diag x)) '' Set.Icc (t₁ - s) (t₂ - s))
    with h𝔪def
  have h𝔪c : Continuous 𝔪 :=
    continuous_const.mul (isCompact_Icc.continuous_sSup
      (f := fun x τ => B (max τ (t₁ - s), Herm.diag x)) hBc')
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h𝔪0 : ∀ x, 0 ≤ 𝔪 x := fun x =>
    mul_nonneg (by linarith) (le_csSup_of_le (hbdd x) ⟨t₁ - s, Set.left_mem_Icc.2 hu₁₂, rfl⟩
      (hB0 _))
  refine ⟨𝔪, fun m => ?_, fun t ht x => ?_⟩
  · -- integrability against `μ = λ_* 𝐆`
    have hwc : Continuous fun x : Fin N → ℝ => 𝔪 x * (1 + ∑ i, x i ^ 2) ^ m :=
      h𝔪c.mul (by fun_prop)
    rw [gbeLaw, integrable_map_measure hwc.aestronglyMeasurable measurable_eigVec.aemeasurable]
    refine ((h𝔐i (2 * m)).const_mul (5 * (1 + N))).mono'
      (hwc.comp (continuous_eigVec N)).aestronglyMeasurable
      (ae_of_all _ fun H => ?_)
    have hsup : 𝔪 (eigVec H) ≤ (1 + N) * (5 * 𝔐 H) := by
      refine mul_le_mul_of_nonneg_left (csSup_le
        ((Set.nonempty_Icc.2 hu₁₂).image _) (Set.forall_mem_image.2 fun τ _ => ?_)) (by linarith)
      rw [hBinv _ (hu₁.trans_le (le_max_right _ _)) H]
      exact hBle _ (le_max_right _ _) H
    have hw : (1 + ∑ i, eigVec H i ^ 2) ^ m ≤ (1 + ‖H‖) ^ (2 * m) := by
      rw [sum_sq_eigVec, pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg H]) m
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h𝔪0 _) (by positivity))]
    calc 𝔪 (eigVec H) * (1 + ∑ i, eigVec H i ^ 2) ^ m
        ≤ ((1 + N) * (5 * 𝔐 H)) * (1 + ‖H‖) ^ (2 * m) :=
          mul_le_mul hsup hw (by positivity) (by have := h𝔐0 H; positivity)
      _ = 5 * (1 + N) * (𝔐 H * (1 + ‖H‖) ^ (2 * m)) := by ring
  · -- the pointwise bound
    have hu : 0 < t - s := by linarith [ht.1]
    have hc0 : ContDiff ℝ (⊤ : ℕ∞) (ouDensity (gaussVar 𝕜 N) ρ' (t - s)) := contDiff_slice hP hu
    have hc1 : ContDiff ℝ (⊤ : ℕ∞) (fun H => G (t - s, H)) := contDiff_slice hG hu
    have e4 : deriv (fun t' => ouDensity (gaussVar 𝕜 N) ρ' (t' - s) (Herm.diag x)) t =
        G (t - s, Herm.diag x) :=
      (deriv_comp_sub_const (fun u' => ouDensity (gaussVar 𝕜 N) ρ' u' (Herm.diag x)) s t).trans
        (hderiv _ hu _)
    have e5 : (fun y => deriv (fun t' => ouDensity (gaussVar 𝕜 N) ρ' (t' - s) (Herm.diag y)) t) =
        fun y => G (t - s, Herm.diag y) := funext fun y =>
      (deriv_comp_sub_const (fun u' => ouDensity (gaussVar 𝕜 N) ρ' u' (Herm.diag y)) s t).trans
        (hderiv _ hu _)
    have hle1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    have hle2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    have b1 := norm_iteratedFDeriv_comp_diag_le hc0 (j := 1) (by exact_mod_cast hle1) x
    have b2 := norm_iteratedFDeriv_comp_diag_le hc0 (j := 2) (by exact_mod_cast hle2) x
    have b3 := norm_iteratedFDeriv_comp_diag_le hc1 (j := 1) (by exact_mod_cast hle1) x
    simp only [norm_iteratedFDeriv_one] at b1 b3
    have hsq : Real.sqrt N ≤ 1 + N :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hsq2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
    have hBx : B (t - s, Herm.diag x) ≤ sSup ((fun τ => B (max τ (t₁ - s), Herm.diag x)) ''
        Set.Icc (t₁ - s) (t₂ - s)) :=
      le_csSup (hbdd x) ⟨t - s, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        by simp only [max_eq_left (show t₁ - s ≤ t - s by linarith [ht.1])]⟩
    have hBval : B (t - s, Herm.diag x) =
        |ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x)| +
          ‖fderiv ℝ (ouDensity (gaussVar 𝕜 N) ρ' (t - s)) (Herm.diag x)‖ +
          ‖iteratedFDeriv ℝ 2 (ouDensity (gaussVar 𝕜 N) ρ' (t - s)) (Herm.diag x)‖ +
          |G (t - s, Herm.diag x)| + ‖fderiv ℝ (fun H => G (t - s, H)) (Herm.diag x)‖ := by
      rw [hBdef]
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, norm_iteratedFDeriv_one]
    rw [hBval] at hBx
    beta_reduce
    rw [e4, e5]
    set S := sSup ((fun τ => B (max τ (t₁ - s), Herm.diag x)) '' Set.Icc (t₁ - s) (t₂ - s))
    set a := |ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x)|
    set b := ‖fderiv ℝ (ouDensity (gaussVar 𝕜 N) ρ' (t - s)) (Herm.diag x)‖
    set c := ‖iteratedFDeriv ℝ 2 (ouDensity (gaussVar 𝕜 N) ρ' (t - s)) (Herm.diag x)‖
    set d := |G (t - s, Herm.diag x)|
    set e := ‖fderiv ℝ (fun H => G (t - s, H)) (Herm.diag x)‖
    have hb : 0 ≤ b := norm_nonneg _
    have hc : 0 ≤ c := norm_nonneg _
    have he : 0 ≤ e := norm_nonneg _
    have ha : 0 ≤ a := abs_nonneg _
    have hd : 0 ≤ d := abs_nonneg _
    rw [pow_one] at b1 b3
    rw [hsq2] at b2
    have k1 : Real.sqrt N * b ≤ (1 + N) * b := mul_le_mul_of_nonneg_right hsq hb
    have k2 : (N : ℝ) * c ≤ (1 + N) * c := mul_le_mul_of_nonneg_right (by linarith) hc
    have k3 : Real.sqrt N * e ≤ (1 + N) * e := mul_le_mul_of_nonneg_right hsq he
    have k4 : a ≤ (1 + N) * a := le_mul_of_one_le_left ha (by linarith)
    have k5 : d ≤ (1 + N) * d := le_mul_of_one_le_left hd (by linarith)
    have hfin : (1 + (N : ℝ)) * (a + b + c + d + e) ≤ 𝔪 x :=
      mul_le_mul_of_nonneg_left hBx (by linarith)
    have hexp : (1 + (N : ℝ)) * (a + b + c + d + e) =
        (1 + N) * a + (1 + N) * b + (1 + N) * c + (1 + N) * d + (1 + N) * e := by ring
    linarith

end Family

/-! ### 5. The case `N = 0` -/

section Zero

attribute [local instance] gaussE_isProbabilityMeasure

/-- Two probability measures on a type with at most one point coincide. -/
private theorem eq_of_isProbabilityMeasure_of_subsingleton {α : Type*} [MeasurableSpace α]
    [Subsingleton α] (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ = ν := by
  ext B hB
  rcases B.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have hB' : B = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    simp [hB']

/-- For `N = 0`, `ℝ^0` is a point, every `ν_t` equals `μ`, and `f ≡ 1` has all the properties. -/
private theorem exists_isSmoothDensity_zero (ρ : Measure (Herm 𝕜 0)) [IsProbabilityMeasure ρ]
    (s : ℝ) : eigFlow ρ s ≪ gbeLaw 𝕜 0 ∧ ∃ f, IsSmoothDensity ρ s f := by
  have : IsProbabilityMeasure (gbeLaw 𝕜 0) := by unfold gbeLaw gaussH; infer_instance
  have hall : ∀ t, eigFlow ρ t = gbeLaw 𝕜 0 := fun t => by
    have := isProbabilityMeasure_ouLaw' (gaussVar 𝕜 0) ρ t
    have : IsProbabilityMeasure (eigFlow ρ t) := by unfold eigFlow; infer_instance
    exact eq_of_isProbabilityMeasure_of_subsingleton _ _
  refine ⟨by rw [hall s], fun _ _ => 1, ?_⟩
  exact
    { smooth := contDiffOn_const
      pos := fun _ _ _ => one_pos
      symm := fun _ _ _ _ => rfl
      density := fun t _ => by simp [hall t]
      eqn := fun t _ x _ => by simpa [dysonGen] using hasDerivAt_const t (1 : ℝ)
      logBound := fun _ _ _ _ => ⟨0, fun _ _ _ => by simp⟩
      dom := fun _ _ _ _ => ⟨fun _ => 1, fun m => by simp,
        fun _ _ _ => by simp [iteratedFDeriv_const_of_ne (two_ne_zero)]⟩
      fisher := fun _ _ => by simp }

end Zero

/-! ### 6. Proposition 15.4 -/

/-- Proposition 15.4: a smooth symmetric version of `dν_t/dμ` solving `∂_t f = L f`. -/
theorem exists_isSmoothDensity {N : ℕ} (ρ : Measure (Herm 𝕜 N)) [IsProbabilityMeasure ρ]
    (hρ : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ) {s : ℝ} (hs : 0 < s) :
    eigFlow ρ s ≪ gbeLaw 𝕜 N ∧ ∃ f, IsSmoothDensity ρ s f := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact exists_isSmoothDensity_zero ρ s
  have hv := gaussVar_pos' (𝕜 := 𝕜) hN
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  have := isProbabilityMeasure_ouLaw' (gaussVar 𝕜 N) ρ s
  have : IsProbabilityMeasure (eigFlow ρ s) := by unfold eigFlow; infer_instance
  have : IsProbabilityMeasure (gbeLaw 𝕜 N) := by unfold gbeLaw gaussH; infer_instance
  -- (i): `ν_s ≪ μ`
  have habs : eigFlow ρ s ≪ gbeLaw 𝕜 N := by
    unfold eigFlow gbeLaw gaussH
    rw [(ouLaw_eq_withDensity hv hs ρ).1]
    exact (withDensity_absolutelyContinuous _ _).map measurable_eigVec
  refine ⟨habs, ?_⟩
  -- `ρ' = Φ_s 𝐆` with `Φ_s = f_s ∘ λ`, `f_s = dν_s/dμ`
  set fs := (eigFlow ρ s).rnDeriv (gbeLaw 𝕜 N) with hfs
  have hfsm : Measurable fs := Measure.measurable_rnDeriv _ _
  have hφ : Measurable fun H : Herm 𝕜 N => fs (eigVec H) := hfsm.comp measurable_eigVec
  obtain ⟨ρ', hρ'def⟩ : ∃ ρ' : Measure (Herm 𝕜 N),
      ρ' = (gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)).withDensity fun H => fs (eigVec H) := ⟨_, rfl⟩
  have hmap : ρ'.map eigVec = (ouLaw (gaussVar 𝕜 N) ρ s).map eigVec := by
    rw [hρ'def, map_withDensity_comp_eigVec _ hfsm]
    have : SigmaFinite (eigFlow ρ s) := inferInstance
    have : SigmaFinite (gbeLaw 𝕜 N) := inferInstance
    exact Measure.withDensity_rnDeriv_eq (eigFlow ρ s) (gbeLaw 𝕜 N) habs
  have : IsProbabilityMeasure ρ' := ⟨by
    have h1 := Measure.map_apply (μ := ρ') measurable_eigVec MeasurableSet.univ
    rw [Set.preimage_univ, hmap, measure_univ] at h1
    exact h1.symm⟩
  have hρ' : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ' := fun m =>
    integrable_norm_pow_of_map_eq hmap.symm
      (integrable_norm_pow_ouLaw gaussVar_nonneg' hs.le ρ hρ m)
  -- `Φ_t = Ψ'(t - s, ·) = T_{t-s} Φ_s` is invariant
  have hinv : ∀ u > 0, Herm.IsInvariant (ouDensity (gaussVar 𝕜 N) ρ' u) := by
    intro u hu U hU H
    have : IsFiniteMeasure ((gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)).withDensity
        fun H => fs (eigVec H)) := by rw [← hρ'def]; infer_instance
    have e : ∀ H, ouDensity (gaussVar 𝕜 N) ρ' u H =
        (mehlerL (gaussVar 𝕜 N) u (fun H => fs (eigVec H)) H).toReal := fun H => by
      rw [← ofReal_ouDensity_withDensity hv hu hφ, ← hρ'def,
        ENNReal.toReal_ofReal ((ouLaw_eq_withDensity hv hu ρ').2 H).le]
    rw [e, e, Herm.IsInvariant.mehlerL (isInvariant_comp_eigVec fs) hφ u U hU H]
  obtain ⟨hP, -⟩ := ouDensity_smooth_and_eq hv ρ' hρ'
  -- (ii), identification: `ν_t = f_t μ`
  have hdens : ∀ t > s, eigFlow ρ t = (gbeLaw 𝕜 N).withDensity
      fun x => ENNReal.ofReal (ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x)) := by
    intro t ht
    have hu : 0 < t - s := sub_pos.2 ht
    have e1 : ouLaw (gaussVar 𝕜 N) ρ t =
        ouLaw (gaussVar 𝕜 N) (ouLaw (gaussVar 𝕜 N) ρ s) (t - s) := by
      rw [ouLaw_ouLaw gaussVar_nonneg' hs.le hu.le, add_sub_cancel]
    have hcont : Continuous fun x : Fin N → ℝ =>
        ENNReal.ofReal (ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x)) :=
      ENNReal.continuous_ofReal.comp ((contDiff_slice hP hu).continuous.comp continuous_diag)
    have e2 : (fun H => ENNReal.ofReal (ouDensity (gaussVar 𝕜 N) ρ' (t - s) H)) =
        fun H => (fun x : Fin N → ℝ =>
          ENNReal.ofReal (ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x))) (eigVec H) :=
      funext fun H => by rw [(hinv _ hu).eq_comp_eigVec H]
    have e3 := map_withDensity_comp_eigVec (gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)) hcont.measurable
    rw [← e2] at e3
    unfold eigFlow
    rw [e1, map_ouLaw_eq hmap.symm, (ouLaw_eq_withDensity hv hu ρ').1, e3]
    rfl
  refine ⟨fun t x => ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x), ?_⟩
  exact
    { smooth := fam_smooth hP s
      pos := fun t ht x => (ouLaw_eq_withDensity hv (sub_pos.2 ht) ρ').2 _
      symm := fun t ht x σ => fam_symm hinv (sub_pos.2 ht) x σ
      density := hdens
      eqn := fun t ht x hx => fam_eqn hN hρ' hinv ht hx
      logBound := fun t₁ t₂ h₁ _ => fam_logBound hN hρ' h₁
      dom := fun t₁ t₂ h₁ h₁₂ => fam_dom hN hρ' hinv
        (fun t x => ouDensity (gaussVar 𝕜 N) ρ' (t - s) (Herm.diag x)) rfl h₁ h₁₂
      fisher := fun t ht => fam_fisher hN hρ' hinv (sub_pos.2 ht) }

end Rigidity
