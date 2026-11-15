import Rigidity.Ensemble.Basic
import Rigidity.Stability.Vector

/-!
# Condition (B) as a spectral condition, the band-matrix witness, and consequences of (A)-(C)

Numbers refer to NP v1.1; the original is cited as [EYY, ...].

For an ensemble satisfying (A), the quadratic-form version of (B) on `𝐞^⊥` is equivalent to the
spectral condition (2.3) of [EYY] (Lemma 2.5 (i)). The band ensemble of width two on `ℤ/8`, the
normalisation of the band-matrix example [EYY, Example 2], is an ensemble of the class with
explicit constants, with variances not all equal. The class constants satisfy `C₀ ≥ 1`, and
`δ₋ + δ₊ ≤ 2` for `N ≥ 2` (Lemma 2.5 (iii)), and the variance matrix of an ensemble in the class
is a `VarProfile` (conditions (A), (B), (C) of Definition 2.2).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- Under (A), `B` preserves the coordinate sum. -/
private lemma specB_sum_mulVec (hA : M.AssumptionA) (v : Fin N → ℝ) :
    ∑ i, (M.varMatrix *ᵥ v) i = ∑ i, v i := by
  simp only [Matrix.mulVec, dotProduct, varMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, hA j, one_mul]

/-- The inner product on `EuclideanSpace ℝ (Fin N)` in coordinates. -/
private lemma specB_inner (x y : EuclideanSpace ℝ (Fin N)) :
    inner ℝ x y = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-- Orthonormality of the eigenvector basis, in coordinates. -/
private lemma specB_orth (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)))
    (α β : Fin N) : ∑ i, b α i * b β i = if α = β then 1 else 0 := by
  rw [← specB_inner]
  exact orthonormal_iff_ite.mp b.orthonormal α β

/-- Condition (B) gives the spectral condition. -/
private lemma specB_toSpec {δm δp : ℝ} (hN : 0 < N) (hA : M.AssumptionA) (hδp : 0 < δp)
    (hB : M.AssumptionB δm δp) : M.AssumptionBSpec δm δp := by
  set hH := M.varMatrix_isHermitian with hHdef
  set b := hH.eigenvectorBasis with hbdef
  set μ := hH.eigenvalues with hμdef
  have hu : ∀ α, M.varMatrix *ᵥ ⇑(b α) = μ α • ⇑(b α) := hH.mulVec_eigenvectorBasis
  have hnorm : ∀ α, ∑ i, b α i ^ 2 = 1 := fun α => by
    simpa [sq] using specB_orth b α α
  have hray : ∀ α, ⇑(b α) ⬝ᵥ (M.varMatrix *ᵥ ⇑(b α)) = μ α := fun α => by
    have h1 : ∑ i, b α i * b α i = 1 := by simpa [sq] using hnorm α
    rw [hu, dotProduct_smul, dotProduct, smul_eq_mul, h1, mul_one]
  have hsum : ∀ α, μ α ≠ 1 → ∑ i, b α i = 0 := fun α hα => by
    have h := M.specB_sum_mulVec hA (b α)
    rw [hu] at h
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
    have : (μ α - 1) * ∑ i, b α i = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by linarith) hα
    · exact h0
  have hloc : ∀ α, μ α ≠ 1 → μ α ∈ Set.Icc (-1 + δm) (1 - δp) := fun α hα => by
    obtain ⟨h1, h2⟩ := hB (b α) (hsum α hα)
    rw [hray α, hnorm α] at h1 h2
    constructor <;> linarith
  have hne : ∀ α, μ α = 1 → ∑ i, b α i ≠ 0 := fun α h0 hs => by
    obtain ⟨-, h2⟩ := hB (b α) hs
    rw [hray α, hnorm α, h0] at h2
    linarith
  have hex : ∃ α, μ α = 1 := by
    by_contra hcon'
    have hcon : ∀ α, μ α ≠ 1 := fun α h => hcon' ⟨α, h⟩
    have hP := b.sum_sq_norm_inner_right (WithLp.toLp 2 fun _ : Fin N => (1 : ℝ))
    have h0 : ∀ α, inner ℝ (b α) (WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)) = 0 := fun α => by
      rw [specB_inner]
      simpa using hsum α (hcon α)
    simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at hP
    have : ‖(WithLp.toLp 2 fun _ : Fin N => (1 : ℝ))‖ ^ 2 = N := by
      rw [EuclideanSpace.norm_sq_eq]
      simp
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    linarith
  have huniq : ∀ α β, μ α = 1 → μ β = 1 → α = β := fun α β hα hβ => by
    by_contra hne'
    set sα := ∑ i, b α i with hsα
    set sβ := ∑ i, b β i with hsβ
    set w : Fin N → ℝ := fun i => sβ * b α i - sα * b β i with hw
    have hw0 : ∑ i, w i = 0 := by
      simp only [hw, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    have hBw : M.varMatrix *ᵥ w = w := by
      have : w = sβ • ⇑(b α) - sα • ⇑(b β) := by
        ext i; simp [hw]
      rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hu, hα, hβ]
      simp
    have hww : ∑ i, w i ^ 2 = sβ ^ 2 + sα ^ 2 := by
      have e1 := hnorm α
      have e2 := hnorm β
      have e3 : ∑ i, b α i * b β i = 0 := by simpa [hne'] using specB_orth b α β
      calc ∑ i, w i ^ 2
          = sβ ^ 2 * ∑ i, b α i ^ 2 + sα ^ 2 * ∑ i, b β i ^ 2
            - 2 * sα * sβ * ∑ i, b α i * b β i := by
            simp only [hw, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = sβ ^ 2 + sα ^ 2 := by rw [e1, e2, e3]; ring
    obtain ⟨-, h2⟩ := hB w hw0
    rw [hBw] at h2
    have hdot : w ⬝ᵥ w = ∑ i, w i ^ 2 := by simp [dotProduct, sq]
    rw [hdot] at h2
    have hpos : 0 < sβ ^ 2 + sα ^ 2 := by
      have := hne α hα
      positivity
    nlinarith
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, hk, fun k' hk' => hloc k' fun h => hk' (huniq k' k h hk)⟩

/-- The spectral condition gives condition (B). -/
private lemma specB_ofSpec {δm δp : ℝ} (hN : 0 < N) (hA : M.AssumptionA) (hδp : 0 < δp)
    (hS : M.AssumptionBSpec δm δp) : M.AssumptionB δm δp := by
  obtain ⟨k, hk, hk'⟩ := hS
  set hH := M.varMatrix_isHermitian with hHdef
  set b := hH.eigenvectorBasis with hbdef
  set μ := hH.eigenvalues with hμdef
  have hu : ∀ α, M.varMatrix *ᵥ ⇑(b α) = μ α • ⇑(b α) := hH.mulVec_eigenvectorBasis
  have hsym : M.varMatrix.IsSymm := Matrix.isHermitian_iff_isSymm.mp hH
  set e : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 fun _ : Fin N => (1 : ℝ) with he
  have hsum : ∀ α, α ≠ k → ∑ i, b α i = 0 := fun α hα => by
    have h := M.specB_sum_mulVec hA (b α)
    rw [hu] at h
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
    have hμ : μ α ≤ 1 - δp := (hk' α hα).2
    have : (μ α - 1) * ∑ i, b α i = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact h0
  have hek : ∀ α, inner ℝ (b α) e = if α = k then ∑ i, b k i else 0 := fun α => by
    rw [specB_inner]
    by_cases hα : α = k
    · subst hα; simp [he]
    · simp [he, hα, hsum α hα]
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsk : (∑ i, b k i) ^ 2 = N := by
    have hP := b.sum_sq_norm_inner_right e
    have : ‖e‖ ^ 2 = N := by
      rw [he, EuclideanSpace.norm_sq_eq]
      simp
    have h3 : ∀ α, ‖inner ℝ (b α) e‖ ^ 2 = if α = k then (∑ i, b k i) ^ 2 else 0 := fun α => by
      rw [hek α]
      split_ifs <;> simp
    rw [← this, ← hP]
    simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsk0 : ∑ i, b k i ≠ 0 := fun h => by rw [h] at hsk; simp at hsk; linarith
  intro v hv
  set x : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 v with hx
  set c : Fin N → ℝ := fun α => ∑ i, b α i * v i with hc
  have hcα : ∀ α, inner ℝ (b α) x = c α := fun α => by rw [specB_inner]
  have hck : c k = 0 := by
    have h1 := b.sum_inner_mul_inner e x
    have h2 : inner ℝ e x = 0 := by
      rw [specB_inner]; simpa [he, hx] using hv
    rw [h2] at h1
    have : ∀ α, inner ℝ e (b α) = inner ℝ (b α) e := fun α => real_inner_comm _ _
    simp only [this, hek, hcα] at h1
    rw [Finset.sum_eq_single k (fun α _ hα => by simp [hα]) (by simp)] at h1
    simp only [ite_true] at h1
    rcases mul_eq_zero.mp h1 with h0 | h0
    · exact absurd h0 hsk0
    · exact h0
  have hnorm2 : ∑ i, v i ^ 2 = ∑ α, c α ^ 2 := by
    have hP := b.sum_sq_norm_inner_right x
    simp only [hcα, Real.norm_eq_abs, sq_abs] at hP
    rw [hP, hx, EuclideanSpace.norm_sq_eq]
    simp
  have hquad : v ⬝ᵥ (M.varMatrix *ᵥ v) = ∑ α, μ α * c α ^ 2 := by
    set y : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (M.varMatrix *ᵥ v) with hy
    have h1 := b.sum_inner_mul_inner x y
    have hxy : inner ℝ x y = v ⬝ᵥ (M.varMatrix *ᵥ v) := by
      rw [specB_inner]; simp [hx, hy, dotProduct]
    have hby : ∀ α, inner ℝ (b α) y = μ α * c α := fun α => by
      rw [specB_inner]
      have : ∑ i, b α i * y i = ⇑(b α) ⬝ᵥ (M.varMatrix *ᵥ v) := rfl
      rw [this, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym.eq, hu,
        smul_dotProduct, smul_eq_mul]
      rfl
    have hxb : ∀ α, inner ℝ x (b α) = c α := fun α => by
      rw [real_inner_comm, hcα]
    rw [← hxy, ← h1]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hxb, hby]; ring
  rw [hnorm2, hquad, Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun α _ => ?_
    by_cases hα : α = k
    · subst hα; simp [hck]
    · exact mul_le_mul_of_nonneg_right (hk' α hα).1 (sq_nonneg _)
  · refine Finset.sum_le_sum fun α _ => ?_
    by_cases hα : α = k
    · subst hα; simp [hck]
    · have := mul_le_mul_of_nonneg_right (hk' α hα).2 (sq_nonneg (c α))
      linarith

/-- Under (A), the quadratic-form version of (B) is equivalent to (2.3). -/
theorem assumptionB_iff (hN : 0 < N) (hA : M.AssumptionA) {δm δp : ℝ} (hδp : 0 < δp) :
    M.AssumptionB δm δp ↔ M.AssumptionBSpec δm δp := by
  exact ⟨M.specB_toSpec hN hA hδp, M.specB_ofSpec hN hA hδp⟩

end Ensemble

/-- The band of width two on `ℤ/8` (normalised Example 2): variance `1/5` for
`|[i - j]_8| ≤ 2`, zero otherwise. -/
def band8 (p : Pair 8) : Prop := p.1.2.val - p.1.1.val ≤ 2 ∨ 6 ≤ p.1.2.val - p.1.1.val

instance : DecidablePred band8 := fun p => by unfold band8; infer_instance

noncomputable def bandEnsemble8 : Ensemble 𝕜 8 where
  law p := if band8 p then rademacherLaw (Real.sqrt 5)⁻¹ else Measure.dirac 0
  isProb p := by split_ifs <;> infer_instance

/-- Integral against the symmetric two-point law. -/
private lemma specB_rademacherLaw_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) (f : 𝕜 → E) :
    ∫ y, f y ∂rademacherLaw (𝕜 := 𝕜) a = (1 / 2 : ℝ) • (f a + f (-a)) := by
  unfold rademacherLaw
  rw [integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]

/-- The variance of an entry of the band ensemble is `1/5` inside the band and `0` outside. -/
private lemma bandEnsemble8_varPair (p : Pair 8) :
    (bandEnsemble8 (𝕜 := 𝕜)).varPair p = if band8 p then 1 / 5 else 0 := by
  unfold Ensemble.varPair bandEnsemble8
  simp only
  split_ifs
  · rw [specB_rademacherLaw_integral]
    simp only [norm_neg, RCLike.norm_ofReal, sq_abs]
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    ring
  · simp

/-- The matrix of variances of the band ensemble, indexed by `i, j`. -/
private lemma bandEnsemble8_var (i j : Fin 8) :
    (bandEnsemble8 (𝕜 := 𝕜)).var i j = if band8 (Pair.mk' i j) then 1 / 5 else 0 :=
  bandEnsemble8_varPair _

/-- The quadratic form of the matrix of variances of the band ensemble. -/
private lemma bandEnsemble8_quad (v : Fin 8 → ℝ) :
    v ⬝ᵥ ((bandEnsemble8 (𝕜 := 𝕜)).varMatrix *ᵥ v) =
      (1 / 5) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 + v 5 ^ 2 + v 6 ^ 2 + v 7 ^ 2
        + 2 * (v 0 * v 1 + v 1 * v 2 + v 2 * v 3 + v 3 * v 4 + v 4 * v 5 + v 5 * v 6 + v 6 * v 7
          + v 7 * v 0)
        + 2 * (v 0 * v 2 + v 1 * v 3 + v 2 * v 4 + v 3 * v 5 + v 4 * v 6 + v 5 * v 7 + v 6 * v 0
          + v 7 * v 1)) := by
  simp only [Ensemble.varMatrix, Matrix.of_apply, bandEnsemble8_var, Matrix.mulVec, dotProduct,
    Fin.sum_univ_eight]
  simp [band8, Pair.mk']
  ring

/-- Condition (B) for the band ensemble with `δ₋ = 1/2`, `δ₊ = 1/4`. With `W` the matrix of
the window of width five, `v ⬝ᵥ W v + (5/4) |v|²` is the sum of the squares
`(v_{i-1} + v_{i+1} + v_i / 2)²`, which gives the lower bound on all of `ℝ⁸`; on `𝐞^⊥` the
upper bound follows from `(∑ v_i)² = 0` and the squares `(v_i + v_{i+3})²`, `(v_i + v_{i+4})²`. -/
private lemma bandEnsemble8_assumptionB :
    (bandEnsemble8 (𝕜 := 𝕜)).AssumptionB (1 / 2) (1 / 4) := by
  intro v hv
  have h0 : (v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7) ^ 2 = 0 := by
    rw [Fin.sum_univ_eight] at hv
    rw [hv]
    ring
  rw [bandEnsemble8_quad, Fin.sum_univ_eight]
  constructor
  · linarith [sq_nonneg (v 7 + v 1 + v 0 / 2), sq_nonneg (v 0 + v 2 + v 1 / 2),
      sq_nonneg (v 1 + v 3 + v 2 / 2), sq_nonneg (v 2 + v 4 + v 3 / 2),
      sq_nonneg (v 3 + v 5 + v 4 / 2), sq_nonneg (v 4 + v 6 + v 5 / 2),
      sq_nonneg (v 5 + v 7 + v 6 / 2), sq_nonneg (v 6 + v 0 + v 7 / 2),
      sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3), sq_nonneg (v 4),
      sq_nonneg (v 5), sq_nonneg (v 6), sq_nonneg (v 7)]
  · linarith [sq_nonneg (v 0 + v 3), sq_nonneg (v 1 + v 4), sq_nonneg (v 2 + v 5),
      sq_nonneg (v 3 + v 6), sq_nonneg (v 4 + v 7), sq_nonneg (v 5 + v 0),
      sq_nonneg (v 6 + v 1), sq_nonneg (v 7 + v 2),
      sq_nonneg (v 0 + v 4), sq_nonneg (v 1 + v 5), sq_nonneg (v 2 + v 6), sq_nonneg (v 3 + v 7),
      sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3), sq_nonneg (v 4),
      sq_nonneg (v 5), sq_nonneg (v 6), sq_nonneg (v 7)]

theorem bandEnsemble8_assumptions :
    (bandEnsemble8 (𝕜 := 𝕜)).Assumptions (1 / 2) (1 / 2) (1 / 4) 2 := by
  refine ⟨?_, ?_, ?_, bandEnsemble8_assumptionB, ?_, ?_⟩
  · intro p
    change ∫ y, y ∂(if band8 p then rademacherLaw (Real.sqrt 5)⁻¹ else Measure.dirac 0) = 0
    split_ifs
    · rw [specB_rademacherLaw_integral]
      simp
    · simp
  · intro i
    change ∀ᵐ y ∂(if band8 (Pair.mk' i i) then rademacherLaw (𝕜 := 𝕜) (Real.sqrt 5)⁻¹
      else Measure.dirac 0), RCLike.im y = 0
    have hm : MeasurableSet {y : 𝕜 | RCLike.im y = 0} :=
      measurableSet_eq_fun RCLike.continuous_im.measurable measurable_const
    split_ifs
    · unfold rademacherLaw
      refine Measure.ae_smul_measure ?_ _
      rw [ae_add_measure_iff]
      refine ⟨?_, ?_⟩ <;> rw [ae_dirac_iff hm] <;> simp
    · rw [ae_dirac_iff hm]
      simp
  · intro j
    simp only [bandEnsemble8_var]
    rw [← Finset.sum_filter, Finset.sum_const]
    have : ∀ j : Fin 8, (Finset.univ.filter fun i : Fin 8 => band8 (Pair.mk' i j)).card = 5 := by
      decide
    rw [this j]
    norm_num
  · intro i j
    rw [bandEnsemble8_var]
    split_ifs <;> norm_num
  · intro p x hx
    refine le_trans (le_of_eq ?_) zero_le
    rw [bandEnsemble8_varPair]
    have hm : ∀ r : ℝ, MeasurableSet {y : 𝕜 | r < ‖y‖} := fun r =>
      measurableSet_lt measurable_const measurable_norm
    change (if band8 p then rademacherLaw (𝕜 := 𝕜) (Real.sqrt 5)⁻¹ else Measure.dirac 0) _ = 0
    split_ifs
    · have hsq : Real.sqrt (1 / 5 : ℝ) = (Real.sqrt 5)⁻¹ := by
        rw [one_div, Real.sqrt_inv]
      have hpos : 0 < (Real.sqrt 5)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
      rw [hsq]
      have hxa : x * (Real.sqrt 5)⁻¹ ≥ (Real.sqrt 5)⁻¹ := by nlinarith
      unfold rademacherLaw
      rw [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ (hm _),
        Measure.dirac_apply' _ (hm _)]
      simp only [Set.indicator, Set.mem_ofPred_eq, norm_neg, RCLike.norm_ofReal, abs_of_pos hpos,
        Pi.one_apply]
      simp [not_lt.mpr hxa]
    · rw [Real.sqrt_zero, mul_zero, Measure.dirac_apply' _ (hm _)]
      simp

namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

end Ensemble

/-- The variance matrix of an ensemble in the class satisfies (A), (B), (C). -/
theorem Ensemble.Assumptions.varProfile {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) : VarProfile M.varMatrix δm δp C₀ := by
  exact
    { symm := Matrix.isHermitian_iff_isSymm.mp M.varMatrix_isHermitian
      nonneg := fun _ _ => integral_nonneg fun _ => sq_nonneg _
      sumA := h.sumA
      specB := h.specB
      boundC := h.boundC }

end Rigidity
