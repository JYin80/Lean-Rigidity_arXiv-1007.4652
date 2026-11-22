module

public import Mathlib
public import Rigidity.MainDefs

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-!
# Ensembles of random hermitian matrices

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].
-/

/-! ### 1. Ensembles (§2, (2.1)–(2.4), (2.17)) -/

namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `σ_ij`. -/
noncomputable def sd (i j : Fin N) : ℝ := Real.sqrt (M.var i j)

theorem varMatrix_isHermitian : M.varMatrix.IsHermitian := by
  ext i j
  simp [varMatrix, var, Pair.mk'_comm i j]

/-- Assumption (B) as printed (2.3): `1` is a simple eigenvalue of `B` and
`Spec B ⊆ [-1 + δ₋, 1 - δ₊] ∪ {1}`. -/
def AssumptionBSpec (δm δp : ℝ) : Prop :=
  ∃ k, M.varMatrix_isHermitian.eigenvalues k = 1 ∧
    ∀ k' ≠ k, M.varMatrix_isHermitian.eigenvalues k' ∈ Set.Icc (-1 + δm) (1 - δp)

theorem Assumptions.mono {ϑ δm δp C₀ ϑ' δm' δp' C₀' : ℝ} (h : M.Assumptions ϑ δm δp C₀)
    (hϑ' : 0 < ϑ') (hϑ : ϑ' ≤ ϑ) (hδm : δm' ≤ δm) (hδp : δp' ≤ δp) (hC : C₀ ≤ C₀') :
    M.Assumptions ϑ' δm' δp' C₀' := by
  obtain ⟨h0, hd, hA, hB, hC', hS⟩ := h
  refine ⟨h0, hd, hA, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨h1, h2⟩ := hB v hv
    have hS : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    constructor
    · nlinarith
    · nlinarith
  · intro i j
    exact (hC' i j).trans (div_le_div_of_nonneg_right hC (Nat.cast_nonneg N))
  · intro p x hx
    refine (hS p x hx).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have h1 : x ^ ϑ' ≤ x ^ ϑ := Real.rpow_le_rpow_of_exponent_le hx hϑ
    have h2 : Real.exp (-(x ^ ϑ)) ≤ Real.exp (-(x ^ ϑ')) := Real.exp_le_exp.mpr (by linarith)
    have h3 : ϑ⁻¹ ≤ ϑ'⁻¹ := inv_anti₀ hϑ' hϑ
    exact mul_le_mul h3 h2 (Real.exp_nonneg _) (inv_nonneg.mpr hϑ'.le)

/-! #### Transformations of ensembles -/

/-- The ensemble of `c • H`, `c` real. -/
noncomputable def smul (c : ℝ) : Ensemble 𝕜 N where
  law p := (M.law p).map fun y => (c : 𝕜) * y
  isProb _ := inferInstance

/-- The hybrid ensemble: entries in `Q` from `Mw`, the others from `M`. -/
noncomputable def hybrid (Mw : Ensemble 𝕜 N) (Q : Set (Pair N)) [DecidablePred (· ∈ Q)] :
    Ensemble 𝕜 N where
  law p := if p ∈ Q then Mw.law p else M.law p
  isProb p := by split_ifs <;> infer_instance

/-- The ensemble of `H_t = e^{-t/2} H + (1 - e^{-t})^{1/2} V` (2.29), `V` with ensemble `g`
independent of `H`: entry laws `law(e^{-t/2} h_p) ∗ law((1 - e^{-t})^{1/2} v_p)`. -/
noncomputable def ouFlow (g : Ensemble 𝕜 N) (t : ℝ) : Ensemble 𝕜 N where
  law p := (M.smul (Real.exp (-t / 2))).law p ∗ (g.smul (Real.sqrt (1 - Real.exp (-t)))).law p
  isProb _ := inferInstance

/-! ### 2. Product splitting -/

end Ensemble

/-! ### 7. Witnesses -/

/-- The symmetric two-point law `(δ_a + δ_{-a}) / 2`. -/
noncomputable def rademacherLaw (a : ℝ) : Measure 𝕜 :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac (a : 𝕜) + Measure.dirac (-(a : 𝕜)))

instance (a : ℝ) : IsProbabilityMeasure (rademacherLaw (𝕜 := 𝕜) a) := by
  constructor
  simp only [rademacherLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The standard Wigner matrix with Rademacher entries `±N^{-1/2}`. -/
noncomputable def rademacher (N : ℕ) : Ensemble 𝕜 N where
  law _ := rademacherLaw (Real.sqrt N)⁻¹
  isProb _ := inferInstance

/-- Integral against the symmetric two-point law. -/
private lemma rademacherLaw_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) (f : 𝕜 → E) :
    ∫ y, f y ∂rademacherLaw (𝕜 := 𝕜) a = (1 / 2 : ℝ) • (f a + f (-a)) := by
  unfold rademacherLaw
  rw [integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]

/-- Every entry of the Rademacher ensemble has variance `1 / N`. -/
private lemma rademacher_var (N : ℕ) (p : Pair N) :
    (rademacher (𝕜 := 𝕜) N).varPair p = 1 / N := by
  unfold Ensemble.varPair rademacher
  simp only
  rw [rademacherLaw_integral]
  simp only [norm_neg, RCLike.norm_ofReal, sq_abs]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

/-- Variance of the Rademacher ensemble, indexed by `i, j`. -/
private lemma rademacher_var' (N : ℕ) (i j : Fin N) :
    (rademacher (𝕜 := 𝕜) N).var i j = 1 / N :=
  rademacher_var N _

theorem rademacher_assumptions (N : ℕ) (hN : 0 < N) :
    (rademacher (𝕜 := 𝕜) N).Assumptions (1 / 2) 1 1 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change ∫ y, y ∂rademacherLaw (𝕜 := 𝕜) (Real.sqrt N)⁻¹ = 0
    rw [rademacherLaw_integral]
    simp
  · intro i
    change ∀ᵐ y ∂rademacherLaw (𝕜 := 𝕜) (Real.sqrt N)⁻¹, RCLike.im y = 0
    unfold rademacherLaw
    refine Measure.ae_smul_measure ?_ _
    rw [ae_add_measure_iff]
    have hm : MeasurableSet {y : 𝕜 | RCLike.im y = 0} :=
      measurableSet_eq_fun RCLike.continuous_im.measurable measurable_const
    refine ⟨?_, ?_⟩ <;> rw [ae_dirac_iff hm] <;> simp
  · intro j
    simp only [rademacher_var']
    simp [Finset.sum_const, hNr.ne']
  · intro v hv
    have hB : (rademacher (𝕜 := 𝕜) N).varMatrix *ᵥ v = 0 := by
      ext i
      simp [Ensemble.varMatrix, rademacher_var', Matrix.mulVec, dotProduct, ← Finset.mul_sum, hv]
    rw [hB]
    simp
  · intro i j
    rw [rademacher_var']
  · intro p x hx
    have hpos : 0 < (Real.sqrt N)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hNr)
    have hv : (rademacher (𝕜 := 𝕜) N).varPair p = ((Real.sqrt N)⁻¹) ^ 2 := by
      rw [rademacher_var, inv_pow, Real.sq_sqrt hNr.le]
      simp
    have hsq : Real.sqrt ((rademacher (𝕜 := 𝕜) N).varPair p) = (Real.sqrt N)⁻¹ := by
      rw [hv, Real.sqrt_sq hpos.le]
    rw [hsq]
    change rademacherLaw (𝕜 := 𝕜) (Real.sqrt N)⁻¹ _ ≤ _
    have hm : MeasurableSet {y : 𝕜 | x * (Real.sqrt N)⁻¹ < ‖y‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hxa : x * (Real.sqrt N)⁻¹ ≥ (Real.sqrt N)⁻¹ := by nlinarith
    unfold rademacherLaw
    rw [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm,
      Measure.dirac_apply' _ hm]
    simp only [Set.indicator, Set.mem_ofPred_eq, norm_neg, RCLike.norm_ofReal, abs_of_pos hpos,
      Pi.one_apply]
    simp [not_lt.mpr hxa]

end Rigidity
