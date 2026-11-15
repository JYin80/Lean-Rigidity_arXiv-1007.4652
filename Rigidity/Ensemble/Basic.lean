import Mathlib

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-!
# Ensembles of random hermitian matrices

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].
-/

/-! ### 1. Ensembles (§2, (2.1)–(2.4), (2.17)) -/

/-- Index pairs `(i, j)` with `i ≤ j`: the independent entries of an `N × N` hermitian matrix. -/
abbrev Pair (N : ℕ) := {p : Fin N × Fin N // p.1 ≤ p.2}

/-- The pair `(min i j, max i j)`. -/
def Pair.mk' {N : ℕ} (i j : Fin N) : Pair N :=
  if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), (not_le.mp h).le⟩

theorem Pair.mk'_comm {N : ℕ} (i j : Fin N) : Pair.mk' i j = Pair.mk' j i := by
  unfold Pair.mk'
  by_cases h₁ : i ≤ j <;> by_cases h₂ : j ≤ i
  · have : i = j := le_antisymm h₁ h₂
    subst this; rfl
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · exact absurd (le_total i j) (by tauto)

/-- The hermitian matrix with upper-triangular entries `x`: `h_ij = x_ij` for `i < j`,
`h_ji = conj h_ij`, and real diagonal `h_ii = re x_ii`. -/
def toMatrix {N : ℕ} (x : Pair N → 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j =>
    if i < j then x (Pair.mk' i j)
    else if j < i then star (x (Pair.mk' i j))
    else ((RCLike.re (x (Pair.mk' i j)) : ℝ) : 𝕜)

theorem toMatrix_isHermitian {N : ℕ} (x : Pair N → 𝕜) : (toMatrix x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, toMatrix, Matrix.of_apply]
  rw [Pair.mk'_comm j i]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · simp
  · simp [h, not_lt_of_gt h]

/-- One `N × N` ensemble: a probability law for each entry `h_ij`, `i ≤ j`. -/
structure Ensemble (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) where
  law : Pair N → Measure 𝕜
  isProb : ∀ p, IsProbabilityMeasure (law p)

attribute [instance] Ensemble.isProb

namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- The joint law of the entries: the product of the entry laws. -/
noncomputable def prodLaw : Measure (Pair N → 𝕜) := Measure.pi M.law

instance : IsProbabilityMeasure M.prodLaw := by unfold prodLaw; infer_instance

/-- `σ_p² = 𝔼|h_p|²` (2.1). -/
noncomputable def varPair (p : Pair N) : ℝ := ∫ y, ‖y‖ ^ 2 ∂M.law p

/-- `σ_ij²` for all `i, j`, with `σ_ji = σ_ij`. -/
noncomputable def var (i j : Fin N) : ℝ := M.varPair (Pair.mk' i j)

/-- `σ_ij`. -/
noncomputable def sd (i j : Fin N) : ℝ := Real.sqrt (M.var i j)

/-- The matrix of variances `B = (σ_ij²)`. -/
noncomputable def varMatrix : Matrix (Fin N) (Fin N) ℝ := Matrix.of M.var

theorem varMatrix_isHermitian : M.varMatrix.IsHermitian := by
  ext i j
  simp [varMatrix, var, Pair.mk'_comm i j]

/-- Mean zero (2.1). -/
def MeanZero : Prop := ∀ p, ∫ y, y ∂M.law p = 0

/-- The diagonal entries are real. -/
def DiagReal : Prop := ∀ i : Fin N, ∀ᵐ y ∂M.law (Pair.mk' i i), RCLike.im y = 0

/-- Assumption (A) (2.2). -/
def AssumptionA : Prop := ∀ j, ∑ i, M.var i j = 1

/-- Assumption (B) as the quadratic-form bound on `𝐞^⊥`. -/
def AssumptionB (δm δp : ℝ) : Prop :=
  ∀ v : Fin N → ℝ, ∑ i, v i = 0 →
    (-1 + δm) * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (M.varMatrix *ᵥ v) ∧
      v ⬝ᵥ (M.varMatrix *ᵥ v) ≤ (1 - δp) * ∑ i, v i ^ 2

/-- Assumption (B) as printed (2.3): `1` is a simple eigenvalue of `B` and
`Spec B ⊆ [-1 + δ₋, 1 - δ₊] ∪ {1}`. -/
def AssumptionBSpec (δm δp : ℝ) : Prop :=
  ∃ k, M.varMatrix_isHermitian.eigenvalues k = 1 ∧
    ∀ k' ≠ k, M.varMatrix_isHermitian.eigenvalues k' ∈ Set.Icc (-1 + δm) (1 - δp)

/-- Assumption (C) (2.4). -/
def AssumptionC (C₀ : ℝ) : Prop := ∀ i j, M.var i j ≤ C₀ / N

/-- Uniform subexponential decay (2.17). -/
def SubexpDecay (ϑ : ℝ) : Prop :=
  ∀ p, ∀ x : ℝ, 1 ≤ x →
    M.law p {y | x * Real.sqrt (M.varPair p) < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))

/-- The hypotheses of Theorems 2.1 and 2.2: (2.1), real diagonal, (A), (B), (C), (2.17). -/
structure Assumptions (ϑ δm δp C₀ : ℝ) : Prop where
  meanZero : M.MeanZero
  diagReal : M.DiagReal
  sumA : M.AssumptionA
  specB : M.AssumptionB δm δp
  boundC : M.AssumptionC C₀
  subexp : M.SubexpDecay ϑ

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

/-- The moment-matching condition (2.40) for `l + u ≤ 2`, on the laws of `h_ij`. -/
def MomentMatch2 (Mv Mw : Ensemble 𝕜 N) : Prop :=
  ∀ p, ∀ l u : ℕ, l + u ≤ 2 →
    ∫ y, star y ^ l * y ^ u ∂Mv.law p = ∫ y, star y ^ l * y ^ u ∂Mw.law p

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
