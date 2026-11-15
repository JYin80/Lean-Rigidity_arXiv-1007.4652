import Mathlib

/-!
# Gaussian measures on a Euclidean space

`gaussE E v` is the centred Gaussian measure on a finite-dimensional real inner product space `E`
with covariance `v · Id` (Definition 14.A), obtained from Mathlib's `stdGaussian E` by the scaling
`z ↦ √v z`. For `v > 0` it has density `gaussDens E v` with respect to the Lebesgue measure of `E`.
The file proves the properties of Lemma 14.B (probability measure, density, invariance under
linear isometries, closure under independent linear combinations, moments) and the one-dimensional
Gaussian tail bound of Lemma 13.B(a).

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real
open scoped ENNReal NNReal

namespace Rigidity

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Definition 14.A: the centred Gaussian measure `g_v` on `E` with covariance `v · Id`
(the image of `stdGaussian E` under `z ↦ √v z`; `g_0 = δ_0`). -/
noncomputable def gaussE (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (v : ℝ) : Measure E :=
  (ProbabilityTheory.stdGaussian E).map fun z => Real.sqrt v • z

/-- The Gaussian density `γ_v(y) = (2πv)^{-d/2} exp(-|y|²/(2v))` (Definition 14.A). -/
noncomputable def gaussDens (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (v : ℝ) (y : E) : ℝ :=
  (2 * π * v) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (2 * v))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Scaling identity `‖√v t‖² = v ‖t‖²` for `v ≥ 0`. -/
private lemma gaussE_norm_sq_smul {v : ℝ} (hv : 0 ≤ v) (t : E) :
    ‖Real.sqrt v • t‖ ^ 2 = v * ‖t‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hv]

/-- The characteristic function of `g_v` is `t ↦ exp (-v |t|² / 2)`, for `v ≥ 0`. -/
private lemma gaussE_charFun {v : ℝ} (hv : 0 ≤ v) (t : E) :
    charFun (gaussE E v) t = Complex.exp (-((v * ‖t‖ ^ 2 / 2 : ℝ) : ℂ)) := by
  unfold gaussE
  rw [charFun_map_smul, ProbabilityTheory.charFun_stdGaussian]
  congr 1
  have h : ((‖Real.sqrt v • t‖ : ℝ) : ℂ) ^ 2 = (v : ℂ) * (‖t‖ : ℂ) ^ 2 := by
    exact_mod_cast gaussE_norm_sq_smul hv t
  rw [h]
  push_cast
  ring

/-- The standard Gaussian measure of `E` has second moment `finrank ℝ E`. -/
private lemma gaussE_integral_norm_sq_std :
    ∫ z, ‖z‖ ^ 2 ∂ProbabilityTheory.stdGaussian E = Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have hint : ∀ i, Integrable (fun z : E => (inner ℝ (b i) z) ^ 2)
      (ProbabilityTheory.stdGaussian E) := by
    intro i
    have := (ProbabilityTheory.IsGaussian.memLp_dual (ProbabilityTheory.stdGaussian E)
      (innerSL ℝ (b i)) 2 (by simp)).integrable_sq
    simpa [innerSL_apply_apply] using this
  have hL : ∀ i, ∫ z, (inner ℝ (b i) z) ^ 2 ∂(ProbabilityTheory.stdGaussian E) = 1 := by
    intro i
    have h := ProbabilityTheory.variance_dual_stdGaussian (E := E) (innerSL ℝ (b i))
    rw [ProbabilityTheory.variance_of_integral_eq_zero (by fun_prop)
      (ProbabilityTheory.integral_strongDual_stdGaussian _)] at h
    simpa [innerSL_apply_apply, innerSL_apply_norm] using h
  calc ∫ z, ‖z‖ ^ 2 ∂ProbabilityTheory.stdGaussian E
      = ∫ z, ∑ i, (inner ℝ (b i) z) ^ 2 ∂ProbabilityTheory.stdGaussian E := by
        simp_rw [b.sum_sq_inner_right]
    _ = ∑ i, ∫ z, (inner ℝ (b i) z) ^ 2 ∂ProbabilityTheory.stdGaussian E :=
        (integral_finsetSum _ fun i _ => hint i)
    _ = Module.finrank ℝ E := by simp [hL]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The Gaussian density is nonnegative for `v > 0`. -/
private lemma gaussDens_nonneg {v : ℝ} (hv : 0 < v) (y : E) : 0 ≤ gaussDens E v y := by
  unfold gaussDens
  positivity

omit [MeasurableSpace E] [BorelSpace E] in
/-- The Gaussian density is continuous in `y`. -/
private lemma gaussDens_continuous (v : ℝ) : Continuous (gaussDens E v) := by
  unfold gaussDens
  fun_prop

/-- The Gaussian density is Lebesgue integrable for `v > 0`. -/
private lemma gaussDens_integrable {v : ℝ} (hv : 0 < v) : Integrable (gaussDens E v) := by
  have hb : (0 : ℝ) < 1 / (2 * v) := by positivity
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
    (b := ((1 / (2 * v) : ℝ) : ℂ)) (by simpa using hb) 0 0).norm
  have h2 : (fun y : E => ‖Complex.exp (-((1 / (2 * v) : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2 +
      0 * ((inner ℝ (0 : E) y : ℝ) : ℂ))‖) = fun y => Real.exp (-‖y‖ ^ 2 / (2 * v)) := by
    ext y
    rw [Complex.norm_exp]
    congr 1
    simp only [zero_mul, add_zero]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp
  rw [h2] at h
  exact h.const_mul _

/-- Lemma 14.B(a). -/
theorem gaussE_isProbabilityMeasure (v : ℝ) : IsProbabilityMeasure (gaussE E v) := by
  unfold gaussE
  exact (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).2
    inferInstance

/-- Lemma 14.B(a), (c): for `v > 0`, `g_v = γ_v · λ_E`. -/
theorem gaussE_eq_withDensity {v : ℝ} (hv : 0 < v) :
    gaussE E v = volume.withDensity fun y => ENNReal.ofReal (gaussDens E v y) := by
  have hint := gaussDens_integrable (E := E) hv
  have hfin : IsFiniteMeasure
      (volume.withDensity fun y : E => ENNReal.ofReal (gaussDens E v y)) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  have := gaussE_isProbabilityMeasure (E := E) v
  have hm : Measurable fun y : E => ENNReal.ofReal (gaussDens E v y) :=
    ENNReal.measurable_ofReal.comp (gaussDens_continuous (E := E) v).measurable
  apply Measure.ext_of_charFun
  ext t
  rw [gaussE_charFun hv.le, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  set X : ℝ := 2 * π * v with hX
  have hXpos : 0 < X := by positivity
  have h1 : ∀ y : E, (ENNReal.ofReal (gaussDens E v y)).toReal •
      Complex.exp ((inner ℝ y t : ℝ) * Complex.I) =
      ((X ^ (-(Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-((1 / (2 * v) : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2 +
          Complex.I * ((inner ℝ t y : ℝ) : ℂ)) := by
    intro y
    rw [ENNReal.toReal_ofReal (gaussDens_nonneg hv y), Complex.real_smul, gaussDens, ← hX,
      Complex.ofReal_mul, mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm y t]
    congr 1
    push_cast
    field_simp
  simp_rw [h1]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (b := ((1 / (2 * v) : ℝ) : ℂ)) (by simpa using (by positivity : (0 : ℝ) < 1 / (2 * v)))]
  have hb : (Real.pi : ℂ) / ((1 / (2 * v) : ℝ) : ℂ) = (X : ℂ) := by
    rw [hX]
    have : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    push_cast
    field_simp
  have hd : ((Module.finrank ℝ E : ℕ) : ℂ) / 2 = (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hpow : ((X ^ (-(Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) *
      (X : ℂ) ^ (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_cpow hXpos.le, ← Complex.ofReal_mul, ← Real.rpow_add hXpos]
    have : -(Module.finrank ℝ E : ℝ) / 2 + (Module.finrank ℝ E : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero, Complex.ofReal_one]
  rw [hb, hd, ← mul_assoc, hpow, one_mul]
  congr 1
  have : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-- Lemma 14.B(b): invariance under linear isometries. -/
theorem gaussE_map_isometry (v : ℝ) (f : E ≃ₗᵢ[ℝ] E) : (gaussE E v).map f = gaussE E v := by
  unfold gaussE
  have hs : Measurable fun z : E => Real.sqrt v • z := measurable_const_smul _
  have hf : Measurable f := f.continuous.measurable
  rw [Measure.map_map hf hs]
  have : ((fun z : E => f z) ∘ fun z : E => Real.sqrt v • z) =
      (fun z : E => Real.sqrt v • z) ∘ f := by
    ext z; simp
  rw [this, ← Measure.map_map hs hf, ProbabilityTheory.stdGaussian_map f]

/-- Lemma 14.B(e): `α Y + β Z ∼ g_{(α²+β²) v}` for independent `Y, Z ∼ g_v`. -/
theorem gaussE_prod_map_add {v : ℝ} (hv : 0 ≤ v) (α β : ℝ) :
    ((gaussE E v).prod (gaussE E v)).map (fun p => α • p.1 + β • p.2) =
      gaussE E ((α ^ 2 + β ^ 2) * v) := by
  have := gaussE_isProbabilityMeasure (E := E) v
  have := gaussE_isProbabilityMeasure (E := E) ((α ^ 2 + β ^ 2) * v)
  have hm : Measurable (fun p : E × E => α • p.1 + β • p.2) := by fun_prop
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  have h1 : ∀ p : E × E, Complex.exp ((inner ℝ (α • p.1 + β • p.2) t : ℝ) * Complex.I) =
      Complex.exp ((inner ℝ p.1 (α • t) : ℝ) * Complex.I) *
        Complex.exp ((inner ℝ p.2 (β • t) : ℝ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right]
    push_cast
    ring_nf
  simp_rw [h1]
  rw [integral_prod_mul (fun x : E => Complex.exp ((inner ℝ x (α • t) : ℝ) * Complex.I))
    (fun x : E => Complex.exp ((inner ℝ x (β • t) : ℝ) * Complex.I))]
  rw [← charFun_apply, ← charFun_apply, gaussE_charFun hv, gaussE_charFun hv,
    gaussE_charFun (by positivity), ← Complex.exp_add]
  congr 1
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  push_cast
  ring

/-- Lemma 14.B(f): `E|Y|² = d v`. -/
theorem integral_norm_sq_gaussE {v : ℝ} (hv : 0 ≤ v) :
    ∫ y, ‖y‖ ^ 2 ∂gaussE E v = Module.finrank ℝ E * v := by
  unfold gaussE
  rw [integral_map (measurable_const_smul _).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [gaussE_norm_sq_smul hv]
  rw [integral_const_mul, gaussE_integral_norm_sq_std, mul_comm]

/-- Lemma 14.B(f): finite moments of every order. -/
theorem integrable_norm_rpow_gaussE (v p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun y => ‖y‖ ^ p) (gaussE E v) := by
  unfold gaussE
  rw [integrable_map_measure (Continuous.aestronglyMeasurable (by fun_prop))
    (measurable_const_smul _).aemeasurable]
  have h : ((fun y : E => ‖y‖ ^ p) ∘ fun z : E => Real.sqrt v • z) =
      fun z : E => Real.sqrt v ^ p * ‖z‖ ^ p := by
    ext z
    simp only [Function.comp_apply]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg v),
      Real.mul_rpow (Real.sqrt_nonneg v) (norm_nonneg z)]
  rw [h]
  rcases hp.eq_or_lt with rfl | hp'
  · simp
  · have := (ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian E)
      (ENNReal.ofReal p) ENNReal.ofReal_ne_top).integrable_norm_rpow
      (by simpa using hp') ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp, id_eq] at this
    exact this.const_mul _

/-- Lemma 13.B(a): Gaussian tail. -/
theorem gaussianReal_tail (v : ℝ≥0) {y : ℝ} (hy : 0 ≤ y) :
    ProbabilityTheory.gaussianReal 0 v {x | y * Real.sqrt v < |x|} ≤
      ENNReal.ofReal (2 * Real.exp (-y ^ 2 / 2)) := by
  by_cases hv : v = 0
  · subst hv
    rw [ProbabilityTheory.gaussianReal_zero_var,
      Measure.dirac_apply' _ (measurableSet_lt measurable_const (by fun_prop))]
    simp
  · have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
    set τ : ℝ := Real.sqrt v with hτ
    have hτpos : 0 < τ := Real.sqrt_pos.2 hvpos
    have hτsq : τ ^ 2 = v := Real.sq_sqrt hvpos.le
    set μ := ProbabilityTheory.gaussianReal 0 v with hμ
    have hmgf : ∀ t : ℝ, ProbabilityTheory.mgf id μ t = Real.exp (v * t ^ 2 / 2) := by
      intro t
      rw [hμ, ProbabilityTheory.mgf_id_gaussianReal]
      simp
    have hint : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * id x)) μ := fun t =>
      ProbabilityTheory.integrable_exp_mul_gaussianReal t
    have hup : μ.real {x | y * τ ≤ id x} ≤ Real.exp (-y ^ 2 / 2) := by
      have h := ProbabilityTheory.measure_ge_le_exp_mul_mgf (X := id) (μ := μ)
        (t := y / τ) (y * τ) (div_nonneg hy hτpos.le) (hint _)
      rw [hmgf, ← Real.exp_add] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      field_simp
      rw [← hτsq]
      ring
    have hlow : μ.real {x | id x ≤ -(y * τ)} ≤ Real.exp (-y ^ 2 / 2) := by
      have h := ProbabilityTheory.measure_le_le_exp_mul_mgf (X := id) (μ := μ)
        (t := -(y / τ)) (-(y * τ)) (by simpa using div_nonneg hy hτpos.le) (hint _)
      rw [hmgf, ← Real.exp_add] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      field_simp
      rw [← hτsq]
      ring
    have hsub : {x : ℝ | y * τ < |x|} ⊆ {x | y * τ ≤ id x} ∪ {x | id x ≤ -(y * τ)} := by
      intro x hx
      rcases lt_abs.1 (show y * τ < |x| from hx) with h | h
      · exact Or.inl h.le
      · exact Or.inr (show x ≤ -(y * τ) by linarith)
    calc μ {x : ℝ | y * τ < |x|}
        ≤ μ ({x | y * τ ≤ id x} ∪ {x | id x ≤ -(y * τ)}) := measure_mono hsub
      _ ≤ μ {x | y * τ ≤ id x} + μ {x | id x ≤ -(y * τ)} := measure_union_le _ _
      _ = ENNReal.ofReal (μ.real {x | y * τ ≤ id x}) +
            ENNReal.ofReal (μ.real {x | id x ≤ -(y * τ)}) := by
          rw [ofReal_measureReal, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (Real.exp (-y ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-y ^ 2 / 2)) :=
          add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
      _ = ENNReal.ofReal (2 * Real.exp (-y ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
          congr 1
          ring

end Gaussian

end Rigidity
