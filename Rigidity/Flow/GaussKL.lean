import Rigidity.Flow.Gaussian
import Rigidity.Flow.Mehler

/-!
# Relative entropy of Gaussian measures and along the Ornstein–Uhlenbeck flow

For a finite-dimensional real inner product space `E` of dimension `d` and a variance `v`
(the `σ²` of §14.3), this file proves Lemma 14.H. Part (a) is the closed form
`S(N(m, σ² s) | g) = (d/2)(s - 1 - log s) + |m|²/(2σ²)` for the relative entropy of a translated
Gaussian with respect to `g = g_v`. Part (b) is the bound for the law `ρ_u` of §14.3 started from a
probability measure `ρ` with finite second moment: it follows from (a), the convexity of
`t ↦ t log t - t + 1` (Jensen's inequality for the density `Ψ(u, ·) = ∫ K(u, ·, w) ρ(dw)`) and the
identity `K(u, ·, w) g = N(a_u w, σ² s_u)` of Lemma 14.E(a).

Statement numbers refer to the blueprint NP v1.1; a result of Erdős–Yau–Yin (arXiv:1007.4652) is
cited as [EYY, …]. The relative entropy `S(ν | ν')` is Mathlib's `InformationTheory.klDiv`, which
agrees with it for probability measures.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section Mehler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

attribute [local instance] gaussE_isProbabilityMeasure

/-! ### Translates of Gaussian measures -/

omit [MeasurableSpace E] [BorelSpace E] in
private lemma gaussKL_gaussDens_pos {v : ℝ} (hv : 0 < v) (y : E) : 0 < gaussDens E v y := by
  unfold gaussDens; positivity

omit [MeasurableSpace E] [BorelSpace E] in
private lemma gaussKL_gaussDens_continuous (v : ℝ) : Continuous (gaussDens E v) := by
  unfold gaussDens; fun_prop

private lemma gaussKL_measurable_ofReal_gaussDens (v : ℝ) (m : E) :
    Measurable fun y : E => ENNReal.ofReal (gaussDens E v (y - m)) :=
  ENNReal.measurable_ofReal.comp
    ((gaussKL_gaussDens_continuous (E := E) v).comp (continuous_id.sub continuous_const)).measurable

/-- Lemma 14.A(c): the translate of `g_v` by `m` is `γ_v(· - m) λ_E`. -/
private lemma gaussKL_map_add_eq_withDensity {v : ℝ} (hv : 0 < v) (m : E) :
    (gaussE E v).map (fun z => m + z) =
      volume.withDensity fun y => ENNReal.ofReal (gaussDens E v (y - m)) := by
  have hd0 : Measurable fun y : E => ENNReal.ofReal (gaussDens E v y) := by
    simpa using gaussKL_measurable_ofReal_gaussDens (E := E) v 0
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF (measurable_const_add m), gaussE_eq_withDensity hv,
    lintegral_withDensity_eq_lintegral_mul _ hd0
      (show Measurable fun x => F (m + x) from hF.comp (measurable_const_add m)),
    lintegral_withDensity_eq_lintegral_mul _ (gaussKL_measurable_ofReal_gaussDens v m) hF,
    ← lintegral_add_left_eq_self (fun y => ((fun y => ENNReal.ofReal (gaussDens E v (y - m))) *
      F) y) m]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, add_sub_cancel_left]

/-- A density `f` with `f γ_v = γ_{vs}(· - m)` turns `g_v` into the translate of `g_{vs}` by `m`. -/
private lemma gaussKL_withDensity_eq_map_add {v s : ℝ} (hv : 0 < v) (hs : 0 < s) {f : E → ℝ}
    (hf : Measurable f) (m : E)
    (h : ∀ y, f y * gaussDens E v y = gaussDens E (v * s) (y - m)) :
    (gaussE E v).withDensity (fun y => ENNReal.ofReal (f y)) =
      (gaussE E (v * s)).map (fun z => m + z) := by
  have hd0 : Measurable fun y : E => ENNReal.ofReal (gaussDens E v y) := by
    simpa using gaussKL_measurable_ofReal_gaussDens (E := E) v 0
  rw [gaussKL_map_add_eq_withDensity (mul_pos hv hs), gaussE_eq_withDensity hv,
    ← withDensity_mul _ hd0 (show Measurable fun y => ENNReal.ofReal (f y) from
      ENNReal.measurable_ofReal.comp hf)]
  congr 1
  funext y
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (gaussKL_gaussDens_pos hv y).le, mul_comm, h]

/-! ### Relative entropy of a density against `g_v` -/

/-- For a measurable density `f ≥ 0` giving a finite measure, `S(f ν | ν) = ∫ h̃(f) dν` with
`h̃(t) = t log t - t + 1`. -/
private lemma gaussKL_klDiv_withDensity {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    [IsFiniteMeasure (ν.withDensity fun y => ENNReal.ofReal (f y))] :
    InformationTheory.klDiv (ν.withDensity fun y => ENNReal.ofReal (f y)) ν =
      ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (f y)) ∂ν := by
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity ν (show Measurable fun y => ENNReal.ofReal (f y) from
    ENNReal.measurable_ofReal.comp hf)] with y hy
  rw [hy, ENNReal.toReal_ofReal (hf0 y)]

/-! ### Lemma 14.H(a) -/

/-- Lemma 14.B(f): `|z|²` is integrable under `g_w`. -/
private lemma gaussKL_integrable_norm_sq (w : ℝ) :
    Integrable (fun z : E => ‖z‖ ^ 2) (gaussE E w) := by
  simpa [Real.rpow_two] using integrable_norm_rpow_gaussE (E := E) w 2 zero_le_two

/-- `⟨m, z⟩` is integrable under `g_w`. -/
private lemma gaussKL_integrable_inner (w : ℝ) (m : E) :
    Integrable (fun z : E => inner ℝ m z) (gaussE E w) := by
  refine ((integrable_norm_rpow_gaussE (E := E) w 1 zero_le_one).const_mul ‖m‖).mono'
    (by fun_prop) (ae_of_all _ fun z => ?_)
  simpa [Real.rpow_one] using norm_inner_le_norm (𝕜 := ℝ) m z

/-- `g_w` is centred: `∫ ⟨m, z⟩ g_w(dz) = 0`. -/
private lemma gaussKL_integral_inner (w : ℝ) (m : E) : ∫ z, inner ℝ m z ∂gaussE E w = 0 := by
  unfold gaussE
  rw [integral_map (measurable_const_smul _).aemeasurable (by fun_prop)]
  simp_rw [inner_smul_right]
  rw [integral_const_mul]
  have h := ProbabilityTheory.integral_strongDual_stdGaussian (innerSL ℝ m)
  simp only [innerSL_apply_apply] at h
  rw [h, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `log (γ_{vs}(y - m) / γ_v(y)) = -(d/2) log s + |y|²/(2v) - |y - m|²/(2vs)`. -/
private lemma gaussKL_log_ratio {v s : ℝ} (hv : 0 < v) (hs : 0 < s) (m y : E) :
    Real.log (gaussDens E (v * s) (y - m) / gaussDens E v y) =
      -(Module.finrank ℝ E / 2 : ℝ) * Real.log s + ‖y‖ ^ 2 / (2 * v) -
        ‖y - m‖ ^ 2 / (2 * (v * s)) := by
  have h1 : 0 < 2 * π * v := by positivity
  have h2 : 0 < 2 * π * (v * s) := by positivity
  have hlog : Real.log (2 * π * (v * s)) = Real.log (2 * π * v) + Real.log s := by
    rw [show 2 * π * (v * s) = 2 * π * v * s by ring, Real.log_mul h1.ne' hs.ne']
  unfold gaussDens
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow h1, Real.log_rpow h2,
    Real.log_exp, Real.log_exp, hlog]
  ring

/-- Lemma 14.H(a): for `m ∈ E` and `s > 0`, the relative entropy of `N(m, σ² s)`, the translate of
`g_{σ² s}` by `m`, with respect to `g = g_{σ²}` is `(d/2)(s - 1 - log s) + |m|²/(2σ²)`
(`σ² = v`, `d = dim E`). -/
theorem klDiv_gaussE_affine {v : ℝ} (hv : 0 < v) {s : ℝ} (hs : 0 < s) (m : E) :
    InformationTheory.klDiv ((gaussE E (v * s)).map fun z => m + z) (gaussE E v) =
      ENNReal.ofReal (Module.finrank ℝ E / 2 * (s - 1 - Real.log s) + ‖m‖ ^ 2 / (2 * v)) := by
  set ϰ : Measure E := (gaussE E (v * s)).map fun z => m + z with hϰ
  have : IsProbabilityMeasure ϰ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_const_add m).aemeasurable).2 inferInstance
  set f : E → ℝ := fun y => gaussDens E (v * s) (y - m) / gaussDens E v y with hf
  have hfm : Measurable f :=
    ((gaussKL_gaussDens_continuous (v * s)).comp
      (continuous_id.sub continuous_const)).measurable.div
      (gaussKL_gaussDens_continuous v).measurable
  have hfpos : ∀ y, 0 < f y := fun y =>
    div_pos (gaussKL_gaussDens_pos (mul_pos hv hs) _) (gaussKL_gaussDens_pos hv y)
  have hden : (gaussE E v).withDensity (fun y => ENNReal.ofReal (f y)) = ϰ :=
    gaussKL_withDensity_eq_map_add hv hs hfm m fun y => by
      rw [hf]
      exact div_mul_cancel₀ _ (gaussKL_gaussDens_pos hv y).ne'
  have hac : ϰ ≪ gaussE E v := hden ▸ withDensity_absolutelyContinuous _ _
  have hllr : llr ϰ (gaussE E v) =ᵐ[ϰ] fun y => Real.log (f y) := by
    refine hac.ae_le ?_
    rw [← hden]
    filter_upwards [Measure.rnDeriv_withDensity (gaussE E v)
      (show Measurable fun y => ENNReal.ofReal (f y) from
        ENNReal.measurable_ofReal.comp hfm)] with y hy
    change Real.log _ = _
    rw [hy, ENNReal.toReal_ofReal (hfpos y).le]
  -- `log f (m + z)` as a quadratic polynomial in `z`
  set c₀ : ℝ := -(Module.finrank ℝ E / 2 : ℝ) * Real.log s + ‖m‖ ^ 2 / (2 * v) with hc₀
  set c₂ : ℝ := 1 / (2 * v) - 1 / (2 * (v * s)) with hc₂
  have hq : ∀ z : E, Real.log (f (m + z)) = c₀ + (1 / v) * inner ℝ m z + c₂ * ‖z‖ ^ 2 := by
    intro z
    rw [hf]
    simp only
    rw [gaussKL_log_ratio hv hs, add_sub_cancel_left, norm_add_sq_real, hc₀, hc₂]
    ring
  have hqint : Integrable (fun z : E => c₀ + (1 / v) * inner ℝ m z + c₂ * ‖z‖ ^ 2)
      (gaussE E (v * s)) :=
    ((integrable_const c₀).add ((gaussKL_integrable_inner (v * s) m).const_mul _)).add
      ((gaussKL_integrable_norm_sq (v * s)).const_mul _)
  have hmeas : AEStronglyMeasurable (fun y => Real.log (f y)) ϰ :=
    (Real.measurable_log.comp hfm).aestronglyMeasurable
  have hint : Integrable (fun y => Real.log (f y)) ϰ := by
    rw [hϰ, integrable_map_measure (hϰ ▸ hmeas) (measurable_const_add m).aemeasurable]
    simpa [Function.comp_def, hq] using hqint
  have hI : ∫ y, Real.log (f y) ∂ϰ =
      Module.finrank ℝ E / 2 * (s - 1 - Real.log s) + ‖m‖ ^ 2 / (2 * v) := by
    rw [hϰ, integral_map (measurable_const_add m).aemeasurable (hϰ ▸ hmeas)]
    simp_rw [hq]
    have h1 : Integrable (fun z : E => c₀ + (1 / v) * inner ℝ m z) (gaussE E (v * s)) :=
      (integrable_const c₀).add ((gaussKL_integrable_inner (v * s) m).const_mul _)
    rw [integral_add h1 ((gaussKL_integrable_norm_sq (v * s)).const_mul _),
      integral_add (integrable_const c₀) ((gaussKL_integrable_inner (v * s) m).const_mul _),
      integral_const, integral_const_mul, integral_const_mul, gaussKL_integral_inner,
      integral_norm_sq_gaussE (mul_pos hv hs).le]
    simp only [probReal_univ, one_smul, mul_zero, add_zero, hc₀, hc₂]
    field_simp
    ring
  rw [InformationTheory.klDiv_of_ac_of_integrable hac ((integrable_congr hllr).2 hint),
    integral_congr_ae hllr, hI]
  simp [Measure.real]

/-! ### Lemma 14.H(b) -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Mehler kernel is jointly continuous. -/
private lemma gaussKL_kernel_continuous (v u : ℝ) :
    Continuous fun p : E × E => mehlerKernel v u p.1 p.2 := by
  unfold mehlerKernel; fun_prop

private lemma gaussKL_ouS_pos {u : ℝ} (hu : 0 < u) : 0 < ouS u := by
  rw [ouS, sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)

private lemma gaussKL_ouS_lt_one {u : ℝ} : ouS u < 1 := by
  rw [ouS]; linarith [Real.exp_pos (-u)]

private lemma gaussKL_ouA_sq (u : ℝ) : ouA u ^ 2 = Real.exp (-u) := by
  rw [ouA, ← Real.exp_nat_mul]; congr 1; push_cast; ring

omit [FiniteDimensional ℝ E] in
/-- For fixed `y`, `K(u, y, ·)` is `ρ`-integrable: it is continuous, positive and bounded. -/
private lemma gaussKL_integrable_kernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (y : E) : Integrable (fun w => mehlerKernel v u y w) ρ :=
  Integrable.of_bound
    ((gaussKL_kernel_continuous v u).comp (Continuous.prodMk_right y)).aestronglyMeasurable
    (ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)))
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (mehlerKernel_pos v hu y w)]
      exact mehlerKernel_le hv hu y w)

omit [FiniteDimensional ℝ E] in
/-- For fixed `y`, `h̃(K(u, y, ·))` is `ρ`-integrable. -/
private lemma gaussKL_integrable_klFun_kernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u)
    (ρ : Measure E) [IsProbabilityMeasure ρ] (y : E) :
    Integrable (fun w => InformationTheory.klFun (mehlerKernel v u y w)) ρ := by
  set C : ℝ := ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (‖y‖ ^ 2 / (2 * v))
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := C)).exists_bound_of_continuousOn
    InformationTheory.continuous_klFun.continuousOn
  exact Integrable.of_bound
    (InformationTheory.continuous_klFun.comp
      ((gaussKL_kernel_continuous v u).comp (Continuous.prodMk_right y))).aestronglyMeasurable B
    (ae_of_all _ fun w => hB _ ⟨(mehlerKernel_pos v hu y w).le, mehlerKernel_le hv hu y w⟩)

omit [FiniteDimensional ℝ E] in
/-- Jensen's inequality for `h̃(t) = t log t - t + 1` and `Ψ(u, y) = ∫ K(u, y, w) ρ(dw)`. -/
private lemma gaussKL_jensen {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (y : E) :
    InformationTheory.klFun (ouDensity v ρ u y) ≤
      ∫ w, InformationTheory.klFun (mehlerKernel v u y w) ∂ρ :=
  ConvexOn.map_integral_le InformationTheory.convexOn_klFun
    InformationTheory.continuous_klFun.continuousOn isClosed_Ici
    (ae_of_all _ fun w => (mehlerKernel_pos v hu y w).le) (gaussKL_integrable_kernel hv hu ρ y)
    (gaussKL_integrable_klFun_kernel hv hu ρ y)

/-- `∫ h̃(K(u, y, w)) g_v(dy) = S(N(a_u w, σ² s_u) | g)`, by Lemma 14.E(a) and Lemma 14.H(a). -/
private lemma gaussKL_lintegral_klFun_kernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (w : E) :
    ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (mehlerKernel v u y w)) ∂gaussE E v =
      ENNReal.ofReal (Module.finrank ℝ E / 2 * (ouS u - 1 - Real.log (ouS u)) +
        Real.exp (-u) * ‖w‖ ^ 2 / (2 * v)) := by
  have hs := gaussKL_ouS_pos hu
  have hfc : Continuous fun y : E => mehlerKernel v u y w :=
    (gaussKL_kernel_continuous v u).comp (Continuous.prodMk_left w)
  have hden : (gaussE E v).withDensity (fun y => ENNReal.ofReal (mehlerKernel v u y w)) =
      (gaussE E (v * ouS u)).map (fun z => ouA u • w + z) :=
    gaussKL_withDensity_eq_map_add hv hs hfc.measurable (ouA u • w)
      fun y => mehlerKernel_mul_gaussDens' hv hu y w
  have : IsFiniteMeasure
      ((gaussE E v).withDensity fun y => ENNReal.ofReal (mehlerKernel v u y w)) := by
    rw [hden]
    have := (Measure.isProbabilityMeasure_map_iff (μ := gaussE E (v * ouS u))
      (measurable_const_add (ouA u • w)).aemeasurable).2 inferInstance
    infer_instance
  rw [← gaussKL_klDiv_withDensity (gaussE E v) hfc.measurable
    fun y => (mehlerKernel_pos v hu y w).le, hden, klDiv_gaussE_affine hv hs]
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, gaussKL_ouA_sq]

/-- Lemma 14.H(b): Gaussian relative entropy of `ρ_u`. -/
theorem klDiv_ouLaw_le {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (hρ : Integrable (fun w => ‖w‖ ^ 2) ρ) :
    InformationTheory.klDiv (ouLaw v ρ u) (gaussE E v) ≤
      ENNReal.ofReal (Module.finrank ℝ E / 2 * Real.log (1 / (1 - Real.exp (-u))) +
        Real.exp (-u) * (∫ w, ‖w‖ ^ 2 ∂ρ) / (2 * v)) := by
  have hs := gaussKL_ouS_pos hu
  have hs1 : ouS u < 1 := gaussKL_ouS_lt_one
  have hd : (0 : ℝ) ≤ Module.finrank ℝ E / 2 := by positivity
  set c : ℝ := Module.finrank ℝ E / 2 * (ouS u - 1 - Real.log (ouS u)) with hc
  have hc0 : 0 ≤ c := by
    refine mul_nonneg hd ?_
    linarith [Real.log_le_sub_one_of_pos hs]
  obtain ⟨hlaw, hpos⟩ := ouLaw_eq_withDensity hv hu ρ
  have hΨm : Measurable (ouDensity v ρ u) :=
    (StronglyMeasurable.integral_prod_right (f := fun y w => mehlerKernel v u y w)
      (gaussKL_kernel_continuous v u).stronglyMeasurable).measurable
  have : IsFiniteMeasure
      ((gaussE E v).withDensity fun y => ENNReal.ofReal (ouDensity v ρ u y)) := by
    rw [← hlaw]
    unfold ouLaw
    infer_instance
  have hK : Measurable fun p : E × E =>
      ENNReal.ofReal (InformationTheory.klFun (mehlerKernel v u p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp
      (InformationTheory.continuous_klFun.comp (gaussKL_kernel_continuous v u)).measurable
  rw [hlaw, gaussKL_klDiv_withDensity (gaussE E v) hΨm fun y => (hpos y).le]
  calc ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (ouDensity v ρ u y)) ∂gaussE E v
      ≤ ∫⁻ y, ENNReal.ofReal (∫ w, InformationTheory.klFun (mehlerKernel v u y w) ∂ρ)
          ∂gaussE E v :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (gaussKL_jensen hv hu ρ y)
    _ = ∫⁻ y, ∫⁻ w, ENNReal.ofReal (InformationTheory.klFun (mehlerKernel v u y w)) ∂ρ
          ∂gaussE E v :=
        lintegral_congr fun y => ofReal_integral_eq_lintegral_ofReal
          (gaussKL_integrable_klFun_kernel hv hu ρ y)
          (ae_of_all _ fun w => InformationTheory.klFun_nonneg (mehlerKernel_pos v hu y w).le)
    _ = ∫⁻ w, ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun (mehlerKernel v u y w))
          ∂gaussE E v ∂ρ :=
        lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ w, ENNReal.ofReal (c + Real.exp (-u) / (2 * v) * ‖w‖ ^ 2) ∂ρ :=
        lintegral_congr fun w => by
          rw [gaussKL_lintegral_klFun_kernel hv hu w, ← hc]
          congr 2
          ring
    _ = ENNReal.ofReal (∫ w, (c + Real.exp (-u) / (2 * v) * ‖w‖ ^ 2) ∂ρ) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrable_const c).add (hρ.const_mul _))
          (ae_of_all _ fun w => add_nonneg hc0 (by positivity))).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (integrable_const c) (hρ.const_mul _), integral_const,
          integral_const_mul, probReal_univ, one_smul, one_div, Real.log_inv, hc]
        have hsu : 1 - Real.exp (-u) = ouS u := rfl
        rw [hsu]
        have h3 : Module.finrank ℝ E / 2 * (ouS u - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hd (by linarith)
        rw [mul_div_right_comm (Real.exp (-u))]
        nlinarith

end Mehler

end Rigidity
