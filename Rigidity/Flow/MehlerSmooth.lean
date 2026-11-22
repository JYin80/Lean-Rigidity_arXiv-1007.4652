module

public import Rigidity.Flow.Gaussian
public import Rigidity.Flow.Mehler
public import Rigidity.Flow.MehlerKernelBounds

@[expose] public section

/-!
# Smoothness of the Ornstein–Uhlenbeck densities and of the Mehler semigroup

For a finite-dimensional real inner product space `E`, a variance `v > 0` (the `σ²` of §14.3) and
a probability measure `ρ` on `E` with finite moments of every order, this file proves Lemma 14.2
for the density `Ψ(u, y) = ∫ K(u, y, w) ρ(dw)` of `ρ_u` with respect to `g_v`: (i) `Ψ` is `C^∞`
on `(0, ∞) × E` and solves `∂_u Ψ = A Ψ` for the generator `A = (v/2) Δ - (1/2) ⟨y, ∇⟩` of
(14.1); (ii) the bound on `|log Ψ|`; (iii) an integrable dominating function for the derivatives
`∂_u^j D_y^k Ψ`, `j ≤ 1`, `k ≤ 3`, uniformly in `u ≥ u₁`; (iv) the bound on the Fisher information.
It also proves Lemma 14.3 for the Mehler semigroup `T_u` acting on bounded Borel data:
smoothness, the bound `|T_u Φ| ≤ ‖Φ‖_∞`, the equation `∂_u T_u Φ = A T_u Φ`, and, for continuous
`Φ`, the limits as `u ↓ 0` and `u → ∞`.

Statement numbers refer to the blueprint NP v1.1; a result of Erdős–Yau–Yin (arXiv:1007.4652) is
cited as [EYY, …].
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section Mehler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The generator `A = (v/2) Δ - (1/2) ⟨y, ∇⟩` (14.1). -/
noncomputable def ouGen (v : ℝ) (Φ : E → ℝ) (y : E) : ℝ :=
  v / 2 * Laplacian.laplacian Φ y - 1 / 2 * inner ℝ y (gradient Φ y)

/-- Lemma 14.2(i): `Ψ` is smooth on `(0, ∞) × E` and solves `∂_u Ψ = A Ψ`. -/
theorem ouDensity_smooth_and_eq {v : ℝ} (hv : 0 < v) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => ouDensity v ρ p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∀ u > 0, ∀ y, HasDerivAt (fun u' => ouDensity v ρ u' y)
        (ouGen v (ouDensity v ρ u) y) u := by
  have hh : Measurable fun _ : E => (1 : ℝ) := measurable_const
  have hC : ∀ w : E, |(fun _ : E => (1 : ℝ)) w| ≤ 1 := fun _ => by simp
  refine ⟨?_, fun u hu y => ?_⟩
  · have h := contDiffOn_kernelIntegral hv hρ hh hC
    simp only [mul_one] at h
    exact h
  · have h := mehlerKernelBounds_hasDerivAt_kernelIntegral hv hρ hh hC hu y
    simp only [mul_one] at h
    exact h

/-- Lemma 14.3: bounded continuous data, the two limits. -/
theorem tendsto_mehler {v : ℝ} (hv : 0 < v) {Φ : E → ℝ} (hΦ : Continuous Φ)
    (hb : ∃ C, ∀ y, |Φ y| ≤ C) (y : E) :
    Tendsto (fun u => mehler v u Φ y) (𝓝[>] 0) (𝓝 (Φ y)) ∧
      Tendsto (fun u => mehler v u Φ y) atTop (𝓝 (∫ z, Φ z ∂gaussE E v)) := by
  obtain ⟨C, hC⟩ := hb
  have hA : Continuous ouA := by unfold ouA; fun_prop
  have hS : Continuous fun u => Real.sqrt (ouS u) := by unfold ouS; fun_prop
  have key : ∀ {l : Filter ℝ} [l.IsCountablyGenerated] {a s : ℝ} (f : E → E),
      Tendsto ouA l (𝓝 a) → Tendsto (fun u => Real.sqrt (ouS u)) l (𝓝 s) →
      (∀ z, Φ (a • y + s • z) = Φ (f z)) →
      Tendsto (fun u => mehler v u Φ y) l (𝓝 (∫ z, Φ (f z) ∂gaussE E v)) := by
    intro l _ a s f ha hs hf
    have := gaussE_isProbabilityMeasure (E := E) v
    simp_rw [← hf]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall fun u => (hΦ.comp (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact hC _) (integrable_const C) (ae_of_all _ fun z => ?_)
    exact (hΦ.tendsto _).comp ((ha.smul_const y).add (hs.smul_const z))
  refine ⟨?_, ?_⟩
  · have h := key (l := 𝓝[>] (0 : ℝ)) (a := 1) (s := 0) (fun _ => y)
      (by simpa [ouA] using (hA.tendsto 0).mono_left nhdsWithin_le_nhds)
      (by simpa [ouS] using (hS.tendsto 0).mono_left nhdsWithin_le_nhds) (fun z => by simp)
    have := gaussE_isProbabilityMeasure (E := E) v
    simpa using h
  · refine key (l := atTop) (a := 0) (s := 1) id ?_ ?_ (fun z => by simp)
    · have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
      refine h.congr fun u => ?_
      simp [ouA, neg_div]
    · have h : Tendsto (fun u : ℝ => ouS u) atTop (𝓝 1) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero).const_sub (1 : ℝ)
        simpa [ouS] using this
      have h2 := (Real.continuous_sqrt.tendsto 1).comp h
      rw [Real.sqrt_one] at h2
      exact h2

/-- `g_v` has finite moments of every order. -/
private lemma mehlerSmooth_moments_gaussE (v : ℝ) (m : ℕ) :
    Integrable (fun w : E => ‖w‖ ^ m) (gaussE E v) := by
  simpa [Real.rpow_natCast] using integrable_norm_rpow_gaussE (E := E) v m (Nat.cast_nonneg m)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `0 < s_{u₁} ≤ s_u ≤ 1` for `0 < u₁ ≤ u`. -/
private lemma mehlerSmooth_ouS_bounds {u₁ u : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u) :
    0 < ouS u₁ ∧ ouS u₁ ≤ ouS u ∧ ouS u ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ouS; linarith [Real.exp_lt_one_iff.2 (neg_lt_zero.2 hu₁)]
  · unfold ouS; linarith [Real.exp_le_exp.2 (neg_le_neg hu)]
  · unfold ouS; linarith [Real.exp_pos (-u)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `w ↦ K(u, y, w)` is continuous. -/
private lemma mehlerSmooth_kernel_continuous (v u : ℝ) (y : E) :
    Continuous fun w => mehlerKernel v u y w := by
  unfold mehlerKernel; fun_prop

omit [FiniteDimensional ℝ E] in
/-- `K(u, y, ·)` is integrable for every finite measure (it is bounded and continuous). -/
private lemma mehlerSmooth_integrable_kernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u)
    (ρ : Measure E) [IsFiniteMeasure ρ] (y : E) : Integrable (fun w => mehlerKernel v u y w) ρ :=
  Integrable.of_bound (mehlerSmooth_kernel_continuous v u y).aestronglyMeasurable
    (ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)))
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (mehlerKernel_pos v hu y w)]
      exact mehlerKernel_le hv hu y w)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `u ≥ u₁ > 0` and `|w|² ≤ 2M`: `K(u, y, w) ≥ exp(-(|y|² + 2M) / (v s_{u₁}))`. -/
private lemma mehlerSmooth_kernel_ge {v : ℝ} (hv : 0 < v) {u₁ u : ℝ} (hu₁ : 0 < u₁)
    (hu : u₁ ≤ u) {M : ℝ} (hM : 0 ≤ M) (y w : E) (hw : ‖w‖ ^ 2 ≤ 2 * M) :
    Real.exp (-(‖y‖ ^ 2 + 2 * M) / (v * ouS u₁)) ≤ mehlerKernel v u y w := by
  obtain ⟨hs₁, hs₁s, hs1⟩ := mehlerSmooth_ouS_bounds hu₁ hu
  have hs : 0 < ouS u := hs₁.trans_le hs₁s
  have ha : 0 < ouA u := Real.exp_pos _
  have ha1 : ouA u ^ 2 ≤ 1 := by
    have : ouA u ^ 2 = Real.exp (-u) := by
      rw [ouA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]; exact Real.exp_le_one_iff.2 (by linarith)
  unfold mehlerKernel
  have h1 : 1 ≤ ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1
      (by have := (Module.finrank ℝ E).cast_nonneg (α := ℝ); linarith)
  refine le_trans ?_ (le_mul_of_one_le_left (Real.exp_pos _).le h1)
  refine Real.exp_le_exp.2 ?_
  have hsq : 0 ≤ ‖y + ouA u • w‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hsq
  have hY := sq_nonneg ‖y‖
  have hW := sq_nonneg ‖w‖
  have hnum : -(2 * (‖y‖ ^ 2 + 2 * M)) ≤
      2 * ouA u * inner ℝ y w - ouA u ^ 2 * (‖y‖ ^ 2 + ‖w‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right ha1 hY, mul_le_mul_of_nonneg_right ha1 hW]
  calc -(‖y‖ ^ 2 + 2 * M) / (v * ouS u₁) ≤ -(‖y‖ ^ 2 + 2 * M) / (v * ouS u) := by
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hs₁s hv.le)
    _ = -(2 * (‖y‖ ^ 2 + 2 * M)) / (2 * v * ouS u) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If `M = ∫ |w|² ρ(dw)`, then `ρ(|w|² ≤ 2M) ≥ 1/2` (Chebyshev). -/
private lemma mehlerSmooth_half_le (ρ : Measure E) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun w => ‖w‖ ^ 2) ρ) :
    1 / 2 ≤ ρ.real {w | ‖w‖ ^ 2 ≤ 2 * ∫ w, ‖w‖ ^ 2 ∂ρ} := by
  set M := ∫ w, ‖w‖ ^ 2 ∂ρ
  have hM : 0 ≤ M := integral_nonneg fun w => sq_nonneg _
  have hmeas : MeasurableSet {w : E | 2 * M ≤ ‖w‖ ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  rcases hM.eq_or_lt with h0 | hpos
  · have hz := (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg ‖w‖) h2).1 h0.symm
    have hfull : ρ {w | ‖w‖ ^ 2 ≤ 2 * M}ᶜ = 0 := by
      refine measure_mono_null (fun w hw => ?_) (ae_iff.1 hz)
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, ← h0] at hw ⊢
      simp only [Pi.zero_apply]
      simpa using hw.ne'
    have hmeas' : MeasurableSet {w : E | ‖w‖ ^ 2 ≤ 2 * M} :=
      measurableSet_le (by fun_prop) measurable_const
    have h0' : ρ.real {w | ‖w‖ ^ 2 ≤ 2 * M}ᶜ = 0 := by simp [Measure.real, hfull]
    linarith [probReal_compl_eq_one_sub (μ := ρ) hmeas']
  · have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun w => sq_nonneg ‖w‖) h2 (2 * M)
    have hle : ρ.real {w | 2 * M ≤ ‖w‖ ^ 2} ≤ 1 / 2 := by
      rw [le_div_iff₀ two_pos]
      nlinarith
    have hsub : {w : E | 2 * M ≤ ‖w‖ ^ 2}ᶜ ⊆ {w | ‖w‖ ^ 2 ≤ 2 * M} := fun w hw => by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hw ⊢
      exact hw.le
    have := measureReal_mono (μ := ρ) hsub
    rw [probReal_compl_eq_one_sub hmeas] at this
    linarith

/-- Lemma 14.2(ii): for `0 < u₁ ≤ u` and `y ∈ E`, `|log Ψ(u, y)| ≤ C_log (1 + |y|²)` with
`C_log = log 2 + (d/2) log (1/s_{u₁}) + (1 + 2 M₂') / (v s_{u₁})`, where `d = dim E`,
`M₂' = ∫ |w|² ρ(dw)` and `σ² = v`. -/
theorem abs_log_ouDensity_le {v : ℝ} (hv : 0 < v) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {u₁ : ℝ} (hu₁ : 0 < u₁) {u : ℝ}
    (hu : u₁ ≤ u) (y : E) :
    |Real.log (ouDensity v ρ u y)| ≤
      (Real.log 2 + Module.finrank ℝ E / 2 * Real.log (1 / ouS u₁) +
        (1 + 2 * ∫ w, ‖w‖ ^ 2 ∂ρ) / (v * ouS u₁)) * (1 + ‖y‖ ^ 2) := by
  obtain ⟨hs₁, hs₁s, hs1⟩ := mehlerSmooth_ouS_bounds hu₁ hu
  have hu0 : 0 < u := hu₁.trans_le hu
  have hs : 0 < ouS u := hs₁.trans_le hs₁s
  set M := ∫ w, ‖w‖ ^ 2 ∂ρ with hMdef
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hM : 0 ≤ M := integral_nonneg fun w => sq_nonneg _
  have hΨ : 0 < ouDensity v ρ u y := (ouLaw_eq_withDensity hv hu0 ρ).2 y
  have hint := mehlerSmooth_integrable_kernel hv hu0 ρ y
  set Y := ‖y‖ ^ 2
  have hY : 0 ≤ Y := sq_nonneg _
  -- upper bound
  have hup : ouDensity v ρ u y ≤ ouS u₁ ^ (-d / 2) * Real.exp (Y / (2 * v)) := by
    have h := integral_mono hint (integrable_const (ouS u₁ ^ (-d / 2) * Real.exp (Y / (2 * v))))
      fun w => (mehlerKernel_le hv hu0 y w).trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hs₁ hs₁s (by linarith)) (Real.exp_pos _).le)
    rwa [integral_const, probReal_univ, one_smul] at h
  have hlogup : Real.log (ouDensity v ρ u y) ≤ d / 2 * Real.log (1 / ouS u₁) + Y / (2 * v) := by
    refine (Real.log_le_log hΨ hup).trans_eq ?_
    rw [Real.log_mul (Real.rpow_pos_of_pos hs₁ _).ne' (Real.exp_pos _).ne', Real.log_rpow hs₁,
      Real.log_exp, one_div, Real.log_inv]
    ring
  -- lower bound
  set c := Real.exp (-(Y + 2 * M) / (v * ouS u₁))
  have hR : MeasurableSet {w : E | ‖w‖ ^ 2 ≤ 2 * M} :=
    measurableSet_le (by fun_prop) measurable_const
  have hlow : c / 2 ≤ ouDensity v ρ u y := by
    have h1 := setIntegral_ge_of_const_le (c := c) hR (measure_ne_top _ _)
      (fun w hw => mehlerSmooth_kernel_ge hv hu₁ hu hM y w hw) hint.integrableOn
    have h2 := setIntegral_le_integral (s := {w : E | ‖w‖ ^ 2 ≤ 2 * M}) hint
      (ae_of_all _ fun w => (mehlerKernel_pos v hu0 y w).le)
    have h3 := mehlerSmooth_half_le ρ (hρ 2)
    rw [smul_eq_mul] at h1
    have hc : 0 < c := Real.exp_pos _
    unfold ouDensity
    nlinarith
  have hloglow : -(Real.log 2 + (Y + 2 * M) / (v * ouS u₁)) ≤ Real.log (ouDensity v ρ u y) := by
    refine le_trans (le_of_eq ?_) (Real.log_le_log (by positivity) hlow)
    rw [Real.log_div (Real.exp_pos _).ne' two_ne_zero, Real.log_exp]
    ring
  -- combine
  have hL : 0 ≤ Real.log (1 / ouS u₁) :=
    Real.log_nonneg (by rw [le_div_iff₀ hs₁]; linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hvs : 0 < v * ouS u₁ := mul_pos hv hs₁
  have hA : 1 / (2 * v) ≤ (1 + 2 * M) / (v * ouS u₁) := by
    rw [div_le_div_iff₀ (by positivity) hvs]
    nlinarith
  have hA' : 0 ≤ (1 + 2 * M) / (v * ouS u₁) := by positivity
  rw [abs_le]
  constructor
  · refine le_trans ?_ hloglow
    rw [neg_le_neg_iff]
    have e1 : (Y + 2 * M) / (v * ouS u₁) ≤ (1 + 2 * M) / (v * ouS u₁) * (1 + Y) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hvs]
      nlinarith
    nlinarith [mul_nonneg hd hL, mul_nonneg (mul_nonneg hd hL) hY, mul_nonneg hl2.le hY]
  · refine hlogup.trans ?_
    have e1 : Y / (2 * v) ≤ (1 + 2 * M) / (v * ouS u₁) * Y := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hA hY
    nlinarith [mul_nonneg hd hL, mul_nonneg (mul_nonneg hd hL) hY, mul_nonneg hl2.le hY]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `P` smooth on `(0, ∞) × E` and `u > 0`, the `y`-derivatives of `P(u, ·)` are the joint
derivatives of `P` restricted to the directions `(0, e)`. -/
private lemma mehlerSmooth_iteratedFDeriv_slice {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {P : ℝ × E → F}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) {u : ℝ} (hu : 0 < u) :
    ∀ k (y : E), iteratedFDeriv ℝ k (fun y' => P (u, y')) y =
      (iteratedFDeriv ℝ k P (u, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E)
  | 0, y => by ext m; simp
  | k + 1, y => by
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := isOpen_Ioi.prod isOpen_univ
    have hev : iteratedFDeriv ℝ k (fun y' => P (u, y')) = fun y' =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) (iteratedFDeriv ℝ k P (u, y')) :=
      funext fun y' => mehlerSmooth_iteratedFDeriv_slice hP hu k y'
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k P) (u, y) :=
      (hP.contDiffAt (hU.mem_nhds (show (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) from
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `P` smooth on `(0, ∞) × E`, `u > 0` and `j ≤ 1`, the `k`-th `y`-derivative of
`∂_u^j P(u, ·)` has norm at most `‖D^{j+k} P(u, y)‖`. -/
private lemma mehlerSmooth_norm_mixed_le {P : ℝ × E → ℝ}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P (Set.Ioi 0 ×ˢ Set.univ)) {u : ℝ} (hu : 0 < u) (y : E) {j : ℕ}
    (hj : j ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y' => iteratedDeriv j (fun u' => P (u', y')) u) y‖ ≤
      ‖iteratedFDeriv ℝ (j + k) P (u, y)‖ := by
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := isOpen_Ioi.prod isOpen_univ
  have hinr : ∏ _i : Fin k, ‖ContinuousLinearMap.inr ℝ ℝ E‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => ContinuousLinearMap.opNorm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ E)
  have hslice : ∀ {Q : ℝ × E → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) Q (Set.Ioi 0 ×ˢ Set.univ) →
      ‖iteratedFDeriv ℝ k (fun y' => Q (u, y')) y‖ ≤ ‖iteratedFDeriv ℝ k Q (u, y)‖ := by
    intro Q hQ
    rw [mehlerSmooth_iteratedFDeriv_slice hQ hu k y]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) hinr
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with rfl | rfl
  · rw [Nat.zero_add]
    exact hslice hP
  · simp only [iteratedDeriv_one]
    let L : (ℝ × E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))
    have hQ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ P x ((1 : ℝ), (0 : E)))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      (hP.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    have heq : (fun y' => deriv (fun u' => P (u', y')) u) =
        fun y' => fderiv ℝ P (u, y') ((1 : ℝ), (0 : E)) := by
      funext y'
      have hd : DifferentiableAt ℝ P (u, y') :=
        (hP.contDiffAt (hU.mem_nhds (show (u, y') ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) from
          ⟨hu, trivial⟩))).differentiableAt (by simp)
      have h := hd.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u y'))
      exact h.deriv
    rw [heq]
    refine (hslice hQ).trans ?_
    have hc : ContDiffAt ℝ (⊤ : ℕ∞) P (u, y) := hP.contDiffAt (hU.mem_nhds
      (show (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) from ⟨hu, trivial⟩))
    have hL : ∀ T : ℝ × E →L[ℝ] ℝ, ‖L T‖ ≤ ‖T‖ := fun T => by
      have : ‖((1 : ℝ), (0 : E))‖ = 1 := by simp
      calc ‖L T‖ = ‖T ((1 : ℝ), (0 : E))‖ := rfl
        _ ≤ ‖T‖ * ‖((1 : ℝ), (0 : E))‖ := T.le_opNorm _
        _ = ‖T‖ := by rw [this, mul_one]
    have hcd : ContDiffAt ℝ k (fderiv ℝ P) (u, y) :=
      hc.fderiv_right (m := (k : WithTop ℕ∞)) (by exact_mod_cast le_top)
    have h := L.iteratedFDeriv_comp_left hcd (i := k) le_rfl
    rw [show (fun x => fderiv ℝ P x ((1 : ℝ), (0 : E))) = ⇑L ∘ fderiv ℝ P from rfl, h,
      add_comm 1 k, ← norm_iteratedFDeriv_fderiv]
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => ?_
    rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    exact (hL _).trans (ContinuousMultilinearMap.le_opNorm _ _)

/-- `(1 + τ)^q ≤ 4^q (1 + (2v)^q q!) e^{τ²/(2v)}` for `τ ≥ 0`. -/
private lemma mehlerSmooth_one_add_pow_le {v : ℝ} (hv : 0 < v) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (1 + τ) ^ q ≤ 4 ^ q * (1 + (2 * v) ^ q * q.factorial) * Real.exp (τ ^ 2 / (2 * v)) := by
  set x := τ ^ 2 with hxdef
  have hx : 0 ≤ x := sq_nonneg τ
  have h1 : (1 + τ) ^ q ≤ 2 ^ q * (1 + x) ^ q := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) q
  have h2 : (1 + x) ^ q ≤ 2 ^ q * (1 + x ^ q) := by
    rcases le_total x 1 with h | h
    · calc (1 + x) ^ q ≤ 2 ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
        _ ≤ 2 ^ q * (1 + x ^ q) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx q])
    · calc (1 + x) ^ q ≤ (2 * x) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
        _ = 2 ^ q * x ^ q := mul_pow _ _ _
        _ ≤ 2 ^ q * (1 + x ^ q) := by gcongr; linarith
  have h3 : x ^ q ≤ (2 * v) ^ q * q.factorial * Real.exp (x / (2 * v)) := by
    have := Real.pow_div_factorial_le_exp (x / (2 * v)) (by positivity) q
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at this
    calc x ^ q ≤ _ := this
      _ = _ := by ring
  have h4 : 1 ≤ Real.exp (x / (2 * v)) := Real.one_le_exp (by positivity)
  calc (1 + τ) ^ q ≤ 2 ^ q * (2 ^ q * (1 + x ^ q)) := h1.trans (by gcongr)
    _ ≤ 2 ^ q * (2 ^ q * (Real.exp (x / (2 * v)) +
        (2 * v) ^ q * q.factorial * Real.exp (x / (2 * v)))) := by gcongr
    _ = _ := by
      rw [show (4 : ℝ) ^ q = 2 ^ q * 2 ^ q by rw [← mul_pow]; norm_num]; ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `u ≥ u₁ > 0` and `q ∈ ℕ`:
`K(u, y, w) ≤ s_{u₁}^{-d/2} e^{|y|²/(2v)} D_q (1 + |w|)^q / (1 + |y|)^q` with
`D_q = 4^q (1 + (2v)^q q!)` (from Lemma 14.E(d)). -/
private lemma mehlerSmooth_kernel_le_poly {v : ℝ} (hv : 0 < v) {u₁ u : ℝ} (hu₁ : 0 < u₁)
    (hu : u₁ ≤ u) (q : ℕ) (y w : E) :
    mehlerKernel v u y w ≤ ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (‖y‖ ^ 2 / (2 * v)) *
        (4 ^ q * (1 + (2 * v) ^ q * q.factorial) * (1 + ‖w‖) ^ q / (1 + ‖y‖) ^ q) := by
  obtain ⟨hs₁, hs₁s, -⟩ := mehlerSmooth_ouS_bounds hu₁ hu
  have hu0 := hu₁.trans_le hu
  have hs := hs₁.trans_le hs₁s
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set τ := max (‖y‖ - ‖w‖) 0 with hτdef
  have hτ : 0 ≤ τ := le_max_right _ _
  set Dq := 4 ^ q * (1 + (2 * v) ^ q * q.factorial) with hDq
  have hγ : 0 < gaussDens E v y := by unfold gaussDens; positivity
  have h1 : mehlerKernel v u y w ≤
      ouS u ^ (-d / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)) * Real.exp (-τ ^ 2 / (2 * v)) := by
    have h := mehlerKernel_mul_gaussDens_le hv hu0 y w
    refine le_of_mul_le_mul_right (h.trans_eq ?_) hγ
    unfold gaussDens
    rw [Real.mul_rpow (by positivity) hs.le]
    have hee : Real.exp (‖y‖ ^ 2 / (2 * v)) * Real.exp (-‖y‖ ^ 2 / (2 * v)) = 1 := by
      rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
    linear_combination (-((2 * π * v) ^ (-d / 2) * ouS u ^ (-d / 2) *
      Real.exp (-τ ^ 2 / (2 * v)))) * hee
  have h2 : ouS u ^ (-d / 2) ≤ ouS u₁ ^ (-d / 2) :=
    Real.rpow_le_rpow_of_nonpos hs₁ hs₁s (by linarith)
  have hτy : 1 + ‖y‖ ≤ (1 + ‖w‖) * (1 + τ) := by
    have : ‖y‖ - ‖w‖ ≤ τ := le_max_left _ _
    nlinarith [norm_nonneg w]
  have h3 : Real.exp (-τ ^ 2 / (2 * v)) ≤ Dq * (1 + ‖w‖) ^ q / (1 + ‖y‖) ^ q := by
    rw [le_div_iff₀ (by positivity)]
    have h4 := mehlerSmooth_one_add_pow_le hv q hτ
    have h5 : (1 + ‖y‖) ^ q ≤ (1 + ‖w‖) ^ q * (1 + τ) ^ q := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hτy q
    have hee : Real.exp (-τ ^ 2 / (2 * v)) * Real.exp (τ ^ 2 / (2 * v)) = 1 := by
      rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
    have he0 := (Real.exp_pos (-τ ^ 2 / (2 * v))).le
    calc Real.exp (-τ ^ 2 / (2 * v)) * (1 + ‖y‖) ^ q
        ≤ Real.exp (-τ ^ 2 / (2 * v)) * ((1 + ‖w‖) ^ q * (Dq * Real.exp (τ ^ 2 / (2 * v)))) := by
          gcongr; exact h5.trans (by gcongr)
      _ = Dq * (1 + ‖w‖) ^ q * (Real.exp (-τ ^ 2 / (2 * v)) * Real.exp (τ ^ 2 / (2 * v))) := by
          ring
      _ = Dq * (1 + ‖w‖) ^ q := by rw [hee, mul_one]
  calc mehlerKernel v u y w ≤ _ := h1
    _ ≤ ouS u₁ ^ (-d / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)) *
        (Dq * (1 + ‖w‖) ^ q / (1 + ‖y‖) ^ q) := by
      gcongr

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `w ↦ (a + |w|)^N` is integrable if all moments `∫ |w|^m dρ` are finite. -/
private lemma mehlerSmooth_integrable_add_pow {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) (a : ℝ) (N : ℕ) :
    Integrable (fun w => (a + ‖w‖) ^ N) ρ := by
  simp_rw [add_pow]
  exact integrable_finsetSum _ fun m _ => ((hρ (N - m)).const_mul (a ^ m)).mul_const _

/-- Lemma 14.2(iii): for `u₁ > 0` there is a function `𝔐` on `E` with `𝔐 (1 + |y|)^m`
integrable with respect to `g_v` for every `m ∈ ℕ` such that, for all `u ≥ u₁`, `y ∈ E`, `j ≤ 1`
and `k ≤ 3`, the norm `N_k(∂_u^j Ψ(u, ·))(y)` of the `k`-th derivative in `y` of `∂_u^j Ψ(u, ·)`
(the norm of a `k`-linear form) is at most `𝔐(y)`. Each coordinate derivative
`∂_u^j ∂_y^α Ψ(u, y)` with `|α| = k` is bounded by this norm. -/
theorem integrable_sup_derivs_ouDensity {v : ℝ} (hv : 0 < v) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {u₁ : ℝ}
    (hu₁ : 0 < u₁) :
    ∃ 𝔐 : E → ℝ, (∀ m : ℕ, Integrable (fun y => 𝔐 y * (1 + ‖y‖) ^ m) (gaussE E v)) ∧
      ∀ u, u₁ ≤ u → ∀ y, ∀ j ≤ 1, ∀ k ≤ 3,
        ‖iteratedFDeriv ℝ k (fun y' => iteratedDeriv j (fun u' => ouDensity v ρ u' y') u) y‖ ≤
          𝔐 y := by
  set d := Module.finrank ℝ E with hd_def
  set κ := mehlerKernelBoundsKappa v u₁
  set C₀ := ∑ n ∈ Finset.range 5, 2 ^ n * |mehlerKernelBoundsCHat v d n| * κ ^ (2 * n) with hC₀
  set S₁ := ouS u₁ ^ (-(d : ℝ) / 2) with hS₁
  have hs₁ : 0 < ouS u₁ := (mehlerSmooth_ouS_bounds hu₁ le_rfl).1
  have hκn : ∀ n : ℕ, 0 ≤ κ ^ (2 * n) := fun n => by rw [pow_mul]; positivity
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun n _ => by have := hκn n; positivity
  have hS₁0 : 0 ≤ S₁ := Real.rpow_nonneg hs₁.le _
  let D : ℕ → ℝ := fun q => 4 ^ q * (1 + (2 * v) ^ q * q.factorial)
  have hD : ∀ q, 0 ≤ D q := fun q => by positivity
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, A = fun q => C₀ * S₁ * D q * ∫ w, (1 + ‖w‖) ^ (8 + q) ∂ρ :=
    ⟨_, rfl⟩
  have hA : ∀ q, 0 ≤ A q := fun q => by
    have : 0 ≤ ∫ w, (1 + ‖w‖) ^ (8 + q) ∂ρ := integral_nonneg fun w => by positivity
    have := hD q
    rw [hAdef]
    positivity
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → E → ℝ, f = fun q y =>
      A q * (Real.exp (‖y‖ ^ 2 / (2 * v)) * ((1 + ‖y‖) ^ 8 / (1 + ‖y‖) ^ q)) := ⟨_, rfl⟩
  have hf0 : ∀ q y, 0 ≤ f q y := fun q y => by have := hA q; rw [hfdef]; positivity
  have hbdd : ∀ y, BddBelow (Set.range fun q => f q y) := fun y =>
    ⟨0, by rintro _ ⟨q, rfl⟩; exact hf0 q y⟩
  have hmeas : ∀ q, Measurable (f q) := fun q => by rw [hfdef]; fun_prop
  -- the joint derivatives of `Ψ` are bounded by every `f q`
  have hjoint : ∀ u, u₁ ≤ u → ∀ y, ∀ n ≤ 4, ∀ q,
      ‖iteratedFDeriv ℝ n (fun p : ℝ × E => ouDensity v ρ p.1 p.2) (u, y)‖ ≤ f q y := by
    intro u hu y n hn q
    have hu0 : 0 < u := hu₁.trans_le hu
    obtain ⟨hI, hD'⟩ := iteratedFDeriv_kernelIntegral hv hρ (h := fun _ => (1 : ℝ))
      measurable_const (C := 1) (fun _ => by simp) n
      (show (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) from ⟨hu0, trivial⟩)
    simp only [mul_one, one_smul] at hI hD'
    have hfun : (fun p : ℝ × E => ouDensity v ρ p.1 p.2) =
        fun x => ∫ w, mehlerKernel v x.1 x.2 w ∂ρ := rfl
    rw [hfun, hD']
    set B := C₀ * S₁ * D q * (Real.exp (‖y‖ ^ 2 / (2 * v)) * ((1 + ‖y‖) ^ 8 / (1 + ‖y‖) ^ q))
    have hint : Integrable (fun w => B * (1 + ‖w‖) ^ (8 + q)) ρ :=
      (mehlerSmooth_integrable_add_pow hρ 1 (8 + q)).const_mul B
    refine (norm_integral_le_of_norm_le hint (ae_of_all _ fun w => ?_)).trans_eq ?_
    · have hK := mehlerKernel_pos v hu0 y w
      have hT : 1 ≤ 1 + ‖y‖ + ‖w‖ := by linarith [norm_nonneg y, norm_nonneg w]
      have hcoef : 2 ^ n * mehlerKernelBoundsCHat v d n * κ ^ (2 * n) ≤ C₀ := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun n =>
          2 ^ n * |mehlerKernelBoundsCHat v d n| * κ ^ (2 * n))
          (fun n _ => by have := hκn n; positivity) (Finset.mem_range.2 (by omega : n < 5)))
        have := hκn n
        gcongr
        exact le_abs_self _
      have hpow : (1 + ‖y‖ + ‖w‖) ^ (2 * n) ≤ ((1 + ‖y‖) * (1 + ‖w‖)) ^ 8 :=
        (pow_le_pow_right₀ hT (by omega)).trans
          (pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg y, norm_nonneg w]) 8)
      have hKq := mehlerSmooth_kernel_le_poly hv hu₁ hu q y w
      calc ‖iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) (u, y)‖
          ≤ 2 ^ n * mehlerKernelBoundsCHat v d n *
              (κ * (1 + ‖y‖ + ‖w‖)) ^ (2 * n) * mehlerKernel v u y w :=
            norm_iteratedFDeriv_mehlerKernel_le hv hu₁ n hu y w
        _ = (2 ^ n * mehlerKernelBoundsCHat v d n * κ ^ (2 * n)) *
              ((1 + ‖y‖ + ‖w‖) ^ (2 * n) * mehlerKernel v u y w) := by rw [mul_pow]; ring
        _ ≤ C₀ * (((1 + ‖y‖) * (1 + ‖w‖)) ^ 8 * (S₁ * Real.exp (‖y‖ ^ 2 / (2 * v)) *
              (D q * (1 + ‖w‖) ^ q / (1 + ‖y‖) ^ q))) := by
            gcongr
        _ = B * (1 + ‖w‖) ^ (8 + q) := by
            simp only [B, D]
            rw [pow_add, mul_pow]
            field_simp
    · rw [integral_const_mul, hfdef, hAdef]
      ring
  refine ⟨fun y => ⨅ q, f q y, fun m => ?_, fun u hu y j hj k hk => ?_⟩
  · -- integrability against `g_v`
    set q := m + 9 + d with hq
    have hγm : Measurable fun y : E => ENNReal.ofReal (gaussDens E v y) := by
      unfold gaussDens; fun_prop
    have hdom : Integrable (fun y => f q y * (1 + ‖y‖) ^ m) (gaussE E v) := by
      rw [gaussE_eq_withDensity hv, integrable_withDensity_iff hγm
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      have hr : ((d : ℝ)) < (d : ℝ) + 1 := by linarith
      refine ((integrable_one_add_norm (μ := (volume : Measure E)) hr).const_mul
        (A q * (2 * π * v) ^ (-(d : ℝ) / 2))).congr (ae_of_all _ fun y => ?_)
      have hy1 : 0 < 1 + ‖y‖ := by positivity
      have hγ0 : 0 ≤ gaussDens E v y := by unfold gaussDens; positivity
      simp only
      rw [ENNReal.toReal_ofReal hγ0, hfdef]
      beta_reduce
      unfold gaussDens
      have hpq : (1 + ‖y‖) ^ q = (1 + ‖y‖) ^ 8 * (1 + ‖y‖) ^ m * (1 + ‖y‖) ^ (d + 1) := by
        rw [← pow_add, ← pow_add, hq]; congr 1; ring
      rw [show -((d : ℝ) + 1) = -((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hy1.le,
        Real.rpow_natCast, hpq]
      have hee : Real.exp (‖y‖ ^ 2 / (2 * v)) * Real.exp (-‖y‖ ^ 2 / (2 * v)) = 1 := by
        rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
      have h8 : (1 + ‖y‖) ^ 8 * (1 + ‖y‖) ^ m ≠ 0 := by positivity
      calc A q * (2 * π * v) ^ (-(d : ℝ) / 2) * ((1 + ‖y‖) ^ (d + 1))⁻¹
          = A q * (2 * π * v) ^ (-(d : ℝ) / 2) * ((1 + ‖y‖) ^ 8 * (1 + ‖y‖) ^ m /
              ((1 + ‖y‖) ^ 8 * (1 + ‖y‖) ^ m * (1 + ‖y‖) ^ (d + 1))) := by
            rw [div_mul_cancel_left₀ h8]
        _ = A q * (Real.exp (‖y‖ ^ 2 / (2 * v)) * ((1 + ‖y‖) ^ 8 /
              ((1 + ‖y‖) ^ 8 * (1 + ‖y‖) ^ m * (1 + ‖y‖) ^ (d + 1)))) * (1 + ‖y‖) ^ m *
              ((2 * π * v) ^ (-(d : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (2 * v))) := by
            rw [← mul_one (A q * (2 * π * v) ^ (-(d : ℝ) / 2) * _), ← hee]
            ring
    refine hdom.mono' (((Measurable.iInf hmeas).mul (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    have h0 : 0 ≤ ⨅ q, f q y := le_ciInf fun q => hf0 q y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (ciInf_le (hbdd y) q) (by positivity)
  · -- the mixed derivatives
    have hu0 : 0 < u := hu₁.trans_le hu
    refine le_ciInf fun q => ?_
    refine (mehlerSmooth_norm_mixed_le (ouDensity_smooth_and_eq hv ρ hρ).1 hu0 y hj k).trans ?_
    exact hjoint u hu y (j + k) (by omega) q

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `(y, w) ↦ K(u, y, w)` is continuous. -/
private lemma mehlerSmooth_kernel_continuous₂ (v u : ℝ) :
    Continuous fun p : E × E => mehlerKernel v u p.1 p.2 := by
  unfold mehlerKernel; fun_prop

/-- Lemma 14.E(c) under the integral: for `u > 0`,
`∇Ψ(u, ·)(y) = ∫ K(u, y, w) V(y, w) ρ(dw)` with `V(y, w) = a_u (w - a_u y) / (v s_u)`, and the
integrand is integrable. -/
private lemma mehlerSmooth_hasGradientAt {v : ℝ} (hv : 0 < v) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {u : ℝ}
    (hu : 0 < u) (y : E) :
    Integrable (fun w => mehlerKernel v u y w • ((ouA u / (v * ouS u)) • (w - ouA u • y))) ρ ∧
      HasGradientAt (ouDensity v ρ u)
        (∫ w, mehlerKernel v u y w • ((ouA u / (v * ouS u)) • (w - ouA u • y)) ∂ρ) y := by
  obtain ⟨-, -, hs1⟩ := mehlerSmooth_ouS_bounds hu le_rfl
  have hs : 0 < ouS u := (mehlerSmooth_ouS_bounds hu le_rfl).1
  have ha : 0 < ouA u := Real.exp_pos _
  have ha1 : ouA u ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  set k := ouA u / (v * ouS u) with hk
  have hk0 : 0 ≤ k := by positivity
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  set c₁ := ouS u ^ (-d / 2) * Real.exp ((‖y‖ + 1) ^ 2 / (2 * v)) * k
  have hc₁ : 0 ≤ c₁ := by positivity
  set bound : E → ℝ := fun w => c₁ * (‖w‖ + (‖y‖ + 1))
  have hbound : Integrable bound ρ :=
    (((hρ 1).congr (ae_of_all _ fun w => by simp)).add (integrable_const _)).const_mul c₁
  have hnorm : ∀ y' ∈ Metric.ball y 1, ∀ w,
      ‖mehlerKernel v u y' w • (k • (w - ouA u • y'))‖ ≤ bound w := by
    intro y' hy' w
    have hy'' : ‖y'‖ ≤ ‖y‖ + 1 := by
      have := Metric.mem_ball.1 hy'
      rw [dist_eq_norm] at this
      linarith [norm_le_norm_add_norm_sub' y' y, norm_sub_rev y' y]
    have hK := mehlerKernel_pos v hu y' w
    have hKle : mehlerKernel v u y' w ≤ ouS u ^ (-d / 2) * Real.exp ((‖y‖ + 1) ^ 2 / (2 * v)) :=
      (mehlerKernel_le hv hu y' w).trans (by gcongr)
    have hV : ‖w - ouA u • y'‖ ≤ ‖w‖ + (‖y‖ + 1) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      nlinarith [norm_nonneg y']
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hK,
      abs_of_nonneg hk0]
    calc mehlerKernel v u y' w * (k * ‖w - ouA u • y'‖)
        ≤ (ouS u ^ (-d / 2) * Real.exp ((‖y‖ + 1) ^ 2 / (2 * v))) * (k * (‖w‖ + (‖y‖ + 1))) := by
          gcongr
      _ = bound w := by simp only [bound, c₁]; ring
  have hcont : ∀ y' : E, Continuous fun w : E => mehlerKernel v u y' w • (k • (w - ouA u • y')) :=
    fun y' => by have := mehlerSmooth_kernel_continuous v u y'; fun_prop
  have hint : ∀ y' ∈ Metric.ball y 1,
      Integrable (fun w => mehlerKernel v u y' w • (k • (w - ouA u • y'))) ρ :=
    fun y' hy' => hbound.mono' (hcont y').aestronglyMeasurable
      (ae_of_all _ fun w => hnorm y' hy' w)
  have hint0 := hint y (Metric.mem_ball_self one_pos)
  refine ⟨hint0, ?_⟩
  have hdual : ∀ x : E, InnerProductSpace.toDual ℝ E x = innerSL ℝ x := fun x => by
    ext z; rfl
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ρ) (𝕜 := ℝ)
    (F := fun y' w => mehlerKernel v u y' w)
    (F' := fun y' w => innerSL ℝ (mehlerKernel v u y' w • (k • (w - ouA u • y'))))
    (bound := bound) (Metric.ball_mem_nhds y one_pos)
    (Eventually.of_forall fun y' => (mehlerSmooth_kernel_continuous v u y').aestronglyMeasurable)
    (mehlerSmooth_integrable_kernel hv hu ρ y)
    (((innerSL ℝ).continuous.comp (hcont y)).aestronglyMeasurable)
    (ae_of_all _ fun w y' hy' => by rw [innerSL_apply_norm]; exact hnorm y' hy' w)
    hbound
    (ae_of_all _ fun w y' _ => by
      have := (mehlerKernel_hasGradientAt v u y' w)
      rw [hasGradientAt_iff_hasFDerivAt, hdual] at this
      exact this)
  rw [hasGradientAt_iff_hasFDerivAt, hdual]
  rw [ContinuousLinearMap.integral_comp_comm _ hint0] at h
  exact h

/-- Cauchy–Schwarz under the integral: for `K ≥ 0` with `∫ K > 0`,
`|∫ K V|² ≤ (∫ K) (∫ K |V|²)`. -/
private lemma mehlerSmooth_cauchySchwarz {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {ρ : Measure α} {K : α → ℝ} {V : α → F}
    (hK0 : ∀ w, 0 ≤ K w) (hKi : Integrable K ρ) (hKV : Integrable (fun w => K w • V w) ρ)
    (hKV2 : Integrable (fun w => K w * ‖V w‖ ^ 2) ρ) (hpos : 0 < ∫ w, K w ∂ρ) :
    ‖∫ w, K w • V w ∂ρ‖ ^ 2 / ∫ w, K w ∂ρ ≤ ∫ w, K w * ‖V w‖ ^ 2 ∂ρ := by
  set G := ∫ w, K w • V w ∂ρ
  set Ψ := ∫ w, K w ∂ρ
  set c := Ψ⁻¹ • G
  have hpt : ∀ w, 2 * inner ℝ c (K w • V w) - K w * ‖c‖ ^ 2 ≤ K w * ‖V w‖ ^ 2 := fun w => by
    have h := mul_nonneg (hK0 w) (sq_nonneg ‖V w - c‖)
    rw [norm_sub_sq_real] at h
    rw [inner_smul_right, real_inner_comm]
    nlinarith
  have hint : Integrable (fun w => 2 * inner ℝ c (K w • V w) - K w * ‖c‖ ^ 2) ρ :=
    ((hKV.const_inner c).const_mul 2).sub (hKi.mul_const _)
  have h := integral_mono hint hKV2 hpt
  rw [integral_sub ((hKV.const_inner c).const_mul 2) (hKi.mul_const _), integral_const_mul,
    integral_inner hKV, integral_mul_const] at h
  have e1 : inner ℝ c G = ‖G‖ ^ 2 / Ψ := by
    rw [inner_smul_left, real_inner_self_eq_norm_sq]; simp [div_eq_inv_mul]
  have e2 : ‖c‖ ^ 2 = ‖G‖ ^ 2 / Ψ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, div_eq_inv_mul]
  rw [e1, e2] at h
  have : 2 * (‖G‖ ^ 2 / Ψ) - Ψ * (‖G‖ ^ 2 / Ψ ^ 2) = ‖G‖ ^ 2 / Ψ := by
    field_simp; ring
  linarith

/-- Lemma 14.2(iv): for `u > 0`, in `[0, ∞]`,
`∫ |∇Ψ(u, ·)|² / Ψ(u, ·) dg_v ≤ 2d / (v s_u) + 2 (e^{-u} M₂' + s_u v d) / v² < ∞`, where
`d = dim E`, `M₂' = ∫ |w|² ρ(dw)` and `σ² = v`. -/
theorem lintegral_fisher_ouDensity_lt_top {v : ℝ} (hv : 0 < v) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {u : ℝ}
    (hu : 0 < u) :
    ∫⁻ y, ENNReal.ofReal (‖gradient (ouDensity v ρ u) y‖ ^ 2 / ouDensity v ρ u y) ∂gaussE E v ≤
        ENNReal.ofReal (2 * Module.finrank ℝ E / (v * ouS u) +
          2 * (Real.exp (-u) * ∫ w, ‖w‖ ^ 2 ∂ρ + ouS u * v * Module.finrank ℝ E) / v ^ 2) ∧
      ∫⁻ y, ENNReal.ofReal (‖gradient (ouDensity v ρ u) y‖ ^ 2 / ouDensity v ρ u y)
        ∂gaussE E v < ∞ := by
  have := gaussE_isProbabilityMeasure (E := E) v
  have hs : 0 < ouS u := (mehlerSmooth_ouS_bounds hu le_rfl).1
  have hs1 : ouS u ≤ 1 := (mehlerSmooth_ouS_bounds hu le_rfl).2.2
  have ha : 0 < ouA u := Real.exp_pos _
  have ha2 : ouA u ^ 2 = Real.exp (-u) := by
    rw [ouA, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have has : ouA u ^ 2 + ouS u = 1 := by rw [ha2, ouS]; ring
  have ha21 : ouA u ^ 2 ≤ 1 := by linarith
  set a := ouA u
  set σ := ouS u
  set k := a / (v * σ) with hk
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set M := ∫ w, ‖w‖ ^ 2 ∂ρ with hMdef
  have hM : 0 ≤ M := integral_nonneg fun w => sq_nonneg _
  set V : E → E → ℝ := fun y w => ‖k • (w - a • y)‖ ^ 2 with hV
  have hVc : Continuous fun p : E × E => mehlerKernel v u p.1 p.2 * V p.1 p.2 := by
    have := mehlerSmooth_kernel_continuous₂ (E := E) v u
    simp only [hV]
    fun_prop
  -- integrability of `K |V|²` in `w`
  have hKV2 : ∀ y, Integrable (fun w => mehlerKernel v u y w * V y w) ρ := by
    intro y
    set c := σ ^ (-d / 2) * Real.exp (‖y‖ ^ 2 / (2 * v))
    refine ((((hρ 2).const_mul 2).add (integrable_const (2 * ‖y‖ ^ 2))).const_mul
      (c * k ^ 2)).mono' (hVc.comp (Continuous.prodMk_right y)).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    have hK := mehlerKernel_pos v hu y w
    have hKle := mehlerKernel_le hv hu y w
    have hVle : V y w ≤ k ^ 2 * (2 * ‖w‖ ^ 2 + 2 * ‖y‖ ^ 2) := by
      simp only [hV]
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      gcongr
      have h1 := norm_sub_le w (a • y)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h1
      have h2 : a * ‖y‖ ≤ ‖y‖ := by
        have : a ≤ 1 := by nlinarith
        nlinarith [norm_nonneg y]
      have h3 : ‖w - a • y‖ ^ 2 ≤ (‖w‖ + ‖y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
      nlinarith [sq_nonneg (‖w‖ - ‖y‖)]
    have hV0 : 0 ≤ V y w := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK.le hV0)]
    calc mehlerKernel v u y w * V y w ≤ c * (k ^ 2 * (2 * ‖w‖ ^ 2 + 2 * ‖y‖ ^ 2)) :=
          mul_le_mul hKle hVle hV0 (by positivity)
      _ = _ := by simp only [Pi.add_apply]; ring
  -- pointwise bound by Cauchy–Schwarz
  have hpt : ∀ y, ‖gradient (ouDensity v ρ u) y‖ ^ 2 / ouDensity v ρ u y ≤
      ∫ w, mehlerKernel v u y w * V y w ∂ρ := by
    intro y
    obtain ⟨hint, hgrad⟩ := mehlerSmooth_hasGradientAt hv ρ hρ hu y
    rw [hgrad.gradient]
    exact mehlerSmooth_cauchySchwarz (fun w => (mehlerKernel_pos v hu y w).le)
      (mehlerSmooth_integrable_kernel hv hu ρ y) hint (hKV2 y) ((ouLaw_eq_withDensity hv hu ρ).2 y)
  -- the inner `g_v`-integral for fixed `w`
  have hinner : ∀ w, ∫⁻ y, ENNReal.ofReal (mehlerKernel v u y w * V y w) ∂gaussE E v ≤
      ENNReal.ofReal (k ^ 2 * (2 * σ ^ 2 * ‖w‖ ^ 2 + 2 * a ^ 2 * σ * (d * v))) := by
    intro w
    have hmeas : Measurable fun y => ENNReal.ofReal (V y w) := by
      simp only [hV]; fun_prop
    have h1 : ∫⁻ y, ENNReal.ofReal (mehlerKernel v u y w * V y w) ∂gaussE E v =
        mehlerL v u (fun y => ENNReal.ofReal (V y w)) w := by
      rw [mehlerL_eq_lintegral_kernel hv hu hmeas w]
      refine lintegral_congr fun y => ?_
      rw [mehlerKernel_comm v u y w, mul_comm, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [h1, mehlerL]
    have hsq : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hs.le
    have hint2 : Integrable (fun z : E => k ^ 2 * (2 * σ ^ 2 * ‖w‖ ^ 2) +
        k ^ 2 * (2 * a ^ 2 * σ) * ‖z‖ ^ 2) (gaussE E v) :=
      (integrable_const _).add ((mehlerSmooth_moments_gaussE v 2).const_mul _)
    calc ∫⁻ z, ENNReal.ofReal (V (a • w + Real.sqrt σ • z) w) ∂gaussE E v
        ≤ ∫⁻ z, ENNReal.ofReal (k ^ 2 * (2 * σ ^ 2 * ‖w‖ ^ 2) +
            k ^ 2 * (2 * a ^ 2 * σ) * ‖z‖ ^ 2) ∂gaussE E v := by
          refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
          have heq : w - a • (a • w + Real.sqrt σ • z) = σ • w - (a * Real.sqrt σ) • z := by
            rw [smul_add, smul_smul, smul_smul, show σ = 1 - a * a by nlinarith]
            module
          simp only [hV]
          rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          have h2 : ‖σ • w - (a * Real.sqrt σ) • z‖ ^ 2 ≤
              2 * ‖σ • w‖ ^ 2 + 2 * ‖(a * Real.sqrt σ) • z‖ ^ 2 := by
            have h3 := pow_le_pow_left₀ (norm_nonneg _)
              (norm_sub_le (σ • w) ((a * Real.sqrt σ) • z)) 2
            nlinarith [sq_nonneg (‖σ • w‖ - ‖(a * Real.sqrt σ) • z‖)]
          rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
            sq_abs, mul_pow, hsq] at h2
          nlinarith [sq_nonneg k]
      _ = ENNReal.ofReal (k ^ 2 * (2 * σ ^ 2 * ‖w‖ ^ 2 + 2 * a ^ 2 * σ * (d * v))) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun z => by positivity),
            integral_add (integrable_const _) ((mehlerSmooth_moments_gaussE v 2).const_mul _),
            integral_const, integral_const_mul, integral_norm_sq_gaussE hv.le, probReal_univ,
            one_smul, ← hd_def]
          ring_nf
  -- assemble
  have hbound : ∫⁻ y, ENNReal.ofReal (‖gradient (ouDensity v ρ u) y‖ ^ 2 / ouDensity v ρ u y)
      ∂gaussE E v ≤ ENNReal.ofReal (k ^ 2 * (2 * σ ^ 2 * M + 2 * a ^ 2 * σ * (d * v))) := by
    have hw : Integrable (fun w : E => k ^ 2 * (2 * σ ^ 2 * ‖w‖ ^ 2 + 2 * a ^ 2 * σ * (d * v)))
        ρ := (((hρ 2).const_mul _).add (integrable_const _)).const_mul _
    calc ∫⁻ y, ENNReal.ofReal (‖gradient (ouDensity v ρ u) y‖ ^ 2 / ouDensity v ρ u y)
          ∂gaussE E v
        ≤ ∫⁻ y, ∫⁻ w, ENNReal.ofReal (mehlerKernel v u y w * V y w) ∂ρ ∂gaussE E v := by
          refine lintegral_mono fun y => ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hKV2 y)
            (ae_of_all _ fun w => mul_nonneg (mehlerKernel_pos v hu y w).le (sq_nonneg _))]
          exact ENNReal.ofReal_le_ofReal (hpt y)
      _ = ∫⁻ w, ∫⁻ y, ENNReal.ofReal (mehlerKernel v u y w * V y w) ∂gaussE E v ∂ρ :=
          lintegral_lintegral_swap (ENNReal.measurable_ofReal.comp hVc.measurable).aemeasurable
      _ ≤ ∫⁻ w, ENNReal.ofReal (k ^ 2 * (2 * σ ^ 2 * ‖w‖ ^ 2 + 2 * a ^ 2 * σ * (d * v))) ∂ρ :=
          lintegral_mono hinner
      _ = _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal hw (ae_of_all _ fun w => by positivity),
            integral_const_mul, integral_add ((hρ 2).const_mul _) (integrable_const _),
            integral_const_mul, integral_const, probReal_univ, one_smul]
  have hfinal : k ^ 2 * (2 * σ ^ 2 * M + 2 * a ^ 2 * σ * (d * v)) ≤
      2 * d / (v * σ) + 2 * (Real.exp (-u) * M + σ * v * d) / v ^ 2 := by
    rw [← ha2, hk]
    have e : (a / (v * σ)) ^ 2 * (2 * σ ^ 2 * M + 2 * a ^ 2 * σ * (d * v)) =
        2 * a ^ 2 * M / v ^ 2 + 2 * (a ^ 2) ^ 2 * d / (v * σ) := by
      field_simp
    rw [e]
    have h1 : 2 * (a ^ 2) ^ 2 * d / (v * σ) ≤ 2 * d / (v * σ) := by
      gcongr
      nlinarith
    have h2 : 0 ≤ 2 * (σ * v * d) / v ^ 2 := by positivity
    have h3 : 2 * (a ^ 2 * M + σ * v * d) / v ^ 2 =
        2 * a ^ 2 * M / v ^ 2 + 2 * (σ * v * d) / v ^ 2 := by
      ring
    rw [h3]
    linarith
  exact ⟨hbound.trans (ENNReal.ofReal_le_ofReal hfinal),
    hbound.trans_lt ENNReal.ofReal_lt_top⟩

/-- On `(0, ∞) × E`, `T_u Φ(y) = Ψ_Φ(u, y) = ∫ K(u, y, w) Φ(w) g_v(dw)`. -/
private lemma mehlerSmooth_mehler_eq {v : ℝ} (hv : 0 < v) {Φ : E → ℝ} (hΦ : Measurable Φ)
    {u : ℝ} (hu : 0 < u) (y : E) :
    mehler v u Φ y = ∫ w, mehlerKernel v u y w * Φ w ∂gaussE E v := by
  rw [mehler_eq_integral_kernel hv hu hΦ]
  simp_rw [mul_comm (Φ _)]

/-- Lemma 14.3: for bounded Borel `Φ`, `(u, y) ↦ T_u Φ(y)` is `C^∞` on `(0, ∞) × E`. -/
theorem contDiffOn_mehler {v : ℝ} (hv : 0 < v) {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hb : ∃ C, ∀ y, |Φ y| ≤ C) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => mehler v p.1 Φ p.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  obtain ⟨C, hC⟩ := hb
  exact (contDiffOn_kernelIntegral hv (mehlerSmooth_moments_gaussE v) hΦ hC).congr
    fun p hp => mehlerSmooth_mehler_eq hv hΦ hp.1 p.2

/-- Lemma 14.3: if `|Φ| ≤ C`, then `|T_u Φ(y)| ≤ C` for all `u` and `y`. -/
theorem abs_mehler_le (v u : ℝ) {Φ : E → ℝ} {C : ℝ} (hC : ∀ y, |Φ y| ≤ C) (y : E) :
    |mehler v u Φ y| ≤ C := by
  have := gaussE_isProbabilityMeasure (E := E) v
  have h := norm_integral_le_of_norm_le_const (μ := gaussE E v)
    (f := fun z => Φ (ouA u • y + Real.sqrt (ouS u) • z)) (C := C)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- Lemma 14.3: for bounded Borel `Φ`, `u > 0` and `y ∈ E`, `∂_u T_u Φ(y) = A T_u Φ(y)`. -/
theorem hasDerivAt_mehler {v : ℝ} (hv : 0 < v) {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hb : ∃ C, ∀ y, |Φ y| ≤ C) {u : ℝ} (hu : 0 < u) (y : E) :
    HasDerivAt (fun u' => mehler v u' Φ y) (ouGen v (mehler v u Φ) y) u := by
  obtain ⟨C, hC⟩ := hb
  have h := mehlerKernelBounds_hasDerivAt_kernelIntegral hv (mehlerSmooth_moments_gaussE v) hΦ hC
    hu y
  have hfun : mehler v u Φ = fun y' => ∫ w, mehlerKernel v u y' w * Φ w ∂gaussE E v :=
    funext fun y' => mehlerSmooth_mehler_eq hv hΦ hu y'
  rw [ouGen, hfun]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hu] with u' hu'
  exact mehlerSmooth_mehler_eq hv hΦ hu' y

end Mehler

end Rigidity
