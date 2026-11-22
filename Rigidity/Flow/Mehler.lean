module

public import Rigidity.Flow.Gaussian
public import Rigidity.MainDefs

@[expose] public section

/-!
# The Ornstein–Uhlenbeck (Mehler) semigroup on a Euclidean space

For a finite-dimensional real inner product space `E` and a variance `v` (the `σ²` of §14.3), this
file defines the Mehler semigroup `T_u` of (14.1) on real- and `[0, ∞]`-valued functions, the law
`ρ_u = law(a_u Y + s_u^{1/2} Z)` of §14.3, the Mehler kernel `K` of (14.2), and the density
`Ψ(u, ·) = ∫ K(u, ·, w) ρ(dw)` of Lemma 14.1(iv). It proves Lemma 14.E (positivity, symmetry and
the Gaussian identities of the kernel, the kernel representation of `T_u`, the derivatives of the
kernel and the equation `∂_u K = A_y K`, the kernel bounds) and the `[0, ∞]`-valued form of
Lemma 14.1 (semigroup property, symmetry in `L²(g_v)`, invariance under linear isometries, the
density of `ρ_u`, the identity `∫ F dρ_u = ∫ T_u F dρ`, and the moment bounds of `ρ_u`).

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

/-- The Mehler semigroup (14.1), real-valued integrand:
`T_u Φ(y) = ∫ Φ(a_u y + s_u^{1/2} z) g_v(dz)`. -/
noncomputable def mehler (v u : ℝ) (Φ : E → ℝ) (y : E) : ℝ :=
  ∫ z, Φ (ouA u • y + Real.sqrt (ouS u) • z) ∂gaussE E v

/-- The Mehler semigroup (14.1) on `[0, ∞]`-valued functions. -/
noncomputable def mehlerL (v u : ℝ) (Φ : E → ℝ≥0∞) (y : E) : ℝ≥0∞ :=
  ∫⁻ z, Φ (ouA u • y + Real.sqrt (ouS u) • z) ∂gaussE E v

/-- The Mehler kernel `K(u, y, w)` (14.2). -/
noncomputable def mehlerKernel (v u : ℝ) (y w : E) : ℝ :=
  ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp ((2 * ouA u * inner ℝ y w - ouA u ^ 2 * (‖y‖ ^ 2 + ‖w‖ ^ 2)) / (2 * v * ouS u))

/-- `Ψ(u, y) = ∫ K(u, y, w) ρ(dw)`, the density of `ρ_u` with respect to `g_v` (Lemma 14.1(iv)). -/
noncomputable def ouDensity (v : ℝ) (ρ : Measure E) (u : ℝ) (y : E) : ℝ :=
  ∫ w, mehlerKernel v u y w ∂ρ

attribute [local instance] gaussE_isProbabilityMeasure

/-! ### The coefficients `a_u`, `s_u` -/

private lemma ouA_pos (u : ℝ) : 0 < ouA u := Real.exp_pos _

private lemma ouA_sq (u : ℝ) : ouA u ^ 2 = Real.exp (-u) := by
  rw [ouA, ← Real.exp_nat_mul]; congr 1; push_cast; ring

private lemma ouA_le_one {u : ℝ} (hu : 0 ≤ u) : ouA u ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

private lemma ouS_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ouS u := by
  rw [ouS, sub_nonneg]; exact Real.exp_le_one_iff.2 (by linarith)

private lemma ouS_pos {u : ℝ} (hu : 0 < u) : 0 < ouS u := by
  rw [ouS, sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)

private lemma ouS_le_one (u : ℝ) : ouS u ≤ 1 := by
  rw [ouS]; linarith [Real.exp_pos (-u)]

private lemma ouA_sq_add_ouS (u : ℝ) : ouA u ^ 2 + ouS u = 1 := by
  rw [ouA_sq, ouS]; ring

private lemma ouA_mul_ouA (u w : ℝ) : ouA w * ouA u = ouA (u + w) := by
  rw [ouA, ouA, ouA, ← Real.exp_add]; congr 1; ring

private lemma ouS_add (u w : ℝ) : ouA w ^ 2 * ouS u + ouS w = ouS (u + w) := by
  rw [ouA_sq, ouS, ouS, ouS, neg_add, Real.exp_add]; ring

/-! ### Gaussian measures: scaling and the degenerate case -/

omit [MeasurableSpace E] [BorelSpace E] in
private lemma mehler_gaussDens_nonneg {v : ℝ} (hv : 0 < v) (y : E) : 0 ≤ gaussDens E v y := by
  unfold gaussDens; positivity

omit [MeasurableSpace E] [BorelSpace E] in
private lemma mehler_gaussDens_continuous (v : ℝ) : Continuous (gaussDens E v) := by
  unfold gaussDens; fun_prop

/-- Lemma 14.B(c), scaling case: the image of `g_v` under `z ↦ √s z` is `g_{v s}`. -/
private lemma mehler_gaussE_map_sqrt_smul {v s : ℝ} (hs : 0 ≤ s) :
    (gaussE E v).map (fun z => Real.sqrt s • z) = gaussE E (v * s) := by
  unfold gaussE
  rw [Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
  congr 1
  funext z
  simp only [Function.comp_apply, smul_smul]
  rw [mul_comm v s, Real.sqrt_mul hs]

/-- `T_u Φ(y) = ∫ Φ(a_u y + x) g_{v s_u}(dx)`. -/
private lemma mehlerL_eq_lintegral_gaussE {v u : ℝ} (hu : 0 ≤ u) {Φ : E → ℝ≥0∞}
    (hΦ : Measurable Φ) (y : E) :
    mehlerL v u Φ y = ∫⁻ x, Φ (ouA u • y + x) ∂gaussE E (v * ouS u) := by
  unfold mehlerL
  rw [← mehler_gaussE_map_sqrt_smul (ouS_nonneg hu),
    lintegral_map (f := fun x => Φ (ouA u • y + x)) (hΦ.comp (measurable_const_add _))
      (measurable_const_smul _)]

/-- `T_u Φ` is measurable for measurable `Φ`. -/
private lemma measurable_mehlerL (v u : ℝ) {Φ : E → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable (mehlerL v u Φ) := by
  unfold mehlerL
  exact (hΦ.comp (by fun_prop : Measurable fun p : E × E =>
    ouA u • p.1 + Real.sqrt (ouS u) • p.2)).lintegral_prod_right'

/-! ### Lemma 14.1 (i), (iii), (v) -/

/-- Lemma 14.1(i): the semigroup property on `[0, ∞]`-valued Borel functions. -/
theorem mehlerL_mehlerL {v : ℝ} (hv : 0 ≤ v) {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w)
    {Φ : E → ℝ≥0∞} (hΦ : Measurable Φ) :
    mehlerL v u (mehlerL v w Φ) = mehlerL v (u + w) Φ := by
  funext y
  set α := ouA w * Real.sqrt (ouS u)
  set β := Real.sqrt (ouS w)
  have hG : Measurable fun x : E => Φ (ouA (u + w) • y + x) := hΦ.comp (measurable_const_add _)
  have hm : Measurable fun p : E × E => α • p.1 + β • p.2 := by fun_prop
  have hab : (α ^ 2 + β ^ 2) * v = v * ouS (u + w) := by
    rw [mul_pow, Real.sq_sqrt (ouS_nonneg hu), Real.sq_sqrt (ouS_nonneg hw), ← ouS_add]; ring
  have h1 : mehlerL v u (mehlerL v w Φ) y =
      ∫⁻ p, Φ (ouA (u + w) • y + (α • p.1 + β • p.2)) ∂(gaussE E v).prod (gaussE E v) := by
    rw [lintegral_prod (fun p : E × E => Φ (ouA (u + w) • y + (α • p.1 + β • p.2)))
      (hG.comp hm).aemeasurable]
    unfold mehlerL
    refine lintegral_congr fun z => lintegral_congr fun z' => ?_
    congr 1
    rw [smul_add, smul_smul, smul_smul, ouA_mul_ouA, add_assoc]
  rw [h1, ← lintegral_map hG hm, gaussE_prod_map_add hv, hab,
    mehlerL_eq_lintegral_gaussE (add_nonneg hu hw) hΦ]

/-- Lemma 14.1(v): `∫ F dρ_u = ∫ T_u F dρ`. -/
theorem lintegral_ouLaw {v : ℝ} (hv : 0 ≤ v) {u : ℝ} (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F y ∂ouLaw v ρ u = ∫⁻ y, mehlerL v u F y ∂ρ := by
  have hm : Measurable fun p : E × E => ouA u • p.1 + Real.sqrt (ouS u) • p.2 := by fun_prop
  unfold ouLaw
  rw [lintegral_map hF hm,
    lintegral_prod (fun p : E × E => F (ouA u • p.1 + Real.sqrt (ouS u) • p.2))
      (hF.comp hm).aemeasurable]
  rfl

/-- `ρ_u` is a probability measure. -/
private lemma isProbabilityMeasure_ouLaw (v : ℝ) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (u : ℝ) : IsProbabilityMeasure (ouLaw v ρ u) := by
  unfold ouLaw
  infer_instance

/-- Lemma 14.1(i): `(ρ_u)_w = ρ_{u+w}`. -/
theorem ouLaw_ouLaw {v : ℝ} (hv : 0 ≤ v) {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) (ρ : Measure E)
    [IsProbabilityMeasure ρ] : ouLaw v (ouLaw v ρ u) w = ouLaw v ρ (u + w) := by
  have := isProbabilityMeasure_ouLaw v ρ u
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_ouLaw hv _ hF, lintegral_ouLaw hv _ (measurable_mehlerL v w hF),
    lintegral_ouLaw hv _ hF, mehlerL_mehlerL hv hu hw hF]

/-- Lemma 14.1(iii): `T_u` commutes with linear isometries. -/
theorem mehlerL_comp_isometry (v u : ℝ) (f : E ≃ₗᵢ[ℝ] E) {Φ : E → ℝ≥0∞} (hΦ : Measurable Φ) :
    mehlerL v u (Φ ∘ f) = mehlerL v u Φ ∘ f := by
  funext y
  simp only [mehlerL, Function.comp_apply, map_add, map_smul]
  conv_rhs => rw [← gaussE_map_isometry v f]
  rw [lintegral_map (f := fun z => Φ (ouA u • f y + Real.sqrt (ouS u) • z))
    (hΦ.comp ((measurable_const_smul _).const_add _)) f.continuous.measurable]

/-! ### Lemma 14.E: the Mehler kernel -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The kernel is jointly continuous in `(y, w)`. -/
private lemma mehlerKernel_continuous (v u : ℝ) :
    Continuous fun p : E × E => mehlerKernel v u p.1 p.2 := by
  unfold mehlerKernel; fun_prop

private lemma measurable_ofReal_mehlerKernel (v u : ℝ) :
    Measurable fun p : E × E => ENNReal.ofReal (mehlerKernel v u p.1 p.2) :=
  ENNReal.measurable_ofReal.comp (mehlerKernel_continuous v u).measurable

private lemma measurable_ofReal_mehlerKernel_left (v u : ℝ) (w : E) :
    Measurable fun y => ENNReal.ofReal (mehlerKernel v u y w) := by
  have h := (measurable_ofReal_mehlerKernel v u).comp (measurable_prodMk_right (y := w))
  exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(a): `K > 0`. -/
theorem mehlerKernel_pos (v : ℝ) {u : ℝ} (hu : 0 < u) (y w : E) : 0 < mehlerKernel v u y w := by
  unfold mehlerKernel
  exact mul_pos (Real.rpow_pos_of_pos (ouS_pos hu) _) (Real.exp_pos _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(a): `K(u, y, w) = K(u, w, y)`. -/
theorem mehlerKernel_comm (v u : ℝ) (y w : E) : mehlerKernel v u y w = mehlerKernel v u w y := by
  unfold mehlerKernel
  rw [real_inner_comm, add_comm (‖y‖ ^ 2)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(a): `γ_v(w) K(u, y, w) = γ_{v s_u}(w - a_u y)`. -/
theorem mehlerKernel_mul_gaussDens {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (y w : E) :
    mehlerKernel v u y w * gaussDens E v w = gaussDens E (v * ouS u) (w - ouA u • y) := by
  have hs := ouS_pos hu
  have hs' : ouS u = 1 - ouA u ^ 2 := by linarith [ouA_sq_add_ouS u]
  unfold mehlerKernel gaussDens
  rw [show 2 * π * (v * ouS u) = (2 * π * v) * ouS u by ring, Real.mul_rpow (by positivity) hs.le,
    show ∀ A B C D : ℝ, A * B * (C * D) = C * A * (B * D) from fun _ _ _ _ => by ring,
    ← Real.exp_add]
  congr 2
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos (ouA_pos u),
    real_inner_comm]
  field_simp
  rw [hs']
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(a): `γ_v(y) K(u, y, w) = γ_{v s_u}(y - a_u w)`. -/
theorem mehlerKernel_mul_gaussDens' {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (y w : E) :
    mehlerKernel v u y w * gaussDens E v y = gaussDens E (v * ouS u) (y - ouA u • w) := by
  rw [mehlerKernel_comm, mehlerKernel_mul_gaussDens hv hu]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(d): `K(u, y, w) ≤ s_u^{-d/2} e^{|y|²/(2v)}`. -/
theorem mehlerKernel_le {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (y w : E) :
    mehlerKernel v u y w ≤
      ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)) := by
  have hs := ouS_pos hu
  have hs' : ouS u = 1 - ouA u ^ 2 := by linarith [ouA_sq_add_ouS u]
  have h1 : 0 ≤ ‖y - ouA u • w‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos (ouA_pos u)]
    at h1
  unfold mehlerKernel
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hs.le _)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (2 * ouA u * inner ℝ y w - ouA u ^ 2 * (‖y‖ ^ 2 + ‖w‖ ^ 2)) * (2 * v) -
      ‖y‖ ^ 2 * (2 * v * ouS u) =
      -(2 * v) * (‖y‖ ^ 2 - 2 * (ouA u * inner ℝ y w) + (ouA u * ‖w‖) ^ 2) := by
    rw [hs']; ring
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * v) h1]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(d): `γ_v(y) K(u, y, w) ≤ (2π v s_u)^{-d/2} exp(-((|y| - |w|)₊)² / (2v))`. -/
theorem mehlerKernel_mul_gaussDens_le {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (y w : E) :
    mehlerKernel v u y w * gaussDens E v y ≤
      (2 * π * v * ouS u) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-(max (‖y‖ - ‖w‖) 0) ^ 2 / (2 * v)) := by
  have hs := ouS_pos hu
  have hs1 := ouS_le_one u
  rw [mehlerKernel_mul_gaussDens' hv hu]
  unfold gaussDens
  rw [show 2 * π * (v * ouS u) = 2 * π * v * ouS u by ring]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg (by positivity) _)
  have hm0 : 0 ≤ max (‖y‖ - ‖w‖) 0 := le_max_right _ _
  have hm : max (‖y‖ - ‖w‖) 0 ≤ ‖y - ouA u • w‖ := by
    refine max_le ?_ (norm_nonneg _)
    have h2 : ‖ouA u • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ouA_pos u)]
      exact mul_le_of_le_one_left (norm_nonneg _) (ouA_le_one hu.le)
    linarith [norm_sub_norm_le y (ouA u • w)]
  rw [neg_div, neg_div, neg_le_neg_iff]
  calc max (‖y‖ - ‖w‖) 0 ^ 2 / (2 * v) ≤ ‖y - ouA u • w‖ ^ 2 / (2 * v) := by gcongr
    _ ≤ ‖y - ouA u • w‖ ^ 2 / (2 * (v * ouS u)) := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        nlinarith

/-- Lemma 14.E(b): `T_u Φ(y) = ∫ Φ(w) K(u, y, w) g_v(dw)` for Borel `Φ ≥ 0`. -/
theorem mehlerL_eq_lintegral_kernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u)
    {Φ : E → ℝ≥0∞} (hΦ : Measurable Φ) (y : E) :
    mehlerL v u Φ y = ∫⁻ w, Φ w * ENNReal.ofReal (mehlerKernel v u y w) ∂gaussE E v := by
  have hs := ouS_pos hu
  have hK : Measurable fun w => mehlerKernel v u y w :=
    ((mehlerKernel_continuous v u).comp (Continuous.prodMk_right y)).measurable
  have hd : ∀ v', Measurable fun x : E => ENNReal.ofReal (gaussDens E v' x) := fun v' =>
    ENNReal.measurable_ofReal.comp (mehler_gaussDens_continuous v').measurable
  rw [mehlerL_eq_lintegral_gaussE hu.le hΦ, gaussE_eq_withDensity (mul_pos hv hs),
    gaussE_eq_withDensity hv,
    lintegral_withDensity_eq_lintegral_mul _ (hd _)
      (by fun_prop : Measurable fun x => Φ (ouA u • y + x)),
    lintegral_withDensity_eq_lintegral_mul _ (hd _)
      (show Measurable fun w => Φ w * ENNReal.ofReal (mehlerKernel v u y w) from
        hΦ.mul (ENNReal.measurable_ofReal.comp hK))]
  conv_rhs => rw [← lintegral_add_left_eq_self _ (ouA u • y)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  have h := mehlerKernel_mul_gaussDens hv hu y (ouA u • y + x)
  rw [add_sub_cancel_left] at h
  rw [mul_left_comm, ← ENNReal.ofReal_mul (mehler_gaussDens_nonneg hv _),
    mul_comm (gaussDens E v _), h, mul_comm]

/-- Lemma 14.E(b), real-valued form: `T_u Φ(y) = ∫ Φ(w) K(u, y, w) g_v(dw)` for Borel `Φ`, as an
identity of Bochner integrals with no integrability hypothesis. -/
theorem mehler_eq_integral_kernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u)
    {Φ : E → ℝ} (hΦ : Measurable Φ) (y : E) :
    mehler v u Φ y = ∫ w, Φ w * mehlerKernel v u y w ∂gaussE E v := by
  have hs := ouS_pos hu
  have hd : ∀ v', Measurable fun x : E => ENNReal.ofReal (gaussDens E v' x) := fun v' =>
    ENNReal.measurable_ofReal.comp (mehler_gaussDens_continuous v').measurable
  have hmap : mehler v u Φ y =
      ∫ x, Φ (ouA u • y + x) ∂(gaussE E v).map (fun z => Real.sqrt (ouS u) • z) :=
    (integral_map (measurable_const_smul _).aemeasurable
      (hΦ.comp (measurable_const_add _)).aestronglyMeasurable).symm
  rw [hmap, mehler_gaussE_map_sqrt_smul hs.le, gaussE_eq_withDensity (mul_pos hv hs),
    gaussE_eq_withDensity hv,
    integral_withDensity_eq_integral_toReal_smul (hd _)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (hd _)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  conv_rhs => rw [← integral_add_left_eq_self _ (ouA u • y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  have h := mehlerKernel_mul_gaussDens hv hu y (ouA u • y + x)
  rw [add_sub_cancel_left] at h
  rw [ENNReal.toReal_ofReal (mehler_gaussDens_nonneg (mul_pos hv hs) _),
    ENNReal.toReal_ofReal (mehler_gaussDens_nonneg hv _), ← h]
  ring

/-! ### Lemma 14.1 (ii), (iv) -/

omit [FiniteDimensional ℝ E] in
/-- The kernel `K(u, y, ·)` is integrable for every probability measure. -/
private lemma integrable_mehlerKernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (ρ : Measure E)
    [IsProbabilityMeasure ρ] (y : E) : Integrable (fun w => mehlerKernel v u y w) ρ :=
  Integrable.of_bound
    ((mehlerKernel_continuous v u).comp (Continuous.prodMk_right y)).aestronglyMeasurable
    (ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (‖y‖ ^ 2 / (2 * v)))
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (mehlerKernel_pos v hu y w)]
      exact mehlerKernel_le hv hu y w)

/-- Lemma 14.1(iv): `ρ_u = Ψ(u, ·) g_v` with the everywhere positive density `Ψ`. -/
theorem ouLaw_eq_withDensity {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (ρ : Measure E)
    [IsProbabilityMeasure ρ] :
    ouLaw v ρ u = (gaussE E v).withDensity (fun y => ENNReal.ofReal (ouDensity v ρ u y)) ∧
      ∀ y, 0 < ouDensity v ρ u y := by
  have hK := measurable_ofReal_mehlerKernel (E := E) v u
  have hdens : (fun y => ENNReal.ofReal (ouDensity v ρ u y)) =
      fun y => ∫⁻ w, ENNReal.ofReal (mehlerKernel v u w y) ∂ρ := by
    funext y
    rw [ouDensity, ofReal_integral_eq_lintegral_ofReal (integrable_mehlerKernel hv hu ρ y)
      (ae_of_all _ fun w => (mehlerKernel_pos v hu y w).le)]
    simp_rw [mehlerKernel_comm v u y]
  refine ⟨?_, fun y => ?_⟩
  · rw [hdens]
    have h2 : Measurable fun p : E × E => ENNReal.ofReal (mehlerKernel v u p.2 p.1) := by
      have h := hK.comp measurable_swap
      exact h
    have hdm : Measurable fun y => ∫⁻ w, ENNReal.ofReal (mehlerKernel v u w y) ∂ρ :=
      h2.lintegral_prod_right'
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    have hsw : Measurable (Function.uncurry fun y w : E =>
        F w * ENNReal.ofReal (mehlerKernel v u y w)) := by
      have h := (hF.comp measurable_snd).mul hK
      exact h
    rw [lintegral_withDensity_eq_lintegral_mul _ hdm hF, lintegral_ouLaw hv.le ρ hF]
    calc ∫⁻ y, mehlerL v u F y ∂ρ
        = ∫⁻ y, ∫⁻ w, F w * ENNReal.ofReal (mehlerKernel v u y w) ∂gaussE E v ∂ρ :=
          lintegral_congr fun y => mehlerL_eq_lintegral_kernel hv hu hF y
      _ = ∫⁻ w, ∫⁻ y, F w * ENNReal.ofReal (mehlerKernel v u y w) ∂ρ ∂gaussE E v :=
          lintegral_lintegral_swap hsw.aemeasurable
      _ = ∫⁻ w, F w * ∫⁻ y, ENNReal.ofReal (mehlerKernel v u y w) ∂ρ ∂gaussE E v :=
          lintegral_congr fun w => lintegral_const_mul _
            (measurable_ofReal_mehlerKernel_left v u w)
      _ = _ := lintegral_congr fun w => by simp only [Pi.mul_apply]; rw [mul_comm]
  · rw [ouDensity, integral_pos_iff_support_of_nonneg (fun w => (mehlerKernel_pos v hu y w).le)
      (integrable_mehlerKernel hv hu ρ y)]
    have : Function.support (fun w => mehlerKernel v u y w) = Set.univ :=
      Set.eq_univ_iff_forall.2 fun w => Function.mem_support.2 (mehlerKernel_pos v hu y w).ne'
    rw [this, measure_univ]
    exact one_pos

/-! ### Lemma 14.1 (vi) -/

/-- `(x + y)^q ≤ 2^q (x^q + y^q)` for `x, y ≥ 0` and `q ≥ 0`. -/
private lemma mehler_add_rpow_le {x y q : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hq : 0 ≤ q) :
    (x + y) ^ q ≤ 2 ^ q * (x ^ q + y ^ q) := by
  have hm : x + y ≤ 2 * max x y := by linarith [le_max_left x y, le_max_right x y]
  calc (x + y) ^ q ≤ (2 * max x y) ^ q := Real.rpow_le_rpow (by positivity) hm hq
    _ = 2 ^ q * max x y ^ q := Real.mul_rpow (by norm_num) (le_max_of_le_left hx)
    _ ≤ 2 ^ q * (x ^ q + y ^ q) := by
        gcongr
        rcases le_total x y with h | h
        · rw [max_eq_right h]; linarith [Real.rpow_nonneg hx q]
        · rw [max_eq_left h]; linarith [Real.rpow_nonneg hy q]

/-- Lemma 14.1(vi), `[0, ∞]`-valued form: for `q ≥ 0`,
`∫ |y|^q ρ_u(dy) ≤ 2^q (∫ |w|^q ρ(dw) + (v s_u)^{q/2} ∫ |z|^q g_1(dz))`. -/
theorem lintegral_norm_rpow_ouLaw_le {v : ℝ} (hv : 0 ≤ v) {u : ℝ} (hu : 0 ≤ u) {q : ℝ}
    (hq : 0 ≤ q) (ρ : Measure E) [IsProbabilityMeasure ρ] :
    ∫⁻ y, ENNReal.ofReal (‖y‖ ^ q) ∂ouLaw v ρ u ≤
      ENNReal.ofReal (2 ^ q) * (∫⁻ w, ENNReal.ofReal (‖w‖ ^ q) ∂ρ +
        ENNReal.ofReal ((v * ouS u) ^ (q / 2)) *
          ∫⁻ z, ENNReal.ofReal (‖z‖ ^ q) ∂gaussE E 1) := by
  set c := Real.sqrt (ouS u) * Real.sqrt v with hc_def
  have hc : 0 ≤ c := by positivity
  have hcq : c ^ q = (v * ouS u) ^ (q / 2) := by
    rw [hc_def, ← Real.sqrt_mul (ouS_nonneg hu), mul_comm (ouS u), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (mul_nonneg hv (ouS_nonneg hu))]
    ring_nf
  have hmeas : Measurable fun y : E => ENNReal.ofReal (‖y‖ ^ q) := by fun_prop
  have hg : gaussE E v = (gaussE E 1).map (fun z => Real.sqrt v • z) := by
    rw [mehler_gaussE_map_sqrt_smul hv, one_mul]
  set I := ∫⁻ z, ENNReal.ofReal (‖z‖ ^ q) ∂gaussE E 1
  have step : ∀ y : E, mehlerL v u (fun y => ENNReal.ofReal (‖y‖ ^ q)) y ≤
      ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal (‖y‖ ^ q) + ENNReal.ofReal (c ^ q) * I) := by
    intro y
    rw [mehlerL, hg, lintegral_map (f := fun z => ENNReal.ofReal (‖ouA u • y +
      Real.sqrt (ouS u) • z‖ ^ q)) (by fun_prop) (measurable_const_smul _)]
    calc ∫⁻ z, ENNReal.ofReal (‖ouA u • y + Real.sqrt (ouS u) • Real.sqrt v • z‖ ^ q)
          ∂gaussE E 1
        ≤ ∫⁻ z, ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal (‖y‖ ^ q) +
            ENNReal.ofReal (c ^ q) * ENNReal.ofReal (‖z‖ ^ q)) ∂gaussE E 1 := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖ouA u • y + Real.sqrt (ouS u) • Real.sqrt v • z‖ ≤ ‖y‖ + c * ‖z‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [smul_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (ouA_pos u), abs_of_nonneg hc]
            gcongr
            exact mul_le_of_le_one_left (norm_nonneg _) (ouA_le_one hu)
          calc ‖ouA u • y + Real.sqrt (ouS u) • Real.sqrt v • z‖ ^ q
              ≤ (‖y‖ + c * ‖z‖) ^ q := Real.rpow_le_rpow (norm_nonneg _) h1 hq
            _ ≤ 2 ^ q * (‖y‖ ^ q + (c * ‖z‖) ^ q) :=
                mehler_add_rpow_le (norm_nonneg _) (by positivity) hq
            _ = 2 ^ q * (‖y‖ ^ q + c ^ q * ‖z‖ ^ q) := by rw [Real.mul_rpow hc (norm_nonneg _)]
      _ = ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal (‖y‖ ^ q) + ENNReal.ofReal (c ^ q) * I) := by
          rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left measurable_const,
            lintegral_const, measure_univ, mul_one, lintegral_const_mul _ (by fun_prop)]
  rw [lintegral_ouLaw hv ρ hmeas, ← hcq]
  calc ∫⁻ y, mehlerL v u (fun y => ENNReal.ofReal (‖y‖ ^ q)) y ∂ρ
      ≤ ∫⁻ y, ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal (‖y‖ ^ q) + ENNReal.ofReal (c ^ q) * I)
          ∂ρ := lintegral_mono step
    _ = _ := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_right _ measurable_const,
          lintegral_const, measure_univ, mul_one]

/-- Lemma 14.1(vi): `∫ |y|^q ρ_u(dy) < ∞` whenever `∫ |w|^q ρ(dw) < ∞` (`q ≥ 0`). -/
theorem mehler_lintegral_norm_rpow_ouLaw_lt_top {v : ℝ} (hv : 0 ≤ v) {u : ℝ} (hu : 0 ≤ u)
    {q : ℝ} (hq : 0 ≤ q) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (hρ : ∫⁻ w, ENNReal.ofReal (‖w‖ ^ q) ∂ρ < ∞) :
    ∫⁻ y, ENNReal.ofReal (‖y‖ ^ q) ∂ouLaw v ρ u < ∞ :=
  (lintegral_norm_rpow_ouLaw_le hv hu hq ρ).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.2 ⟨hρ, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (integrable_norm_rpow_gaussE 1 q hq).lintegral_lt_top⟩))

/-! ### Lemma 14.E(c): derivatives of the kernel -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `K(u, ·, w)` at `y` is `e ↦ ⟨e, V⟩ K` with `V = a_u (w - a_u y) / (v s_u)`. -/
private lemma mehlerKernel_hasFDerivAt (v u : ℝ) (y w : E) :
    HasFDerivAt (fun y' => mehlerKernel v u y' w)
      (mehlerKernel v u y w • innerSL ℝ ((ouA u / (v * ouS u)) • (w - ouA u • y))) y := by
  have e1 : (fun y' : E => inner ℝ y' w) = fun y' => innerSL ℝ w y' := by
    funext y'; simp [real_inner_comm]
  have h1 : HasFDerivAt (fun y' : E => inner ℝ y' w) (innerSL ℝ w) y := by
    rw [e1]; exact (innerSL ℝ w).hasFDerivAt
  have h2 : HasFDerivAt (fun y' : E => ‖y'‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h4 : HasFDerivAt (fun y' : E => 2 * ouA u * inner ℝ y' w - ouA u ^ 2 * (‖y'‖ ^ 2 + ‖w‖ ^ 2))
      ((2 * ouA u) • innerSL ℝ w - (ouA u ^ 2) • (2 • innerSL ℝ y)) y :=
    HasFDerivAt.sub (h1.const_mul (2 * ouA u)) ((h2.add_const (‖w‖ ^ 2)).const_mul (ouA u ^ 2))
  have h5 := HasFDerivAt.const_mul (HasFDerivAt.exp (HasFDerivAt.mul_const h4
    (2 * v * ouS u)⁻¹)) (ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2))
  have hd : ∀ x : ℝ, x / (2 * v * ouS u) = x * (2 * v * ouS u)⁻¹ := fun x => div_eq_mul_inv _ _
  unfold mehlerKernel
  simp only [hd]
  convert h5 using 1
  ext h
  simp
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(c): `∇_y K(u, y, w) = K(u, y, w) V` with `V = a_u (w - a_u y) / (v s_u)`, i.e.
`∂_e K = ⟨e, V⟩ K`. -/
theorem mehlerKernel_hasGradientAt (v u : ℝ) (y w : E) :
    HasGradientAt (fun y' => mehlerKernel v u y' w)
      (mehlerKernel v u y w • ((ouA u / (v * ouS u)) • (w - ouA u • y))) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert mehlerKernel_hasFDerivAt v u y w using 1
  ext h
  simp [InnerProductSpace.toDual_apply_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(c): `Δ_y K(u, y, w) = (|V|² - d c_u) K(u, y, w)` with
`V = a_u (w - a_u y) / (v s_u)` and `c_u = a_u² / (v s_u)` (equivalently
`∂_{e'} ⟨e, V⟩ = -c_u ⟨e, e'⟩`). -/
theorem mehlerKernel_laplacian (v u : ℝ) (y w : E) :
    Laplacian.laplacian (fun y' => mehlerKernel v u y' w) y =
      (‖(ouA u / (v * ouS u)) • (w - ouA u • y)‖ ^ 2 -
        Module.finrank ℝ E * (ouA u ^ 2 / (v * ouS u))) * mehlerKernel v u y w := by
  set k := ouA u / (v * ouS u) with hk
  have hfd : fderiv ℝ (fun y' => mehlerKernel v u y' w) =
      fun y' => mehlerKernel v u y' w • innerSL ℝ (k • (w - ouA u • y')) :=
    funext fun y' => (mehlerKernel_hasFDerivAt v u y' w).fderiv
  have hV : HasFDerivAt (fun y' : E => innerSL ℝ (k • (w - ouA u • y')))
      ((innerSL ℝ).comp (k • ((0 : E →L[ℝ] E) - ouA u • ContinuousLinearMap.id ℝ E))) y :=
    (innerSL ℝ).hasFDerivAt.comp y
      (((hasFDerivAt_const w y).sub ((hasFDerivAt_id y).const_smul (ouA u))).const_smul k)
  have h2 := (mehlerKernel_hasFDerivAt v u y w).smul hV
  have h3 := h2.fderiv
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  simp only [iteratedFDeriv_two_apply, hfd]
  have h4 : fderiv ℝ (fun y' => mehlerKernel v u y' w • innerSL ℝ (k • (w - ouA u • y'))) y =
      fderiv ℝ ((fun y' => mehlerKernel v u y' w) • fun y' => innerSL ℝ (k • (w - ouA u • y')))
        y := rfl
  rw [h4, h3]
  simp only [← hk]
  set b := stdOrthonormalBasis ℝ E
  have hb1 : ∀ i, inner ℝ (b i) (b i) = (1 : ℝ) := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
  have hsum : ∑ i, (inner ℝ w (b i) - ouA u * inner ℝ y (b i)) ^ 2 = ‖w - ouA u • y‖ ^ 2 := by
    rw [← b.sum_sq_inner_right (w - ouA u • y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm w, real_inner_comm y]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    ContinuousLinearMap.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
    inner_smul_left, inner_sub_left, zero_sub, RCLike.conj_to_real,
    neg_apply, inner_neg_left]
  calc ∑ i, _ = ∑ i, mehlerKernel v u y w *
        (k ^ 2 * (inner ℝ w (b i) - ouA u * inner ℝ y (b i)) ^ 2 - k * ouA u) :=
      Finset.sum_congr rfl fun i _ => by rw [hb1]; ring
    _ = mehlerKernel v u y w * (k ^ 2 * ∑ i, (inner ℝ w (b i) - ouA u * inner ℝ y (b i)) ^ 2 -
        ∑ _i : Fin (Module.finrank ℝ E), k * ouA u) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_smul,
        mul_pow, Real.norm_eq_abs, sq_abs, hk]
      ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(c): `∂_u K = A_y K` with `A = (v/2) Δ - (1/2) ⟨y, ∇⟩` acting on the variable `y`. -/
theorem hasDerivAt_mehlerKernel {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u) (y w : E) :
    HasDerivAt (fun u' => mehlerKernel v u' y w)
      (v / 2 * Laplacian.laplacian (fun y' => mehlerKernel v u y' w) y -
        1 / 2 * inner ℝ y (gradient (fun y' => mehlerKernel v u y' w) y)) u := by
  rw [mehlerKernel_laplacian, (mehlerKernel_hasGradientAt v u y w).gradient]
  have hs0 := ouS_pos hu
  have ha : HasDerivAt ouA (-(ouA u) / 2) u := by
    have := ((hasDerivAt_neg u).div_const 2).exp
    convert this using 1 <;> first | rfl | (rw [ouA]; ring)
  have hs : HasDerivAt ouS (ouA u ^ 2) u := by
    have := ((hasDerivAt_neg u).exp).const_sub 1
    rw [ouA_sq]
    convert this using 1 <;> first | (funext x; rfl) | ring
  have hpow := hs.rpow_const (p := -(Module.finrank ℝ E : ℝ) / 2) (Or.inl hs0.ne')
  have hN : HasDerivAt (fun u' => 2 * ouA u' * inner ℝ y w - ouA u' ^ 2 * (‖y‖ ^ 2 + ‖w‖ ^ 2))
      (2 * (-(ouA u) / 2) * inner ℝ y w - (2 * ouA u * (-(ouA u) / 2)) * (‖y‖ ^ 2 + ‖w‖ ^ 2))
      u := by
    have := ((ha.const_mul 2).mul_const (inner ℝ y w)).sub ((ha.pow 2).mul_const
      (‖y‖ ^ 2 + ‖w‖ ^ 2))
    convert this using 1
    push_cast; ring
  have hD : HasDerivAt (fun u' => 2 * v * ouS u') (2 * v * ouA u ^ 2) u := hs.const_mul (2 * v)
  have hQ := hN.fun_div hD (by positivity)
  have hK := hpow.mul hQ.exp
  unfold mehlerKernel
  convert hK using 1
  rw [Real.rpow_sub_one hs0.ne']
  have hs' : ouS u = 1 - ouA u ^ 2 := by linarith [ouA_sq_add_ouS u]
  set S := ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2)
  set X := Real.exp ((2 * ouA u * inner ℝ y w - ouA u ^ 2 * (‖y‖ ^ 2 + ‖w‖ ^ 2)) /
    (2 * v * ouS u))
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real,
    abs_of_pos (ouA_pos u), real_inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_comm w y]
  field_simp
  rw [hs']
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lemma 14.E(c): `K ∈ C^∞((0, ∞) × E × E)`. -/
theorem mehlerKernel_contDiffOn {v : ℝ} (hv : 0 < v) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E × E => mehlerKernel v p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hS : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E × E => ouS p.1 := by unfold ouS; fun_prop
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E × E => ouA p.1 := by unfold ouA; fun_prop
  have hpos : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (E × E)), ouS p.1 ≠ 0 :=
    fun p hp => (ouS_pos hp.1).ne'
  have hnum : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E × E =>
      2 * ouA p.1 * inner ℝ p.2.1 p.2.2 - ouA p.1 ^ 2 * (‖p.2.1‖ ^ 2 + ‖p.2.2‖ ^ 2) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E × E => inner ℝ p.2.1 p.2.2 :=
      contDiff_inner.comp (contDiff_snd.fst.prodMk contDiff_snd.snd)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E × E => ‖p.2.1‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp contDiff_snd.fst
    have h3 : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × E × E => ‖p.2.2‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp contDiff_snd.snd
    exact ((contDiff_const.mul hA).mul h1).sub ((hA.pow 2).mul (h2.add h3))
  unfold mehlerKernel
  refine (hS.contDiffOn.rpow_const_of_ne hpos).mul ?_
  refine Real.contDiff_exp.comp_contDiffOn (hnum.contDiffOn.div
    (contDiff_const.mul hS).contDiffOn fun p hp => ?_)
  exact mul_ne_zero (by positivity) (hpos p hp)

end Mehler

end Rigidity
