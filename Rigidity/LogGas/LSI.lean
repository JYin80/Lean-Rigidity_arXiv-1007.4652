import Rigidity.Flow.Chamber
import Rigidity.LogGas.Defs
import Rigidity.LogGas.PrekopaLeindler

/-!
# Logarithmic Sobolev inequality for convex log-gases

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The file proves Theorem 17.4 (`logSobolev`): for a convex log-gas `ω` (Definition 17.2) with
`κ > 0` and `q ∈ C²(ℝ^N)`, `q > 0`, `∫ q dω = 1`,
`∫ (q log q - q + 1) dω ≤ (2κ)⁻¹ ∫ |∇q|²/q dω` (17.8), both sides in `[0, ∞]`.

The proof follows the proof of Theorem 17.4.
* Step 1, (17.9): for `g` bounded, with bounded gradient and with the quadratic upper bound
  `g(w) ≤ g(z) + Dg(z)(w - z) + (M/2)|w - z|²`, Step 1a and the Prékopa–Leindler inequality
  (Theorem 17.1) give (17.10). In Step 1c the integrals `a(s)`, `b(s)` are bounded by
  `e^{g/(1-s)} ≥ e^g (1 + s g/(1-s))` and `e^{g + c|∇g|²} ≤ e^g (1 + c|∇g|² e^{c G₁})`, and the
  right derivatives at `s = 0` of the two resulting explicit functions of `s` are compared.
* Step 2: Step 1 is applied to `g = log q_t`, `q_t = q χ_t² + t`, with the cutoff
  `χ_t(x) = ψ(t² |x|²)`; the parameters `1/k`, `1/r` and `η` of Steps 2a–2c are all taken equal
  to `t`, so that (17.13) becomes `∫ |∇q_t|²/q_t ≤ (1 + t) 𝓘 + 64 L² (1 + t) t` with
  `L = sup |ψ'|`. Fatou's lemma along `t = 1/(n + 1) → 0` (Step 2d) concludes.

All Euclidean norms are written as sums `∑ x_i²`; the bound `M` is obtained from the Lipschitz
constant of `Dg` for the sup norm of `ℝ^N`, which only affects `s₀` in Step 1a.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `𝓥` is measurable on `ℝ^N`. -/
private theorem LSI_measurable_logGasH {N : ℕ} (β : ℝ) {V₀ : (Fin N → ℝ) → ℝ}
    (hV : Continuous V₀) : Measurable (logGasH β V₀) := by
  unfold logGasH
  refine hV.measurable.sub (measurable_const.mul ?_)
  refine Finset.measurable_sum _ fun p _ => ?_
  exact Real.measurable_log.comp ((measurable_pi_apply _).sub (measurable_pi_apply _))

/-- The density `e^{-𝓥}` is measurable. -/
private theorem LSI_measurable_rho {N : ℕ} (β : ℝ) {V₀ : (Fin N → ℝ) → ℝ}
    (hV : Continuous V₀) :
    Measurable fun x => ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (LSI_measurable_logGasH β hV).neg)

/-- `Z = ∫_Σ e^{-𝓥} dx > 0` (Definition 17.2, Comment (1)). -/
private theorem LSI_Z_pos {N : ℕ} (β : ℝ) {V₀ : (Fin N → ℝ) → ℝ} (hV : Continuous V₀) :
    0 < ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) := by
  rw [setLIntegral_pos_iff (LSI_measurable_rho β hV)]
  have hsupp : Function.support (fun x => ENNReal.ofReal (Real.exp (-logGasH β V₀ x))) =
      Set.univ := by
    ext x; simp [Real.exp_pos]
  rw [hsupp, Set.univ_inter]
  refine (isOpen_chamber N).measure_pos volume ⟨fun i => (i : ℝ), ?_⟩
  intro i j hij
  exact Nat.cast_lt.2 hij

/-- A convex log-gas is a probability measure (Definition 17.2). -/
private theorem LSI_isProbabilityMeasure {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) : IsProbabilityMeasure (logGasMeasure β V₀) := by
  constructor
  unfold logGasMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (LSI_Z_pos β hω.cont).ne' hω.finite.ne

/-- `∫⁻ f dω = Z⁻¹ ∫⁻_Σ e^{-𝓥} f dx`. -/
private theorem LSI_lintegral_eq {N : ℕ} (β : ℝ) {V₀ : (Fin N → ℝ) → ℝ} (hV : Continuous V₀)
    {f : (Fin N → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂logGasMeasure β V₀ =
      (∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)))⁻¹ *
        ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) * f x := by
  unfold logGasMeasure
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ (LSI_measurable_rho β hV) hf]
  rfl

/-- A linear functional on `ℝ^N` in coordinates: `L v = ∑ v_i L(e_i)`. -/
private theorem LSI_clm_apply {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ) (v : Fin N → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (v i) = v i • (Pi.single i (1 : ℝ) : Fin N → ℝ) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- Step 1a of the proof of Theorem 17.4: for `x, y ∈ Σ`, `z = τ x + (1 - τ) y` and
`κτ - M(1 - τ) > 0`, `g(x) - τ𝓥(x) - (1 - τ)𝓥(y) ≤ g_τ(z) - 𝓥(z)`. -/
private theorem LSI_step1a {N : ℕ} {β κ M τ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hc : 0 < κ * τ - M * (1 - τ)) {g : (Fin N → ℝ) → ℝ}
    (hup : ∀ z w, g w ≤ g z + fderiv ℝ g z (w - z) + M / 2 * ∑ i, (w i - z i) ^ 2)
    {x y : Fin N → ℝ} (hx : x ∈ chamber N) (hy : y ∈ chamber N) :
    g x - τ * logGasH β V₀ x - (1 - τ) * logGasH β V₀ y ≤
      g (τ • x + (1 - τ) • y) + (1 - τ) * (∑ i, pderiv i g (τ • x + (1 - τ) • y) ^ 2) /
        (2 * (κ * τ - M * (1 - τ))) - logGasH β V₀ (τ • x + (1 - τ) • y) := by
  set z := τ • x + (1 - τ) • y with hz
  set c := κ * τ - M * (1 - τ) with hcdef
  have hk := logGasH_kconvex hω hx hy (τ := τ) ⟨hτ0.le, hτ1.le⟩
  have hxz : ∀ i, x i - z i = (1 - τ) * (x i - y i) := fun i => by
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hu := hup z x
  rw [LSI_clm_apply] at hu
  simp only [Pi.sub_apply, hxz] at hu
  have hterm : ∀ i, (1 - τ) * (x i - y i) * pderiv i g z + M / 2 * ((1 - τ) * (x i - y i)) ^ 2
      - κ / 2 * τ * (1 - τ) * (x i - y i) ^ 2 ≤ (1 - τ) * pderiv i g z ^ 2 / (2 * c) := by
    intro i
    have h1 : 0 ≤ (1 - τ) * (pderiv i g z - c * (x i - y i)) ^ 2 / (2 * c) := by
      have : 0 ≤ 1 - τ := by linarith
      positivity
    have h2 : (1 - τ) * pderiv i g z ^ 2 / (2 * c) - ((1 - τ) * (x i - y i) * pderiv i g z +
        M / 2 * ((1 - τ) * (x i - y i)) ^ 2 - κ / 2 * τ * (1 - τ) * (x i - y i) ^ 2) =
        (1 - τ) * (pderiv i g z - c * (x i - y i)) ^ 2 / (2 * c) := by
      field_simp
      rw [hcdef]
      ring
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div] at hsum
  have e1 : ∑ i, M / 2 * ((1 - τ) * (x i - y i)) ^ 2 = M / 2 * ∑ i, ((1 - τ) * (x i - y i)) ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  have e2 : ∑ i, κ / 2 * τ * (1 - τ) * (x i - y i) ^ 2 =
      κ / 2 * τ * (1 - τ) * ∑ i, (x i - y i) ^ 2 := (Finset.mul_sum _ _ _).symm
  have e3 : ∑ i, (1 - τ) * pderiv i g z ^ 2 = (1 - τ) * ∑ i, pderiv i g z ^ 2 :=
    (Finset.mul_sum _ _ _).symm
  rw [e1, e2, e3] at hsum
  simp only [pderiv] at hsum ⊢
  linarith

/-- `|∇g|² = ∑ (∂_i g)²` is measurable. -/
private theorem LSI_measurable_grad {N : ℕ} (g : (Fin N → ℝ) → ℝ) :
    Measurable fun x => ∑ i, pderiv i g x ^ 2 :=
  Finset.measurable_sum _ fun _ _ => (measurable_fderiv_apply_const ℝ g _).pow_const 2

/-- `∫⁻ 𝟙_Σ e^{φ - 𝓥} dx = Z ∫⁻ e^φ dω`. -/
private theorem LSI_lintegral_indicator {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) {φ : (Fin N → ℝ) → ℝ} (hφ : Measurable φ) :
    ∫⁻ x, (chamber N).indicator (fun x => ENNReal.ofReal (Real.exp (φ x - logGasH β V₀ x))) x =
      (∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x))) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (φ x)) ∂logGasMeasure β V₀ := by
  rw [LSI_lintegral_eq β hω.cont (f := fun x => ENNReal.ofReal (Real.exp (φ x)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hφ)),
    ← mul_assoc, ENNReal.mul_inv_cancel (LSI_Z_pos β hω.cont).ne' hω.finite.ne, one_mul,
    lintegral_indicator (isOpen_chamber N).measurableSet]
  refine setLIntegral_congr_fun (isOpen_chamber N).measurableSet fun x _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- `∫⁻ e^φ dω = ofReal (∫ e^φ dω)` for measurable `φ ≤ C`. -/
private theorem LSI_lintegral_exp {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) {φ : (Fin N → ℝ) → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, φ x ≤ C) :
    Integrable (fun x => Real.exp (φ x)) (logGasMeasure β V₀) ∧
    ∫⁻ x, ENNReal.ofReal (Real.exp (φ x)) ∂logGasMeasure β V₀ =
      ENNReal.ofReal (∫ x, Real.exp (φ x) ∂logGasMeasure β V₀) := by
  have := LSI_isProbabilityMeasure hω
  have hi : Integrable (fun x => Real.exp (φ x)) (logGasMeasure β V₀) :=
    Integrable.of_bound (Real.measurable_exp.comp hφ).aestronglyMeasurable (Real.exp C)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hC x))
  exact ⟨hi, (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm⟩

/-- Step 1b of the proof of Theorem 17.4, (17.10): Prékopa–Leindler (Theorem 17.1) applied to
`e^{g/τ - 𝓥} 𝟙_Σ`, `e^{-𝓥} 𝟙_Σ` and `e^{g_τ - 𝓥} 𝟙_Σ`. -/
private theorem LSI_step1b {N : ℕ} {β κ M τ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hc : 0 < κ * τ - M * (1 - τ)) {g : (Fin N → ℝ) → ℝ} (hg : Continuous g) {G₀ G₁ : ℝ}
    (hG₀ : ∀ x, |g x| ≤ G₀) (hG₁ : ∀ x, ∑ i, pderiv i g x ^ 2 ≤ G₁)
    (hup : ∀ z w, g w ≤ g z + fderiv ℝ g z (w - z) + M / 2 * ∑ i, (w i - z i) ^ 2) :
    (∫ x, Real.exp (g x / τ) ∂logGasMeasure β V₀) ^ τ ≤
      ∫ x, Real.exp (g x + (1 - τ) * (∑ i, pderiv i g x ^ 2) / (2 * (κ * τ - M * (1 - τ))))
        ∂logGasMeasure β V₀ := by
  set c := κ * τ - M * (1 - τ) with hcdef
  set φ : (Fin N → ℝ) → ℝ := fun x => (1 - τ) * (∑ i, pderiv i g x ^ 2) / (2 * c) with hφdef
  have hφm : Measurable φ :=
    (measurable_const.mul (LSI_measurable_grad g)).div_const _
  have hgm : Measurable g := hg.measurable
  have h1τ : 0 < 1 - τ := by linarith
  have hφC : ∀ x, φ x ≤ (1 - τ) * G₁ / (2 * c) := fun x =>
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hG₁ x) h1τ.le) (by positivity)
  set Z := ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) with hZ
  have hZ0 : Z ≠ 0 := (LSI_Z_pos β hω.cont).ne'
  have hZt : Z ≠ ⊤ := hω.finite.ne
  have hmeasH := LSI_measurable_logGasH β hω.cont
  have hu : Measurable ((chamber N).indicator
      fun x => ENNReal.ofReal (Real.exp (g x / τ - logGasH β V₀ x))) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hgm.div_const _).sub hmeasH))).indicator (isOpen_chamber N).measurableSet
  have hv : Measurable ((chamber N).indicator
      fun x => ENNReal.ofReal (Real.exp (0 - logGasH β V₀ x))) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.sub hmeasH))).indicator (isOpen_chamber N).measurableSet
  have hw : Measurable ((chamber N).indicator
      fun x => ENNReal.ofReal (Real.exp ((g x + φ x) - logGasH β V₀ x))) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((hgm.add hφm).sub hmeasH))).indicator (isOpen_chamber N).measurableSet
  have hPL := prekopaLeindler N τ hτ0 hτ1 _ _ _ hu hv hw (by
    intro x y
    by_cases hx : x ∈ chamber N
    · by_cases hy : y ∈ chamber N
      · have hz : τ • x + (1 - τ) • y ∈ chamber N :=
          convex_chamber N hx hy hτ0.le h1τ.le (by ring)
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hτ0.le,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1τ.le,
          ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have := LSI_step1a hω hτ0 hτ1 hc hup hx hy
        have e : (g x / τ - logGasH β V₀ x) * τ = g x - τ * logGasH β V₀ x := by
          field_simp
        rw [e]
        simp only [hφdef]
        linarith
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos h1τ]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hτ0])
  rw [LSI_lintegral_indicator hω (hgm.div_const _), LSI_lintegral_indicator hω measurable_const,
    LSI_lintegral_indicator hω (φ := fun x => g x + φ x) (hgm.add hφm)] at hPL
  obtain ⟨-, ha⟩ := LSI_lintegral_exp hω (hgm.div_const τ) (C := G₀ / τ) fun x =>
    div_le_div_of_nonneg_right ((le_abs_self _).trans (hG₀ x)) hτ0.le
  obtain ⟨-, hb⟩ := LSI_lintegral_exp hω (φ := fun x => g x + φ x) (hgm.add hφm)
    (C := G₀ + (1 - τ) * G₁ / (2 * c))
    fun x => add_le_add ((le_abs_self _).trans (hG₀ x)) (hφC x)
  have := LSI_isProbabilityMeasure hω
  have h0 : ∫⁻ x, ENNReal.ofReal (Real.exp (0 : ℝ)) ∂logGasMeasure β V₀ = 1 := by simp
  rw [ha, hb, h0, mul_one, ENNReal.mul_rpow_of_nonneg _ _ hτ0.le, mul_comm (Z ^ τ), mul_assoc,
    ← ENNReal.rpow_add _ _ hZ0 hZt, add_sub_cancel, ENNReal.rpow_one, mul_comm _ Z,
    ENNReal.mul_le_mul_iff_right hZ0 hZt,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => (Real.exp_pos _).le) hτ0.le,
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => (Real.exp_pos _).le)] at hPL
  exact hPL

/-- A function `h` with `h(0) = 0`, `h ≥ 0` to the right of `0` and derivative `h'(0)` has
`h'(0) ≥ 0`; stated for `h = g - f`. -/
private theorem LSI_deriv_le {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasDerivAt f f' 0)
    (hg : HasDerivAt g g' 0) (h0 : f 0 = g 0) (hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s ≤ g s) :
    f' ≤ g' := by
  have h := (hg.sub hf).tendsto_slope_zero_right
  have : 0 ≤ g' - f' := by
    refine ge_of_tendsto h ?_
    filter_upwards [hle, self_mem_nhdsWithin] with s hs hpos
    simp only [zero_add, Pi.sub_apply, smul_eq_mul, h0, sub_self, sub_zero]
    exact mul_nonneg (inv_nonneg.2 (le_of_lt hpos)) (sub_nonneg.2 hs)
  linarith

/-- A bounded measurable function is `ω`-integrable. -/
private theorem LSI_integrable_of_bound {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) {F : (Fin N → ℝ) → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) : Integrable F (logGasMeasure β V₀) := by
  have := LSI_isProbabilityMeasure hω
  exact Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- Step 1 of the proof of Theorem 17.4, (17.9): for `g` bounded, with bounded gradient and with
the quadratic upper bound `g(w) ≤ g(z) + Dg(z)(w - z) + (M/2)|w - z|²`,
`∫ klFun(e^g) dω ≤ klFun(∫ e^g dω) + (2κ)⁻¹ ∫ |∇g|² e^g dω`. -/
private theorem LSI_step1 {N : ℕ} {β κ M : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) (hκ : 0 < κ) (hM : 0 ≤ M) {g : (Fin N → ℝ) → ℝ}
    (hg : Continuous g) {G₀ G₁ : ℝ} (hG₀ : ∀ x, |g x| ≤ G₀)
    (hG₁ : ∀ x, ∑ i, pderiv i g x ^ 2 ≤ G₁)
    (hup : ∀ z w, g w ≤ g z + fderiv ℝ g z (w - z) + M / 2 * ∑ i, (w i - z i) ^ 2) :
    ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (Real.exp (g x))) ∂logGasMeasure β V₀ ≤
      ENNReal.ofReal (InformationTheory.klFun (∫ x, Real.exp (g x) ∂logGasMeasure β V₀)) +
        ENNReal.ofReal (1 / (2 * κ)) *
          ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i g x ^ 2) * Real.exp (g x)) ∂logGasMeasure β V₀ := by
  have hP := LSI_isProbabilityMeasure hω
  set ω := logGasMeasure β V₀ with hωdef
  set S : (Fin N → ℝ) → ℝ := fun x => ∑ i, pderiv i g x ^ 2 with hSdef
  have hSm : Measurable S := LSI_measurable_grad g
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgm : Measurable g := hg.measurable
  have hK0 : 0 ≤ G₁ := (hS0 0).trans (hG₁ 0)
  have hG00 : 0 ≤ G₀ := (abs_nonneg _).trans (hG₀ 0)
  have hgle : ∀ x, g x ≤ G₀ := fun x => (le_abs_self _).trans (hG₀ x)
  have hexpg : ∀ x, Real.exp (g x) ≤ Real.exp G₀ := fun x => Real.exp_le_exp.2 (hgle x)
  have iE : Integrable (fun x => Real.exp (g x)) ω :=
    LSI_integrable_of_bound hω (Real.measurable_exp.comp hgm) (C := Real.exp G₀) fun x => by
      rw [abs_of_pos (Real.exp_pos _)]; exact hexpg x
  have iA : Integrable (fun x => g x * Real.exp (g x)) ω :=
    LSI_integrable_of_bound hω (hgm.mul (Real.measurable_exp.comp hgm))
      (C := G₀ * Real.exp G₀) fun x => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hG₀ x) (hexpg x) (Real.exp_pos _).le hG00
  have iB : Integrable (fun x => S x * Real.exp (g x)) ω :=
    LSI_integrable_of_bound hω (hSm.mul (Real.measurable_exp.comp hgm))
      (C := G₁ * Real.exp G₀) fun x => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hS0 x)]
      exact mul_le_mul (hG₁ x) (hexpg x) (Real.exp_pos _).le hK0
  set m := ∫ x, Real.exp (g x) ∂ω with hmdef
  set A := ∫ x, g x * Real.exp (g x) ∂ω with hAdef
  set B := ∫ x, S x * Real.exp (g x) ∂ω with hBdef
  have hm : 0 < m := integral_exp_pos iE
  -- the comparison functions
  set c : ℝ → ℝ := fun s => s / (2 * (κ - (κ + M) * s)) with hcdef
  set F : ℝ → ℝ := fun s => (1 - s) * Real.log (m + s / (1 - s) * A) with hFdef
  set G : ℝ → ℝ := fun s => Real.log (m + c s * Real.exp (c s * G₁) * B) with hGdef
  -- derivatives at `0`
  have hd1 : HasDerivAt (fun s : ℝ => s / (1 - s)) 1 0 := by
    have := (hasDerivAt_id' (0 : ℝ)).div ((hasDerivAt_id' (0 : ℝ)).const_sub 1) (by norm_num)
    convert this using 1; norm_num
  have hL : HasDerivAt (fun s : ℝ => m + s / (1 - s) * A) A 0 := by
    have := (hd1.mul_const A).const_add m
    convert this using 1; ring
  have hF : HasDerivAt F (-Real.log m + A / m) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_sub 1).mul (hL.log (by simp [hm.ne']))
    convert this using 1; simp
  have hc : HasDerivAt c (1 / (2 * κ)) 0 := by
    have h2 : HasDerivAt (fun s : ℝ => 2 * (κ - (κ + M) * s)) (2 * (-(κ + M))) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_mul (κ + M)).const_sub κ).const_mul 2
      convert this using 1; ring
    have := (hasDerivAt_id' (0 : ℝ)).div h2 (by simp [hκ.ne'])
    convert this using 1
    simp only [mul_zero, sub_zero, one_mul, zero_mul]
    field_simp
  have hc0 : c 0 = 0 := by simp [hcdef]
  have hce : HasDerivAt (fun s => c s * Real.exp (c s * G₁)) (1 / (2 * κ)) 0 := by
    have := hc.mul ((hc.mul_const G₁).exp)
    convert this using 1; simp [hc0]
  have hG : HasDerivAt G (1 / (2 * κ) * B / m) 0 := by
    have := ((hce.mul_const B).const_add m).log (by simp [hc0, hm.ne'])
    convert this using 1; simp [hc0]
  have hFG0 : F 0 = G 0 := by simp [hFdef, hGdef, hc0]
  -- the inequality to the right of `0`
  have hs₁ : 0 < κ / (κ + M) := div_pos hκ (by linarith)
  have hLpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < m + s / (1 - s) * A := by
    have hcont := hL.continuousAt
    have : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < m + s / (1 - s) * A :=
      hcont.eventually (lt_mem_nhds (by simpa using hm))
    exact nhdsWithin_le_nhds this
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < κ / (κ + M) :=
    nhdsWithin_le_nhds (gt_mem_nhds hs₁)
  have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), F s ≤ G s := by
    filter_upwards [hLpos, hsmall, self_mem_nhdsWithin] with s hLs hss hs0
    have hs0 : 0 < s := hs0
    have hκM : 0 < κ + M := by linarith
    have hD : 0 < κ - (κ + M) * s := by
      have := (lt_div_iff₀ hκM).1 hss
      linarith
    have hs1 : s < 1 := by
      have : κ / (κ + M) ≤ 1 := (div_le_one hκM).2 (by linarith)
      linarith
    have h1s : 0 < 1 - s := by linarith
    have hcs : 0 ≤ c s := div_nonneg hs0.le (by linarith)
    -- Step 1b at `τ = 1 - s`
    have h1b := LSI_step1b hω (τ := 1 - s) h1s (by linarith)
      (by have : κ * (1 - s) - M * (1 - (1 - s)) = κ - (κ + M) * s := by ring
          rw [this]; exact hD) hg hG₀ hG₁ hup
    have hcS : ∀ x, (1 - (1 - s)) * (∑ i, pderiv i g x ^ 2) /
        (2 * (κ * (1 - s) - M * (1 - (1 - s)))) = c s * S x :=
      fun x => by
        have : κ * (1 - s) - M * (1 - (1 - s)) = κ - (κ + M) * s := by ring
        rw [this, sub_sub_cancel, hcdef]
        ring
    simp only [hcS] at h1b
    -- lower bound for `a(s)`
    have iA' : Integrable (fun x => Real.exp (g x / (1 - s))) ω :=
      LSI_integrable_of_bound hω (Real.measurable_exp.comp (hgm.div_const _))
        (C := Real.exp (G₀ / (1 - s))) fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (hgle x) h1s.le)
    have ha : m + s / (1 - s) * A ≤ ∫ x, Real.exp (g x / (1 - s)) ∂ω := by
      have hpt : ∀ x, Real.exp (g x) + s / (1 - s) * (g x * Real.exp (g x)) ≤
          Real.exp (g x / (1 - s)) := fun x => by
        have e : g x / (1 - s) = g x + s / (1 - s) * g x := by field_simp; ring
        rw [e, Real.exp_add]
        have := Real.add_one_le_exp (s / (1 - s) * g x)
        nlinarith [Real.exp_pos (g x)]
      have e : ∫ x, (Real.exp (g x) + s / (1 - s) * (g x * Real.exp (g x))) ∂ω =
          m + s / (1 - s) * A := by
        rw [integral_add iE (iA.const_mul _), integral_const_mul]
      rw [← e]
      exact integral_mono (iE.add (iA.const_mul (s / (1 - s)))) iA' hpt
    -- upper bound for `b(s)`
    have iB' : Integrable (fun x => Real.exp (g x + c s * S x)) ω :=
      LSI_integrable_of_bound hω (Real.measurable_exp.comp (hgm.add (hSm.const_mul _)))
        (C := Real.exp (G₀ + c s * G₁)) fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (add_le_add (hgle x) (mul_le_mul_of_nonneg_left (hG₁ x) hcs))
    have hb : ∫ x, Real.exp (g x + c s * S x) ∂ω ≤ m + c s * Real.exp (c s * G₁) * B := by
      have hpt : ∀ x, Real.exp (g x + c s * S x) ≤
          Real.exp (g x) + c s * Real.exp (c s * G₁) * (S x * Real.exp (g x)) := fun x => by
        set t := c s * S x
        have ht0 : 0 ≤ t := mul_nonneg hcs (hS0 x)
        have htK : Real.exp t ≤ Real.exp (c s * G₁) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hG₁ x) hcs)
        have h1 : Real.exp t ≤ 1 + t * Real.exp t := by
          have := Real.add_one_le_exp (-t)
          have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos t]
        have h3 : Real.exp t ≤ 1 + t * Real.exp (c s * G₁) := by nlinarith
        rw [Real.exp_add]
        have : Real.exp (g x) * Real.exp t ≤ Real.exp (g x) * (1 + t * Real.exp (c s * G₁)) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        have e : Real.exp (g x) * (1 + t * Real.exp (c s * G₁)) =
            Real.exp (g x) + c s * Real.exp (c s * G₁) * (S x * Real.exp (g x)) := by ring
        linarith
      have e : ∫ x, (Real.exp (g x) + c s * Real.exp (c s * G₁) * (S x * Real.exp (g x))) ∂ω =
          m + c s * Real.exp (c s * G₁) * B := by
        rw [integral_add iE (iB.const_mul _), integral_const_mul]
      rw [← e]
      exact integral_mono iB' (iE.add (iB.const_mul (c s * Real.exp (c s * G₁)))) hpt
    -- combine
    have hLa : (m + s / (1 - s) * A) ^ (1 - s) ≤ (∫ x, Real.exp (g x / (1 - s)) ∂ω) ^ (1 - s) :=
      Real.rpow_le_rpow hLs.le ha h1s.le
    have hchain := hLa.trans (h1b.trans hb)
    have hpos : 0 < (m + s / (1 - s) * A) ^ (1 - s) := Real.rpow_pos_of_pos hLs _
    have := Real.log_le_log hpos hchain
    rw [Real.log_rpow hLs] at this
    exact this
  have key := LSI_deriv_le hF hG hFG0 hle
  have e1 : -Real.log m + A / m = (A - m * Real.log m) / m := by field_simp; ring
  have e2 : 1 / (2 * κ) * B / m = (1 / (2 * κ) * B) / m := rfl
  rw [e1, e2, div_le_div_iff_of_pos_right hm] at key
  -- conversion to the form `∫ klFun(e^g) ≤ klFun(m) + (2κ)⁻¹ ∫ |∇g|² e^g`
  have hpt : ∀ x, InformationTheory.klFun (Real.exp (g x)) =
      g x * Real.exp (g x) + 1 - Real.exp (g x) := fun x => by
    rw [InformationTheory.klFun_apply, Real.log_exp]; ring
  have iK : Integrable (fun x => InformationTheory.klFun (Real.exp (g x))) ω := by
    simp_rw [hpt]
    exact (iA.add (integrable_const 1)).sub iE
  have hint : ∫ x, InformationTheory.klFun (Real.exp (g x)) ∂ω = A + 1 - m := by
    simp_rw [hpt]
    rw [integral_sub (f := fun x => g x * Real.exp (g x) + 1) (iA.add (integrable_const 1)) iE,
      integral_add iA (integrable_const 1)]
    simp [hAdef, hmdef]
  have hB0 : 0 ≤ B := integral_nonneg fun x => mul_nonneg (hS0 x) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal iK (Filter.Eventually.of_forall fun x =>
      InformationTheory.klFun_nonneg (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal iB (Filter.Eventually.of_forall fun x =>
      mul_nonneg (hS0 x) (Real.exp_pos _).le),
    hint, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (InformationTheory.klFun_nonneg hm.le) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [InformationTheory.klFun_apply]
  linarith

/-- `‖v‖² ≤ ∑ v_i²` for the sup norm on `ℝ^N`. -/
private theorem LSI_norm_sq_le {N : ℕ} (v : Fin N → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have hs : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (∑ i, v i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
    _ = ∑ i, v i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- A `C²` function whose derivative has compact support satisfies the quadratic upper bound
`g(w) ≤ g(z) + Dg(z)(w - z) + (M/2)|w - z|²` (Step 1a of the proof of Theorem 17.4). -/
private theorem LSI_quad_upper {N : ℕ} {g : (Fin N → ℝ) → ℝ} (hg : ContDiff ℝ 2 g)
    (hsupp : HasCompactSupport (fderiv ℝ g)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z w, g w ≤ g z + fderiv ℝ g z (w - z) + M / 2 * ∑ i, (w i - z i) ^ 2 := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp h1 (by norm_num)
  set C : ℝ := (K : ℝ) with hCdef
  have hC0 : 0 ≤ C := K.2
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hlip : ∀ y z, ‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ C * ‖y - z‖ := fun y z =>
    hK.norm_sub_le y z
  refine ⟨2 * C, by positivity, fun z w => ?_⟩
  have hmv := (convex_segment z w).norm_image_sub_le_of_norm_fderiv_le' (f := g)
    (φ := fderiv ℝ g z) (C := C * ‖w - z‖) (fun x _ => hdiff x)
    (fun x hx => (hlip x z).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hx) hC0))
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  have h2 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hmv)
  have h3 := LSI_norm_sq_le (w - z)
  simp only [Pi.sub_apply] at h3
  have h4 : C * ‖w - z‖ * ‖w - z‖ ≤ C * ∑ i, (w i - z i) ^ 2 := by
    rw [mul_assoc, ← pow_two]
    exact mul_le_mul_of_nonneg_left h3 hC0
  linarith

/-- The profile `ψ(s) = smoothTransition((4 - s)/3)` of the cutoff: `ψ = 1` on `(-∞, 1]` and
`ψ = 0` on `[4, ∞)` (Step 2a of the proof of Theorem 17.4). -/
private noncomputable def LSI_psi (s : ℝ) : ℝ := Real.smoothTransition ((4 - s) / 3)

/-- `ψ` is `C²`. -/
private theorem LSI_psi_contDiff : ContDiff ℝ 2 LSI_psi :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

/-- `0 ≤ ψ`. -/
private theorem LSI_psi_nonneg (s : ℝ) : 0 ≤ LSI_psi s := Real.smoothTransition.nonneg _

/-- `ψ ≤ 1`. -/
private theorem LSI_psi_le_one (s : ℝ) : LSI_psi s ≤ 1 := Real.smoothTransition.le_one _

/-- `ψ = 1` on `(-∞, 1]`. -/
private theorem LSI_psi_of_le {s : ℝ} (hs : s ≤ 1) : LSI_psi s = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

/-- `ψ = 0` on `[4, ∞)`. -/
private theorem LSI_psi_of_ge {s : ℝ} (hs : 4 ≤ s) : LSI_psi s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

/-- `|ψ'| ≤ L` on `[0, ∞)`. -/
private theorem LSI_psi_deriv_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ s, 0 ≤ s → |deriv LSI_psi s| ≤ L := by
  have hc : Continuous (deriv LSI_psi) := LSI_psi_contDiff.continuous_deriv (by norm_num)
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun s hs => ?_⟩
  rcases le_or_gt s 4 with h4 | h4
  · exact (Real.norm_eq_abs _ ▸ hL s ⟨hs, h4⟩).trans (le_max_left _ _)
  · have hev : LSI_psi =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [lt_mem_nhds h4] with u hu using LSI_psi_of_ge hu.le
    rw [hev.deriv_eq, deriv_const, abs_zero]
    exact le_max_right _ _

/-- `|x|² = ∑ x_i²`. -/
private noncomputable def LSI_sq {N : ℕ} (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ 2

/-- `|x|² ≥ 0`. -/
private theorem LSI_sq_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ LSI_sq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `|x|²` is `C²`. -/
private theorem LSI_sq_contDiff {N : ℕ} : ContDiff ℝ 2 (LSI_sq (N := N)) :=
  ContDiff.sum fun i _ =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).contDiff.pow 2

/-- The derivative of `|x|²`. -/
private theorem LSI_hasFDerivAt_sq {N : ℕ} (x : Fin N → ℝ) :
    HasFDerivAt (LSI_sq (N := N))
      (∑ i ∈ Finset.univ, ((2 : ℕ) • x i ^ (2 - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i) x := by
  unfold LSI_sq
  exact HasFDerivAt.fun_sum fun i _ => (hasFDerivAt_apply (𝕜 := ℝ) i x).pow 2

/-- The cutoff `χ_t(x) = ψ(t² |x|²)`; `t → 0` plays the role of `r = 1/t → ∞` in Step 2a. -/
private noncomputable def LSI_cut {N : ℕ} (t : ℝ) (x : Fin N → ℝ) : ℝ := LSI_psi (t ^ 2 * LSI_sq x)

/-- `χ_t` is `C²`. -/
private theorem LSI_cut_contDiff {N : ℕ} (t : ℝ) : ContDiff ℝ 2 (LSI_cut (N := N) t) :=
  LSI_psi_contDiff.comp (contDiff_const.mul LSI_sq_contDiff)

/-- `∂_i χ_t(x) = ψ'(t² |x|²) · 2 t² x_i`. -/
private theorem LSI_pderiv_cut {N : ℕ} (t : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    pderiv i (LSI_cut t) x = deriv LSI_psi (t ^ 2 * LSI_sq x) * (t ^ 2 * (2 * x i)) := by
  have hψ : HasDerivAt LSI_psi (deriv LSI_psi (t ^ 2 * LSI_sq x)) (t ^ 2 * LSI_sq x) :=
    (LSI_psi_contDiff.differentiable (by norm_num) _).hasDerivAt
  have h := hψ.comp_hasFDerivAt x ((LSI_hasFDerivAt_sq x).const_mul (t ^ 2))
  unfold pderiv
  rw [show LSI_cut t = LSI_psi ∘ fun x => t ^ 2 * LSI_sq x from rfl, h.fderiv]
  simp [Pi.single_apply]

/-- `|∇χ_t|² ≤ 16 L² t²` for `|ψ'| ≤ L` on `[0, ∞)` (Step 2a, with `C_χ = 4L` and `r = 1/t`). -/
private theorem LSI_grad_cut {N : ℕ} {L : ℝ} (hL : ∀ s, 0 ≤ s → |deriv LSI_psi s| ≤ L)
    (t : ℝ) (x : Fin N → ℝ) : ∑ i, pderiv i (LSI_cut t) x ^ 2 ≤ 16 * L ^ 2 * t ^ 2 := by
  simp only [LSI_pderiv_cut]
  set s := t ^ 2 * LSI_sq x with hs
  have hs0 : 0 ≤ s := mul_nonneg (sq_nonneg _) (LSI_sq_nonneg x)
  have e : ∑ i, (deriv LSI_psi s * (t ^ 2 * (2 * x i))) ^ 2 =
      4 * t ^ 2 * deriv LSI_psi s ^ 2 * s := by
    rw [hs, LSI_sq, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  rcases le_or_gt s 4 with h4 | h4
  · have h1 : deriv LSI_psi s ^ 2 ≤ L ^ 2 := by
      have := hL s hs0
      nlinarith [abs_nonneg (deriv LSI_psi s), sq_abs (deriv LSI_psi s)]
    have h2 : deriv LSI_psi s ^ 2 * s ≤ L ^ 2 * 4 :=
      mul_le_mul h1 h4 hs0 (sq_nonneg _)
    nlinarith [sq_nonneg t]
  · have hev : LSI_psi =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [lt_mem_nhds h4] with u hu using LSI_psi_of_ge hu.le
    rw [hev.deriv_eq, deriv_const]
    nlinarith [sq_nonneg t, sq_nonneg L]

/-- `0 ≤ χ_t`. -/
private theorem LSI_cut_nonneg {N : ℕ} (t : ℝ) (x : Fin N → ℝ) : 0 ≤ LSI_cut t x :=
  LSI_psi_nonneg _

/-- `χ_t ≤ 1`. -/
private theorem LSI_cut_le_one {N : ℕ} (t : ℝ) (x : Fin N → ℝ) : LSI_cut t x ≤ 1 :=
  LSI_psi_le_one _

/-- `χ_t(x) = 1` for `t² |x|² ≤ 1`. -/
private theorem LSI_cut_of_le {N : ℕ} {t : ℝ} {x : Fin N → ℝ} (h : t ^ 2 * LSI_sq x ≤ 1) :
    LSI_cut t x = 1 := LSI_psi_of_le h

/-- `χ_t = 0` near every `x` with `t² |x|² > 4`. -/
private theorem LSI_cut_of_gt {N : ℕ} {t : ℝ} {x : Fin N → ℝ} (h : 4 < t ^ 2 * LSI_sq x) :
    LSI_cut t =ᶠ[𝓝 x] fun _ => 0 := by
  have hc : Continuous fun y : Fin N → ℝ => t ^ 2 * LSI_sq y :=
    continuous_const.mul LSI_sq_contDiff.continuous
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds h] with y hy
  exact LSI_psi_of_ge (le_of_lt hy)

/-- The set `{t² |x|² ≤ 4}` is compact for `t ≠ 0`. -/
private theorem LSI_isCompact_ball {N : ℕ} {t : ℝ} (ht : t ≠ 0) :
    IsCompact {x : Fin N → ℝ | t ^ 2 * LSI_sq x ≤ 4} := by
  have hc : Continuous fun y : Fin N → ℝ => t ^ 2 * LSI_sq y :=
    continuous_const.mul LSI_sq_contDiff.continuous
  have ht2 : 0 < t ^ 2 := by positivity
  refine (isCompact_closedBall (0 : Fin N → ℝ) (Real.sqrt (4 / t ^ 2))).of_isClosed_subset
    (isClosed_le hc continuous_const) fun x hx => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h1 : x i ^ 2 ≤ LSI_sq x := Finset.single_le_sum (f := fun j => x j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : LSI_sq x ≤ 4 / t ^ 2 := by
    rw [le_div_iff₀ ht2]; have hx' : t ^ 2 * LSI_sq x ≤ 4 := hx; linarith
  linarith


/-- A continuous function that is constant off a compact set is bounded. -/
private theorem LSI_bound_off {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) {c : ℝ} (hc : ∀ x ∉ K, f x = c) :
    ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C |c|, fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (Real.norm_eq_abs (f x) ▸ hC x hx).trans (le_max_left _ _)
  · rw [hc x hx]; exact le_max_right _ _

/-- `(u + v)² ≤ (1 + t) u² + ((1 + t)/t) v²` for `t > 0` (Step 2b, with `η = t`). -/
private theorem LSI_sq_add_le {t : ℝ} (ht : 0 < t) (u v : ℝ) :
    (u + v) ^ 2 ≤ (1 + t) * u ^ 2 + (1 + t) / t * v ^ 2 := by
  have h : t * (u + v) ^ 2 ≤ t * ((1 + t) * u ^ 2) + (1 + t) * v ^ 2 := by
    nlinarith [sq_nonneg (t * u - v)]
  rw [← sub_nonneg]
  have e : (1 + t) * u ^ 2 + (1 + t) / t * v ^ 2 - (u + v) ^ 2 =
      (t * ((1 + t) * u ^ 2) + (1 + t) * v ^ 2 - t * (u + v) ^ 2) / t := by
    field_simp
  rw [e]
  exact div_nonneg (by linarith) ht.le

/-- `∂_i(q χ_t² + t) = χ_t (χ_t ∂_i q + 2 q ∂_i χ_t)`. -/
private theorem LSI_pderiv_approx {N : ℕ} {q : (Fin N → ℝ) → ℝ} (hq : Differentiable ℝ q)
    (t : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    pderiv i (fun y => q y * LSI_cut t y ^ 2 + t) x =
      LSI_cut t x * (LSI_cut t x * pderiv i q x + 2 * q x * pderiv i (LSI_cut t) x) := by
  have hχ : DifferentiableAt ℝ (LSI_cut (N := N) t) x :=
    (LSI_cut_contDiff t).differentiable (by norm_num) x
  have h : HasFDerivAt (fun y => q y * LSI_cut t y ^ 2 + t) _ x :=
    (((hq x).hasFDerivAt).mul (hχ.hasFDerivAt.pow 2)).add_const t
  unfold pderiv
  rw [h.fderiv]
  simp
  ring

/-- Step 2b of the proof of Theorem 17.4 (pointwise form of (17.13)): with `q_t = q χ_t² + t`,
`|∇q_t|²/q_t ≤ (1 + t)|∇q|²/q + 64 L² (1 + t) t q`. -/
private theorem LSI_fisher_pt {N : ℕ} {q : (Fin N → ℝ) → ℝ} (hq : Differentiable ℝ q)
    (hpos : ∀ x, 0 < q x) {L : ℝ} (hL : ∀ s, 0 ≤ s → |deriv LSI_psi s| ≤ L) {t : ℝ}
    (ht : 0 < t) (x : Fin N → ℝ) :
    (∑ i, pderiv i (fun y => q y * LSI_cut t y ^ 2 + t) x ^ 2) / (q x * LSI_cut t x ^ 2 + t) ≤
      (1 + t) * ((∑ i, pderiv i q x ^ 2) / q x) + 64 * L ^ 2 * (1 + t) * t * q x := by
  simp only [LSI_pderiv_approx hq]
  have hb : ∑ i, pderiv i (LSI_cut t) x ^ 2 ≤ 16 * L ^ 2 * t ^ 2 := LSI_grad_cut hL t x
  set c := LSI_cut t x with hcdef
  have hc0 : 0 ≤ c := LSI_cut_nonneg t x
  have hc1 : c ≤ 1 := LSI_cut_le_one t x
  set a : Fin N → ℝ := fun i => pderiv i q x with hadef
  set b : Fin N → ℝ := fun i => pderiv i (LSI_cut t) x with hbdef
  have hqx := hpos x
  set A := ∑ i, a i ^ 2 with hAdef
  set B := ∑ i, b i ^ 2 with hBdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e1 : ∑ i, (c * (c * a i + 2 * q x * b i)) ^ 2 =
      c ^ 2 * ∑ i, (c * a i + 2 * q x * b i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, (c * a i + 2 * q x * b i) ^ 2 ≤
      (1 + t) * c ^ 2 * A + (1 + t) / t * (4 * q x ^ 2) * B := by
    calc ∑ i, (c * a i + 2 * q x * b i) ^ 2
        ≤ ∑ i, ((1 + t) * (c * a i) ^ 2 + (1 + t) / t * (2 * q x * b i) ^ 2) :=
          Finset.sum_le_sum fun i _ => LSI_sq_add_le ht _ _
      _ = (1 + t) * c ^ 2 * A + (1 + t) / t * (4 * q x ^ 2) * B := by
          rw [Finset.sum_add_distrib, hAdef, hBdef, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : (1 + t) * c ^ 2 * A ≤ (1 + t) * A := by
    have : c ^ 2 ≤ 1 := by nlinarith
    have h1t : 0 ≤ 1 + t := by linarith
    nlinarith [mul_nonneg h1t hA0]
  have h4 : (1 + t) / t * (4 * q x ^ 2) * B ≤ 64 * L ^ 2 * (1 + t) * t * q x ^ 2 := by
    calc (1 + t) / t * (4 * q x ^ 2) * B ≤ (1 + t) / t * (4 * q x ^ 2) * (16 * L ^ 2 * t ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 64 * L ^ 2 * (1 + t) * t * q x ^ 2 := by field_simp; ring
  set R := (1 + t) * (A / q x) + 64 * L ^ 2 * (1 + t) * t * q x with hRdef
  have hR0 : 0 ≤ R := by positivity
  have e2 : c ^ 2 * ((1 + t) * A + 64 * L ^ 2 * (1 + t) * t * q x ^ 2) = (q x * c ^ 2) * R := by
    rw [hRdef]; field_simp
  rw [div_le_iff₀ (by positivity), e1]
  calc c ^ 2 * ∑ i, (c * a i + 2 * q x * b i) ^ 2
      ≤ c ^ 2 * ((1 + t) * A + 64 * L ^ 2 * (1 + t) * t * q x ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg c)
    _ = (q x * c ^ 2) * R := e2
    _ ≤ R * (q x * c ^ 2 + t) := by nlinarith [mul_nonneg hR0 ht.le]


/-- Steps 2a–2b of the proof of Theorem 17.4 at the scale `t = 1/r`: (17.12) for
`q_t = q χ_t² + t`, combined with the bound (17.13) of its Fisher information. -/
private theorem LSI_step2 {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) (hκ : 0 < κ) {q : (Fin N → ℝ) → ℝ} (hq : ContDiff ℝ 2 q)
    (hpos : ∀ x, 0 < q x) (hnorm : ∫ x, q x ∂logGasMeasure β V₀ = 1) {L : ℝ}
    (hL : ∀ s, 0 ≤ s → |deriv LSI_psi s| ≤ L) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (q x * LSI_cut t x ^ 2 + t))
        ∂logGasMeasure β V₀ ≤
      ENNReal.ofReal (InformationTheory.klFun
          (∫ x, (q x * LSI_cut t x ^ 2 + t) ∂logGasMeasure β V₀)) +
        ENNReal.ofReal (1 / (2 * κ)) *
          (ENNReal.ofReal (1 + t) *
              ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i q x ^ 2) / q x) ∂logGasMeasure β V₀ +
            ENNReal.ofReal (64 * L ^ 2 * (1 + t) * t)) := by
  have hP := LSI_isProbabilityMeasure hω
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hχc : ContDiff ℝ 2 (LSI_cut (N := N) t) := LSI_cut_contDiff t
  have hQc : ContDiff ℝ 2 fun x => q x * LSI_cut t x ^ 2 + t :=
    (hq.mul (hχc.pow 2)).add contDiff_const
  have hQpos : ∀ x, 0 < q x * LSI_cut t x ^ 2 + t := fun x => by
    have := mul_nonneg (hpos x).le (sq_nonneg (LSI_cut t x)); linarith
  have hgc : ContDiff ℝ 2 fun x => Real.log (q x * LSI_cut t x ^ 2 + t) :=
    hQc.log fun x => (hQpos x).ne'
  have hK : IsCompact {x : Fin N → ℝ | t ^ 2 * LSI_sq x ≤ 4} := LSI_isCompact_ball ht.ne'
  have hoff : ∀ x ∉ {x : Fin N → ℝ | t ^ 2 * LSI_sq x ≤ 4},
      (fun x => Real.log (q x * LSI_cut t x ^ 2 + t)) =ᶠ[𝓝 x] fun _ => Real.log t :=
    fun x hx => by
      have h4 : 4 < t ^ 2 * LSI_sq x := lt_of_not_ge hx
      filter_upwards [LSI_cut_of_gt h4] with y hy
      simp [hy]
  have hDg0 : ∀ x ∉ {x : Fin N → ℝ | t ^ 2 * LSI_sq x ≤ 4},
      fderiv ℝ (fun x => Real.log (q x * LSI_cut t x ^ 2 + t)) x = 0 := fun x hx => by
    rw [(hoff x hx).fderiv_eq]
    exact fderiv_const_apply _
  have hsupp : HasCompactSupport (fderiv ℝ fun x => Real.log (q x * LSI_cut t x ^ 2 + t)) :=
    HasCompactSupport.intro hK hDg0
  obtain ⟨M, hM, hup⟩ := LSI_quad_upper hgc hsupp
  obtain ⟨G₀, hG₀⟩ := LSI_bound_off hgc.continuous hK (c := Real.log t)
    fun x hx => (hoff x hx).eq_of_nhds
  have hSc : Continuous fun x =>
      ∑ i, pderiv i (fun x => Real.log (q x * LSI_cut t x ^ 2 + t)) x ^ 2 :=
    continuous_finsetSum _ fun i _ =>
      ((hgc.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
  obtain ⟨G₁, hG₁⟩ := LSI_bound_off hSc hK (c := 0) fun x hx => by
    simp [pderiv, hDg0 x hx]
  have h1 := LSI_step1 hω hκ hM hgc.continuous hG₀ (fun x => (le_abs_self _).trans (hG₁ x)) hup
  have hexp : ∀ x, Real.exp (Real.log (q x * LSI_cut t x ^ 2 + t)) = q x * LSI_cut t x ^ 2 + t :=
    fun x => Real.exp_log (hQpos x)
  simp only [hexp] at h1
  -- the Fisher information of `q_t`
  have hpg : ∀ x, (∑ i, pderiv i (fun x => Real.log (q x * LSI_cut t x ^ 2 + t)) x ^ 2) *
      (q x * LSI_cut t x ^ 2 + t) =
        (∑ i, pderiv i (fun y => q y * LSI_cut t y ^ 2 + t) x ^ 2) /
          (q x * LSI_cut t x ^ 2 + t) := fun x => by
    have hd : ∀ i, pderiv i (fun x => Real.log (q x * LSI_cut t x ^ 2 + t)) x =
        (q x * LSI_cut t x ^ 2 + t)⁻¹ * pderiv i (fun y => q y * LSI_cut t y ^ 2 + t) x :=
      fun i => by
        unfold pderiv
        rw [fderiv.log (hQc.differentiable (by norm_num) x) (hQpos x).ne']
        rfl
    simp only [hd]
    have hQ := (hQpos x).ne'
    rw [Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  simp only [hpg] at h1
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by simp)))
  -- `∫ |∇q_t|²/q_t ≤ (1 + t) 𝓘 + 64 L² (1 + t) t`
  have hmeasA : Measurable fun x => (∑ i, pderiv i q x ^ 2) / q x :=
    (LSI_measurable_grad q).div hq.continuous.measurable
  have hq1 : ∫⁻ x, ENNReal.ofReal (q x) ∂logGasMeasure β V₀ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero (by simp [hnorm]))
      (Filter.Eventually.of_forall fun x => (hpos x).le), hnorm, ENNReal.ofReal_one]
  calc ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i (fun y => q y * LSI_cut t y ^ 2 + t) x ^ 2) /
          (q x * LSI_cut t x ^ 2 + t)) ∂logGasMeasure β V₀
      ≤ ∫⁻ x, (ENNReal.ofReal (1 + t) * ENNReal.ofReal ((∑ i, pderiv i q x ^ 2) / q x) +
          ENNReal.ofReal (64 * L ^ 2 * (1 + t) * t) * ENNReal.ofReal (q x))
          ∂logGasMeasure β V₀ := by
        refine lintegral_mono fun x => ?_
        have hA : 0 ≤ (∑ i, pderiv i q x ^ 2) / q x :=
          div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hpos x).le
        have hL0 : 0 ≤ 64 * L ^ 2 * (1 + t) * t := by positivity
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hL0,
          ← ENNReal.ofReal_add (by positivity) (mul_nonneg hL0 (hpos x).le)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := LSI_fisher_pt hqd hpos hL ht x
        linarith
    _ = ENNReal.ofReal (1 + t) *
            ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i q x ^ 2) / q x) ∂logGasMeasure β V₀ +
          ENNReal.ofReal (64 * L ^ 2 * (1 + t) * t) := by
        rw [lintegral_add_left (f := fun x => ENNReal.ofReal (1 + t) *
            ENNReal.ofReal ((∑ i, pderiv i q x ^ 2) / q x))
            ((ENNReal.measurable_ofReal.comp hmeasA).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hq1,
          mul_one]


/-- Theorem 17.4 (LSI): `Ent_ω(q) ≤ (2κ)⁻¹ ∫ |∇q|²/q dω`, with
`Ent_ω(q) = ∫ (q log q - q + 1) dω` for `∫ q dω = 1`. -/
theorem logSobolev {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ} (hω : IsConvexLogGas N β κ V₀)
    (hκ : 0 < κ) {q : (Fin N → ℝ) → ℝ} (hq : ContDiff ℝ 2 q) (hpos : ∀ x, 0 < q x)
    (hnorm : ∫ x, q x ∂logGasMeasure β V₀ = 1) :
    ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (q x)) ∂logGasMeasure β V₀ ≤
      ENNReal.ofReal (1 / (2 * κ)) *
        ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i q x ^ 2) / q x) ∂logGasMeasure β V₀ := by
  have hP := LSI_isProbabilityMeasure hω
  obtain ⟨L, -, hL⟩ := LSI_psi_deriv_bound
  have hqi : Integrable q (logGasMeasure β V₀) :=
    Integrable.of_integral_ne_zero (by simp [hnorm])
  set I := ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i q x ^ 2) / q x) ∂logGasMeasure β V₀ with hI
  -- the scales `t_n = 1/(n + 1)`
  set tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with htn
  have htn0 : ∀ n, 0 < tn n := fun n => by simp only [htn]; positivity
  have htn1 : ∀ n, tn n ≤ 1 := fun n => by
    simp only [htn]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have htlim : Tendsto tn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set qn : ℕ → (Fin N → ℝ) → ℝ := fun n x => q x * LSI_cut (tn n) x ^ 2 + tn n with hqn
  have hqnc : ∀ n, Continuous (qn n) := fun n =>
    (hq.continuous.mul ((LSI_cut_contDiff (tn n)).continuous.pow 2)).add continuous_const
  -- Step 2d: pointwise convergence `q_n → q`
  have hconv : ∀ x, Tendsto (fun n => qn n x) atTop (𝓝 (q x)) := by
    intro x
    have hev : ∀ᶠ n in atTop, q x + tn n = qn n x := by
      filter_upwards [eventually_ge_atTop ⌈LSI_sq x⌉₊] with n hn
      have h1 : LSI_sq x ≤ (n : ℝ) + 1 := by
        have := Nat.le_ceil (LSI_sq x)
        have : (⌈LSI_sq x⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have h2 : tn n ^ 2 * LSI_sq x ≤ 1 := by
        simp only [htn]
        rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simp only [hqn, LSI_cut_of_le h2, one_pow, mul_one]
    have : Tendsto (fun n => q x + tn n) atTop (𝓝 (q x)) := by
      simpa using tendsto_const_nhds.add htlim
    exact this.congr' hev
  -- the masses `m_n = ∫ q_n dω → 1`
  have hmass : Tendsto (fun n => ∫ x, qn n x ∂logGasMeasure β V₀) atTop (𝓝 1) := by
    rw [← hnorm]
    refine tendsto_integral_of_dominated_convergence (fun x => q x + 1)
      (fun n => (hqnc n).aestronglyMeasurable) (hqi.add (integrable_const 1))
      (fun n => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall hconv)
    have hc0 := LSI_cut_nonneg (tn n) x
    have hc1 := LSI_cut_le_one (tn n) x
    have hqx := hpos x
    have h0 : 0 ≤ qn n x := by
      simp only [hqn]; have := htn0 n; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [hqn]
    have : LSI_cut (tn n) x ^ 2 ≤ 1 := by nlinarith
    nlinarith [htn1 n]
  -- the bounds of Steps 2a–2c
  set b : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (InformationTheory.klFun (∫ x, qn n x ∂logGasMeasure β V₀)) +
      ENNReal.ofReal (1 / (2 * κ)) *
        (ENNReal.ofReal (1 + tn n) * I + ENNReal.ofReal (64 * L ^ 2 * (1 + tn n) * tn n))
    with hb
  have hstep : ∀ n, ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (qn n x))
      ∂logGasMeasure β V₀ ≤ b n := fun n =>
    LSI_step2 hω hκ hq hpos hnorm hL (htn0 n)
  have hblim : Tendsto b atTop (𝓝 (ENNReal.ofReal (1 / (2 * κ)) * I)) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal
        (InformationTheory.klFun (∫ x, qn n x ∂logGasMeasure β V₀))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal
        ((InformationTheory.continuous_klFun.tendsto 1).comp hmass)
      simpa [InformationTheory.klFun_one] using this
    have h2 : Tendsto (fun n => ENNReal.ofReal (1 + tn n)) atTop (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (tendsto_const_nhds.add htlim (a := (1 : ℝ)))
      simpa using this
    have h3 : Tendsto (fun n => ENNReal.ofReal (64 * L ^ 2 * (1 + tn n) * tn n)) atTop (𝓝 0) := by
      have h := ((tendsto_const_nhds (x := 64 * L ^ 2)).mul
        (tendsto_const_nhds.add htlim (a := (1 : ℝ)))).mul htlim
      have := ENNReal.tendsto_ofReal h
      simpa using this
    have h4 := (ENNReal.Tendsto.mul_const h2 (b := I) (Or.inl one_ne_zero)).add h3
    have h5 := ENNReal.Tendsto.const_mul h4 (a := ENNReal.ofReal (1 / (2 * κ)))
      (Or.inr ENNReal.ofReal_ne_top)
    have h6 := h1.add h5
    rw [zero_add, one_mul, add_zero] at h6
    exact h6
  -- Fatou's lemma
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal (InformationTheory.klFun (qn n x)) :=
    fun n => (ENNReal.continuous_ofReal.comp
      (InformationTheory.continuous_klFun.comp (hqnc n))).measurable
  have hlim : ∀ x, liminf (fun n => ENNReal.ofReal (InformationTheory.klFun (qn n x))) atTop =
      ENNReal.ofReal (InformationTheory.klFun (q x)) := fun x =>
    ((ENNReal.continuous_ofReal.tendsto _).comp
      ((InformationTheory.continuous_klFun.tendsto _).comp (hconv x))).liminf_eq
  calc ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (q x)) ∂logGasMeasure β V₀
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal (InformationTheory.klFun (qn n x))) atTop
          ∂logGasMeasure β V₀ := lintegral_congr fun x => (hlim x).symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (qn n x))
          ∂logGasMeasure β V₀) atTop := lintegral_liminf_le hmeas
    _ ≤ liminf b atTop := liminf_le_liminf (Filter.Eventually.of_forall hstep)
    _ = ENNReal.ofReal (1 / (2 * κ)) * I := hblim.liminf_eq

end Rigidity
