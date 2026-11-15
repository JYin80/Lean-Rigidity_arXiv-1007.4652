import Rigidity.Ensemble.Basic

/-!
# Moments of the entries and transformations of ensembles

Numbers refer to NP v1.1; the original is cited as [EYY, ...].

This file proves the parts of Lemma 2.5 on moments and on transformations of an ensemble:
all moments of an entry are finite under the subexponential decay (2.17), an entry of vanishing
variance vanishes almost surely, real scaling acts on the product law and on the variances, the
Ornstein-Uhlenbeck flow (2.29) acts on the variances by `e^{-t} σ² + (1 - e^{-t}) σ_g²`, and the
reflected ensemble `(-1)_* ν` and real scalar multiples keep the conditions of Lemma 2.5 (iv), (v).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- Under the subexponential decay (2.17), a vanishing variance forces the entry to vanish
almost surely. -/
private lemma law_ne_zero_of_subexp {ϑ : ℝ} (h : M.SubexpDecay ϑ) (p : Pair N)
    (hp : M.varPair p = 0) : M.law p {y | y ≠ 0} = 0 := by
  have key : ∀ x : ℝ, 1 ≤ x →
      M.law p {y | y ≠ 0} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ))) := by
    intro x hx
    have := h p x hx
    simpa [hp] using this
  rcases le_or_gt ϑ 0 with hϑ | hϑ
  · have h1 := key 1 le_rfl
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hϑ)
      (Real.exp_pos _).le)] at h1
    exact le_antisymm h1 zero_le
  · have ht : Tendsto (fun x : ℝ => ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))) atTop
        (𝓝 0) := by
      have h0 : Tendsto (fun x : ℝ => ϑ⁻¹ * Real.exp (-(x ^ ϑ))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_rpow_atTop hϑ)).const_mul ϑ⁻¹
        simpa using this
      simpa using (ENNReal.tendsto_ofReal h0)
    have := ge_of_tendsto ht (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx using key x hx)
    exact le_antisymm this zero_le

theorem Assumptions.integrable_norm_pow {ϑ δm δp C₀ : ℝ} (h : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) (p : Pair N) (k : ℕ) : Integrable (fun y => ‖y‖ ^ k) (M.law p) := by
  have hmeas : AEStronglyMeasurable (fun y : 𝕜 => ‖y‖ ^ k) (M.law p) := by fun_prop
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hv0 : 0 ≤ M.varPair p := integral_nonneg fun y => by positivity
  rcases hv0.eq_or_lt with hv | hv
  · have h0 := law_ne_zero_of_subexp M h.subexp p hv.symm
    refine (integrable_zero _ _ _).congr ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with y hy
    have : y = 0 := by simpa using hy
    simp [this, hk.ne']
  set σ := Real.sqrt (M.varPair p) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  set b : ℝ := (σ ^ ϑ)⁻¹ with hbdef
  have hb : 0 < b := inv_pos.mpr (Real.rpow_pos_of_pos hσ _)
  set C : ℝ := max ϑ⁻¹ (Real.exp 1) with hCdef
  have hC0 : 0 ≤ C := (Real.exp_pos 1).le.trans (le_max_right _ _)
  -- tail bound for all `t > 0`
  have tail : ∀ t : ℝ, 0 < t →
      M.law p {y | t < ‖y‖} ≤ ENNReal.ofReal (C * Real.exp (-b * t ^ ϑ)) := by
    intro t ht
    have hbt : b * t ^ ϑ = (t / σ) ^ ϑ := by
      rw [Real.div_rpow ht.le hσ.le, hbdef]
      ring
    rw [neg_mul, hbt]
    rcases le_or_gt 1 (t / σ) with hx | hx
    · have := h.subexp p (t / σ) hx
      rw [← hσdef, div_mul_cancel₀ _ hσ.ne'] at this
      refine this.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (t / σ) ^ ϑ ≤ 1 :=
        Real.rpow_le_one (div_pos ht hσ).le hx.le hϑ.le
      calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
        _ ≤ C * Real.exp (-(t / σ) ^ ϑ) :=
          mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_pos _).le hC0
  refine ⟨hmeas, ?_⟩
  have hnn : 0 ≤ᵐ[M.law p] fun y : 𝕜 => ‖y‖ ^ k :=
    Filter.Eventually.of_forall fun y => by positivity
  rw [hasFiniteIntegral_iff_ofReal hnn]
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hint : IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - 1) * Real.exp (-b * t ^ ϑ))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hϑ hb
  have hlt := (hint.const_mul C).lintegral_lt_top
  have hlay := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := M.law p)
    (f := fun y : 𝕜 => ‖y‖) (Filter.Eventually.of_forall fun y => norm_nonneg y)
    measurable_norm.aemeasurable hk'
  have hconv : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ k) ∂M.law p =
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ (k : ℝ)) ∂M.law p := by
    simp only [Real.rpow_natCast]
  rw [hconv, hlay]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hlt)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  calc M.law p {a | t < ‖a‖} * ENNReal.ofReal (t ^ ((k : ℝ) - 1))
      ≤ ENNReal.ofReal (C * Real.exp (-b * t ^ ϑ)) * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) :=
        mul_le_mul' (tail t ht') le_rfl
    _ = ENNReal.ofReal (C * Real.exp (-b * t ^ ϑ) * t ^ ((k : ℝ) - 1)) :=
        (ENNReal.ofReal_mul (mul_nonneg hC0 (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (C * (t ^ ((k : ℝ) - 1) * Real.exp (-b * t ^ ϑ))) := by
        congr 1; ring

/-- A vanishing variance forces the entry to vanish almost surely. -/
theorem Assumptions.law_ne_zero {ϑ δm δp C₀ : ℝ} (h : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) (hp : M.varPair p = 0) : M.law p {y | y ≠ 0} = 0 :=
  law_ne_zero_of_subexp M h.subexp p hp

theorem prodLaw_smul (c : ℝ) :
    (M.smul c).prodLaw = M.prodLaw.map fun x => (c : 𝕜) • x := by
  have hm : Measurable fun y : 𝕜 => (c : 𝕜) * y := measurable_const.mul measurable_id
  have h := Measure.pi_map_pi (μ := M.law) (f := fun _ : Pair N => fun y : 𝕜 => (c : 𝕜) * y)
    fun _ => hm.aemeasurable
  unfold prodLaw
  change _ = Measure.map (fun x i => (c : 𝕜) * x i) (Measure.pi M.law)
  rw [h]
  rfl

theorem varPair_smul (c : ℝ) (p : Pair N) : (M.smul c).varPair p = c ^ 2 * M.varPair p := by
  have hm : Measurable fun y : 𝕜 => (c : 𝕜) * y := measurable_const.mul measurable_id
  unfold varPair
  change ∫ y, ‖y‖ ^ 2 ∂(M.law p).map (fun y : 𝕜 => (c : 𝕜) * y) = _
  rw [integral_map hm.aemeasurable (by fun_prop), ← integral_const_mul]
  congr 1
  ext y
  rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- Multiplication by a real scalar is measurable. -/
private lemma measurable_ofReal_mul (c : ℝ) : Measurable fun y : 𝕜 => (c : 𝕜) * y :=
  measurable_const.mul measurable_id

/-- Real scaling preserves mean zero (2.1). -/
private lemma smul_meanZero (c : ℝ) (hZ : M.MeanZero) : (M.smul c).MeanZero := by
  intro p
  change ∫ y, y ∂(M.law p).map (fun y : 𝕜 => (c : 𝕜) * y) = 0
  rw [integral_map (measurable_ofReal_mul c).aemeasurable (by fun_prop),
    integral_const_mul, hZ p, mul_zero]

/-- Real scaling preserves reality of the diagonal entries. -/
private lemma smul_diagReal (c : ℝ) (hR : M.DiagReal) : (M.smul c).DiagReal := by
  intro i
  change ∀ᵐ y ∂(M.law (Pair.mk' i i)).map (fun y : 𝕜 => (c : 𝕜) * y), RCLike.im y = 0
  have hm : MeasurableSet {y : 𝕜 | RCLike.im y = 0} :=
    measurableSet_eq_fun RCLike.continuous_im.measurable measurable_const
  rw [ae_map_iff (measurable_ofReal_mul c).aemeasurable hm]
  filter_upwards [hR i] with y hy
  simp [hy]

/-- Real scaling preserves the subexponential decay (2.17) with the same `ϑ`. -/
private lemma smul_subexp {ϑ : ℝ} (c : ℝ) (hD : M.SubexpDecay ϑ) :
    (M.smul c).SubexpDecay ϑ := by
  intro p x hx
  change (M.law p).map (fun y : 𝕜 => (c : 𝕜) * y)
    {y | x * Real.sqrt ((M.smul c).varPair p) < ‖y‖} ≤ _
  have hm : MeasurableSet {y : 𝕜 | x * Real.sqrt ((M.smul c).varPair p) < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  rw [Measure.map_apply (measurable_ofReal_mul c) hm]
  refine le_trans (measure_mono ?_) (hD p x hx)
  intro y hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy ⊢
  rw [varPair_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, norm_mul,
    RCLike.norm_ofReal] at hy
  exact lt_of_mul_lt_mul_left (by linarith) (abs_nonneg c)

/-- The variances of a scaled ensemble. -/
private lemma var_smul (c : ℝ) (i j : Fin N) : (M.smul c).var i j = c ^ 2 * M.var i j :=
  varPair_smul M c _

/-- The second moment of a real-scaled entry is finite if that of the entry is. -/
private lemma integrable_sq_smul (c : ℝ) (p : Pair N)
    (hi : Integrable (fun y : 𝕜 => ‖y‖ ^ 2) (M.law p)) :
    Integrable (fun y : 𝕜 => ‖y‖ ^ 2) ((M.smul c).law p) := by
  change Integrable (fun y : 𝕜 => ‖y‖ ^ 2) ((M.law p).map fun y : 𝕜 => (c : 𝕜) * y)
  rw [integrable_map_measure (by fun_prop) (measurable_ofReal_mul c).aemeasurable]
  refine (hi.const_mul (c ^ 2)).congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp_apply, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]

/-- A finite second moment on a probability space gives a finite first moment. -/
private lemma integrable_of_integrable_sq {μ : Measure 𝕜} [IsProbabilityMeasure μ]
    (hi : Integrable (fun y : 𝕜 => ‖y‖ ^ 2) μ) : Integrable (fun y : 𝕜 => y) μ := by
  refine (hi.add (integrable_const (1 : ℝ))).mono' aestronglyMeasurable_id
    (ae_of_all _ fun y => ?_)
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 1)]

theorem varPair_ouFlow (g : Ensemble 𝕜 N) (t : ℝ) (ht : 0 ≤ t) (hM : M.MeanZero)
    (hg : g.MeanZero) (p : Pair N) (hMi : Integrable (fun y => ‖y‖ ^ 2) (M.law p))
    (hgi : Integrable (fun y => ‖y‖ ^ 2) (g.law p)) :
    (M.ouFlow g t).varPair p =
      Real.exp (-t) * M.varPair p + (1 - Real.exp (-t)) * g.varPair p := by
  have _ := hM
  set a : ℝ := Real.exp (-t / 2) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-t)) with hb
  have ha2 : a ^ 2 = Real.exp (-t) := by
    rw [ha, sq, ← Real.exp_add]
    ring_nf
  have hb2 : b ^ 2 = 1 - Real.exp (-t) :=
    Real.sq_sqrt (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
  have hμi := integrable_sq_smul M a p hMi
  have hνi := integrable_sq_smul g b p hgi
  have hμ1 := integrable_of_integrable_sq hμi
  have hν1 := integrable_of_integrable_sq hνi
  have hν0 : ∫ y, y ∂(g.smul b).law p = 0 := smul_meanZero g b hg p
  set μ : Measure 𝕜 := (M.smul a).law p with hμdef
  set ν : Measure 𝕜 := (g.smul b).law p with hνdef
  have hadd : Measurable fun z : 𝕜 × 𝕜 => z.1 + z.2 := measurable_fst.add measurable_snd
  have hcross : ∫ z, RCLike.re (inner 𝕜 z.1 z.2) ∂μ.prod ν = 0 := by
    have hconj : Integrable (fun x : 𝕜 => starRingEnd 𝕜 x) (μ) :=
      hμ1.norm.mono' RCLike.continuous_conj.aestronglyMeasurable (ae_of_all _ fun x => by simp)
    have hI : Integrable (fun z : 𝕜 × 𝕜 => starRingEnd 𝕜 z.1 * z.2)
        (μ.prod ν) := hconj.mul_prod hν1
    have h1 : ∫ z, RCLike.re (inner 𝕜 z.1 z.2) ∂μ.prod ν =
        RCLike.re (∫ z, starRingEnd 𝕜 z.1 * z.2 ∂μ.prod ν) := by
      rw [← integral_re hI]
      simp only [RCLike.inner_apply']
    rw [h1, integral_prod_mul (fun x : 𝕜 => starRingEnd 𝕜 x) (fun y : 𝕜 => y), hν0]
    simp
  have hsum : ∫ z, ‖z.1 + z.2‖ ^ 2 ∂μ.prod ν =
      (M.smul a).varPair p + (g.smul b).varPair p := by
    have e : ∀ z : 𝕜 × 𝕜, ‖z.1 + z.2‖ ^ 2 =
        ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 + 2 * RCLike.re (inner 𝕜 z.1 z.2) := fun z => by
      rw [norm_add_sq (𝕜 := 𝕜)]; ring
    have hI1 : Integrable (fun z : 𝕜 × 𝕜 => ‖z.1‖ ^ 2)
        (μ.prod ν) := hμi.comp_fst _
    have hI2 : Integrable (fun z : 𝕜 × 𝕜 => ‖z.2‖ ^ 2)
        (μ.prod ν) := hνi.comp_snd _
    have hI3 : Integrable (fun z : 𝕜 × 𝕜 => 2 * RCLike.re (inner 𝕜 z.1 z.2))
        (μ.prod ν) := by
      have hconj : Integrable (fun x : 𝕜 => starRingEnd 𝕜 x) (μ) :=
        hμ1.norm.mono' RCLike.continuous_conj.aestronglyMeasurable (ae_of_all _ fun x => by simp)
      have hI : Integrable (fun z : 𝕜 × 𝕜 => starRingEnd 𝕜 z.1 * z.2)
          (μ.prod ν) := hconj.mul_prod hν1
      refine (hI.re.const_mul 2).congr (ae_of_all _ fun z => ?_)
      simp only [RCLike.inner_apply']
    simp_rw [e]
    have hI12 : Integrable (fun z : 𝕜 × 𝕜 => ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
        (μ.prod ν) := hI1.add hI2
    rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, hcross]
    have h1 := integral_prod_mul (μ := μ) (ν := ν)
      (fun x : 𝕜 => ‖x‖ ^ 2) (fun _ => (1 : ℝ))
    have h2 := integral_prod_mul (μ := μ) (ν := ν)
      (fun _ => (1 : ℝ)) (fun x : 𝕜 => ‖x‖ ^ 2)
    simp only [mul_one, one_mul, integral_const, probReal_univ, smul_eq_mul] at h1 h2
    rw [h1, h2]
    unfold varPair
    ring
  change ∫ z, ‖z‖ ^ 2 ∂(μ ∗ ν) = _
  unfold Measure.conv
  rw [integral_map hadd.aemeasurable (by fun_prop)]
  rw [hsum, varPair_smul, varPair_smul, ha2, hb2]

/-- Lemma 2.5 (iv): the reflected ensemble `ν⁻ = (−1)_* ν` is in the same class. -/
theorem Assumptions.neg {ϑ δm δp C₀ : ℝ} (h : M.Assumptions ϑ δm δp C₀) :
    (M.smul (-1)).Assumptions ϑ δm δp C₀ := by
  have hv : (M.smul (-1)).var = M.var := by
    ext i j
    rw [var_smul]
    ring
  have hB : (M.smul (-1)).varMatrix = M.varMatrix := by
    unfold varMatrix
    rw [hv]
  refine ⟨smul_meanZero M _ h.meanZero, smul_diagReal M _ h.diagReal, ?_, ?_, ?_,
    smul_subexp M _ h.subexp⟩
  · intro j
    have := h.sumA j
    rwa [hv]
  · unfold AssumptionB
    rw [hB]
    exact h.specB
  · intro i j
    rw [hv]
    exact h.boundC i j

/-- Lemma 2.5 (v): (R), (Z), (D) are preserved under real scaling, with the same `ϑ`. -/
theorem smul_conditions {ϑ : ℝ} (c : ℝ) (hZ : M.MeanZero) (hR : M.DiagReal)
    (hD : M.SubexpDecay ϑ) :
    (M.smul c).MeanZero ∧ (M.smul c).DiagReal ∧ (M.smul c).SubexpDecay ϑ :=
  ⟨smul_meanZero M c hZ, smul_diagReal M c hR, smul_subexp M c hD⟩

end Ensemble

end Rigidity
