import Rigidity.Ensemble.Basic
import Rigidity.Flow.Ensembles
import Rigidity.Flow.GaussEnsemble
import Rigidity.Flow.GaussKL
import Rigidity.Flow.Herm
import Rigidity.Flow.JointDensity
import Rigidity.LogGas.Defs
import Rigidity.Semicircle.Density

/-!
# The local relaxation measure and a priori entropy bounds

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `R > 0` let `W_R(x) = |x - γ|²/(2R²)` (`relaxW`) and `ω_R = e^{-N W_R} μ / ∫ e^{-N W_R} dμ`
(`relaxMeasure`, Definition 16.5), with `μ = gbeLaw` the law of the eigenvalues of the Gaussian
ensemble.  The file proves:
* Definition 17.2, Comment (2): `ω_R` is a convex log-gas with `κ = N(β/2 + R⁻²)`
  (`isConvexLogGas_relaxV₀`), and it is the log-gas of `𝓥₀ = βN|x|²/4 + N|x - γ|²/(2R²)`
  (`relaxMeasure_eq_logGasMeasure`, using Theorem 16.3);
* Lemma 18.1: `S(ν_s|μ) ≤ S(law H_s|𝐆) ≤ (d/2) log(1/(1-e^{-s})) + (βN²/4) e^{-s}`
  (`klDiv_eigLaw_le`), and `S(ν_s|μ) ≤ N³` for `s ≥ N⁻²` (`klDiv_eigLaw_le_cube`);
* Lemma 18.2: `S(ν'|ω) ≤ S(ν'|μ) + (N/(2R²)) ∫ |x - γ|² dν'` (`klDiv_relaxMeasure_le`).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `W_R(x) = |x - γ|²/(2R²)` (Definition 16.5). -/
noncomputable def relaxW (N : ℕ) (R : ℝ) (x : Fin N → ℝ) : ℝ :=
  (2 * R ^ 2)⁻¹ * ∑ k, (x k - gamma N k) ^ 2

/-- Definition 16.5: the local relaxation measure `ω_R = e^{-NW} μ / ∫ e^{-NW} dμ`. -/
noncomputable def relaxMeasure (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (R : ℝ) : Measure (Fin N → ℝ) :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * relaxW N R x))) ∂gbeLaw 𝕜 N)⁻¹ •
    (gbeLaw 𝕜 N).withDensity fun x => ENNReal.ofReal (Real.exp (-(N * relaxW N R x)))

/-- `𝓥₀` of the local relaxation measure: `βN|x|²/4 + N|x - γ|²/(2R²)` (Definition 16.5). -/
noncomputable def relaxV₀ (β : ℝ) (N : ℕ) (R : ℝ) (x : Fin N → ℝ) : ℝ :=
  β * N / 4 * ∑ k, x k ^ 2 + N / (2 * R ^ 2) * ∑ k, (x k - gamma N k) ^ 2

/-- The identity `τ|x - c|² + (1 - τ)|y - c|² - |τx + (1 - τ)y - c|² = τ(1 - τ)|x - y|²`. -/
private lemma entropy_sq_comb {N : ℕ} (c x y : Fin N → ℝ) (τ : ℝ) :
    τ * ∑ i, (x i - c i) ^ 2 + (1 - τ) * ∑ i, (y i - c i) ^ 2 -
        ∑ i, ((τ • x + (1 - τ) • y) i - c i) ^ 2 = τ * (1 - τ) * ∑ i, (x i - y i) ^ 2 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The convexity defect of `𝓥₀` is exactly `(κ/2) τ (1 - τ) |x - y|²`. -/
private lemma entropy_relaxV₀_comb (β : ℝ) (N : ℕ) (R : ℝ) (x y : Fin N → ℝ) (τ : ℝ) :
    τ * relaxV₀ β N R x + (1 - τ) * relaxV₀ β N R y - relaxV₀ β N R (τ • x + (1 - τ) • y) =
      N * (β / 2 + 1 / R ^ 2) / 2 * τ * (1 - τ) * ∑ i, (x i - y i) ^ 2 := by
  have h0 := entropy_sq_comb (0 : Fin N → ℝ) x y τ
  have h1 := entropy_sq_comb (gamma N) x y τ
  simp only [Pi.zero_apply, sub_zero] at h0
  unfold relaxV₀
  linear_combination (β * N / 4) * h0 + (N / (2 * R ^ 2)) * h1

/-- Definition 17.2, Comment (2): `ω_R` is a convex log-gas with `κ = N(β/2 + R⁻²)`. -/
theorem isConvexLogGas_relaxV₀ {β : ℝ} (hβ : 1 ≤ β) (N : ℕ) {R : ℝ} (hR : 0 < R) :
    IsConvexLogGas N β (N * (β / 2 + 1 / R ^ 2)) (relaxV₀ β N R) := by
  have hβ0 : 0 ≤ β := by linarith
  have hκ : 0 ≤ (N : ℝ) * (β / 2 + 1 / R ^ 2) := by positivity
  have hcont : Continuous (relaxV₀ β N R) := by
    unfold relaxV₀
    fun_prop
  have hconv : ∀ x y : Fin N → ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      (N * (β / 2 + 1 / R ^ 2)) / 2 * τ * (1 - τ) * ∑ i, (x i - y i) ^ 2 ≤
        τ * relaxV₀ β N R x + (1 - τ) * relaxV₀ β N R y -
          relaxV₀ β N R (τ • x + (1 - τ) • y) := fun x y τ _ =>
    (entropy_relaxV₀_comb β N R x y τ).ge
  refine ⟨hβ, hκ, hcont, hconv, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine lintegral_logGas_lt_top (κ := 1) hβ0 one_pos hcont fun x y τ _ => ?_
    simp [relaxV₀]
  · exact lintegral_logGas_lt_top hβ0 (by positivity) hcont hconv

/-- `μ = λ_* 𝐆` is a probability measure. -/
private instance entropy_isProbabilityMeasure_gbeLaw {N : ℕ} :
    IsProbabilityMeasure (gbeLaw 𝕜 N) := by
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  exact (Measure.isProbabilityMeasure_map_iff (continuous_eigVec N).measurable.aemeasurable).2
    inferInstance

private lemma entropy_continuous_relaxW (N : ℕ) (R : ℝ) : Continuous (relaxW N R) := by
  unfold relaxW
  fun_prop

private lemma entropy_measurable_dens (N : ℕ) (R : ℝ) :
    Measurable fun x : Fin N → ℝ => ENNReal.ofReal (Real.exp (-(N * relaxW N R x))) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (entropy_continuous_relaxW N R)).neg).measurable

private lemma entropy_measurable_gbeWeight (β : ℝ) (N : ℕ) :
    Measurable fun x : Fin N → ℝ => ENNReal.ofReal (gbeWeight β N x) := by
  refine ENNReal.measurable_ofReal.comp ?_
  unfold gbeWeight vandermonde
  fun_prop

/-- On the chamber, `w e^{-N W} = e^{-𝓥}` with `𝓥 = 𝓥₀ - β ∑_{i<j} log (x_j - x_i)`. -/
private lemma entropy_weight_mul_eq {N : ℕ} (β : ℝ) (R : ℝ) {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    gbeWeight β N x * Real.exp (-(N * relaxW N R x)) =
      Real.exp (-logGasH β (relaxV₀ β N R) x) := by
  have hpos : ∀ p : {q : Fin N × Fin N // q.1 < q.2}, x p.1.2 - x p.1.1 ≠ 0 :=
    fun p => (sub_pos.2 (hx p.2)).ne'
  have hv : 0 < vandermonde x := Finset.prod_pos fun p _ => sub_pos.2 (hx p.2)
  have hlog : Real.log (vandermonde x) =
      ∑ p : {q : Fin N × Fin N // q.1 < q.2}, Real.log (x p.1.2 - x p.1.1) :=
    Real.log_prod (fun p _ => hpos p)
  unfold gbeWeight
  rw [Real.rpow_def_of_pos hv, hlog, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold logGasH relaxV₀ relaxW
  ring

/-- Definition 16.5, second form of (16.5) (uses Theorem 16.3). -/
theorem relaxMeasure_eq_logGasMeasure (N : ℕ) {R : ℝ} (hR : 0 < R) :
    relaxMeasure 𝕜 N R = logGasMeasure (betaF 𝕜) (relaxV₀ (betaF 𝕜) N R) := by
  have _ := hR
  set β : ℝ := betaF 𝕜 with hβ
  set Zμ : ℝ≥0∞ := ∫⁻ x in chamber N, ENNReal.ofReal (gbeWeight β N x) with hZμ
  set ν : Measure (Fin N → ℝ) :=
    (volume.restrict (chamber N)).withDensity fun x => ENNReal.ofReal (gbeWeight β N x) with hν
  set g : (Fin N → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(N * relaxW N R x))) with hg
  set w : (Fin N → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (gbeWeight β N x) with hw
  set h : (Fin N → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (Real.exp (-logGasH β (relaxV₀ β N R) x)) with hh
  set Zω : ℝ≥0∞ := ∫⁻ x in chamber N, h x with hZω
  have hgm : Measurable g := entropy_measurable_dens N R
  have hwm : Measurable w := entropy_measurable_gbeWeight β N
  have hcm : MeasurableSet (chamber N) := (isOpen_chamber N).measurableSet
  have hμν : gbeLaw 𝕜 N = Zμ⁻¹ • ν := gbeLaw_eq_muStar N
  have hνuniv : ν Set.univ = Zμ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 : Zμ⁻¹ * Zμ = 1 := by
    have := measure_univ (μ := gbeLaw 𝕜 N)
    rwa [hμν, Measure.smul_apply, hνuniv, smul_eq_mul] at this
  have hZ0 : Zμ ≠ 0 := by
    rintro h0
    rw [h0] at h1
    simp at h1
  have hZtop : Zμ ≠ ⊤ := by
    rintro h0
    rw [h0] at h1
    simp at h1
  have hpt : ∀ x ∈ chamber N, (w * g) x = h x := by
    intro x hx
    simp only [Pi.mul_apply, hw, hg, hh]
    rw [← ENNReal.ofReal_mul (by
      unfold gbeWeight
      exact mul_nonneg (Real.rpow_nonneg (Finset.prod_nonneg fun p _ =>
        (sub_pos.2 (hx p.2)).le) _) (Real.exp_pos _).le), entropy_weight_mul_eq β R hx]
  have hdens : (ν.withDensity g) = (volume.restrict (chamber N)).withDensity h := by
    rw [hν, ← withDensity_mul _ hwm hgm]
    exact withDensity_congr_ae ((ae_restrict_iff' hcm).2 (ae_of_all _ hpt))
  have hZW : ∫⁻ x, g x ∂gbeLaw 𝕜 N = Zμ⁻¹ * Zω := by
    rw [hμν, lintegral_smul_measure, smul_eq_mul, hν,
      lintegral_withDensity_eq_lintegral_mul _ hwm hgm, hZω]
    congr 1
    exact setLIntegral_congr_fun hcm hpt
  have hdens' : (gbeLaw 𝕜 N).withDensity g =
      Zμ⁻¹ • (volume.restrict (chamber N)).withDensity h := by
    rw [hμν, withDensity_smul_measure, hdens]
  have hinv : (Zμ⁻¹ * Zω)⁻¹ * Zμ⁻¹ = Zω⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hZtop)) (Or.inl (ENNReal.inv_ne_top.2 hZ0)),
      inv_inv, mul_assoc, mul_comm Zω⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, one_mul]
  unfold relaxMeasure logGasMeasure
  rw [hdens', hZW, smul_smul, hinv]

/-- `H_0` has a probability law on `𝓗`. -/
private instance entropy_isProbabilityMeasure_hermLaw {N : ℕ} (M : Ensemble 𝕜 N) :
    IsProbabilityMeasure M.hermLaw := by
  unfold Ensemble.hermLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (Herm.measurable_ofPair (𝕜 := 𝕜) N).aemeasurable).2 inferInstance

/-- The law of `H_s` on `𝓗` is a probability measure. -/
private instance entropy_isProbabilityMeasure_flowLaw {N : ℕ} (M : Ensemble 𝕜 N) (s : ℝ) :
    IsProbabilityMeasure (M.flowLaw s) := by
  unfold Ensemble.flowLaw ouLaw
  have : IsProbabilityMeasure (gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)) := gaussE_isProbabilityMeasure _
  infer_instance

/-- `𝐆` is a probability measure. -/
private instance entropy_isProbabilityMeasure_gaussH {N : ℕ} : IsProbabilityMeasure (gaussH 𝕜 N) :=
  gaussE_isProbabilityMeasure _

private lemma entropy_one_le_betaF : 1 ≤ betaF 𝕜 := by
  unfold betaF
  exact_mod_cast Module.finrank_pos

private lemma entropy_betaF_le_two : betaF 𝕜 ≤ 2 := by
  unfold betaF
  exact_mod_cast RCLike.finrank_le_two 𝕜

/-- Lemma 18.1: `S(ν_s|μ) ≤ S(law H_s|𝐆) ≤ (d/2) log(1/(1-e^{-s})) + (βN²/4) e^{-s}`. -/
theorem klDiv_eigLaw_le {N : ℕ} {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) {M : Ensemble 𝕜 N}
    (hM : M.Assumptions ϑ δm δp C₀) {s : ℝ} (hs : 0 < s) :
    InformationTheory.klDiv (M.eigLaw s) (gbeLaw 𝕜 N) ≤
        InformationTheory.klDiv (M.flowLaw s) (gaussH 𝕜 N) ∧
      InformationTheory.klDiv (M.flowLaw s) (gaussH 𝕜 N) ≤
        ENNReal.ofReal (Module.finrank ℝ (Herm 𝕜 N) / 2 * Real.log (1 / (1 - Real.exp (-s))) +
          betaF 𝕜 * N ^ 2 / 4 * Real.exp (-s)) := by
  refine ⟨InformationTheory.klDiv_map_le (M.flowLaw s) (gaussH 𝕜 N)
    (continuous_eigVec N).measurable, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hfin : (Module.finrank ℝ (Herm 𝕜 0) : ℝ) = 0 := by
      rw [finrank_herm]
      simp
    have hsub : Subsingleton (Herm 𝕜 0) := Module.finrank_zero_iff.1 (by exact_mod_cast hfin)
    have heq : M.flowLaw s = gaussH 𝕜 0 := by
      ext t _
      rcases t.eq_empty_or_nonempty with rfl | hne
      · simp
      · rw [hne.eq_univ, measure_univ, measure_univ]
    rw [heq, InformationTheory.klDiv_self]
    exact zero_le
  · have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hβ := entropy_one_le_betaF (𝕜 := 𝕜)
    have hv : 0 < gaussVar 𝕜 N := by
      unfold gaussVar
      positivity
    have hint : Integrable (fun w : Herm 𝕜 N => ‖w‖ ^ 2) M.hermLaw := by
      simpa only [Real.rpow_two] using
        Ensemble.integrable_norm_pow_hermLaw hϑ hM (q := 2) (by norm_num)
    have h := klDiv_ouLaw_le hv hs M.hermLaw hint
    rw [Ensemble.integral_norm_sq_hermLaw hϑ hM] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    unfold gaussVar
    field_simp
    ring

/-- Lemma 18.1: `S(ν_s|μ) ≤ N³` for `s ≥ N⁻²`. -/
theorem klDiv_eigLaw_le_cube {N : ℕ} (hN : 1 ≤ N) {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    {M : Ensemble 𝕜 N} (hM : M.Assumptions ϑ δm δp C₀) {s : ℝ} (hs : (N : ℝ)⁻¹ ^ 2 ≤ s) :
    InformationTheory.klDiv (M.eigLaw s) (gbeLaw 𝕜 N) ≤ ENNReal.ofReal ((N : ℝ) ^ 3) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs
  obtain ⟨h1, h2⟩ := klDiv_eigLaw_le hϑ hM hspos
  refine h1.trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
  have hβ1 := entropy_one_le_betaF (𝕜 := 𝕜)
  have hβ2 := entropy_betaF_le_two (𝕜 := 𝕜)
  rw [finrank_herm]
  set β : ℝ := betaF 𝕜 with hβ
  set e : ℝ := Real.exp (-s) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have ha1 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hNr
  have has : 1 ≤ (N : ℝ) ^ 2 * s := by
    have h := mul_le_mul_of_nonneg_left hs (sq_nonneg (N : ℝ))
    rwa [← mul_pow, mul_inv_cancel₀ hN0.ne', one_pow] at h
  have hes : e * (1 + s) ≤ 1 := by
    have h := Real.add_one_le_exp s
    have h' := mul_le_mul_of_nonneg_left h he0.le
    rw [he, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h'
    linarith
  have hX : s ≤ (1 - e) * (1 + s) := by nlinarith
  have hlow : 1 ≤ 2 * (N : ℝ) ^ 2 * (1 - e) := by
    have hY : 1 + s ≤ 2 * (N : ℝ) ^ 2 * s := by
      nlinarith [mul_nonneg hspos.le (sub_nonneg.2 ha1)]
    have hZ : 1 + s ≤ (2 * (N : ℝ) ^ 2 * (1 - e)) * (1 + s) := by
      have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2)
      nlinarith
    exact le_of_mul_le_mul_right (by linarith) (by linarith : (0 : ℝ) < 1 + s)
  have hpos : 0 < 1 - e := by linarith
  set L : ℝ := Real.log (1 / (1 - e)) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_one_div hpos (by linarith))
  have hLle : L ≤ Real.log 2 + 2 * ((N : ℝ) - 1) := by
    have h1' : 1 / (1 - e) ≤ 2 * (N : ℝ) ^ 2 := by
      rw [div_le_iff₀ hpos]
      linarith
    have h2' : L ≤ Real.log (2 * (N : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) h1'
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2'
    have h3' := Real.log_le_sub_one_of_pos hN0
    push_cast at h2'
    linarith
  set d : ℝ := (N : ℝ) + β * N * (N - 1) / 2 with hd
  have hd0 : 0 ≤ d := by
    have : 0 ≤ β * N * (N - 1) := by
      exact mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ β) hN0.le)
        (by linarith : (0 : ℝ) ≤ N - 1)
    rw [hd]
    positivity
  have hdle : d ≤ (N : ℝ) ^ 2 := by
    have : β * N * (N - 1) ≤ 2 * N * (N - 1) := by
      have := mul_nonneg hN0.le (by linarith : (0 : ℝ) ≤ N - 1)
      nlinarith
    rw [hd]
    nlinarith
  have h3 : d / 2 * L ≤ (N : ℝ) ^ 2 / 2 * (Real.log 2 + 2 * ((N : ℝ) - 1)) := by
    calc d / 2 * L ≤ (N : ℝ) ^ 2 / 2 * L := by gcongr
      _ ≤ (N : ℝ) ^ 2 / 2 * (Real.log 2 + 2 * ((N : ℝ) - 1)) := by gcongr
  have h4 : β * (N : ℝ) ^ 2 / 4 * e ≤ (N : ℝ) ^ 2 / 2 := by
    have h5 : β * e ≤ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 4)]
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.2 hlog2.le)]

private lemma entropy_relaxW_nonneg (N : ℕ) (R : ℝ) (x : Fin N → ℝ) : 0 ≤ relaxW N R x := by
  unfold relaxW
  positivity

private lemma entropy_integrable_exp (N : ℕ) (R : ℝ) :
    Integrable (fun x => Real.exp (-(N * relaxW N R x))) (gbeLaw 𝕜 N) := by
  refine (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.comp (continuous_const.mul (entropy_continuous_relaxW N R)).neg
      ).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have := entropy_relaxW_nonneg N R x
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- `ω_R` is the exponential tilt of `μ` by `-N W_R` (Definition 16.5, first form of (16.5)). -/
private lemma entropy_relaxMeasure_eq_tilted (N : ℕ) (R : ℝ) :
    relaxMeasure 𝕜 N R = (gbeLaw 𝕜 N).tilted (fun x => -(N * relaxW N R x)) := by
  have hint := entropy_integrable_exp (𝕜 := 𝕜) N R
  have hZpos : 0 < ∫ x, Real.exp (-(N * relaxW N R x)) ∂gbeLaw 𝕜 N := integral_exp_pos hint
  have hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (-(N * relaxW N R x))) ∂gbeLaw 𝕜 N =
      ENNReal.ofReal (∫ x, Real.exp (-(N * relaxW N R x)) ∂gbeLaw 𝕜 N) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  unfold relaxMeasure Measure.tilted
  rw [hZ, ← ENNReal.ofReal_inv_of_pos hZpos, ← withDensity_smul _ (entropy_measurable_dens N R)]
  congr 1
  ext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le), div_eq_inv_mul]

/-- Lemma 18.2: `S(ν'|ω) ≤ S(ν'|μ) + (N/(2R²)) ∫ |x - γ|² dν'`. -/
theorem klDiv_relaxMeasure_le {N : ℕ} {R : ℝ} (hR : 0 < R) (ν' : Measure (Fin N → ℝ))
    [IsProbabilityMeasure ν'] (hac : ν' ≪ gbeLaw 𝕜 N)
    (h2 : Integrable (fun x => ∑ k, x k ^ 2) ν') :
    InformationTheory.klDiv ν' (relaxMeasure 𝕜 N R) ≤
      InformationTheory.klDiv ν' (gbeLaw 𝕜 N) +
        ENNReal.ofReal (N / (2 * R ^ 2) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂ν') := by
  rw [entropy_relaxMeasure_eq_tilted]
  set f : (Fin N → ℝ) → ℝ := fun x => -(N * relaxW N R x) with hf
  have hint : Integrable (fun x => Real.exp (f x)) (gbeLaw 𝕜 N) := entropy_integrable_exp N R
  have hωprob : IsProbabilityMeasure ((gbeLaw 𝕜 N).tilted f) := isProbabilityMeasure_tilted hint
  have hacω : ν' ≪ (gbeLaw 𝕜 N).tilted f := hac.trans (absolutelyContinuous_tilted hint)
  by_cases htop : InformationTheory.klDiv ν' (gbeLaw 𝕜 N) = ⊤
  · rw [htop, top_add]
    exact le_top
  · obtain ⟨-, hllr⟩ := InformationTheory.klDiv_ne_top_iff.1 htop
    have hS : Integrable (fun x : Fin N → ℝ => ∑ k, (x k - gamma N k) ^ 2) ν' := by
      have hcont : Continuous fun x : Fin N → ℝ => ∑ k, (x k - gamma N k) ^ 2 := by fun_prop
      refine ((h2.const_mul 2).add (integrable_const (2 * ∑ k, gamma N k ^ 2))).mono'
        hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
      change ∑ k, (x k - gamma N k) ^ 2 ≤ 2 * ∑ k, x k ^ 2 + 2 * ∑ k, gamma N k ^ 2
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (x k + gamma N k)]
    have hfν : Integrable f ν' := by
      have : f = fun x => -((N : ℝ) * (2 * R ^ 2)⁻¹) * ∑ k, (x k - gamma N k) ^ 2 := by
        ext x
        simp only [hf, relaxW]
        ring
      rw [this]
      exact hS.const_mul _
    have hA : 0 ≤ ∫ x, llr ν' (gbeLaw 𝕜 N) x ∂ν' := by
      have := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hllr
      simpa using this
    have hB : 0 ≤ (N : ℝ) / (2 * R ^ 2) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂ν' :=
      mul_nonneg (by positivity)
        (integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hZle : ∫ x, Real.exp (f x) ∂(gbeLaw 𝕜 N) ≤ 1 := by
      calc ∫ x, Real.exp (f x) ∂(gbeLaw 𝕜 N) ≤ ∫ _x, (1 : ℝ) ∂(gbeLaw 𝕜 N) :=
            integral_mono hint (integrable_const _) fun x => by
              rw [Real.exp_le_one_iff]
              have := entropy_relaxW_nonneg N R x
              have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
              simp only [hf]
              nlinarith
        _ = 1 := by simp
    have hlogZ : Real.log (∫ x, Real.exp (f x) ∂(gbeLaw 𝕜 N)) ≤ 0 :=
      Real.log_nonpos (integral_nonneg fun x => (Real.exp_pos _).le) hZle
    have hllr' : Integrable (llr ν' ((gbeLaw 𝕜 N).tilted f)) ν' :=
      integrable_llr_tilted_right hac hfν hllr hint
    have hintf : ∫ x, f x ∂ν' = -((N : ℝ) / (2 * R ^ 2) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂ν') := by
      have : f = fun x => -((N : ℝ) / (2 * R ^ 2)) * ∑ k, (x k - gamma N k) ^ 2 := by
        ext x
        simp only [hf, relaxW]
        ring
      rw [this, integral_const_mul]
      ring
    rw [InformationTheory.klDiv_of_ac_of_integrable hacω hllr',
      InformationTheory.klDiv_of_ac_of_integrable hac hllr,
      integral_llr_tilted_right hac hfν hint hllr, hintf]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [← ENNReal.ofReal_add hA hB]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith

end Rigidity
