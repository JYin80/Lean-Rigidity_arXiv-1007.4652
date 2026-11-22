module

public import Mathlib

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace Rigidity

open ProbabilityTheory

/-!
# Moments, Hoeffding and large deviations

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].
-/

/-! ### §4.1–4.2: moments, Hoeffding, large deviations (Lemmas 4.1–4.3) -/

/-- `C_ϑ = 90a` (§4). -/
noncomputable def cTheta (a : ℝ) : ℝ := 90 * a

/-- `κ_ϑ = log a + 4a log(4 C_ϑ)` (§4). -/
noncomputable def kappaTheta (a : ℝ) : ℝ := Real.log a + 4 * a * Real.log (4 * cTheta a)

/-- The loss factor `ℓ(κ) = 5 κ^{a + 1/2}` of (4.2). -/
noncomputable def lossL (a κ : ℝ) : ℝ := 5 * κ ^ (a + 1 / 2)

/-- The loss factor `ℓ₂(κ, n) = 2 ℓ(κ)² √(2⌈log₂ n⌉ + 2)` of (4.2). -/
noncomputable def lossL2 (a κ : ℝ) (n : ℕ) : ℝ :=
  2 * lossL a κ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)

/-- The elementary bound `u ^ t * exp (-u / 2) ≤ (2 * t) ^ t` for `t, u > 0`, that is
`sup_{u>0} u^t e^{-u/2} ≤ (2t)^t` in the proof of Lemma 4.1 (a) (§4.1). -/
private lemma rpow_mul_exp_neg_half_le {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    u ^ t * Real.exp (-u / 2) ≤ (2 * t) ^ t := by
  have h2t : 0 < 2 * t := by positivity
  have hlog : Real.log (u / (2 * t)) ≤ u / (2 * t) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hu.ne' h2t.ne'] at hlog
  have h3 := mul_le_mul_of_nonneg_left hlog ht.le
  have h4 : t * (u / (2 * t) - 1) = u / 2 - t := by field_simp
  rw [h4] at h3
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos h2t, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

/-- The integral `∫₀¹ u^(t-1) du = 1/t` for `t > 0`, as a `ℝ≥0∞`-valued Lebesgue integral
(the contribution of `x ≤ 1` in the proof of Lemma 4.1 (a)). -/
private lemma lintegral_rpow_sub_one_Ioc {t : ℝ} (ht : 0 < t) :
    ∫⁻ u in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ (t - 1)) = ENNReal.ofReal (1 / t) := by
  have hint : IntervalIntegrable (fun u : ℝ => u ^ (t - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hint' : IntegrableOn (fun u : ℝ => u ^ (t - 1)) (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun u : ℝ => u ^ (t - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact Real.rpow_nonneg hu.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint' hnn,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
  have : t - 1 + 1 = t := by ring
  rw [this, Real.one_rpow, Real.zero_rpow ht.ne']
  simp

/-- The integral `∫₀^∞ K e^{-u/2} du = 2K` for `K ≥ 0`, as a `ℝ≥0∞`-valued Lebesgue integral
(Lemma 4.1 (a), §4.1). -/
private lemma lintegral_exp_neg_half_Ioi {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (K * Real.exp (-u / 2)) = ENNReal.ofReal (2 * K) := by
  have hint : IntegrableOn (fun u : ℝ => K * Real.exp (-u / 2)) (Set.Ioi 0) volume := by
    have e : (fun u : ℝ => K * Real.exp (-u / 2)) = fun u : ℝ => K * Real.exp (-1 / 2 * u) := by
      funext u; congr 2; ring
    rw [e]
    exact (integrableOn_exp_mul_Ioi (a := -1 / 2) (by norm_num) 0).const_mul K
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun u : ℝ => K * Real.exp (-u / 2) :=
    Filter.Eventually.of_forall fun u => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul]
  have h2 : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u / 2) = 2 := by
    have := integral_exp_mul_Ioi (a := -1 / 2) (by norm_num) 0
    rw [show (fun u : ℝ => Real.exp (-u / 2)) = fun u : ℝ => Real.exp (-1 / 2 * u) from by
      funext u; congr 1; ring]
    rw [this]; norm_num
  rw [h2]; congr 1; ring

/-- Layer-cake estimate of Lemma 4.1 (a) (§4.1): if `ν{Z > u} ≤ a e^{-u}` for all `u ≥ 1` and
`ν` is a probability measure, then `∫ Z^t dν ≤ 1 + 2 a t (2t)^t` for `t > 0`. -/
private lemma moments_aux {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {Z : α → ℝ} (hZ : Measurable Z) (hZ0 : ∀ y, 0 ≤ Z y) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t)
    (htail : ∀ u : ℝ, 1 ≤ u → ν {y | u < Z y} ≤ ENNReal.ofReal (a * Real.exp (-u))) :
    ∫⁻ y, ENNReal.ofReal (Z y ^ t) ∂ν ≤ ENNReal.ofReal (1 + 2 * a * t * (2 * t) ^ t) := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul ν (Filter.Eventually.of_forall hZ0)
    hZ.aemeasurable ht]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
  have h1 : ∫⁻ u in Set.Ioc (0 : ℝ) 1, ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1)) ≤
      ENNReal.ofReal (1 / t) := by
    rw [← lintegral_rpow_sub_one_Ioc ht]
    refine lintegral_mono fun u => ?_
    calc ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1))
        ≤ 1 * ENNReal.ofReal (u ^ (t - 1)) := by gcongr; exact prob_le_one
      _ = _ := one_mul _
  have h2 : ∫⁻ u in Set.Ioi (1 : ℝ), ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1)) ≤
      ENNReal.ofReal (2 * (a * (2 * t) ^ t)) := by
    have hK : 0 ≤ a * (2 * t) ^ t := by positivity
    rw [← lintegral_exp_neg_half_Ioi hK]
    calc ∫⁻ u in Set.Ioi (1 : ℝ), ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1))
        ≤ ∫⁻ u in Set.Ioi (1 : ℝ), ENNReal.ofReal (a * (2 * t) ^ t * Real.exp (-u / 2)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun u hu => ?_
          have hu1 : (1 : ℝ) ≤ u := hu.le
          have hu0 : 0 < u := by linarith
          calc ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1))
              ≤ ENNReal.ofReal (a * Real.exp (-u)) * ENNReal.ofReal (u ^ (t - 1)) := by
                gcongr; exact htail u hu1
            _ = ENNReal.ofReal (a * Real.exp (-u) * u ^ (t - 1)) := by
                exact (ENNReal.ofReal_mul (by positivity)).symm
            _ ≤ _ := by
                apply ENNReal.ofReal_le_ofReal
                have h5 : u ^ (t - 1) ≤ u ^ t :=
                  Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
                have h6 := rpow_mul_exp_neg_half_le ht hu0
                have h7 : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
                  rw [← Real.exp_add]; congr 1; ring
                have h8 : 0 < Real.exp (-u / 2) := Real.exp_pos _
                calc a * Real.exp (-u) * u ^ (t - 1)
                    ≤ a * Real.exp (-u) * u ^ t := by gcongr
                  _ = a * Real.exp (-u / 2) * (u ^ t * Real.exp (-u / 2)) := by rw [h7]; ring
                  _ ≤ a * Real.exp (-u / 2) * (2 * t) ^ t := by gcongr
                  _ = a * (2 * t) ^ t * Real.exp (-u / 2) := by ring
      _ ≤ ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (a * (2 * t) ^ t * Real.exp (-u / 2)) :=
          lintegral_mono_set (Set.Ioi_subset_Ioi zero_le_one)
  calc ENNReal.ofReal t *
        ((∫⁻ u in Set.Ioc (0 : ℝ) 1, ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1)))
          + ∫⁻ u in Set.Ioi (1 : ℝ), ν {y | u < Z y} * ENNReal.ofReal (u ^ (t - 1)))
      ≤ ENNReal.ofReal t * (ENNReal.ofReal (1 / t) + ENNReal.ofReal (2 * (a * (2 * t) ^ t))) := by
        gcongr
    _ = ENNReal.ofReal (1 + 2 * a * t * (2 * t) ^ t) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul ht.le]
        congr 1
        field_simp

/-- The numerical step `1 + 2 a t (2t)^t ≤ (90 t)^t` for `a ≤ t` and `t ≥ 1` at the end of the
proof of Lemma 4.1 (a) (§4.1). -/
private lemma moments_real_bound {a t : ℝ} (hat : a ≤ t) (ht : 1 ≤ t) :
    1 + 2 * a * t * (2 * t) ^ t ≤ (90 * t) ^ t := by
  have ht0 : 0 < t := by linarith
  have h2t : t ≤ (2 : ℝ) ^ t := by
    have := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) ht
    norm_num at this
    linarith
  have hX : 1 ≤ (8 * t) ^ t := Real.one_le_rpow (by linarith) ht0.le
  have h3 : 3 ≤ (3 : ℝ) ^ t := by
    calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ 3 ^ t := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
  have e1 : (8 * t) ^ t = 4 ^ t * (2 * t) ^ t := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]; ring_nf
  have e2 : (4 : ℝ) ^ t = 2 ^ t * 2 ^ t := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have e3 : (24 * t) ^ t = 3 ^ t * (8 * t) ^ t := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]; ring_nf
  have h4 : (24 * t) ^ t ≤ (90 * t) ^ t := Real.rpow_le_rpow (by positivity) (by linarith) ht0.le
  have h5 : a * t ≤ 4 ^ t := by
    calc a * t ≤ t * t := by gcongr
      _ ≤ 2 ^ t * 2 ^ t := by gcongr
      _ = 4 ^ t := e2.symm
  have h6 : 2 * a * t * (2 * t) ^ t ≤ 2 * (8 * t) ^ t := by
    rw [e1]
    have : 0 ≤ (2 * t) ^ t := by positivity
    nlinarith
  calc 1 + 2 * a * t * (2 * t) ^ t ≤ 1 + 2 * (8 * t) ^ t := by linarith
    _ ≤ 3 * (8 * t) ^ t := by linarith
    _ ≤ 3 ^ t * (8 * t) ^ t := by gcongr
    _ = (24 * t) ^ t := e3.symm
    _ ≤ (90 * t) ^ t := h4

/-- The Cauchy–Schwarz step of Lemma 4.1 (b) (§4.1): for measurable `f ≥ 0` with `f²` integrable and
measurable `R`, `∫_R f dμ ≤ (∫ f² dμ)^{1/2} μ(R)^{1/2}`. -/
private lemma setIntegral_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hf2 : Integrable (fun y => f y ^ 2) μ) {R : Set α} (hR : MeasurableSet R) :
    ∫ y in R, f y ∂μ ≤ Real.sqrt (∫ y, f y ^ 2 ∂μ) * Real.sqrt (μ.real R) := by
  set g : α → ℝ := R.indicator fun _ => (1 : ℝ) with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have hgm : Measurable g := measurable_const.indicator hR
  have hmf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 hf2
  have hmg : MemLp g (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    refine memLp_of_bounded (a := 0) (b := 1) (Filter.Eventually.of_forall fun y => ?_)
      hgm.aestronglyMeasurable 2
    exact ⟨hg0 y, Set.indicator_le_self' (fun _ _ => zero_le_one) y⟩
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := g) (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hmf hmg
  have e1 : ∫ y, f y * g y ∂μ = ∫ y in R, f y ∂μ := by
    rw [← integral_indicator hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ R <;> simp [hg, hy]
  have e2 : ∫ y, f y ^ (2 : ℝ) ∂μ = ∫ y, f y ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  have e3 : ∫ y, g y ^ (2 : ℝ) ∂μ = μ.real R := by
    rw [← integral_indicator_one hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ R <;> simp [hg, hy]
  rw [e1, e2, e3] at key
  simpa [Real.sqrt_eq_rpow] using key

section Moments

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The case `s = 0` of Lemma 4.1 (a) (§4.1): the tail hypothesis with vanishing scale forces
`μ = δ₀`. -/
private lemma moments_dirac_aux {ϑ : ℝ} (hϑ : 0 < ϑ) {μ : Measure E} [IsProbabilityMeasure μ]
    (htail : ∀ x : ℝ, 1 ≤ x → μ {y | x * 0 < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ))) :
    μ = Measure.dirac 0 := by
  have h0 : μ {y | 0 < ‖y‖} = 0 := by
    have hlim : Filter.Tendsto (fun x : ℝ => ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun x : ℝ => x ^ ϑ) Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop hϑ
      have h2 : Filter.Tendsto (fun x : ℝ => Real.exp (-x ^ ϑ)) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      have h3 := h2.const_mul ϑ⁻¹
      rw [mul_zero] at h3
      simpa using ENNReal.tendsto_ofReal h3
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    simpa using htail x hx
  have hs : MeasurableSet ({0} : Set E) := measurableSet_singleton 0
  have hcompl : μ ({0} : Set E)ᶜ = 0 := by
    have : ({0} : Set E)ᶜ = {y | 0 < ‖y‖} := by
      ext y; simp [norm_pos_iff]
    rw [this]; exact h0
  have hμ0 : μ {0} = 1 := (prob_compl_eq_zero_iff hs).1 hcompl
  have hae : ∀ᵐ y ∂μ, y ∈ ({0} : Set E) := by
    rw [ae_iff]
    exact hcompl
  have hr := Measure.restrict_eq_self_of_ae_mem hae
  rw [Measure.restrict_singleton, hμ0, one_smul] at hr
  exact hr.symm

/-- Lemma 4.1 (a): moments under the tail bound. -/
theorem moments_bound {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {μ : Measure E} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s)
    (htail : ∀ x : ℝ, 1 ≤ x → μ {y | x * s < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)))
    {q : ℝ} (hq : 1 ≤ q) :
    Integrable (fun y => ‖y‖ ^ q) μ ∧ ∫ y, ‖y‖ ^ q ∂μ ≤ (cTheta ϑ⁻¹ * q) ^ (q / ϑ) * s ^ q := by
  have hq0 : 0 < q := by linarith
  by_cases hs0 : s = 0
  · subst hs0
    rw [moments_dirac_aux hϑ htail]
    have hf0 : (fun y : E => ‖y‖ ^ q) =ᵐ[Measure.dirac (0 : E)] fun _ => (0 : ℝ) := by
      have := ae_eq_dirac (a := (0 : E)) (fun y : E => ‖y‖ ^ q)
      refine this.trans (Filter.EventuallyEq.of_eq ?_)
      funext y
      simp [Real.zero_rpow hq0.ne']
    refine ⟨(integrable_zero E ℝ _).congr hf0.symm, ?_⟩
    rw [integral_congr_ae hf0]
    simp [Real.zero_rpow hq0.ne']
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have ha0 : 0 < ϑ⁻¹ := by linarith
  have hta : q / ϑ = ϑ⁻¹ * q := by rw [div_eq_inv_mul]
  have ht1 : 1 ≤ ϑ⁻¹ * q := by nlinarith
  have ht0 : 0 < q / ϑ := by rw [hta]; linarith
  set Z : E → ℝ := fun y => (‖y‖ / s) ^ ϑ with hZdef
  have hZ : Measurable Z := (measurable_norm.div_const s).pow_const ϑ
  have hZ0 : ∀ y, 0 ≤ Z y := fun y => Real.rpow_nonneg (by positivity) _
  have htail' : ∀ u : ℝ, 1 ≤ u → μ {y | u < Z y} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-u)) := by
    intro u hu
    have hu0 : 0 ≤ u := by linarith
    calc μ {y | u < Z y} ≤ μ {y | u ^ ϑ⁻¹ * s < ‖y‖} := by
          refine measure_mono fun y hy => ?_
          have hy' : u < (‖y‖ / s) ^ ϑ := hy
          have h1 : u ^ ϑ⁻¹ < ((‖y‖ / s) ^ ϑ) ^ ϑ⁻¹ := Real.rpow_lt_rpow hu0 hy' ha0
          rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ hϑ.ne', Real.rpow_one] at h1
          exact (lt_div_iff₀ hspos).1 h1
      _ ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(u ^ ϑ⁻¹) ^ ϑ)) :=
          htail (u ^ ϑ⁻¹) (Real.one_le_rpow hu ha0.le)
      _ = ENNReal.ofReal (ϑ⁻¹ * Real.exp (-u)) := by
          rw [← Real.rpow_mul hu0, inv_mul_cancel₀ hϑ.ne', Real.rpow_one]
  have hmain := moments_aux (ν := μ) hZ hZ0 (a := ϑ⁻¹) (t := q / ϑ) ha0.le ht0 htail'
  have hpt : ∀ y : E, ‖y‖ ^ q = s ^ q * Z y ^ (q / ϑ) := by
    intro y
    simp only [hZdef]
    rw [← Real.rpow_mul (by positivity), show ϑ * (q / ϑ) = q by field_simp,
      Real.div_rpow (norm_nonneg y) hspos.le]
    field_simp
  have hbound : 1 + 2 * ϑ⁻¹ * (q / ϑ) * (2 * (q / ϑ)) ^ (q / ϑ) ≤ (cTheta ϑ⁻¹ * q) ^ (q / ϑ) := by
    have := moments_real_bound (a := ϑ⁻¹) (t := q / ϑ) (by rw [hta]; nlinarith)
      (by rw [hta]; exact ht1)
    have e : cTheta ϑ⁻¹ * q = 90 * (q / ϑ) := by rw [hta, cTheta]; ring
    rw [e]; exact this
  have hlint : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ q) ∂μ ≤
      ENNReal.ofReal (s ^ q * (cTheta ϑ⁻¹ * q) ^ (q / ϑ)) := by
    calc ∫⁻ y, ENNReal.ofReal (‖y‖ ^ q) ∂μ
        = ∫⁻ y, ENNReal.ofReal (s ^ q) * ENNReal.ofReal (Z y ^ (q / ϑ)) ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [hpt y, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (s ^ q) * ∫⁻ y, ENNReal.ofReal (Z y ^ (q / ϑ)) ∂μ := by
          rw [lintegral_const_mul]
          exact (hZ.pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal (s ^ q) * ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ (q / ϑ)) := by
          gcongr
          exact hmain.trans (ENNReal.ofReal_le_ofReal hbound)
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hnn : 0 ≤ᵐ[μ] fun y : E => ‖y‖ ^ q := Filter.Eventually.of_forall fun y => by positivity
  have hmeas : Measurable fun y : E => ‖y‖ ^ q := measurable_norm.pow_const q
  have hint : Integrable (fun y : E => ‖y‖ ^ q) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  have hCq : 0 ≤ cTheta ϑ⁻¹ * q := by unfold cTheta; positivity
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
  calc _ ≤ s ^ q * (cTheta ϑ⁻¹ * q) ^ (q / ϑ) := this
    _ = _ := mul_comm _ _

/-- Lemma 4.1 (b): truncation. -/
theorem moments_trunc {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {μ : Measure E} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s)
    (htail : ∀ x : ℝ, 1 ≤ x → μ {y | x * s < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)))
    {T : ℝ} (hT : 1 ≤ T) :
    ∫ y in {y | T * s < ‖y‖}, ‖y‖ ∂μ ≤
        Real.sqrt (∫ y, ‖y‖ ^ 2 ∂μ) * ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2) ∧
      ∫ y in {y | T * s < ‖y‖}, ‖y‖ ^ 2 ∂μ ≤
        (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2 * ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2) := by
  have hRm : MeasurableSet {y : E | T * s < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hμR : μ.real {y : E | T * s < ‖y‖} ≤ ϑ⁻¹ * Real.exp (-T ^ ϑ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (htail T hT)
  have hsq : Real.sqrt (μ.real {y : E | T * s < ‖y‖}) ≤
      ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2) := by
    have e1 : Real.sqrt (ϑ⁻¹ * Real.exp (-T ^ ϑ)) = ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.rpow_neg hϑ.le,
        Real.inv_rpow hϑ.le]
      congr 1
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← Real.exp_add]
      congr 1; ring
    exact (Real.sqrt_le_sqrt hμR).trans e1.le
  have hmul : ∀ {A : ℝ}, 0 ≤ A → A * Real.sqrt (μ.real {y : E | T * s < ‖y‖}) ≤
      A * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) := fun hA => mul_le_mul_of_nonneg_left hsq hA
  obtain ⟨hI2, -⟩ := moments_bound hϑ hϑ1 hs htail (q := 2) (by norm_num)
  obtain ⟨hI4, hB4⟩ := moments_bound hϑ hϑ1 hs htail (q := 4) (by norm_num)
  have hI2' : Integrable (fun y : E => ‖y‖ ^ 2) μ := by
    refine hI2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  have hI4' : Integrable (fun y : E => (‖y‖ ^ 2) ^ 2) μ := by
    refine hI4.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← pow_mul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨?_, ?_⟩
  · calc ∫ y in {y : E | T * s < ‖y‖}, ‖y‖ ∂μ
        ≤ Real.sqrt (∫ y, ‖y‖ ^ 2 ∂μ) * Real.sqrt (μ.real {y : E | T * s < ‖y‖}) :=
          setIntegral_le_sqrt_mul_sqrt (f := fun y : E => ‖y‖) (fun _ => norm_nonneg _)
            measurable_norm hI2' hRm
      _ ≤ Real.sqrt (∫ y, ‖y‖ ^ 2 ∂μ) * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) :=
          hmul (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have hC : 0 ≤ 4 * cTheta ϑ⁻¹ := by unfold cTheta; positivity
    have hW : Real.sqrt (∫ y, (‖y‖ ^ 2) ^ 2 ∂μ) ≤ (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2 := by
      have e2 : (cTheta ϑ⁻¹ * 4) ^ (4 / ϑ) * s ^ (4 : ℝ) =
          ((4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2) ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast s, ← Real.rpow_natCast,
          mul_comm (cTheta ϑ⁻¹) 4, ← Real.rpow_mul hC]
        have : (4 : ℝ) / ϑ = 2 * ϑ⁻¹ * ((2 : ℕ) : ℝ) := by push_cast; ring
        rw [this, ← Real.rpow_mul hs]
        norm_num
      have h4 : ∫ y, (‖y‖ ^ 2) ^ 2 ∂μ ≤ (cTheta ϑ⁻¹ * 4) ^ (4 / ϑ) * s ^ (4 : ℝ) := by
        refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))) hB4
        simp only
        rw [← pow_mul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [e2] at h4
      calc Real.sqrt (∫ y, (‖y‖ ^ 2) ^ 2 ∂μ)
          ≤ Real.sqrt (((4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2) ^ 2) := Real.sqrt_le_sqrt h4
        _ = _ := Real.sqrt_sq (by positivity)
    calc ∫ y in {y : E | T * s < ‖y‖}, ‖y‖ ^ 2 ∂μ
        ≤ Real.sqrt (∫ y, (‖y‖ ^ 2) ^ 2 ∂μ) * Real.sqrt (μ.real {y : E | T * s < ‖y‖}) :=
          setIntegral_le_sqrt_mul_sqrt (f := fun y : E => ‖y‖ ^ 2) (fun _ => by positivity)
            (measurable_norm.pow_const 2) hI4' hRm
      _ ≤ Real.sqrt (∫ y, (‖y‖ ^ 2) ^ 2 ∂μ) * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) :=
          hmul (Real.sqrt_nonneg _)
      _ ≤ ((4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2) *
            (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) := by
          gcongr
      _ = _ := by ring

end Moments

/-- One-sided form of statement (H) of §4.2: for independent sub-Gaussian `ξ i` with variance
proxies `v i` and `V = ∑ v i > 0`, `P(√(2κV) ≤ ∑ ξ i) ≤ e^{-κ}`. -/
private lemma hoeffding_one_sided {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ μ) {v : Fin n → NNReal}
    (hsg : ∀ i, HasSubgaussianMGF (ξ i) (v i) μ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hV : 0 < ∑ i, (v i : ℝ)) :
    μ.real {ω | Real.sqrt (2 * κ * ∑ i, (v i : ℝ)) ≤ ∑ i, ξ i ω} ≤ Real.exp (-κ) := by
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := Finset.univ)
    (fun i _ => hsg i) (ε := Real.sqrt (2 * κ * ∑ i, (v i : ℝ))) (Real.sqrt_nonneg _)
  have e : -(Real.sqrt (2 * κ * ∑ i, (v i : ℝ))) ^ 2 / (2 * ((∑ i, v i : NNReal) : ℝ)) = -κ := by
    rw [Real.sq_sqrt (by positivity), NNReal.coe_sum]
    field_simp
  rwa [e] at h

/-- Statement (H) of §4.2: Hoeffding's inequality, two-sided. -/
theorem hoeffding_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {ξ : Fin n → Ω → ℝ} (hind : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hmean : ∀ i, ∫ ω, ξ i ω ∂μ = 0) {c : Fin n → ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |ξ i ω| ≤ c i)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, ξ i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-κ)) := by
  set v : Fin n → NNReal := fun i => ‖c i‖₊ ^ 2 with hv
  have hvR : ∀ i, (v i : ℝ) = c i ^ 2 := fun i => by simp [hv]
  have hsum : ∑ i, (v i : ℝ) = ∑ i, c i ^ 2 := Finset.sum_congr rfl fun i _ => hvR i
  have hsg : ∀ i, HasSubgaussianMGF (ξ i) (v i) μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := ξ i) (a := -|c i|)
      (b := |c i|) (hmeas i).aemeasurable
      (by
        filter_upwards [hbd i] with ω hω
        have : |ξ i ω| ≤ |c i| := hω.trans (le_abs_self _)
        exact abs_le.1 this) (hmean i)
    have e : (‖|c i| - -|c i|‖₊ / 2) ^ 2 = v i := by
      apply NNReal.coe_injective
      simp only [hv, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
      rw [sub_neg_eq_add, ← two_mul, abs_mul, abs_abs, abs_two]
      ring_nf
    rwa [e] at h
  by_cases hV : ∑ i, c i ^ 2 = 0
  · have hc0 : ∀ i, c i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).1 hV i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hall : ∀ᵐ ω ∂μ, ∀ i, |ξ i ω| ≤ c i := ae_all_iff.2 hbd
    have hnull : μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, ξ i ω|} = 0 := by
      have : ∀ᵐ ω ∂μ, ¬ (Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, ξ i ω|) := by
        filter_upwards [hall] with ω hω
        have hz : ∑ i, ξ i ω = 0 := Finset.sum_eq_zero fun i _ => by
          have := hω i
          rw [hc0 i] at this
          exact abs_nonpos_iff.1 this
        simp [hz]
      simpa [ae_iff] using this
    rw [hnull]
    exact bot_le
  · have hVpos : 0 < ∑ i, c i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (c j)) (Ne.symm hV)
    have hVv : 0 < ∑ i, (v i : ℝ) := by rw [hsum]; exact hVpos
    have hA := hoeffding_one_sided hind hsg hκ hVv
    have hind' : iIndepFun (fun i ω => -ξ i ω) μ :=
      hind.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
    have hsg' : ∀ i, HasSubgaussianMGF (fun ω => -ξ i ω) (v i) μ := fun i => (hsg i).neg
    have hB := hoeffding_one_sided hind' hsg' hκ hVv
    rw [hsum] at hA hB
    have hsub : {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, ξ i ω|} ⊆
        {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) ≤ ∑ i, ξ i ω} ∪
          {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) ≤ ∑ i, -ξ i ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib] at hω ⊢
      rcases lt_abs.1 hω with h | h
      · exact Or.inl h.le
      · exact Or.inr h.le
    calc μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, ξ i ω|}
        ≤ μ ({ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) ≤ ∑ i, ξ i ω} ∪
          {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) ≤ ∑ i, -ξ i ω}) := measure_mono hsub
      _ ≤ μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) ≤ ∑ i, ξ i ω} +
          μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) ≤ ∑ i, -ξ i ω} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-κ)) + ENNReal.ofReal (Real.exp (-κ)) := by
          gcongr
          · rw [← ofReal_measureReal]
            exact ENNReal.ofReal_le_ofReal hA
          · rw [← ofReal_measureReal]
            exact ENNReal.ofReal_le_ofReal hB
      _ = ENNReal.ofReal (2 * Real.exp (-κ)) := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1; ring

end Rigidity
