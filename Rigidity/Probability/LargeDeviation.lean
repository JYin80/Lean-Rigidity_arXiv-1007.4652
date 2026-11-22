module

public import Rigidity.Probability.Moments

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-!
# Large deviation bounds for linear, diagonal and bilinear forms

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

`LDHyp μ ϑ X s` is hypothesis (4.1) of Section 4.2: the complex random variables `X i` are
independent, centred, of variance `s i ^ 2`, and satisfy
`P(‖X i‖ > x s i) ≤ ϑ⁻¹ e^{-x^ϑ}` for `x ≥ 1`. The conjugate family satisfies (4.1) again
(`LDHyp.conj`). For `0 < ϑ ≤ 1`, `κ ≥ κ_ϑ + log n` and the loss factor `ℓ(κ)` of (4.2), Lemma 4.2
bounds the tails of `∑ a i X i` by `ℓ(κ) (∑ ‖a i‖² s i²)^{1/2}` (4.3), of the diagonal form
`∑ b i (‖X i‖² - s i²)` by `ℓ(κ)² (∑ ‖b i‖² s i⁴)^{1/2}` (4.4), and of the bilinear form
`∑ X i B i j Y j` of two independent families by `ℓ(κ)² (∑ s i² ‖B i j‖² t j²)^{1/2}` (4.6).

The proofs follow Section 4.2: truncation at level `T = κ^{ϑ⁻¹}` and recentring (Step 1),
Hoeffding's inequality (H) for the real and imaginary parts of the truncated sums (Steps 2, 3),
and, for the bilinear form, conditioning on the second family through the product structure of
the joint law (Step 4).
-/

/-- Hypothesis (4.1) of §4.2 on a family `X` with scales `s`. -/
structure LDHyp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : ℝ) {n : ℕ}
    (X : Fin n → Ω → ℂ) (s : Fin n → ℝ) : Prop where
  indep : iIndepFun X μ
  meas : ∀ i, Measurable (X i)
  mean : ∀ i, ∫ ω, X i ω ∂μ = 0
  nonneg : ∀ i, 0 ≤ s i
  var : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ = s i ^ 2
  tail : ∀ i, ∀ x : ℝ, 1 ≤ x → μ {ω | x * s i < ‖X i ω‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ))

section LD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ϑ : ℝ}
  {n : ℕ} {X : Fin n → Ω → ℂ} {s : Fin n → ℝ}

/-- The conjugate family satisfies (4.1). -/
theorem LDHyp.conj (hX : LDHyp μ ϑ X s) : LDHyp μ ϑ (fun i ω => starRingEnd ℂ (X i ω)) s := by
  refine ⟨hX.indep.comp (fun _ => starRingEnd ℂ) (fun _ => Complex.continuous_conj.measurable),
    fun i => Complex.continuous_conj.measurable.comp (hX.meas i), fun i => ?_, hX.nonneg,
    fun i => ?_, fun i x hx => ?_⟩
  · rw [integral_conj, hX.mean i, map_zero]
  · simpa only [Complex.norm_conj] using hX.var i
  · simpa only [Complex.norm_conj] using hX.tail i x hx

/-- `log (4 C_ϑ) ≥ 1` for `0 < ϑ ≤ 1`, where `C_ϑ = 90 ϑ⁻¹`. -/
private lemma ld_one_le_log (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) : 1 ≤ Real.log (4 * cTheta ϑ⁻¹) := by
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have he : Real.exp 1 ≤ 4 * cTheta ϑ⁻¹ := by
    unfold cTheta
    have := Real.exp_one_lt_d9
    nlinarith
  exact (Real.le_log_iff_exp_le (by unfold cTheta; positivity)).2 he

/-- The hypothesis `κ_ϑ + log n ≤ κ` of Lemma 4.2 forces `κ ≥ 1`, so that the loss factors are
defined as in (4.2). -/
private lemma ld_one_le_kappa (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n) {κ : ℝ}
    (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) : 1 ≤ κ := by
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have h1 : 0 ≤ Real.log ϑ⁻¹ := Real.log_nonneg ha1
  have h2 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have h3 := ld_one_le_log hϑ hϑ1
  unfold kappaTheta at hκ
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 h3)]

/-- Hoeffding's inequality (H) of §4.2 for complex summands: independent centred `Z i` with
`‖Z i‖ ≤ c i` satisfy `P(2 (κ ∑ c i ^ 2)^{1/2} < ‖∑ Z i‖) ≤ 4 e^{-κ}`. -/
private lemma ld_hoeffding_complex {Z : Fin n → Ω → ℂ} (hind : iIndepFun Z μ)
    (hmeas : ∀ i, Measurable (Z i)) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) {c : Fin n → ℝ}
    (hbd : ∀ i ω, ‖Z i ω‖ ≤ c i) {κ : ℝ} (hκ : 0 ≤ κ) :
    μ {ω | 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖} ≤
      ENNReal.ofReal (4 * Real.exp (-κ)) := by
  have hint : ∀ i, Integrable (Z i) μ := fun i =>
    Integrable.of_bound (hmeas i).aestronglyMeasurable (c i)
      (Filter.Eventually.of_forall fun ω => hbd i ω)
  have hre := hoeffding_abs (μ := μ) (ξ := fun i ω => (Z i ω).re)
    (hind.comp (fun _ => Complex.re) (fun _ => Complex.measurable_re))
    (fun i => Complex.measurable_re.comp (hmeas i))
    (fun i => by
      have := integral_re (hint i)
      simp only [RCLike.re_to_complex] at this
      rw [this, hmean i]; simp) (c := c)
    (fun i => Filter.Eventually.of_forall fun ω => (Complex.abs_re_le_norm _).trans (hbd i ω)) hκ
  have him := hoeffding_abs (μ := μ) (ξ := fun i ω => (Z i ω).im)
    (hind.comp (fun _ => Complex.im) (fun _ => Complex.measurable_im))
    (fun i => Complex.measurable_im.comp (hmeas i))
    (fun i => by
      have := integral_im (hint i)
      simp only [RCLike.im_to_complex] at this
      rw [this, hmean i]; simp) (c := c)
    (fun i => Filter.Eventually.of_forall fun ω => (Complex.abs_im_le_norm _).trans (hbd i ω)) hκ
  have hV : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsub : {ω | 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖} ⊆
      {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, (Z i ω).re|} ∪
        {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, (Z i ω).im|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon hω
    obtain ⟨h1, h2⟩ := hcon
    have hr2 : Real.sqrt (2 * κ * ∑ i, c i ^ 2) ^ 2 = 2 * κ * ∑ i, c i ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hre2 : (∑ i, (Z i ω).re) ^ 2 ≤ 2 * κ * ∑ i, c i ^ 2 := by
      rw [← hr2, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have him2 : (∑ i, (Z i ω).im) ^ 2 ≤ 2 * κ * ∑ i, c i ^ 2 := by
      rw [← hr2, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hn2 : ‖∑ i, Z i ω‖ ^ 2 = (∑ i, (Z i ω).re) ^ 2 + (∑ i, (Z i ω).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, ← Complex.re_sum, ← Complex.im_sum]; ring
    have hlt := pow_lt_pow_left₀ hω (by positivity) (two_ne_zero)
    rw [mul_pow, Real.sq_sqrt (by positivity), hn2] at hlt
    nlinarith
  calc μ {ω | 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖}
      ≤ μ ({ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, (Z i ω).re|} ∪
        {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, (Z i ω).im|}) := measure_mono hsub
    _ ≤ μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, (Z i ω).re|} +
        μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, (Z i ω).im|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-κ)) + ENNReal.ofReal (2 * Real.exp (-κ)) :=
        add_le_add hre him
    _ = ENNReal.ofReal (4 * Real.exp (-κ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring


omit [IsProbabilityMeasure μ] in
/-- Truncation event: `P(∃ i, ‖X i‖ > T s i) ≤ n ϑ⁻¹ e^{-T^ϑ}` (Step 1 of the proof of
Lemma 4.2). -/
private lemma ld_trunc_event (hX : LDHyp μ ϑ X s) {T : ℝ} (hT : 1 ≤ T) :
    μ {ω | ¬ ∀ i, ‖X i ω‖ ≤ T * s i} ≤ ENNReal.ofReal (n * (ϑ⁻¹ * Real.exp (-T ^ ϑ))) := by
  have hsub : {ω | ¬ ∀ i, ‖X i ω‖ ≤ T * s i} ⊆ ⋃ i, {ω | T * s i < ‖X i ω‖} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  calc μ {ω | ¬ ∀ i, ‖X i ω‖ ≤ T * s i} ≤ μ (⋃ i, {ω | T * s i < ‖X i ω‖}) := measure_mono hsub
    _ ≤ ∑ i, μ {ω | T * s i < ‖X i ω‖} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (ϑ⁻¹ * Real.exp (-T ^ ϑ)) :=
        Finset.sum_le_sum fun i _ => hX.tail i T hT
    _ = ENNReal.ofReal (n * (ϑ⁻¹ * Real.exp (-T ^ ϑ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- Combination step of the proofs of (4.3), (4.4): off the truncation event the sum `F` equals a
centred bounded sum plus a constant `m`, and Hoeffding controls the centred sum. -/
private lemma ld_combine {Z : Fin n → Ω → ℂ} (hind : iIndepFun Z μ)
    (hmeas : ∀ i, Measurable (Z i)) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) {c : Fin n → ℝ}
    (hbd : ∀ i ω, ‖Z i ω‖ ≤ c i) {κ : ℝ} (hκ : 0 ≤ κ) {G : Set Ω} {A : ℝ}
    (hG : μ Gᶜ ≤ ENNReal.ofReal A) (hA : 0 ≤ A) {F : Ω → ℂ} {m : ℂ}
    (hF : ∀ ω ∈ G, F ω = ∑ i, Z i ω + m) {R : ℝ}
    (hR : 2 * Real.sqrt (κ * ∑ i, c i ^ 2) + ‖m‖ ≤ R) :
    μ {ω | R < ‖F ω‖} ≤ ENNReal.ofReal (A + 4 * Real.exp (-κ)) := by
  have hsub : {ω | R < ‖F ω‖} ⊆
      Gᶜ ∪ {ω | 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖} := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · right
      have h1 : R < ‖F ω‖ := hω
      rw [hF ω hωG] at h1
      have h2 := norm_add_le (∑ i, Z i ω) m
      change 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖
      linarith
    · exact Or.inl hωG
  calc μ {ω | R < ‖F ω‖}
      ≤ μ (Gᶜ ∪ {ω | 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖}) := measure_mono hsub
    _ ≤ μ Gᶜ + μ {ω | 2 * Real.sqrt (κ * ∑ i, c i ^ 2) < ‖∑ i, Z i ω‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal (4 * Real.exp (-κ)) :=
        add_le_add hG (ld_hoeffding_complex hind hmeas hmean hbd hκ)
    _ = ENNReal.ofReal (A + 4 * Real.exp (-κ)) :=
        (ENNReal.ofReal_add hA (by positivity)).symm

/-- The numerical smallness `√n · e^{L/2} · ϑ^{-1/2} e^{-κ/2} ≤ 1` for `κ ≥ log ϑ⁻¹ + L + log n`
(the recentring terms of Steps 2 and 3). -/
private lemma ld_small (hϑ : 0 < ϑ) (hn : 1 ≤ n) {L κ : ℝ}
    (hκ : Real.log ϑ⁻¹ + L + Real.log n ≤ κ) :
    Real.sqrt n * (Real.exp (L / 2) * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-κ / 2))) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : Real.sqrt n = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]; congr 1; ring
  have e2 : ϑ ^ (-(1 / 2 : ℝ)) = Real.exp (Real.log ϑ⁻¹ / 2) := by
    rw [Real.rpow_def_of_pos hϑ, Real.log_inv]; congr 1; ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
  linarith

/-- Transfer of the hypotheses of Lemma 4.1 to a single variable: for `X` with (4.1) the
truncated moments of `‖X‖` and `‖X‖ ^ 2` on `{T s < ‖X‖}` are bounded as in Lemma 4.1 (b), and
`‖X‖`, `‖X‖ ^ 2` are integrable. -/
private lemma ld_moments {X : Ω → ℂ} (hX : Measurable X) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {s : ℝ}
    (hs : 0 ≤ s) (hvar : ∫ ω, ‖X ω‖ ^ 2 ∂μ = s ^ 2)
    (htail : ∀ x : ℝ, 1 ≤ x → μ {ω | x * s < ‖X ω‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)))
    {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun ω => ‖X ω‖) μ ∧ Integrable (fun ω => ‖X ω‖ ^ 2) μ ∧
      ∫ ω in {ω | T * s < ‖X ω‖}, ‖X ω‖ ∂μ ≤ s * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) ∧
      ∫ ω in {ω | T * s < ‖X ω‖}, ‖X ω‖ ^ 2 ∂μ ≤
        (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2 * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) := by
  have hRm : MeasurableSet {y : ℂ | T * s < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have htail' : ∀ x : ℝ, 1 ≤ x →
      (μ.map X) {y | x * s < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)) := fun x hx => by
    rw [Measure.map_apply hX (measurableSet_lt measurable_const measurable_norm)]
    exact htail x hx
  have hvar' : ∫ y, ‖y‖ ^ 2 ∂(μ.map X) = s ^ 2 := by
    rw [integral_map hX.aemeasurable (measurable_norm.pow_const 2).aestronglyMeasurable]
    exact hvar
  obtain ⟨hset1, hset2⟩ := moments_trunc hϑ hϑ1 hs htail' hT
  obtain ⟨h1, -⟩ := moments_bound hϑ hϑ1 hs htail' (q := 1) le_rfl
  obtain ⟨h2, -⟩ := moments_bound hϑ hϑ1 hs htail' (q := 2) (by norm_num)
  rw [hvar', Real.sqrt_sq hs] at hset1
  rw [setIntegral_map (g := X) (f := fun y : ℂ => ‖y‖) hRm measurable_norm.aestronglyMeasurable
    hX.aemeasurable] at hset1
  rw [setIntegral_map (g := X) (f := fun y : ℂ => ‖y‖ ^ 2) hRm
    (measurable_norm.pow_const 2).aestronglyMeasurable hX.aemeasurable] at hset2
  rw [mul_assoc] at hset1 hset2
  refine ⟨?_, ?_, hset1, hset2⟩
  · have := (integrable_map_measure (measurable_norm.pow_const (1 : ℝ)).aestronglyMeasurable
      hX.aemeasurable).1 h1
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
  · have := (integrable_map_measure (measurable_norm.pow_const (2 : ℝ)).aestronglyMeasurable
      hX.aemeasurable).1 h2
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp


/-- Truncation and recentring of one variable, linear case (Step 1 of the proof of Lemma 4.2,
(T1)–(T3)): there are a Borel function `g` and a constant `m` with `E g(X) = 0`, `‖g‖ ≤ 2 T s`,
`‖m‖ ≤ s ϑ^{-1/2} e^{-T^ϑ/2}`, and `y = g y + m` for `‖y‖ ≤ T s`. -/
private lemma ld_trunc_lin {X : Ω → ℂ} (hX : Measurable X) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (hmean : ∫ ω, X ω ∂μ = 0) {s : ℝ} (hs : 0 ≤ s) (hvar : ∫ ω, ‖X ω‖ ^ 2 ∂μ = s ^ 2)
    (htail : ∀ x : ℝ, 1 ≤ x → μ {ω | x * s < ‖X ω‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)))
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ g : ℂ → ℂ, Measurable g ∧ (∀ y, ‖g y‖ ≤ 2 * (T * s)) ∧ ∫ ω, g (X ω) ∂μ = 0 ∧
      ∃ m : ℂ, ‖m‖ ≤ s * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) ∧
        ∀ y, ‖y‖ ≤ T * s → y = g y + m := by
  obtain ⟨hI1, -, hset1, -⟩ := ld_moments hX hϑ hϑ1 hs hvar htail hT
  have hXint : Integrable X μ :=
    hI1.mono' hX.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => le_rfl)
  have hRm : MeasurableSet {ω | T * s < ‖X ω‖} := measurableSet_lt measurable_const hX.norm
  have hPm : MeasurableSet {y : ℂ | ‖y‖ ≤ T * s} :=
    measurableSet_le measurable_norm measurable_const
  have hTs : 0 ≤ T * s := mul_nonneg (by linarith) hs
  have hind : ∀ ω, {y : ℂ | ‖y‖ ≤ T * s}.indicator id (X ω) =
      {ω | T * s < ‖X ω‖}ᶜ.indicator X ω := by
    intro ω
    by_cases h : ‖X ω‖ ≤ T * s
    · have h1 : X ω ∈ {y : ℂ | ‖y‖ ≤ T * s} := h
      have h2 : ω ∈ {ω | T * s < ‖X ω‖}ᶜ := fun h' => absurd h (not_le.2 h')
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]; rfl
    · have h1 : X ω ∉ {y : ℂ | ‖y‖ ≤ T * s} := h
      have h2 : ω ∉ {ω | T * s < ‖X ω‖}ᶜ := fun h' => h' (not_le.1 h)
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hbd : ∀ y : ℂ, ‖{y : ℂ | ‖y‖ ≤ T * s}.indicator id y‖ ≤ T * s := by
    intro y
    by_cases h : y ∈ {y : ℂ | ‖y‖ ≤ T * s}
    · rw [Set.indicator_of_mem h]; exact h
    · rw [Set.indicator_of_notMem h]; simpa using hTs
  set m : ℂ := ∫ ω, {y : ℂ | ‖y‖ ≤ T * s}.indicator id (X ω) ∂μ with hm
  have hmint : Integrable (fun ω => {y : ℂ | ‖y‖ ≤ T * s}.indicator id (X ω)) μ := by
    have := hXint.indicator hRm.compl
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hind ω).symm
  have hmnorm : ‖m‖ ≤ T * s := by
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun ω => {y : ℂ | ‖y‖ ≤ T * s}.indicator id (X ω)) (C := T * s)
      (Filter.Eventually.of_forall fun ω => hbd (X ω))
    simpa using this
  have hmeq : m = -∫ ω in {ω | T * s < ‖X ω‖}, X ω ∂μ := by
    have h1 := integral_add_compl hRm hXint
    rw [hmean] at h1
    have h2 : m = ∫ ω in {ω | T * s < ‖X ω‖}ᶜ, X ω ∂μ := by
      rw [hm, integral_congr_ae (Filter.Eventually.of_forall hind), integral_indicator hRm.compl]
    rw [h2]
    exact eq_neg_of_add_eq_zero_right h1
  refine ⟨fun y => {y : ℂ | ‖y‖ ≤ T * s}.indicator id y - m,
    (measurable_id.indicator hPm).sub_const m, fun y => ?_, ?_, m, ?_, fun y hy => ?_⟩
  · calc ‖{y : ℂ | ‖y‖ ≤ T * s}.indicator id y - m‖
        ≤ ‖{y : ℂ | ‖y‖ ≤ T * s}.indicator id y‖ + ‖m‖ := norm_sub_le _ _
      _ ≤ 2 * (T * s) := by linarith [hbd y]
  · rw [integral_sub hmint (integrable_const m), integral_const]
    simp [← hm]
  · rw [hmeq, norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact hset1
  · change y = {y : ℂ | ‖y‖ ≤ T * s}.indicator id y - m + m
    rw [Set.indicator_of_mem (show y ∈ {y : ℂ | ‖y‖ ≤ T * s} from hy)]
    simp

/-- Truncation and recentring of one variable, diagonal case (Step 1 of the proof of Lemma 4.2,
(T1)–(T3)): there are a Borel function `h` and a constant `ρ ≥ 0` with `E h(X) = 0`,
`|h| ≤ T² s²`, `ρ ≤ (4 C_ϑ)^{2 ϑ⁻¹} s² ϑ^{-1/2} e^{-T^ϑ/2}`, and `‖y‖² - s² = h y - ρ` for
`‖y‖ ≤ T s`. -/
private lemma ld_trunc_diag {X : Ω → ℂ} (hX : Measurable X) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    {s : ℝ} (hs : 0 ≤ s) (hvar : ∫ ω, ‖X ω‖ ^ 2 ∂μ = s ^ 2)
    (htail : ∀ x : ℝ, 1 ≤ x → μ {ω | x * s < ‖X ω‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-x ^ ϑ)))
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ h : ℂ → ℝ, Measurable h ∧ (∀ y, |h y| ≤ T ^ 2 * s ^ 2) ∧ ∫ ω, h (X ω) ∂μ = 0 ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧
        ρ ≤ (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * s ^ 2 * (ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2)) ∧
        ∀ y, ‖y‖ ≤ T * s → ‖y‖ ^ 2 - s ^ 2 = h y - ρ := by
  obtain ⟨-, hI2, -, hset2⟩ := ld_moments hX hϑ hϑ1 hs hvar htail hT
  have hRm : MeasurableSet {ω | T * s < ‖X ω‖} := measurableSet_lt measurable_const hX.norm
  have hPm : MeasurableSet {y : ℂ | ‖y‖ ≤ T * s} :=
    measurableSet_le measurable_norm measurable_const
  have hTs : 0 ≤ T * s := mul_nonneg (by linarith) hs
  set w : ℂ → ℝ := {y : ℂ | ‖y‖ ≤ T * s}.indicator (fun y => ‖y‖ ^ 2) with hw
  have hwm : Measurable w := (measurable_norm.pow_const 2).indicator hPm
  have hw0 : ∀ y, 0 ≤ w y := fun y => Set.indicator_nonneg (fun y _ => sq_nonneg _) y
  have hw1 : ∀ y, w y ≤ T ^ 2 * s ^ 2 := by
    intro y
    by_cases h : y ∈ {y : ℂ | ‖y‖ ≤ T * s}
    · rw [hw, Set.indicator_of_mem h]
      have : ‖y‖ ≤ T * s := h
      calc ‖y‖ ^ 2 ≤ (T * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = T ^ 2 * s ^ 2 := by ring
    · rw [hw, Set.indicator_of_notMem h]; positivity
  have hind : ∀ ω, w (X ω) = {ω | T * s < ‖X ω‖}ᶜ.indicator (fun ω => ‖X ω‖ ^ 2) ω := by
    intro ω
    by_cases h : ‖X ω‖ ≤ T * s
    · have h1 : X ω ∈ {y : ℂ | ‖y‖ ≤ T * s} := h
      have h2 : ω ∈ {ω | T * s < ‖X ω‖}ᶜ := fun h' => absurd h (not_le.2 h')
      rw [hw, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have h1 : X ω ∉ {y : ℂ | ‖y‖ ≤ T * s} := h
      have h2 : ω ∉ {ω | T * s < ‖X ω‖}ᶜ := fun h' => h' (not_le.1 h)
      rw [hw, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  set M : ℝ := ∫ ω, w (X ω) ∂μ with hM
  have hwint : Integrable (fun ω => w (X ω)) μ :=
    Integrable.of_bound (hwm.comp hX).aestronglyMeasurable (T ^ 2 * s ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)]; exact hw1 _)
  have hM0 : 0 ≤ M := integral_nonneg fun ω => hw0 _
  have hM1 : M ≤ T ^ 2 * s ^ 2 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => w (X ω))
      (C := T ^ 2 * s ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)]; exact hw1 _)
    exact (le_abs_self M).trans (by simpa using this)
  have hρ : s ^ 2 - M = ∫ ω in {ω | T * s < ‖X ω‖}, ‖X ω‖ ^ 2 ∂μ := by
    have h1 := integral_add_compl hRm hI2
    rw [hvar] at h1
    have h2 : M = ∫ ω in {ω | T * s < ‖X ω‖}ᶜ, ‖X ω‖ ^ 2 ∂μ := by
      rw [hM, integral_congr_ae (Filter.Eventually.of_forall hind), integral_indicator hRm.compl]
    rw [h2]; linarith
  refine ⟨fun y => w y - M, hwm.sub_const M, fun y => ?_, ?_, s ^ 2 - M, ?_, ?_, fun y hy => ?_⟩
  · rw [abs_le]; constructor <;> linarith [hw0 y, hw1 y]
  · rw [integral_sub hwint (integrable_const M), integral_const]
    simp [← hM]
  · rw [hρ]; exact setIntegral_nonneg hRm fun ω _ => sq_nonneg _
  · rw [hρ]; exact hset2
  · have : w y = ‖y‖ ^ 2 := by
      rw [hw, Set.indicator_of_mem (show y ∈ {y : ℂ | ‖y‖ ≤ T * s} from hy)]
    simp only [this]; ring


/-- Cauchy–Schwarz for `n` nonnegative terms: `∑ u i ≤ √n (∑ u i ^ 2)^{1/2}`. -/
private lemma ld_cs (u : Fin n → ℝ) : ∑ i, u i ≤ Real.sqrt n * Real.sqrt (∑ i, u i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) u
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)

/-- The loss factor in the form `5 T √κ` with `T = κ^{ϑ⁻¹}`. -/
private lemma ld_lossL_eq {κ : ℝ} (hκ : 0 < κ) :
    lossL ϑ⁻¹ κ = 5 * (κ ^ ϑ⁻¹ * Real.sqrt κ) := by
  unfold lossL
  rw [Real.rpow_add hκ, ← Real.sqrt_eq_rpow]

/-- Lemma 4.2, (4.3): linear forms. -/
theorem ld_linear (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n) (a : Fin n → ℂ)
    {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | lossL ϑ⁻¹ κ * Real.sqrt (∑ i, ‖a i‖ ^ 2 * s i ^ 2) < ‖∑ i, a i * X i ω‖} ≤
      ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) := by
  have hκ1 : 1 ≤ κ := ld_one_le_kappa hϑ hϑ1 hn hκ
  have hκ0 : 0 < κ := by linarith
  set T : ℝ := κ ^ ϑ⁻¹ with hTdef
  have hT1 : 1 ≤ T := Real.one_le_rpow hκ1 (inv_nonneg.2 hϑ.le)
  have hTϑ : T ^ ϑ = κ := by
    rw [hTdef, ← Real.rpow_mul hκ0.le, inv_mul_cancel₀ hϑ.ne', Real.rpow_one]
  choose g hgm hgb hgint m hm hgx using fun i =>
    ld_trunc_lin (hX.meas i) hϑ hϑ1 (hX.mean i) (hX.nonneg i) (hX.var i) (hX.tail i) hT1
  rw [hTϑ] at hm
  have hsn : ∀ i, 0 ≤ s i := hX.nonneg
  set S : ℝ := Real.sqrt (∑ i, ‖a i‖ ^ 2 * s i ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = ∑ i, ‖a i‖ ^ 2 * s i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by have := hsn i; positivity)
  have hZind : iIndepFun (fun i ω => a i * g i (X i ω)) μ :=
    hX.indep.comp (fun i y => a i * g i y) (fun i => measurable_const.mul (hgm i))
  have hZmeas : ∀ i, Measurable (fun ω => a i * g i (X i ω)) := fun i =>
    measurable_const.mul ((hgm i).comp (hX.meas i))
  have hZmean : ∀ i, ∫ ω, a i * g i (X i ω) ∂μ = 0 := fun i => by
    rw [integral_const_mul, hgint i, mul_zero]
  have hZbd : ∀ i ω, ‖a i * g i (X i ω)‖ ≤ ‖a i‖ * (2 * (T * s i)) := fun i ω => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hgb i _) (norm_nonneg _)
  have hcsum : ∑ i, (‖a i‖ * (2 * (T * s i))) ^ 2 = (2 * T * S) ^ 2 := by
    rw [mul_pow, hS2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : Real.sqrt (κ * ∑ i, (‖a i‖ * (2 * (T * s i))) ^ 2) = Real.sqrt κ * (2 * T * S) := by
    rw [hcsum, Real.sqrt_mul hκ0.le, Real.sqrt_sq (by positivity)]
  have hmm : ‖∑ i, a i * m i‖ ≤ S := by
    have hsmall := ld_small hϑ hn (L := 0) (κ := κ) (by
      have h1 := hκ
      unfold kappaTheta at h1
      have h2 := ld_one_le_log hϑ hϑ1
      have h3 : 0 < ϑ⁻¹ := inv_pos.2 hϑ
      nlinarith)
    rw [zero_div, Real.exp_zero, one_mul] at hsmall
    set E : ℝ := ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-κ / 2) with hE
    have hE0 : 0 ≤ E := by positivity
    have hcs := ld_cs (n := n) (fun i => ‖a i‖ * s i)
    have e1 : ∑ i, (‖a i‖ * s i) ^ 2 = S ^ 2 := by
      rw [hS2]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, Real.sqrt_sq hS0] at hcs
    calc ‖∑ i, a i * m i‖ ≤ ∑ i, ‖a i * m i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖a i‖ * s i * E := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          calc ‖a i‖ * ‖m i‖ ≤ ‖a i‖ * (s i * E) :=
                mul_le_mul_of_nonneg_left (hm i) (norm_nonneg _)
            _ = ‖a i‖ * s i * E := by ring
      _ = (∑ i, ‖a i‖ * s i) * E := by rw [Finset.sum_mul]
      _ ≤ (Real.sqrt n * S) * E := mul_le_mul_of_nonneg_right hcs hE0
      _ = S * (Real.sqrt n * E) := by ring
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hsmall hS0
      _ = S := mul_one S
  have hlossL := ld_lossL_eq (ϑ := ϑ) hκ0
  have hTκ : 1 ≤ T * Real.sqrt κ := by
    have : 1 ≤ Real.sqrt κ := Real.one_le_sqrt.2 hκ1
    nlinarith
  have hev := ld_trunc_event hX hT1
  rw [hTϑ] at hev
  have hfin := ld_combine hZind hZmeas hZmean hZbd hκ0.le
    (G := {ω | ∀ i, ‖X i ω‖ ≤ T * s i}) (A := n * (ϑ⁻¹ * Real.exp (-κ))) hev
    (by have := inv_pos.2 hϑ; positivity) (F := fun ω => ∑ i, a i * X i ω)
    (m := ∑ i, a i * m i)
    (fun ω hω => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← mul_add, ← hgx i (X i ω) (hω i)])
    (R := lossL ϑ⁻¹ κ * S) (by
      rw [hsq, hlossL]
      nlinarith [mul_le_mul_of_nonneg_right hTκ hS0])
  refine hfin.trans (le_of_eq ?_)
  congr 1
  rw [div_eq_mul_inv]; ring


/-- Lemma 4.2, (4.4): diagonal quadratic forms. -/
theorem ld_diag (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n) (b : Fin n → ℂ)
    {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ i, ‖b i‖ ^ 2 * s i ^ 4) <
        ‖∑ i, b i * ((‖X i ω‖ ^ 2 : ℝ) - (s i ^ 2 : ℝ))‖} ≤
      ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) := by
  have hκ1 : 1 ≤ κ := ld_one_le_kappa hϑ hϑ1 hn hκ
  have hκ0 : 0 < κ := by linarith
  set T : ℝ := κ ^ ϑ⁻¹ with hTdef
  have hT1 : 1 ≤ T := Real.one_le_rpow hκ1 (inv_nonneg.2 hϑ.le)
  have hTϑ : T ^ ϑ = κ := by
    rw [hTdef, ← Real.rpow_mul hκ0.le, inv_mul_cancel₀ hϑ.ne', Real.rpow_one]
  choose h hhm hhb hhint ρ hρ0 hρ hhx using fun i =>
    ld_trunc_diag (hX.meas i) hϑ hϑ1 (hX.nonneg i) (hX.var i) (hX.tail i) hT1
  rw [hTϑ] at hρ
  have hsn : ∀ i, 0 ≤ s i := hX.nonneg
  set S : ℝ := Real.sqrt (∑ i, ‖b i‖ ^ 2 * s i ^ 4) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = ∑ i, ‖b i‖ ^ 2 * s i ^ 4 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by have := hsn i; positivity)
  have hZind : iIndepFun (fun i ω => b i * ((h i (X i ω) : ℝ) : ℂ)) μ :=
    hX.indep.comp (fun i y => b i * ((h i y : ℝ) : ℂ))
      (fun i => measurable_const.mul (Complex.measurable_ofReal.comp (hhm i)))
  have hZmeas : ∀ i, Measurable (fun ω => b i * ((h i (X i ω) : ℝ) : ℂ)) := fun i =>
    measurable_const.mul (Complex.measurable_ofReal.comp ((hhm i).comp (hX.meas i)))
  have hZmean : ∀ i, ∫ ω, b i * ((h i (X i ω) : ℝ) : ℂ) ∂μ = 0 := fun i => by
    rw [integral_const_mul, integral_complex_ofReal, hhint i]; simp
  have hZbd : ∀ i ω, ‖b i * ((h i (X i ω) : ℝ) : ℂ)‖ ≤ ‖b i‖ * (T ^ 2 * s i ^ 2) := fun i ω => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hhb i _) (norm_nonneg _)
  have hcsum : ∑ i, (‖b i‖ * (T ^ 2 * s i ^ 2)) ^ 2 = (T ^ 2 * S) ^ 2 := by
    rw [mul_pow, hS2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : Real.sqrt (κ * ∑ i, (‖b i‖ * (T ^ 2 * s i ^ 2)) ^ 2) =
      Real.sqrt κ * (T ^ 2 * S) := by
    rw [hcsum, Real.sqrt_mul hκ0.le, Real.sqrt_sq (by positivity)]
  have hmm : ‖-∑ i, b i * (ρ i : ℂ)‖ ≤ S := by
    have hsmall := ld_small hϑ hn (L := 4 * ϑ⁻¹ * Real.log (4 * cTheta ϑ⁻¹)) (κ := κ) (by
      have := hκ
      unfold kappaTheta at this
      linarith)
    have hRc : Real.exp (4 * ϑ⁻¹ * Real.log (4 * cTheta ϑ⁻¹) / 2) =
        (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) := by
      rw [Real.rpow_def_of_pos (by unfold cTheta; positivity)]; congr 1; ring
    rw [hRc] at hsmall
    set Rc : ℝ := (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) with hRcdef
    set E : ℝ := ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-κ / 2) with hE
    have hRc0 : 0 ≤ Rc := by rw [hRcdef]; unfold cTheta; positivity
    have hE0 : 0 ≤ E := by positivity
    have hcs := ld_cs (n := n) (fun i => ‖b i‖ * s i ^ 2)
    have e1 : ∑ i, (‖b i‖ * s i ^ 2) ^ 2 = S ^ 2 := by
      rw [hS2]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, Real.sqrt_sq hS0] at hcs
    rw [norm_neg]
    calc ‖∑ i, b i * (ρ i : ℂ)‖ ≤ ∑ i, ‖b i * (ρ i : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ * s i ^ 2 * (Rc * E) := Finset.sum_le_sum fun i _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 i)]
          calc ‖b i‖ * ρ i ≤ ‖b i‖ * (Rc * s i ^ 2 * E) :=
                mul_le_mul_of_nonneg_left (hρ i) (norm_nonneg _)
            _ = ‖b i‖ * s i ^ 2 * (Rc * E) := by ring
      _ = (∑ i, ‖b i‖ * s i ^ 2) * (Rc * E) := by rw [Finset.sum_mul]
      _ ≤ (Real.sqrt n * S) * (Rc * E) :=
          mul_le_mul_of_nonneg_right hcs (mul_nonneg hRc0 hE0)
      _ = S * (Real.sqrt n * (Rc * E)) := by ring
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hsmall hS0
      _ = S := mul_one S
  have hlossL := ld_lossL_eq (ϑ := ϑ) hκ0
  have hv : 1 ≤ Real.sqrt κ := Real.one_le_sqrt.2 hκ1
  have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT1
  have hev := ld_trunc_event hX hT1
  rw [hTϑ] at hev
  have hfin := ld_combine hZind hZmeas hZmean hZbd hκ0.le
    (G := {ω | ∀ i, ‖X i ω‖ ≤ T * s i}) (A := n * (ϑ⁻¹ * Real.exp (-κ))) hev
    (by have := inv_pos.2 hϑ; positivity)
    (F := fun ω => ∑ i, b i * ((‖X i ω‖ ^ 2 : ℝ) - (s i ^ 2 : ℝ)))
    (m := -∑ i, b i * (ρ i : ℂ))
    (fun ω hω => by
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_sub, ← Complex.ofReal_sub, hhx i (X i ω) (hω i)]
      push_cast; ring)
    (R := lossL ϑ⁻¹ κ ^ 2 * S) (by
      rw [hsq, hlossL]
      have h1 : 1 ≤ T ^ 2 * Real.sqrt κ ^ 2 :=
        one_le_mul_of_one_le_of_one_le hT2 (one_le_pow₀ hv)
      have h2 : Real.sqrt κ * T ^ 2 ≤ T ^ 2 * Real.sqrt κ ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hv) (sq_nonneg T)]
      nlinarith [mul_le_mul_of_nonneg_right h1 hS0, mul_le_mul_of_nonneg_right h2 hS0])
  refine hfin.trans (le_of_eq ?_)
  congr 1
  rw [div_eq_mul_inv]; ring


/-- Lemma 4.2, (4.6): bilinear forms in two independent families. -/
theorem ld_bilinear (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n) {n' : ℕ}
    (hn' : 1 ≤ n') (hn'n : n' ≤ n) {Y : Fin n' → Ω → ℂ} {t : Fin n' → ℝ} (hY : LDHyp μ ϑ Y t)
    (hXY : iIndepFun (Sum.elim X Y) μ) (B : Matrix (Fin n) (Fin n') ℂ) {κ : ℝ}
    (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2) <
        ‖∑ i, ∑ j, X i ω * B i j * Y j ω‖} ≤
      ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := by
  have hκ1 : 1 ≤ κ := ld_one_le_kappa hϑ hϑ1 hn hκ
  have hκ0 : 0 < κ := by linarith
  have hℓ0 : 0 ≤ lossL ϑ⁻¹ κ := by rw [ld_lossL_eq hκ0]; positivity
  set ℓ : ℝ := lossL ϑ⁻¹ κ with hℓ
  have hκ' : kappaTheta ϑ⁻¹ + Real.log n' ≤ κ := by
    have : Real.log (n' : ℝ) ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hn') (by exact_mod_cast hn'n)
    linarith
  set U : Ω → Fin n → ℂ := fun ω i => X i ω with hU
  set W : Ω → Fin n' → ℂ := fun ω j => Y j ω with hW
  have hUm : Measurable U := Measurable.of_eval hX.meas
  have hWm : Measurable W := Measurable.of_eval hY.meas
  have hmeasXY : ∀ k, Measurable (Sum.elim X Y k) := by
    rintro (i | j)
    · exact hX.meas i
    · exact hY.meas j
  have hind := hXY.indepFun_finset (Finset.univ.map Function.Embedding.inl)
    (Finset.univ.map Function.Embedding.inr) (by simp [Finset.disjoint_left]) hmeasXY
  have hUW : IndepFun U W μ :=
    hind.comp
      (φ := fun v : (Finset.univ.map
          (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin n') : Finset _) → ℂ =>
        fun i : Fin n => v ⟨Sum.inl i, by simp⟩)
      (ψ := fun v : (Finset.univ.map
          (Function.Embedding.inr : Fin n' ↪ Fin n ⊕ Fin n') : Finset _) → ℂ =>
        fun j : Fin n' => v ⟨Sum.inr j, by simp⟩)
      (Measurable.of_eval fun i => measurable_pi_apply _)
      (Measurable.of_eval fun i => measurable_pi_apply _)
  have hjoint : μ.map (fun ω => (U ω, W ω)) = (μ.map U).prod (μ.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hUm.aemeasurable hWm.aemeasurable).1 hUW
  set E' : Set ((Fin n → ℂ) × (Fin n' → ℂ)) := {p | ℓ * Real.sqrt (∑ i, ‖∑ j, B i j * p.2 j‖ ^ 2 *
    s i ^ 2) < ‖∑ i, (∑ j, B i j * p.2 j) * p.1 i‖} with hE'
  have hE'm : MeasurableSet E' := by
    refine measurableSet_lt ?_ ?_
    · fun_prop
    · fun_prop
  have hE1 : μ ((fun ω => (U ω, W ω)) ⁻¹' E') ≤ ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) := by
    rw [← Measure.map_apply (hUm.prodMk hWm) hE'm, hjoint, Measure.prod_apply_symm hE'm]
    calc ∫⁻ y, (μ.map U) ((fun x => (x, y)) ⁻¹' E') ∂(μ.map W)
        ≤ ∫⁻ _y, ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) ∂(μ.map W) := by
          refine lintegral_mono fun y => ?_
          rw [Measure.map_apply hUm (hE'm.preimage measurable_prodMk_right)]
          exact ld_linear hX hϑ hϑ1 hn (fun i => ∑ j, B i j * y j) hκ
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hE2 : μ (⋃ i : Fin n, {ω | ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) <
      ‖∑ j, B i j * Y j ω‖}) ≤ ENNReal.ofReal (n * ((4 + n' / ϑ) * Real.exp (-κ))) := by
    calc μ (⋃ i : Fin n, {ω | ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) < ‖∑ j, B i j * Y j ω‖})
        ≤ ∑ i : Fin n, μ {ω | ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) < ‖∑ j, B i j * Y j ω‖} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal ((4 + n' / ϑ) * Real.exp (-κ)) :=
          Finset.sum_le_sum fun i _ => ld_linear hY hϑ hϑ1 hn' (fun j => B i j) hκ'
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  have hsub : {ω | ℓ ^ 2 * Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2) <
        ‖∑ i, ∑ j, X i ω * B i j * Y j ω‖} ⊆
      (fun ω => (U ω, W ω)) ⁻¹' E' ∪ ⋃ i : Fin n, {ω | ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) <
        ‖∑ j, B i j * Y j ω‖} := by
    intro ω hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    set c : Fin n → ℂ := fun i => ∑ j, B i j * Y j ω with hc
    have hsum : ∑ i, ∑ j, X i ω * B i j * Y j ω = ∑ i, c i * X i ω := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc]
      change _ = (∑ j, B i j * Y j ω) * X i ω
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hnorm : ‖∑ i, c i * X i ω‖ ≤ ℓ * Real.sqrt (∑ i, ‖c i‖ ^ 2 * s i ^ 2) := not_lt.1 h1
    have hr : ∀ i, ‖c i‖ ≤ ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) := fun i =>
      not_lt.1 fun hi => h2 (Set.mem_iUnion.2 ⟨i, hi⟩)
    have hQ : ∑ i, ‖c i‖ ^ 2 * s i ^ 2 ≤ ℓ ^ 2 * ∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hq0 : 0 ≤ ∑ j, ‖B i j‖ ^ 2 * t j ^ 2 := Finset.sum_nonneg fun j _ => by positivity
      calc ‖c i‖ ^ 2 * s i ^ 2
          ≤ (ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2)) ^ 2 * s i ^ 2 := by
            gcongr; exact hr i
        _ = ℓ ^ 2 * ((∑ j, ‖B i j‖ ^ 2 * t j ^ 2) * s i ^ 2) := by
            rw [mul_pow, Real.sq_sqrt hq0]; ring
        _ = ℓ ^ 2 * ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2 := by
            rw [Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
    have hfinal : ‖∑ i, ∑ j, X i ω * B i j * Y j ω‖ ≤
        ℓ ^ 2 * Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2) := by
      rw [hsum]
      calc ‖∑ i, c i * X i ω‖ ≤ ℓ * Real.sqrt (∑ i, ‖c i‖ ^ 2 * s i ^ 2) := hnorm
        _ ≤ ℓ * Real.sqrt (ℓ ^ 2 * ∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ) hℓ0
        _ = ℓ ^ 2 * Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg ℓ), Real.sqrt_sq hℓ0]; ring
    exact absurd hω (not_lt.2 hfinal)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : (n' : ℝ) ≤ n := by exact_mod_cast hn'n
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hy0 : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
  have hnum : (4 + n / ϑ) + n * (4 + n' / ϑ) ≤ 10 * n ^ 2 / ϑ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    set a : ℝ := ϑ⁻¹
    set x : ℝ := (n : ℝ)
    set y : ℝ := (n' : ℝ)
    have h1 : 1 ≤ x * x * a :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hx hx) ha
    have h2 : x * a ≤ x * x * a := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ a))
        (sub_nonneg.2 hx)]
    have h3 : x ≤ x * x * a := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ x))
        (sub_nonneg.2 ha), mul_nonneg (by linarith : (0:ℝ) ≤ x) (sub_nonneg.2 hx)]
    have h4 : x * y * a ≤ x * x * a := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ a))
        (sub_nonneg.2 hy)]
    nlinarith
  calc μ {ω | ℓ ^ 2 * Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * t j ^ 2) <
        ‖∑ i, ∑ j, X i ω * B i j * Y j ω‖}
      ≤ μ ((fun ω => (U ω, W ω)) ⁻¹' E' ∪ ⋃ i : Fin n,
          {ω | ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) < ‖∑ j, B i j * Y j ω‖}) :=
        measure_mono hsub
    _ ≤ μ ((fun ω => (U ω, W ω)) ⁻¹' E') + μ (⋃ i : Fin n,
          {ω | ℓ * Real.sqrt (∑ j, ‖B i j‖ ^ 2 * t j ^ 2) < ‖∑ j, B i j * Y j ω‖}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) +
          ENNReal.ofReal (n * ((4 + n' / ϑ) * Real.exp (-κ))) := add_le_add hE1 hE2
    _ = ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ) + n * ((4 + n' / ϑ) * Real.exp (-κ))) :=
        (ENNReal.ofReal_add (by have := inv_pos.2 hϑ; positivity)
          (by have := inv_pos.2 hϑ; positivity)).symm
    _ ≤ ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_right hnum (Real.exp_pos (-κ)).le
        nlinarith


end LD

end Rigidity
