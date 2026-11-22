module

public import Rigidity.Probability.Decoupling
public import Rigidity.Probability.LargeDeviation
public import Rigidity.Probability.Moments

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-!
# Large deviations in moment form

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Under hypothesis (4.1) (`LDHyp`), for `0 < ϑ ≤ 1`, `n ≥ 1` and real `q ≥ 2`, Lemma 4.3 bounds the
`L^q` norm `‖F‖_q = (E |F|^q)^{1/q}` of linear forms by
`C_LD (q + log n)^{ϑ⁻¹ + 1/2} (∑ ‖a i‖² s i²)^{1/2}` (4.7) and of centred quadratic forms
`∑ X̄ i B i j X j - ∑ s i² B i i` by
`C_LD (q + log n)^{2ϑ⁻¹ + 3/2} (∑ s i² ‖B i j‖² s j²)^{1/2}` (4.8), with
`C_LD = 150 (4ϑ⁻¹ + 2 + κ_ϑ)^{2ϑ⁻¹ + 1}` (`cLD`). The same bounds hold for the conjugate family
(`LDHyp.conj`).

The proof follows Lemma 4.3. Step 1 turns a tail bound `P(F > c κ^ρ) ≤ A e^{-κ}` for `κ ≥ κ₀` into
a moment bound by summing over the levels `t_k = c (κ₁ + k)^ρ` (M1 ⇒ M2), with no change of
variables. Steps 2 and 3 apply it to the tail bounds of Lemma 4.2, (4.3) for linear forms and
(4.4), (4.5) for the diagonal and off-diagonal parts of the quadratic form, with
`κ₁ = 2rq + log n + κ_ϑ` and `r = ϑ⁻¹ + 1/2`, respectively `κ₁ = 4rq + 3 log n + κ_ϑ`.
-/

section LDHelpers

/-! ### Numerical facts -/

/-- `e^{1/2} / (1 - e^{-1/2}) ≤ 5`, the constant of the geometric sum in (M2). -/
private lemma ldmoment_geom_const : Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2))) ≤ 5 := by
  have hy0 : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have hy1 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  have hy2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hy3 : Real.exp (1 / 2) ≤ 17 / 10 := by
    have h1 := Real.exp_one_lt_d9
    nlinarith
  have hneg : Real.exp (-(1 / 2)) = (Real.exp (1 / 2))⁻¹ := Real.exp_neg _
  rw [hneg]
  have hpos : 0 < 1 - (Real.exp (1 / 2))⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
  rw [div_le_iff₀ hpos]
  rw [← sub_nonneg]
  have : 5 * (1 - (Real.exp (1 / 2))⁻¹) - Real.exp (1 / 2) =
      (5 * Real.exp (1 / 2) - 5 - Real.exp (1 / 2) ^ 2) / Real.exp (1 / 2) := by
    field_simp
  rw [this]
  apply div_nonneg _ hy0.le
  nlinarith

/-- `e^{12} ≥ 256`. -/
private lemma ldmoment_exp_twelve : (256 : ℝ) ≤ Real.exp 12 := by
  have h3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have : Real.exp 12 = Real.exp 3 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (256 : ℝ) = 4 ^ 4 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h3 4

/-- `κ_ϑ ≥ log ϑ⁻¹ + 12` for `ϑ⁻¹ ≥ 1`. -/
private lemma ldmoment_kappa_ge {a : ℝ} (ha : 1 ≤ a) : Real.log a + 12 ≤ kappaTheta a := by
  unfold kappaTheta cTheta
  have h3 : (3 : ℝ) ≤ Real.log (4 * (90 * a)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h4 : Real.exp 1 ^ 3 ≤ 3 ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 3
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 h3)]

/-- `κ_ϑ ≥ 0` for `ϑ⁻¹ ≥ 1`. -/
private lemma ldmoment_kappa_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ kappaTheta a := by
  have := ldmoment_kappa_ge ha
  have := Real.log_nonneg ha
  linarith

/-- The prefactor times `e^{-κ₁}` for `κ₁ = t + m log n + κ_ϑ` is at most `1/256`:
`n^m ϑ⁻¹ e^{-κ₁} ≤ e^{-12}`. -/
private lemma ldmoment_exp_bound {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (m : ℕ) :
    (n : ℝ) ^ m * a * Real.exp (-(t + m * Real.log n + kappaTheta a)) ≤ 1 / 256 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := by linarith
  have hκ := ldmoment_kappa_ge ha
  have h1 : Real.exp (-(t + m * Real.log n + kappaTheta a)) ≤
      Real.exp (-t) * (((n : ℝ) ^ m)⁻¹ * (a⁻¹ * Real.exp (-12))) := by
    have hnm : Real.exp (-(m * Real.log n)) = ((n : ℝ) ^ m)⁻¹ := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0]
    have hla : Real.exp (-Real.log a) = a⁻¹ := by rw [Real.exp_neg, Real.exp_log ha0]
    have e1 : Real.exp (-(t + m * Real.log n + (Real.log a + 12))) =
        Real.exp (-t) * (Real.exp (-(m * Real.log n)) *
          (Real.exp (-Real.log a) * Real.exp (-12))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [← hnm, ← hla, ← e1]
    exact Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h3 : Real.exp (-12) ≤ 1 / 256 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) ldmoment_exp_twelve
  have hnm : 0 < (n : ℝ) ^ m := by positivity
  calc (n : ℝ) ^ m * a * Real.exp (-(t + m * Real.log n + kappaTheta a))
      ≤ (n : ℝ) ^ m * a * (Real.exp (-t) * (((n : ℝ) ^ m)⁻¹ * (a⁻¹ * Real.exp (-12)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (-t) * Real.exp (-12) := by field_simp
    _ ≤ 1 * (1 / 256) := mul_le_mul h2 h3 (Real.exp_pos _).le zero_le_one
    _ = 1 / 256 := one_mul _

/-- `⌈log₂ n⌉ ≤ (3/2) log n + 1` for `n ≥ 1`. -/
private lemma ldmoment_clog_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 3 / 2 * Real.log n + 1 := by
  rcases hn.eq_or_lt with h1 | h1
  · subst h1; simp
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos := Nat.clog_pos (b := 2) (by norm_num) h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : ((Nat.clog 2 n).pred : ℝ) * Real.log 2 < Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) (by exact_mod_cast hlt)
    have hpred : ((Nat.clog 2 n).pred : ℝ) = (Nat.clog 2 n : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub hpos]; simp
    rw [hpred] at hlog
    have h2 := Real.log_two_gt_d9
    have hD : (1 : ℝ) ≤ Nat.clog 2 n := by exact_mod_cast hpos
    nlinarith

/-- `⌈log₂ 2n⌉ ≤ n` for `n ≥ 1` (`2 n ≤ 2 ^ n`). -/
private lemma ldmoment_clog_two_mul_le {n : ℕ} (hn : 1 ≤ n) : Nat.clog 2 (2 * n) ≤ n := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [pow_succ]
    omega

/-- `C_n = 25 (1 + √(2 ⌈log₂ n⌉ + 2)) ≤ 75 √(q + log n)` for `q ≥ 2` (Step 3 of Lemma 4.3). -/
private lemma ldmoment_cn_le {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : 2 ≤ q) :
    25 * (1 + Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) ≤ 75 * Real.sqrt (q + Real.log n) := by
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hD := ldmoment_clog_le hn
  have h1 : 1 ≤ Real.sqrt (q + Real.log n) := Real.one_le_sqrt.2 (by linarith)
  have h2 : Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2) ≤ 2 * Real.sqrt (q + Real.log n) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith
  nlinarith

/-- The power bound used for both (4.7) and (4.8): `κ₁ ≤ Z M` with `1 ≤ Z ≤ Y` and `ρ ≤ e` give
`κ₁^ρ ≤ Y^e M^ρ`. -/
private lemma ldmoment_kappa_pow {κ₁ Z Y ρ M e : ℝ} (hκ : 0 ≤ κ₁) (h : κ₁ ≤ Z * M) (hZ : 1 ≤ Z)
    (hZY : Z ≤ Y) (hρ : 0 ≤ ρ) (hρe : ρ ≤ e) (hM : 0 ≤ M) : κ₁ ^ ρ ≤ Y ^ e * M ^ ρ := by
  have hZ0 : 0 ≤ Z := by linarith
  calc κ₁ ^ ρ ≤ (Z * M) ^ ρ := Real.rpow_le_rpow hκ h hρ
    _ = Z ^ ρ * M ^ ρ := Real.mul_rpow hZ0 hM
    _ ≤ Y ^ e * M ^ ρ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hM _)
        calc Z ^ ρ ≤ Y ^ ρ := Real.rpow_le_rpow hZ0 hZY hρ
          _ ≤ Y ^ e := Real.rpow_le_rpow_of_exponent_le (by linarith) hρe

/-- At the level `k + 1` of (M2): `t_{k+1}^q ≤ t_0^q e^{(k+1)/2}` when `2 ρ q ≤ κ₁`. -/
private lemma ldmoment_level {c S ρ q κ₁ : ℝ} (hc : 0 < c) (hS : 0 < S) (hρ : 0 < ρ)
    (hq : 0 < q) (hκ : 0 < κ₁) (hκ₁ : 2 * ρ * q ≤ κ₁) (k : ℕ) :
    (c * (κ₁ + ((k + 1 : ℕ) : ℝ)) ^ ρ * S) ^ q ≤
      (c * κ₁ ^ ρ * S) ^ q * Real.exp (((k : ℝ) + 1) / 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set u : ℝ := 1 + ((k : ℝ) + 1) / κ₁ with hu
  have hu0 : 0 ≤ u := by positivity
  have hκu : κ₁ + ((k + 1 : ℕ) : ℝ) = κ₁ * u := by
    rw [hu]; push_cast; field_simp
  rw [hκu, Real.mul_rpow hκ.le hu0]
  have e1 : c * (κ₁ ^ ρ * u ^ ρ) * S = (c * κ₁ ^ ρ * S) * u ^ ρ := by ring
  rw [e1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hu0]
  gcongr
  calc u ^ (ρ * q) ≤ Real.exp (((k : ℝ) + 1) / κ₁) ^ (ρ * q) :=
        Real.rpow_le_rpow hu0 (by have := Real.add_one_le_exp (((k : ℝ) + 1) / κ₁); linarith)
          (by positivity)
    _ = Real.exp (((k : ℝ) + 1) / κ₁ * (ρ * q)) := (Real.exp_mul _ _).symm
    _ ≤ Real.exp (((k : ℝ) + 1) / 2) := by
        apply Real.exp_le_exp.2
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hκ two_pos]
        nlinarith [mul_le_mul_of_nonneg_left hκ₁ (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1)]

/-- The pointwise decomposition of (M2): if the levels `t k` tend to `∞`, then
`x ^ q ≤ t 0 ^ q + ∑_k t (k + 1) ^ q 1(t k < x)` for `q > 0` and `x ≥ 0`. -/
private lemma ldmoment_pointwise {t : ℕ → ℝ} (htu : Tendsto t atTop atTop) {q : ℝ} (hq : 0 < q)
    {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (x ^ q) ≤ ENNReal.ofReal (t 0 ^ q) +
      ∑' k : ℕ, if t k < x then ENNReal.ofReal (t (k + 1) ^ q) else 0 := by
  by_cases h0 : x ≤ t 0
  · exact le_trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx h0 hq.le)) le_self_add
  · have h0 := not_le.1 h0
    classical
    have hex : ∃ m, x ≤ t m := (htu.eventually_ge_atTop x).exists
    have hmspec : x ≤ t (Nat.find hex) := Nat.find_spec hex
    have hm0 : Nat.find hex ≠ 0 := fun h => by
      rw [h] at hmspec; exact absurd hmspec (not_le.2 h0)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hjlt : t j < x := not_le.1 (Nat.find_min hex (show j < Nat.find hex by omega))
    rw [hj] at hmspec
    calc ENNReal.ofReal (x ^ q) ≤ ENNReal.ofReal (t (j + 1) ^ q) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx hmspec hq.le)
      _ = if t j < x then ENNReal.ofReal (t (j + 1) ^ q) else 0 := by simp [hjlt]
      _ ≤ ∑' k : ℕ, if t k < x then ENNReal.ofReal (t (k + 1) ^ q) else 0 :=
          le_tsum (fun k => if t k < x then ENNReal.ofReal (t (k + 1) ^ q) else 0) j
      _ ≤ _ := le_add_self

end LDHelpers

section LDCore

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Step 1 of Lemma 4.3 (M1 ⇒ M2) in `ℝ≥0∞`: a tail bound `P(‖G‖ > c κ^ρ S) ≤ A e^{-κ}` for
`κ ≥ κ₀` and `S > 0` gives `E ‖G‖^q ≤ (c κ₁^ρ S)^q (1 + 5 A e^{-κ₁})` for every `κ₁ ≥ κ₀` with
`κ₁ ≥ 2 ρ q`. -/
private lemma ldmoment_lintegral {G : Ω → ℂ} (hG : Measurable G) {S c ρ A κ₀ κ₁ q : ℝ}
    (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ) (hA : 0 ≤ A) (hq : 0 < q)
    (hκ₀ : κ₀ ≤ κ₁) (hκ₁ : 2 * ρ * q ≤ κ₁)
    (ht : ∀ κ, κ₀ ≤ κ → μ {ω | c * κ ^ ρ * S < ‖G ω‖} ≤ ENNReal.ofReal (A * Real.exp (-κ))) :
    ∫⁻ ω, ‖G ω‖ₑ ^ q ∂μ ≤
      ENNReal.ofReal ((c * κ₁ ^ ρ * S) ^ q * (1 + 5 * A * Real.exp (-κ₁))) := by
  have hκ1 : 0 < κ₁ := by
    have := mul_pos (mul_pos two_pos hρ) hq; linarith
  set t : ℕ → ℝ := fun k => c * (κ₁ + k) ^ ρ * S with htdef
  have htpos : ∀ k, 0 < t k := fun k => by
    have : 0 < κ₁ + (k : ℝ) := by positivity
    simp only [htdef]; positivity
  have htu : Tendsto t atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => κ₁ + (k : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ κ₁ tendsto_natCast_atTop_atTop
    exact ((tendsto_rpow_atTop hρ).comp h1 |>.const_mul_atTop hc).atTop_mul_const hS
  have hT0 : t 0 = c * κ₁ ^ ρ * S := by simp [htdef]
  have hmeas : ∀ k, MeasurableSet {ω | t k < ‖G ω‖} := fun k =>
    measurableSet_lt measurable_const hG.norm
  have hpt : ∀ ω, ‖G ω‖ₑ ^ q ≤ ENNReal.ofReal (t 0 ^ q) +
      ∑' k : ℕ, Set.indicator {ω | t k < ‖G ω‖} (fun _ => ENNReal.ofReal (t (k + 1) ^ q)) ω := by
    intro ω
    have e : ‖G ω‖ₑ ^ q = ENNReal.ofReal (‖G ω‖ ^ q) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]
    rw [e]
    refine (ldmoment_pointwise htu hq (norm_nonneg (G ω))).trans (le_of_eq ?_)
    congr 1
  have hu0 : 0 ≤ Real.exp (-(1 / 2)) := (Real.exp_pos _).le
  have hu1 : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  set K : ℝ := t 0 ^ q * A * Real.exp (-κ₁) * Real.exp (1 / 2) with hK
  have hK0 : 0 ≤ K := by
    have := htpos 0
    simp only [hK]; positivity
  have hreal : ∀ k : ℕ, t (k + 1) ^ q * (A * Real.exp (-(κ₁ + k))) ≤
      K * Real.exp (-(1 / 2)) ^ k := fun k => by
    have h1 := ldmoment_level hc hS hρ hq hκ1 hκ₁ k
    have h2 : Real.exp (((k : ℝ) + 1) / 2) * Real.exp (-(κ₁ + k)) =
        Real.exp (-κ₁) * Real.exp (1 / 2) * Real.exp (-(1 / 2)) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc t (k + 1) ^ q * (A * Real.exp (-(κ₁ + k)))
        ≤ ((c * κ₁ ^ ρ * S) ^ q * Real.exp (((k : ℝ) + 1) / 2)) *
            (A * Real.exp (-(κ₁ + k))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (c * κ₁ ^ ρ * S) ^ q * A *
            (Real.exp (((k : ℝ) + 1) / 2) * Real.exp (-(κ₁ + k))) := by ring
      _ = K * Real.exp (-(1 / 2)) ^ k := by
          rw [h2, hK, hT0]; ring
  have hsum : Summable (fun k : ℕ => K * Real.exp (-(1 / 2)) ^ k) :=
    (summable_geometric_of_lt_one hu0 hu1).mul_left K
  calc ∫⁻ ω, ‖G ω‖ₑ ^ q ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (t 0 ^ q) +
          ∑' k : ℕ, Set.indicator {ω | t k < ‖G ω‖}
            (fun _ => ENNReal.ofReal (t (k + 1) ^ q)) ω) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (t 0 ^ q) +
          ∑' k : ℕ, ENNReal.ofReal (t (k + 1) ^ q) * μ {ω | t k < ‖G ω‖} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum (fun k => (measurable_const.indicator (hmeas k)).aemeasurable)]
        congr 1
        exact tsum_congr fun k => lintegral_indicator_const (hmeas k) _
    _ ≤ ENNReal.ofReal (t 0 ^ q) +
          ∑' k : ℕ, ENNReal.ofReal (K * Real.exp (-(1 / 2)) ^ k) := by
        gcongr with k
        calc ENNReal.ofReal (t (k + 1) ^ q) * μ {ω | t k < ‖G ω‖}
            ≤ ENNReal.ofReal (t (k + 1) ^ q) * ENNReal.ofReal (A * Real.exp (-(κ₁ + k))) := by
              gcongr
              exact ht (κ₁ + k) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
          _ = ENNReal.ofReal (t (k + 1) ^ q * (A * Real.exp (-(κ₁ + k)))) :=
              (ENNReal.ofReal_mul (Real.rpow_nonneg (htpos _).le _)).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (hreal k)
    _ = ENNReal.ofReal (t 0 ^ q) + ENNReal.ofReal (K / (1 - Real.exp (-(1 / 2)))) := by
        congr 1
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum, tsum_mul_left,
          tsum_geometric_of_lt_one hu0 hu1, ← div_eq_mul_inv]
    _ ≤ ENNReal.ofReal ((c * κ₁ ^ ρ * S) ^ q * (1 + 5 * A * Real.exp (-κ₁))) := by
        have hT0q : 0 ≤ t 0 ^ q := Real.rpow_nonneg (htpos 0).le _
        have hpos : 0 < 1 - Real.exp (-(1 / 2)) := by linarith
        have hKle : K / (1 - Real.exp (-(1 / 2))) ≤ t 0 ^ q * (5 * A * Real.exp (-κ₁)) := by
          have h5 := ldmoment_geom_const
          have : K / (1 - Real.exp (-(1 / 2))) =
              t 0 ^ q * A * Real.exp (-κ₁) *
                (Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) := by
            rw [hK]; ring
          rw [this]
          have hnn : 0 ≤ t 0 ^ q * A * Real.exp (-κ₁) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h5 hnn]
        rw [← ENNReal.ofReal_add hT0q (by positivity), hT0]
        apply ENNReal.ofReal_le_ofReal
        rw [hT0] at hKle
        nlinarith

/-- Step 1 of Lemma 4.3 (M1 ⇒ M2) in the form used for (4.7) and (4.8): the tail bound
`P(‖G‖ > c κ^ρ S) ≤ A e^{-κ}` for `κ ≥ κ₀`, with `S ≥ 0`, gives `‖G‖_q ≤ (3/2) c κ₁^ρ S` for every
`κ₁ ≥ κ₀` with `κ₁ ≥ 2 ρ q` and `5 A e^{-κ₁} ≤ 1`, and every real `q ≥ 2`. For `S = 0` the tail
bound forces `G = 0` almost surely. -/
private lemma ldmoment_eLpNorm {G : Ω → ℂ} (hG : Measurable G)
    {S c ρ A κ₀ κ₁ q : ℝ}
    (hS : 0 ≤ S) (hc : 0 < c) (hρ : 0 < ρ) (hA : 0 ≤ A) (hq : 2 ≤ q)
    (hκ₀ : κ₀ ≤ κ₁) (hκ₁ : 2 * ρ * q ≤ κ₁) (hAκ : 5 * A * Real.exp (-κ₁) ≤ 1)
    (ht : ∀ κ, κ₀ ≤ κ → μ {ω | c * κ ^ ρ * S < ‖G ω‖} ≤ ENNReal.ofReal (A * Real.exp (-κ))) :
    eLpNorm G (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (3 / 2 * (c * κ₁ ^ ρ * S)) := by
  have hq0 : 0 < q := by linarith
  rcases hS.eq_or_lt with hS0 | hSpos
  · subst hS0
    have h0 : μ {ω | 0 < ‖G ω‖} = 0 := by
      refine le_antisymm ?_ bot_le
      have hlim : Tendsto (fun κ : ℝ => ENNReal.ofReal (A * Real.exp (-κ))) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul A)
        simpa using this
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop κ₀] with κ hκ
      simpa using ht κ hκ
    have h0' : μ {ω | ¬ G ω = 0} = 0 := by simpa [norm_pos_iff] using h0
    have hae : G =ᵐ[μ] 0 := by
      rw [Filter.EventuallyEq, ae_iff]; exact h0'
    rw [eLpNorm_congr_ae hae, eLpNorm_zero]
    exact bot_le
  · have hint := ldmoment_lintegral hG hSpos hc hρ hA hq0 hκ₀ hκ₁ ht
    have hκ1 : 0 < κ₁ := by
      have := mul_pos (mul_pos two_pos hρ) hq0; linarith
    set T : ℝ := c * κ₁ ^ ρ * S with hT
    have hT0 : 0 ≤ T := by simp only [hT]; positivity
    have hTq : 0 ≤ T ^ q := Real.rpow_nonneg hT0 _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne'
      ENNReal.ofReal_ne_top hG.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    have h2q : (2 : ℝ) ^ (1 / q) ≤ 3 / 2 := by
      calc (2 : ℝ) ^ (1 / q) ≤ 2 ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by rw [div_le_div_iff₀ hq0 two_pos]; linarith)
        _ = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
        _ ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    calc (∫⁻ ω, ‖G ω‖ₑ ^ q ∂μ) ^ (1 / q)
        ≤ ENNReal.ofReal (T ^ q * (1 + 5 * A * Real.exp (-κ₁))) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hint (by positivity)
      _ ≤ ENNReal.ofReal (T ^ q * 2) ^ (1 / q) := by
          refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hTq
      _ = ENNReal.ofReal ((T ^ q * 2) ^ (1 / q)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (3 / 2 * T) := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.mul_rpow hTq (by norm_num), one_div, Real.rpow_rpow_inv hT0 hq0.ne', ← one_div]
          nlinarith

end LDCore

section LDQuad

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ϑ : ℝ}
  {n : ℕ} {X : Fin n → Ω → ℂ} {s : Fin n → ℝ}

/-- The splitting of the centred quadratic form of (4.8) into its diagonal and off-diagonal
parts: `∑ X̄ i B i j X j - ∑ s i² B i i = ∑ B i i (‖X i‖² - s i²) + ∑_{i ≠ j} X̄ i B i j X j`. -/
private lemma ldmoment_quad_split (B : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (s : Fin n → ℝ) :
    ∑ i, ∑ j, starRingEnd ℂ (x i) * B i j * x j - ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i =
      ∑ i, B i i * (((‖x i‖ ^ 2 : ℝ) : ℂ) - ((s i ^ 2 : ℝ) : ℂ)) +
        ∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (x i) * B i j * x j := by
  classical
  have hpt : ∀ i j, starRingEnd ℂ (x i) * B i j * x j =
      (if i = j then B i i * ((‖x i‖ ^ 2 : ℝ) : ℂ) else 0) +
        if i = j then 0 else starRingEnd ℂ (x i) * B i j * x j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp only [↓reduceIte]
      rw [mul_assoc, mul_comm (B i i), ← mul_assoc, Complex.conj_mul']
      push_cast; ring
    · simp [h]
  have hdiag : ∑ i, ∑ j, (if i = j then B i i * ((‖x i‖ ^ 2 : ℝ) : ℂ) else 0) =
      ∑ i, B i i * ((‖x i‖ ^ 2 : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun i _ => by simp
  calc ∑ i, ∑ j, starRingEnd ℂ (x i) * B i j * x j - ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i
      = ∑ i, ∑ j, ((if i = j then B i i * ((‖x i‖ ^ 2 : ℝ) : ℂ) else 0) +
          if i = j then 0 else starRingEnd ℂ (x i) * B i j * x j) -
          ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i :=
        by simp only [← hpt]
    _ = _ := by
        simp only [Finset.sum_add_distrib, hdiag]
        rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The tail bound for the centred quadratic form in the shape (M1) of Step 3 of Lemma 4.3: for
`κ ≥ κ_ϑ + log n`, the form exceeds `C_n κ^{2ϑ⁻¹ + 1} S_B` with probability at most
`25 n³ ϑ⁻¹ e^{-κ}`, where `C_n = 25 (1 + √(2 ⌈log₂ n⌉ + 2))`. It combines (4.4) for the diagonal
part with (4.5) for the off-diagonal part. -/
private lemma ldmoment_quad_tail (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℂ) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | 25 * (1 + Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) * κ ^ (2 * ϑ⁻¹ + 1) *
        Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) <
        ‖∑ i, ∑ j, starRingEnd ℂ (X i ω) * B i j * X j ω -
          ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i‖} ≤
      ENNReal.ofReal (25 * (n : ℝ) ^ 3 * ϑ⁻¹ * Real.exp (-κ)) := by
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hN
  have hκ0 : 0 < κ := by
    have := ldmoment_kappa_ge ha1
    have := Real.log_nonneg ha1
    linarith
  have hsn : ∀ i, 0 ≤ s i := hX.nonneg
  set SB : ℝ := Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) with hSB
  set Sd : ℝ := Real.sqrt (∑ i, ‖B i i‖ ^ 2 * s i ^ 4) with hSd
  set So : ℝ := Real.sqrt (∑ i, ∑ j, if i = j then 0 else s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2)
    with hSo
  have hnn : ∀ i j, 0 ≤ s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2 := fun i j => by positivity
  have hSd_le : Sd ≤ SB := by
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖B i i‖ ^ 2 * s i ^ 4 = s i ^ 2 * ‖B i i‖ ^ 2 * s i ^ 2 := by ring
      _ ≤ ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2 :=
        Finset.single_le_sum (f := fun j => s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2)
          (fun j _ => hnn i j) (Finset.mem_univ i)
  have hSo_le : So ≤ SB := by
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact hnn i j
    · exact le_rfl
  set ℓ : ℝ := lossL ϑ⁻¹ κ with hℓ
  have hsq : ℓ ^ 2 = 25 * κ ^ (2 * ϑ⁻¹ + 1) := by
    have h : (κ ^ (ϑ⁻¹ + 1 / 2)) ^ 2 = κ ^ (2 * ϑ⁻¹ + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ0.le]
      congr 1; push_cast; ring
    simp only [hℓ, lossL]
    rw [mul_pow, h]; norm_num
  have hℓ2 : lossL2 ϑ⁻¹ κ n / 2 = ℓ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2) := by
    simp only [lossL2, hℓ]; ring
  have hℓ2nn : 0 ≤ lossL2 ϑ⁻¹ κ n / 2 := by rw [hℓ2]; positivity
  have hcn : 25 * (1 + Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) * κ ^ (2 * ϑ⁻¹ + 1) =
      ℓ ^ 2 + lossL2 ϑ⁻¹ κ n / 2 := by
    rw [hℓ2, hsq]; ring
  have hd : μ {ω | ℓ ^ 2 * Sd <
        ‖∑ i, B i i * (((‖X i ω‖ ^ 2 : ℝ) : ℂ) - ((s i ^ 2 : ℝ) : ℂ))‖} ≤
      ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) :=
    ld_diag hX hϑ hϑ1 hn (fun i => B i i) hκ
  have ho : μ {ω | lossL2 ϑ⁻¹ κ n / 2 * So <
        ‖∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω‖} ≤
      ENNReal.ofReal (20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) / ϑ * Real.exp (-κ)) :=
    ld_offdiag hX hϑ hϑ1 hn B hκ
  have hsub : {ω | 25 * (1 + Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) * κ ^ (2 * ϑ⁻¹ + 1) * SB <
        ‖∑ i, ∑ j, starRingEnd ℂ (X i ω) * B i j * X j ω -
          ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i‖} ⊆
      {ω | ℓ ^ 2 * Sd <
        ‖∑ i, B i i * (((‖X i ω‖ ^ 2 : ℝ) : ℂ) - ((s i ^ 2 : ℝ) : ℂ))‖} ∪
      {ω | lossL2 ϑ⁻¹ κ n / 2 * So <
        ‖∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω‖} := by
    intro ω hω
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    obtain ⟨h1, h2⟩ := hnot
    have h1' : ‖∑ i, B i i * (((‖X i ω‖ ^ 2 : ℝ) : ℂ) - ((s i ^ 2 : ℝ) : ℂ))‖ ≤ ℓ ^ 2 * Sd :=
      not_lt.1 h1
    have h2' : ‖∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω‖ ≤
        lossL2 ϑ⁻¹ κ n / 2 * So := not_lt.1 h2
    have hω' := hω
    have hsplit : ∑ i, ∑ j, starRingEnd ℂ (X i ω) * B i j * X j ω -
          ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i =
        ∑ i, B i i * (((‖X i ω‖ ^ 2 : ℝ) : ℂ) - ((s i ^ 2 : ℝ) : ℂ)) +
          ∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω :=
      ldmoment_quad_split B (fun i => X i ω) s
    simp only [Set.mem_ofPred_eq] at hω'
    rw [hsplit] at hω'
    have h3 := norm_add_le (∑ i, B i i * (((‖X i ω‖ ^ 2 : ℝ) : ℂ) - ((s i ^ 2 : ℝ) : ℂ)))
      (∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω)
    have h4 : ℓ ^ 2 * Sd + lossL2 ϑ⁻¹ κ n / 2 * So ≤ (ℓ ^ 2 + lossL2 ϑ⁻¹ κ n / 2) * SB := by
      nlinarith [mul_le_mul_of_nonneg_left hSd_le (sq_nonneg ℓ),
        mul_le_mul_of_nonneg_left hSo_le hℓ2nn]
    rw [hcn] at hω'
    linarith
  have hN3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) (by nlinarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1)]
  have hD' : (Nat.clog 2 (2 * n) : ℝ) ≤ n := by exact_mod_cast ldmoment_clog_two_mul_le hn
  have hsum : (4 + n / ϑ) * Real.exp (-κ) +
      20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) / ϑ * Real.exp (-κ) ≤
      25 * (n : ℝ) ^ 3 * ϑ⁻¹ * Real.exp (-κ) := by
    rw [div_eq_mul_inv (n : ℝ) ϑ, div_eq_mul_inv (20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ)) ϑ]
    have h1 : 1 ≤ (n : ℝ) ^ 3 := one_le_pow₀ hN
    have h4 : 4 ≤ 4 * (n : ℝ) ^ 3 * ϑ⁻¹ := by
      nlinarith [mul_le_mul h1 ha1 zero_le_one (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]
    have h5 : (n : ℝ) * ϑ⁻¹ ≤ (n : ℝ) ^ 3 * ϑ⁻¹ :=
      mul_le_mul_of_nonneg_right hN3 (by linarith)
    have h6 : 20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) * ϑ⁻¹ ≤ 20 * (n : ℝ) ^ 3 * ϑ⁻¹ := by
      have : (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) ≤ (n : ℝ) ^ 2 * n :=
        mul_le_mul_of_nonneg_left hD' (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ ϑ⁻¹)]
    have : 4 + (n : ℝ) * ϑ⁻¹ + 20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) * ϑ⁻¹ ≤
        25 * (n : ℝ) ^ 3 * ϑ⁻¹ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (Real.exp_pos (-κ)).le]
  calc μ {ω | 25 * (1 + Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) * κ ^ (2 * ϑ⁻¹ + 1) * SB <
        ‖∑ i, ∑ j, starRingEnd ℂ (X i ω) * B i j * X j ω -
          ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i‖}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ)) +
        ENNReal.ofReal (20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) / ϑ * Real.exp (-κ)) :=
        add_le_add hd ho
    _ = ENNReal.ofReal ((4 + n / ϑ) * Real.exp (-κ) +
        20 * (n : ℝ) ^ 2 * (Nat.clog 2 (2 * n) : ℝ) / ϑ * Real.exp (-κ)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

end LDQuad

section LD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ϑ : ℝ}
  {n : ℕ} {X : Fin n → Ω → ℂ} {s : Fin n → ℝ}

/-- `C_LD = 150 (4a + 2 + κ_ϑ)^{2a+1}` of Lemma 4.3. -/
noncomputable def cLD (a : ℝ) : ℝ := 150 * (4 * a + 2 + kappaTheta a) ^ (2 * a + 1)

/-- Lemma 4.3, (4.7): moments of linear forms. -/
theorem ldm_linear (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n) {q : ℝ}
    (hq : 2 ≤ q) (a : Fin n → ℂ) :
    eLpNorm (fun ω => ∑ i, a i * X i ω) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (cLD ϑ⁻¹ * (q + Real.log n) ^ (ϑ⁻¹ + 1 / 2) *
        Real.sqrt (∑ i, ‖a i‖ ^ 2 * s i ^ 2)) := by
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hN
  have hκθ := ldmoment_kappa_nonneg ha1
  set S : ℝ := Real.sqrt (∑ i, ‖a i‖ ^ 2 * s i ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hρ : 0 < ϑ⁻¹ + 1 / 2 := by linarith
  have hq0 : 0 ≤ 2 * (ϑ⁻¹ + 1 / 2) * q := by
    have : 0 ≤ q := by linarith
    positivity
  set κ₁ : ℝ := 2 * (ϑ⁻¹ + 1 / 2) * q + 1 * Real.log n + kappaTheta ϑ⁻¹ with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := by rw [hκ₁]; linarith
  have hmeas : Measurable (fun ω => ∑ i, a i * X i ω) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (hX.meas i)
  have hexp := ldmoment_exp_bound ha1 hn hq0 1
  simp only [Nat.cast_one, pow_one] at hexp
  have hAκ : 5 * (4 + n / ϑ) * Real.exp (-κ₁) ≤ 1 := by
    have h1 : 1 ≤ (n : ℝ) * ϑ⁻¹ := one_le_mul_of_one_le_of_one_le hN ha1
    have h2 : 4 + (n : ℝ) / ϑ ≤ 5 * ((n : ℝ) * ϑ⁻¹) := by rw [div_eq_mul_inv]; linarith
    calc 5 * (4 + (n : ℝ) / ϑ) * Real.exp (-κ₁)
        ≤ 5 * (5 * ((n : ℝ) * ϑ⁻¹)) * Real.exp (-κ₁) := by gcongr
      _ = 25 * ((n : ℝ) * ϑ⁻¹ * Real.exp (-κ₁)) := by ring
      _ ≤ 25 * (1 / 256) := by gcongr
      _ ≤ 1 := by norm_num
  have hcore := ldmoment_eLpNorm (μ := μ) hmeas (S := S) (c := 5) (ρ := ϑ⁻¹ + 1 / 2)
    (A := 4 + n / ϑ) (κ₀ := kappaTheta ϑ⁻¹ + Real.log n) (κ₁ := κ₁) (q := q) hS0
    (by norm_num) hρ (by positivity) hq (by rw [hκ₁]; linarith) (by rw [hκ₁]; linarith) hAκ
    (fun κ hκ => ld_linear hX hϑ hϑ1 hn a hκ)
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hM0 : 0 ≤ q + Real.log n := by linarith
  have hκ1le : κ₁ ≤ (2 * ϑ⁻¹ + 1 + kappaTheta ϑ⁻¹) * (q + Real.log n) := by
    rw [hκ₁]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ϑ⁻¹) hL,
      mul_nonneg hκθ (by linarith : (0 : ℝ) ≤ q - 1), mul_nonneg hκθ hL]
  have hpow := ldmoment_kappa_pow (κ₁ := κ₁) (Z := 2 * ϑ⁻¹ + 1 + kappaTheta ϑ⁻¹)
    (Y := 4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹) (ρ := ϑ⁻¹ + 1 / 2) (M := q + Real.log n)
    (e := 2 * ϑ⁻¹ + 1) hκ₁0 hκ1le (by linarith) (by linarith) hρ.le (by linarith) hM0
  have hP : 0 ≤ (4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹) ^ (2 * ϑ⁻¹ + 1) *
      (q + Real.log n) ^ (ϑ⁻¹ + 1 / 2) * S :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hM0 _)) hS0
  unfold cLD
  nlinarith [mul_le_mul_of_nonneg_right hpow hS0]

/-- Lemma 4.3, (4.8): moments of centred quadratic forms. -/
theorem ldm_quad (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n) {q : ℝ}
    (hq : 2 ≤ q) (B : Matrix (Fin n) (Fin n) ℂ) :
    eLpNorm (fun ω => ∑ i, ∑ j, starRingEnd ℂ (X i ω) * B i j * X j ω -
        ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (cLD ϑ⁻¹ * (q + Real.log n) ^ (2 * ϑ⁻¹ + 3 / 2) *
        Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2)) := by
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hN
  have hκθ := ldmoment_kappa_nonneg ha1
  set SB : ℝ := Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) with hSB
  have hSB0 : 0 ≤ SB := Real.sqrt_nonneg _
  set cn : ℝ := 25 * (1 + Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) with hcn
  have hcn0 : 0 < cn := by rw [hcn]; positivity
  have hρ : 0 < 2 * ϑ⁻¹ + 1 := by linarith
  have hq0 : 0 ≤ 2 * (2 * ϑ⁻¹ + 1) * q := by
    have : 0 ≤ q := by linarith
    positivity
  set κ₁ : ℝ := 2 * (2 * ϑ⁻¹ + 1) * q + 3 * Real.log n + kappaTheta ϑ⁻¹ with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := by rw [hκ₁]; linarith
  have hmeas : Measurable (fun ω => ∑ i, ∑ j, starRingEnd ℂ (X i ω) * B i j * X j ω -
        ∑ i, ((s i ^ 2 : ℝ) : ℂ) * B i i) := by
    refine Measurable.sub ?_ measurable_const
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact ((Complex.continuous_conj.measurable.comp (hX.meas i)).mul_const _).mul (hX.meas j)
  have hexp := ldmoment_exp_bound ha1 hn hq0 3
  simp only [Nat.cast_ofNat] at hexp
  have hAκ : 5 * (25 * (n : ℝ) ^ 3 * ϑ⁻¹) * Real.exp (-κ₁) ≤ 1 := by
    calc 5 * (25 * (n : ℝ) ^ 3 * ϑ⁻¹) * Real.exp (-κ₁)
        = 125 * ((n : ℝ) ^ 3 * ϑ⁻¹ * Real.exp (-κ₁)) := by ring
      _ ≤ 125 * (1 / 256) := by gcongr
      _ ≤ 1 := by norm_num
  have hcore := ldmoment_eLpNorm (μ := μ) hmeas (S := SB) (c := cn) (ρ := 2 * ϑ⁻¹ + 1)
    (A := 25 * (n : ℝ) ^ 3 * ϑ⁻¹) (κ₀ := kappaTheta ϑ⁻¹ + Real.log n) (κ₁ := κ₁) (q := q)
    hSB0 hcn0 hρ (by positivity) hq (by rw [hκ₁]; linarith) (by rw [hκ₁]; linarith) hAκ
    (fun κ hκ => ldmoment_quad_tail hX hϑ hϑ1 hn B hκ)
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hM0 : 0 < q + Real.log n := by linarith
  have hκ1le : κ₁ ≤ (4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹) * (q + Real.log n) := by
    rw [hκ₁]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ϑ⁻¹ - 1) hL,
      mul_nonneg hκθ (by linarith : (0 : ℝ) ≤ q - 1), mul_nonneg hκθ hL]
  have hpow := ldmoment_kappa_pow (κ₁ := κ₁) (Z := 4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹)
    (Y := 4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹) (ρ := 2 * ϑ⁻¹ + 1) (M := q + Real.log n)
    (e := 2 * ϑ⁻¹ + 1) hκ₁0 hκ1le (by linarith) le_rfl hρ.le le_rfl hM0.le
  have hcnle : cn ≤ 75 * Real.sqrt (q + Real.log n) := ldmoment_cn_le hn hq
  have hM : (q + Real.log n) ^ (2 * ϑ⁻¹ + 3 / 2) =
      (q + Real.log n) ^ (2 * ϑ⁻¹ + 1) * Real.sqrt (q + Real.log n) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hM0]
    congr 1; ring
  have h1 : cn * κ₁ ^ (2 * ϑ⁻¹ + 1) ≤
      (75 * Real.sqrt (q + Real.log n)) *
        ((4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹) ^ (2 * ϑ⁻¹ + 1) * (q + Real.log n) ^ (2 * ϑ⁻¹ + 1)) :=
    mul_le_mul hcnle hpow (Real.rpow_nonneg hκ₁0 _) (by positivity)
  have hP : 0 ≤ Real.sqrt (q + Real.log n) *
      ((4 * ϑ⁻¹ + 2 + kappaTheta ϑ⁻¹) ^ (2 * ϑ⁻¹ + 1) * (q + Real.log n) ^ (2 * ϑ⁻¹ + 1)) *
        SB :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hM0.le _))) hSB0
  rw [hM]
  unfold cLD
  nlinarith [mul_le_mul_of_nonneg_right h1 hSB0]

end LD

end Rigidity
