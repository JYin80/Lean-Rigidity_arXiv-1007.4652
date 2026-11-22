module

public import Rigidity.Flow.Chamber
public import Rigidity.LogGas.TwoPoint

@[expose] public section

/-!
# Log-gases on the Weyl chamber

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The file defines the Hamiltonian `logGasH` `𝓥 = 𝓥₀ - β ∑_{i<j} log(x_j - x_i)`, the log-gas
`logGasMeasure` `ω = Z⁻¹ e^{-𝓥} 𝟙_Σ dx` on the chamber `Σ`, and the structure `IsConvexLogGas` of
convex log-gases (Definition 17.2): `β ≥ 1`, `κ ≥ 0`, `𝓥₀` continuous and `κ`-convex, and
`Z < ∞`.  It proves Lemma 17.3:
* (a) `logGasH_kconvex`: `𝓥` is `κ`-convex on the chamber;
* (b) `logGasH_midpoint`: the pair inequality with the two-point function `Λ` (`logCoshRatio`);
* (c) `lintegral_logGas_lt_top`: for `κ > 0` and `β ≥ 0` the partition function is finite.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `𝓥(x) = 𝓥₀(x) - β ∑_{i<j} log(x_j - x_i)` (Definition 17.2). -/
noncomputable def logGasH {N : ℕ} (β : ℝ) (V₀ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  V₀ x - β * ∑ p : {q : Fin N × Fin N // q.1 < q.2}, Real.log (x p.1.2 - x p.1.1)

/-- The log-gas `ω = Z⁻¹ e^{-𝓥} 𝟙_Σ dx` (Definition 17.2). -/
noncomputable def logGasMeasure {N : ℕ} (β : ℝ) (V₀ : (Fin N → ℝ) → ℝ) : Measure (Fin N → ℝ) :=
  (∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)))⁻¹ •
    (volume.restrict (chamber N)).withDensity fun x => ENNReal.ofReal (Real.exp (-logGasH β V₀ x))

/-- Definition 17.2: `(β, κ, 𝓥₀)` define a convex log-gas. -/
structure IsConvexLogGas (N : ℕ) (β κ : ℝ) (V₀ : (Fin N → ℝ) → ℝ) : Prop where
  one_le_beta : 1 ≤ β
  kappa_nonneg : 0 ≤ κ
  cont : Continuous V₀
  kconvex : ∀ x y : Fin N → ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
    κ / 2 * τ * (1 - τ) * ∑ i, (x i - y i) ^ 2 ≤ τ * V₀ x + (1 - τ) * V₀ y - V₀ (τ • x + (1 - τ) • y)
  finite : ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) < ∞

/-- For `a, b > 0` and `τ ∈ [0, 1]`, `τ log a + (1 - τ) log b ≤ log (τ a + (1 - τ) b)`
(concavity of `log`, Lemma 17.3). -/
private theorem logGas_log_concave {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    τ * Real.log a + (1 - τ) * Real.log b ≤ Real.log (τ * a + (1 - τ) * b) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb) hτ.1
    (sub_nonneg.2 hτ.2) (add_sub_cancel τ 1)
  simpa [smul_eq_mul] using h

/-- The decomposition of `τ 𝓥(x) + (1 - τ) 𝓥(y) - 𝓥(τ x + (1 - τ) y)` into the `𝓥₀` part and
the logarithmic part, as in the proof of Lemma 17.3. -/
private theorem logGasH_convex_comb {N : ℕ} (β : ℝ) (V₀ : (Fin N → ℝ) → ℝ)
    (x y : Fin N → ℝ) (τ : ℝ) :
    τ * logGasH β V₀ x + (1 - τ) * logGasH β V₀ y - logGasH β V₀ (τ • x + (1 - τ) • y) =
      (τ * V₀ x + (1 - τ) * V₀ y - V₀ (τ • x + (1 - τ) • y)) +
        β * ∑ p : {q : Fin N × Fin N // q.1 < q.2},
          (Real.log (τ * (x p.1.2 - x p.1.1) + (1 - τ) * (y p.1.2 - y p.1.1))
            - τ * Real.log (x p.1.2 - x p.1.1) - (1 - τ) * Real.log (y p.1.2 - y p.1.1)) := by
  have hz : ∀ p : {q : Fin N × Fin N // q.1 < q.2},
      (τ • x + (1 - τ) • y) p.1.2 - (τ • x + (1 - τ) • y) p.1.1 =
        τ * (x p.1.2 - x p.1.1) + (1 - τ) * (y p.1.2 - y p.1.1) := by
    intro p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold logGasH
  simp_rw [hz]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Lemma 17.3 (a): the `κ`-convexity inequality for `𝓥` on the chamber. -/
theorem logGasH_kconvex {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ} (h : IsConvexLogGas N β κ V₀)
    {x y : Fin N → ℝ} (hx : x ∈ chamber N) (hy : y ∈ chamber N) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    κ / 2 * τ * (1 - τ) * ∑ i, (x i - y i) ^ 2 ≤
      τ * logGasH β V₀ x + (1 - τ) * logGasH β V₀ y - logGasH β V₀ (τ • x + (1 - τ) • y) := by
  have hid := logGasH_convex_comb β V₀ x y τ
  have hβ : 0 ≤ β := by linarith [h.one_le_beta]
  have hsum : 0 ≤ ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      (Real.log (τ * (x p.1.2 - x p.1.1) + (1 - τ) * (y p.1.2 - y p.1.1))
        - τ * Real.log (x p.1.2 - x p.1.1) - (1 - τ) * Real.log (y p.1.2 - y p.1.1)) :=
    Finset.sum_nonneg fun p _ => by
      linarith [logGas_log_concave (sub_pos.2 (hx p.2)) (sub_pos.2 (hy p.2)) hτ]
  linarith [h.kconvex x y τ hτ, mul_nonneg hβ hsum]

/-- For `a, b > 0`, `Λ(a/b) = log((a + b)/2) - (log a + log b)/2` (17.2). -/
private theorem logCoshRatio_div_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logCoshRatio (a / b) =
      Real.log (1 / 2 * a + (1 - 1 / 2) * b) - 1 / 2 * Real.log a - (1 - 1 / 2) * Real.log b := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have ha2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hb2 : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have harg : (1 + a / b) / (2 * Real.sqrt (a / b)) =
      (1 / 2 * a + (1 - 1 / 2) * b) / (Real.sqrt a * Real.sqrt b) := by
    rw [Real.sqrt_div ha.le]
    field_simp
    nlinarith [ha2, hb2]
  unfold logCoshRatio
  rw [harg, Real.log_div (by positivity) (by positivity),
    Real.log_mul hsa.ne' hsb.ne', Real.log_sqrt ha.le, Real.log_sqrt hb.le]
  ring

/-- Lemma 17.3 (b): the pair inequality from the logarithmic interaction. -/
theorem logGasH_midpoint {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ} (h : IsConvexLogGas N β κ V₀)
    {x y : Fin N → ℝ} (hx : x ∈ chamber N) (hy : y ∈ chamber N) :
    2 * β * ∑ p : {q : Fin N × Fin N // q.1 < q.2},
        logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) ≤
      logGasH β V₀ x + logGasH β V₀ y - 2 * logGasH β V₀ ((1 / 2 : ℝ) • (x + y)) := by
  have hz : (1 / 2 : ℝ) • (x + y) = (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hid := logGasH_convex_comb β V₀ x y (1 / 2)
  rw [← hz] at hid
  have hβ : 0 ≤ β := by linarith [h.one_le_beta]
  have hΛ : ∑ p : {q : Fin N × Fin N // q.1 < q.2},
        logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) =
      ∑ p : {q : Fin N × Fin N // q.1 < q.2},
        (Real.log (1 / 2 * (x p.1.2 - x p.1.1) + (1 - 1 / 2) * (y p.1.2 - y p.1.1))
          - 1 / 2 * Real.log (x p.1.2 - x p.1.1) - (1 - 1 / 2) * Real.log (y p.1.2 - y p.1.1)) :=
    Finset.sum_congr rfl fun p _ => logCoshRatio_div_eq (sub_pos.2 (hx p.2)) (sub_pos.2 (hy p.2))
  have hk := h.kconvex x y (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [← hz] at hk
  have hsq : 0 ≤ κ / 2 * (1 / 2) * (1 - 1 / 2) * ∑ i, (x i - y i) ^ 2 :=
    mul_nonneg (by have := h.kappa_nonneg; positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hΛ]
  linarith [hid, hk, hsq]

/-- The closed Euclidean unit ball of `ℝ^N` is compact. -/
private theorem logGas_isCompact_ball (N : ℕ) :
    IsCompact {e : Fin N → ℝ | ∑ i, (e i) ^ 2 ≤ 1} := by
  have hcl : IsClosed {e : Fin N → ℝ | ∑ i, (e i) ^ 2 ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const
  refine (isCompact_closedBall (0 : Fin N → ℝ) 1).of_isClosed_subset hcl fun e he => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : (e i) ^ 2 ≤ ∑ j, (e j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (e j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : |e i| ≤ 1 := by
    have := Real.abs_le_sqrt (h1.trans he)
    simpa using this
  simpa using h2

/-- Quadratic lower bound for a continuous `κ`-convex function (Lemma 17.3 (c)):
`𝓥₀(x) ≥ (κ/2) |x|² - c |x| - C` with `|x|² = ∑ x_i²`. -/
private theorem logGas_V0_lower {N : ℕ} {κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ} (hκ : 0 ≤ κ)
    (hc : Continuous V₀)
    (hconv : ∀ x y : Fin N → ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, κ / 2 * τ * (1 - τ) *
      ∑ i, (x i - y i) ^ 2 ≤ τ * V₀ x + (1 - τ) * V₀ y - V₀ (τ • x + (1 - τ) • y)) :
    ∃ c C : ℝ, 0 ≤ c ∧ 0 ≤ C ∧ ∀ x : Fin N → ℝ,
      κ / 2 * (∑ i, (x i) ^ 2) - c * Real.sqrt (∑ i, (x i) ^ 2) - C ≤ V₀ x := by
  obtain ⟨B, hB⟩ := (logGas_isCompact_ball N).exists_bound_of_continuousOn hc.continuousOn
  have h0mem : (0 : Fin N → ℝ) ∈ {e : Fin N → ℝ | ∑ i, (e i) ^ 2 ≤ 1} := by simp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 h0mem)
  refine ⟨κ / 2 + B + |V₀ 0|, B + κ / 2, by positivity, by positivity, fun x => ?_⟩
  set q : ℝ := ∑ i, (x i) ^ 2 with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  set ρ : ℝ := Real.sqrt q with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρq : ρ ^ 2 = q := Real.sq_sqrt hq0
  rcases le_or_gt q 1 with hq1 | hq1
  · have hxB : ‖V₀ x‖ ≤ B := hB x hq1
    have hV : -B ≤ V₀ x := by
      have := neg_abs_le (V₀ x)
      rw [Real.norm_eq_abs] at hxB
      linarith
    have hρ1 : ρ ≤ 1 := by
      rw [hρ]
      exact Real.sqrt_le_one.2 hq1
    have hcρ : 0 ≤ (κ / 2 + B + |V₀ 0|) * ρ := by positivity
    have hκq : κ / 2 * q ≤ κ / 2 * 1 := mul_le_mul_of_nonneg_left hq1 (by positivity)
    linarith
  · have hρ1 : 1 < ρ := by
      rw [hρ]
      exact Real.lt_sqrt_of_sq_lt (by simpa using hq1)
    have hρpos : 0 < ρ := by linarith
    set τ : ℝ := ρ⁻¹ with hτ
    have hτρ : τ * ρ = 1 := inv_mul_cancel₀ hρpos.ne'
    have hτ0 : 0 < τ := inv_pos.2 hρpos
    have hτ1 : τ ≤ 1 := inv_le_one_of_one_le₀ hρ1.le
    have hτmem : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨hτ0.le, hτ1⟩
    have hk := hconv x 0 τ hτmem
    have hsm : τ • x + (1 - τ) • (0 : Fin N → ℝ) = τ • x := by simp
    rw [hsm] at hk
    have hsq0 : ∑ i, (x i - (0 : Fin N → ℝ) i) ^ 2 = q := by simp [hq]
    rw [hsq0] at hk
    have he : τ • x ∈ {e : Fin N → ℝ | ∑ i, (e i) ^ 2 ≤ 1} := by
      change ∑ i, ((τ • x) i) ^ 2 ≤ 1
      have : ∑ i, ((τ • x) i) ^ 2 = τ ^ 2 * q := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, hq, Finset.mul_sum]
      rw [this, ← hρq]
      have : τ ^ 2 * ρ ^ 2 = 1 := by rw [← mul_pow, hτρ, one_pow]
      exact this.le
    have heB : ‖V₀ (τ • x)‖ ≤ B := hB _ he
    rw [Real.norm_eq_abs] at heB
    have heB' : -B ≤ V₀ (τ • x) := by linarith [neg_abs_le (V₀ (τ • x))]
    have h0B : (1 - τ) * V₀ 0 ≤ |V₀ 0| := by
      calc (1 - τ) * V₀ 0 ≤ |(1 - τ) * V₀ 0| := le_abs_self _
        _ = (1 - τ) * |V₀ 0| := by rw [abs_mul, abs_of_nonneg (by linarith)]
        _ ≤ 1 * |V₀ 0| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = |V₀ 0| := one_mul _
    -- multiply `hk` by `ρ`
    have hk2 : κ / 2 * (1 - τ) * q ≤ V₀ x + ρ * ((1 - τ) * V₀ 0) - ρ * V₀ (τ • x) := by
      have := mul_le_mul_of_nonneg_left hk hρ0
      have e1 : ρ * (κ / 2 * τ * (1 - τ) * q) = κ / 2 * (1 - τ) * q := by
        calc ρ * (κ / 2 * τ * (1 - τ) * q) = (τ * ρ) * (κ / 2 * (1 - τ) * q) := by ring
          _ = _ := by rw [hτρ, one_mul]
      have e2 : ρ * (τ * V₀ x + (1 - τ) * V₀ 0 - V₀ (τ • x)) =
          V₀ x + ρ * ((1 - τ) * V₀ 0) - ρ * V₀ (τ • x) := by
        calc ρ * (τ * V₀ x + (1 - τ) * V₀ 0 - V₀ (τ • x))
            = (τ * ρ) * V₀ x + ρ * ((1 - τ) * V₀ 0) - ρ * V₀ (τ • x) := by ring
          _ = _ := by rw [hτρ, one_mul]
      rw [e1, e2] at this
      exact this
    have e3 : (1 - τ) * q = q - ρ := by
      calc (1 - τ) * q = q - τ * ρ ^ 2 := by rw [← hρq]; ring
        _ = q - ρ := by rw [pow_two, ← mul_assoc, hτρ, one_mul]
    have h4 : ρ * ((1 - τ) * V₀ 0) ≤ ρ * |V₀ 0| := mul_le_mul_of_nonneg_left h0B hρ0
    have h5 : ρ * (-B) ≤ ρ * V₀ (τ • x) := mul_le_mul_of_nonneg_left heB' hρ0
    have h6 : κ / 2 * (1 - τ) * q = κ / 2 * (q - ρ) := by rw [mul_assoc, e3]
    have hBC : 0 ≤ B + κ / 2 := by positivity
    nlinarith [h4, h5, h6, hk2]

/-- Lemma 17.3 (c): `Z < ∞` is automatic for `κ > 0`. -/
theorem lintegral_logGas_lt_top {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ} (hβ : 0 ≤ β)
    (hκ : 0 < κ) (hc : Continuous V₀)
    (hconv : ∀ x y : Fin N → ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, κ / 2 * τ * (1 - τ) *
      ∑ i, (x i - y i) ^ 2 ≤ τ * V₀ x + (1 - τ) * V₀ y - V₀ (τ • x + (1 - τ) • y)) :
    ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) < ∞ := by
  obtain ⟨c, C, hc0, hC0, hlow⟩ := logGas_V0_lower hκ.le hc hconv
  set K : ℝ := (Fintype.card {q : Fin N × Fin N // q.1 < q.2} : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  set c₄ : ℝ := c + 2 * β * K with hc₄
  have hc₄0 : 0 ≤ c₄ := by positivity
  set D : ℝ := C + c₄ ^ 2 / κ with hD
  -- pointwise bound on the chamber
  have hbound : ∀ x ∈ chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) ≤
      ENNReal.ofReal (Real.exp D * ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2)) := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    set q : ℝ := ∑ i, (x i) ^ 2 with hq
    have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
    set ρ : ℝ := Real.sqrt q with hρ
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρq : ρ ^ 2 = q := Real.sq_sqrt hq0
    have habs : ∀ i, |x i| ≤ ρ := fun i => by
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hlog : ∑ p : {q : Fin N × Fin N // q.1 < q.2}, Real.log (x p.1.2 - x p.1.1) ≤
        K * (2 * ρ) := by
      have h1 : ∑ p : {q : Fin N × Fin N // q.1 < q.2}, Real.log (x p.1.2 - x p.1.1) ≤
          (Finset.univ : Finset {q : Fin N × Fin N // q.1 < q.2}).card • (2 * ρ) :=
        Finset.sum_le_card_nsmul _ _ _ fun p _ => by
          have hd : 0 < x p.1.2 - x p.1.1 := sub_pos.2 (hx p.2)
          have h2 : x p.1.2 - x p.1.1 ≤ 2 * ρ := by
            have := habs p.1.2
            have := habs p.1.1
            have := le_abs_self (x p.1.2)
            have := neg_abs_le (x p.1.1)
            linarith
          exact (Real.log_le_self hd.le).trans h2
      simpa [hK, nsmul_eq_mul] using h1
    have hH : -logGasH β V₀ x ≤ -V₀ x + β * (K * (2 * ρ)) := by
      unfold logGasH
      linarith [mul_le_mul_of_nonneg_left hlog hβ]
    have hlow' := hlow x
    have hamgm : c₄ * ρ ≤ κ / 4 * ρ ^ 2 + c₄ ^ 2 / κ := by
      have h1 : 0 ≤ (κ * ρ / 2 - c₄) ^ 2 := sq_nonneg _
      have h2 : 0 ≤ (κ * ρ / 2 - c₄) ^ 2 / κ := div_nonneg h1 hκ.le
      have h3 : (κ * ρ / 2 - c₄) ^ 2 / κ = κ / 4 * ρ ^ 2 - c₄ * ρ + c₄ ^ 2 / κ := by
        field_simp
        ring
      linarith
    have hexp : -logGasH β V₀ x ≤ D + -(κ / 4) * q := by
      have hβK : β * (K * (2 * ρ)) = 2 * β * K * ρ := by ring
      have hcc : c * ρ + 2 * β * K * ρ = c₄ * ρ := by rw [hc₄]; ring
      have hκρ : κ / 4 * ρ ^ 2 = κ / 4 * q := by rw [hρq]
      have hκq : -(κ / 4) * q = -(κ / 4 * q) := by ring
      rw [hκq]
      linarith [hH, hlow', hamgm, hcc, hβK, hκρ]
    calc Real.exp (-logGasH β V₀ x) ≤ Real.exp (D + -(κ / 4) * q) := Real.exp_le_exp.2 hexp
      _ = Real.exp D * ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2) := by
        rw [Real.exp_add, ← Real.exp_sum, hq, Finset.mul_sum]
  have hmono : ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) ≤
      ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp D * ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2)) :=
    setLIntegral_mono' (isOpen_chamber N).measurableSet hbound
  have hle : ∫⁻ x in chamber N,
      ENNReal.ofReal (Real.exp D * ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2)) ≤
      ∫⁻ x : Fin N → ℝ, ENNReal.ofReal (Real.exp D * ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2)) :=
    setLIntegral_le_lintegral _ _
  have hint : Integrable (fun x : Fin N → ℝ => ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2))
      (Measure.pi fun _ : Fin N => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (f := fun (_ : Fin N) (t : ℝ) => Real.exp (-(κ / 4) * t ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by positivity)
  have hfin : ∫⁻ x : Fin N → ℝ,
      ENNReal.ofReal (Real.exp D * ∏ i, Real.exp (-(κ / 4) * (x i) ^ 2)) < ∞ := by
    refine Integrable.lintegral_lt_top ?_
    rw [volume_pi]
    exact hint.const_mul _
  exact lt_of_le_of_lt (hmono.trans hle) hfin

/-! ### Instances -/

end Rigidity
