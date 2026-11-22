module

public import Rigidity.Ensemble.Basic
public import Rigidity.LocalLaw.GoodEvent
public import Rigidity.Probability.Moments
public import Rigidity.Spectrum.Net

@[expose] public section

/-!
# The a priori bound on the norm

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For an ensemble `ν ∈ ℰ_N(ϑ, δ₋, δ₊, C₀)` with product law `ℙ` on `Ω = 𝕜^{𝒫_N}`, this file proves
Lemma 4.5 (`prodLaw_norm_gt`): for `N ≥ max {13, √C₀}` and `κ ≥ κ_ϑ + 3 log N`,
`ℙ(‖H‖ > 25 κ^{1/ϑ} √(C₀ log N)) ≤ N² ϑ⁻¹ e^{-κ} + 2 e^{-N log N}`.

The proof truncates every entry at `T σ_ij`, `T = κ^{1/ϑ}`, and recentres it (Step 1); for a fixed
unit vector `y` the quadratic form of the recentred matrix is a sum of independent centred bounded
variables, one for each pair `(i, j) ∈ 𝒫_N`, to which Hoeffding's inequality (H) of §4.2 applies
(Step 2); the finite net of Lemma 3.14 and a union bound control the operator norm (Step 3).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-! ### 1. Entries and linearity of `x ↦ H(x)` -/

/-- The entry `h_kl` as a function of the coordinate `x_{{k,l}}`. -/
private def crude_ent {N : ℕ} (k l : Fin N) (z : 𝕜) : 𝕜 :=
  if k < l then z else if l < k then star z else ((RCLike.re z : ℝ) : 𝕜)

private lemma crude_toMatrix_apply {N : ℕ} (x : Pair N → 𝕜) (k l : Fin N) :
    toMatrix x k l = crude_ent k l (x (Pair.mk' k l)) := rfl

private lemma crude_norm_ent_le {N : ℕ} (k l : Fin N) (z : 𝕜) : ‖crude_ent k l z‖ ≤ ‖z‖ := by
  unfold crude_ent
  split_ifs
  · exact le_rfl
  · rw [norm_star]
  · rw [RCLike.norm_ofReal]
    exact RCLike.abs_re_le_norm z

private lemma crude_continuous_ent {N : ℕ} (k l : Fin N) : Continuous (crude_ent (𝕜 := 𝕜) k l) := by
  unfold crude_ent
  split_ifs
  · exact continuous_id
  · exact continuous_star
  · exact RCLike.continuous_ofReal.comp RCLike.continuous_re

private lemma crude_toMatrix_add {N : ℕ} (x y : Pair N → 𝕜) :
    toMatrix (x + y) = toMatrix x + toMatrix y := by
  ext i j
  simp only [toMatrix, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs
  · rfl
  · rw [star_add]
  · rw [map_add, RCLike.ofReal_add]

/-- For a function `f` with integral zero, the entry of `f` also has integral zero. -/
private lemma crude_integral_ent {α : Type*} [MeasurableSpace α] {μ : Measure α} {N : ℕ}
    (k l : Fin N) {f : α → 𝕜} (hf : Integrable f μ) (h0 : ∫ a, f a ∂μ = 0) :
    ∫ a, crude_ent k l (f a) ∂μ = 0 := by
  unfold crude_ent
  split_ifs
  · exact h0
  · simp only [RCLike.star_def]
    rw [integral_conj, h0, map_zero]
  · rw [integral_ofReal, integral_re hf, h0]
    simp

private lemma crude_integrable_ent {α : Type*} [MeasurableSpace α] {μ : Measure α} {N : ℕ}
    (k l : Fin N) {f : α → 𝕜} (hf : Integrable f μ) :
    Integrable (fun a => crude_ent k l (f a)) μ :=
  hf.norm.mono' ((crude_continuous_ent k l).comp_aestronglyMeasurable hf.1)
    (Eventually.of_forall fun a => crude_norm_ent_le k l (f a))

/-! ### 2. The operator norm and the entries -/

/-- `‖M‖ ≤ (∑ᵢⱼ ‖Mᵢⱼ‖²)^{1/2}` for the `ℓ²` operator norm. -/
private theorem crude_norm_le_sqrt_sum_sq {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜) :
    ‖M‖ ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun X => ?_
  change ‖Matrix.toEuclideanLin M X‖ ≤ _ * ‖X‖
  have hrow : ∀ i, ‖(M *ᵥ X.ofLp) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := fun i => by
    have h1 : ‖(M *ᵥ X.ofLp) i‖ ≤ ∑ j, ‖M i j‖ * ‖X.ofLp j‖ := by
      calc ‖(M *ᵥ X.ofLp) i‖ = ‖∑ j, M i j * X.ofLp j‖ := rfl
        _ ≤ ∑ j, ‖M i j * X.ofLp j‖ := norm_sum_le _ _
        _ = ∑ j, ‖M i j‖ * ‖X.ofLp j‖ := by simp only [norm_mul]
    calc ‖(M *ᵥ X.ofLp) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖X.ofLp j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖X.ofLp j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖(Matrix.toEuclideanLin M X).ofLp i‖ ^ 2 = ∑ i, ‖(M *ᵥ X.ofLp) i‖ ^ 2 := by
        rfl
    _ ≤ ∑ i, (∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := by rw [Finset.sum_mul]
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]

/-- If every coordinate of `μ` has norm at most `m`, then `‖H(μ)‖ ≤ N m`. -/
private lemma crude_norm_toMatrix_le {N : ℕ} (μ : Pair N → 𝕜) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ p, ‖μ p‖ ≤ m) : ‖toMatrix μ‖ ≤ N * m := by
  refine (crude_norm_le_sqrt_sum_sq _).trans ?_
  rw [Real.sqrt_le_left (by positivity)]
  have hent : ∀ i j : Fin N, ‖toMatrix μ i j‖ ^ 2 ≤ m ^ 2 := fun i j =>
    pow_le_pow_left₀ (norm_nonneg _)
      ((crude_norm_ent_le i j _).trans (h (Pair.mk' i j))) 2
  calc ∑ i, ∑ j, ‖toMatrix μ i j‖ ^ 2 ≤ ∑ _i : Fin N, ∑ _j : Fin N, m ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = (N * m) ^ 2 := by simp [Finset.sum_const]; ring


private lemma crude_integrable_re {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) : Integrable (fun a => RCLike.re (f a)) μ :=
  hf.norm.mono' (RCLike.continuous_re.comp_aestronglyMeasurable hf.1)
    (Eventually.of_forall fun a => by simpa using RCLike.abs_re_le_norm (f a))

/-! ### 3. Truncation and recentring (Step 1 of Lemma 4.5) -/

section Truncation

variable {N : ℕ} (M : Ensemble 𝕜 N) (T : ℝ) (p : Pair N)

/-- `y ↦ y 𝟙(‖y‖ ≤ T σ_p)`. -/
private noncomputable def crude_trunc (y : 𝕜) : 𝕜 :=
  if ‖y‖ ≤ T * Real.sqrt (M.varPair p) then y else 0

/-- `μ_p = 𝔼[x_p 𝟙(‖x_p‖ ≤ T σ_p)]`. -/
private noncomputable def crude_mu : 𝕜 := ∫ y, crude_trunc M T p y ∂M.law p

/-- The recentred truncation `x̂_p = x_p 𝟙(‖x_p‖ ≤ T σ_p) - μ_p`. -/
private noncomputable def crude_hat (y : 𝕜) : 𝕜 := crude_trunc M T p y - crude_mu M T p

variable {M T p}

private lemma crude_measurable_trunc : Measurable (crude_trunc M T p) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    measurable_const

private lemma crude_norm_trunc_le (hT : 0 ≤ T) (y : 𝕜) :
    ‖crude_trunc M T p y‖ ≤ T * Real.sqrt (M.varPair p) := by
  unfold crude_trunc
  split_ifs with h
  · exact h
  · rw [norm_zero]; positivity

private lemma crude_integrable_trunc (hT : 0 ≤ T) : Integrable (crude_trunc M T p) (M.law p) :=
  Integrable.of_bound crude_measurable_trunc.aestronglyMeasurable (T * Real.sqrt (M.varPair p))
    (Eventually.of_forall (crude_norm_trunc_le hT))

private lemma crude_norm_mu_le (hT : 0 ≤ T) : ‖crude_mu M T p‖ ≤ T * Real.sqrt (M.varPair p) := by
  have := norm_integral_le_of_norm_le_const (μ := M.law p) (f := crude_trunc M T p)
    (C := T * Real.sqrt (M.varPair p)) (Eventually.of_forall (crude_norm_trunc_le hT))
  simpa [crude_mu] using this

private lemma crude_norm_hat_le (hT : 0 ≤ T) (y : 𝕜) :
    ‖crude_hat M T p y‖ ≤ 2 * T * Real.sqrt (M.varPair p) := by
  unfold crude_hat
  have h1 := crude_norm_trunc_le (M := M) (p := p) hT y
  have h2 := crude_norm_mu_le (M := M) (p := p) hT
  calc ‖crude_trunc M T p y - crude_mu M T p‖ ≤ ‖crude_trunc M T p y‖ + ‖crude_mu M T p‖ :=
        norm_sub_le _ _
    _ ≤ 2 * T * Real.sqrt (M.varPair p) := by linarith

private lemma crude_measurable_hat : Measurable (crude_hat M T p) :=
  crude_measurable_trunc.sub measurable_const

private lemma crude_integrable_hat (hT : 0 ≤ T) : Integrable (crude_hat M T p) (M.law p) :=
  (crude_integrable_trunc hT).sub (integrable_const _)

private lemma crude_integral_hat (hT : 0 ≤ T) : ∫ y, crude_hat M T p y ∂M.law p = 0 := by
  unfold crude_hat
  rw [integral_sub (crude_integrable_trunc hT) (integrable_const _)]
  simp [crude_mu]

/-- Recentring: `|μ_p| ≤ σ_p ϑ^{-1/2} e^{-T^ϑ/2}` (Lemma 4.1 (b) and the centring (2.1)). -/
private lemma crude_norm_mu_le_tail {ϑ δm δp C₀ : ℝ} (h : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hT : 1 ≤ T) :
    ‖crude_mu M T p‖ ≤ Real.sqrt (M.varPair p) * ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-T ^ ϑ / 2) := by
  set σ := Real.sqrt (M.varPair p) with hσ
  set S : Set 𝕜 := {y | ‖y‖ ≤ T * σ} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have hint : Integrable (fun y : 𝕜 => y) (M.law p) := by
    have := Ensemble.Assumptions.integrable_norm_pow M h hϑ p 1
    refine (integrable_norm_iff (f := fun y : 𝕜 => y) aestronglyMeasurable_id).1 ?_
    simpa using this
  have htrunc : crude_trunc M T p = S.indicator (fun y => y) := by
    funext y
    unfold crude_trunc
    simp [Set.indicator, S, σ]
  have hsplit := integral_add_compl hS hint
  have h0 : ∫ y, y ∂M.law p = 0 := h.meanZero p
  have hmu : crude_mu M T p = -∫ y in Sᶜ, y ∂M.law p := by
    unfold crude_mu
    rw [htrunc, integral_indicator hS]
    rw [h0] at hsplit
    exact eq_neg_of_add_eq_zero_left hsplit
  have hSc : Sᶜ = {y : 𝕜 | T * σ < ‖y‖} := by
    ext y
    simp [S]
  rw [hmu, norm_neg, hSc]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact (moments_trunc hϑ hϑ1 (Real.sqrt_nonneg _) (fun x hx => h.subexp p x hx) hT).1

end Truncation


/-! ### 4. Numerical consequences of the hypotheses -/

private lemma crude_varPair_nonneg {N : ℕ} (M : Ensemble 𝕜 N) (p : Pair N) : 0 ≤ M.varPair p :=
  integral_nonneg fun _ => by positivity

/-- Assumption (C) in terms of the variance of the coordinate `p`. -/
private lemma crude_varPair_le {N : ℕ} {M : Ensemble 𝕜 N} {C₀ : ℝ} (hC : M.AssumptionC C₀)
    (p : Pair N) : M.varPair p ≤ C₀ / N := by
  have h := hC p.1.1 p.1.2
  have e : Pair.mk' p.1.1 p.1.2 = p := by simp [Pair.mk', p.2]
  unfold Ensemble.var at h
  rwa [e] at h

/-- `κ ≥ κ_ϑ + 3 log N` forces `κ ≥ 1` and `κ ≥ log ϑ⁻¹ + 3 log N`. -/
private lemma crude_kappa_bounds {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ κ) :
    1 ≤ κ ∧ Real.log ϑ⁻¹ + 3 * Real.log N ≤ κ := by
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have h1 : 0 ≤ Real.log ϑ⁻¹ := Real.log_nonneg ha
  have h2 : 1 ≤ Real.log (4 * cTheta ϑ⁻¹) := by
    rw [Real.le_log_iff_exp_le (by unfold cTheta; positivity)]
    unfold cTheta
    have := Real.exp_one_lt_d9
    nlinarith
  have h3 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h4 : 4 ≤ 4 * ϑ⁻¹ * Real.log (4 * cTheta ϑ⁻¹) := by nlinarith
  unfold kappaTheta at hκ
  constructor <;> nlinarith

/-- Step 1: the recentring matrix has operator norm at most `1`. -/
private lemma crude_norm_mu_matrix_le_one {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hN : 1 ≤ N)
    (hN' : Real.sqrt C₀ ≤ N) {κ : ℝ} (hκ1 : 1 ≤ κ) (hκ : Real.log ϑ⁻¹ + 3 * Real.log N ≤ κ) :
    ‖toMatrix (fun p => crude_mu M (κ ^ ϑ⁻¹) p)‖ ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hC0 : 0 ≤ C₀ := by
    have := h.boundC (Fin.mk 0 hN) (Fin.mk 0 hN)
    have h0 : 0 ≤ M.var (Fin.mk 0 hN) (Fin.mk 0 hN) := crude_varPair_nonneg M _
    have := h0.trans this
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => by
      have : (N : ℝ) ≤ 0 := h.2
      linarith
  set T := κ ^ ϑ⁻¹ with hTdef
  have hT1 : 1 ≤ T := Real.one_le_rpow hκ1 (inv_nonneg.2 hϑ.le)
  have hTκ : T ^ ϑ = κ := Real.rpow_inv_rpow (by linarith) hϑ.ne'
  set m := Real.sqrt (C₀ / N) * ϑ ^ (-(1 / 2 : ℝ)) * Real.exp (-κ / 2) with hmdef
  have hm : 0 ≤ m := by positivity
  have hmu : ∀ p, ‖crude_mu M T p‖ ≤ m := fun p => by
    refine (crude_norm_mu_le_tail h hϑ hϑ1 hT1).trans ?_
    rw [hTκ, hmdef]
    gcongr
    exact crude_varPair_le h.boundC p
  refine (crude_norm_toMatrix_le _ hm hmu).trans ?_
  have e1 : Real.sqrt (C₀ / N) ^ 2 = C₀ / N := Real.sq_sqrt (by positivity)
  have e2 : (ϑ ^ (-(1 / 2 : ℝ))) ^ 2 = ϑ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hϑ.le]
    norm_num
    exact Real.rpow_neg_one ϑ
  have e3 : Real.exp (-κ / 2) ^ 2 = Real.exp (-κ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsq : ((N : ℝ) * m) ^ 2 = N * C₀ * ϑ⁻¹ * Real.exp (-κ) := by
    rw [mul_pow, hmdef, mul_pow, mul_pow, e1, e2, e3]
    field_simp
  set Q : ℝ := ϑ⁻¹ * (N : ℝ) ^ 3 with hQ
  have hQpos : 0 < Q := by positivity
  have hlogQ : Real.log Q = Real.log ϑ⁻¹ + 3 * Real.log N := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hexp : Real.exp (-κ) ≤ Q⁻¹ := by
    rw [Real.exp_neg]
    refine inv_anti₀ hQpos ?_
    calc Q = Real.exp (Real.log Q) := (Real.exp_log hQpos).symm
      _ ≤ Real.exp κ := Real.exp_le_exp.2 (by linarith)
  have hC2 : C₀ ≤ (N : ℝ) ^ 2 := by
    calc C₀ = Real.sqrt C₀ ^ 2 := (Real.sq_sqrt hC0).symm
      _ ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hN' 2
  have h1 : (N : ℝ) * C₀ * ϑ⁻¹ ≤ Q := by
    rw [hQ]
    have : (N : ℝ) * C₀ ≤ (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    calc (N : ℝ) * C₀ * ϑ⁻¹ ≤ (N : ℝ) * (N : ℝ) ^ 2 * ϑ⁻¹ := by gcongr
      _ = ϑ⁻¹ * (N : ℝ) ^ 3 := by ring
  have h2 : ((N : ℝ) * m) ^ 2 ≤ 1 := by
    rw [hsq]
    calc (N : ℝ) * C₀ * ϑ⁻¹ * Real.exp (-κ) ≤ Q * Q⁻¹ := by
          gcongr
      _ = 1 := mul_inv_cancel₀ hQpos.ne'
  have h3 : 0 ≤ (N : ℝ) * m := by positivity
  nlinarith


/-! ### 5. The quadratic form of a recentred matrix (Step 2 of Lemma 4.5) -/

section Form

variable {N : ℕ} (y : Fin N → 𝕜)

/-- The part of `Re ⟨y, H(x) y⟩` that depends on the coordinate `x_p`: the sum of
`Re (ȳ_k h_kl y_l)` over the ordered pairs `(k, l)` with `{k, l} = p`. -/
private noncomputable def crude_xi (p : Pair N) (z : 𝕜) : ℝ :=
  ∑ q : Fin N × Fin N,
    if Pair.mk' q.1 q.2 = p then RCLike.re (star (y q.1) * crude_ent q.1 q.2 z * y q.2) else 0

/-- The weight `∑ ‖y_k‖ ‖y_l‖` over the ordered pairs `(k, l)` with `{k, l} = p`. -/
private noncomputable def crude_w (p : Pair N) : ℝ :=
  ∑ q : Fin N × Fin N, if Pair.mk' q.1 q.2 = p then ‖y q.1‖ * ‖y q.2‖ else 0

private lemma crude_sum_xi (x : Pair N → 𝕜) :
    ∑ p, crude_xi y p (x p) = RCLike.re (star y ⬝ᵥ (toMatrix x *ᵥ y)) := by
  unfold crude_xi
  rw [Finset.sum_comm]
  have h1 : ∀ q : Fin N × Fin N,
      (∑ p : Pair N, if Pair.mk' q.1 q.2 = p then
        RCLike.re (star (y q.1) * crude_ent q.1 q.2 (x p) * y q.2) else 0) =
      RCLike.re (star (y q.1) * toMatrix x q.1 q.2 * y q.2) := fun q => by
    rw [Finset.sum_ite_eq]
    simp [crude_toMatrix_apply]
  rw [Finset.sum_congr rfl fun q _ => h1 q]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, map_sum]
  rw [Fintype.sum_prod_type' (fun k l => RCLike.re (star (y k) * toMatrix x k l * y l))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc]

private lemma crude_xi_abs_le (p : Pair N) (z : 𝕜) : |crude_xi y p z| ≤ ‖z‖ * crude_w y p := by
  unfold crude_xi crude_w
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  split_ifs
  · calc |RCLike.re (star (y q.1) * crude_ent q.1 q.2 z * y q.2)|
        ≤ ‖star (y q.1) * crude_ent q.1 q.2 z * y q.2‖ := RCLike.abs_re_le_norm _
      _ = ‖y q.1‖ * ‖crude_ent q.1 q.2 z‖ * ‖y q.2‖ := by simp only [norm_mul, norm_star]
      _ ≤ ‖y q.1‖ * ‖z‖ * ‖y q.2‖ := by
          gcongr
          exact crude_norm_ent_le _ _ _
      _ = ‖z‖ * (‖y q.1‖ * ‖y q.2‖) := by ring
  · simp

private lemma crude_continuous_xi (p : Pair N) : Continuous (crude_xi y p) := by
  unfold crude_xi
  refine continuous_finsetSum _ fun q _ => ?_
  refine Continuous.if_const _ ?_ continuous_const
  exact RCLike.continuous_re.comp
    ((continuous_const.mul (crude_continuous_ent q.1 q.2)).mul continuous_const)

/-- The ordered pairs `(k, l)` with `{k, l} = p` are at most two. -/
private lemma crude_card_fiber (p : Pair N) :
    (Finset.univ.filter fun q : Fin N × Fin N => Pair.mk' q.1 q.2 = p).card ≤ 2 := by
  refine (Finset.card_le_card (t := {p.1, p.1.swap}) ?_).trans Finset.card_le_two
  rintro ⟨a, b⟩ hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold Pair.mk' at hq
  split_ifs at hq with h
  · left
    exact congrArg Subtype.val hq
  · right
    have := congrArg Subtype.val hq
    simp only at this
    rw [← this]
    rfl

private lemma crude_w_sq_le (p : Pair N) :
    crude_w y p ^ 2 ≤ 2 * ∑ q : Fin N × Fin N,
      if Pair.mk' q.1 q.2 = p then ‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2 else 0 := by
  unfold crude_w
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  set F := Finset.univ.filter fun q : Fin N × Fin N => Pair.mk' q.1 q.2 = p with hF
  calc (∑ q ∈ F, ‖y q.1‖ * ‖y q.2‖) ^ 2
      ≤ F.card * ∑ q ∈ F, (‖y q.1‖ * ‖y q.2‖) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ 2 * ∑ q ∈ F, ‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2 := by
        have hc : (F.card : ℝ) ≤ 2 := by exact_mod_cast crude_card_fiber p
        simp only [mul_pow]
        gcongr

/-- `∑_p σ_p² w_p² ≤ 2 (C₀ / N) |y|⁴` by Assumption (C). -/
private lemma crude_sum_var_w_sq_le {M : Ensemble 𝕜 N} {C₀ : ℝ} (hC : M.AssumptionC C₀)
    (hC₀ : 0 ≤ C₀) (hy : ∑ i, ‖y i‖ ^ 2 ≤ 1) :
    ∑ p, M.varPair p * crude_w y p ^ 2 ≤ 2 * (C₀ / N) := by
  have h1 : ∀ p : Pair N, M.varPair p * (2 * ∑ q : Fin N × Fin N,
      if Pair.mk' q.1 q.2 = p then ‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2 else 0) =
      2 * ∑ q : Fin N × Fin N, if Pair.mk' q.1 q.2 = p then
        M.var q.1 q.2 * (‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2) else 0 := fun p => by
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rw [← h]
      rfl
    · simp
  calc ∑ p, M.varPair p * crude_w y p ^ 2
      ≤ ∑ p, M.varPair p * (2 * ∑ q : Fin N × Fin N,
          if Pair.mk' q.1 q.2 = p then ‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun p _ =>
          mul_le_mul_of_nonneg_left (crude_w_sq_le y p) (crude_varPair_nonneg M p)
    _ = 2 * ∑ q : Fin N × Fin N, M.var q.1 q.2 * (‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2) := by
        rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ ≤ 2 * ∑ q : Fin N × Fin N, (C₀ / N) * (‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2) := by
        gcongr with q
        exact hC q.1 q.2
    _ = 2 * ((C₀ / N) * (∑ i, ‖y i‖ ^ 2) ^ 2) := by
        have hs : ∑ q : Fin N × Fin N, ‖y q.1‖ ^ 2 * ‖y q.2‖ ^ 2 = (∑ i, ‖y i‖ ^ 2) ^ 2 := by
          rw [Fintype.sum_prod_type' (fun a b => ‖y a‖ ^ 2 * ‖y b‖ ^ 2), sq, Finset.sum_mul_sum]
        rw [← Finset.mul_sum, hs]
    _ ≤ 2 * (C₀ / N) := by
        have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
        have hs2 : (∑ i, ‖y i‖ ^ 2) ^ 2 ≤ 1 := by nlinarith
        have : 0 ≤ C₀ / N := by positivity
        nlinarith


private lemma crude_w_nonneg (p : Pair N) : 0 ≤ crude_w y p :=
  Finset.sum_nonneg fun q _ => by
    split_ifs
    · positivity
    · exact le_rfl

variable {M : Ensemble 𝕜 N} {T : ℝ}

private lemma crude_integral_xi_hat (hT : 0 ≤ T) (p : Pair N) :
    ∫ z, crude_xi y p (crude_hat M T p z) ∂M.law p = 0 := by
  have hint := crude_integrable_hat (M := M) (p := p) hT
  unfold crude_xi
  have hterm : ∀ q : Fin N × Fin N, Integrable (fun z => if Pair.mk' q.1 q.2 = p then
      RCLike.re (star (y q.1) * crude_ent q.1 q.2 (crude_hat M T p z) * y q.2) else 0)
      (M.law p) := by
    intro q
    by_cases hq : Pair.mk' q.1 q.2 = p
    · simp only [hq, ↓reduceIte]
      exact crude_integrable_re (((crude_integrable_ent q.1 q.2 hint).const_mul _).mul_const _)
    · simp only [hq, ↓reduceIte]
      exact integrable_zero _ _ _
  rw [integral_finsetSum _ fun q _ => hterm q]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : Pair.mk' q.1 q.2 = p
  · simp only [hq, ↓reduceIte]
    rw [integral_re (((crude_integrable_ent q.1 q.2 hint).const_mul _).mul_const _),
      integral_mul_const, integral_const_mul,
      crude_integral_ent q.1 q.2 hint (crude_integral_hat hT)]
    simp
  · simp only [hq, ↓reduceIte]
    simp

end Form

/-- Hoeffding's inequality (H) of §4.2 for a finite index type. -/
private lemma crude_hoeffding {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] {ξ : ι → Ω → ℝ} (hind : iIndepFun ξ μ)
    (hmeas : ∀ i, Measurable (ξ i)) (hmean : ∀ i, ∫ ω, ξ i ω ∂μ = 0) {c : ι → ℝ}
    (hbd : ∀ i ω, |ξ i ω| ≤ c i) {κ : ℝ} (hκ : 0 ≤ κ) :
    μ {ω | Real.sqrt (2 * κ * ∑ i, c i ^ 2) < |∑ i, ξ i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-κ)) := by
  set e := (Fintype.equivFin ι).symm with he
  have h := hoeffding_abs (μ := μ) (ξ := fun j => ξ (e j)) (hind.precomp e.injective)
    (fun j => hmeas _) (fun j => hmean _) (c := fun j => c (e j))
    (fun j => Eventually.of_forall fun ω => hbd _ _) hκ
  have e1 : ∑ j, c (e j) ^ 2 = ∑ i, c i ^ 2 := Equiv.sum_comp e (fun i => c i ^ 2)
  have e2 : ∀ ω, ∑ j, ξ (e j) ω = ∑ i, ξ i ω := fun ω => Equiv.sum_comp e (fun i => ξ i ω)
  simp only [e1, e2] at h
  exact h

section FormTail

variable {N : ℕ}

/-- Step 2: for a fixed `y` with `|y| ≤ 1`, the quadratic form of the recentred matrix is small
outside an event of probability `2 e^{-4 N log N}`. -/
private lemma crude_form_tail (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) {T : ℝ} (hT : 0 ≤ T) (hC₀ : 0 ≤ C₀) (hN : 1 ≤ N)
    {y : Fin N → 𝕜} (hy : ∑ i, ‖y i‖ ^ 2 ≤ 1) :
    M.prodLaw {x | 8 * T * Real.sqrt (C₀ * Real.log N) <
        ‖star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y)‖} ≤
      ENNReal.ofReal (2 * Real.exp (-(4 * N * Real.log N))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  set ξ : Pair N → (Pair N → 𝕜) → ℝ := fun p x => crude_xi y p (crude_hat M T p (x p)) with hξ
  set c : Pair N → ℝ := fun p => 2 * T * Real.sqrt (M.varPair p) * crude_w y p with hc
  have hmeasξ : ∀ p, Measurable (fun z : 𝕜 => crude_xi y p (crude_hat M T p z)) := fun p =>
    (crude_continuous_xi y p).measurable.comp crude_measurable_hat
  have hind : iIndepFun ξ M.prodLaw :=
    iIndepFun_pi (μ := M.law) (X := fun p z => crude_xi y p (crude_hat M T p z))
      (fun p => (hmeasξ p).aemeasurable)
  have hmeas : ∀ p, Measurable (ξ p) := fun p => (hmeasξ p).comp (measurable_pi_apply p)
  have hmean : ∀ p, ∫ x, ξ p x ∂M.prodLaw = 0 := fun p => by
    have := integral_comp_eval (μ := M.law) (i := p)
      (f := fun z => crude_xi y p (crude_hat M T p z)) (hmeasξ p).aestronglyMeasurable
    exact this.trans (crude_integral_xi_hat y hT p)
  have hbd : ∀ p x, |ξ p x| ≤ c p := fun p x =>
    (crude_xi_abs_le y p _).trans
      (by
        calc ‖crude_hat M T p (x p)‖ * crude_w y p
            ≤ (2 * T * Real.sqrt (M.varPair p)) * crude_w y p :=
              mul_le_mul_of_nonneg_right (crude_norm_hat_le hT _) (crude_w_nonneg y p)
          _ = c p := rfl)
  have hκ : 0 ≤ 4 * (N : ℝ) * Real.log N := by positivity
  have h0 := crude_hoeffding hind hmeas hmean hbd hκ
  have hV : ∑ p, c p ^ 2 ≤ 8 * T ^ 2 * (C₀ / N) := by
    have hcp : ∀ p, c p ^ 2 = 4 * T ^ 2 * (M.varPair p * crude_w y p ^ 2) := fun p => by
      simp only [hc]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (crude_varPair_nonneg M p)]
      ring
    calc ∑ p, c p ^ 2 = 4 * T ^ 2 * ∑ p, M.varPair p * crude_w y p ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => hcp p
      _ ≤ 4 * T ^ 2 * (2 * (C₀ / N)) := by
          gcongr
          exact crude_sum_var_w_sq_le y h.boundC hC₀ hy
      _ = 8 * T ^ 2 * (C₀ / N) := by ring
  have hB : 0 ≤ 8 * T * Real.sqrt (C₀ * Real.log N) := by positivity
  have hsq : Real.sqrt (2 * (4 * N * Real.log N) * ∑ p, c p ^ 2) ≤
      8 * T * Real.sqrt (C₀ * Real.log N) := by
    rw [Real.sqrt_le_left hB, mul_pow, Real.sq_sqrt (by positivity)]
    calc 2 * (4 * (N : ℝ) * Real.log N) * ∑ p, c p ^ 2
        ≤ 2 * (4 * (N : ℝ) * Real.log N) * (8 * T ^ 2 * (C₀ / N)) := by gcongr
      _ = (8 * T) ^ 2 * (C₀ * Real.log N) := by field_simp; ring
  refine le_trans (measure_mono ?_) h0
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hA := toMatrix_isHermitian (fun p => crude_hat M T p (x p))
  have him := hA.im_star_dotProduct_mulVec_self y
  have hre := crude_sum_xi y (fun p => crude_hat M T p (x p))
  have hnorm : ‖star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y)‖ = |∑ p, ξ p x| := by
    rw [hξ]
    simp only
    rw [hre]
    set w := star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y) with hw
    have : w = ((RCLike.re w : ℝ) : 𝕜) := by
      conv_lhs => rw [← RCLike.re_add_im w]
      rw [him]
      simp
    rw [this, RCLike.norm_ofReal]
    simp
  rw [hnorm] at hx
  exact lt_of_le_of_lt hsq hx

end FormTail

/-! ### 6. Lemma 4.5 -/

/-- Lemma 4.5: the a priori bound on the norm. -/
theorem prodLaw_norm_gt {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀)
    (hN : 13 ≤ N) (hN' : Real.sqrt C₀ ≤ N) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ κ) :
    M.prodLaw {x | 25 * κ ^ ϑ⁻¹ * Real.sqrt (C₀ * Real.log N) < ‖toMatrix x‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-κ) + 2 * Real.exp (-(N * Real.log N))) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN13 : (13 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hκ1, hκ2⟩ := crude_kappa_bounds hϑ hϑ1 hN1 hκ
  set T := κ ^ ϑ⁻¹ with hTdef
  have hT1 : 1 ≤ T := Real.one_le_rpow hκ1 (inv_nonneg.2 hϑ.le)
  have hTκ : T ^ ϑ = κ := Real.rpow_inv_rpow (by linarith) hϑ.ne'
  have hC0 : 0 ≤ C₀ := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    linarith
  have hS1 : 1 ≤ Real.sqrt (C₀ * Real.log N) := by
    rw [Real.one_le_sqrt]
    nlinarith
  obtain ⟨hfin, hcard⟩ := normNet_card (𝕜 := 𝕜) hN
  set 𝒩 := hfin.toFinset with h𝒩
  set B : ℝ := 8 * T * Real.sqrt (C₀ * Real.log N) with hB
  have hB0 : 0 ≤ B := by positivity
  set A : Set (Pair N → 𝕜) := {x | ∃ p, T * Real.sqrt (M.varPair p) < ‖x p‖} with hAdef
  set E : Set (Pair N → 𝕜) := ⋃ y ∈ 𝒩, {x | B <
    ‖star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y)‖} with hEdef
  have hA : M.prodLaw A ≤ ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-κ)) := by
    have := hM.prodLaw_large_entry hϑ hT1
    rw [hTκ] at this
    rwa [div_eq_mul_inv]
  have hE : M.prodLaw E ≤ ENNReal.ofReal (2 * Real.exp (-(N * Real.log N))) := by
    have hy : ∀ y ∈ 𝒩, M.prodLaw {x | B <
        ‖star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y)‖} ≤
        ENNReal.ofReal (2 * Real.exp (-(4 * N * Real.log N))) := fun y hy =>
      crude_form_tail M hM (by linarith) hC0 hN1 (hfin.mem_toFinset.1 hy).2
    calc M.prodLaw E ≤ ∑ y ∈ 𝒩, M.prodLaw {x | B <
          ‖star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y)‖} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _y ∈ 𝒩, ENNReal.ofReal (2 * Real.exp (-(4 * N * Real.log N))) :=
          Finset.sum_le_sum hy
      _ = ENNReal.ofReal (𝒩.card * (2 * Real.exp (-(4 * N * Real.log N)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(N * Real.log N))) := by
          apply ENNReal.ofReal_le_ofReal
          have hc : (𝒩.card : ℝ) ≤ Real.exp (3 * N * Real.log N) := by
            rw [h𝒩, ← Set.ncard_eq_toFinset_card _ hfin]
            exact hcard
          have e : Real.exp (3 * N * Real.log N) * Real.exp (-(4 * N * Real.log N)) =
              Real.exp (-(N * Real.log N)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc (𝒩.card : ℝ) * (2 * Real.exp (-(4 * N * Real.log N)))
              ≤ Real.exp (3 * N * Real.log N) * (2 * Real.exp (-(4 * N * Real.log N))) := by
                gcongr
            _ = 2 * (Real.exp (3 * N * Real.log N) * Real.exp (-(4 * N * Real.log N))) := by ring
            _ = 2 * Real.exp (-(N * Real.log N)) := by rw [e]
  have hsub : {x | 25 * T * Real.sqrt (C₀ * Real.log N) < ‖toMatrix x‖} ⊆ A ∪ E := by
    intro x hx
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hxA, hxE⟩ := hcon
    have hxA' : ∀ p, ‖x p‖ ≤ T * Real.sqrt (M.varPair p) := fun p =>
      not_lt.1 fun hlt => hxA ⟨p, hlt⟩
    have hxE' : ∀ y ∈ 𝒩, ‖star y ⬝ᵥ (toMatrix (fun p => crude_hat M T p (x p)) *ᵥ y)‖ ≤ B :=
      fun y hy => not_lt.1 fun hlt => hxE (Set.mem_iUnion₂.2 ⟨y, hy, hlt⟩)
    set Hh := toMatrix (fun p => crude_hat M T p (x p)) with hHh
    have hdec : toMatrix x = Hh + toMatrix (fun p => crude_mu M T p) := by
      rw [hHh, ← crude_toMatrix_add]
      congr 1
      funext p
      have : crude_trunc M T p (x p) = x p := by
        unfold crude_trunc
        simp only [hxA' p, ↓reduceIte]
      simp only [Pi.add_apply, crude_hat, this]
      ring
    have hnet : ‖Hh‖ ≤ 2 * B := by
      have h1 := norm_le_two_iSup_net (toMatrix_isHermitian (fun p => crude_hat M T p (x p)))
      have h2 : (⨆ y : normNet 𝕜 N, ‖star (y : Fin N → 𝕜) ⬝ᵥ (Hh *ᵥ (y : Fin N → 𝕜))‖) ≤ B :=
        Real.iSup_le (fun y => hxE' y.1 (hfin.mem_toFinset.2 y.2)) hB0
      linarith
    have hM1 : ‖toMatrix (fun p => crude_mu M T p)‖ ≤ 1 :=
      crude_norm_mu_matrix_le_one hM hϑ hϑ1 hN1 hN' hκ1 hκ2
    have hsum : ‖toMatrix x‖ ≤ ‖Hh‖ + ‖toMatrix (fun p => crude_mu M T p)‖ := by
      rw [hdec]
      exact norm_add_le _ _
    have hTs : 1 ≤ T * Real.sqrt (C₀ * Real.log N) := by nlinarith
    have hx' : 25 * T * Real.sqrt (C₀ * Real.log N) < ‖toMatrix x‖ := hx
    have : B = 8 * (T * Real.sqrt (C₀ * Real.log N)) := by rw [hB]; ring
    nlinarith
  calc M.prodLaw {x | 25 * κ ^ ϑ⁻¹ * Real.sqrt (C₀ * Real.log N) < ‖toMatrix x‖}
      ≤ M.prodLaw (A ∪ E) := measure_mono hsub
    _ ≤ M.prodLaw A + M.prodLaw E := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-κ)) +
          ENNReal.ofReal (2 * Real.exp (-(N * Real.log N))) := add_le_add hA hE
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-κ) + 2 * Real.exp (-(N * Real.log N))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end Rigidity
