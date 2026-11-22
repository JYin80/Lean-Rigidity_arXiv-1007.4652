module

public import Rigidity.Ensemble.Basic
public import Rigidity.Flow.Correlation
public import Rigidity.Flow.GoodSet
public import Rigidity.Flow.Main
public import Rigidity.LocalLaw.Strong
public import Rigidity.MainDefs

@[expose] public section

/-!
# Local ergodicity of Dyson Brownian motion: the unconditional endpoints

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

* `exists_rigidityBound`: Theorem 2.2, (2.25) and (2.26), with one tuple of constants for both
  events; this is the hypothesis `RigidityBound` of the conditional statements of
  `Rigidity.Flow.Main`, available for every parameter tuple.
* `dbm_quantitative`: Theorem 12.1, (12.4), obtained from `exists_rigidityBound` at the rescaled
  parameters of Lemma 13.1.
* `dbm_localErgodicity`: Theorem 2.3, (2.36).  Dimensions below the threshold of Corollary 19.5 are
  handled by the trivial bound `|𝒳^O| ≤ N^n ‖O‖_∞` of Lemma 19.2 (d), which is absorbed into the
  constant (proof of Theorem 2.3).
* `ErgodicityBound`, `dbm_localErgodicity_uniform`: Theorem 2.3 with one constant `C` for both
  fields `𝕂 = ℝ, ℂ`.
* `dbm_localErgodicity_hoelder`: Corollary 19.5 (Hölder test functions).

The last section contains compiled instances at the Rademacher ensemble.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
open scoped NNReal

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- (RA1): Theorem 2.2 with one constant tuple for both events. -/
theorem exists_rigidityBound :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
      ∃ A₀ C c φ : ℝ, ∃ N₀ : ℕ, RigidityBound 𝕜 ϑ δm δp C₀ A₀ C c φ N₀ := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  refine ⟨A₀, C, c, φ, N₀, hA, hC, hc, hφ, hφ1, fun N hN M hM L hL => ?_⟩
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N hN M hM L hL
  refine ⟨(measure_mono ?_).trans hprob, (measure_mono ?_).trans hprob⟩
  · intro x hx hxΞ
    obtain ⟨k, hk⟩ := hx
    exact absurd ((hgood x hxΞ).2.2.2.1 k) (not_lt.2 hk)
  · intro x hx hxΞ
    exact absurd (hgood x hxΞ).2.2.2.2 (not_lt.2 hx)

/-- The rigidity bound at the rescaled parameters of Lemma 13.1. -/
private lemma Endpoint_rigidityBound_tilde {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hδm : 0 < δm)
    (hδp : 0 < δp) :
    ∃ A₀ C c φ : ℝ, ∃ N₀ : ℕ,
      RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀) A₀ C c φ N₀ :=
  exists_rigidityBound (𝕜 := 𝕜) _ _ _ _
    (div_pos (lt_min hϑ one_pos) (by norm_num))
    (mul_pos (by norm_num) (lt_min hδm one_pos))
    (mul_pos (by norm_num) (lt_min hδp one_pos))
    (lt_of_lt_of_le (by norm_num) (le_max_right _ _))

/-- Theorem 12.1 (quantitative form of Theorem 2.3). -/
theorem dbm_quantitative :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n → ∀ ρO : ℝ, 0 < ρO →
    ∃ A₁ : ℝ, 1 ≤ A₁ ∧ ∃ Nq : ℕ, 3 ≤ Nq ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ N : ℕ, max Nq n ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ t : ℝ, 0 < t → Real.log N ^ 2 ≤ N * t →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
      corrLHS M O E b t ≤ C₁ * (Bd + K) * Real.exp (A₁ * Real.log (Real.log N) ^ 2) *
        (b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N * t) ^ (-(1 / 2 : ℝ))) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀ c hc hc2 n hn ρO hρO
  obtain ⟨A₀, C, c', φ, N₀, hR⟩ := Endpoint_rigidityBound_tilde (𝕜 := 𝕜) (C₀ := C₀) hϑ hδm hδp
  exact dbm_quantitative_of_rigidityBound hϑ hδm hδp hC₀ hR hc hc2 hn hρO

private lemma Endpoint_isProbabilityMeasure_gbeLaw (N : ℕ) :
    IsProbabilityMeasure (gbeLaw 𝕜 N) := by
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  exact (Measure.isProbabilityMeasure_map_iff (continuous_eigVec N).measurable.aemeasurable).2
    inferInstance

private lemma Endpoint_isProbabilityMeasure_eigLaw {N : ℕ} (M : Ensemble 𝕜 N) (t : ℝ) :
    IsProbabilityMeasure (M.eigLaw t) := by
  have hρ : IsProbabilityMeasure M.hermLaw := by
    unfold Ensemble.hermLaw
    exact (Measure.isProbabilityMeasure_map_iff
      (Herm.measurable_ofPair (𝕜 := 𝕜) N).aemeasurable).2 inferInstance
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  unfold Ensemble.eigLaw eigFlow ouLaw
  infer_instance

/-- `|𝔼_ν 𝒳^O_{E',ϱ}| ≤ N^n ‖O‖_∞` for a probability measure `ν` (Lemma 19.2 (d)). -/
private lemma Endpoint_abs_integral_corrX_le {N n : ℕ} (ν : Measure (Fin N → ℝ))
    [IsProbabilityMeasure ν] {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hB : ∀ u, |O u| ≤ B)
    (E' ϱ : ℝ) : |∫ x, corrX O E' ϱ x ∂ν| ≤ (N : ℝ) ^ n * B := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun x => corrX O E' ϱ x)
    (C := (N : ℝ) ^ n * B)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_corrX_le hB E' ϱ x)
  rw [Real.norm_eq_abs] at h
  simpa using h

/-- `0 ≤ C_{N,n} ≤ N^n` (12.2). -/
private lemma Endpoint_corrC_le (N n : ℕ) : 0 ≤ corrC N n ∧ corrC N n ≤ (N : ℝ) ^ n := by
  unfold corrC
  have h1 : ((N - n).factorial : ℝ) ≤ N.factorial := by
    exact_mod_cast Nat.factorial_le (Nat.sub_le N n)
  have h2 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The trivial bound `corrLHS ≤ 2 N^{2n} ‖O‖_∞`, from Lemma 19.2 (d) and `C_{N,n} ≤ N^n`. -/
private lemma Endpoint_corrLHS_le {N n : ℕ} (M : Ensemble 𝕜 N)
    {O : EuclideanSpace ℝ (Fin n) → ℝ} {Bd : ℝ} (hB : ∀ u, |O u| ≤ Bd) {E b : ℝ} (hb : 0 < b)
    (t : ℝ) : corrLHS M O E b t ≤ 2 * (N : ℝ) ^ (2 * n) * Bd := by
  have := Endpoint_isProbabilityMeasure_eigLaw M t
  have := Endpoint_isProbabilityMeasure_gbeLaw (𝕜 := 𝕜) N
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hB 0)
  obtain ⟨hC0, hC1⟩ := Endpoint_corrC_le N n
  have hNn : (0 : ℝ) ≤ (N : ℝ) ^ n := by positivity
  unfold corrLHS
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := E - b) (b := E + b)
    (C := (2 * b)⁻¹ * (N : ℝ) ^ n * (2 * ((N : ℝ) ^ n * Bd)))
    (f := fun E' => (2 * b)⁻¹ * corrC N n *
      ((∫ x, corrX O E' (rhoSc E) x ∂M.eigLaw t) - ∫ x, corrX O E' (rhoSc E) x ∂gbeLaw 𝕜 N))
    (fun E' _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * b)⁻¹ * corrC N n)]
      have h1 := Endpoint_abs_integral_corrX_le (M.eigLaw t) hB E' (rhoSc E)
      have h2 := Endpoint_abs_integral_corrX_le (gbeLaw 𝕜 N) hB E' (rhoSc E)
      have h3 := abs_sub
        (∫ x, corrX O E' (rhoSc E) x ∂M.eigLaw t) (∫ x, corrX O E' (rhoSc E) x ∂gbeLaw 𝕜 N)
      have h4 : 0 ≤ (2 * b)⁻¹ := by positivity
      gcongr
      linarith)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [show E + b - (E - b) = 2 * b by ring, abs_of_pos (by positivity),
    show 2 * n = n + n by ring, pow_add]
  field_simp

/-- Theorem 2.3, (2.36) (strong local ergodicity of Dyson Brownian motion). -/
theorem dbm_localErgodicity :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO →
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, max n 3 ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + K) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ) ^ (-1 + ε') + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2)) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀ ε' δ hε' hδ c hc hc2 n hn ρO hρO
  obtain ⟨A₀, C₁, c₁, φ, N₀, hR⟩ := Endpoint_rigidityBound_tilde (𝕜 := 𝕜) (C₀ := C₀) hϑ hδm hδp
  obtain ⟨N₂, CH, hCH, hH⟩ := dbm_localErgodicity_hoelder_of_rigidityBound hϑ hδm hδp hC₀ hR hε'
    hδ hc hc2 hn hρO (α := 1) one_pos le_rfl
  set C₀' : ℝ := 2 * (N₂ : ℝ) ^ (2 * n) * (N₂ : ℝ) ^ (δ / 2) with hC₀'
  have hC0' : 0 ≤ C₀' := by positivity
  refine ⟨max CH C₀', lt_of_lt_of_le hCH (le_max_left _ _), ?_⟩
  have hCpos : 0 < max CH C₀' := lt_of_lt_of_le hCH (le_max_left _ _)
  intro N hN M hM O Bd K hB hL hsupp E hE b hb hb2 t ht
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hB 0)
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  have hP : 1 ≤ (N : ℝ) ^ (2 * ε') := Real.one_le_rpow (by linarith) (by positivity)
  have hb1 : b ≤ 1 := by linarith
  have hb12 : 1 ≤ b ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb hb1 (by norm_num)
  rcases le_or_gt N₂ N with h2 | h2
  · have hH' := hH N h2 M hM O Bd K hB (fun u v => by
        rw [Real.rpow_one]
        have := hL.dist_le_mul u v
        rwa [Real.dist_eq, dist_eq_norm] at this) hsupp E hE b hb hb2 t ht
    rw [Real.rpow_one] at hH'
    have hNe : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-1 + ε') := by
      rw [Real.rpow_add hNpos, Real.rpow_neg_one]
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by linarith) hε'.le)
    refine hH'.trans ?_
    have hb0 : 0 ≤ b⁻¹ := by positivity
    have hCH' : CH ≤ max CH C₀' := le_max_left _ _
    have : b⁻¹ * (N : ℝ)⁻¹ ≤ b⁻¹ * (N : ℝ) ^ (-1 + ε') := by gcongr
    gcongr
  · have h1 := Endpoint_corrLHS_le M hB (E := E) hb t
    have hNN : (N : ℝ) ≤ N₂ := by exact_mod_cast h2.le
    have hN₂pos : (0 : ℝ) < N₂ := by linarith
    have hpow : (N : ℝ) ^ (2 * n) ≤ (N₂ : ℝ) ^ (2 * n) := pow_le_pow_left₀ hNpos.le hNN _
    have hneg : (N₂ : ℝ) ^ (-δ / 2) ≤ (N : ℝ) ^ (-δ / 2) :=
      Real.rpow_le_rpow_of_nonpos hNpos hNN (by linarith)
    have hmul : (N₂ : ℝ) ^ (δ / 2) * (N₂ : ℝ) ^ (-δ / 2) = 1 := by
      rw [← Real.rpow_add hN₂pos, show δ / 2 + -δ / 2 = 0 by ring, Real.rpow_zero]
    set X : ℝ := b⁻¹ * (N : ℝ) ^ (-1 + ε') + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2) with hX
    have hXge : (N₂ : ℝ) ^ (-δ / 2) ≤ X := by
      have h3 : 0 ≤ b⁻¹ * (N : ℝ) ^ (-1 + ε') := by positivity
      have h4 : (N : ℝ) ^ (-δ / 2) ≤ b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2) :=
        le_mul_of_one_le_left (by positivity) hb12
      linarith
    have hCC : C₀' ≤ max CH C₀' := le_max_right _ _
    calc corrLHS M O E b t ≤ 2 * (N : ℝ) ^ (2 * n) * Bd := h1
      _ ≤ 2 * (N₂ : ℝ) ^ (2 * n) * Bd := by gcongr
      _ = C₀' * (N₂ : ℝ) ^ (-δ / 2) * Bd := by
          rw [hC₀']
          linear_combination (-(2 * (N₂ : ℝ) ^ (2 * n) * Bd)) * hmul
      _ ≤ max CH C₀' * (N₂ : ℝ) ^ (-δ / 2) * Bd := by gcongr
      _ ≤ max CH C₀' * X * Bd := by gcongr
      _ = max CH C₀' * Bd * 1 * X := by ring
      _ ≤ max CH C₀' * (Bd + K) * (N : ℝ) ^ (2 * ε') * X := by gcongr; linarith

/-- Theorem 2.3 with one constant for both fields (NP: `C` does not depend on `𝕂`). -/
theorem dbm_localErgodicity_uniform :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO →
    ∃ C : ℝ, 0 < C ∧ ErgodicityBound ℝ ϑ δm δp C₀ ε' δ c n ρO C ∧
      ErgodicityBound ℂ ϑ δm δp C₀ ε' δ c n ρO C := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀ ε' δ hε' hδ c hc hc2 n hn ρO hρO
  obtain ⟨Cr, hCr, hr⟩ := dbm_localErgodicity (𝕜 := ℝ) ϑ δm δp C₀ hϑ hδm hδp hC₀
    ε' δ hε' hδ c hc hc2 n hn ρO hρO
  obtain ⟨Cc, hCc, hc'⟩ := dbm_localErgodicity (𝕜 := ℂ) ϑ δm δp C₀ hϑ hδm hδp hC₀
    ε' δ hε' hδ c hc hc2 n hn ρO hρO
  refine ⟨max Cr Cc, lt_of_lt_of_le hCr (le_max_left _ _), ?_, ?_⟩
  · intro N hN M hM O Bd K hB hL hsupp E hE b hb hb2 t ht
    have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hB 0)
    have hK : (0 : ℝ) ≤ K := K.coe_nonneg
    refine (hr N hN M hM O Bd K hB hL hsupp E hE b hb hb2 t ht).trans ?_
    have := le_max_left Cr Cc
    gcongr
  · intro N hN M hM O Bd K hB hL hsupp E hE b hb hb2 t ht
    have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hB 0)
    have hK : (0 : ℝ) ≤ K := K.coe_nonneg
    refine (hc' N hN M hM O Bd K hB hL hsupp E hE b hb hb2 t ht).trans ?_
    have := le_max_right Cr Cc
    gcongr

/-- Corollary 19.5 (Hölder test functions), final form. -/
theorem dbm_localErgodicity_hoelder :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO → ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ N₂ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, N₂ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd Hα : ℝ, (∀ u, |O u| ≤ Bd) →
      (∀ u v, |O u - O v| ≤ Hα * ‖u - v‖ ^ α) → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + Hα) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2)) ^ α := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀ ε' δ hε' hδ c hc hc2 n hn ρO hρO α hα hα1
  obtain ⟨A₀, C, c', φ, N₀, hR⟩ := Endpoint_rigidityBound_tilde (𝕜 := 𝕜) (C₀ := C₀) hϑ hδm hδp
  exact dbm_localErgodicity_hoelder_of_rigidityBound hϑ hδm hδp hC₀ hR hε' hδ hc hc2 hn hρO hα
    hα1


/-! ### Instances

The parameters are `ϑ = δ₋ = δ₊ = C₀ = 1`, `c = 1`, `n = 2`, `ρ_O = 1`, `ε' = δ = 1/4`,
`α = 1/2`, and `𝕜` is an arbitrary `RCLike` field (in particular `ℝ` and `ℂ`).  The ensemble is
the Rademacher ensemble, `E = 0`, `b = 1/4`. -/

/-- Integral against the symmetric two-point law. -/
private lemma Endpoint_rademacherLaw_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (a : ℝ) (f : 𝕜 → F) :
    ∫ y, f y ∂rademacherLaw (𝕜 := 𝕜) a = (1 / 2 : ℝ) • (f a + f (-a)) := by
  unfold rademacherLaw
  rw [integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]

/-- The entries of the Rademacher ensemble have variance `1 / N`. -/
private lemma Endpoint_rademacher_var (N : ℕ) (p : Pair N) :
    (rademacher (𝕜 := 𝕜) N).varPair p = 1 / N := by
  unfold Ensemble.varPair rademacher
  simp only
  rw [Endpoint_rademacherLaw_integral]
  simp only [norm_neg, RCLike.norm_ofReal, sq_abs]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

/-- The Rademacher ensemble satisfies the hypotheses with `ϑ = δ₋ = δ₊ = C₀ = 1`: its entries are
bounded by their standard deviation, so (2.17) holds for every `ϑ`. -/
private lemma Endpoint_rademacher_one (N : ℕ) (hN : 0 < N) :
    (rademacher (𝕜 := 𝕜) N).Assumptions 1 1 1 1 := by
  have h := rademacher_assumptions (𝕜 := 𝕜) N hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨h.meanZero, h.diagReal, h.sumA, h.specB, h.boundC, ?_⟩
  intro p x hx
  have hpos : 0 < (Real.sqrt N)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hNr)
  have hv : (rademacher (𝕜 := 𝕜) N).varPair p = ((Real.sqrt N)⁻¹) ^ 2 := by
    rw [Endpoint_rademacher_var, inv_pow, Real.sq_sqrt hNr.le]
    simp
  have hsq : Real.sqrt ((rademacher (𝕜 := 𝕜) N).varPair p) = (Real.sqrt N)⁻¹ := by
    rw [hv, Real.sqrt_sq hpos.le]
  rw [hsq]
  change rademacherLaw (𝕜 := 𝕜) (Real.sqrt N)⁻¹ _ ≤ _
  have hm : MeasurableSet {y : 𝕜 | x * (Real.sqrt N)⁻¹ < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hxa : x * (Real.sqrt N)⁻¹ ≥ (Real.sqrt N)⁻¹ := by nlinarith
  unfold rademacherLaw
  rw [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ hm]
  simp only [Set.indicator, Set.mem_ofPred_eq, norm_neg, RCLike.norm_ofReal, abs_of_pos hpos,
    Pi.one_apply]
  simp [not_lt.mpr hxa]

/-- The test function `O(u) = max(0, 1 - ‖u‖)` on `ℝ²`. -/
private noncomputable def Endpoint_testO (u : EuclideanSpace ℝ (Fin 2)) : ℝ := max 0 (1 - ‖u‖)

private lemma Endpoint_testO_abs_le (u : EuclideanSpace ℝ (Fin 2)) : |Endpoint_testO u| ≤ 1 := by
  unfold Endpoint_testO
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (by linarith [norm_nonneg u])

private lemma Endpoint_testO_lip : LipschitzWith 1 Endpoint_testO := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  unfold Endpoint_testO
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, max_comm 0, max_comm 0 (1 - ‖v‖)]
  refine (abs_max_sub_max_le_abs (1 - ‖u‖) (1 - ‖v‖) 0).trans ?_
  rw [show 1 - ‖u‖ - (1 - ‖v‖) = ‖v‖ - ‖u‖ by ring, abs_sub_comm]
  exact abs_norm_sub_norm_le u v

private lemma Endpoint_testO_supp (u : EuclideanSpace ℝ (Fin 2)) (h : ∃ k, 1 < |u k|) :
    Endpoint_testO u = 0 := by
  obtain ⟨k, hk⟩ := h
  have := PiLp.norm_apply_le u k
  rw [Real.norm_eq_abs] at this
  unfold Endpoint_testO
  exact max_eq_left (by linarith)

private lemma Endpoint_testO_nonneg (u : EuclideanSpace ℝ (Fin 2)) : 0 ≤ Endpoint_testO u := by
  unfold Endpoint_testO
  exact le_max_left _ _

/-- The test function is not identically zero. -/
example : Endpoint_testO 0 = 1 := by simp [Endpoint_testO]

/-- The Hölder test function `O(u) = (max(0, 1 - ‖u‖))^{1/2}` on `ℝ²`. -/
private noncomputable def Endpoint_testH (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sqrt (Endpoint_testO u)

/-- `|√a - √b| ≤ √|a - b|` for `a, b ≥ 0`. -/
private lemma Endpoint_abs_sqrt_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  have key : ∀ x y : ℝ, 0 ≤ y → Real.sqrt x ≤ Real.sqrt y + Real.sqrt |x - y| := by
    intro x y hy
    rw [Real.sqrt_le_left (by positivity)]
    have h1 := Real.sq_sqrt hy
    have h2 := Real.sq_sqrt (abs_nonneg (x - y))
    have h3 : 0 ≤ Real.sqrt y * Real.sqrt |x - y| := by positivity
    have h4 := le_abs_self (x - y)
    nlinarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [key a b hb]
  · have := key b a ha
    rw [abs_sub_comm] at this
    linarith

private lemma Endpoint_testH_abs_le (u : EuclideanSpace ℝ (Fin 2)) : |Endpoint_testH u| ≤ 1 := by
  unfold Endpoint_testH
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
  exact (abs_le.1 (Endpoint_testO_abs_le u)).2

private lemma Endpoint_testH_hoelder (u v : EuclideanSpace ℝ (Fin 2)) :
    |Endpoint_testH u - Endpoint_testH v| ≤ 1 * ‖u - v‖ ^ (1 / 2 : ℝ) := by
  unfold Endpoint_testH
  rw [one_mul, ← Real.sqrt_eq_rpow]
  refine (Endpoint_abs_sqrt_sub_le (Endpoint_testO_nonneg u) (Endpoint_testO_nonneg v)).trans
    (Real.sqrt_le_sqrt ?_)
  have := Endpoint_testO_lip.dist_le_mul u v
  rwa [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm] at this

private lemma Endpoint_testH_supp (u : EuclideanSpace ℝ (Fin 2)) (h : ∃ k, 1 < |u k|) :
    Endpoint_testH u = 0 := by
  unfold Endpoint_testH
  rw [Endpoint_testO_supp u h, Real.sqrt_zero]

/-- The Hölder test function is not identically zero. -/
example : Endpoint_testH 0 = 1 := by simp [Endpoint_testH, Endpoint_testO]

/-- `(log N)² ≤ N` for `N ≥ 1`. -/
private lemma Endpoint_log_sq_le {N : ℕ} (hN : 1 ≤ N) : Real.log N ^ 2 ≤ N * 1 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set s := Real.sqrt (Real.sqrt N) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (Real.sqrt_pos.2 hN0)
  have hs2 : s ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = N := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hN0.le]
  have hlog : Real.log N = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos hs0
  have h0 : 0 ≤ Real.log N := Real.log_nonneg hNR
  have h2 : Real.log N ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 2)]
  rw [mul_one]
  calc Real.log N ^ 2 ≤ (s ^ 2) ^ 2 := pow_le_pow_left₀ h0 h2 2
    _ = N := by rw [← hs4]; ring

/-- Theorem 2.2 at the Rademacher ensemble: one constant tuple, and both events bounded at one
admissible pair `(N, L)`. -/
example : ∃ A₀ C c φ : ℝ, ∃ N₀ : ℕ, RigidityBound 𝕜 1 1 1 1 A₀ C c φ N₀ ∧
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ L : ℝ, LRange A₀ N L ∧
      (rademacher (𝕜 := 𝕜) N).prodLaw {x | ∃ k : Fin N, Real.log N ^ L *
          (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          |eig x k - gamma N k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
      (rademacher (𝕜 := 𝕜) N).prodLaw
          {x | Real.log N ^ L / N ≤ ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  obtain ⟨A₀, C, c, φ, N₀, hR⟩ := exists_rigidityBound (𝕜 := 𝕜) 1 1 1 1 one_pos one_pos one_pos
    one_pos
  obtain ⟨N₁, hL⟩ := exists_LRange_nonempty A₀
  set N := max (max N₀ N₁) 16
  obtain ⟨L, hLN⟩ := (hL N ((le_max_right _ _).trans (le_max_left _ _))).1
  exact ⟨A₀, C, c, φ, N₀, hR, N, (le_max_left _ _).trans (le_max_left _ _), L, hLN,
    hR.2.2.2.2.2 N ((le_max_left _ _).trans (le_max_left _ _)) _
      (Endpoint_rademacher_one N (by omega)) L hLN⟩

/-- Theorem 12.1 at the Rademacher ensemble, for the test function `Endpoint_testO` (`‖O‖_∞ ≤ 1`,
`Lip(O) ≤ 1`), `t = 1`, and every `N ≥ max(N_q, 2)`. -/
example : ∃ A₁ : ℝ, 1 ≤ A₁ ∧ ∃ Nq : ℕ, 3 ≤ Nq ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ N : ℕ, max Nq 2 ≤ N →
      corrLHS (rademacher (𝕜 := 𝕜) N) Endpoint_testO 0 (1 / 4) 1 ≤
        C₁ * (1 + ((1 : ℝ≥0) : ℝ)) * Real.exp (A₁ * Real.log (Real.log N) ^ 2) *
          ((1 / 4 : ℝ)⁻¹ * (N : ℝ)⁻¹ +
            (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * (N * 1) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨A₁, hA₁, Nq, hNq, C₁, hC₁, h⟩ := dbm_quantitative (𝕜 := 𝕜) 1 1 1 1 one_pos one_pos
    one_pos one_pos 1 one_pos (by norm_num) 2 (by norm_num) 1 one_pos
  refine ⟨A₁, hA₁, Nq, hNq, C₁, hC₁, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := hNq.trans ((le_max_left _ _).trans hN)
  exact h N hN _ (Endpoint_rademacher_one N (by omega)) Endpoint_testO 1 1
    Endpoint_testO_abs_le Endpoint_testO_lip Endpoint_testO_supp 1 one_pos
    (Endpoint_log_sq_le (by omega)) 0 (by norm_num) (1 / 4) (by norm_num) (by norm_num)

/-- Theorem 2.3, (2.36) at the Rademacher ensemble, with `t = N^{-1/2}` (the smallest admissible
time), for every `N ≥ 3`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
    corrLHS (rademacher (𝕜 := 𝕜) N) Endpoint_testO 0 (1 / 4) ((N : ℝ) ^ (-1 + 1 / 4 + 1 / 4 : ℝ)) ≤
      C * (1 + ((1 : ℝ≥0) : ℝ)) * (N : ℝ) ^ (2 * (1 / 4 : ℝ)) *
        ((1 / 4 : ℝ)⁻¹ * (N : ℝ) ^ (-1 + 1 / 4 : ℝ) +
          (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-(1 / 4 : ℝ) / 2)) := by
  obtain ⟨C, hC, h⟩ := dbm_localErgodicity (𝕜 := 𝕜) 1 1 1 1 one_pos one_pos one_pos one_pos
    (1 / 4) (1 / 4) (by norm_num) (by norm_num) 1 one_pos (by norm_num) 2 (by norm_num) 1 one_pos
  refine ⟨C, hC, fun N hN => ?_⟩
  exact h N (by omega) _ (Endpoint_rademacher_one N (by omega)) Endpoint_testO 1 1
    Endpoint_testO_abs_le Endpoint_testO_lip Endpoint_testO_supp 0 (by norm_num) (1 / 4)
    (by norm_num) (by norm_num) _ le_rfl

/-- Theorem 2.3 with one constant for both fields: the same `C` bounds the Rademacher ensembles
over `ℝ` and over `ℂ`, for every `N ≥ 3`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
    (corrLHS (rademacher (𝕜 := ℝ) N) Endpoint_testO 0 (1 / 4) ((N : ℝ) ^ (-1 + 1 / 4 + 1 / 4 : ℝ)) ≤
      C * (1 + ((1 : ℝ≥0) : ℝ)) * (N : ℝ) ^ (2 * (1 / 4 : ℝ)) *
        ((1 / 4 : ℝ)⁻¹ * (N : ℝ) ^ (-1 + 1 / 4 : ℝ) +
          (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-(1 / 4 : ℝ) / 2))) ∧
    (corrLHS (rademacher (𝕜 := ℂ) N) Endpoint_testO 0 (1 / 4) ((N : ℝ) ^ (-1 + 1 / 4 + 1 / 4 : ℝ)) ≤
      C * (1 + ((1 : ℝ≥0) : ℝ)) * (N : ℝ) ^ (2 * (1 / 4 : ℝ)) *
        ((1 / 4 : ℝ)⁻¹ * (N : ℝ) ^ (-1 + 1 / 4 : ℝ) +
          (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-(1 / 4 : ℝ) / 2))) := by
  obtain ⟨C, hC, hr, hc⟩ := dbm_localErgodicity_uniform 1 1 1 1 one_pos one_pos one_pos one_pos
    (1 / 4) (1 / 4) (by norm_num) (by norm_num) 1 one_pos (by norm_num) 2 (by norm_num) 1 one_pos
  refine ⟨C, hC, fun N hN => ⟨?_, ?_⟩⟩
  · exact hr N (by omega) _ (Endpoint_rademacher_one N (by omega)) Endpoint_testO
      1 1 Endpoint_testO_abs_le Endpoint_testO_lip Endpoint_testO_supp 0 (by norm_num) (1 / 4)
      (by norm_num) (by norm_num) _ le_rfl
  · exact hc N (by omega) _ (Endpoint_rademacher_one N (by omega)) Endpoint_testO
      1 1 Endpoint_testO_abs_le Endpoint_testO_lip Endpoint_testO_supp 0 (by norm_num) (1 / 4)
      (by norm_num) (by norm_num) _ le_rfl

/-- Corollary 19.5 at the Rademacher ensemble, for the Hölder test function `Endpoint_testH`
(`‖O‖_∞ ≤ 1`, `[O]_{1/2} ≤ 1`), `t = N^{-1/2}`, and every `N ≥ max(N₂, 1)`. -/
example : ∃ N₂ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, max N₂ 1 ≤ N →
    corrLHS (rademacher (𝕜 := 𝕜) N) Endpoint_testH 0 (1 / 4) ((N : ℝ) ^ (-1 + 1 / 4 + 1 / 4 : ℝ)) ≤
      C * (1 + 1) * (N : ℝ) ^ (2 * (1 / 4 : ℝ)) *
        ((1 / 4 : ℝ)⁻¹ * (N : ℝ)⁻¹ +
          (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-(1 / 4 : ℝ) / 2)) ^ (1 / 2 : ℝ) := by
  obtain ⟨N₂, C, hC, h⟩ := dbm_localErgodicity_hoelder (𝕜 := 𝕜) 1 1 1 1 one_pos one_pos one_pos
    one_pos (1 / 4) (1 / 4) (by norm_num) (by norm_num) 1 one_pos (by norm_num) 2 (by norm_num) 1
    one_pos (1 / 2) (by norm_num) (by norm_num)
  refine ⟨N₂, C, hC, fun N hN => ?_⟩
  exact h N ((le_max_left _ _).trans hN) _
    (Endpoint_rademacher_one N (lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)))
    Endpoint_testH 1 1 Endpoint_testH_abs_le Endpoint_testH_hoelder Endpoint_testH_supp 0
    (by norm_num) (1 / 4) (by norm_num) (by norm_num) _ le_rfl

end Rigidity
