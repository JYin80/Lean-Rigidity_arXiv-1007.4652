import Rigidity.Strong.Extension
import Rigidity.Strong.Norm

/-!
# The event `Ξ_K` (NP v1.1, §8.2: Definition 8.1, Proposition 8.2, Theorem 2.6 (i)–(iii))

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Definition 8.1: `Ξ_K = Ξ_K^{(1)} ∩ Ξ_K^{(2)}`. -/
noncomputable def XiK {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) : Set (Pair N → 𝕜) :=
  strongXi1 M a C₀ K ∩ strongXi2 M a C₀ K

/-! The proofs follow NP v1.1, §8.2. The complement of `Ξ_K` is the union of the complements of
`Ξ_K^{(1)}` (Proposition 7.2 and Lemma 7.5) and `Ξ_K^{(2)}` (Proposition 8.1). Both exponents
`p₁ = 2⌈K^{3/2}/2⌉` and `p₂ = 2⌈K/2⌉` are at least `K`, and `3 N²¹ e^{-K} ≤ e^{-K/2}` as soon as
`log N ≥ 7` and `K ≥ (log N)³`. For (i), (ii) the exponents `b + 5` and `b + 6` are at most
`C₂ = b + 7`, and (iii) is Proposition 8.1. -/

/-- Numerical step of Proposition 8.2: for `log N ≥ 7`, `K ≥ (log N)³` and `p₁, p₂ ≥ K`,
`2 N²¹ e^{-p₁} + N⁶ e^{-p₂} ≤ e^{-K/2}`. -/
private lemma event_numeric {N : ℕ} (hN : 1 ≤ N) {K p₁ p₂ : ℝ} (hL : 7 ≤ Real.log N)
    (hK : Real.log N ^ 3 ≤ K) (hp₁ : K ≤ p₁) (hp₂ : K ≤ p₂) :
    2 * (N : ℝ) ^ 21 * Real.exp (-p₁) + (N : ℝ) ^ 6 * Real.exp (-p₂) ≤ Real.exp (-K / 2) := by
  set L := Real.log N with hLdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow : (N : ℝ) ^ 21 = Real.exp (21 * L) := by
    rw [hLdef, ← Real.exp_log hNpos, ← Real.exp_nat_mul, Real.log_exp]
    push_cast
    rfl
  have hL2 : 49 ≤ L ^ 2 := by nlinarith
  have hK49 : 49 * L ≤ K := by
    have : L * 49 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by linarith)
    nlinarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2
    linarith
  have hN6 : (N : ℝ) ^ 6 ≤ (N : ℝ) ^ 21 := pow_le_pow_right₀ hN1 (by norm_num)
  have e1 : Real.exp (-p₁) ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (-p₂) ≤ Real.exp (-K) := Real.exp_le_exp.2 (by linarith)
  have hN21 : 0 ≤ (N : ℝ) ^ 21 := by positivity
  have hEK : 0 ≤ Real.exp (-K) := (Real.exp_pos _).le
  calc 2 * (N : ℝ) ^ 21 * Real.exp (-p₁) + (N : ℝ) ^ 6 * Real.exp (-p₂)
      ≤ 2 * (N : ℝ) ^ 21 * Real.exp (-K) + (N : ℝ) ^ 21 * Real.exp (-K) := by
        gcongr
    _ = 3 * (Real.exp (21 * L) * Real.exp (-K)) := by rw [hpow]; ring
    _ ≤ Real.exp 2 * (Real.exp (21 * L) * Real.exp (-K)) := by gcongr
    _ = Real.exp (2 + 21 * L + -K) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
    _ ≤ Real.exp (-K / 2) := Real.exp_le_exp.2 (by linarith)

/-- Proposition 8.2: `Ξ_K` is closed and `ℙ(Ξ_Kᶜ) ≤ 2N^{21} e^{-p₁} + N⁶ e^{-p₂} ≤ e^{-K/2}`. -/
theorem prob_XiK {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
        IsClosed (XiK M ϑ⁻¹ C₀ K) ∧
        M.prodLaw (XiK M ϑ⁻¹ C₀ K)ᶜ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ 21 *
          Real.exp (-(levelP1 K : ℝ)) + (N : ℝ) ^ 6 * Real.exp (-(levelP2 K : ℝ))) ∧
        M.prodLaw (XiK M ϑ⁻¹ C₀ K)ᶜ ≤ ENNReal.ofReal (Real.exp (-K / 2)) := by
  obtain ⟨N₁, h1⟩ := localLaw_i_ii (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := norm_bound_strongXi2 (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₃, h3⟩ := standing_ineq hϑ hϑ1 hC₀ 1
  refine ⟨max (max (max N₁ N₂) N₃) ⌈Real.exp 7⌉₊, ?_⟩
  intro N hN M hM K hK1 hK2
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN7 : Real.exp 7 ≤ N := Nat.ceil_le.1 (by omega)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 7) hN7
  have hL7 : 7 ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).2 hN7
  obtain ⟨⟨hK0, h13, -, -⟩, -, ⟨-, -, hp2, hp1, -⟩, -⟩ := h3 N hN3 K hK1 hK2
  have hKp1 : K ≤ (levelP1 K : ℝ) := by
    refine le_trans ?_ hp1
    calc K = K ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK0 (by norm_num)
  obtain ⟨hc1, hp1', -⟩ := h1 N hN1 M hM K hK1 hK2
  obtain ⟨hc2, hp2', -⟩ := h2 N hN2 M hM K hK1 hK2
  have hunion : M.prodLaw (XiK M ϑ⁻¹ C₀ K)ᶜ ≤
      M.prodLaw (strongXi1 M ϑ⁻¹ C₀ K)ᶜ + M.prodLaw (strongXi2 M ϑ⁻¹ C₀ K)ᶜ := by
    rw [XiK, Set.compl_inter]
    exact measure_union_le _ _
  have hfirst : M.prodLaw (XiK M ϑ⁻¹ C₀ K)ᶜ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ 21 *
      Real.exp (-(levelP1 K : ℝ)) + (N : ℝ) ^ 6 * Real.exp (-(levelP2 K : ℝ))) := by
    refine hunion.trans ((add_le_add hp1' hp2').trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have : (N : ℝ) ^ 20 ≤ (N : ℝ) ^ 21 := pow_le_pow_right₀ hN1' (by norm_num)
    have hE : 0 ≤ Real.exp (-(levelP1 K : ℝ)) := (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_right this hE]
  refine ⟨hc1.inter hc2, hfirst, hfirst.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact event_numeric (by omega) hL7 hK1 hKp1 hp2

/-- Theorem 2.6 (i)–(iii) at every point of `Ξ_K`, for all `z ∈ D_K` simultaneously. -/
theorem localLaw_i_iii {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ x ∈ XiK M ϑ⁻¹ C₀ K,
        (∀ z ∈ DK ϑ⁻¹ N K, Lam x z ≤ K ^ ledgerC2 ϑ⁻¹ / (N * z.im)) ∧
        (∀ z ∈ DK ϑ⁻¹ N K, LamD x z + LamO x z ≤
          K ^ ledgerC2 ϑ⁻¹ * (Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im))) ∧
        ∀ k, |eig x k| ≤ 2 + K ^ ledgerC3 ϑ⁻¹ * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨N₁, h1⟩ := localLaw_i_ii (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := norm_bound_strongXi2 (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₃, h3⟩ := standing_ineq hϑ hϑ1 hC₀ 1
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN M hM K hK1 hK2 x hx
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  obtain ⟨⟨hK0, h13, -, -⟩, -, -, -⟩ := h3 N hN3 K hK1 hK2
  have ha : (1 : ℝ) ≤ ϑ⁻¹ := one_le_inv₀ hϑ |>.2 hϑ1
  have hC2 : ledgerB ϑ⁻¹ + 7 ≤ ledgerC2 ϑ⁻¹ := (ledger_closes ha).2.2.2.2.2.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow5 : K ^ (ledgerB ϑ⁻¹ + 5) ≤ K ^ ledgerC2 ϑ⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hK0 (by linarith)
  have hpow6 : K ^ (ledgerB ϑ⁻¹ + 6) ≤ K ^ ledgerC2 ϑ⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hK0 (by linarith)
  obtain ⟨-, -, hi⟩ := h1 N hN1 M hM K hK1 hK2
  obtain ⟨-, -, hiii⟩ := h2 N hN2 M hM K hK1 hK2
  have hDK : ∀ z ∈ DK ϑ⁻¹ N K, 0 < (N : ℝ) * z.im := fun z hz => by
    have : 0 < K ^ ledgerC1 ϑ⁻¹ / N := by
      have : 0 < K := lt_of_lt_of_le one_pos hK0
      positivity
    exact mul_pos hNpos (lt_of_lt_of_le this hz.2.1)
  refine ⟨fun z hz => ?_, fun z hz => ?_, hiii x hx.2⟩
  · exact ((hi x hx.1 z hz).1).trans (div_le_div_of_nonneg_right hpow5 (hDK z hz).le)
  · refine ((hi x hx.1 z hz).2).trans (mul_le_mul_of_nonneg_right hpow6 ?_)
    have := hDK z hz
    positivity

end Rigidity
