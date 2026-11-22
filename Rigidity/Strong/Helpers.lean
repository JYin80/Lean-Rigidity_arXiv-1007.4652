module

public import Rigidity.LocalLaw.Lattice
public import Rigidity.Semicircle.Size

@[expose] public section

/-!
# Standing consequences of §7 (NP v1.1, §7: (T4)–(T6))

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file proves the three numerical consequences of the standing conditions of §7:

* `strong_T4` (T4): on `𝐃^near`, for every Hermitian `H`, one has `η ≥ N⁻¹`, `N η ≥ K^{C₁-1}`,
  `ϰ ≥ N^{-1/2}`, the bounds `η/150 ≤ Im m_sc ≤ ϰ` and `ϰ/1950 ≤ |m_sc (1 - m_sc²)| ≤ 4 ϰ`, and
  the crude bound `Λ ≤ 2N`;
* `strong_T5` (T5): for `1 ≤ K ≤ N^{c₀}`, the powers `K^b`, `K^{b+2}`, `K^{C₁-1}` are at most
  `N^{1/16}`, `N^{3/32}`, `N^{1/3}`;
* `strong_T6` (T6): for `z ∈ 𝕃` and `p ∈ {p₁, p₂}` and `N` large,
  `2N · ℙ(𝒢_col(z)ᶜ)^{1/p} ≤ N⁻⁸` and `2N (N¹⁰ e^{-p₁})^{1/p₂} ≤ N⁻⁸`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. Real-variable helpers -/

/-- `c₀` as an explicit reciprocal of an affine function. -/
private lemma helpers_c0_eq (a : ℝ) : ledgerc0 a = 1 / (192 * a + 288) := by
  unfold ledgerc0 ledgerC3
  congr 1
  ring

/-- `K ≤ N^c` and `c e ≤ t` give `K^e ≤ N^t`, for `N ≥ 1`, `K ≥ 0` and `e ≥ 0`. -/
private lemma helpers_rpow_le {K N c e t : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K) (hKN : K ≤ N ^ c)
    (he : 0 ≤ e) (h : c * e ≤ t) : K ^ e ≤ N ^ t :=
  calc K ^ e ≤ (N ^ c) ^ e := Real.rpow_le_rpow hK hKN he
    _ = N ^ (c * e) := (Real.rpow_mul (by linarith) c e).symm
    _ ≤ N ^ t := Real.rpow_le_rpow_of_exponent_le hN h

/-- The common estimate behind (T6): if `log B ≤ c + 10 log N - D` with `D ≥ 40 q log N`,
`q ≥ max 1 (log N)` and `2 e^c e^{10} ≤ N^{31}`, then `2N B^{1/q} ≤ N^{-8}`. -/
private lemma helpers_core {N q c D B : ℝ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hqL : Real.log N ≤ q)
    (hc : 0 ≤ c) (hB : 0 < B) (hlog : Real.log B ≤ c + 10 * Real.log N - D)
    (hD : 40 * q * Real.log N ≤ D) (hbig : 2 * Real.exp c * Real.exp 10 ≤ N ^ 31) :
    2 * N * B ^ (1 / q) ≤ N ^ (-8 : ℝ) := by
  have hNpos : 0 < N := by linarith
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hq0 : 0 < q := by linarith
  have h1 : Real.log B / q ≤ c + 10 - 40 * Real.log N := by
    rw [div_le_iff₀ hq0]
    nlinarith [mul_le_mul_of_nonneg_left hq hc]
  have h2 : B ^ (1 / q) ≤ Real.exp (c + 10 - 40 * Real.log N) := by
    rw [Real.rpow_def_of_pos hB]
    exact Real.exp_le_exp.2 (by rw [mul_one_div]; exact h1)
  have hN31 : Real.exp (31 * Real.log N) = N ^ 31 := by
    have := Real.exp_nat_mul (Real.log N) 31
    rw [Real.exp_log hNpos] at this
    simpa using this
  have hN8 : N ^ (-8 : ℝ) = Real.exp (-(8 * Real.log N)) := by
    rw [Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  have hNe : N = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
  calc 2 * N * B ^ (1 / q) ≤ 2 * N * Real.exp (c + 10 - 40 * Real.log N) := by gcongr
    _ = (2 * Real.exp c * Real.exp 10) * Real.exp (-(39 * Real.log N)) := by
        have h3 : 2 * N * Real.exp (c + 10 - 40 * Real.log N) =
            2 * Real.exp (Real.log N) * Real.exp (c + 10 - 40 * Real.log N) := by rw [← hNe]
        have h4 : Real.exp (Real.log N) * Real.exp (c + 10 - 40 * Real.log N) =
            Real.exp c * Real.exp 10 * Real.exp (-(39 * Real.log N)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [h3, mul_assoc, h4]
        ring
    _ ≤ N ^ 31 * Real.exp (-(39 * Real.log N)) := by
        gcongr
    _ = N ^ (-8 : ℝ) := by
        rw [← hN31, ← Real.exp_add, hN8]
        congr 1
        ring

/-! ### 2. (T4) -/

/-- (T4): sizes on `𝐃^near` (deterministic, any Hermitian `H`). -/
theorem strong_T4 {a K : ℝ} (ha : 1 ≤ a) (hK : 1 ≤ K) {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (hz : z ∈ Dnear a K N) (x : Pair N → 𝕜) :
    1 / N ≤ z.im ∧ K ^ (ledgerC1 a - 1) ≤ N * z.im ∧ 1 / Real.sqrt N ≤ varkappa z ∧
      z.im / 150 ≤ (msc z).im ∧ (msc z).im ≤ varkappa z ∧
      varkappa z / 1950 ≤ ‖msc z * (1 - msc z ^ 2)‖ ∧ ‖msc z * (1 - msc z ^ 2)‖ ≤ 4 * varkappa z ∧
      Lam x z ≤ 2 * N := by
  obtain ⟨hre, hη1, hη2⟩ := hz
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hC : 0 ≤ ledgerC1 a - 1 := by unfold ledgerC1; linarith
  have hKe : 1 ≤ K ^ (ledgerC1 a - 1) := Real.one_le_rpow hK hC
  have hη0 : 1 / (N : ℝ) ≤ z.im :=
    le_trans (div_le_div_of_nonneg_right hKe hNpos.le) hη1
  have hpos : 0 < z.im := lt_of_lt_of_le (by positivity) hη0
  have hNη : K ^ (ledgerC1 a - 1) ≤ N * z.im := by
    rwa [div_le_iff₀ hNpos, mul_comm] at hη1
  have hvk : 1 / Real.sqrt N ≤ varkappa z := by
    unfold varkappa
    have h : 1 / Real.sqrt N = Real.sqrt (1 / N) := by rw [one_div, one_div, Real.sqrt_inv]
    rw [h]
    refine Real.sqrt_le_sqrt ?_
    have := abs_nonneg (|z.re| - 2)
    unfold kappaE
    linarith
  obtain ⟨hs1, hs2, hs3, hs4⟩ := msc_size hre hpos hη2
  obtain ⟨hc1, hc2, -⟩ := msc_im_chain hre hpos hη2
  have hv0 : 0 ≤ varkappa z := Real.sqrt_nonneg _
  refine ⟨hη0, hNη, hvk, by linarith, hc2, ?_, ?_, ?_⟩
  · rw [norm_mul]
    have := mul_le_mul hs1 hs3 (by positivity) (norm_nonneg _)
    linarith
  · rw [norm_mul]
    have := mul_le_mul hs2 hs4 (norm_nonneg _) zero_le_one
    linarith
  · have hG : ∀ k : Fin N, ‖green (toMatrix x) z k k‖ ≤ 1 / z.im := fun k =>
      norm_green_apply_le (toMatrix_isHermitian x) hpos k k
    have htr : ‖(green (toMatrix x) z).trace‖ ≤ N * (1 / z.im) := by
      unfold Matrix.trace
      calc ‖∑ i, (green (toMatrix x) z).diag i‖ ≤ ∑ i, ‖(green (toMatrix x) z).diag i‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : Fin N, 1 / z.im := Finset.sum_le_sum fun i _ => hG i
        _ = N * (1 / z.im) := by simp
    have hcard : ‖((Fintype.card (Fin N) : ℂ))⁻¹‖ = 1 / N := by simp
    have hinv : 1 / z.im ≤ N := by
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hNpos] at hη0
      linarith
    unfold Lam stieltjesEmp
    calc ‖((Fintype.card (Fin N) : ℂ))⁻¹ * (green (toMatrix x) z).trace - msc z‖
        ≤ ‖((Fintype.card (Fin N) : ℂ))⁻¹ * (green (toMatrix x) z).trace‖ + ‖msc z‖ :=
          norm_sub_le _ _
      _ ≤ 1 / N * (N * (1 / z.im)) + 1 := by
          rw [norm_mul, hcard]
          gcongr
      _ = 1 / z.im + 1 := by field_simp
      _ ≤ 2 * N := by linarith

/-! ### 3. (T5) -/

/-- (T5): powers of `K` against powers of `N` (deterministic). -/
theorem strong_T5 {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hN : 1 ≤ N) {K : ℝ} (hK : 1 ≤ K)
    (hKN : K ≤ (N : ℝ) ^ ledgerc0 a) :
    K ^ ledgerB a ≤ (N : ℝ) ^ (1 / 16 : ℝ) ∧ K ^ (ledgerB a + 2) ≤ (N : ℝ) ^ (3 / 32 : ℝ) ∧
      K ^ (ledgerC1 a - 1) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := by linarith
  have hd : 0 < 192 * a + 288 := by linarith
  have hB0 : 0 ≤ ledgerB a := by unfold ledgerB; linarith
  obtain ⟨-, -, -, -, -, -, -, hL8, -⟩ := ledger_closes ha
  refine ⟨helpers_rpow_le hNr hK0 hKN hB0 ?_, helpers_rpow_le hNr hK0 hKN (by linarith) ?_,
    helpers_rpow_le hNr hK0 hKN (by unfold ledgerC1; linarith) hL8⟩
  · rw [helpers_c0_eq, one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    unfold ledgerB
    linarith
  · rw [helpers_c0_eq, one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    unfold ledgerB
    linarith

/-! ### 4. (T6) -/

/-- (T6): bad sets in `L^p`, for `z ∈ 𝕃` and `p ∈ {p₁, p₂}`. -/
theorem strong_T6 {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ lattice ϑ⁻¹ C₀ K N, ∀ p ∈ ({levelP1 K, levelP2 K} : Finset ℕ),
        ENNReal.ofReal (2 * N) * M.prodLaw (goodCol M ϑ⁻¹ C₀ K z)ᶜ ^ (1 / (p : ℝ)) ≤
          ENNReal.ofReal ((N : ℝ) ^ (-8 : ℝ)) ∧
        2 * N * ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ))) ^ (1 / (levelP2 K : ℝ)) ≤
          (N : ℝ) ^ (-8 : ℝ) := by
  obtain ⟨N₁, h1⟩ := lattice_card (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₂, h2⟩ := standing_ineq hϑ hϑ1 hC₀ 1
  have hA : 1 ≤ 460 / ϑ := by
    rw [le_div_iff₀ hϑ]
    linarith
  refine ⟨max (max N₁ N₂) ⌈2 * (460 / ϑ) * Real.exp 10⌉₊, fun N hN M hM K hK1 hK2 z hz p hp => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : (⌈2 * (460 / ϑ) * Real.exp 10⌉₊ : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨-, -, hlat⟩ := h1 N hN1 K hK1 hK2
  obtain ⟨⟨hK1', hN13, -, -⟩, -, ⟨hS3a, hS3b, hS3c, hS3d, -⟩, -⟩ := h2 N hN2 K hK1 hK2
  have hNr13 : (13 : ℝ) ≤ N := by exact_mod_cast hN13
  have hNr : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hKL : Real.log N ≤ K := by
    have h1 : 0 ≤ Real.log N - 1 := by linarith
    have h2 : 0 ≤ Real.log N := by linarith
    have : Real.log N ≤ Real.log N ^ 3 := by nlinarith [mul_nonneg h1 h2]
    linarith
  have hK1r : 1 ≤ K := by linarith
  -- sizes of `p₁` and `p₂`
  have hp1K : K ≤ (levelP1 K : ℝ) := by
    refine le_trans ?_ hS3d
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ ≤ K ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1r (by norm_num)
  have hp2le : (levelP2 K : ℝ) ≤ levelP1 K := by
    have h0 : (0 : ℝ) ≤ levelP2 K := Nat.cast_nonneg _
    nlinarith
  have hbig : 2 * (460 / ϑ) * Real.exp 10 ≤ (N : ℝ) ^ 31 := by
    have h := Nat.le_ceil (2 * (460 / ϑ) * Real.exp 10)
    have h' : ((⌈2 * (460 / ϑ) * Real.exp 10⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN3
    exact le_trans (le_trans h h') (le_self_pow₀ hNr (by norm_num))
  have hbig' : 2 * Real.exp 0 * Real.exp 10 ≤ (N : ℝ) ^ 31 := by
    rw [Real.exp_zero]
    refine le_trans ?_ hbig
    have := Real.exp_pos 10
    nlinarith
  refine ⟨?_, ?_⟩
  · -- the bad set
    have hpmem : (1 : ℝ) ≤ p ∧ Real.log N ≤ p ∧ 40 * (p : ℝ) * Real.log N ≤ K ^ 2 := by
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact ⟨by linarith, by linarith, hS3a⟩
      · rw [Finset.mem_singleton.1 hp]
        refine ⟨by linarith, by linarith, ?_⟩
        calc 40 * (levelP2 K : ℝ) * Real.log N ≤ 40 * (levelP1 K : ℝ) * Real.log N := by
              gcongr
          _ ≤ K ^ 2 := hS3a
    obtain ⟨hp1, hpL, hpK⟩ := hpmem
    have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hB : 0 < 460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-K ^ 2) := by positivity
    have hP := hlat M hM z hz
    have hreal : 2 * (N : ℝ) * (460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-K ^ 2)) ^ (1 / (p : ℝ)) ≤
        (N : ℝ) ^ (-8 : ℝ) := by
      refine helpers_core hNr hp1 hpL (Real.log_nonneg hA) hB ?_ hpK ?_
      · rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
          (by positivity), Real.log_pow, Real.log_exp]
        have := Real.log_nonneg hNr
        push_cast
        linarith
      · rwa [Real.exp_log (by linarith)]
    calc ENNReal.ofReal (2 * N) * M.prodLaw (goodCol M ϑ⁻¹ C₀ K z)ᶜ ^ (1 / (p : ℝ))
        ≤ ENNReal.ofReal (2 * N) *
            (ENNReal.ofReal (460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-K ^ 2))) ^ (1 / (p : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (2 * N * (460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-K ^ 2)) ^ (1 / (p : ℝ))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB.le hp0]
          exact (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-8 : ℝ)) := ENNReal.ofReal_le_ofReal hreal
  · -- the union bound
    have hq1 : (1 : ℝ) ≤ levelP2 K := by linarith
    have hqL : Real.log N ≤ (levelP2 K : ℝ) := by linarith
    have hB : 0 < (N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)) := by positivity
    refine helpers_core hNr hq1 hqL le_rfl hB ?_ hS3b ?_
    · rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]
      push_cast
      linarith
    · simpa using hbig'

end Rigidity
