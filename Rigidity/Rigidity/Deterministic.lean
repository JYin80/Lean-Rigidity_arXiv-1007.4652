module

public import Rigidity.Rigidity.Conversion
public import Rigidity.LocalLaw.Ledger
public import Rigidity.Resolvent.Spectral

@[expose] public section

/-!
# Counting function and rigidity from the local law (NP v1.1, §9: Proposition 9.2)

Numbers in this file refer to the blueprint NP v1.1; the original argument is in the proof of
[EYY, Theorem 2.2] (Erdős–Yau–Yin, arXiv:1007.4652).

`rigidity_of_localLaw` is Proposition 9.2: if `‖m - m_sc‖ ≤ K^{C₂} / (N η)` on
`{|E| ≤ 7/2, K^{C₁}/N ≤ η ≤ 2}` and `max_j |λ_j| ≤ 2 + K^{C₃} N^{-2/3}`, then
`sup_E |𝔫 - n_sc| ≤ K^{C₅} / N` and `|λ_j - γ_j| ≤ K^{C₄} ĵ^{-1/3} N^{-2/3}`, with the exponents
of the ledger (Lemma A.1) and `(log N)³ ≤ K ≤ N^{c₀}`.

The counting bound applies Lemma 3.16 on `[-3, E]` with `η = K^{C₁}/N` and `U = K^{C₂}`, the
eigenvalues lying in `(-3, 3)`; the rigidity bound applies Lemma 9.1 with `Δ = K^{C₅}` and
`ω = K^{C₃} N^{-2/3}`. The exponent relations (L9)–(L11) of Lemma A.1 absorb the constants.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Elementary lemmas -/

/-- `(x ^ (1/3)) ^ 3 = x` for `x ≥ 0`. -/
private lemma rigDet_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `x ^ (2/3) = (x ^ (1/3)) ^ 2` for `x ≥ 0`. -/
private lemma rigDet_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 / 3 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- If all `λ_k ≤ E` then the counting function at `E` is `1`. -/
private lemma rigDet_countOf_top {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E : ℝ}
    (h : ∀ k, lam k ≤ E) : countOf lam E = 1 := by
  unfold countOf
  rw [Finset.filter_true_of_mem (fun k _ => h k), Finset.card_univ, Fintype.card_fin]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- If all `λ_k > E` then the counting function at `E` is `0`. -/
private lemma rigDet_countOf_bot {N : ℕ} (lam : Fin N → ℝ) {E : ℝ} (h : ∀ k, E < lam k) :
    countOf lam E = 0 := by
  unfold countOf
  rw [Finset.filter_false_of_mem (fun k _ => not_le.2 (h k))]
  simp

/-- `ĵ ≥ 1`. -/
private lemma rigDet_rigWeight_one_le {N : ℕ} (k : Fin N) : (1 : ℝ) ≤ (rigWeight N k : ℝ) := by
  have h : 1 ≤ rigWeight N k := by
    unfold rigWeight
    have := k.isLt
    omega
  exact_mod_cast h

/-- A power `K ^ C` with `K ≤ N ^ c₀` and `c₀ C ≤ 1/8` is at most `N ^ (1/8)`. -/
private lemma rigDet_K_le {K N C c₀ : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K) (hKN : K ≤ N ^ c₀)
    (hC : 0 ≤ C) (h : c₀ * C ≤ 1 / 8) : K ^ C ≤ N ^ (1 / 8 : ℝ) := by
  calc K ^ C ≤ (N ^ c₀) ^ C := Real.rpow_le_rpow hK hKN hC
    _ = N ^ (c₀ * C) := (Real.rpow_mul (by linarith) _ _).symm
    _ ≤ N ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN h

/-- Numerical consequences of `N ≥ e⁶` and `(log N)³ ≤ K ≤ N ^ c₀`. -/
private lemma rigDet_numerics {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hN : Real.exp 6 ≤ N) {K : ℝ}
    (hK1 : Real.log N ^ 3 ≤ K) (hK2 : K ≤ (N : ℝ) ^ ledgerc0 a) :
    216 ≤ K ∧ Real.log N ≤ K ^ (1 / 3 : ℝ) ∧
      K ^ ledgerC1 a ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧ K ^ ledgerC3 a ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
      K ^ ledgerC5 a ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧ (N : ℝ) ^ (1 / 8 : ℝ) * 100 ≤ N ∧
      (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) < 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, L11, -, -, -, -, -, hc0⟩ := ledger_closes ha
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 6) hN
  have hN1' : (1 : ℝ) < N := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (by norm_num)) hN
  have hN1 : (1 : ℝ) ≤ N := hN1'.le
  have hlog : (6 : ℝ) ≤ Real.log N := by
    calc (6 : ℝ) = Real.log (Real.exp 6) := (Real.log_exp 6).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 6) hN
  have hK216 : (216 : ℝ) ≤ K := by
    calc (216 : ℝ) = 6 ^ 3 := by norm_num
      _ ≤ Real.log N ^ 3 := pow_le_pow_left₀ (by norm_num) hlog 3
      _ ≤ K := hK1
  have hK0 : 0 ≤ K := by linarith
  refine ⟨hK216, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : 0 ≤ Real.log N := by linarith
    have : (Real.log N ^ 3) ^ (1 / 3 : ℝ) ≤ K ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hK1 (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul h0, show ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num,
      Real.rpow_one] at this
  · exact rigDet_K_le hN1 hK0 hK2 (by unfold ledgerC1; linarith)
      ((mul_le_mul_of_nonneg_left (le_max_left _ _) hc0.le).trans L11)
  · exact rigDet_K_le hN1 hK0 hK2 (by unfold ledgerC3; linarith)
      ((mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) hc0.le).trans L11)
  · exact rigDet_K_le hN1 hK0 hK2 (by unfold ledgerC5; linarith)
      ((mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) hc0.le).trans L11)
  · -- `N ^ (7/8) ≥ 100`, hence `N ^ (1/8) ≤ N / 100`
    have hN78 : (100 : ℝ) ≤ (N : ℝ) ^ (7 / 8 : ℝ) := by
      have h1 : Real.exp (21 / 4) ≤ (N : ℝ) ^ (7 / 8 : ℝ) := by
        calc Real.exp (21 / 4) = (Real.exp 6) ^ (7 / 8 : ℝ) := by
              rw [← Real.exp_mul]; norm_num
          _ ≤ (N : ℝ) ^ (7 / 8 : ℝ) := Real.rpow_le_rpow (Real.exp_pos 6).le hN (by norm_num)
      have h2 : (100 : ℝ) ≤ Real.exp (21 / 4) := by
        have h3 : Real.exp 5 ≤ Real.exp (21 / 4) := Real.exp_le_exp.2 (by norm_num)
        have h4 : Real.exp 5 = Real.exp 1 ^ 5 := by
          rw [← Real.exp_nat_mul]; norm_num
        have h6 := Real.exp_one_gt_d9
        have h7 : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 5
        have h8 : (100 : ℝ) ≤ 2.7 ^ 5 := by norm_num
        linarith
      linarith
    have : (N : ℝ) = (N : ℝ) ^ (1 / 8 : ℝ) * (N : ℝ) ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_add hNpos]; norm_num
    have h0 : 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg hNpos.le _
    nlinarith
  · rw [← Real.rpow_add hNpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hN1' (by norm_num)

/-- The counting bound `10 / N (U log (2 / η) + N η) ≤ K ^ C₅ / N` at `η = K ^ C₁ / N`,
`U = K ^ C₂`. -/
private lemma rigDet_count_arith {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hNpos : (0 : ℝ) < N)
    {K : ℝ} (hK216 : 216 ≤ K) (hlogK : Real.log N ≤ K ^ (1 / 3 : ℝ))
    (hlog : (1 : ℝ) ≤ Real.log N) :
    10 / N * (K ^ ledgerC2 a * Real.log (2 / (K ^ ledgerC1 a / N)) +
      N * (K ^ ledgerC1 a / N)) ≤ K ^ ledgerC5 a / N := by
  obtain ⟨-, -, -, -, -, -, -, -, L9, -, -, hC1, hC2, -, -, -, -⟩ := ledger_closes ha
  have hK0 : 0 < K := by linarith
  have hK1' : 1 ≤ K := by linarith
  have hKC1pos : 0 < K ^ ledgerC1 a := Real.rpow_pos_of_pos hK0 _
  have hlogb : Real.log (2 / (K ^ ledgerC1 a / N)) ≤ 2 * K ^ (1 / 3 : ℝ) := by
    have h2 : 2 / (K ^ ledgerC1 a / N) ≤ 2 * N := by
      rw [div_div_eq_mul_div]
      exact div_le_self (by positivity) (Real.one_le_rpow hK1' (by linarith))
    have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    calc Real.log (2 / (K ^ ledgerC1 a / N)) ≤ Real.log (2 * N) :=
          Real.log_le_log (by positivity) h2
      _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) hNpos.ne'
      _ ≤ 2 * K ^ (1 / 3 : ℝ) := by linarith
  have hB1 : K ^ ledgerC1 a ≤ K ^ (ledgerC5 a - 1) :=
    Real.rpow_le_rpow_of_exponent_le hK1'
      (by linarith [le_max_left (ledgerC1 a) (ledgerC2 a + 1 / 3)])
  have hB2 : K ^ (ledgerC2 a + 1 / 3) ≤ K ^ (ledgerC5 a - 1) :=
    Real.rpow_le_rpow_of_exponent_le hK1'
      (by linarith [le_max_right (ledgerC1 a) (ledgerC2 a + 1 / 3)])
  have hK5 : K ^ ledgerC5 a = K * K ^ (ledgerC5 a - 1) := by
    rw [Real.rpow_sub_one hK0.ne']; field_simp
  have hmul : K ^ ledgerC2 a * K ^ (1 / 3 : ℝ) = K ^ (ledgerC2 a + 1 / 3) :=
    (Real.rpow_add hK0 _ _).symm
  have hU0 : 0 ≤ K ^ ledgerC2 a := by positivity
  have hB0 : 0 ≤ K ^ (ledgerC5 a - 1) := by positivity
  rw [mul_div_cancel₀ _ hNpos.ne', div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]
  have h4 : K ^ ledgerC2 a * Real.log (2 / (K ^ ledgerC1 a / N)) ≤ 2 * K ^ (ledgerC5 a - 1) := by
    calc K ^ ledgerC2 a * Real.log (2 / (K ^ ledgerC1 a / N))
        ≤ K ^ ledgerC2 a * (2 * K ^ (1 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hlogb hU0
      _ = 2 * K ^ (ledgerC2 a + 1 / 3) := by rw [← hmul]; ring
      _ ≤ 2 * K ^ (ledgerC5 a - 1) := by linarith
  have h30 : 30 * K ^ (ledgerC5 a - 1) ≤ K * K ^ (ledgerC5 a - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hB0
  linarith

/-- The final comparison of Proposition 9.2: the bound of Lemma 9.1 with `Δ = K ^ C₅` and
`ω = K ^ C₃ N ^ (-2/3)` is at most `K ^ C₄ ĵ ^ (-1/3) N ^ (-2/3)`. -/
private lemma rigDet_final_arith {a : ℝ} (ha : 1 ≤ a) {K J s : ℝ} (hK216 : 216 ≤ K)
    (hJ1 : 1 ≤ J) (hs0 : 0 < s) :
    9 * K ^ ledgerC5 a * J ^ (-(1 / 3 : ℝ)) * s +
      (if J ≤ 3 * K ^ ledgerC5 a then
        K ^ ledgerC3 a * s + 9 * (K ^ ledgerC5 a) ^ (2 / 3 : ℝ) * s else 0) ≤
      K ^ ledgerC4 a * J ^ (-(1 / 3 : ℝ)) * s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, L10, -, -, -, -, -, -, -⟩ := ledger_closes ha
  have hK0 : 0 < K := by linarith
  have hK1' : 1 ≤ K := by linarith
  have hΔ : 1 ≤ K ^ ledgerC5 a := Real.one_le_rpow hK1' (by unfold ledgerC5; linarith)
  have hw0 : 0 < J ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hws : 0 < J ^ (-(1 / 3 : ℝ)) * s := mul_pos hw0 hs0
  have hD1 : K ^ ledgerC5 a ≤ K ^ (ledgerC4 a - 1) :=
    Real.rpow_le_rpow_of_exponent_le hK1'
      (by linarith [le_max_left (ledgerC5 a) (ledgerC3 a + ledgerC5 a / 3)])
  have hD2 : K ^ ledgerC3 a * K ^ (ledgerC5 a / 3) ≤ K ^ (ledgerC4 a - 1) := by
    rw [← Real.rpow_add hK0]
    exact Real.rpow_le_rpow_of_exponent_le hK1'
      (by linarith [le_max_right (ledgerC5 a) (ledgerC3 a + ledgerC5 a / 3)])
  have hK4 : K ^ ledgerC4 a = K * K ^ (ledgerC4 a - 1) := by
    rw [Real.rpow_sub_one hK0.ne']; field_simp
  have hD0 : 0 ≤ K ^ (ledgerC4 a - 1) := by positivity
  split_ifs with hj
  · -- the edge regime `ĵ ≤ 3 K ^ C₅`
    set u : ℝ := K ^ (ledgerC5 a / 3) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hK0 _
    have hu1 : (K ^ ledgerC5 a) ^ (1 / 3 : ℝ) = u := by
      rw [← Real.rpow_mul hK0.le, hu, mul_one_div]
    have hu3 : u ^ 3 = K ^ ledgerC5 a := by rw [← hu1]; exact rigDet_cube (by positivity)
    have hu2 : (K ^ ledgerC5 a) ^ (2 / 3 : ℝ) = u ^ 2 := by
      rw [rigDet_two_thirds (by positivity), hu1]
    have hv0 : 0 < J ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hvle : J ^ (1 / 3 : ℝ) ≤ 2 * u := by
      refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
      rw [rigDet_cube (by linarith), mul_pow, hu3]
      norm_num
      linarith
    have hwu : 1 ≤ 2 * u * J ^ (-(1 / 3 : ℝ)) := by
      rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, one_le_div hv0]
      exact hvle
    have h_om : K ^ ledgerC3 a * s ≤
        2 * (K ^ ledgerC3 a * u) * (J ^ (-(1 / 3 : ℝ)) * s) := by
      calc K ^ ledgerC3 a * s = K ^ ledgerC3 a * s * 1 := (mul_one _).symm
        _ ≤ K ^ ledgerC3 a * s * (2 * u * J ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hwu (by positivity)
        _ = 2 * (K ^ ledgerC3 a * u) * (J ^ (-(1 / 3 : ℝ)) * s) := by ring
    have h_d : 9 * u ^ 2 * s ≤ 18 * K ^ ledgerC5 a * (J ^ (-(1 / 3 : ℝ)) * s) := by
      rw [← hu3]
      calc 9 * u ^ 2 * s = 9 * u ^ 2 * s * 1 := (mul_one _).symm
        _ ≤ 9 * u ^ 2 * s * (2 * u * J ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hwu (by positivity)
        _ = 18 * u ^ 3 * (J ^ (-(1 / 3 : ℝ)) * s) := by ring
    rw [hu2]
    have hfin : (27 * K ^ ledgerC5 a + 2 * (K ^ ledgerC3 a * u)) * (J ^ (-(1 / 3 : ℝ)) * s) ≤
        K * K ^ (ledgerC4 a - 1) * (J ^ (-(1 / 3 : ℝ)) * s) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hws.le
    rw [hK4]
    nlinarith
  · -- the bulk regime
    rw [add_zero, hK4]
    have h1 : 9 * K ^ ledgerC5 a ≤ K * K ^ (ledgerC4 a - 1) := by nlinarith
    have h2 : 9 * K ^ ledgerC5 a * (J ^ (-(1 / 3 : ℝ)) * s) ≤
        K * K ^ (ledgerC4 a - 1) * (J ^ (-(1 / 3 : ℝ)) * s) :=
      mul_le_mul_of_nonneg_right h1 hws.le
    nlinarith

/-- Proposition 9.2: counting function and rigidity from the local law (deterministic). -/
theorem rigidity_of_localLaw {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hN : Real.exp 6 ≤ N) {K : ℝ}
    (hK1 : Real.log N ^ 3 ≤ K) (hK2 : K ≤ (N : ℝ) ^ ledgerc0 a)
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (h1 : ∀ z : ℂ, |z.re| ≤ 7 / 2 → K ^ ledgerC1 a / N ≤ z.im → z.im ≤ 2 →
      LamM A z ≤ K ^ ledgerC2 a / (N * z.im))
    (h3 : ∀ k, |eigAsc hA k| ≤ 2 + K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ))) :
    (∀ E, |countOf (eigAsc hA) E - nsc E| ≤ K ^ ledgerC5 a / N) ∧
      ∀ k, |eigAsc hA k - gamma N k| ≤
        K ^ ledgerC4 a * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨hK216, hlogK, hKC1, hKC3, hKC5, hN18, hN18s⟩ := rigDet_numerics ha hN hK1 hK2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hC1, hC2, hC3, hC4, hC5, hc0⟩ := ledger_closes ha
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 6) hN
  have hNn : 0 < N := by exact_mod_cast hNpos
  have hlog : (6 : ℝ) ≤ Real.log N := by
    calc (6 : ℝ) = Real.log (Real.exp 6) := (Real.log_exp 6).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 6) hN
  have hN1 : (1 : ℝ) ≤ N := by
    calc (1 : ℝ) ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
      _ ≤ N := hN
  have hK0 : 0 < K := by linarith
  have hK1' : 1 ≤ K := by linarith
  have hs0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hKs : K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) <
      1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hKC3 hs0.le) hN18s
  have hη0 : 0 < K ^ ledgerC1 a / N := by positivity
  have hη2 : K ^ ledgerC1 a / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hU : 1 ≤ K ^ ledgerC2 a := Real.one_le_rpow hK1' (by linarith)
  -- all eigenvalues lie in `(-3, 3)`
  have hlam : ∀ k, |eigAsc hA k| < 3 := fun k => by linarith [h3 k]
  -- the counting function
  have hcount : ∀ E, |countOf (eigAsc hA) E - nsc E| ≤ K ^ ledgerC5 a / N := by
    intro E
    have hbd : 0 ≤ K ^ ledgerC5 a / N := by positivity
    by_cases hE3 : 3 ≤ E
    · rw [rigDet_countOf_top hNn (eigAsc hA) fun k => (abs_lt.1 (hlam k)).2.le.trans hE3,
        nsc_props.2.2.2.2.1 E (by linarith)]
      simpa using hbd
    by_cases hE3' : E ≤ -3
    · rw [rigDet_countOf_bot (eigAsc hA) fun k => lt_of_le_of_lt hE3' (abs_lt.1 (hlam k)).1,
        nsc_props.2.2.2.1 E (by linarith)]
      simpa using hbd
    have hE3 := not_le.1 hE3
    have hE3' := not_le.1 hE3'
    -- Lemma 3.16 with `E₁ = -3`, `E₂ = E`, `η = K ^ C₁ / N`, `U = K ^ C₂`
    have hreg : ∀ x ∈ Set.Icc (-3 - K ^ ledgerC1 a / N) (E + K ^ ledgerC1 a / N),
        ∀ y ∈ Set.Icc (K ^ ledgerC1 a / N) 2,
        ‖stieltjesOf (eigAsc hA) (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤
          K ^ ledgerC2 a / (N * y) := by
      intro x hx y hy
      have hy0 : 0 < (x + y * Complex.I).im := by simp; linarith [hy.1]
      have hS : stieltjesOf (eigAsc hA) (x + y * Complex.I) =
          stieltjesEmp A (x + y * Complex.I) := by
        rw [stieltjesEmp_eq_sum hA hy0]; rfl
      rw [hS]
      have hx' : |(x + y * Complex.I).re| ≤ 7 / 2 := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im]
        rw [abs_le]
        constructor <;> nlinarith [hx.1, hx.2]
      have := h1 (x + y * Complex.I) hx' (by simpa using hy.1) (by simpa using hy.2)
      simpa [LamM] using this
    have hmid := count_from_stieltjes hNn (eigAsc hA) (E₁ := -3) (E₂ := E) hE3'
      (by linarith) hη0 hη2 hU hreg
    rw [rigDet_countOf_bot (eigAsc hA) fun k => (abs_lt.1 (hlam k)).1,
      nsc_props.2.2.2.1 (-3) (by norm_num), sub_zero, sub_zero] at hmid
    exact hmid.trans (rigDet_count_arith ha hNpos hK216 hlogK (by linarith))
  -- rigidity
  refine ⟨hcount, fun k => ?_⟩
  have hΔ : 1 ≤ K ^ ledgerC5 a := Real.one_le_rpow hK1' (by linarith)
  have hω0 : 0 ≤ K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have hΔN : 100 * K ^ ledgerC5 a ≤ N := by nlinarith
  have hlo : ∀ k, -2 - K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ eigAsc hA k :=
    fun k => by linarith [(abs_le.1 (h3 k)).1]
  have hhi : ∀ k, eigAsc hA k ≤ 2 + K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
    fun k => (abs_le.1 (h3 k)).2
  refine (rigidity_of_counting (eigAsc hA) (eigAsc_monotone hA) hΔ hω0 hKs.le hΔN hcount hlo
    hhi k).trans ?_
  exact rigDet_final_arith ha hK216 (rigDet_rigWeight_one_le k) hs0

end Rigidity
