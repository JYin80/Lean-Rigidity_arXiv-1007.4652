import Rigidity.LocalLaw.WeakOnePoint
import Rigidity.Semicircle.Size

/-!
# Weak dichotomy (NP v1.1, §5.2: Lemma 5.2)

Numbers in this file refer to the blueprint NP v1.1.
-/

/-!
The statement is deterministic at a point `x` of the event `𝒢(z) ∩ {Λ_d + Λ_o ≤ λ_st}`, for one
fixed `z ∈ 𝐃^near`. The proof reduces it to elementary inequalities between the real numbers
`𝔏`, `u = Nη`, `ϰ`, `Λ`, `|w₀|`, `Im m_sc` and `Ψ`, using (5.2′), (5.3), (5.5) of Lemma 5.1, the
sizes (3.3) of Lemma 3.2, and the standing inequalities (S1), (S2) of Lemma 4.6. The constants
are `C = 2·10⁴ C_a` and `U_w = 7800 C`, with `C_a = 3·10⁶ C_s²` of (5.2′).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `ϰ_w(z) = U_w 𝔏^{2/3} (Nη)^{-1/3}` of Lemma 5.2. -/
noncomputable def weakKw (U a C₀ K : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  U * levelFL a C₀ K N ^ (2 / 3 : ℝ) * ((N : ℝ) * z.im) ^ (-(1 / 3 : ℝ))

/-! ### 1. Elementary inequalities

Throughout, `u = Nη`, `y = 𝔏^{2/3} u^{-1/3}` (so `y³ u = 𝔏²`), `Λ = |w|`, `W = |w₀|`,
`s = Im m_sc` and `Ψ = r + 1/u` with `r = √((s + Λ)/u)` (so `r² u = s + Λ`). -/

/-- Part (a) of Lemma 5.2: if `Λ² ≤ WΛ + C_a 𝔏 Ψ + (3/10) Λ²`, `W ≤ 4ϰ` and `s ≤ ϰ`, then
`Λ ≤ 64 C_a (ϰ + y)`. -/
private lemma weakDichotomy_partA {Ca L u κ y Λ W s r : ℝ} (hCa : 1 ≤ Ca) (hL : 1 ≤ L)
    (hu : 0 < u) (hκ : 0 ≤ κ) (hy0 : 0 < y) (hy1 : y ≤ 1) (hy3 : y ^ 3 * u = L ^ 2)
    (hΛ0 : 0 ≤ Λ) (hW : W ≤ 4 * κ) (hs1 : s ≤ κ) (hr0 : 0 ≤ r)
    (hr2 : r ^ 2 * u = s + Λ)
    (hQ : Λ ^ 2 ≤ W * Λ + Ca * L * (r + 1 / u) + 3 / 10 * Λ ^ 2) :
    Λ ≤ 64 * Ca * (κ + y) := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  set M := 64 * Ca with hM
  have hM64 : 64 ≤ M := by linarith
  have hΛpos : 0 < Λ := lt_of_le_of_lt (by positivity) hlt
  have hκM : M * κ ≤ Λ := by nlinarith
  have hyM : M * y ≤ Λ := by nlinarith
  have hκΛ : κ ≤ Λ := by nlinarith
  -- `W Λ ≤ Λ²/16`
  have h1 : W * Λ ≤ Λ ^ 2 / 16 := by
    have e1 : W * Λ ≤ 4 * κ * Λ := mul_le_mul_of_nonneg_right hW hΛ0
    have e2 : M * (W * Λ) ≤ M * (4 * κ * Λ) := mul_le_mul_of_nonneg_left e1 (by linarith)
    have e3 : M * (4 * κ * Λ) = 4 * Λ * (M * κ) := by ring
    have e4 : 4 * Λ * (M * κ) ≤ 4 * Λ * Λ := mul_le_mul_of_nonneg_left hκM (by linarith)
    nlinarith
  -- `C_a 𝔏 r ≤ Λ²/4`
  have h2 : Ca * L * r ≤ Λ ^ 2 / 4 := by
    have e1 : (L * r) ^ 2 = y ^ 3 * (s + Λ) := by
      rw [← hr2, mul_pow, ← hy3]; ring
    have e2 : (L * r) ^ 2 ≤ 2 * y ^ 3 * Λ := by
      rw [e1]
      have : s + Λ ≤ 2 * Λ := by linarith
      nlinarith [pow_pos hy0 3]
    have e3 : (M * y) ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (by positivity) hyM 3
    have e4 : M ^ 3 * (L * r) ^ 2 ≤ 2 * Λ ^ 4 := by
      have : M ^ 3 * (L * r) ^ 2 ≤ 2 * (M * y) ^ 3 * Λ := by
        rw [mul_pow]; nlinarith [pow_pos (by positivity : (0 : ℝ) < M) 3]
      nlinarith
    have e5 : 32 * Ca ^ 2 ≤ M ^ 3 := by
      rw [hM]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hCa 3]
    have e6 : (Ca * L * r) ^ 2 ≤ (Λ ^ 2 / 4) ^ 2 := by
      have hLr : 0 ≤ (L * r) ^ 2 := sq_nonneg _
      have : 32 * Ca ^ 2 * (L * r) ^ 2 ≤ M ^ 3 * (L * r) ^ 2 :=
        mul_le_mul_of_nonneg_right e5 hLr
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 e6
  -- `C_a 𝔏 / u ≤ Λ²/4096`
  have h3 : Ca * L * (1 / u) ≤ Λ ^ 2 / 4096 := by
    have e1 : L * (1 / u) ≤ y ^ 2 := by
      have : L * (1 / u) * L = y ^ 3 := by
        field_simp
        nlinarith
      have : y ^ 3 ≤ y ^ 2 := by nlinarith
      nlinarith
    have e2 : (M * y) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) hyM 2
    have e3 : 4096 * Ca * (Ca * y ^ 2) ≤ Λ ^ 2 := by
      rw [mul_pow, hM] at e2; nlinarith
    have e4 : Ca * y ^ 2 ≤ Λ ^ 2 / 4096 := by
      have : 4096 * (Ca * y ^ 2) ≤ 4096 * Ca * (Ca * y ^ 2) := by nlinarith
      linarith
    calc Ca * L * (1 / u) = Ca * (L * (1 / u)) := by ring
      _ ≤ Ca * y ^ 2 := mul_le_mul_of_nonneg_left e1 (by linarith)
      _ ≤ Λ ^ 2 / 4096 := e4
  have h4 : Ca * L * (r + 1 / u) ≤ Λ ^ 2 / 4 + Λ ^ 2 / 4096 := by
    rw [mul_add]; linarith
  nlinarith

/-- Part (b) of Lemma 5.2: if `U_w y ≤ ϰ` with `U_w = 7800 C`, `C = 2·10⁴ C_a`, and
`Λ ≤ W/2`, then `Λ ≤ C 𝔏 v ≤ W/4`, where `v = (ϰu)^{-1/2}`; moreover `𝔏 v ≤ y`. -/
private lemma weakDichotomy_partB {Ca C L u κ y v Λ W s r U : ℝ} (hCa : 1 ≤ Ca) (hL : 1 ≤ L)
    (hu : 0 < u) (hLu : 1 ≤ L * u) (hκ : 0 < κ) (hy0 : 0 < y) (hy3 : y ^ 3 * u = L ^ 2)
    (hv0 : 0 < v) (hv2 : v ^ 2 * (κ * u) = 1) (hΛ0 : 0 ≤ Λ) (hW1 : κ / 1950 ≤ W)
    (hs1 : s ≤ κ) (hr0 : 0 ≤ r) (hr2 : r ^ 2 * u = s + Λ)
    (hQ : Λ * (W - Λ) ≤ Ca * L * (r + 1 / u) + 3 / 10 * Λ ^ 2) (hC : C = 20000 * Ca)
    (hU : U = 7800 * C) (hUy : U * y ≤ κ) (hΛW : Λ ≤ W / 2) (hW2 : W ≤ 4 * κ) :
    Λ ≤ C * L * v ∧ C * L * v ≤ W / 4 ∧ L * v ≤ y := by
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hU1 : 1 ≤ U := by rw [hU]; linarith
  have hyκ : y ≤ κ := by nlinarith
  -- `ϰ u ≥ 1`
  have hκu : 1 ≤ κ * u := by
    by_contra h
    replace h := not_le.1 h
    have e1 : (κ * u) ^ 3 < 1 := pow_lt_one₀ (by positivity) h (by norm_num)
    have e2 : (y * u) ^ 3 ≤ (κ * u) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hyκ hu.le) 3
    have e3 : (y * u) ^ 3 = (L * u) ^ 2 := by rw [mul_pow, mul_pow]; nlinarith
    have e4 : 1 ≤ (L * u) ^ 2 := one_le_pow₀ hLu
    linarith
  have hv1 : v ≤ 1 := by
    by_contra h
    replace h := not_le.1 h
    nlinarith
  have hinvu : 1 / u = κ * v ^ 2 := by
    field_simp
    linarith
  -- `Ψ ≤ 3 ϰ v`
  have hr : r ≤ 2 * κ * v := by
    have e1 : r ^ 2 = (s + Λ) * (κ * v ^ 2) := by
      rw [← hinvu, ← hr2]; field_simp
    have e2 : s + Λ ≤ 3 * κ := by linarith
    have e3 : r ^ 2 ≤ (2 * κ * v) ^ 2 := by
      rw [e1]; nlinarith [mul_pos hκ (pow_pos hv0 2)]
    exact (pow_le_pow_iff_left₀ hr0 (by positivity) two_ne_zero).1 e3
  have hΨ : r + 1 / u ≤ 3 * κ * v := by
    rw [hinvu]; nlinarith
  -- `(7/20) W Λ ≤ C_a 𝔏 Ψ`
  have h1 : 7 / 20 * (W * Λ) ≤ Ca * L * (r + 1 / u) := by nlinarith
  have h2 : 7 / 20 * (W * Λ) ≤ Ca * L * (3 * κ * v) :=
    h1.trans (mul_le_mul_of_nonneg_left hΨ (by positivity))
  have h3 : κ / 1950 * Λ ≤ W * Λ := mul_le_mul_of_nonneg_right hW1 hΛ0
  have e1 : (L * v) ^ 2 * κ = y ^ 3 := by
    have : (L * v) ^ 2 * κ = y ^ 3 * (v ^ 2 * (κ * u)) := by rw [mul_pow, ← hy3]; ring
    rw [this, hv2, mul_one]
  have hLv : 0 ≤ L * v := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have e2 : κ * (7 * Λ) ≤ κ * (117000 * (Ca * (L * v))) := by nlinarith
    have e3 := le_of_mul_le_mul_left e2 hκ
    have e4 : 0 ≤ Ca * (L * v) := by positivity
    rw [hC]
    nlinarith
  · -- `(U_w 𝔏 v)² ≤ ϰ²`
    have e2 : (U * y) ^ 3 ≤ κ ^ 3 := pow_le_pow_left₀ (by positivity) hUy 3
    have e3 : U ^ 2 ≤ U ^ 3 := pow_le_pow_right₀ hU1 (by norm_num)
    have e4 : (U * (L * v)) ^ 2 * κ ≤ κ ^ 3 := by
      have : (U * (L * v)) ^ 2 * κ = U ^ 2 * y ^ 3 := by
        rw [mul_pow, mul_assoc, e1]
      rw [this]
      calc U ^ 2 * y ^ 3 ≤ U ^ 3 * y ^ 3 := mul_le_mul_of_nonneg_right e3 (by positivity)
        _ = (U * y) ^ 3 := by ring
        _ ≤ κ ^ 3 := e2
    have e5 : (U * (L * v)) ^ 2 ≤ κ ^ 2 := by
      have : κ * (U * (L * v)) ^ 2 ≤ κ * κ ^ 2 := by
        calc κ * (U * (L * v)) ^ 2 = (U * (L * v)) ^ 2 * κ := mul_comm _ _
          _ ≤ κ ^ 3 := e4
          _ = κ * κ ^ 2 := by ring
      exact le_of_mul_le_mul_left this hκ
    have e6 : U * (L * v) ≤ κ :=
      (pow_le_pow_iff_left₀ (by positivity) hκ.le two_ne_zero).1 e5
    have e7 : C * L * v = U * (L * v) / 7800 := by rw [hU]; ring
    rw [e7]
    linarith
  · have e2 : (L * v) ^ 2 ≤ y ^ 2 := by
      have : κ * (L * v) ^ 2 ≤ κ * y ^ 2 := by
        calc κ * (L * v) ^ 2 = y ^ 2 * y := by rw [← pow_succ, ← e1]; ring
          _ ≤ y ^ 2 * κ := mul_le_mul_of_nonneg_left hyκ (sq_nonneg _)
          _ = κ * y ^ 2 := by ring
      exact le_of_mul_le_mul_left this hκ
    exact (pow_le_pow_iff_left₀ hLv hy0.le two_ne_zero).1 e2

/-- Part (c) of Lemma 5.2, once `Λ ≤ C_c y` is known: by (5.3), (5.5) and (5.2′),
`Λ_d + Λ_o ≤ K 𝔏 u^{-1/3} ≤ λ_st/2`, where `t = u^{-1/3}` and `λ_st = 1/(576 C_s)`. -/
private lemma weakDichotomy_partC {Cs L u t y Λ D LD LO K Cc r : ℝ} (hCs : 1 ≤ Cs) (hL : 1 ≤ L)
    (hu : 0 < u) (ht0 : 0 < t) (ht3 : t ^ 3 * u = 1) (hy0 : 0 < y) (hy3 : y ^ 3 * u = L ^ 2)
    (hΛ0 : 0 ≤ Λ) (hΛl : Λ ≤ 1 / (576 * Cs)) (hΛy : Λ ≤ Cc * y) (hΨ : r + 1 / u ≤ 2 * t)
    (hLO : LO ≤ 35 * L * (r + 1 / u)) (hD : D ≤ 1036 * Cs * L * (r + 1 / u) + 144 * Cs * Λ ^ 2)
    (hLD : LD ≤ Λ + D) (hK : 5 / 4 * Cc + 2072 * Cs + 70 ≤ K) (hKu : (1152 * Cs * K * L) ^ 3 ≤ u) :
    LD + LO ≤ K * L * t ∧ K * L * t ≤ 1 / (576 * Cs) / 2 := by
  have hCs0 : 0 < Cs := by linarith
  -- `y ≤ 𝔏 t`
  have hyt : y ≤ L * t := by
    have e1 : y ^ 3 = L ^ 2 * t ^ 3 := by
      have : y ^ 3 * u = L ^ 2 * t ^ 3 * u := by rw [hy3, mul_assoc, ht3, mul_one]
      exact mul_right_cancel₀ hu.ne' this
    have e2 : y ^ 3 ≤ (L * t) ^ 3 := by
      rw [e1, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by norm_num)) (by positivity)
    exact (pow_le_pow_iff_left₀ hy0.le (by positivity) (by norm_num)).1 e2
  have hΛ' : Λ ≤ Cc * (L * t) := by
    have hCc : 0 ≤ Cc := by
      by_contra h
      replace h := not_le.1 h
      nlinarith
    exact hΛy.trans (mul_le_mul_of_nonneg_left hyt hCc)
  -- `144 C_s Λ² ≤ Λ/4`
  have hsq : 144 * Cs * Λ ^ 2 ≤ Λ / 4 := by
    have e1 : Λ * (576 * Cs) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hΛl; exact hΛl
    nlinarith
  have hLt : 0 ≤ L * t := by positivity
  refine ⟨?_, ?_⟩
  · have e1 : 35 * L * (r + 1 / u) ≤ 70 * (L * t) := by nlinarith
    have e2 : 1036 * Cs * L * (r + 1 / u) ≤ 2072 * Cs * (L * t) := by nlinarith
    have e3 : (5 / 4 * Cc + 2072 * Cs + 70) * (L * t) ≤ K * (L * t) :=
      mul_le_mul_of_nonneg_right hK hLt
    nlinarith
  · have e1 : (1152 * Cs * K * L * t) ^ 3 ≤ 1 := by
      calc (1152 * Cs * K * L * t) ^ 3 = (1152 * Cs * K * L) ^ 3 * t ^ 3 := by ring
        _ ≤ u * t ^ 3 := mul_le_mul_of_nonneg_right hKu (by positivity)
        _ = 1 := by rw [mul_comm]; exact ht3
    have hK0 : 0 ≤ K := by nlinarith
    have e2 : 1152 * Cs * K * L * t ≤ 1 :=
      (pow_le_one_iff_of_nonneg (by positivity) (by norm_num)).1 e1
    rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith

/-- `y = 𝔏^{2/3} u^{-1/3}`, `t = u^{-1/3}` and `v = (ϰu)^{-1/2}` satisfy `y³ u = 𝔏²`,
`t³ u = 1` and `v² ϰu = 1`. -/
private lemma weakDichotomy_rpow {L u κ : ℝ} (hL : 0 < L) (hu : 0 < u) (hκ : 0 < κ) :
    0 < u ^ (-(1 / 3 : ℝ)) ∧ (u ^ (-(1 / 3 : ℝ))) ^ 3 * u = 1 ∧
    0 < L ^ (2 / 3 : ℝ) * u ^ (-(1 / 3 : ℝ)) ∧
    (L ^ (2 / 3 : ℝ) * u ^ (-(1 / 3 : ℝ))) ^ 3 * u = L ^ 2 ∧
    0 < (κ * u) ^ (-(1 / 2 : ℝ)) ∧ ((κ * u) ^ (-(1 / 2 : ℝ))) ^ 2 * (κ * u) = 1 := by
  have ht : (u ^ (-(1 / 3 : ℝ))) ^ 3 * u = 1 := by
    rw [← Real.rpow_mul_natCast hu.le, show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num,
      Real.rpow_neg_one, inv_mul_cancel₀ hu.ne']
  have hL3 : (L ^ (2 / 3 : ℝ)) ^ 3 = L ^ 2 := by
    rw [← Real.rpow_mul_natCast hL.le, show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 2 by norm_num,
      Real.rpow_two]
  have hκu : 0 < κ * u := mul_pos hκ hu
  refine ⟨Real.rpow_pos_of_pos hu _, ht, by positivity, ?_, Real.rpow_pos_of_pos hκu _, ?_⟩
  · rw [mul_pow, hL3, mul_assoc, ht, mul_one]
  · rw [← Real.rpow_mul_natCast hκu.le, show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num,
      Real.rpow_neg_one, inv_mul_cancel₀ hκu.ne']

/-- `2/√u ≤ 2 u^{-1/3}` for `u ≥ 1`. -/
private lemma weakDichotomy_sqrt {u t : ℝ} (hu : 1 ≤ u) (ht0 : 0 < t) (ht3 : t ^ 3 * u = 1) :
    2 / Real.sqrt u ≤ 2 * t := by
  have hq : 0 < Real.sqrt u := Real.sqrt_pos.2 (by linarith)
  have hq2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt (by linarith)
  have h1 : 1 ≤ t * Real.sqrt u := by
    by_contra h
    replace h := not_le.1 h
    have e1 : (t * Real.sqrt u) ^ 6 < 1 := pow_lt_one₀ (by positivity) h (by norm_num)
    have e2 : (t * Real.sqrt u) ^ 6 = (t ^ 3 * u) ^ 2 * u := by
      rw [← hq2]; ring_nf; rw [Real.sq_sqrt (by linarith)]
    rw [e2, ht3] at e1
    linarith
  rw [div_le_iff₀ hq]
  nlinarith

/-! ### 2. Lemma 5.2 -/

/-- Lemma 5.2: the weak dichotomy in the near regime, (a)–(c), with constants `U_w ≥ 1` and `C`
depending only on the model parameters. -/
theorem weak_dichotomy {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδp : 0 < δp) (hC₀ : 1 ≤ C₀) :
    ∃ U C : ℝ, 1 ≤ U ∧ 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ Dnear ϑ⁻¹ K N, ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z,
        LamD x z + LamO x z ≤ lamSt C₀ δm δp →
        Lam x z ≤ C * (varkappa z +
          levelFL ϑ⁻¹ C₀ K N ^ (2 / 3 : ℝ) * ((N : ℝ) * z.im) ^ (-(1 / 3 : ℝ))) ∧
        (weakKw U ϑ⁻¹ C₀ K N z ≤ varkappa z → Lam x z ≤ ‖msc z * (1 - msc z ^ 2)‖ / 2 →
          Lam x z ≤ C * levelFL ϑ⁻¹ C₀ K N * (varkappa z * (N * z.im)) ^ (-(1 / 2 : ℝ)) ∧
          C * levelFL ϑ⁻¹ C₀ K N * (varkappa z * (N * z.im)) ^ (-(1 / 2 : ℝ)) ≤
            ‖msc z * (1 - msc z ^ 2)‖ / 4) ∧
        (varkappa z < weakKw U ϑ⁻¹ C₀ K N z ∨
            (weakKw U ϑ⁻¹ C₀ K N z ≤ varkappa z ∧ Lam x z ≤ ‖msc z * (1 - msc z ^ 2)‖ / 2) →
          LamD x z + LamO x z ≤ K * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 3 : ℝ)) ∧
          K * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 3 : ℝ)) ≤ lamSt C₀ δm δp / 2) := by
  have hCs1 : 1 ≤ stabCs C₀ δm δp :=
    le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) (lt_min hδm hδp).le)
  have hCa1 : 1 ≤ aprioriCa C₀ δm δp := by
    have : aprioriCa C₀ δm δp = 3 * 10 ^ 6 * stabCs C₀ δm δp ^ 2 := rfl
    rw [this]; nlinarith
  obtain ⟨N₁, hA⟩ := apriori_bounds (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₂, hS⟩ := standing_ineq hϑ hϑ1 hC₀
    (2 * (20000 * aprioriCa C₀ δm δp * (7800 * (20000 * aprioriCa C₀ δm δp) + 1)) +
      4000 * stabCs C₀ δm δp)
  refine ⟨7800 * (20000 * aprioriCa C₀ δm δp), 20000 * aprioriCa C₀ δm δp, by nlinarith,
    by positivity, max N₁ N₂, ?_⟩
  intro N hN M hM K hK1 hK2 z hz x hx hs
  obtain ⟨-, -, hpt⟩ := hA N (le_trans (le_max_left _ _) hN) M hM K hK1 hK2
  obtain ⟨-, -, -, -, hLO, -, -, -, hD, hLD, hΨ2, -, hQ⟩ := hpt z hz x hx hs
  obtain ⟨⟨hK₀, hN13, -, -⟩, ⟨hL150, hLK, -, -⟩, -, -⟩ :=
    hS N (le_trans (le_max_right _ _) hN) K hK1 hK2
  obtain ⟨hE, hη1, hη'⟩ := hz
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  -- the constants
  set Cs := stabCs C₀ δm δp with hCs
  set Ca := aprioriCa C₀ δm δp with hCa
  set C := 20000 * Ca with hC
  set U := 7800 * C with hU
  have hC1 : 1 ≤ C := by rw [hC]; linarith
  have hU1 : 1 ≤ U := by rw [hU]; linarith
  have hKCs : 1152 * Cs ≤ K := by nlinarith
  have hKc : 5 / 4 * (C * (U + 1)) + 2072 * Cs + 70 ≤ K := by nlinarith
  have hKpos : 0 < K := by linarith
  have hK1' : 1 ≤ K := by linarith
  -- `η > 0` and `u = Nη ≥ K^{C₁-1}`
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hKC : 0 < K ^ (ledgerC1 ϑ⁻¹ - 1) := Real.rpow_pos_of_pos hKpos _
  have hη : 0 < z.im := lt_of_lt_of_le (div_pos hKC hNr) hη1
  have hu1 : K ^ (ledgerC1 ϑ⁻¹ - 1) ≤ N * z.im := by
    rw [div_le_iff₀ hNr, mul_comm] at hη1
    exact hη1
  set L := levelFL ϑ⁻¹ C₀ K N with hLdef
  set u := (N : ℝ) * z.im with hudef
  have hu0 : 0 < u := mul_pos hNr hη
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  -- (S2) and (L1): `(1152 C_s K 𝔏)³ ≤ u`
  have hKu : (1152 * Cs * K * L) ^ 3 ≤ u := by
    have e1 : 1152 * Cs * K * L ≤ K ^ (4 * ϑ⁻¹ + 5) := by
      have : K ^ (4 * ϑ⁻¹ + 5) = K ^ 2 * K ^ (4 * ϑ⁻¹ + 3) := by
        rw [show 4 * ϑ⁻¹ + 5 = 2 + (4 * ϑ⁻¹ + 3) by ring, Real.rpow_add hKpos, Real.rpow_two]
      rw [this]
      have e2 : 1152 * Cs * K ≤ K ^ 2 := by nlinarith
      calc 1152 * Cs * K * L ≤ K ^ 2 * L := mul_le_mul_of_nonneg_right e2 hL0.le
        _ ≤ K ^ 2 * K ^ (4 * ϑ⁻¹ + 3) := mul_le_mul_of_nonneg_left hLK (by positivity)
    have e3 : (K ^ (4 * ϑ⁻¹ + 5)) ^ 3 ≤ K ^ (ledgerC1 ϑ⁻¹ - 1) := by
      rw [← Real.rpow_mul_natCast hKpos.le]
      apply Real.rpow_le_rpow_of_exponent_le hK1'
      unfold ledgerC1
      push_cast
      linarith
    calc (1152 * Cs * K * L) ^ 3 ≤ (K ^ (4 * ϑ⁻¹ + 5)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) e1 3
      _ ≤ K ^ (ledgerC1 ϑ⁻¹ - 1) := e3
      _ ≤ u := hu1
  have hu4 : 4 ≤ u := by
    have e0 : 1 ≤ Cs * K * L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCs1 hK1') hL1
    have e1 : (4 : ℝ) ≤ 1152 * Cs * K * L := by
      have : 1152 * Cs * K * L = 1152 * (Cs * K * L) := by ring
      linarith only [this, e0]
    have e2 : 1152 * Cs * K * L ≤ (1152 * Cs * K * L) ^ 3 :=
      le_self_pow₀ (by linarith only [e1]) (by norm_num)
    linarith only [e1, e2, hKu]
  have hLu : 1 ≤ L * u := by nlinarith only [hL1, hu4]
  have hLu2 : L ^ 2 ≤ u := by
    have e0 : 1 ≤ 1152 * Cs * K := by nlinarith only [hCs1, hK1']
    have e1 : L ≤ 1152 * Cs * K * L := le_mul_of_one_le_left hL0.le e0
    have e2 : 1 ≤ 1152 * Cs * K * L := hL1.trans e1
    calc L ^ 2 ≤ (1152 * Cs * K * L) ^ 2 := pow_le_pow_left₀ hL0.le e1 2
      _ ≤ (1152 * Cs * K * L) ^ 3 := pow_le_pow_right₀ e2 (by norm_num)
      _ ≤ u := hKu
  -- sizes of `m_sc`
  obtain ⟨hm1, hm2, hm3, hm4⟩ := msc_size hE hη hη'
  obtain ⟨hs0', hs1, -⟩ := msc_im_chain hE hη hη'
  have hs0 : 0 ≤ (msc z).im := le_trans (by positivity) hs0'
  set κ := varkappa z with hκdef
  have hκ : 0 < κ := by
    have : 0 < kappaE z.re + z.im := by
      have : 0 ≤ kappaE z.re := abs_nonneg _
      linarith
    exact Real.sqrt_pos.2 this
  set W := ‖msc z * (1 - msc z ^ 2)‖ with hWdef
  have hWeq : W = ‖msc z‖ * ‖1 - msc z ^ 2‖ := norm_mul _ _
  have hW1 : κ / 1950 ≤ W := by
    rw [hWeq]
    have : 1 / 13 * (1 / 150 * κ) ≤ ‖msc z‖ * ‖1 - msc z ^ 2‖ :=
      mul_le_mul hm1 hm3 (by positivity) (norm_nonneg _)
    linarith
  have hW2 : W ≤ 4 * κ := by
    rw [hWeq]
    have : ‖msc z‖ * ‖1 - msc z ^ 2‖ ≤ 1 * (4 * κ) :=
      mul_le_mul hm2 hm4 (norm_nonneg _) zero_le_one
    linarith
  -- `Λ`, `Ψ`, and the quadratic relations
  set w := stieltjesEmp (toMatrix x) z - msc z with hwdef
  have hΛdef : Lam x z = ‖w‖ := rfl
  set Λ := Lam x z with hΛ
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; exact norm_nonneg _
  have hQ1 : Λ ^ 2 ≤ W * Λ + ‖w ^ 2 - msc z * (1 - msc z ^ 2) * w‖ := by
    have e1 : ‖w ^ 2‖ ≤ ‖w ^ 2 - msc z * (1 - msc z ^ 2) * w‖ + ‖msc z * (1 - msc z ^ 2) * w‖ := by
      have := norm_add_le (w ^ 2 - msc z * (1 - msc z ^ 2) * w) (msc z * (1 - msc z ^ 2) * w)
      rwa [sub_add_cancel] at this
    rw [norm_pow, norm_mul] at e1
    rw [hΛdef]
    linarith
  have hQ2 : Λ * (W - Λ) ≤ ‖w ^ 2 - msc z * (1 - msc z ^ 2) * w‖ := by
    have e1 : w ^ 2 - msc z * (1 - msc z ^ 2) * w = w * (w - msc z * (1 - msc z ^ 2)) := by ring
    have e2 : W - Λ ≤ ‖w - msc z * (1 - msc z ^ 2)‖ := by
      rw [norm_sub_rev, hΛdef]
      exact norm_sub_norm_le _ _
    rw [e1, norm_mul, ← hΛdef]
    exact mul_le_mul_of_nonneg_left e2 hΛ0
  have hΨdef : ctrlPsi x z = Real.sqrt (((msc z).im + Λ) / u) + 1 / u := rfl
  set r := Real.sqrt (((msc z).im + Λ) / u) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 * u = (msc z).im + Λ := by
    rw [hrdef, Real.sq_sqrt (div_nonneg (by linarith) hu0.le)]
    field_simp
  rw [hΨdef] at hLO hD hΨ2 hQ
  -- `Λ ≤ λ_st` (Lemma 3.10)
  have hLO0 : 0 ≤ LamO x z := Real.iSup_nonneg fun _ => norm_nonneg _
  have hLDs : LamDM (toMatrix x) z ≤ lamSt C₀ δm δp := by
    change LamD x z ≤ _
    linarith only [hs, hLO0]
  have hN2 : 2 ≤ N := by omega
  obtain ⟨-, hwD, -⟩ :=
    stab_near (toMatrix_isHermitian x) hM.varProfile hδm hδp hN2 hE hη hη' hLDs
  have hΛl : Λ ≤ 1 / (576 * Cs) := hwD.trans hLDs
  -- the powers `y`, `t`, `v`
  obtain ⟨ht0, ht3, hy0, hy3, hv0, hv2⟩ := weakDichotomy_rpow hL0 hu0 hκ
  set t := u ^ (-(1 / 3 : ℝ)) with htdef
  set y := L ^ (2 / 3 : ℝ) * t with hydef
  set v := (κ * u) ^ (-(1 / 2 : ℝ)) with hvdef
  have hy1 : y ≤ 1 := by
    have e1 : y ^ 3 * u ≤ 1 * u := by rw [hy3, one_mul]; exact hLu2
    have e2 : y ^ 3 ≤ 1 := le_of_mul_le_mul_right e1 hu0
    exact (pow_le_one_iff_of_nonneg hy0.le (by norm_num)).1 e2
  have hΨt : r + 1 / u ≤ 2 * t := hΨ2.trans (weakDichotomy_sqrt (by linarith only [hu4]) ht0 ht3)
  have hKw : weakKw U ϑ⁻¹ C₀ K N z = U * y := by
    rw [hydef, hU]; unfold weakKw; ring
  rw [hKw]
  -- (a)
  have hPa : Λ ≤ 64 * Ca * (κ + y) :=
    weakDichotomy_partA hCa1 hL1 hu0 hκ.le hy0 hy1 hy3 hΛ0 hW2 hs1 hr0 hr2
      (by linarith only [hQ, hQ1])
  have hPb : U * y ≤ κ → Λ ≤ W / 2 → Λ ≤ C * L * v ∧ C * L * v ≤ W / 4 ∧ L * v ≤ y :=
    fun hUy hΛW => weakDichotomy_partB hCa1 hL1 hu0 hLu hκ hy0 hy3 hv0 hv2 hΛ0 hW1 hs1 hr0 hr2
      (by linarith only [hQ, hQ2]) hC hU hUy hΛW hW2
  have hCa64 : 64 * Ca ≤ C := by rw [hC]; linarith only [hCa1]
  have hCy : 0 ≤ C * y := mul_nonneg (by linarith only [hC1]) hy0.le
  refine ⟨?_, fun hUy hΛW => ⟨(hPb hUy hΛW).1, (hPb hUy hΛW).2.1⟩, fun h => ?_⟩
  · exact hPa.trans (mul_le_mul_of_nonneg_right hCa64 (add_pos hκ hy0).le)
  · have hCUy : C * y ≤ C * (U + 1) * y := by
      have : C * (U + 1) * y = C * y + U * (C * y) := by ring
      rw [this]
      have : 0 ≤ U * (C * y) := mul_nonneg (by linarith only [hU1]) hCy
      linarith only [this]
    have hΛy : Λ ≤ C * (U + 1) * y := by
      rcases h with h | ⟨hUy, hΛW⟩
      · calc Λ ≤ 64 * Ca * (κ + y) := hPa
          _ ≤ C * (κ + y) := mul_le_mul_of_nonneg_right hCa64 (add_pos hκ hy0).le
          _ ≤ C * (U * y + y) :=
            mul_le_mul_of_nonneg_left (by linarith only [h]) (by linarith only [hC1])
          _ = C * (U + 1) * y := by ring
      · obtain ⟨e1, -, e2⟩ := hPb hUy hΛW
        have e3 : C * L * v ≤ C * y := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e2 (by linarith only [hC1])
        linarith only [e1, e3, hCUy]
    exact weakDichotomy_partC hCs1 hL1 hu0 ht0 ht3 hy0 hy3 hΛ0 hΛl hΛy hΨt hLO hD hLD hKc hKu

end Rigidity
