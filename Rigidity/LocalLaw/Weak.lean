import Rigidity.LocalLaw.WeakDichotomy
import Rigidity.LocalLaw.WeakFar
import Rigidity.LocalLaw.WeakInitial

/-!
# The weak local law on the lattice (NP v1.1, §5.3: Theorem 5.5)

Numbers in this file refer to the blueprint NP v1.1; [EYY, …] refers to the original paper
(Erdős–Yau–Yin, arXiv:1007.4652).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-!
The proof is the continuity argument of §5.3 along the column `col(z)` of a lattice point
(Definition 5.1). In the near regime the induction carries, at each point `z_j` of the column,
the bound `Λ_d + Λ_o ≤ K 𝔏 (Nη_j)^{-1/3} ≤ λ_st/2` together with `Λ ≤ |w₀|/4` whenever
`ϰ ≥ ϰ_w`; each step is Lemma 5.2 at `z_{j+1}`, whose hypotheses follow from the Lipschitz bounds
(5.b). In the far regime the induction carries `maxᵢ |Gᵢᵢ| ≤ 1` and `Λ_o ≤ λ_f`; each step is
Lemma 5.4 at `z_j` followed by the Lipschitz bounds (5.c). The Lipschitz bounds are used on
`{Im ≥ 1/(2N)}`, which contains both domains. Part (c) and the probability bound follow from the
sizes of `m_sc` (Lemma 3.1 (c), Lemma 3.2) and the union bound of Definition 5.1. This is
[EYY, Theorem 3.1] in the form of NP v1.1.
-/

/-! ### 1. Elementary facts -/

/-- `Λ ≤ Λ_d`: the modulus of an average is at most the largest modulus of its terms. -/
private lemma weakLaw_lam_le_lamD {N : ℕ} (hN : 0 < N) (x : Pair N → 𝕜) (z : ℂ) :
    Lam x z ≤ LamD x z := by
  have hb : ∀ i : Fin N, ‖green (toMatrix x) z i i - msc z‖ ≤ LamD x z := fun i =>
    le_ciSup (f := fun k : Fin N => ‖green (toMatrix x) z k k - msc z‖)
      (Finite.bddAbove_range _) i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : stieltjesEmp (toMatrix x) z - msc z =
      (N : ℂ)⁻¹ * ∑ i, (green (toMatrix x) z i i - msc z) := by
    unfold stieltjesEmp
    rw [Fintype.card_fin, Matrix.trace, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ hNc, one_mul]
    rfl
  unfold Lam
  rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, (green (toMatrix x) z i i - msc z)‖
      ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, LamD x z := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb i)
    _ = LamD x z := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hNpos.ne', one_mul]

/-- `Λ_d ≥ 0`. -/
private lemma weakLaw_lamD_nonneg {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : 0 ≤ LamD x z :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- `Λ_o ≥ 0`. -/
private lemma weakLaw_lamO_nonneg {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : 0 ≤ LamO x z :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- Two consecutive points `z_j = E + i(10 - j N⁻⁴)` and `z_{j+1}` of a column: their distance
is at most `N⁻⁴`, the imaginary part decreases, and so does the modulus while the imaginary part
stays nonnegative. -/
private lemma weakLaw_col_step (E : ℝ) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    ‖(⟨E, 10 - j / (N : ℝ) ^ 4⟩ : ℂ) - ⟨E, 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4⟩‖ ≤
        1 / (N : ℝ) ^ 4 ∧
      (⟨E, 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4⟩ : ℂ).im ≤ (⟨E, 10 - j / (N : ℝ) ^ 4⟩ : ℂ).im ∧
      (0 ≤ (⟨E, 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4⟩ : ℂ).im →
        ‖(⟨E, 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4⟩ : ℂ)‖ ≤ ‖(⟨E, 10 - j / (N : ℝ) ^ 4⟩ : ℂ)‖) := by
  have hP : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have hd : (10 - j / (N : ℝ) ^ 4) - (10 - (j + 1 : ℕ) / (N : ℝ) ^ 4) = 1 / (N : ℝ) ^ 4 := by
    push_cast; ring
  have hd0 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 4 := by positivity
  refine ⟨?_, ?_, fun h0 => ?_⟩
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp only [Complex.sub_re, Complex.sub_im, sub_self, abs_zero, zero_add]
    rw [hd, abs_of_nonneg hd0]
  · change 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4 ≤ 10 - j / (N : ℝ) ^ 4
    linarith
  · rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_apply, Complex.normSq_apply]
    have h1 : (⟨E, 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4⟩ : ℂ).im ≤
        (⟨E, 10 - j / (N : ℝ) ^ 4⟩ : ℂ).im := by
      change 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4 ≤ 10 - j / (N : ℝ) ^ 4
      linarith
    have h2 : (⟨E, 10 - (j + 1 : ℕ) / (N : ℝ) ^ 4⟩ : ℂ).re = (⟨E, 10 - j / (N : ℝ) ^ 4⟩ : ℂ).re :=
      rfl
    rw [h2]
    nlinarith

/-- The Lipschitz bounds (5.b), (5.c) on `{Im ≥ 1/(2N)}` for two points at distance at most
`N⁻⁴` (Lemma 3.5 (c), Lemma 3.1 (f)): `Λ`, `Λ_d`, `Λ_o` move by at most `7 N⁻²`, the diagonal
entries of `G` by at most `4 N⁻²`, and `w₀ = m_sc (1 - m_sc²)` by at most `12 N⁻²`. -/
private lemma weakLaw_lip {N : ℕ} (hN : 0 < N) (x : Pair N → 𝕜) {z w : ℂ}
    (hz : 1 / (2 * (N : ℝ)) ≤ z.im) (hw : 1 / (2 * (N : ℝ)) ≤ w.im)
    (hzw : ‖z - w‖ ≤ 1 / (N : ℝ) ^ 4) :
    |Lam x z - Lam x w| ≤ 7 / (N : ℝ) ^ 2 ∧ |LamD x z - LamD x w| ≤ 7 / (N : ℝ) ^ 2 ∧
      |LamO x z - LamO x w| ≤ 7 / (N : ℝ) ^ 2 ∧
      (∀ i, ‖green (toMatrix x) z i i - green (toMatrix x) w i i‖ ≤ 4 / (N : ℝ) ^ 2) ∧
      ‖msc z * (1 - msc z ^ 2) - msc w * (1 - msc w ^ 2)‖ ≤ 12 / (N : ℝ) ^ 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hη₀ : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  have hinv : (1 / (2 * (N : ℝ)))⁻¹ = 2 * N := by rw [one_div, inv_inv]
  have hd0 : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hz0 : 0 < z.im := lt_of_lt_of_le hη₀ hz
  have hw0 : 0 < w.im := lt_of_lt_of_le hη₀ hw
  obtain ⟨h1, h2, h3⟩ := abs_LamM_sub_le (toMatrix_isHermitian x) hη₀ hz hw
  rw [hinv] at h1 h2 h3
  have hfac : ((2 * (N : ℝ)) ^ 2 + 2 * N + 1) * ‖z - w‖ ≤ 7 / (N : ℝ) ^ 2 := by
    calc ((2 * (N : ℝ)) ^ 2 + 2 * N + 1) * ‖z - w‖
        ≤ ((2 * (N : ℝ)) ^ 2 + 2 * N + 1) * (1 / (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left hzw (by positivity)
      _ ≤ 7 / (N : ℝ) ^ 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : (2 * (N : ℝ)) ^ 2 + 2 * N + 1 ≤ 7 * (N : ℝ) ^ 2 := by nlinarith
          have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
          calc ((2 * (N : ℝ)) ^ 2 + 2 * N + 1) * (N : ℝ) ^ 2 ≤ 7 * (N : ℝ) ^ 2 * (N : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right this h4
            _ = 7 * (N : ℝ) ^ 4 := by ring
  refine ⟨h1.trans hfac, h2.trans hfac, h3.trans hfac, fun i => ?_, ?_⟩
  · refine (norm_green_sub_le (toMatrix_isHermitian x) hz0 hw0 i i).trans ?_
    rw [div_le_iff₀ (mul_pos hz0 hw0)]
    have hzw' : 1 / (2 * (N : ℝ)) * (1 / (2 * (N : ℝ))) ≤ z.im * w.im :=
      mul_le_mul hz hw hη₀.le hz0.le
    have e1 : 4 / (N : ℝ) ^ 2 * (1 / (2 * (N : ℝ)) * (1 / (2 * (N : ℝ)))) = 1 / (N : ℝ) ^ 4 := by
      field_simp; ring
    calc ‖z - w‖ ≤ 1 / (N : ℝ) ^ 4 := hzw
      _ = 4 / (N : ℝ) ^ 2 * (1 / (2 * (N : ℝ)) * (1 / (2 * (N : ℝ)))) := e1.symm
      _ ≤ 4 / (N : ℝ) ^ 2 * (z.im * w.im) := mul_le_mul_of_nonneg_left hzw' (by positivity)
  · have hm := norm_msc_sub_le hη₀ hz hw
    have hmz := (msc_bounds hz0).2.1
    have hmw := (msc_bounds hw0).2.1
    have hfac' : (1 / (2 * (N : ℝ)) + 1) / (1 / (2 * (N : ℝ))) = 1 + 2 * N := by
      field_simp
    rw [hfac'] at hm
    have hid : msc z * (1 - msc z ^ 2) - msc w * (1 - msc w ^ 2) =
        (msc z - msc w) * (1 - msc z ^ 2 - msc z * msc w - msc w ^ 2) := by ring
    have hq : ‖1 - msc z ^ 2 - msc z * msc w - msc w ^ 2‖ ≤ 4 := by
      have e1 : ‖1 - msc z ^ 2 - msc z * msc w - msc w ^ 2‖ ≤
          ‖(1 : ℂ)‖ + ‖msc z‖ ^ 2 + ‖msc z‖ * ‖msc w‖ + ‖msc w‖ ^ 2 := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_))
          (by rw [norm_pow])
        · rw [norm_pow]
        · rw [norm_mul]
      rw [norm_one] at e1
      have e2 : ‖msc z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (msc z)]
      have e3 : ‖msc w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (msc w)]
      have e4 : ‖msc z‖ * ‖msc w‖ ≤ 1 := by nlinarith [norm_nonneg (msc z), norm_nonneg (msc w)]
      linarith
    rw [hid, norm_mul]
    have hm' : ‖msc z - msc w‖ ≤ 3 / (N : ℝ) ^ 3 := by
      refine hm.trans ?_
      calc (1 + 2 * (N : ℝ)) * ‖z - w‖ ≤ (1 + 2 * (N : ℝ)) * (1 / (N : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left hzw (by positivity)
        _ ≤ 3 / (N : ℝ) ^ 3 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            have : 1 + 2 * (N : ℝ) ≤ 3 * N := by linarith
            calc (1 + 2 * (N : ℝ)) * (N : ℝ) ^ 3 ≤ 3 * N * (N : ℝ) ^ 3 :=
                  mul_le_mul_of_nonneg_right this (by positivity)
              _ = 3 * (N : ℝ) ^ 4 := by ring
    have h3N : 3 / (N : ℝ) ^ 3 ≤ 3 / (N : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      calc (N : ℝ) ^ 2 = (N : ℝ) ^ 2 * 1 := by ring
        _ ≤ (N : ℝ) ^ 2 * N := mul_le_mul_of_nonneg_left hNr (by positivity)
        _ = (N : ℝ) ^ 3 := by ring
    calc ‖msc z - msc w‖ * ‖1 - msc z ^ 2 - msc z * msc w - msc w ^ 2‖
        ≤ 3 / (N : ℝ) ^ 2 * 4 :=
          mul_le_mul (hm'.trans h3N) hq (norm_nonneg _) (by positivity)
      _ = 12 / (N : ℝ) ^ 2 := by ring

/-- On `|E| ≤ 5`, `t ≤ η ≤ 10` with `0 < t ≤ 1`: `|w₀| = |m_sc| |1 - m_sc²| ≥ ϰ/1950 ≥ t/1950`
(Lemma 3.2, (3.3)). -/
private lemma weakLaw_W_lo {w : ℂ} (hE : |w.re| ≤ 5) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (ht : t ≤ w.im) (h10 : w.im ≤ 10) : t / 1950 ≤ ‖msc w * (1 - msc w ^ 2)‖ := by
  have hw0 : 0 < w.im := lt_of_lt_of_le ht0 ht
  obtain ⟨hm13, -, hm150, -⟩ := msc_size hE hw0 h10
  have hκ : t ≤ varkappa w := by
    unfold varkappa
    rw [Real.le_sqrt ht0.le (by unfold kappaE; positivity)]
    have : 0 ≤ kappaE w.re := by unfold kappaE; positivity
    nlinarith
  rw [norm_mul]
  have e1 : 1 / 150 * t ≤ ‖1 - msc w ^ 2‖ := le_trans (by linarith) hm150
  calc t / 1950 = 1 / 13 * (1 / 150 * t) := by ring
    _ ≤ ‖msc w‖ * ‖1 - msc w ^ 2‖ := mul_le_mul hm13 e1 (by positivity) (norm_nonneg _)

/-- On `𝐃^far` (with `E_max ≥ 1`): `λ_f(z) ≥ 1/(30 E_max)` and `|z| + 1 ≤ 13 E_max`. -/
private lemma weakLaw_far_size {a C₀ K : ℝ} {N : ℕ} {w : ℂ} (hw : w ∈ Dfar a C₀ K N)
    (hE : 1 ≤ levelEmax a C₀ K N) :
    1 / (30 * levelEmax a C₀ K N) ≤ farLam w ∧ ‖w‖ + 1 ≤ 13 * levelEmax a C₀ K N := by
  obtain ⟨-, hre, hlo, h10⟩ := hw
  have him0 : 0 ≤ w.im := le_trans (by positivity) hlo
  have hn : ‖w‖ ≤ levelEmax a C₀ K N + 11 := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_nonneg him0] at this
    linarith
  refine ⟨?_, by linarith⟩
  unfold farLam
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- A point of `𝐃^near` with `K ≥ 1` has `η ≥ 1/N` and `Nη ≥ K^{C₁-1}`. -/
private lemma weakLaw_near_im {a K : ℝ} {N : ℕ} (hN : 0 < N) (ha : 0 ≤ a) (hK : 1 ≤ K) {w : ℂ}
    (hw : w ∈ Dnear a K N) :
    1 / (N : ℝ) ≤ w.im ∧ K ^ (ledgerC1 a - 1) ≤ N * w.im := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨-, hlo, -⟩ := hw
  have h1 : 1 ≤ K ^ (ledgerC1 a - 1) := Real.one_le_rpow hK (by unfold ledgerC1; linarith)
  refine ⟨le_trans (div_le_div_of_nonneg_right h1 hNr.le) hlo, ?_⟩
  rw [div_le_iff₀ hNr] at hlo
  linarith

/-- A point of `𝐃^far` has `η ≥ 1/(2√N) ≥ 1/(2N)`. -/
private lemma weakLaw_far_im {a C₀ K : ℝ} {N : ℕ} (hN : 0 < N) {w : ℂ}
    (hw : w ∈ Dfar a C₀ K N) : 1 / (2 * (N : ℝ)) ≤ w.im := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨-, -, hlo, -⟩ := hw
  have hs : Real.sqrt N ≤ N := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  exact le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) hlo

/-- The last step of part (c), near regime: if `Nη ≥ K^{18a+19}`, `𝔏 ≤ K^{4a+3}`,
`p₁ ≤ 2K^{3/2}` and `K ≥ 416`, then `16 p₁ K 𝔏 (Nη)^{-1/3} ≤ 1/13`. -/
private lemma weakLaw_near_c {a K L p u : ℝ} (ha : 1 ≤ a) (hK : 416 ≤ K)
    (hLK : L ≤ K ^ (4 * a + 3)) (hp0 : 0 ≤ p) (hp : p ≤ 2 * K ^ (3 / 2 : ℝ))
    (hu : K ^ (18 * a + 19) ≤ u) :
    K * L * u ^ (-(1 / 3 : ℝ)) * (16 * p) ≤ 1 / 13 := by
  have hK0 : 0 < K := by linarith
  have hv : u ^ (-(1 / 3 : ℝ)) ≤ K ^ ((18 * a + 19) * (-(1 / 3 : ℝ))) := by
    rw [Real.rpow_mul hK0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hu (by norm_num)
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hv0 : 0 ≤ u ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hu0.le _
  calc K * L * u ^ (-(1 / 3 : ℝ)) * (16 * p)
      ≤ K * K ^ (4 * a + 3) * K ^ ((18 * a + 19) * (-(1 / 3 : ℝ))) *
          (16 * (2 * K ^ (3 / 2 : ℝ))) := by gcongr
    _ = 32 * K ^ (1 + (4 * a + 3) + (18 * a + 19) * (-(1 / 3 : ℝ)) + 3 / 2) := by
        rw [Real.rpow_add hK0 (1 + (4 * a + 3) + (18 * a + 19) * (-(1 / 3 : ℝ))) (3 / 2),
          Real.rpow_add hK0 (1 + (4 * a + 3)) _, Real.rpow_add hK0 1 (4 * a + 3), Real.rpow_one]
        ring
    _ ≤ 32 * K ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) (by norm_num)
    _ = 32 / K := by rw [Real.rpow_neg_one]; ring
    _ ≤ 1 / 13 := by rw [div_le_div_iff₀ hK0 (by norm_num)]; linarith

/-- The last step of part (c), far regime: if `η ≥ 1/(2√N)` and `1248 N^{1/32} ≤ N^{1/8}`, then
`1248 N^{1/32} (Nη)^{-1/2} ≤ 1`. -/
private lemma weakLaw_far_c {N η : ℝ} (hN : 1 ≤ N) (hη : 1 / (2 * Real.sqrt N) ≤ η)
    (hs : 1248 * N ^ (1 / 32 : ℝ) ≤ N ^ (1 / 8 : ℝ)) :
    1248 * N ^ (1 / 32 : ℝ) * (N * η) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  set s := N ^ (1 / 8 : ℝ) with hsdef
  have h32 : 1 ≤ N ^ (1 / 32 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hs1 : 1248 ≤ s := by nlinarith
  have hsq : Real.sqrt N = s ^ 4 := by
    rw [Real.sqrt_eq_rpow, hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hu : s ^ 2 ≤ N * η := by
    have e1 : N * (1 / (2 * Real.sqrt N)) = Real.sqrt N / 2 := by
      have : N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0.le).symm
      rw [this, Real.sqrt_sq hsN.le]
      field_simp
    have e2 : Real.sqrt N / 2 ≤ N * η := by
      rw [← e1]; exact mul_le_mul_of_nonneg_left hη hN0.le
    rw [hsq] at e2
    have hs2 : 2 ≤ s ^ 2 := by nlinarith
    have e3 : s ^ 2 * 2 ≤ s ^ 2 * s ^ 2 := mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)
    have e4 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
    linarith
  have hu0 : 0 < N * η := by positivity
  have hr : s ≤ Real.sqrt (N * η) := (Real.le_sqrt (by linarith) hu0.le).2 hu
  rw [Real.rpow_neg hu0.le, ← Real.sqrt_eq_rpow]
  have hr0 : 0 < Real.sqrt (N * η) := Real.sqrt_pos.2 hu0
  rw [← div_eq_mul_inv, div_le_one hr0]
  linarith

/-! ### 2. The two inductions along a column -/

/-- The near-regime induction `𝓗_j` of the proof of Theorem 5.5 (a), for the column
`z_j = E + i(10 - j N⁻⁴)`, `j ≤ k`. The inputs are: the start `𝓗₀`-hypotheses at `z₀`; the step
of Lemma 5.2, in the form "if `Λ_d + Λ_o ≤ λ` and (`ϰ ≥ ϰ_w ⇒ Λ ≤ |w₀|/2`), then `𝓗_j`"; the
monotonicity of `ϰ_w` along the column; and `λ/2 + 14N⁻² ≤ λ`. -/
private lemma weakLaw_near {N : ℕ} (hN : 78000 ≤ N) (x : Pair N → 𝕜) {E : ℝ} (hE : |E| ≤ 5)
    (c : ℕ → ℂ) (hc : ∀ j, c j = ⟨E, 10 - j / (N : ℝ) ^ 4⟩) (k : ℕ) (lam : ℝ) (B κw : ℂ → ℝ)
    (hlo : ∀ j ≤ k, 1 / (N : ℝ) ≤ (c j).im)
    (hκw : ∀ j < k, κw (c j) ≤ κw (c (j + 1)))
    (hlam : lam / 2 + 14 / (N : ℝ) ^ 2 ≤ lam)
    (hbase : LamD x (c 0) + LamO x (c 0) ≤ lam ∧
      Lam x (c 0) ≤ ‖msc (c 0) * (1 - msc (c 0) ^ 2)‖ / 2)
    (hstep : ∀ j ≤ k, LamD x (c j) + LamO x (c j) ≤ lam →
      (κw (c j) ≤ varkappa (c j) → Lam x (c j) ≤ ‖msc (c j) * (1 - msc (c j) ^ 2)‖ / 2) →
      LamD x (c j) + LamO x (c j) ≤ B (c j) ∧ B (c j) ≤ lam / 2 ∧
        (κw (c j) ≤ varkappa (c j) → Lam x (c j) ≤ ‖msc (c j) * (1 - msc (c j) ^ 2)‖ / 4)) :
    ∀ j ≤ k, LamD x (c j) + LamO x (c j) ≤ B (c j) ∧ B (c j) ≤ lam / 2 ∧
      (κw (c j) ≤ varkappa (c j) → Lam x (c j) ≤ ‖msc (c j) * (1 - msc (c j) ^ 2)‖ / 4) := by
  have hNr : (78000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < N := by omega
  have hNr0 : (0 : ℝ) < N := by linarith
  have hgeo : ∀ j, ‖c j - c (j + 1)‖ ≤ 1 / (N : ℝ) ^ 4 ∧ (c (j + 1)).im ≤ (c j).im ∧
      (c (j + 1)).re = (c j).re := by
    intro j
    rw [hc j, hc (j + 1)]
    obtain ⟨h1, h2, -⟩ := weakLaw_col_step E hNpos j
    exact ⟨h1, h2, rfl⟩
  have hre : ∀ j, (c j).re = E := fun j => by rw [hc j]
  have him10 : ∀ j, (c j).im ≤ 10 := by
    intro j
    rw [hc j]
    change 10 - j / (N : ℝ) ^ 4 ≤ 10
    have : (0 : ℝ) ≤ j / (N : ℝ) ^ 4 := by positivity
    linarith
  have h2N : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hNr0 (by linarith)
  have hlo2 : ∀ j ≤ k, 1 / (2 * (N : ℝ)) ≤ (c j).im := fun j hj => h2N.trans (hlo j hj)
  have hN1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNr0]; linarith
  have h40 : 40 / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) / 1950 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hW : ∀ j ≤ k, 40 / (N : ℝ) ^ 2 ≤ ‖msc (c j) * (1 - msc (c j) ^ 2)‖ := fun j hj =>
    h40.trans (weakLaw_W_lo (by rw [hre]; exact hE) (by positivity) hN1 (hlo j hj) (him10 j))
  intro j
  induction j with
  | zero => intro _; exact hstep 0 (Nat.zero_le _) hbase.1 (fun _ => hbase.2)
  | succ j ih =>
    intro hj
    have hP := ih (by omega)
    obtain ⟨hlΛ, hlD, hlO, -, hlW⟩ :=
      weakLaw_lip hNpos x (hlo2 j (by omega)) (hlo2 (j + 1) hj) (hgeo j).1
    refine hstep (j + 1) hj ?_ ?_
    · obtain ⟨e1, -⟩ := abs_le.1 hlD
      obtain ⟨e2, -⟩ := abs_le.1 hlO
      have q : (14 : ℝ) / (N : ℝ) ^ 2 = 2 * (7 / (N : ℝ) ^ 2) := by ring
      linarith [hP.1, hP.2.1]
    · intro hκ
      have hϰ : varkappa (c (j + 1)) ≤ varkappa (c j) := by
        unfold varkappa
        rw [(hgeo j).2.2]
        exact Real.sqrt_le_sqrt (by linarith [(hgeo j).2.1])
      have hΛj := hP.2.2 ((hκw j (by omega)).trans (hκ.trans hϰ))
      have hWj : ‖msc (c j) * (1 - msc (c j) ^ 2)‖ ≤
          ‖msc (c (j + 1)) * (1 - msc (c (j + 1)) ^ 2)‖ + 12 / (N : ℝ) ^ 2 :=
        (norm_le_norm_add_norm_sub' (msc (c j) * (1 - msc (c j) ^ 2))
          (msc (c (j + 1)) * (1 - msc (c (j + 1)) ^ 2))).trans (by linarith [hlW])
      obtain ⟨e1, -⟩ := abs_le.1 hlΛ
      have e2 := hW (j + 1) hj
      have q1 : (12 : ℝ) / (N : ℝ) ^ 2 = 12 / 7 * (7 / (N : ℝ) ^ 2) := by ring
      have q2 : (40 : ℝ) / (N : ℝ) ^ 2 = 40 / 7 * (7 / (N : ℝ) ^ 2) := by ring
      linarith

/-- The far-regime induction `𝓕_j` of the proof of Theorem 5.5 (b), for the column
`z_j = E + i(10 - j N⁻⁴)`, `j ≤ k`: `maxᵢ |Gᵢᵢ(z_j)| ≤ 1` and `Λ_o(z_j) ≤ λ_f(z_j)`. The inputs
are `𝓕₀`, the step of Lemma 5.4 at `z_j`, and `λ_f ≥ 14 N⁻²` on the column. -/
private lemma weakLaw_far {N : ℕ} (hN : 3 ≤ N) (x : Pair N → 𝕜) {E : ℝ}
    (c : ℕ → ℂ) (hc : ∀ j, c j = ⟨E, 10 - j / (N : ℝ) ^ 4⟩) (k : ℕ)
    (hlo : ∀ j ≤ k, 1 / (2 * (N : ℝ)) ≤ (c j).im)
    (hfl : ∀ j ≤ k, 14 / (N : ℝ) ^ 2 ≤ farLam (c j))
    (hbase : (∀ i, ‖green (toMatrix x) (c 0) i i‖ ≤ 1) ∧ LamO x (c 0) ≤ farLam (c 0))
    (hstep : ∀ j < k, (∀ i, ‖green (toMatrix x) (c j) i i‖ ≤ 1) → LamO x (c j) ≤ farLam (c j) →
      (∀ i, ‖green (toMatrix x) (c j) i i‖ ≤ 1 / 2) ∧ LamO x (c j) ≤ farLam (c j) / 2) :
    ∀ j ≤ k, (∀ i, ‖green (toMatrix x) (c j) i i‖ ≤ 1) ∧ LamO x (c j) ≤ farLam (c j) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < N := by omega
  have h4 : 4 / (N : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  intro j
  induction j with
  | zero => intro _; exact hbase
  | succ j ih =>
    intro hj
    have hP := ih (by omega)
    obtain ⟨hG, hO⟩ := hstep j (by omega) hP.1 hP.2
    have hgeo : ‖c j - c (j + 1)‖ ≤ 1 / (N : ℝ) ^ 4 ∧
        (0 ≤ (c (j + 1)).im → ‖c (j + 1)‖ ≤ ‖c j‖) := by
      rw [hc j, hc (j + 1)]
      obtain ⟨h1, -, h3⟩ := weakLaw_col_step E hNpos j
      exact ⟨h1, h3⟩
    obtain ⟨-, -, hlO, hlG, -⟩ := weakLaw_lip hNpos x (hlo j (by omega)) (hlo (j + 1) hj) hgeo.1
    have him0 : 0 ≤ (c (j + 1)).im := le_trans (by positivity) (hlo (j + 1) hj)
    have hfm : farLam (c j) ≤ farLam (c (j + 1)) := by
      unfold farLam
      exact one_div_le_one_div_of_le (by positivity) (by linarith [hgeo.2 him0])
    refine ⟨fun i => ?_, ?_⟩
    · have e1 := norm_le_norm_add_norm_sub' (green (toMatrix x) (c (j + 1)) i i)
        (green (toMatrix x) (c j) i i)
      rw [norm_sub_rev] at e1
      linarith [hG i, hlG i]
    · obtain ⟨e1, -⟩ := abs_le.1 hlO
      have e2 := hfl (j + 1) hj
      have q : (14 : ℝ) / (N : ℝ) ^ 2 = 2 * (7 / (N : ℝ) ^ 2) := by ring
      linarith

/-! ### 3. The deterministic part at one lattice point -/

/-- The numerical consequences of the standing inequalities (S1)–(S4) used below, with
`a = 1/ϑ`, `C_s` of Lemma 3.9, `𝔏`, `E_max` of Definition 4.4, and `N ≥ 2·10⁵ C_s`,
`K ≥ 2·10⁴ C_s`. -/
private lemma weakLaw_nums {a Cs K L Em N : ℝ} (ha : 1 ≤ a) (hCs : 1 ≤ Cs)
    (hNc : 200000 * Cs ≤ N) (hK₀ : 20000 * Cs ≤ K) (hL150 : 150 ≤ L)
    (hLK : L ≤ K ^ (4 * a + 3)) (hE1 : 1 ≤ Em) (hEK : Em ≤ K ^ (2 * a + 1))
    (hKN : K ^ (6 * a + 6) ≤ N ^ (1 / 32 : ℝ))
    (hK0N : 20000 * Cs * N ^ (1 / 32 : ℝ) ≤ N ^ (1 / 8 : ℝ)) :
    200000 ≤ N ∧ 1 ≤ K ∧ 4 * L / Real.sqrt N ≤ 1 / (5000 * Cs) ∧
      4 * L / Real.sqrt N ≤ 1 / (30 * Em) ∧ Em ≤ N ∧
      K ^ (3 / 2 : ℝ) * (L * Em) ≤ N ^ (1 / 32 : ℝ) ∧
      1248 * N ^ (1 / 32 : ℝ) ≤ N ^ (1 / 8 : ℝ) := by
  have hNr : (200000 : ℝ) ≤ N := by nlinarith only [hNc, hCs]
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNr0 : (0 : ℝ) < N := by linarith
  have hK1 : 1 ≤ K := by nlinarith only [hK₀, hCs]
  have hKpos : 0 < K := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr0
  have hsq : N ^ (1 / 8 : ℝ) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hN32 : 1 ≤ N ^ (1 / 32 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hKe : ∀ e : ℝ, e ≤ 6 * a + 6 → K ^ e ≤ N ^ (1 / 32 : ℝ) := fun e he =>
    (Real.rpow_le_rpow_of_exponent_le hK1 he).trans hKN
  have hL0 : 0 ≤ L := by linarith
  have hEm0 : 0 ≤ Em := by linarith
  have hLN : L ≤ N ^ (1 / 32 : ℝ) := hLK.trans (hKe _ (by linarith))
  have hPLE : K ^ (3 / 2 : ℝ) * (L * Em) ≤ N ^ (1 / 32 : ℝ) := by
    calc K ^ (3 / 2 : ℝ) * (L * Em)
        ≤ K ^ (3 / 2 : ℝ) * (K ^ (4 * a + 3) * K ^ (2 * a + 1)) := by gcongr
      _ = K ^ (3 / 2 + (4 * a + 3) + (2 * a + 1)) := by
          rw [Real.rpow_add hKpos (3 / 2 + (4 * a + 3)) _, Real.rpow_add hKpos (3 / 2) (4 * a + 3)]
          ring
      _ ≤ _ := hKe _ (by linarith)
  have hK32 : 1 ≤ K ^ (3 / 2 : ℝ) := Real.one_le_rpow hK1 (by norm_num)
  have hLE0 : 0 ≤ L * Em := by positivity
  have hLE : L * Em ≤ N ^ (1 / 32 : ℝ) := by
    have : L * Em ≤ K ^ (3 / 2 : ℝ) * (L * Em) := le_mul_of_one_le_left hLE0 hK32
    linarith only [this, hPLE]
  have hEN : Em ≤ N := by
    have e1 : Em ≤ L * Em := le_mul_of_one_le_left hEm0 (by linarith)
    have e2 : N ^ (1 / 32 : ℝ) ≤ N := by
      calc N ^ (1 / 32 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = N := Real.rpow_one _
    linarith only [e1, e2, hLE]
  have hroot : 20000 * Cs * N ^ (1 / 32 : ℝ) ≤ Real.sqrt N := hK0N.trans hsq
  refine ⟨hNr, hK1, ?_, ?_, hEN, hPLE, ?_⟩
  · rw [div_le_div_iff₀ hsN (by positivity)]
    have := mul_le_mul_of_nonneg_left hLN (by positivity : (0 : ℝ) ≤ 20000 * Cs)
    linarith only [this, hroot]
  · rw [div_le_div_iff₀ hsN (by positivity)]
    have e1 : 120 * N ^ (1 / 32 : ℝ) ≤ 20000 * Cs * N ^ (1 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have e2 := mul_le_mul_of_nonneg_left hLE (by norm_num : (0 : ℝ) ≤ 120)
    linarith only [e1, e2, hroot]
  · have : 1248 * N ^ (1 / 32 : ℝ) ≤ 20000 * Cs * N ^ (1 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith only [this, hK0N]

/-- The deterministic part of Theorem 5.5 at one lattice point `z`, for one ensemble and one
level `K`. The hypotheses `h2`, `h3`, `h4` are Lemmas 5.2 (b), (c), 5.4 and 5.3 at this
`N`, `K`; the remaining ones are (S1)–(S4) and `N ≥ 2·10⁵ C_s`. -/
private lemma weakLaw_det {ϑ δm δp C₀ : ℝ} {N : ℕ} (M : Ensemble 𝕜 N) {K U : ℝ} {z : ℂ}
    (ha : 1 ≤ ϑ⁻¹) (hU : 1 ≤ U) (hCs1 : 1 ≤ stabCs C₀ δm δp)
    (hNc : 200000 * stabCs C₀ δm δp ≤ N) (hK₀ : 20000 * stabCs C₀ δm δp ≤ K)
    (hL150 : 150 ≤ levelFL ϑ⁻¹ C₀ K N) (hLK : levelFL ϑ⁻¹ C₀ K N ≤ K ^ (4 * ϑ⁻¹ + 3))
    (hE1 : 1 ≤ levelEmax ϑ⁻¹ C₀ K N) (hEK : levelEmax ϑ⁻¹ C₀ K N ≤ K ^ (2 * ϑ⁻¹ + 1))
    (hP1lo : K ^ (3 / 2 : ℝ) ≤ levelP1 K) (hP1hi : (levelP1 K : ℝ) ≤ 2 * K ^ (3 / 2 : ℝ))
    (hKN : K ^ (6 * ϑ⁻¹ + 6) ≤ (N : ℝ) ^ (1 / 32 : ℝ))
    (hK0N : 20000 * stabCs C₀ δm δp * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ))
    (hz : z ∈ lattice ϑ⁻¹ C₀ K N)
    (h2 : ∀ w ∈ Dnear ϑ⁻¹ K N, ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) w,
      LamD x w + LamO x w ≤ lamSt C₀ δm δp →
      (weakKw U ϑ⁻¹ C₀ K N w ≤ varkappa w → Lam x w ≤ ‖msc w * (1 - msc w ^ 2)‖ / 2 →
        Lam x w ≤ ‖msc w * (1 - msc w ^ 2)‖ / 4) ∧
      (varkappa w < weakKw U ϑ⁻¹ C₀ K N w ∨
          (weakKw U ϑ⁻¹ C₀ K N w ≤ varkappa w ∧ Lam x w ≤ ‖msc w * (1 - msc w ^ 2)‖ / 2) →
        LamD x w + LamO x w ≤ K * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * w.im) ^ (-(1 / 3 : ℝ)) ∧
        K * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * w.im) ^ (-(1 / 3 : ℝ)) ≤ lamSt C₀ δm δp / 2))
    (h3 : ∀ w ∈ Dfar ϑ⁻¹ C₀ K N, ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) w,
      (∀ i, ‖green (toMatrix x) w i i‖ ≤ 1) → LamO x w ≤ farLam w →
      (∀ i, ‖green (toMatrix x) w i i‖ ≤ 1 / 2) ∧
      LamD x w ≤ 6 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * w.im) ^ (-(1 / 2 : ℝ)) ∧
      LamO x w ≤ 3 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * w.im) ^ (-(1 / 2 : ℝ)) ∧
      LamO x w ≤ farLam w / 2)
    (h4 : ∀ w : ℂ, w.im = 10 → ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) w,
      (∀ i, ‖green (toMatrix x) w i i‖ ≤ 1 / 10) ∧
      LamD x w + LamO x w ≤ 4 * levelFL ϑ⁻¹ C₀ K N / Real.sqrt N) :
    ∀ x ∈ goodCol M ϑ⁻¹ C₀ K z,
      (z ∈ Dnear ϑ⁻¹ K N → LamD x z + LamO x z ≤
          K * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 3 : ℝ)) ∧
        K * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 3 : ℝ)) ≤ lamSt C₀ δm δp / 2) ∧
      (z ∈ Dfar ϑ⁻¹ C₀ K N → (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2) ∧
        LamD x z + LamO x z ≤ 9 * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 2 : ℝ))) ∧
      x ∈ aprioriEvent N (levelP1 K) z := by
  have ha0 : 0 ≤ ϑ⁻¹ := by linarith
  have hlam : lamSt C₀ δm δp = 1 / (576 * stabCs C₀ δm δp) := rfl
  obtain ⟨hNr, hK1', hb4, hbF, hEN, hPLE, hs1248⟩ :=
    weakLaw_nums ha hCs1 hNc hK₀ hL150 hLK hE1 hEK hKN hK0N
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hN78 : 78000 ≤ N := by
    have : (78000 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNr0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hL0 : 0 ≤ levelFL ϑ⁻¹ C₀ K N := by linarith
  have hfl : ∀ w ∈ Dfar ϑ⁻¹ C₀ K N, 14 / (N : ℝ) ^ 2 ≤ farLam w := by
    intro w hw
    refine le_trans ?_ (weakLaw_far_size hw hE1).1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 420 * (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hNr]
    linarith only [this, hEN]
  intro x hx
  have hgood : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z, x ∈ goodEvent M ϑ⁻¹ (K ^ 2) w :=
    fun w hw => Set.mem_iInter₂.1 hx w hw
  obtain ⟨-, m, k, hzk⟩ := id hz
  have hk : z.im = 10 - k / (N : ℝ) ^ 4 := by rw [hzk]
  obtain ⟨hcol, -, -, -, hnear, hfar⟩ := latticeCol_eq hNpos hz hk
  set c : ℕ → ℂ := fun j => ⟨z.re, 10 - j / (N : ℝ) ^ 4⟩ with hcdef
  have hc : ∀ j, c j = ⟨z.re, 10 - j / (N : ℝ) ^ 4⟩ := fun _ => rfl
  have hmem : ∀ j ≤ k, c j ∈ latticeCol ϑ⁻¹ C₀ K N z := fun j hj => by
    rw [hcol]; exact ⟨j, hj, rfl⟩
  have hck : c k = z := Complex.ext rfl hk.symm
  have hc0 : (c 0).im = 10 := by simp [hcdef]
  have hzcol : z ∈ latticeCol ϑ⁻¹ C₀ K N z := ⟨hz, rfl, le_rfl⟩
  have hinit := h4 (c 0) hc0 x (hgood _ (hmem 0 (Nat.zero_le _)))
  -- (a): the near-regime induction
  have hA : z ∈ Dnear ϑ⁻¹ K N → LamD x z + LamO x z ≤
        K * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 3 : ℝ)) ∧
      K * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 3 : ℝ)) ≤ lamSt C₀ δm δp / 2 := by
    intro hzn
    have hD : ∀ j ≤ k, c j ∈ Dnear ϑ⁻¹ K N := fun j hj => hnear hzn (hmem j hj)
    have hlo : ∀ j ≤ k, 1 / (N : ℝ) ≤ (c j).im := fun j hj =>
      (weakLaw_near_im hNpos ha0 hK1' (hD j hj)).1
    have hind := weakLaw_near hN78 x hzn.1 c hc k (lamSt C₀ δm δp)
      (fun w => K * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * w.im) ^ (-(1 / 3 : ℝ)))
      (weakKw U ϑ⁻¹ C₀ K N) hlo ?_ ?_ ?_ ?_ k le_rfl
    · rw [hck] at hind
      exact ⟨hind.1, hind.2.1⟩
    · -- `ϰ_w` increases down the column
      intro j hj
      have hgeo := (weakLaw_col_step z.re hNpos j).2.1
      have h1 : 0 < (N : ℝ) * (c (j + 1)).im :=
        mul_pos hNr0 (lt_of_lt_of_le (by positivity) (hlo (j + 1) hj))
      have h2 : (N : ℝ) * (c (j + 1)).im ≤ (N : ℝ) * (c j).im :=
        mul_le_mul_of_nonneg_left hgeo hNr0.le
      unfold weakKw
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos h1 h2 (by norm_num))
        (mul_nonneg (by linarith) (Real.rpow_nonneg hL0 _))
    · -- `λ_st/2 + 14 N⁻² ≤ λ_st`
      have e1 : 14 / (N : ℝ) ^ 2 ≤ 1 / (1152 * stabCs C₀ δm δp) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 16128 * stabCs C₀ δm δp ≤ (N : ℝ) ^ 2 := by nlinarith only [hNc, hCs1, hN1]
        linarith only [this]
      have e2 : lamSt C₀ δm δp = 2 * (1 / (1152 * stabCs C₀ δm δp)) := by
        rw [hlam]; field_simp; ring
      linarith only [e1, e2]
    · -- `𝓗₀`: Lemma 5.3 at `z₀ = E + 10i`
      have hW0 : 1 / 1950 ≤ ‖msc (c 0) * (1 - msc (c 0) ^ 2)‖ := by
        have := weakLaw_W_lo (w := c 0) hzn.1 one_pos le_rfl (by rw [hc0]; norm_num)
          (by rw [hc0])
        linarith only [this]
      have e1 : 1 / (5000 * stabCs C₀ δm δp) ≤ 1 / 5000 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have e2 : 1 / (5000 * stabCs C₀ δm δp) ≤ 1 / (576 * stabCs C₀ δm δp) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have e3 := weakLaw_lam_le_lamD hNpos x (c 0)
      have e4 := weakLaw_lamO_nonneg x (c 0)
      have e5 := hinit.2
      refine ⟨by rw [hlam]; linarith only [e5, hb4, e2], ?_⟩
      linarith only [e1, e3, e4, e5, hb4, hW0]
    · -- the step: Lemma 5.2 at `z_j`
      intro j hj hs hQ
      obtain ⟨hb, hc'⟩ := h2 (c j) (hD j hj) x (hgood _ (hmem j hj)) hs
      rcases lt_or_ge (varkappa (c j)) (weakKw U ϑ⁻¹ C₀ K N (c j)) with hlt | hle
      · obtain ⟨e1, e2⟩ := hc' (Or.inl hlt)
        exact ⟨e1, e2, fun h => absurd h (not_le.2 hlt)⟩
      · have hΛ := hQ hle
        obtain ⟨e1, e2⟩ := hc' (Or.inr ⟨hle, hΛ⟩)
        exact ⟨e1, e2, fun _ => hb hle hΛ⟩
  -- (b): the far-regime induction
  have hB : z ∈ Dfar ϑ⁻¹ C₀ K N → (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2) ∧
      LamD x z ≤ 6 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) ∧
      LamO x z ≤ 3 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) := by
    intro hzf
    have hF : ∀ j ≤ k, c j ∈ Dfar ϑ⁻¹ C₀ K N := fun j hj => hfar hzf (hmem j hj)
    have hind := weakLaw_far (by omega) x c hc k (fun j hj => weakLaw_far_im hNpos (hF j hj))
      (fun j hj => hfl _ (hF j hj)) ?_ ?_ k le_rfl
    · rw [hck] at hind
      obtain ⟨hG, hLD, hLO, -⟩ := h3 z hzf x (hgood z hzcol) hind.1 hind.2
      exact ⟨hG, hLD, hLO⟩
    · -- `𝓕₀`: Lemma 5.3 at `z₀ = E + 10i`
      have e1 := weakLaw_lamD_nonneg x (c 0)
      have e2 := (weakLaw_far_size (hF 0 (Nat.zero_le _)) hE1).1
      have e3 := hinit.2
      exact ⟨fun i => (hinit.1 i).trans (by norm_num), by linarith only [e1, e2, e3, hbF]⟩
    · -- the step: Lemma 5.4 at `z_j`
      intro j hj hG1 hO
      obtain ⟨hG, -, -, hlf⟩ := h3 (c j) (hF j hj.le) x (hgood _ (hmem j hj.le)) hG1 hO
      exact ⟨hG, hlf⟩
  -- (c): `𝒢_col(z) ⊆ Ξ(z)`
  have hK32 : 1 ≤ K ^ (3 / 2 : ℝ) := Real.one_le_rpow hK1' (by norm_num)
  have hp1 : (1 : ℝ) ≤ levelP1 K := hK32.trans hP1lo
  have hp0 : (0 : ℝ) < 16 * (levelP1 K : ℝ) := by positivity
  have hC : x ∈ aprioriEvent N (levelP1 K) z := by
    rcases hz.1 with hzn | hzf
    · obtain ⟨h1, h2⟩ := hA hzn
      obtain ⟨hlo, hu⟩ := weakLaw_near_im hNpos ha0 hK1' hzn
      have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) hlo
      have hm13 := (msc_size hzn.1 hz0 hzn.2.2).1
      have e1 := weakLaw_lamD_nonneg x z
      have e2 := weakLaw_lamO_nonneg x z
      have e3 : lamSt C₀ δm δp ≤ 1 / 576 := by
        rw [hlam]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      refine ⟨by linarith only [h1, h2, hm13, e2, e3], ?_⟩
      rw [le_div_iff₀ hp0]
      have hu' : K ^ (18 * ϑ⁻¹ + 19) ≤ (N : ℝ) * z.im := by
        have : ledgerC1 ϑ⁻¹ - 1 = 18 * ϑ⁻¹ + 19 := by unfold ledgerC1; ring
        rwa [this] at hu
      have hc := weakLaw_near_c ha (by linarith) hLK (by positivity) hP1hi hu'
      have e4 : LamO x z * (16 * (levelP1 K : ℝ)) ≤
          K * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 3 : ℝ)) *
            (16 * (levelP1 K : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith only [h1, e1]) hp0.le
      linarith only [e4, hc, hm13]
    · obtain ⟨-, hD6, hO3⟩ := hB hzf
      have hlo := weakLaw_far_im hNpos hzf
      have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) hlo
      have hmb := (msc_bounds hz0).1
      have hzE := (weakLaw_far_size hzf hE1).2
      set v := ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) with hv
      have hv0 : 0 ≤ v := Real.rpow_nonneg (by positivity) _
      have hfc := weakLaw_far_c hN1 hzf.2.2.1 hs1248
      -- `48 p₁ 𝔏 v ≤ |m_sc(z)|`
      have hkey : 48 * (levelP1 K : ℝ) * (levelFL ϑ⁻¹ C₀ K N * v) ≤ ‖msc z‖ := by
        have hz1 : 0 < ‖z‖ + 1 := by positivity
        have e1 : 48 * (levelP1 K : ℝ) * (levelFL ϑ⁻¹ C₀ K N * v) * (‖z‖ + 1) ≤ 1 := by
          calc 48 * (levelP1 K : ℝ) * (levelFL ϑ⁻¹ C₀ K N * v) * (‖z‖ + 1)
              ≤ 48 * (2 * K ^ (3 / 2 : ℝ)) * (levelFL ϑ⁻¹ C₀ K N * v) *
                  (13 * levelEmax ϑ⁻¹ C₀ K N) := by gcongr
            _ = 1248 * (K ^ (3 / 2 : ℝ) *
                  (levelFL ϑ⁻¹ C₀ K N * levelEmax ϑ⁻¹ C₀ K N)) * v := by ring
            _ ≤ 1248 * (N : ℝ) ^ (1 / 32 : ℝ) * v := by gcongr
            _ ≤ 1 := hfc
        have e2 : 48 * (levelP1 K : ℝ) * (levelFL ϑ⁻¹ C₀ K N * v) ≤ 1 / (‖z‖ + 1) := by
          rw [le_div_iff₀ hz1]; exact e1
        linarith only [e2, hmb]
      have hLv : 0 ≤ levelFL ϑ⁻¹ C₀ K N * v := mul_nonneg hL0 hv0
      have e3 : 12 * (levelFL ϑ⁻¹ C₀ K N * v) ≤
          48 * (levelP1 K : ℝ) * (levelFL ϑ⁻¹ C₀ K N * v) := by nlinarith only [hp1, hLv]
      refine ⟨by linarith only [hD6, e3, hkey], ?_⟩
      rw [le_div_iff₀ hp0]
      have e4 : LamO x z * (16 * (levelP1 K : ℝ)) ≤
          3 * levelFL ϑ⁻¹ C₀ K N * v * (16 * (levelP1 K : ℝ)) :=
        mul_le_mul_of_nonneg_right hO3 hp0.le
      linarith only [e4, hkey]
  exact ⟨hA, fun hzf => ⟨(hB hzf).1, by linarith only [(hB hzf).2.1, (hB hzf).2.2]⟩, hC⟩

/-! ### 4. Theorem 5.5 -/

/-- Theorem 5.5: the weak local law on the lattice, deterministic form, and the probability of
the a priori event `Ξ(z) = Ξ_{p₁}(z)`. -/
theorem weakLaw_lattice {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ → ∀ z ∈ lattice ϑ⁻¹ C₀ K N,
        (∀ x ∈ goodCol M ϑ⁻¹ C₀ K z,
          (z ∈ Dnear ϑ⁻¹ K N → LamD x z + LamO x z ≤
              K * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 3 : ℝ)) ∧
            K * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 3 : ℝ)) ≤ lamSt C₀ δm δp / 2) ∧
          (z ∈ Dfar ϑ⁻¹ C₀ K N → (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2) ∧
            LamD x z + LamO x z ≤ 9 * levelFL ϑ⁻¹ C₀ K N * (N * z.im) ^ (-(1 / 2 : ℝ))) ∧
          x ∈ aprioriEvent N (levelP1 K) z) ∧
        M.prodLaw (aprioriEvent N (levelP1 K) z)ᶜ ≤
          ENNReal.ofReal (C * N ^ 9 * Real.exp (-K ^ 2)) := by
  -- `δ₋ ≤ 1`, `δ₊ ≤ 1` (Convention 1.1) are not needed in the proof
  have _ : δm ≤ 1 ∧ δp ≤ 1 := ⟨hδm1, hδp1⟩
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hCs1 : 1 ≤ stabCs C₀ δm δp :=
    le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) (lt_min hδm hδp).le)
  obtain ⟨U, Cw, hU, -, N₂, h2⟩ := weak_dichotomy (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₃, h3⟩ := far_step (𝕜 := 𝕜) (δm := δm) (δp := δp) hϑ hϑ1 hC₀
  obtain ⟨N₄, h4⟩ := initial_estimate (𝕜 := 𝕜) (δm := δm) (δp := δp) hϑ hϑ1 hC₀
  obtain ⟨N₅, h5⟩ := lattice_card (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₆, h6⟩ := standing_ineq hϑ hϑ1 hC₀ (20000 * stabCs C₀ δm δp)
  refine ⟨460 / ϑ, by positivity,
    max (max (max N₂ N₃) (max N₄ N₅)) (max N₆ ⌈200000 * stabCs C₀ δm δp⌉₊), ?_⟩
  intro N hN M hM K hK1 hK2 z hz
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : N₅ ≤ N := by omega
  have hN6 : N₆ ≤ N := by omega
  have hNc : 200000 * stabCs C₀ δm δp ≤ N := Nat.ceil_le.1 (by omega)
  obtain ⟨⟨hK₀, -, -, -⟩, ⟨hL150, hLK, hE1, hEK⟩, ⟨-, -, -, hP1lo, hP1hi⟩, hKN, hK0N⟩ :=
    h6 N hN6 K hK1 hK2
  have hdet := weakLaw_det M ha hU hCs1 hNc hK₀ hL150 hLK hE1 hEK hP1lo hP1hi hKN hK0N hz
    (fun w hw x hx hs => by
      obtain ⟨-, hb, hc⟩ := h2 N hN2 M hM K hK1 hK2 w hw x hx hs
      exact ⟨fun h1 h2 => (hb h1 h2).1.trans (hb h1 h2).2, hc⟩)
    (fun w hw x hx hG hO => by
      obtain ⟨hG', -, hLD, hΨ, hLO, hlf⟩ := h3 N hN3 M hM K hK1 hK2 w hw x hx hG hO
      exact ⟨hG', hLD.trans hΨ, by linarith only [hLO, hΨ],
        by linarith only [hLO, hΨ, hlf]⟩)
    (fun w hw x hx => h4 N hN4 M hM K hK1 hK2 w hw x hx)
  -- the probability of `Ξ(z)ᶜ`
  have hN1 : (1 : ℝ) ≤ N := by
    have : (200000 : ℝ) ≤ N := by nlinarith only [hNc, hCs1]
    linarith
  obtain ⟨-, -, hprob⟩ := h5 N hN5 K hK1 hK2
  refine ⟨hdet, ?_⟩
  calc M.prodLaw (aprioriEvent N (levelP1 K) z)ᶜ ≤ M.prodLaw (goodCol M ϑ⁻¹ C₀ K z)ᶜ :=
        measure_mono (Set.compl_subset_compl.2 fun x hx => (hdet x hx).2.2)
    _ ≤ ENNReal.ofReal (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2)) := hprob M hM z hz
    _ ≤ ENNReal.ofReal (460 / ϑ * N ^ 9 * Real.exp (-K ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have : (N : ℝ) ^ 8 ≤ (N : ℝ) ^ 9 := pow_le_pow_right₀ hN1 (by norm_num)
        gcongr

end Rigidity
