import Rigidity.Fluctuation.Structure
import Rigidity.LocalLaw.Lattice

/-!
# The a priori event and the crude moment bound (NP v1.1, §6.3: Lemmas 6.6, 6.7)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

section EventHelpers

variable {N : ℕ}

private lemma eventBounds_var_nonneg (M : Ensemble 𝕜 N) (i j : Fin N) : 0 ≤ M.var i j :=
  integral_nonneg fun y => by positivity

private lemma eventBounds_var_comm (M : Ensemble 𝕜 N) (i j : Fin N) : M.var i j = M.var j i := by
  unfold Ensemble.var
  rw [Pair.mk'_comm]

/-- The row form of (A): `∑_l σ_al² = 1`. -/
private lemma eventBounds_row_sum (M : Ensemble 𝕜 N) (hA : M.AssumptionA) (a : Fin N) :
    ∑ l, M.var a l = 1 :=
  (Finset.sum_congr rfl fun l _ => eventBounds_var_comm M a l).trans (hA a)

/-- (A) and (C) force `C₀ ≥ 1`. -/
private lemma eventBounds_one_le_C₀ (M : Ensemble 𝕜 N) {C₀ : ℝ} (hA : M.AssumptionA)
    (hC : M.AssumptionC C₀) (a : Fin N) : 1 ≤ C₀ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos a
  calc (1 : ℝ) = ∑ l, M.var a l := (eventBounds_row_sum M hA a).symm
    _ ≤ ∑ _l : Fin N, C₀ / N := Finset.sum_le_sum fun l _ => hC a l
    _ = C₀ := by simp [Finset.sum_const]; field_simp

private lemma eventBounds_im_green_diag_nonneg {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (a : Fin N) :
    0 ≤ (greenT A T z a a).im := by
  by_cases ha : a ∈ T
  · simp [greenT, ha]
  · have hP : (minor A T).IsHermitian := hA.submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    have : greenT A T z a a = green (minor A T) z ⟨a, ha⟩ ⟨a, ha⟩ := by
      simp [greenT, greenMinor, ha]
    rw [this]
    exact (green_im_diag_pos hP hz _).le

private lemma eventBounds_im_stieltjesT {A : Matrix (Fin N) (Fin N) 𝕜} {z : ℂ}
    (T : Finset (Fin N)) :
    (stieltjesT A T z).im = (N : ℝ)⁻¹ * ∑ k, (greenT A T z k k).im := by
  unfold stieltjesT
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul, Complex.im_sum]

private lemma eventBounds_im_stieltjesEmp {A : Matrix (Fin N) (Fin N) 𝕜} {z : ℂ} :
    (stieltjesEmp A z).im = (N : ℝ)⁻¹ * ∑ k, (green A z k k).im := by
  unfold stieltjesEmp
  rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  simp [Matrix.trace, Complex.im_sum]

private lemma eventBounds_norm_diag_le_LamD (x : Pair N → 𝕜) (z : ℂ) (k : Fin N) :
    ‖green (toMatrix x) z k k - msc z‖ ≤ LamD x z :=
  le_ciSup (f := fun k => ‖green (toMatrix x) z k k - msc z‖) (Finite.bddAbove_range _) k

private lemma eventBounds_norm_off_le_LamO (x : Pair N → 𝕜) (z : ℂ) {a b : Fin N} (h : a ≠ b) :
    ‖green (toMatrix x) z a b‖ ≤ LamO x z :=
  le_ciSup (f := fun q : {q : Fin N × Fin N // q.1 ≠ q.2} => ‖green (toMatrix x) z q.1.1 q.1.2‖)
    (Finite.bddAbove_range _) ⟨(a, b), h⟩


/-- Lemma 6.6 (b), the closeness of the minor entries: on `Ξ_p(z)`, for `l ∉ L`,
`|G^{(L)}_ll - m_sc| ≤ (33/64)|m_sc|`. -/
private lemma eventBounds_greenT_close (x : Pair N → 𝕜) {z : ℂ} (hz : 0 < z.im) {p : ℕ}
    (hp : 1 ≤ p) {L : Finset (Fin N)} (hL : L.Nonempty) (hLp : L.card ≤ p)
    (hx : x ∈ aprioriEvent N p z) {l : Fin N} (hl : l ∉ L) :
    ‖greenT (toMatrix x) L z l l - msc z‖ ≤ 33 / 64 * ‖msc z‖ := by
  obtain ⟨hD, hO⟩ := hx
  have hA := toMatrix_isHermitian x
  have hm0 : 0 < ‖msc z‖ := norm_pos_iff.2 fun h => by
    have := msc_im_pos hz
    rw [h] at this
    simp at this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  have hrp : (L.card : ℝ) ≤ p := by exact_mod_cast hLp
  have hg : 0 < ‖msc z‖ / 2 := by positivity
  have hdiag : ∀ a ∈ L, ‖msc z‖ / 2 ≤ ‖green (toMatrix x) z a a‖ := fun a _ => by
    have h1 := eventBounds_norm_diag_le_LamD x z a
    have h2 : ‖msc z‖ - ‖green (toMatrix x) z a a - msc z‖ ≤ ‖green (toMatrix x) z a a‖ := by
      have := norm_sub_norm_le (msc z) (green (toMatrix x) z a a)
      rw [norm_sub_rev] at this
      linarith
    linarith
  have hOle : ‖msc z‖ / (16 * p) ≤ ‖msc z‖ / 2 / (2 * L.card) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hoff : ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
      ‖green (toMatrix x) z a b‖ ≤ ‖msc z‖ / 2 / (2 * L.card) := fun a _ b _ hab =>
    (eventBounds_norm_off_le_LamO x z hab).trans (hO.trans hOle)
  have hkey := norm_greenT_sub_le hA hz hL hg hdiag hoff hl hl
  have : Nonempty L := hL.to_subtype
  have hsup : ∀ a : L, ‖green (toMatrix x) z l a‖ ≤ ‖msc z‖ / (16 * p) := fun a =>
    (eventBounds_norm_off_le_LamO x z (fun (h : l = a) => hl (h ▸ a.2))).trans hO
  have hsup' : ∀ b : L, ‖green (toMatrix x) z b l‖ ≤ ‖msc z‖ / (16 * p) := fun b =>
    (eventBounds_norm_off_le_LamO x z (fun (h : (b : Fin N) = l) => hl (h ▸ b.2))).trans hO
  have hs1 : (⨆ a : L, ‖green (toMatrix x) z l a‖) ≤ ‖msc z‖ / (16 * p) := ciSup_le hsup
  have hs2 : (⨆ b : L, ‖green (toMatrix x) z b l‖) ≤ ‖msc z‖ / (16 * p) := ciSup_le hsup'
  have hs1' : 0 ≤ (⨆ a : L, ‖green (toMatrix x) z l a‖) :=
    le_ciSup_of_le (Finite.bddAbove_range _) (⟨_, hL.choose_spec⟩ : L) (norm_nonneg _)
  have hs2' : 0 ≤ (⨆ b : L, ‖green (toMatrix x) z b l‖) :=
    le_ciSup_of_le (Finite.bddAbove_range _) (⟨_, hL.choose_spec⟩ : L) (norm_nonneg _)
  have hbound : 2 * (L.card : ℝ) ^ 2 / (‖msc z‖ / 2) *
      (⨆ a : L, ‖green (toMatrix x) z l a‖) * (⨆ b : L, ‖green (toMatrix x) z b l‖) ≤
      ‖msc z‖ / 64 := by
    calc 2 * (L.card : ℝ) ^ 2 / (‖msc z‖ / 2) *
          (⨆ a : L, ‖green (toMatrix x) z l a‖) * (⨆ b : L, ‖green (toMatrix x) z b l‖)
        ≤ 2 * (L.card : ℝ) ^ 2 / (‖msc z‖ / 2) * (‖msc z‖ / (16 * p)) *
            (‖msc z‖ / (16 * p)) := by
          gcongr
      _ = (L.card : ℝ) ^ 2 / (p : ℝ) ^ 2 * (‖msc z‖ / 64) := by
          field_simp
          ring
      _ ≤ 1 * (‖msc z‖ / 64) := by
          gcongr
          rw [div_le_one (by positivity)]
          exact pow_le_pow_left₀ hr0.le hrp 2
      _ = ‖msc z‖ / 64 := one_mul _
  have hD' := eventBounds_norm_diag_le_LamD x z l
  calc ‖greenT (toMatrix x) L z l l - msc z‖
      = ‖(greenT (toMatrix x) L z l l - green (toMatrix x) z l l) +
          (green (toMatrix x) z l l - msc z)‖ := by ring_nf
    _ ≤ ‖greenT (toMatrix x) L z l l - green (toMatrix x) z l l‖ +
          ‖green (toMatrix x) z l l - msc z‖ := norm_add_le _ _
    _ ≤ ‖msc z‖ / 64 + ‖msc z‖ / 2 := by linarith
    _ = 33 / 64 * ‖msc z‖ := by ring

end EventHelpers

/-- Lemma 6.6: the a priori event `Ξ_p(z)` controls all minors with `1 ≤ |L| ≤ p`, (a)–(c). -/
theorem faEvent_bounds {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) {p : ℕ} (hp : 1 ≤ p) (hpN : 12 * C₀ * p ≤ N)
    {L : Finset (Fin N)} (hL1 : 1 ≤ L.card) (hLp : L.card ≤ p) {z : ℂ} (hz : 0 < z.im)
    (x : Pair N → 𝕜) :
    (1 / N ≤ phiStarSq p x z ∧ phiL C₀ L z x ^ 2 ≤ 2 * C₀ ^ 2 * phiStarSq p x z) ∧
    (x ∈ aprioriEvent N p z → (stieltjesEmp (toMatrix x) z).im ≤ 3 / 2 ∧
      ∀ a ∈ L, 2 / 5 ≤ ‖z + mL M L z a x‖) ∧
    (z.im ≤ 10 → (p : ℝ) ≤ N * z.im → x ∈ aprioriEvent N p z →
      phiL C₀ L z x ^ 2 ≤ 25 * C₀ ^ 2 / (N * z.im)) := by
  have hL : L.Nonempty := Finset.card_pos.1 hL1
  obtain ⟨a₀, -⟩ := hL
  have hNr : (0 : ℝ) < N := by exact_mod_cast Fin.pos a₀
  have hC₁ : 1 ≤ C₀ := eventBounds_one_le_C₀ M hM.sumA hM.boundC a₀
  have hA : (toMatrix x).IsHermitian := toMatrix_isHermitian x
  have hηN : 0 < (N : ℝ) * z.im := mul_pos hNr hz
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hm0 : 0 ≤ (stieltjesEmp (toMatrix x) z).im := by
    rw [eventBounds_im_stieltjesEmp]
    exact mul_nonneg (inv_nonneg.2 hNr.le)
      (Finset.sum_nonneg fun k _ => (green_im_diag_pos hA hz k).le)
  have hmT0 : 0 ≤ (stieltjesT (toMatrix x) L z).im := by
    rw [eventBounds_im_stieltjesT]
    exact mul_nonneg (inv_nonneg.2 hNr.le)
      (Finset.sum_nonneg fun k _ => eventBounds_im_green_diag_nonneg hA hz L k)
  have hmT : (stieltjesT (toMatrix x) L z).im ≤
      (stieltjesEmp (toMatrix x) z).im + p / (N * z.im) := by
    have h1 := norm_stieltjesT_sub_le hA hz L
    have h2 := Complex.abs_im_le_norm (stieltjesT (toMatrix x) L z - stieltjesEmp (toMatrix x) z)
    rw [Complex.sub_im] at h2
    have h3 : (L.card : ℝ) / (N * z.im) ≤ p / (N * z.im) := by
      gcongr
    have := (le_abs_self _).trans (h2.trans (h1.trans h3))
    linarith
  have hΦ : phiL C₀ L z x ^ 2 ≤ 2 * C₀ ^ 2 * phiStarSq p x z := by
    unfold phiL phiStarSq
    have hu : Real.sqrt (C₀ / N) ^ 2 = C₀ / N :=
      Real.sq_sqrt (div_nonneg (by linarith) hNr.le)
    have hv : (C₀ * Real.sqrt ((stieltjesT (toMatrix x) L z).im / (N * z.im))) ^ 2 =
        C₀ ^ 2 * ((stieltjesT (toMatrix x) L z).im / (N * z.im)) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hmT0 hηN.le)]
    have hsq : (Real.sqrt (C₀ / N) + C₀ * Real.sqrt ((stieltjesT (toMatrix x) L z).im /
        (N * z.im))) ^ 2 ≤ 2 * Real.sqrt (C₀ / N) ^ 2 + 2 * (C₀ * Real.sqrt
          ((stieltjesT (toMatrix x) L z).im / (N * z.im))) ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (C₀ / N) - C₀ * Real.sqrt
        ((stieltjesT (toMatrix x) L z).im / (N * z.im)))]
    rw [hu, hv] at hsq
    refine hsq.trans ?_
    have h1 : (stieltjesT (toMatrix x) L z).im / (N * z.im) ≤
        1 / (N * z.im) * ((stieltjesEmp (toMatrix x) z).im + p / (N * z.im)) := by
      rw [one_div_mul_eq_div]
      gcongr
    have hCN : C₀ / N ≤ C₀ ^ 2 * (1 / N) := by
      rw [← mul_one_div]
      gcongr
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg C₀)]
  have h1N : 1 / (N : ℝ) ≤ phiStarSq p x z := by
    unfold phiStarSq
    have : 0 ≤ 1 / (N * z.im) * ((stieltjesEmp (toMatrix x) z).im + p / (N * z.im)) :=
      mul_nonneg (by positivity) (add_nonneg hm0 (by positivity))
    linarith
  have hm0pos : 0 < ‖msc z‖ := norm_pos_iff.2 fun h => by
    have := msc_im_pos hz
    rw [h] at this
    simp at this
  have hm1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hb1 : x ∈ aprioriEvent N p z → (stieltjesEmp (toMatrix x) z).im ≤ 3 / 2 := fun hx => by
    have hdiag : ∀ k, (green (toMatrix x) z k k).im ≤ 3 / 2 := fun k => by
      have h1 := eventBounds_norm_diag_le_LamD x z k
      have h2 := hx.1
      have h3 : ‖green (toMatrix x) z k k‖ ≤ ‖msc z‖ + ‖green (toMatrix x) z k k - msc z‖ := by
        calc ‖green (toMatrix x) z k k‖
            = ‖(green (toMatrix x) z k k - msc z) + msc z‖ := by rw [sub_add_cancel]
          _ ≤ ‖green (toMatrix x) z k k - msc z‖ + ‖msc z‖ := norm_add_le _ _
          _ = _ := add_comm _ _
      have h4 := (le_abs_self _).trans (Complex.abs_im_le_norm (green (toMatrix x) z k k))
      linarith
    rw [eventBounds_im_stieltjesEmp]
    calc (N : ℝ)⁻¹ * ∑ k, (green (toMatrix x) z k k).im ≤ (N : ℝ)⁻¹ * ∑ _k : Fin N, (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hdiag k)
            (inv_nonneg.2 hNr.le)
      _ = 3 / 2 := by simp [Finset.sum_const]; field_simp
  refine ⟨⟨h1N, hΦ⟩, fun hx => ⟨hb1 hx, fun a ha => ?_⟩, fun hη10 hpη hx => ?_⟩
  · have hrow := eventBounds_row_sum M hM.sumA a
    have hclose : ∀ l, ‖greenT (toMatrix x) L z l l - msc z‖ ≤
        33 / 64 * ‖msc z‖ + (if l ∈ L then ‖msc z‖ else 0) := fun l => by
      by_cases hl : l ∈ L
      · have : greenT (toMatrix x) L z l l = 0 := by simp [greenT, hl]
        rw [this, zero_sub, norm_neg]
        simp only [hl, ↓reduceIte]
        linarith
      · simp only [hl, ↓reduceIte, add_zero]
        exact eventBounds_greenT_close x hz hp ⟨a, ha⟩ hLp hx hl
    have hS : mL M L z a x - msc z =
        ∑ l, (M.var a l : ℂ) * (greenT (toMatrix x) L z l l - msc z) := by
      unfold mL
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hrow]
      simp
    have hSn : ‖mL M L z a x - msc z‖ ≤ 33 / 64 * ‖msc z‖ +
        ‖msc z‖ * ∑ l ∈ L, M.var a l := by
      rw [hS]
      calc ‖∑ l, (M.var a l : ℂ) * (greenT (toMatrix x) L z l l - msc z)‖
          ≤ ∑ l, ‖(M.var a l : ℂ) * (greenT (toMatrix x) L z l l - msc z)‖ := norm_sum_le _ _
        _ ≤ ∑ l, M.var a l * (33 / 64 * ‖msc z‖ + (if l ∈ L then ‖msc z‖ else 0)) := by
            refine Finset.sum_le_sum fun l _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (eventBounds_var_nonneg M a l)]
            exact mul_le_mul_of_nonneg_left (hclose l) (eventBounds_var_nonneg M a l)
        _ = 33 / 64 * ‖msc z‖ + ‖msc z‖ * ∑ l ∈ L, M.var a l := by
            simp only [mul_add, Finset.sum_add_distrib]
            rw [← Finset.sum_mul, hrow]
            have : ∑ l, M.var a l * (if l ∈ L then ‖msc z‖ else 0) =
                ‖msc z‖ * ∑ l ∈ L, M.var a l := by
              simp only [mul_ite, mul_zero]
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
                Finset.mul_sum]
              exact Finset.sum_congr rfl fun l _ => mul_comm _ _
            rw [this]
            ring
    have hLsum : ∑ l ∈ L, M.var a l ≤ 1 / 12 := by
      calc ∑ l ∈ L, M.var a l ≤ ∑ _l ∈ L, C₀ / N :=
            Finset.sum_le_sum fun l _ => hM.boundC a l
        _ = L.card * (C₀ / N) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ p * (C₀ / N) := by
            gcongr
        _ = C₀ * p / N := by ring
        _ ≤ 1 / 12 := by
            rw [div_le_div_iff₀ hNr (by norm_num)]
            linarith
    have hSn' : ‖mL M L z a x - msc z‖ ≤ 3 / 5 := by
      have h1 : ‖msc z‖ * ∑ l ∈ L, M.var a l ≤ ‖msc z‖ * (1 / 12) :=
        mul_le_mul_of_nonneg_left hLsum hm0pos.le
      nlinarith
    have hne : z + msc z ≠ 0 := fun h => by
      have := congrArg Complex.im h
      have h2 := msc_im_pos hz
      simp at this
      linarith
    have hinv := msc_add_inv hz
    have hmul : msc z * (z + msc z) = -1 := by
      field_simp at hinv
      linear_combination hinv
    have hnorm : ‖msc z‖ * ‖z + msc z‖ = 1 := by
      rw [← norm_mul, hmul]
      simp
    have hge : 1 ≤ ‖z + msc z‖ := by
      have := norm_nonneg (z + msc z)
      nlinarith
    have h5 : ‖z + msc z‖ ≤ ‖z + mL M L z a x‖ + ‖mL M L z a x - msc z‖ := by
      calc ‖z + msc z‖ = ‖(z + mL M L z a x) - (mL M L z a x - msc z)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  · have hb := hb1 hx
    have h1 : 1 / (N : ℝ) ≤ 10 / (N * z.im) := by
      rw [div_le_div_iff₀ hNr hηN]
      nlinarith
    have h2 : (p : ℝ) / (N * z.im) ≤ 1 := by
      rw [div_le_one hηN]
      exact hpη
    have h3 : phiStarSq p x z ≤ 25 / 2 / (N * z.im) := by
      unfold phiStarSq
      have h4 : 1 / (N * z.im) * ((stieltjesEmp (toMatrix x) z).im + p / (N * z.im)) ≤
          1 / (N * z.im) * (5 / 2) := by
        gcongr
        linarith
      have h5 : 1 / (N * z.im) * (5 / 2 : ℝ) = 5 / 2 / (N * z.im) := by ring
      have h6 : (25 / 2 : ℝ) / (N * z.im) = 10 / (N * z.im) + 5 / 2 / (N * z.im) := by ring
      linarith
    calc phiL C₀ L z x ^ 2 ≤ 2 * C₀ ^ 2 * phiStarSq p x z := hΦ
      _ ≤ 2 * C₀ ^ 2 * (25 / 2 / (N * z.im)) := by gcongr
      _ = 25 * C₀ ^ 2 / (N * z.im) := by ring


section CrudeHelpers

/-- `|∑_{i,l} u_i G_il ū_l| ≤ ‖G‖ ∑ |u_i|²` for the `ℓ²` operator norm. -/
private lemma eventBounds_bilinear_le {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (u : n → ℂ) :
    ‖∑ i, ∑ l, u i * G i l * starRingEnd ℂ (u l)‖ ≤ ‖G‖ * ∑ i, ‖u i‖ ^ 2 := by
  set w : EuclideanSpace ℂ n := WithLp.toLp 2 (fun l => starRingEnd ℂ (u l)) with hw
  have hGw := Matrix.l2_opNorm_mulVec G w
  have hw2 : ‖w‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hw]
  have hsum : ∑ i, ∑ l, u i * G i l * starRingEnd ℂ (u l) = ∑ i, u i * (G.mulVec w.ofLp) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hv2 : ∑ i, ‖(G.mulVec w.ofLp) i‖ ^ 2 ≤ (‖G‖ * ‖w‖) ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hGw 2
    rwa [EuclideanSpace.norm_sq_eq] at h1
  have hS : 0 ≤ ∑ i, ‖u i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hT : ‖∑ i, u i * (G.mulVec w.ofLp) i‖ ≤ ∑ i, ‖u i‖ * ‖(G.mulVec w.ofLp) i‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => (norm_mul _ _).le
  have hT0 : 0 ≤ ∑ i, ‖u i‖ * ‖(G.mulVec w.ofLp) i‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖u i‖)
    (fun i => ‖(G.mulVec w.ofLp) i‖)
  have hK : 0 ≤ ‖G‖ * ∑ i, ‖u i‖ ^ 2 := mul_nonneg (norm_nonneg _) hS
  have hfin : ∑ i, ‖u i‖ * ‖(G.mulVec w.ofLp) i‖ ≤ ‖G‖ * ∑ i, ‖u i‖ ^ 2 := by
    refine (sq_le_sq₀ hT0 hK).1 ?_
    calc (∑ i, ‖u i‖ * ‖(G.mulVec w.ofLp) i‖) ^ 2
        ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖(G.mulVec w.ofLp) i‖ ^ 2 := hCS
      _ ≤ (∑ i, ‖u i‖ ^ 2) * (‖G‖ * ‖w‖) ^ 2 := mul_le_mul_of_nonneg_left hv2 hS
      _ = (‖G‖ * ∑ i, ‖u i‖ ^ 2) ^ 2 := by rw [mul_pow, hw2]; ring
  rw [hsum]
  exact hT.trans hfin


variable {N : ℕ}

/-- A sum over `Fin N` whose terms vanish on `S` is the sum over the complement of `S`. -/
private lemma eventBounds_sum_compl {β : Type*} [AddCommMonoid β] {S : Finset (Fin N)}
    (f : Fin N → β) (h : ∀ i ∈ S, f i = 0) : ∑ i, f i = ∑ i : {i // i ∉ S}, f i.val := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => i ∉ S) (by simp) f,
    Finset.sum_filter_of_ne]
  intro i _ hi
  by_contra hS
  exact hi (h i hS)

/-- A sum over the complement of `S` of nonnegative terms is at most the full sum. -/
private lemma eventBounds_sum_compl_le {S : Finset (Fin N)} (f : Fin N → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ a : {i // i ∉ S}, f a.val ≤ ∑ k, f k := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => i ∉ S) (by simp) f]
  exact Finset.sum_le_univ_sum_of_nonneg hf

private lemma eventBounds_toC_star (y : 𝕜) : toC (star y) = starRingEnd ℂ (toC y) := by
  apply Complex.ext <;> simp [toC]

private lemma eventBounds_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- `|G^{(S)}_kl| ≤ η⁻¹`. -/
private lemma eventBounds_norm_greenT_le {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (k l : Fin N) :
    ‖greenT A T z k l‖ ≤ 1 / z.im := by
  by_cases h : k ∉ T ∧ l ∉ T
  · have hP : (minor A T).IsHermitian := hA.submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    have : greenT A T z k l = green (minor A T) z ⟨k, h.1⟩ ⟨l, h.2⟩ := by
      simp [greenT, greenMinor, h.1, h.2]
    rw [this]
    exact norm_green_apply_le hP hz _ _
  · have : greenT A T z k l = 0 := by
      by_cases hk : k ∈ T
      · simp [greenT, hk]
      · have hl : l ∈ T := by tauto
        simp [greenT, hl]
    rw [this, norm_zero]
    exact (one_div_pos.2 hz).le

/-- `|∑_{i,l} u_i G^{(S)}_il ū_l| ≤ η⁻¹ ∑ |u_i|²`. -/
private lemma eventBounds_quad_le {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (S : Finset (Fin N)) (u : Fin N → ℂ) :
    ‖∑ i, ∑ l, u i * greenT A S z i l * starRingEnd ℂ (u l)‖ ≤ 1 / z.im * ∑ i, ‖u i‖ ^ 2 := by
  have hP : (minor A S).IsHermitian := hA.submatrix (Subtype.val : {i // i ∉ S} → Fin N)
  have hG := norm_green_le hP hz
  have hinner : ∀ i : Fin N, ∑ l, u i * greenT A S z i l * starRingEnd ℂ (u l) =
      ∑ l : {l // l ∉ S}, u i * greenT A S z i l.val * starRingEnd ℂ (u l.val) := fun i =>
    eventBounds_sum_compl (S := S) (fun l => u i * greenT A S z i l * starRingEnd ℂ (u l))
      fun l hl => by simp [greenT, hl]
  have hsub : ∑ i, ∑ l, u i * greenT A S z i l * starRingEnd ℂ (u l) =
      ∑ i : {i // i ∉ S}, ∑ l : {l // l ∉ S},
        u i.val * greenMinor A S z i l * starRingEnd ℂ (u l.val) := by
    rw [eventBounds_sum_compl (S := S)
      (fun i => ∑ l, u i * greenT A S z i l * starRingEnd ℂ (u l))
      fun i hi => by simp [greenT, hi]]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hinner i.val]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [greenT, i.2, l.2]
  rw [hsub]
  refine (eventBounds_bilinear_le (greenMinor A S z) fun i : {i // i ∉ S} => u i.val).trans ?_
  have h2 := eventBounds_sum_compl_le (S := S) (fun i => ‖u i‖ ^ 2) fun i => by positivity
  exact mul_le_mul hG h2 (Finset.sum_nonneg fun i _ => by positivity) (by positivity)


/-- The pointwise bound `|X_k| ≤ |h_kk| + N ∑_i |h_ki|² + N` for `η ≥ 1/N`. -/
private lemma eventBounds_norm_selfX_le (M : Ensemble 𝕜 N) (hA : M.AssumptionA) {z : ℂ}
    (hη : 1 / (N : ℝ) ≤ z.im) (k : Fin N) (x : Pair N → 𝕜) :
    ‖selfX (toMatrix x) M.varMatrix z k‖ ≤
      ‖toMatrix x k k‖ + N * ∑ i, ‖toMatrix x k i‖ ^ 2 + N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hH := toMatrix_isHermitian x
  have hηN : 1 / z.im ≤ N := by
    rw [one_div_le hz hNr]
    exact hη
  have hQ : ‖∑ i, ∑ l, toC (toMatrix x k i) * greenT (toMatrix x) {k} z i l *
      toC (toMatrix x l k)‖ ≤ N * ∑ i, ‖toMatrix x k i‖ ^ 2 := by
    have h1 : ∀ l, toC (toMatrix x l k) = starRingEnd ℂ (toC (toMatrix x k l)) := fun l => by
      rw [← eventBounds_toC_star]
      congr 1
      exact (hH.apply k l).symm ▸ (star_star _).symm
    simp only [h1]
    refine (eventBounds_quad_le hH hz {k} fun i => toC (toMatrix x k i)).trans ?_
    simp only [eventBounds_norm_toC]
    exact mul_le_mul_of_nonneg_right hηN (Finset.sum_nonneg fun i _ => by positivity)
  have hR : ‖∑ i, (M.varMatrix k i : ℂ) * greenT (toMatrix x) {k} z i i‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖(M.varMatrix k i : ℂ) * greenT (toMatrix x) {k} z i i‖
        ≤ ∑ i, M.var k i * (1 / z.im) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have : M.varMatrix k i = M.var k i := rfl
          rw [this, abs_of_nonneg (eventBounds_var_nonneg M k i)]
          exact mul_le_mul_of_nonneg_left (eventBounds_norm_greenT_le hH hz {k} i i)
            (eventBounds_var_nonneg M k i)
      _ = 1 / z.im := by rw [← Finset.sum_mul, eventBounds_row_sum M hA k, one_mul]
      _ ≤ N := hηN
  unfold selfX selfZ
  calc ‖toC (toMatrix x k k) - (∑ i, ∑ l, toC (toMatrix x k i) * greenT (toMatrix x) {k} z i l *
        toC (toMatrix x l k) - ∑ i, (M.varMatrix k i : ℂ) * greenT (toMatrix x) {k} z i i)‖
      ≤ ‖toC (toMatrix x k k)‖ + ‖∑ i, ∑ l, toC (toMatrix x k i) * greenT (toMatrix x) {k} z i l *
        toC (toMatrix x l k) - ∑ i, (M.varMatrix k i : ℂ) * greenT (toMatrix x) {k} z i i‖ :=
        norm_sub_le _ _
    _ ≤ ‖toC (toMatrix x k k)‖ + (‖∑ i, ∑ l, toC (toMatrix x k i) *
        greenT (toMatrix x) {k} z i l * toC (toMatrix x l k)‖ +
        ‖∑ i, (M.varMatrix k i : ℂ) * greenT (toMatrix x) {k} z i i‖) := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖toMatrix x k k‖ + N * ∑ i, ‖toMatrix x k i‖ ^ 2 + N := by
        rw [eventBounds_norm_toC]
        linarith


private lemma eventBounds_norm_entry_le (x : Pair N → 𝕜) (i j : Fin N) :
    ‖toMatrix x i j‖ ≤ ‖x (Pair.mk' i j)‖ := by
  unfold toMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact le_rfl
  · simp
  · simpa using RCLike.abs_re_le_norm (x (Pair.mk' i j))

private lemma eventBounds_continuous_entry (i j : Fin N) :
    Continuous fun x : Pair N → 𝕜 => toMatrix x i j := by
  unfold toMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact RCLike.continuous_ofReal.comp (RCLike.continuous_re.comp (continuous_apply _))

/-- The `L^r` norm of an entry `h_ij` is at most `(C_ϑ r)^a σ_ij` (Lemma 4.1 (a)). -/
private lemma eventBounds_eLpNorm_entry (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (i j : Fin N) {r : ℝ}
    (hr : 1 ≤ r) :
    eLpNorm (fun x => toMatrix x i j) (ENNReal.ofReal r) M.prodLaw ≤
      ENNReal.ofReal ((cTheta ϑ⁻¹ * r) ^ ϑ⁻¹ * Real.sqrt (M.var i j)) := by
  have hr0 : 0 < r := by linarith
  have ha : 0 < ϑ⁻¹ := inv_pos.2 hϑ
  have hC : 0 ≤ cTheta ϑ⁻¹ * r := by unfold cTheta; positivity
  set P := Pair.mk' i j with hP
  have h1 : eLpNorm (fun x => toMatrix x i j) (ENNReal.ofReal r) M.prodLaw ≤
      eLpNorm (fun x : Pair N → 𝕜 => x P) (ENNReal.ofReal r) M.prodLaw :=
    eLpNorm_mono (eventBounds_continuous_entry i j).aestronglyMeasurable fun x =>
      eventBounds_norm_entry_le x i j
  refine h1.trans ?_
  have h2 : eLpNorm (fun x : Pair N → 𝕜 => x P) (ENNReal.ofReal r) M.prodLaw =
      eLpNorm (id : 𝕜 → 𝕜) (ENNReal.ofReal r) (M.law P) := by
    have hmp := measurePreserving_eval M.law P
    rw [← hmp.map_eq, eLpNorm_map_measure aestronglyMeasurable_id hmp.measurable.aemeasurable]
    rfl
  rw [h2]
  obtain ⟨hint, -⟩ := moments_bound hϑ hϑ1 (μ := M.law P) (Real.sqrt_nonneg (M.varPair P))
    (fun x hx => hM.subexp P x hx) hr
  have hmom := Ensemble.Assumptions.moment_le hM hϑ hϑ1 P hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top
    aestronglyMeasurable_id, ENNReal.toReal_ofReal hr0.le]
  have h3 : ∫⁻ y, ‖y‖ₑ ^ r ∂M.law P = ENNReal.ofReal (∫ y, ‖y‖ ^ r ∂M.law P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)]
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  simp only [id]
  rw [h3]
  have hs : 0 ≤ Real.sqrt (M.varPair P) := Real.sqrt_nonneg _
  calc ENNReal.ofReal (∫ y, ‖y‖ ^ r ∂M.law P) ^ (1 / r)
      = ENNReal.ofReal ((∫ y, ‖y‖ ^ r ∂M.law P) ^ (1 / r)) :=
        ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _)
          (by positivity)
    _ ≤ ENNReal.ofReal (((cTheta ϑ⁻¹ * r) ^ (ϑ⁻¹ * r) * Real.sqrt (M.varPair P) ^ r) ^ (1 / r)) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _) hmom
            (by positivity))
    _ = ENNReal.ofReal ((cTheta ϑ⁻¹ * r) ^ ϑ⁻¹ * Real.sqrt (M.var i j)) := by
        congr 1
        rw [Real.mul_rpow (Real.rpow_nonneg hC _) (Real.rpow_nonneg hs _),
          ← Real.rpow_mul hC, ← Real.rpow_mul hs, mul_one_div_cancel hr0.ne', Real.rpow_one,
          mul_comm ϑ⁻¹ r, mul_one_div, mul_div_cancel_left₀ _ hr0.ne']
        rfl


/-- The `L^q` norm of `|h_ij|²` is the square of the `L^{2q}` norm of `h_ij`. -/
private lemma eventBounds_eLpNorm_entry_sq (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (i j : Fin N) {q : ℝ}
    (hq : 1 ≤ q) :
    eLpNorm (fun x => ‖toMatrix x i j‖ ^ 2) (ENNReal.ofReal q) M.prodLaw ≤
      ENNReal.ofReal (((cTheta ϑ⁻¹ * (q * 2)) ^ ϑ⁻¹) ^ 2 * M.var i j) := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < ϑ⁻¹ := inv_pos.2 hϑ
  have hC : 0 ≤ cTheta ϑ⁻¹ * (q * 2) := by unfold cTheta; positivity
  have hfun : (fun x : Pair N → 𝕜 => ‖toMatrix x i j‖ ^ 2) =
      fun x => ‖toMatrix x i j‖ ^ (2 : ℝ) := by
    funext x
    rw [Real.rpow_two]
  rw [hfun, eLpNorm_norm_rpow _ (eventBounds_continuous_entry i j).aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 2), ← ENNReal.ofReal_mul hq0.le, ENNReal.rpow_two]
  have h1 := eventBounds_eLpNorm_entry M hM hϑ hϑ1 i j (r := q * 2) (by linarith)
  calc eLpNorm (fun x => toMatrix x i j) (ENNReal.ofReal (q * ENNReal.toReal 2)) M.prodLaw ^ 2
      ≤ ENNReal.ofReal ((cTheta ϑ⁻¹ * (q * 2)) ^ ϑ⁻¹ * Real.sqrt (M.var i j)) ^ 2 := by
        gcongr
        simpa using h1
    _ = ENNReal.ofReal (((cTheta ϑ⁻¹ * (q * 2)) ^ ϑ⁻¹ * Real.sqrt (M.var i j)) ^ 2) :=
        (ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hC _) (Real.sqrt_nonneg _)) 2).symm
    _ = ENNReal.ofReal (((cTheta ϑ⁻¹ * (q * 2)) ^ ϑ⁻¹) ^ 2 * M.var i j) := by
        rw [mul_pow, Real.sq_sqrt (eventBounds_var_nonneg M i j)]

end CrudeHelpers

/-- Lemma 6.7: the crude moment bound `‖X_k‖_q ≤ 3N(2C_ϑ q)^{2a}`, and `‖X_k‖_{2p} ≤ N²` when
`3(4C_ϑ p)^{2a} ≤ N`. -/
theorem faCrude {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {z : ℂ} (hη : 1 / N ≤ z.im)
    (k : Fin N) :
    (∀ q : ℝ, 2 ≤ q →
      eLpNorm (fun x => selfX (toMatrix x) M.varMatrix z k) (ENNReal.ofReal q) M.prodLaw ≤
        ENNReal.ofReal (3 * N * (2 * cTheta ϑ⁻¹ * q) ^ (2 * ϑ⁻¹))) ∧
    (∀ p : ℕ, 1 ≤ p → 3 * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹) ≤ N →
      eLpNorm (fun x => selfX (toMatrix x) M.varMatrix z k) (2 * p) M.prodLaw ≤
        ENNReal.ofReal ((N : ℝ) ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos k
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have ha0 : 0 < ϑ⁻¹ := by linarith
  have hsc : Continuous fun x : Pair N → 𝕜 => selfX (toMatrix x) M.varMatrix z k :=
    ((polyGrowth_schurM M 0 hz ∅).2.2.2.2.1 k).1
  have hpart1 : ∀ q : ℝ, 2 ≤ q →
      eLpNorm (fun x => selfX (toMatrix x) M.varMatrix z k) (ENNReal.ofReal q) M.prodLaw ≤
        ENNReal.ofReal (3 * N * (2 * cTheta ϑ⁻¹ * q) ^ (2 * ϑ⁻¹)) := by
    intro q hq
    have hq0 : 0 < q := by linarith
    have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    set T : ℝ := (2 * cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ with hT
    have hC90 : 90 ≤ cTheta ϑ⁻¹ := by unfold cTheta; linarith
    have hbase : 1 ≤ 2 * cTheta ϑ⁻¹ * q := by nlinarith
    have hT1 : 1 ≤ T := Real.one_le_rpow hbase ha0.le
    have hT2 : T ^ 2 = (2 * cTheta ϑ⁻¹ * q) ^ (2 * ϑ⁻¹) := by
      rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
      ring_nf
    have hdiag : (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ ≤ T := by
      rw [hT]
      exact Real.rpow_le_rpow (by unfold cTheta; positivity) (by nlinarith) ha0.le
    -- the three terms
    have hk1 : eLpNorm (fun x : Pair N → 𝕜 => ‖toMatrix x k k‖) (ENNReal.ofReal q) M.prodLaw ≤
        ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var k k)) := by
      rw [eLpNorm_norm _ (eventBounds_continuous_entry k k).aestronglyMeasurable]
      exact eventBounds_eLpNorm_entry M hM hϑ hϑ1 k k (by linarith)
    have hk2 : ∀ i, eLpNorm (fun x : Pair N → 𝕜 => ‖toMatrix x k i‖ ^ 2) (ENNReal.ofReal q)
        M.prodLaw ≤ ENNReal.ofReal (T ^ 2 * M.var k i) := by
      intro i
      refine (eventBounds_eLpNorm_entry_sq M hM hϑ hϑ1 k i (by linarith)).trans ?_
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      have : 2 * cTheta ϑ⁻¹ * q = cTheta ϑ⁻¹ * (q * 2) := by ring
      rw [hT, this]
    have hsum : eLpNorm (fun x : Pair N → 𝕜 => ∑ i, ‖toMatrix x k i‖ ^ 2) (ENNReal.ofReal q)
        M.prodLaw ≤ ENNReal.ofReal (T ^ 2) := by
      have h1 := eLpNorm_sum_le (μ := M.prodLaw) (s := Finset.univ)
        (f := fun i (x : Pair N → 𝕜) => ‖toMatrix x k i‖ ^ 2) hq1
      have h2 : (∑ i : Fin N, fun x : Pair N → 𝕜 => ‖toMatrix x k i‖ ^ 2) =
          fun x => ∑ i, ‖toMatrix x k i‖ ^ 2 := by
        funext x
        simp [Finset.sum_apply]
      rw [h2] at h1
      refine h1.trans ?_
      calc ∑ i : Fin N, eLpNorm (fun x : Pair N → 𝕜 => ‖toMatrix x k i‖ ^ 2) (ENNReal.ofReal q)
            M.prodLaw ≤ ∑ i : Fin N, ENNReal.ofReal (T ^ 2 * M.var k i) :=
            Finset.sum_le_sum fun i _ => hk2 i
        _ = ENNReal.ofReal (∑ i : Fin N, T ^ 2 * M.var k i) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ =>
              mul_nonneg (by positivity) (eventBounds_var_nonneg M k i)).symm
        _ = ENNReal.ofReal (T ^ 2) := by
            rw [← Finset.mul_sum, eventBounds_row_sum M hM.sumA k, mul_one]
    have hk3 : eLpNorm (fun x : Pair N → 𝕜 => (N : ℝ) * ∑ i, ‖toMatrix x k i‖ ^ 2)
        (ENNReal.ofReal q) M.prodLaw ≤ ENNReal.ofReal (N * T ^ 2) := by
      have : (fun x : Pair N → 𝕜 => (N : ℝ) * ∑ i, ‖toMatrix x k i‖ ^ 2) =
          (N : ℝ) • fun x : Pair N → 𝕜 => ∑ i, ‖toMatrix x k i‖ ^ 2 := rfl
      rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hNr.le,
        ENNReal.ofReal_mul hNr.le]
      gcongr
    have hk4 : eLpNorm (fun _ : Pair N → 𝕜 => (N : ℝ)) (ENNReal.ofReal q) M.prodLaw ≤
        ENNReal.ofReal N := by
      rw [eLpNorm_const _ (ENNReal.ofReal_pos.2 hq0).ne' (IsProbabilityMeasure.ne_zero _)]
      simp
    have hvar : Real.sqrt (M.var k k) ≤ 1 := by
      rw [Real.sqrt_le_one]
      calc M.var k k ≤ ∑ l, M.var k l :=
            Finset.single_le_sum (f := fun l => M.var k l) (fun l _ => eventBounds_var_nonneg M k l)
              (Finset.mem_univ k)
        _ = 1 := eventBounds_row_sum M hM.sumA k
    have hreal : (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var k k) + N * T ^ 2 + N ≤
        3 * N * (2 * cTheta ϑ⁻¹ * q) ^ (2 * ϑ⁻¹) := by
      rw [← hT2]
      have h1 : (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var k k) ≤ T ^ 2 := by
        calc (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var k k) ≤ T * 1 :=
              mul_le_mul hdiag hvar (Real.sqrt_nonneg _) (by linarith)
          _ ≤ T ^ 2 := by nlinarith
      have h2 : 1 ≤ T ^ 2 := by nlinarith
      have h3 : T ^ 2 ≤ N * T ^ 2 := by nlinarith
      have h4 : (N : ℝ) ≤ N * T ^ 2 := by nlinarith
      linarith
    calc eLpNorm (fun x => selfX (toMatrix x) M.varMatrix z k) (ENNReal.ofReal q) M.prodLaw
        ≤ eLpNorm (fun x : Pair N → 𝕜 => ‖toMatrix x k k‖ + N * ∑ i, ‖toMatrix x k i‖ ^ 2 + N)
          (ENNReal.ofReal q) M.prodLaw :=
          eLpNorm_mono_ae_real hsc.aestronglyMeasurable (Eventually.of_forall fun x =>
            eventBounds_norm_selfX_le M hM.sumA hη k x)
      _ ≤ eLpNorm (fun x : Pair N → 𝕜 => ‖toMatrix x k k‖) (ENNReal.ofReal q) M.prodLaw +
          eLpNorm (fun x : Pair N → 𝕜 => (N : ℝ) * ∑ i, ‖toMatrix x k i‖ ^ 2)
            (ENNReal.ofReal q) M.prodLaw +
          eLpNorm (fun _ : Pair N → 𝕜 => (N : ℝ)) (ENNReal.ofReal q) M.prodLaw :=
          (eLpNorm_add_le (f := fun x : Pair N → 𝕜 => ‖toMatrix x k k‖ +
            N * ∑ i, ‖toMatrix x k i‖ ^ 2) (g := fun _ => (N : ℝ)) hq1).trans
            (by gcongr; exact eLpNorm_add_le hq1)
      _ ≤ ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var k k)) +
          ENNReal.ofReal (N * T ^ 2) + ENNReal.ofReal N := by gcongr
      _ = ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var k k) + N * T ^ 2 + N) := by
          rw [ENNReal.ofReal_add (by positivity) hNr.le,
            ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  refine ⟨hpart1, fun p hp hpN => ?_⟩
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h2p : ((2 : ENNReal) * p) = ENNReal.ofReal (2 * p) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
    simp
  rw [h2p]
  refine (hpart1 (2 * p) (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
  have e : 2 * cTheta ϑ⁻¹ * (2 * (p : ℝ)) = 4 * cTheta ϑ⁻¹ * p := by ring
  rw [e]
  calc 3 * (N : ℝ) * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹)
      = N * (3 * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹)) := by ring
    _ ≤ N * N := mul_le_mul_of_nonneg_left hpN hNr.le
    _ = (N : ℝ) ^ 2 := by ring

end Rigidity
