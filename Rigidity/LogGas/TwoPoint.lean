module

public import Mathlib

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

/-!
# The two-point function `Λ`

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].
-/

namespace Rigidity

/-- `Λ(r) = log((1 + r)/(2√r)) = log cosh(½ log r)` (17.2). -/
noncomputable def logCoshRatio (r : ℝ) : ℝ := Real.log ((1 + r) / (2 * Real.sqrt r))

/-- `c₀ = log cosh ½` (Lemma 17.6). -/
noncomputable def cZero : ℝ := Real.log (Real.cosh (1 / 2))

/-- `C⋆(A, A', ρ) = max(A²/(2c₀), (9/8)(eρA')²)` (Lemma 17.6). -/
noncomputable def cStar (A A' ρ : ℝ) : ℝ :=
  max (A ^ 2 / (2 * cZero)) (9 / 8 * (Real.exp 1 * ρ * A') ^ 2)

/-- For `t ≥ 0`, `1 + t²/2 ≤ cosh t` (Lemma 17.6, Step 1). -/
private theorem one_add_sq_div_two_le_cosh {t : ℝ} (ht : 0 ≤ t) :
    1 + t ^ 2 / 2 ≤ Real.cosh t := by
  have h := Real.cosh_two_mul (t / 2)
  have h2 : Real.cosh (2 * (t / 2)) = Real.cosh t := by congr 1; ring
  have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have hc := Real.cosh_sq (t / 2)
  rw [h2] at h
  have hs2 : (t / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hs 2
  nlinarith

/-- For `0 ≤ ϑ ≤ 1`, `ϑ²/9 ≤ log cosh(ϑ/2)` (Lemma 17.6, Step 1). -/
private theorem sq_div_nine_le_log_cosh {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ ^ 2 / 9 ≤ Real.log (Real.cosh (θ / 2)) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = θ ^ 2 / 8 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 8 := by rw [hy]; nlinarith
  have hc : 1 + y ≤ Real.cosh (θ / 2) := by
    have := one_add_sq_div_two_le_cosh (t := θ / 2) (by linarith)
    rw [hy]
    nlinarith
  have hpos : 0 < 1 + y := by linarith
  have hlog : y / (1 + y) ≤ Real.log (1 + y) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + y)⁻¹) (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have e : (1 + y)⁻¹ - 1 = -(y / (1 + y)) := by field_simp; ring
    linarith
  have hlow : 8 * y / 9 ≤ y / (1 + y) := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hmono : Real.log (1 + y) ≤ Real.log (Real.cosh (θ / 2)) :=
    Real.log_le_log hpos hc
  have : θ ^ 2 / 9 = 8 * y / 9 := by rw [hy]; ring
  linarith

/-- If `0 < v ≤ u`, `v ≤ ρ` and `log(u/v) < 1`, then `u - v ≤ eρ log(u/v)`
(Lemma 17.6, Case 3). -/
private theorem sub_le_exp_mul_log_div {u v ρ : ℝ} (hv : 0 < v) (hvu : v ≤ u) (hvρ : v ≤ ρ)
    (hlog : Real.log (u / v) < 1) : u - v ≤ Real.exp 1 * ρ * Real.log (u / v) := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have hq : 1 ≤ u / v := by rw [le_div_iff₀ hv]; linarith
  have hl0 : 0 ≤ Real.log (u / v) := Real.log_nonneg hq
  have hex : u / v < Real.exp 1 := by
    have := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (div_pos hu hv)] at this
  have hue : u ≤ Real.exp 1 * ρ := by
    have h1 : u < Real.exp 1 * v := by
      rw [div_lt_iff₀ hv] at hex; linarith
    have h2 : Real.exp 1 * v ≤ Real.exp 1 * ρ :=
      mul_le_mul_of_nonneg_left hvρ (Real.exp_pos 1).le
    linarith
  have hlogv : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (div_pos hv hu)
  have hinv : Real.log (v / u) = -Real.log (u / v) := by
    rw [← inv_div, Real.log_inv]
  rw [hinv] at hlogv
  have hvu' : v / u * u = v := div_mul_cancel₀ v hu.ne'
  have h3 : u - v ≤ u * Real.log (u / v) := by nlinarith
  have h4 : u * Real.log (u / v) ≤ Real.exp 1 * ρ * Real.log (u / v) :=
    mul_le_mul_of_nonneg_right hue hl0
  linarith

theorem logCoshRatio_eq {r : ℝ} (hr : 0 < r) :
    logCoshRatio r = Real.log (Real.cosh (Real.log r / 2)) := by
  unfold logCoshRatio
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h1 : Real.log r / 2 = Real.log (Real.sqrt r) := (Real.log_sqrt hr.le).symm
  rw [h1, Real.cosh_log hs]
  congr 1
  have h2 := Real.sq_sqrt hr.le
  field_simp
  nlinarith

theorem logCoshRatio_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ logCoshRatio r := by
  rw [logCoshRatio_eq hr]
  exact Real.log_nonneg (Real.one_le_cosh _)

theorem cZero_pos : 0 < cZero := by
  unfold cZero
  exact Real.log_pos (Real.one_lt_cosh.mpr (by norm_num))

/-- Lemma 17.6 (two-point inequality). -/
theorem twoPoint_ineq {A A' ρ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ) {g : ℝ → ℝ}
    (hgb : ∀ u, 0 < u → |g u| ≤ A)
    (hgl : ∀ u v, 0 < u → 0 < v → |g u - g v| ≤ A' * |u - v|)
    (hg0 : ∀ u, ρ < u → g u = 0) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (s : ℝ) :
    s * (g u - g v) ≤ 2 * logCoshRatio (u / v) + cStar A A' ρ * s ^ 2 := by
  have hc0 := cZero_pos
  have huv : 0 < u / v := div_pos hu hv
  have hΛ0 : 0 ≤ logCoshRatio (u / v) := logCoshRatio_nonneg huv
  have hstar1 : A ^ 2 / (2 * cZero) ≤ cStar A A' ρ := le_max_left _ _
  have hstar2 : 9 / 8 * (Real.exp 1 * ρ * A') ^ 2 ≤ cStar A A' ρ := le_max_right _ _
  have hstar0 : 0 ≤ cStar A A' ρ := le_trans (by positivity) hstar1
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = |Real.log (u / v)| := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact abs_nonneg _
  have hΛθ : logCoshRatio (u / v) = Real.log (Real.cosh (θ / 2)) := by
    rw [logCoshRatio_eq huv, hθ, ← Real.cosh_abs (Real.log (u / v) / 2), abs_div, abs_two]
  have hs0 : 0 ≤ cStar A A' ρ * s ^ 2 := by positivity
  by_cases h1 : 1 ≤ θ
  · -- Case 1: `ϑ ≥ 1`
    have hΛ : cZero ≤ logCoshRatio (u / v) := by
      rw [hΛθ]
      unfold cZero
      apply Real.log_le_log (Real.cosh_pos _)
      rw [Real.cosh_le_cosh, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_of_nonneg (by linarith : 0 ≤ θ / 2)]
      linarith
    have hgu := hgb u hu
    have hgv := hgb v hv
    have hs1 : s * (g u - g v) ≤ 2 * (|s| * A) := by
      calc s * (g u - g v) ≤ |s * (g u - g v)| := le_abs_self _
        _ = |s| * |g u - g v| := abs_mul _ _
        _ ≤ |s| * (|g u| + |g v|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
        _ ≤ |s| * (A + A) :=
          mul_le_mul_of_nonneg_left (add_le_add hgu hgv) (abs_nonneg _)
        _ = 2 * (|s| * A) := by ring
    have hs2 : 2 * (|s| * A) ≤ 2 * cZero + A ^ 2 / (2 * cZero) * s ^ 2 := by
      have e : A ^ 2 / (2 * cZero) * s ^ 2 = (|s| * A) ^ 2 / (2 * cZero) := by
        rw [mul_pow, sq_abs]; ring
      rw [e, ← sub_nonneg]
      have e2 : 2 * cZero + (|s| * A) ^ 2 / (2 * cZero) - 2 * (|s| * A)
          = (|s| * A - 2 * cZero) ^ 2 / (2 * cZero) := by
        field_simp
        ring
      rw [e2]
      positivity
    have hs3 : A ^ 2 / (2 * cZero) * s ^ 2 ≤ cStar A A' ρ * s ^ 2 :=
      mul_le_mul_of_nonneg_right hstar1 (sq_nonneg s)
    linarith
  · have h1 : θ < 1 := lt_of_not_ge h1
    by_cases hmin : ρ < u ∧ ρ < v
    · -- Case 2: `ϑ < 1` and `min(u, v) > ρ`
      rw [hg0 u hmin.1, hg0 v hmin.2]
      linarith
    · -- Case 3: `ϑ < 1` and `min(u, v) ≤ ρ`
      have hmin' : u ≤ ρ ∨ v ≤ ρ := by
        by_contra hcon
        exact hmin ⟨lt_of_not_ge fun h => hcon (Or.inl h),
          lt_of_not_ge fun h => hcon (Or.inr h)⟩
      have hdist : |u - v| ≤ Real.exp 1 * ρ * θ := by
        rcases le_total v u with hvu | huv'
        · have hl : θ = Real.log (u / v) := by
            rw [hθ]
            exact abs_of_nonneg (Real.log_nonneg ((le_div_iff₀ hv).mpr (by linarith)))
          have hvρ : v ≤ ρ := by
            rcases hmin' with h | h
            · exact le_trans hvu h
            · exact h
          rw [abs_of_nonneg (by linarith), hl]
          exact sub_le_exp_mul_log_div hv hvu hvρ (hl ▸ h1)
        · have hl : θ = Real.log (v / u) := by
            rw [hθ, Real.log_div hu.ne' hv.ne', ← neg_sub, abs_neg, Real.log_div hv.ne' hu.ne']
            exact abs_of_nonneg (by
              have := Real.log_le_log hu huv'
              linarith)
          have huρ : u ≤ ρ := by
            rcases hmin' with h | h
            · exact h
            · exact le_trans huv' h
          rw [abs_of_nonpos (by linarith), neg_sub, hl]
          exact sub_le_exp_mul_log_div hu huv' huρ (hl ▸ h1)
      have hX : 0 ≤ Real.exp 1 * ρ * A' := by positivity
      have hlip := hgl u v hu hv
      have hbound : s * (g u - g v) ≤ (Real.exp 1 * ρ * A') * |s| * θ := by
        calc s * (g u - g v) ≤ |s * (g u - g v)| := le_abs_self _
          _ = |s| * |g u - g v| := abs_mul _ _
          _ ≤ |s| * (A' * |u - v|) := mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
          _ ≤ |s| * (A' * (Real.exp 1 * ρ * θ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist hA') (abs_nonneg _)
          _ = (Real.exp 1 * ρ * A') * |s| * θ := by ring
      have hsq : (Real.exp 1 * ρ * A') * |s| * θ
          ≤ 2 / 9 * θ ^ 2 + 9 / 8 * (Real.exp 1 * ρ * A') ^ 2 * s ^ 2 := by
        have := sq_abs s
        nlinarith [sq_nonneg (θ - 9 / 4 * (Real.exp 1 * ρ * A') * |s|)]
      have hstep1 := sq_div_nine_le_log_cosh hθ0 h1.le
      have hs3 : 9 / 8 * (Real.exp 1 * ρ * A') ^ 2 * s ^ 2 ≤ cStar A A' ρ * s ^ 2 :=
        mul_le_mul_of_nonneg_right hstar2 (sq_nonneg s)
      rw [hΛθ]
      linarith

end Rigidity
