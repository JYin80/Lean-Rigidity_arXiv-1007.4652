import Mathlib

open MeasureTheory Real Matrix
open scoped ENNReal

/-! # Vector stability on `𝐞^⊥`

Lemma 3.9 of NP v1.1 §3.3: for a symmetric matrix `B` obeying conditions (A), (B), (C) of
Definition 2.2, the map `1 - ζ B` with `‖ζ‖ ≤ 1` is invertible on the hyperplane `∑ xᵢ = 0`, with
an `ℓ²` inverse bound `δ_min⁻¹` and a sup-norm inverse bound `C_s = 1 + √C₀ / δ_min`, free of
`log N`. -/

namespace Rigidity

/-- Conditions (A), (B), (C) of Definition 2.2 on a real matrix `B` (§3.3). -/
structure VarProfile {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (δm δp C₀ : ℝ) : Prop where
  symm : B.IsSymm
  nonneg : ∀ i j, 0 ≤ B i j
  sumA : ∀ j, ∑ i, B i j = 1
  specB : ∀ v : Fin N → ℝ, ∑ i, v i = 0 →
    (-1 + δm) * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (B *ᵥ v) ∧ v ⬝ᵥ (B *ᵥ v) ≤ (1 - δp) * ∑ i, v i ^ 2
  boundC : ∀ i j, B i j ≤ C₀ / N

/-- `C_s = 1 + √C₀ / δ_min` of Lemma 3.9. -/
noncomputable def stabCs (C₀ δm δp : ℝ) : ℝ := 1 + Real.sqrt C₀ / min δm δp

/-- `λ_st = 1/(576 C_s)` of (3.7). -/
noncomputable def lamSt (C₀ δm δp : ℝ) : ℝ := 1 / (576 * stabCs C₀ δm δp)

/-! ### Auxiliary facts on the complexified matrix

For `x` with `∑ x i = 0`, the sesquilinear form `∑ conj (x i) * (B x) i` is real and obeys the
quadratic-form bounds of condition (B) (proof of Lemma 3.9, Step 2). -/

private lemma vecStab_form {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ} {δm δp C₀ : ℝ}
    (hB : VarProfile B δm δp C₀) {x : Fin N → ℂ} (hx : ∑ i, x i = 0) :
    ∃ q : ℝ, ∑ i, (starRingEnd ℂ) (x i) * (B.map (fun r : ℝ => (r : ℂ)) *ᵥ x) i = q ∧
      (-1 + δm) * ∑ i, ‖x i‖ ^ 2 ≤ q ∧ q ≤ (1 - δp) * ∑ i, ‖x i‖ ^ 2 := by
  set a : Fin N → ℝ := fun i => (x i).re with ha_def
  set b : Fin N → ℝ := fun i => (x i).im with hb_def
  have ha : ∑ i, a i = 0 := by
    have := congrArg Complex.re hx
    simpa [Complex.re_sum, ha_def] using this
  have hb : ∑ i, b i = 0 := by
    have := congrArg Complex.im hx
    simpa [Complex.im_sum, hb_def] using this
  have hS : ∑ i, ‖x i‖ ^ 2 = ∑ i, a i ^ 2 + ∑ i, b i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq, ha_def, hb_def]
  have hsym : a ⬝ᵥ (B *ᵥ b) = b ⬝ᵥ (B *ᵥ a) := by
    have h : ∀ v : Fin N → ℝ, v ᵥ* B = B *ᵥ v := fun v => by
      rw [← Matrix.vecMul_transpose, hB.symm.eq]
    rw [Matrix.dotProduct_mulVec, h, dotProduct_comm]
  refine ⟨a ⬝ᵥ (B *ᵥ a) + b ⬝ᵥ (B *ᵥ b), ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp [Complex.re_sum, Matrix.mulVec, dotProduct, Finset.mul_sum, ha_def, hb_def]
      simp only [Finset.sum_add_distrib]
    · simp [Complex.im_sum, Matrix.mulVec, dotProduct, Finset.mul_sum, ha_def, hb_def]
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, ha_def, hb_def] at hsym
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [hsym]; ring
  · have h1 := (hB.specB a ha).1
    have h2 := (hB.specB b hb).1
    rw [hS]; linarith
  · have h1 := (hB.specB a ha).2
    have h2 := (hB.specB b hb).2
    rw [hS]; linarith

/-- Coercivity of `1 - ζ B` on `{∑ x i = 0}`: `δ_min² |x|² ≤ |(1 - ζ B) x|²`
(Lemma 3.9, Steps 2 and 3). -/
private lemma vecStab_coercive {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ} {δm δp C₀ : ℝ}
    (hB : VarProfile B δm δp C₀) (hδ : 0 ≤ min δm δp) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    {x : Fin N → ℂ} (hx : ∑ i, x i = 0) :
    min δm δp ^ 2 * ∑ i, ‖x i‖ ^ 2 ≤
      ∑ i, ‖(x - ζ • (B.map (fun r : ℝ => (r : ℂ)) *ᵥ x)) i‖ ^ 2 := by
  obtain ⟨q, hq, hql, hqu⟩ := vecStab_form hB hx
  set S : ℝ := ∑ i, ‖x i‖ ^ 2 with hS
  set y : Fin N → ℂ := x - ζ • (B.map (fun r : ℝ => (r : ℂ)) *ᵥ x) with hy
  set δ : ℝ := min δm δp with hδdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hinner : ∑ i, (starRingEnd ℂ) (x i) * y i = (S : ℂ) - ζ * q := by
    simp only [hy, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [hS]; push_cast
      exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' (x i)
    · rw [← hq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  have hCS : ‖∑ i, (starRingEnd ℂ) (x i) * y i‖ ^ 2 ≤ S * ∑ i, ‖y i‖ ^ 2 := by
    have h1 : ‖∑ i, (starRingEnd ℂ) (x i) * y i‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, Complex.norm_conj]
    calc ‖∑ i, (starRingEnd ℂ) (x i) * y i‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ S * ∑ i, ‖y i‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hqabs : |q| ≤ (1 - δ) * S := by
    have h1 : δ ≤ δm := min_le_left _ _
    have h2 : δ ≤ δp := min_le_right _ _
    rw [abs_le]
    constructor <;> nlinarith
  have hlow : δ * S ≤ ‖∑ i, (starRingEnd ℂ) (x i) * y i‖ := by
    rw [hinner]
    have h1 : ‖(S : ℂ)‖ - ‖ζ * (q : ℂ)‖ ≤ ‖(S : ℂ) - ζ * q‖ := norm_sub_norm_le _ _
    have h2 : ‖(S : ℂ)‖ = S := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    have h3 : ‖ζ * (q : ℂ)‖ ≤ |q| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) hζ
    nlinarith
  have hsq : (δ * S) ^ 2 ≤ S * ∑ i, ‖y i‖ ^ 2 :=
    (pow_le_pow_left₀ (mul_nonneg hδ hS0) hlow 2).trans hCS
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [mul_zero]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith

/-- The `ℓ²` bound `|d| ≤ δ_min⁻¹ |u|` of Lemma 3.9, in squared form. -/
private lemma vecStab_l2 {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ} {δm δp C₀ : ℝ}
    (hB : VarProfile B δm δp C₀) (hδm : 0 < δm) (hδp : 0 < δp) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    {u d : Fin N → ℂ} (hd : ∑ i, d i = 0)
    (hdu : d - ζ • (B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) = u) :
    ∑ i, ‖d i‖ ^ 2 ≤ (min δm δp)⁻¹ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
  have hδ : 0 < min δm δp := lt_min hδm hδp
  have h := vecStab_coercive hB hδ.le hζ hd
  rw [hdu] at h
  rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  linarith

/-- Lemma 3.9: the two bounds `|d| ≤ δ_min⁻¹ |u|` and `‖d‖_∞ ≤ C_s ‖u‖_∞`. -/
theorem vecStab_bounds {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ} {δm δp C₀ : ℝ}
    (hB : VarProfile B δm δp C₀) (hδm : 0 < δm) (hδp : 0 < δp) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    {u d : Fin N → ℂ} (hd : ∑ i, d i = 0)
    (hdu : d - ζ • (B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) = u) :
    ∑ i, ‖d i‖ ^ 2 ≤ (min δm δp)⁻¹ ^ 2 * ∑ i, ‖u i‖ ^ 2 ∧ ‖d‖ ≤ stabCs C₀ δm δp * ‖u‖ := by
  have hδ : 0 < min δm δp := lt_min hδm hδp
  have hl2 := vecStab_l2 hB hδm hδp hζ hd hdu
  refine ⟨hl2, ?_⟩
  have hCs : 0 ≤ stabCs C₀ δm δp := by unfold stabCs; positivity
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hCs (norm_nonneg u))]
  intro i
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Fin.pos i)
  have hC0 : 0 ≤ C₀ := by
    have h : 0 ≤ C₀ / N := (hB.nonneg i i).trans (hB.boundC i i)
    by_contra hneg
    exact absurd h (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hneg) hNpos))
  have hrow : ∑ j, B i j = 1 := by
    rw [← hB.sumA i]
    exact Finset.sum_congr rfl fun j _ => (hB.symm.apply i j).symm
  have hrow2 : ∑ j, B i j ^ 2 ≤ C₀ / N := by
    calc ∑ j, B i j ^ 2 ≤ ∑ j, (C₀ / N) * B i j := Finset.sum_le_sum fun j _ => by
          have := hB.boundC i j
          have := hB.nonneg i j
          nlinarith
      _ = C₀ / N := by rw [← Finset.mul_sum, hrow, mul_one]
  have hBd : ‖(B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i‖ ≤ ∑ j, B i j * ‖d j‖ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB.nonneg i j)]
  have hSu : ∑ j, ‖u j‖ ^ 2 ≤ N * ‖u‖ ^ 2 := by
    calc ∑ j, ‖u j‖ ^ 2 ≤ ∑ _j : Fin N, ‖u‖ ^ 2 :=
          Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u j) 2
      _ = N * ‖u‖ ^ 2 := by simp
  have hsq : ‖(B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i‖ ^ 2 ≤
      (Real.sqrt C₀ / min δm δp * ‖u‖) ^ 2 := by
    have h1 : ‖(B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i‖ ^ 2 ≤ (∑ j, B i j * ‖d j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hBd 2
    have h2 : (∑ j, B i j * ‖d j‖) ^ 2 ≤ (∑ j, B i j ^ 2) * ∑ j, ‖d j‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : (∑ j, B i j ^ 2) * ∑ j, ‖d j‖ ^ 2 ≤
        (C₀ / N) * ((min δm δp)⁻¹ ^ 2 * (N * ‖u‖ ^ 2)) := by
      refine mul_le_mul hrow2 (hl2.trans ?_) (Finset.sum_nonneg fun j _ => sq_nonneg _)
        (div_nonneg hC0 hNpos.le)
      exact mul_le_mul_of_nonneg_left hSu (by positivity)
    have h4 : (C₀ / N) * ((min δm δp)⁻¹ ^ 2 * (N * ‖u‖ ^ 2)) =
        (Real.sqrt C₀ / min δm δp * ‖u‖) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hC0, inv_pow]
      field_simp
    linarith
  have hBd2 : ‖(B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i‖ ≤ Real.sqrt C₀ / min δm δp * ‖u‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hdi : d i = u i + ζ * (B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i := by
    have := congrFun hdu i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]; ring
  calc ‖d i‖ = ‖u i + ζ * (B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i‖ := by rw [← hdi]
    _ ≤ ‖u i‖ + ‖ζ‖ * ‖(B.map (fun r : ℝ => (r : ℂ)) *ᵥ d) i‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ ‖u‖ + 1 * (Real.sqrt C₀ / min δm δp * ‖u‖) := by
        gcongr
        · exact norm_le_pi_norm u i
    _ = stabCs C₀ δm δp * ‖u‖ := by unfold stabCs; ring

end Rigidity
