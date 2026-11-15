import Rigidity.Resolvent.Basic
import Rigidity.Resolvent.Spectral
import Rigidity.Semicircle.Basic
import Rigidity.Semicircle.Size
import Rigidity.Stability.Equations
import Rigidity.Stability.Vector

/-!
# Stability of the self-consistent equation in the near regime

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Write `m = m_sc(z)`, `v_i = G_ii - m`, `w = ⟨v⟩ = m(z) - m`, `d_i = v_i - w`, `D = max_i |d_i|`,
`Υ_max = max_i |Υ_i|` and `w₀ = m (1 - m²)`.  This file proves Lemma 3.10 (§3.3):
* the identity `w² - w₀ w = m³ ⟨Υ⟩ - ⟨d²⟩ + ⟨v³/G⟩`, valid for `Im z > 0` when the rows and the
  columns of `B` sum to `1` (`stab_identity`);
* under conditions (A), (B), (C) of Definition 2.2, for `|E| ≤ 5`, `0 < η ≤ 10` and
  `Λ_d ≤ λ_st = 1/(576 C_s)`: the bounds `3/52 ≤ |G_ii| ≤ 5/4`, `Λ ≤ Λ_d`, `D ≤ 2 Λ_d`,
  `D ≤ 4 C_s Υ_max + 144 C_s Λ²`, `Λ_d ≤ Λ + D`, and
  `|w² - w₀ w| ≤ |⟨Υ⟩| + 40 C_s² Υ_max² + (90 + 72 C_s) Λ³` (`stab_near`).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The modulus of an average is at most a uniform bound on the moduli of the terms. -/
private theorem near_norm_avg_le {N : ℕ} (hN : 0 < N) {f : Fin N → ℂ} {c : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ c) : ‖(N : ℂ)⁻¹ * ∑ i, f i‖ ≤ c := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ‖∑ i, f i‖ ≤ N * c :=
    calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, c := Finset.sum_le_sum fun i _ => hf i
      _ = N * c := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, f i‖ ≤ (N : ℝ)⁻¹ * (N * c) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c := by field_simp

/-- A term of a finite family is at most its supremum. -/
private theorem near_le_iSup {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : f i ≤ ⨆ j, f j :=
  le_ciSup (Set.finite_range f).bddAbove i

/-- `(a + b)² ≤ 2 a² + 2 b²`. -/
private theorem near_sq_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- `(a + b)³ ≤ 4 a³ + 4 b³` for `a, b ≥ 0`. -/
private theorem near_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * a ^ 3 + 4 * b ^ 3 := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

/-- `⟨v⟩ = m(z) - m_sc(z)`. -/
private theorem near_avg_eq {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) 𝕜) (z : ℂ) :
    stieltjesEmp A z - msc z = (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold stieltjesEmp
  simp only [Fintype.card_fin, Matrix.trace, Matrix.diag, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_sub]
  field_simp

/-- Lemma 3.10, the identity `w² - w₀ w = m³ ⟨Υ⟩ - ⟨d²⟩ + ⟨v³/G⟩` with `w = ⟨v⟩`,
`w₀ = m (1 - m²)`, `d_i = v_i - w`, for `Im z > 0` and row and column sums of `B` equal to `1`. -/
theorem stab_identity {N : ℕ} (hN : 0 < N) {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : ∀ i, ∑ j, B i j = 1) (hBc : ∀ j, ∑ i, B i j = 1)
    {z : ℂ} (hz : 0 < z.im) :
    let w := stieltjesEmp A z - msc z
    w ^ 2 - msc z * (1 - msc z ^ 2) * w =
      msc z ^ 3 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i) -
        (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z - w) ^ 2 +
        (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 3 / green A z i i := by
  intro w
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hw : w = (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) := near_avg_eq hN A z
  clear_value w
  have hS : ∑ i, (green A z i i - msc z) = N * w := by
    rw [hw, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  have havg := sce_avg hA hB hBc hz
  rw [← hw] at havg
  have hr : msc z * ∑ i, (green A z i i - msc z) ^ 2 / green A z i i =
      ∑ i, (green A z i i - msc z) ^ 2 - ∑ i, (green A z i i - msc z) ^ 3 / green A z i i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hG : green A z i i ≠ 0 := fun h => by
      have := green_im_diag_pos hA hz i
      rw [h, Complex.zero_im] at this
      exact lt_irrefl _ this
    field_simp
    ring
  have hd : ∑ i, (green A z i i - msc z - w) ^ 2 =
      ∑ i, (green A z i i - msc z) ^ 2 - 2 * w * ∑ i, (green A z i i - msc z) + N * w ^ 2 := by
    have : ∀ i, (green A z i i - msc z - w) ^ 2 =
        (green A z i i - msc z) ^ 2 - 2 * w * (green A z i i - msc z) + w ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hd, hS]
  have hinv : (N : ℂ)⁻¹ * N = 1 := inv_mul_cancel₀ hN0
  linear_combination (-msc z) * havg - (N : ℂ)⁻¹ * hr - w ^ 2 * hinv


/-- Lemma 3.10: stability in the near regime. -/
theorem stab_near {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {B : Matrix (Fin N) (Fin N) ℝ} {δm δp C₀ : ℝ} (hB : VarProfile B δm δp C₀) (hδm : 0 < δm)
    (hδp : 0 < δp) (hN : 2 ≤ N) {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη' : z.im ≤ 10)
    (hsmall : LamDM A z ≤ lamSt C₀ δm δp) :
    let w := stieltjesEmp A z - msc z
    let D := ⨆ i, ‖green A z i i - msc z - w‖
    let Υ := ⨆ i, ‖selfUps A B z i‖
    let Cs := stabCs C₀ δm δp
    (∀ i, 3 / 52 ≤ ‖green A z i i‖ ∧ ‖green A z i i‖ ≤ 5 / 4) ∧ ‖w‖ ≤ LamDM A z ∧
      D ≤ 2 * LamDM A z ∧ D ≤ 4 * Cs * Υ + 144 * Cs * ‖w‖ ^ 2 ∧ LamDM A z ≤ ‖w‖ + D ∧
      ‖w ^ 2 - msc z * (1 - msc z ^ 2) * w‖ ≤
        ‖(N : ℂ)⁻¹ * ∑ i, selfUps A B z i‖ + 40 * Cs ^ 2 * Υ ^ 2 + (90 + 72 * Cs) * ‖w‖ ^ 3 := by
  intro w D Υ Cs
  have hwdef : w = stieltjesEmp A z - msc z := rfl
  have hDdef : D = ⨆ i, ‖green A z i i - msc z - w‖ := rfl
  have hΥdef : Υ = ⨆ i, ‖selfUps A B z i‖ := rfl
  have hCsdef : Cs = stabCs C₀ δm δp := rfl
  clear_value D Υ Cs w
  have hN0 : 0 < N := by omega
  have : Nonempty (Fin N) := ⟨⟨0, hN0⟩⟩
  obtain ⟨hm1, hm2, -, -⟩ := msc_size hE hη hη'
  have hrow : ∀ i, ∑ j, B i j = 1 := fun i => by
    rw [← hB.sumA i]
    exact Finset.sum_congr rfl fun j _ => (hB.symm.apply i j).symm
  -- the constants `C_s ≥ 1` and `C_s λ_st = 1/576`
  have hCs1 : 1 ≤ Cs := by
    rw [hCsdef]
    exact le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) (lt_min hδm hδp).le)
  have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs1
  have hlamdef : lamSt C₀ δm δp = 1 / (576 * Cs) := by rw [hCsdef]; rfl
  have hlamCs : Cs * lamSt C₀ δm δp = 1 / 576 := by
    rw [hlamdef]; field_simp
  have hlam0 : 0 ≤ lamSt C₀ δm δp := by rw [hlamdef]; positivity
  have hlam1 : lamSt C₀ δm δp ≤ 1 / 576 := by
    have := mul_le_mul_of_nonneg_right hCs1 hlam0
    linarith
  -- elementary bounds (Step 1)
  have hv : ∀ i, ‖green A z i i - msc z‖ ≤ LamDM A z := fun i =>
    near_le_iSup (fun k => ‖green A z k k - msc z‖) i
  have hΛd0 : 0 ≤ LamDM A z := (norm_nonneg _).trans (hv ⟨0, hN0⟩)
  have hΛd1 : LamDM A z ≤ 1 / 576 := hsmall.trans hlam1
  have hG : ∀ i, 3 / 52 ≤ ‖green A z i i‖ ∧ ‖green A z i i‖ ≤ 5 / 4 := by
    intro i
    have h1 : ‖msc z‖ ≤ ‖green A z i i‖ + ‖green A z i i - msc z‖ := by
      have := norm_sub_le (green A z i i) (green A z i i - msc z)
      rwa [sub_sub_cancel] at this
    have h2 : ‖green A z i i‖ ≤ ‖green A z i i - msc z‖ + ‖msc z‖ := by
      have := norm_add_le (green A z i i - msc z) (msc z)
      rwa [sub_add_cancel] at this
    have := hv i
    constructor <;> linarith
  have hw : w = (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) := by
    rw [hwdef]; exact near_avg_eq hN0 A z
  have hwΛ : ‖w‖ ≤ LamDM A z := by rw [hw]; exact near_norm_avg_le hN0 hv
  have hd : ∀ i, ‖green A z i i - msc z - w‖ ≤ D := fun i => by
    rw [hDdef]; exact near_le_iSup (fun k => ‖green A z k k - msc z - w‖) i
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hd ⟨0, hN0⟩)
  have hD2 : D ≤ 2 * LamDM A z := by
    rw [hDdef]
    refine ciSup_le fun i => ?_
    have := norm_sub_le (green A z i i - msc z) w
    linarith [hv i]
  have hΛdD : LamDM A z ≤ ‖w‖ + D := ciSup_le fun i => by
    have := norm_add_le w (green A z i i - msc z - w)
    rw [add_sub_cancel] at this
    linarith [hd i]
  have hU : ∀ i, ‖selfUps A B z i‖ ≤ Υ := fun i => by
    rw [hΥdef]; exact near_le_iSup (fun k => ‖selfUps A B z k‖) i
  have hΥ0 : 0 ≤ Υ := (norm_nonneg _).trans (hU ⟨0, hN0⟩)
  have hm2' : ‖msc z ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hm2
  have hr : ∀ i, ‖(green A z i i - msc z) ^ 2 / green A z i i‖ ≤ 18 * LamDM A z ^ 2 := by
    intro i
    rw [norm_div, norm_pow]
    calc ‖green A z i i - msc z‖ ^ 2 / ‖green A z i i‖ ≤ LamDM A z ^ 2 / (3 / 52) :=
          div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
            (by norm_num) (hG i).1
      _ ≤ 18 * LamDM A z ^ 2 := by nlinarith [sq_nonneg (LamDM A z)]
  have hr3 : ∀ i, ‖(green A z i i - msc z) ^ 3 / green A z i i‖ ≤ 18 * LamDM A z ^ 3 := by
    intro i
    rw [norm_div, norm_pow]
    calc ‖green A z i i - msc z‖ ^ 3 / ‖green A z i i‖ ≤ LamDM A z ^ 3 / (3 / 52) :=
          div_le_div₀ (pow_nonneg hΛd0 3) (pow_le_pow_left₀ (norm_nonneg _) (hv i) 3)
            (by norm_num) (hG i).1
      _ ≤ 18 * LamDM A z ^ 3 := by nlinarith [pow_nonneg hΛd0 3]
  -- the equation for `d` (Step 2)
  set y : Fin N → ℂ := fun i =>
    -msc z ^ 2 * selfUps A B z i + (green A z i i - msc z) ^ 2 / green A z i i with hy_def
  have hy : ∀ i, ‖y i‖ ≤ Υ + 18 * LamDM A z ^ 2 := by
    intro i
    refine (norm_add_le _ _).trans (add_le_add ?_ (hr i))
    rw [norm_mul, norm_neg]
    calc ‖msc z ^ 2‖ * ‖selfUps A B z i‖ ≤ 1 * Υ :=
          mul_le_mul hm2' (hU i) (norm_nonneg _) zero_le_one
      _ = Υ := one_mul _
  have hyavg : (1 - msc z ^ 2) * w = (N : ℂ)⁻¹ * ∑ i, y i := by
    rw [hw, sce_avg hA hrow hB.sumA hη]
    simp only [hy_def, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hdsum : ∑ i, (fun i => green A z i i - msc z - w) i = 0 := by
    have hS : ∑ i, (green A z i i - msc z) = N * w := by
      have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
      rw [hw, ← mul_assoc, mul_inv_cancel₀ hN0', one_mul]
    calc _ = ∑ i, (green A z i i - msc z) - ∑ _i : Fin N, w := Finset.sum_sub_distrib _ _
      _ = 0 := by rw [hS]; simp
  have hdu : (fun i => green A z i i - msc z - w) - msc z ^ 2 •
      (B.map (fun r : ℝ => (r : ℂ)) *ᵥ fun i => green A z i i - msc z - w) =
      fun i => y i - (1 - msc z ^ 2) * w := by
    funext i
    have h3 := (sce hA hrow hη i).2.2
    have hs : ∑ j, (B i j : ℂ) * (green A z j j - msc z - w) =
        ∑ j, (B i j : ℂ) * (green A z j j - msc z) - w := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [← Complex.ofReal_sum, hrow i]
      simp
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.map_apply, hy_def]
    rw [hs]
    linear_combination h3
  have hstab := (vecStab_bounds hB hδm hδp hm2' hdsum hdu).2
  rw [← hCsdef] at hstab
  have hu : ‖fun i => y i - (1 - msc z ^ 2) * w‖ ≤ 2 * (Υ + 18 * LamDM A z ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have h1 : ‖(1 - msc z ^ 2) * w‖ ≤ Υ + 18 * LamDM A z ^ 2 := by
      rw [hyavg]; exact near_norm_avg_le hN0 hy
    calc ‖y i - (1 - msc z ^ 2) * w‖ ≤ ‖y i‖ + ‖(1 - msc z ^ 2) * w‖ := norm_sub_le _ _
      _ ≤ 2 * (Υ + 18 * LamDM A z ^ 2) := by linarith [hy i]
  have hDle : D ≤ Cs * (2 * (Υ + 18 * LamDM A z ^ 2)) := by
    rw [hDdef]
    exact ciSup_le fun i => (norm_le_pi_norm (fun i => green A z i i - msc z - w) i).trans
      (hstab.trans (mul_le_mul_of_nonneg_left hu hCs0))
  -- absorption (end of Step 2)
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hΛdsq : LamDM A z ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * D ^ 2 := by
    have := pow_le_pow_left₀ hΛd0 hΛdD 2
    linarith [near_sq_le ‖w‖ D]
  have hDlam : D ≤ 2 * lamSt C₀ δm δp := hD2.trans (by linarith)
  have h72 : 72 * Cs * D ^ 2 ≤ D / 4 := by
    have h1 : Cs * D * D ≤ Cs * (2 * lamSt C₀ δm δp) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDlam hCs0) hD0
    have h2 : Cs * (2 * lamSt C₀ δm δp) * D = D / 288 := by
      rw [show Cs * (2 * lamSt C₀ δm δp) * D = 2 * (Cs * lamSt C₀ δm δp) * D by ring, hlamCs]
      ring
    linarith
  have hsharp : D ≤ 8 / 3 * Cs * Υ + 96 * Cs * ‖w‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hΛdsq hCs0
    linarith
  refine ⟨hG, hwΛ, hD2, ?_, hΛdD, ?_⟩
  · linarith [mul_nonneg hCs0 hΥ0, mul_nonneg hCs0 (sq_nonneg ‖w‖)]
  -- the quadratic bound (Steps 3 and 4)
  have hid : w ^ 2 - msc z * (1 - msc z ^ 2) * w =
      msc z ^ 3 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i) -
        (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z - w) ^ 2 +
        (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 3 / green A z i i :=
    by rw [hwdef]; exact stab_identity hN0 hA hrow hB.sumA hη
  have hd2 : ‖(N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z - w) ^ 2‖ ≤ D ^ 2 :=
    near_norm_avg_le hN0 fun i => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hd i) 2
  have hv3 : ‖(N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 3 / green A z i i‖ ≤
      18 * LamDM A z ^ 3 := near_norm_avg_le hN0 hr3
  have hm3 : ‖msc z ^ 3 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i)‖ ≤
      ‖(N : ℂ)⁻¹ * ∑ i, selfUps A B z i‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hm2)
  have hquad : ‖w ^ 2 - msc z * (1 - msc z ^ 2) * w‖ ≤
      ‖(N : ℂ)⁻¹ * ∑ i, selfUps A B z i‖ + D ^ 2 + 18 * LamDM A z ^ 3 := by
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le (msc z ^ 3 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i))
      ((N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z - w) ^ 2)
    linarith
  -- `18 Λ_d³ ≤ 72 Λ³ + D²/4`
  have hcube : LamDM A z ^ 3 ≤ 4 * ‖w‖ ^ 3 + 4 * D ^ 3 := by
    have := pow_le_pow_left₀ hΛd0 hΛdD 3
    linarith [near_cube_le hw0 hD0]
  have hD3 : 72 * D ^ 3 ≤ D ^ 2 / 4 := by
    have h1 : D ^ 3 = D * D ^ 2 := by ring
    have h2 : D * D ^ 2 ≤ 2 * lamSt C₀ δm δp * D ^ 2 :=
      mul_le_mul_of_nonneg_right hDlam (sq_nonneg D)
    have h3 : 144 * lamSt C₀ δm δp * D ^ 2 ≤ 1 / 4 * D ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg D)
    linarith
  -- `D² ≤ (128/9) C_s² Υ² + 32 C_s Λ³`
  have hDsq : D ^ 2 ≤ 128 / 9 * Cs ^ 2 * Υ ^ 2 + 32 * Cs * ‖w‖ ^ 3 := by
    have h1 : D ^ 2 ≤ (8 / 3 * Cs * Υ + 96 * Cs * ‖w‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hD0 hsharp 2
    have h2 : (8 / 3 * Cs * Υ + 96 * Cs * ‖w‖ ^ 2) ^ 2 ≤
        128 / 9 * Cs ^ 2 * Υ ^ 2 + 18432 * Cs ^ 2 * ‖w‖ ^ 4 := by
      have := near_sq_le (8 / 3 * Cs * Υ) (96 * Cs * ‖w‖ ^ 2)
      linarith
    have h3 : ‖w‖ ^ 4 ≤ lamSt C₀ δm δp * ‖w‖ ^ 3 := by
      have : ‖w‖ ≤ lamSt C₀ δm δp := hwΛ.trans hsmall
      have h4 : ‖w‖ ^ 4 = ‖w‖ * ‖w‖ ^ 3 := by ring
      rw [h4]; exact mul_le_mul_of_nonneg_right this (pow_nonneg hw0 3)
    have h5 : 18432 * Cs ^ 2 * ‖w‖ ^ 4 ≤ 32 * Cs * ‖w‖ ^ 3 := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 18432 * Cs ^ 2)
      have h6 : 18432 * Cs ^ 2 * (lamSt C₀ δm δp * ‖w‖ ^ 3) =
          32 * Cs * ‖w‖ ^ 3 * (576 * (Cs * lamSt C₀ δm δp)) := by ring
      rw [h6, hlamCs] at this
      linarith
    linarith
  have hfin : D ^ 2 + 18 * LamDM A z ^ 3 ≤ 40 * Cs ^ 2 * Υ ^ 2 + (90 + 72 * Cs) * ‖w‖ ^ 3 := by
    linarith [mul_nonneg (sq_nonneg Cs) (sq_nonneg Υ), mul_nonneg hCs0 (pow_nonneg hw0 3),
      pow_nonneg hw0 3]
  linarith

end Rigidity
