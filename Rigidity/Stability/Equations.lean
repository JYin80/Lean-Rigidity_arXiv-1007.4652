module

public import Rigidity.Resolvent.Basic
public import Rigidity.Resolvent.Schur
public import Rigidity.Resolvent.Spectral
public import Rigidity.Semicircle.Algebra
public import Rigidity.Semicircle.Basic
public import Rigidity.Stability.Vector

@[expose] public section

/-!
# The self-consistent equation and its stability in the far regime

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `H` over `ℝ` or `ℂ` and a real matrix `B = (σ_ij²)`, this file defines the
error terms `Z_i`, `X_i`, `A_i` and `Υ_i` of Definition 3.2 (`selfZ`, `selfX`, `selfA`,
`selfUps`).  It proves:
* Lemma 3.8: the exact self-consistent equations (3.6), (3.7) for `G_ii` when the row sums of `B`
  are `1` (`sce`), and the averaged equation `(1 - m²) ⟨v⟩ = -m² ⟨Υ⟩ + ⟨r⟩` of (3.7), which
  also needs the column sums of `B` to be `1` (`sce_avg`);
* Lemma 3.12: for `|Re z| ≥ 4` and `|G_ii| ≤ 1`, the bounds `Λ_d ≤ Υ/2`,
  `Λ ≤ |⟨Υ⟩| / 8 + (9/8) Λ_d² (|z| + 1 + Υ)` and `1/|G_ii| ≤ |z| + 1 + Υ` (`stab_far`).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `Z_i` of Definition 3.2. -/
noncomputable def selfZ {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (B : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (i : Fin N) : ℂ :=
  ∑ k, ∑ l, toC (A i k) * greenT A {i} z k l * toC (A l i) - ∑ k, (B i k : ℂ) * greenT A {i} z k k

/-- `X_i = h_ii - Z_i` of Definition 3.2. -/
noncomputable def selfX {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (B : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (i : Fin N) : ℂ :=
  toC (A i i) - selfZ A B z i

/-- `A_i` of Definition 3.2. -/
noncomputable def selfA {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (B : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (i : Fin N) : ℂ :=
  (B i i : ℂ) * green A z i i +
    ∑ j, if j = i then 0 else (B i j : ℂ) * green A z i j * green A z j i / green A z i i

/-- `Υ_i = A_i + X_i` of Definition 3.2. -/
noncomputable def selfUps {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (B : Matrix (Fin N) (Fin N) ℝ)
    (z : ℂ) (i : Fin N) : ℂ :=
  selfA A B z i + selfX A B z i

/-- `G_ii ≠ 0` for `Im z > 0` (Lemma 3.5 (a)). -/
private theorem selfEq_green_ne_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (i : Fin N) : green A z i i ≠ 0 := fun h => by
  have := green_im_diag_pos hA hz i
  rw [h, Complex.zero_im] at this
  exact lt_irrefl _ this

/-- By (I3) with one removed index, `∑_k σ_ik² G^{(i)}_kk = ∑_k σ_ik² G_kk - A_i`. -/
private theorem selfEq_sum_minor {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (B : Matrix (Fin N) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im) (i : Fin N) :
    ∑ k, (B i k : ℂ) * greenT A {i} z k k =
      ∑ k, (B i k : ℂ) * green A z k k - selfA A B z i := by
  have hpt : ∀ k, (B i k : ℂ) * greenT A {i} z k k =
      (B i k : ℂ) * green A z k k - (if k = i then (B i i : ℂ) * green A z i i else 0) -
        (if k = i then 0 else (B i k : ℂ) * green A z i k * green A z k i / green A z i i) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have : greenT A {k} z k k = 0 := by simp [greenT]
      simp [this]
    · rw [greenT_single hA hz hk hk]
      simp only [hk, ite_false, sub_zero]
      ring
  rw [Finset.sum_congr rfl fun k _ => hpt k, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, ite_true]
  unfold selfA
  ring

/-- A real row of nonnegative weights summing to `1` averages complex numbers of norm at most
`c` to a complex number of norm at most `c`. -/
private theorem selfEq_norm_row_le {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : ∀ i, ∑ j, B i j = 1) (hBn : ∀ i j, 0 ≤ B i j) (i : Fin N) {f : Fin N → ℂ} {c : ℝ}
    (hf : ∀ j, ‖f j‖ ≤ c) : ‖∑ j, (B i j : ℂ) * f j‖ ≤ c := by
  calc ‖∑ j, (B i j : ℂ) * f j‖ ≤ ∑ j, ‖(B i j : ℂ) * f j‖ := norm_sum_le _ _
    _ ≤ ∑ j, B i j * c := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hBn i j)]
        exact mul_le_mul_of_nonneg_left (hf j) (hBn i j)
    _ = c := by rw [← Finset.sum_mul, hB i, one_mul]

/-- Lemma 3.8: the exact self-consistent equations (3.6). -/
theorem sce {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : ∀ i, ∑ j, B i j = 1) {z : ℂ} (hz : 0 < z.im)
    (i : Fin N) :
    1 / green A z i i = -z - ∑ j, (B i j : ℂ) * green A z j j + selfUps A B z i ∧
      green A z i i - msc z = msc z * green A z i i *
        (∑ j, (B i j : ℂ) * (green A z j j - msc z) - selfUps A B z i) ∧
      (green A z i i - msc z) - msc z ^ 2 * ∑ j, (B i j : ℂ) * (green A z j j - msc z) =
        -msc z ^ 2 * selfUps A B z i + (green A z i i - msc z) ^ 2 / green A z i i := by
  have hGi := selfEq_green_ne_zero hA hz i
  have hmq := msc_sq_add hz
  have hrow : ∑ j, (B i j : ℂ) = 1 := by rw [← Complex.ofReal_sum, hB i]; simp
  have hS : ∑ j, (B i j : ℂ) * (green A z j j - msc z) =
      ∑ j, (B i j : ℂ) * green A z j j - msc z := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hrow, one_mul]
  have e1 : 1 / green A z i i = -z - ∑ j, (B i j : ℂ) * green A z j j + selfUps A B z i := by
    have h := inv_green_diag hA hz i
    have h2 := selfEq_sum_minor hA B hz i
    unfold selfUps selfX selfZ
    linear_combination h - h2
  have hG : green A z i i * (-z - ∑ j, (B i j : ℂ) * green A z j j + selfUps A B z i) = 1 := by
    rw [← e1]; field_simp
  have e2 : green A z i i - msc z = msc z * green A z i i *
      (∑ j, (B i j : ℂ) * (green A z j j - msc z) - selfUps A B z i) := by
    rw [hS]
    linear_combination (msc z) * hG + (green A z i i) * hmq
  refine ⟨e1, e2, ?_⟩
  have e3 : (green A z i i - msc z) ^ 2 / green A z i i =
      (green A z i i - msc z) - msc z ^ 2 *
        (∑ j, (B i j : ℂ) * (green A z j j - msc z) - selfUps A B z i) := by
    rw [div_eq_iff hGi]
    linear_combination (-(msc z)) * e2
  rw [e3]
  ring

/-- Lemma 3.8, the averaged equation of (3.7): with `v_i = G_ii - m_sc`, `r_i = v_i² / G_ii` and
`⟨u⟩ = N⁻¹ ∑_i u_i`, `(1 - m_sc²) ⟨v⟩ = -m_sc² ⟨Υ⟩ + ⟨r⟩`.  It needs the row sums and the
column sums of `B` to be `1` (condition (A) for a symmetric `B`). -/
theorem sce_avg {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : ∀ i, ∑ j, B i j = 1) (hBc : ∀ j, ∑ i, B i j = 1)
    {z : ℂ} (hz : 0 < z.im) :
    (1 - msc z ^ 2) * ((N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z)) =
      -msc z ^ 2 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i) +
        (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 2 / green A z i i := by
  have hsum : ∑ i, ∑ j, (B i j : ℂ) * (green A z j j - msc z) =
      ∑ j, (green A z j j - msc z) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, (B i j : ℂ) = 1 := by rw [← Complex.ofReal_sum, hBc j]; simp
    rw [this, one_mul]
  have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (sce hA hB hz i).2.2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
    at h
  linear_combination (N : ℂ)⁻¹ * h

/-- Lemma 3.12: stability in the far regime. -/
theorem stab_far {N : ℕ} (hN : 0 < N) {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : ∀ i, ∑ j, B i j = 1) (hBc : ∀ j, ∑ i, B i j = 1) (hBn : ∀ i j, 0 ≤ B i j)
    {z : ℂ} (hE : 4 ≤ |z.re|) (hη : 0 < z.im) (hG : ∀ i, ‖green A z i i‖ ≤ 1) :
    let Υ := ⨆ i, ‖selfUps A B z i‖
    LamDM A z ≤ Υ / 2 ∧
      LamM A z ≤ ‖(N : ℂ)⁻¹ * ∑ i, selfUps A B z i‖ / 8 + 9 / 8 * LamDM A z ^ 2 * (‖z‖ + 1 + Υ) ∧
      ∀ i, 1 / ‖green A z i i‖ ≤ ‖z‖ + 1 + Υ := by
  intro Υ
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨hm1, -, hm3⟩ := msc_far hη hE
  have hbdd : ∀ f : Fin N → ℝ, BddAbove (Set.range f) := fun f => (Set.finite_range f).bddAbove
  have hU : ∀ i, ‖selfUps A B z i‖ ≤ Υ := fun i =>
    le_ciSup (f := fun i => ‖selfUps A B z i‖) (hbdd _) i
  have hU0 : 0 ≤ Υ := (norm_nonneg _).trans (hU ⟨0, hN⟩)
  have hv : ∀ i, ‖green A z i i - msc z‖ ≤ LamDM A z := fun i =>
    le_ciSup (hbdd fun k => ‖green A z k k - msc z‖) i
  have hLd0 : 0 ≤ LamDM A z := (norm_nonneg _).trans (hv ⟨0, hN⟩)
  -- the first conjunct
  have hstep : ∀ i, ‖green A z i i - msc z‖ ≤ (LamDM A z + Υ) / 3 := by
    intro i
    rw [(sce hA hB hη i).2.1, norm_mul, norm_mul]
    have hS := norm_sub_le (∑ j, (B i j : ℂ) * (green A z j j - msc z)) (selfUps A B z i)
    have hrow := selfEq_norm_row_le hB hBn i hv
    calc ‖msc z‖ * ‖green A z i i‖ *
          ‖∑ j, (B i j : ℂ) * (green A z j j - msc z) - selfUps A B z i‖
        ≤ 1 / 3 * 1 * (LamDM A z + Υ) :=
          mul_le_mul (mul_le_mul hm1 (hG i) (norm_nonneg _) (by norm_num))
            (hS.trans (add_le_add hrow (hU i))) (norm_nonneg _) (by norm_num)
      _ = (LamDM A z + Υ) / 3 := by ring
  have hLd : LamDM A z ≤ (LamDM A z + Υ) / 3 := ciSup_le hstep
  have h1 : LamDM A z ≤ Υ / 2 := by linarith
  -- the third conjunct
  have h3 : ∀ i, 1 / ‖green A z i i‖ ≤ ‖z‖ + 1 + Υ := by
    intro i
    have hT : ‖∑ j, (B i j : ℂ) * green A z j j‖ ≤ 1 := selfEq_norm_row_le hB hBn i hG
    have hn : 1 / ‖green A z i i‖ = ‖1 / green A z i i‖ := by rw [norm_div, norm_one]
    rw [hn, (sce hA hB hη i).1]
    calc ‖-z - ∑ j, (B i j : ℂ) * green A z j j + selfUps A B z i‖
        ≤ ‖-z - ∑ j, (B i j : ℂ) * green A z j j‖ + ‖selfUps A B z i‖ := norm_add_le _ _
      _ ≤ (‖z‖ + 1) + Υ := by
          refine add_le_add ?_ (hU i)
          calc ‖-z - ∑ j, (B i j : ℂ) * green A z j j‖
              ≤ ‖-z‖ + ‖∑ j, (B i j : ℂ) * green A z j j‖ := norm_sub_le _ _
            _ ≤ ‖z‖ + 1 := by rw [norm_neg]; linarith
      _ = ‖z‖ + 1 + Υ := by ring
  -- the second conjunct
  have hr : ‖(N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 2 / green A z i i‖ ≤
      LamDM A z ^ 2 * (‖z‖ + 1 + Υ) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hterm : ∀ i, ‖(green A z i i - msc z) ^ 2 / green A z i i‖ ≤
        LamDM A z ^ 2 * (‖z‖ + 1 + Υ) := by
      intro i
      have hGn : 0 < ‖green A z i i‖ := norm_pos_iff.mpr (selfEq_green_ne_zero hA hη i)
      rw [norm_div, norm_pow, div_eq_mul_one_div]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hv i) 2) (h3 i)
        (by positivity) (by positivity)
    have hsum : ‖∑ i, (green A z i i - msc z) ^ 2 / green A z i i‖ ≤
        N * (LamDM A z ^ 2 * (‖z‖ + 1 + Υ)) := by
      calc ‖∑ i, (green A z i i - msc z) ^ 2 / green A z i i‖
          ≤ ∑ i, ‖(green A z i i - msc z) ^ 2 / green A z i i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin N, LamDM A z ^ 2 * (‖z‖ + 1 + Υ) := Finset.sum_le_sum fun i _ => hterm i
        _ = N * (LamDM A z ^ 2 * (‖z‖ + 1 + Υ)) := by simp
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ i, (green A z i i - msc z) ^ 2 / green A z i i‖
        ≤ (N : ℝ)⁻¹ * (N * (LamDM A z ^ 2 * (‖z‖ + 1 + Υ))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = LamDM A z ^ 2 * (‖z‖ + 1 + Υ) := by field_simp
  have hlam : LamM A z = ‖(N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z)‖ := by
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    unfold LamM stieltjesEmp
    congr 1
    simp only [Fintype.card_fin, Matrix.trace, Matrix.diag, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_sub]
    field_simp
  have havg := sce_avg hA hB hBc hη (B := B)
  have hm2 : ‖msc z ^ 2‖ ≤ 1 / 9 := by
    rw [norm_pow]
    calc ‖msc z‖ ^ 2 ≤ (1 / 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hm1 2
      _ = 1 / 9 := by norm_num
  have hlhs : ‖1 - msc z ^ 2‖ * ‖(N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z)‖ ≤
      1 / 9 * ‖(N : ℂ)⁻¹ * ∑ i, selfUps A B z i‖ + LamDM A z ^ 2 * (‖z‖ + 1 + Υ) := by
    rw [← norm_mul, havg]
    calc ‖-msc z ^ 2 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i) +
          (N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 2 / green A z i i‖
        ≤ ‖-msc z ^ 2 * ((N : ℂ)⁻¹ * ∑ i, selfUps A B z i)‖ +
          ‖(N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z) ^ 2 / green A z i i‖ := norm_add_le _ _
      _ ≤ 1 / 9 * ‖(N : ℂ)⁻¹ * ∑ i, selfUps A B z i‖ + LamDM A z ^ 2 * (‖z‖ + 1 + Υ) := by
          refine add_le_add ?_ hr
          rw [norm_mul, norm_neg]
          exact mul_le_mul_of_nonneg_right hm2 (norm_nonneg _)
  have hlow := mul_le_mul_of_nonneg_right hm3
    (norm_nonneg ((N : ℂ)⁻¹ * ∑ i, (green A z i i - msc z)))
  refine ⟨h1, ?_, h3⟩
  rw [hlam]
  linarith

end Rigidity
