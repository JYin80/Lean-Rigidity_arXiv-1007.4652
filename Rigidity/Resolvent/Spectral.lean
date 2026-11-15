import Rigidity.Resolvent.Ward
import Rigidity.Semicircle.Basic

/-!
# Spectral form of the Green function, eigenvalue counting, and the comparison quantities

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `H` over `ℝ` or `ℂ` with Green function `G(z) = (H - z)⁻¹` and
`m(z) = N⁻¹ tr G(z)` this file proves the following parts of Lemma 3.5.
* The comparison quantities `Λ = |m - m_sc|`, `Λ_d = max_k |G_kk - m_sc|` and
  `Λ_o = max_{k ≠ l} |G_kl|` of a matrix, with their Lipschitz bounds on `{Im z ≥ η₀}`, constant
  `η₀⁻² + η₀⁻¹ + 1` (Lemma 3.5 (c)).
* Lemma 3.5 (d): `Im m = N⁻¹ ∑_k η / ((λ_k - E)² + η²)` for `z = E + iη`.
* Lemma 3.5 (e): the number of eigenvalues in `[E - η, E + η]` is at most `2 N η Im m(E + iη)`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Λ = |m - m_sc|` for a matrix. -/
noncomputable def LamM (A : Matrix n n 𝕜) (z : ℂ) : ℝ := ‖stieltjesEmp A z - msc z‖

/-- `Λ_d = max_k |G_kk - m_sc|` for a matrix. -/
noncomputable def LamDM (A : Matrix n n 𝕜) (z : ℂ) : ℝ := ⨆ k : n, ‖green A z k k - msc z‖

/-- `Λ_o = max_{k ≠ l} |G_kl|` for a matrix. -/
noncomputable def LamOM (A : Matrix n n 𝕜) (z : ℂ) : ℝ :=
  ⨆ q : {q : n × n // q.1 ≠ q.2}, ‖green A z q.1.1 q.1.2‖

/-- If two families on a finite index type differ by at most `C` termwise, their suprema differ by
at most `C`. -/
private theorem spectral_abs_iSup_sub_le {ι : Type*} [Finite ι] (f g : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, |f i - g i| ≤ C) : |(⨆ i, f i) - ⨆ i, g i| ≤ C := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [hC]
  · rw [abs_le]
    have h1 : (⨆ i, f i) ≤ (⨆ i, g i) + C := ciSup_le fun i => by
      have := (abs_le.mp (h i)).2
      have := le_ciSup (Finite.bddAbove_range g) i
      linarith
    have h2 : (⨆ i, g i) ≤ (⨆ i, f i) + C := ciSup_le fun i => by
      have := (abs_le.mp (h i)).1
      have := le_ciSup (Finite.bddAbove_range f) i
      linarith
    constructor <;> linarith

/-- Entrywise Lipschitz bound for `G` on `{Im ≥ η₀}`. -/
private theorem spectral_entry_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z w : ℂ} {η₀ : ℝ}
    (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) (i j : n) :
    ‖green A z i j - green A w i j‖ ≤ η₀⁻¹ ^ 2 * ‖z - w‖ := by
  have hz0 : 0 < z.im := lt_of_lt_of_le hη₀ hz
  have hw0 : 0 < w.im := lt_of_lt_of_le hη₀ hw
  refine (norm_green_sub_le hA hz0 hw0 i j).trans ?_
  have h1 : η₀ * η₀ ≤ z.im * w.im := mul_le_mul hz hw hη₀.le hz0.le
  have h2 : ‖z - w‖ / (z.im * w.im) ≤ ‖z - w‖ / (η₀ * η₀) :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h1
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- Lipschitz bound for `m` on `{Im ≥ η₀}`. -/
private theorem spectral_stieltjes_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z w : ℂ}
    {η₀ : ℝ} (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖stieltjesEmp A z - stieltjesEmp A w‖ ≤ η₀⁻¹ ^ 2 * ‖z - w‖ := by
  have hC : 0 ≤ η₀⁻¹ ^ 2 * ‖z - w‖ := by positivity
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : stieltjesEmp A z - stieltjesEmp A w = 0 := by simp [stieltjesEmp]
    rw [h0, norm_zero]
    exact hC
  have hpos : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have h1 : stieltjesEmp A z - stieltjesEmp A w =
      ((Fintype.card n : ℂ))⁻¹ * ∑ k, (green A z k k - green A w k k) := by
    unfold stieltjesEmp Matrix.trace
    simp only [Matrix.diag, Finset.sum_sub_distrib]
    ring
  rw [h1, norm_mul, norm_inv, Complex.norm_natCast]
  have h2 : ‖∑ k, (green A z k k - green A w k k)‖ ≤ Fintype.card n * (η₀⁻¹ ^ 2 * ‖z - w‖) := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul Finset.univ (fun k => ‖green A z k k - green A w k k‖)
      (η₀⁻¹ ^ 2 * ‖z - w‖) fun k _ => spectral_entry_le hA hη₀ hz hw k k
    simpa [nsmul_eq_mul] using this
  calc (Fintype.card n : ℝ)⁻¹ * ‖∑ k, (green A z k k - green A w k k)‖
      ≤ (Fintype.card n : ℝ)⁻¹ * (Fintype.card n * (η₀⁻¹ ^ 2 * ‖z - w‖)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = η₀⁻¹ ^ 2 * ‖z - w‖ := by field_simp

/-- Lemma 3.5 (c): Lipschitz bounds for `Λ`, `Λ_d`, `Λ_o` on `{Im ≥ η₀}`. -/
theorem abs_LamM_sub_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {z w : ℂ} {η₀ : ℝ}
    (hη₀ : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    |LamM A z - LamM A w| ≤ (η₀⁻¹ ^ 2 + η₀⁻¹ + 1) * ‖z - w‖ ∧
      |LamDM A z - LamDM A w| ≤ (η₀⁻¹ ^ 2 + η₀⁻¹ + 1) * ‖z - w‖ ∧
      |LamOM A z - LamOM A w| ≤ (η₀⁻¹ ^ 2 + η₀⁻¹ + 1) * ‖z - w‖ := by
  have hm := norm_msc_sub_le hη₀ hz hw
  have hc : (η₀ + 1) / η₀ = η₀⁻¹ + 1 := by field_simp; ring
  rw [hc] at hm
  have hnn : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hconst : (η₀⁻¹ ^ 2 + η₀⁻¹ + 1) * ‖z - w‖ =
      η₀⁻¹ ^ 2 * ‖z - w‖ + (η₀⁻¹ + 1) * ‖z - w‖ := by ring
  have hC : 0 ≤ (η₀⁻¹ ^ 2 + η₀⁻¹ + 1) * ‖z - w‖ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold LamM
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have h1 := spectral_stieltjes_le hA hη₀ hz hw
    calc ‖(stieltjesEmp A z - msc z) - (stieltjesEmp A w - msc w)‖
        = ‖(stieltjesEmp A z - stieltjesEmp A w) - (msc z - msc w)‖ := by congr 1; ring
      _ ≤ ‖stieltjesEmp A z - stieltjesEmp A w‖ + ‖msc z - msc w‖ := norm_sub_le _ _
      _ ≤ _ := by rw [hconst]; exact add_le_add h1 hm
  · unfold LamDM
    refine spectral_abs_iSup_sub_le _ _ hC fun k => ?_
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have h1 := spectral_entry_le hA hη₀ hz hw k k
    calc ‖(green A z k k - msc z) - (green A w k k - msc w)‖
        = ‖(green A z k k - green A w k k) - (msc z - msc w)‖ := by congr 1; ring
      _ ≤ ‖green A z k k - green A w k k‖ + ‖msc z - msc w‖ := norm_sub_le _ _
      _ ≤ _ := by rw [hconst]; exact add_le_add h1 hm
  · unfold LamOM
    refine spectral_abs_iSup_sub_le _ _ hC fun q => ?_
    refine (abs_norm_sub_norm_le _ _).trans ?_
    refine (spectral_entry_le hA hη₀ hz hw q.1.1 q.1.2).trans ?_
    have : 0 ≤ (η₀⁻¹ + 1) * ‖z - w‖ := by positivity
    linarith

end Resolvent

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectral_im_inv (μ : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (1 / ((μ : ℂ) - z)).im = z.im / ((μ - z.re) ^ 2 + z.im ^ 2) := by
  have h : 0 < (μ - z.re) ^ 2 + z.im ^ 2 := by positivity
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
    neg_neg]
  congr 1
  ring

end Spectral

/-- Lemma 3.5 (d): `Im m`. -/
theorem im_stieltjesEmp_eq {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) :
    (stieltjesEmp A z).im = (N : ℝ)⁻¹ * ∑ k, z.im / ((eigAsc hA k - z.re) ^ 2 + z.im ^ 2) := by
  rw [stieltjesEmp_eq_sum hA hz]
  have h1 : (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [h1, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact spectral_im_inv _ hz

/-- Lemma 3.5 (e): counting eigenvalues near `E`. -/
theorem card_eig_near_le {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) (E : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ({k : Fin N | |eigAsc hA k - E| ≤ η}.ncard : ℝ) ≤
      2 * N * η * (stieltjesEmp A (E + η * Complex.I)).im := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Set.eq_empty_of_isEmpty]
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hre : (E + η * Complex.I).re = E := by simp
  have him : (E + η * Complex.I).im = η := by simp
  have h := im_stieltjesEmp_eq hA (z := E + η * Complex.I) (by rw [him]; exact hη)
  rw [hre, him] at h
  rw [h]
  have hset : {k : Fin N | |eigAsc hA k - E| ≤ η} =
      ↑(Finset.univ.filter fun k : Fin N => |eigAsc hA k - E| ≤ η) := by
    ext k; simp
  rw [hset, Set.ncard_coe_finset]
  set T : Fin N → ℝ := fun k => η / ((eigAsc hA k - E) ^ 2 + η ^ 2) with hT
  have hTnn : ∀ k, 0 ≤ T k := fun k => by positivity
  have hsub : ∑ k ∈ Finset.univ.filter (fun k : Fin N => |eigAsc hA k - E| ≤ η), T k ≤
      ∑ k, T k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => hTnn k
  have hlow : ∀ k ∈ Finset.univ.filter (fun k : Fin N => |eigAsc hA k - E| ≤ η),
      1 / (2 * η) ≤ T k := by
    intro k hk
    have hk' : |eigAsc hA k - E| ≤ η := (Finset.mem_filter.mp hk).2
    have h1 : (eigAsc hA k - E) ^ 2 ≤ η ^ 2 := by
      have := sq_le_sq' (abs_le.mp hk').1 (abs_le.mp hk').2
      simpa using this
    have h2 : 1 / (2 * η) = η / (2 * η ^ 2) := by field_simp
    rw [h2, hT]
    exact div_le_div_of_nonneg_left hη.le (by positivity) (by linarith)
  have h3 : ((Finset.univ.filter fun k : Fin N => |eigAsc hA k - E| ≤ η).card : ℝ) *
      (1 / (2 * η)) ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin N => |eigAsc hA k - E| ≤ η), T k := by
    have := Finset.card_nsmul_le_sum _ T (1 / (2 * η)) hlow
    simpa [nsmul_eq_mul] using this
  have h4 : ((Finset.univ.filter fun k : Fin N => |eigAsc hA k - E| ≤ η).card : ℝ) ≤
      2 * η * ∑ k, T k := by
    have h5 : ((Finset.univ.filter fun k : Fin N => |eigAsc hA k - E| ≤ η).card : ℝ) =
        ((Finset.univ.filter fun k : Fin N => |eigAsc hA k - E| ≤ η).card : ℝ) *
          (1 / (2 * η)) * (2 * η) := by field_simp
    rw [h5, mul_comm (2 * η)]
    exact mul_le_mul_of_nonneg_right (h3.trans hsub) (by positivity)
  calc _ ≤ 2 * η * ∑ k, T k := h4
    _ = 2 * N * η * ((N : ℝ)⁻¹ * ∑ k, η / ((eigAsc hA k - E) ^ 2 + η ^ 2)) := by
      rw [hT]; field_simp

end Rigidity
