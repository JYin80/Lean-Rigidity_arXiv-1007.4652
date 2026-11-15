import Rigidity.Edge.Hybrid
import Rigidity.Edge.Resolvent
import Rigidity.Edge.SmoothCount
import Rigidity.Ensemble.Basic
import Rigidity.Spectrum.Continuity
import Rigidity.Spectrum.Eigenvalues

/-!
# Continuity of `X`, of `λ_N` and of the resolvent in the entries

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file proves the measurability remark after Lemma 11.8: for fixed `E₁ ≤ E₂` and `η > 0` the
smoothed counting functional `X(A) = smoothCount E₁ E₂ η A` is Lipschitz in the operator norm on
hermitian matrices, with constant `n (E₂ - E₁) / (π η²)` (Lemma 11.8 (c)).  Consequently
`x ↦ X(H(x))` and `x ↦ X((H(x)^{[p]})^{(c)})` are continuous on `Ω = Pair N → 𝕜`.  The largest
eigenvalue `x ↦ λ_N(H(x))` is continuous (Lemma 3.13 (d)), and so is each entry of the resolvent
`x ↦ G_{kl}(z)` for `Im z > 0` (Lemma 3.5).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. Lipschitz bound for `X` -/

/-- A matrix entry is bounded by the `ℓ²` operator norm. -/
private lemma continuity_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  refine le_trans (le_of_eq ?_) h2
  simp

/-- `|Im tr M| ≤ n ‖M‖`. -/
private lemma continuity_abs_trace_im_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : |M.trace.im| ≤ Fintype.card n * ‖M‖ := by
  calc |M.trace.im| ≤ ‖M.trace‖ := Complex.abs_im_le_norm _
    _ ≤ ∑ i, ‖M i i‖ := by
        unfold Matrix.trace
        simpa using norm_sum_le Finset.univ (fun i => M.diag i)
    _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => continuity_norm_entry_le M i i
    _ = Fintype.card n * ‖M‖ := by simp

/-- Matrix inversion is continuous at a matrix with nonzero determinant. -/
private lemma continuity_continuousAt_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (h : A.det ≠ 0) : ContinuousAt Inv.inv A := by
  refine continuousAt_matrix_inv A ?_
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ h

/-- The resolvent entries depend continuously on a continuous family of hermitian matrices and
spectral parameters in the upper half plane. -/
private lemma continuity_resolventMat_continuous {α : Type*} [TopologicalSpace α]
    {n : Type*} [Fintype n] [DecidableEq n] {g : α → Matrix n n ℂ} {z : α → ℂ}
    (hg : Continuous g) (hz : Continuous z) (hh : ∀ x, (g x).IsHermitian)
    (him : ∀ x, (z x).im ≠ 0) :
    Continuous fun x => resolventMat (g x) (z x) := by
  have hc : Continuous fun x => g x - z x • (1 : Matrix n n ℂ) :=
    hg.sub (hz.smul continuous_const)
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact ContinuousAt.comp (f := fun x => g x - z x • (1 : Matrix n n ℂ))
    (continuity_continuousAt_inv (det_sub_smul_ne_zero (hh x) (him x))) hc.continuousAt

/-- `y ↦ Im tr G_A(y + iη)` is continuous. -/
private lemma continuity_trace_im_continuous {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η) :
    Continuous fun y : ℝ => (resolventMat A ⟨y, η⟩).trace.im := by
  have hz : Continuous fun y : ℝ => (⟨y, η⟩ : ℂ) := by
    have : (fun y : ℝ => (⟨y, η⟩ : ℂ)) = fun y : ℝ => (y : ℂ) + (η : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [this]; fun_prop
  have := continuity_resolventMat_continuous (g := fun _ : ℝ => A) continuous_const hz
    (fun _ => hA) (fun _ => hη.ne')
  exact Complex.continuous_im.comp this.matrix_trace

/-- Lemma 11.8 (c): `|X(A) - X(A')| ≤ n (E₂ - E₁) / (π η²) ‖A - A'‖`. -/
theorem abs_smoothCount_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A A' : Matrix n n ℂ}
    (hA : A.IsHermitian) (hA' : A'.IsHermitian) {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) :
    |smoothCount E₁ E₂ η A - smoothCount E₁ E₂ η A'| ≤
      Fintype.card n * (E₂ - E₁) / (π * η ^ 2) * ‖A - A'‖ := by
  have hint : ∀ {B : Matrix n n ℂ}, B.IsHermitian →
      IntervalIntegrable (fun y : ℝ => (resolventMat B ⟨y, η⟩).trace.im) volume E₁ E₂ :=
    fun hB => (continuity_trace_im_continuous hB hη).intervalIntegrable _ _
  have hz : ∀ y : ℝ, 0 < (⟨y, η⟩ : ℂ).im := fun _ => hη
  have hpt : ∀ y ∈ Set.uIoc E₁ E₂,
      ‖(resolventMat A ⟨y, η⟩).trace.im - (resolventMat A' ⟨y, η⟩).trace.im‖ ≤
        Fintype.card n * (1 / η * (‖A - A'‖ * (1 / η))) := by
    intro y _
    have h1 : (resolventMat A ⟨y, η⟩).trace.im - (resolventMat A' ⟨y, η⟩).trace.im =
        (resolventMat A ⟨y, η⟩ * (A' - A) * resolventMat A' ⟨y, η⟩).trace.im := by
      rw [← resolventMat_sub_resolventMat hA hA' (hz y).ne', Matrix.trace_sub, Complex.sub_im]
    rw [h1, Real.norm_eq_abs]
    refine (continuity_abs_trace_im_le _).trans ?_
    gcongr
    calc ‖resolventMat A ⟨y, η⟩ * (A' - A) * resolventMat A' ⟨y, η⟩‖
        ≤ ‖resolventMat A ⟨y, η⟩ * (A' - A)‖ * ‖resolventMat A' ⟨y, η⟩‖ := norm_mul_le _ _
      _ ≤ ‖resolventMat A ⟨y, η⟩‖ * ‖A' - A‖ * ‖resolventMat A' ⟨y, η⟩‖ := by
          gcongr; exact norm_mul_le _ _
      _ ≤ 1 / η * ‖A - A'‖ * (1 / η) := by
          rw [norm_sub_rev A' A]
          gcongr
          · exact norm_resolventMat_le hA (hz y)
          · exact norm_resolventMat_le hA' (hz y)
      _ = 1 / η * (‖A - A'‖ * (1 / η)) := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  unfold smoothCount
  rw [← mul_sub, ← intervalIntegral.integral_sub (hint hA) (hint hA'), abs_mul,
    abs_of_pos (inv_pos.2 pi_pos)]
  rw [Real.norm_eq_abs] at hb
  rw [abs_of_nonneg (sub_nonneg.2 hE)] at hb
  calc π⁻¹ * |∫ y in E₁..E₂, ((resolventMat A ⟨y, η⟩).trace.im -
          (resolventMat A' ⟨y, η⟩).trace.im)|
      ≤ π⁻¹ * (Fintype.card n * (1 / η * (‖A - A'‖ * (1 / η))) * (E₂ - E₁)) := by
        gcongr
    _ = Fintype.card n * (E₂ - E₁) / (π * η ^ 2) * ‖A - A'‖ := by
        field_simp

/-! ### 2. Continuity in the entries -/

/-- `x ↦ H(x)` is continuous (entrywise, equivalently in the operator norm). -/
private lemma continuity_toMatrixC_continuous {N : ℕ} :
    Continuous fun x : Pair N → 𝕜 => toMatrixC x := by
  have htoC : Continuous (toC : 𝕜 → ℂ) := by
    have : (toC : 𝕜 → ℂ) = fun y => (RCLike.re y : ℂ) + (RCLike.im y : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp [toC]
    rw [this]
    fun_prop
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · exact htoC.comp (continuous_apply _)
  · exact htoC.comp (continuous_star.comp (continuous_apply _))
  · exact htoC.comp (RCLike.continuous_ofReal.comp
      (RCLike.continuous_re.comp (continuous_apply _)))

/-- `X` is continuous along a continuous family of hermitian matrices. -/
private lemma continuity_smoothCount_continuous {α : Type*} [TopologicalSpace α]
    {n : Type*} [Fintype n] [DecidableEq n] {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂)
    {g : α → Matrix n n ℂ} (hg : Continuous g) (hh : ∀ x, (g x).IsHermitian) :
    Continuous fun x => smoothCount E₁ E₂ η (g x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Tendsto (fun x => Fintype.card n * (E₂ - E₁) / (π * η ^ 2) * ‖g x - g x₀‖)
      (𝓝 x₀) (𝓝 0) := by
    have h0 : Tendsto (fun x => ‖g x - g x₀‖) (𝓝 x₀) (𝓝 0) := by
      have := (hg.tendsto x₀)
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      exact this
    simpa using h0.const_mul (Fintype.card n * (E₂ - E₁) / (π * η ^ 2))
  refine squeeze_zero (fun _ => dist_nonneg) (fun x => ?_) hc
  rw [Real.dist_eq]
  exact abs_smoothCount_sub_le (hh x) (hh x₀) hη hE

theorem continuous_smoothCount_toMatrixC {N : ℕ} {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) :
    Continuous fun x : Pair N → 𝕜 => smoothCount E₁ E₂ η (toMatrixC x) := by
  exact continuity_smoothCount_continuous hη hE continuity_toMatrixC_continuous
    toMatrixC_isHermitian

theorem continuous_smoothCount_minor {N : ℕ} {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂)
    (p : Pair N) (c : Fin N) :
    Continuous fun x : Pair N → 𝕜 => smoothCount E₁ E₂ η
      ((toMatrixC (Function.update x p 0)).submatrix
        (Subtype.val : {i // i ∉ ({c} : Finset (Fin N))} → Fin N) Subtype.val) := by
  have hu : Continuous fun x : Pair N → 𝕜 => Function.update x p 0 :=
    continuous_pi fun q => by
      by_cases h : q = p
      · subst h; simp only [Function.update_self]; exact continuous_const
      · simp only [Function.update_of_ne h]; exact continuous_apply q
  refine continuity_smoothCount_continuous hη hE ?_ fun x => (toMatrixC_isHermitian _).submatrix _
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j.val).comp
      ((continuous_apply i.val).comp (continuity_toMatrixC_continuous.comp hu))

theorem continuous_lamMax {N : ℕ} : Continuous (lamMax : (Pair N → 𝕜) → ℝ) := by
  unfold lamMax
  by_cases h : 0 < N
  · simp only [h, dite_true]
    exact continuous_eig _
  · simp only [h, dite_false]
    exact continuous_const

theorem continuous_resolventMat_toMatrixC {N : ℕ} {z : ℂ} (hz : 0 < z.im) (k l : Fin N) :
    Continuous fun x : Pair N → 𝕜 => resolventMat (toMatrixC x) z k l := by
  have := continuity_resolventMat_continuous (g := fun x : Pair N → 𝕜 => toMatrixC x)
    (z := fun _ => z) continuity_toMatrixC_continuous continuous_const toMatrixC_isHermitian
    (fun _ => hz.ne')
  exact (continuous_apply l).comp ((continuous_apply k).comp this)

end Rigidity
