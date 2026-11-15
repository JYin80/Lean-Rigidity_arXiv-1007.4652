import Rigidity.Edge.EntryDet
import Rigidity.Edge.LogBounds
import Rigidity.Edge.Resolvent
import Rigidity.Edge.SpecF

/-!
# The smoothed counting functional

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `A` and `η > 0`,
`smoothCount E₁ E₂ η A = π⁻¹ ∫_{E₁}^{E₂} Im tr G_A(y + iη) dy` (Definition 11.7).
By the spectral theorem it equals `∑ᵢ f(λᵢ)` with the window function `f` of
Lemma 11.8.  The determinant `p_A(y) = det (A - y - iη)` has derivative
`-p_A tr G_A` (Lemma 11.9 (i)).  If a function `D` satisfies `D · p_B = κ p_A` on `[E₁, E₂]` and
stays off the cut `(-∞, 0]`, the fundamental theorem of calculus for `Complex.log ∘ D` gives
`X(A) - X(B) = -π⁻¹ Im [Log D(E₂) - Log D(E₁)]`, with the bound `2/π (|D(E₁) - 1| + |D(E₂) - 1|)`
when `D(E₁)` and `D(E₂)` lie within `1/2` of `1` (Lemma 11.9 (ii)).  For a one-entry perturbation of
a hermitian matrix this yields the exact formula of Corollary 11.11 (i).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section SmoothCountC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Definition 11.7: `X_{E₁,E₂,η}(A) = π⁻¹ ∫_{E₁}^{E₂} Im tr G_A(y + iη) dy`; it is `0` for the
empty matrix. -/
noncomputable def smoothCount (E₁ E₂ η : ℝ) (A : Matrix n n ℂ) : ℝ :=
  π⁻¹ * ∫ y in E₁..E₂, (resolventMat A ⟨y, η⟩).trace.im

/-- `A - z` is conjugate to the diagonal matrix of the shifted eigenvalues. -/
private lemma smoothCount_sub_eq_conj {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    A - z • (1 : Matrix n n ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ) - z) *
        (star hA.eigenvectorUnitary : Matrix n n ℂ) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_mul_star_self _
  have h1 := hA.spectral_theorem
  have h2 : z • (1 : Matrix n n ℂ) = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (z • (1 : Matrix n n ℂ)) * (star hA.eigenvectorUnitary : Matrix n n ℂ) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]
  conv_lhs => rw [h1, h2]
  rw [Unitary.conjStarAlgAut_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- `det (A - z) = ∏ᵢ (λᵢ - z)` for hermitian `A`. -/
private lemma smoothCount_det_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    (A - z • (1 : Matrix n n ℂ)).det = ∏ i, (((hA.eigenvalues i : ℝ) : ℂ) - z) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_mul_star_self _
  rw [smoothCount_sub_eq_conj hA z, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    mul_comm (hA.eigenvectorUnitary : Matrix n n ℂ).det, mul_assoc, ← Matrix.det_mul, hU,
    Matrix.det_one, mul_one]

/-- `tr G_A(z) = ∑ᵢ (λᵢ - z)⁻¹` for hermitian `A` and `Im z ≠ 0`. -/
private lemma smoothCount_trace_resolvent {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    (resolventMat A z).trace = ∑ i, (((hA.eigenvalues i : ℝ) : ℂ) - z)⁻¹ := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ) * (star hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_mul_star_self _
  have hU' : (star hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self _
  have hne : ∀ i, ((hA.eigenvalues i : ℝ) : ℂ) - z ≠ 0 := fun i h => by
    exact hz (by simpa using congrArg Complex.im h)
  have hD : (Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ) - z))⁻¹ =
      Matrix.diagonal (fun i => (((hA.eigenvalues i : ℝ) : ℂ) - z)⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    exact mul_inv_cancel₀ (hne i)
  unfold resolventMat
  rw [smoothCount_sub_eq_conj hA z, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_eq_right_inv hU, Matrix.inv_eq_right_inv hU', hD,
    ← Matrix.mul_assoc, Matrix.trace_mul_cycle, hU', Matrix.one_mul, Matrix.trace_diagonal]

/-- `Im tr G_A(y + iη) = ∑ᵢ η / ((λᵢ - y)² + η²)` for hermitian `A` and `η ≠ 0`. -/
private lemma smoothCount_trace_im {A : Matrix n n ℂ} (hA : A.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (y : ℝ) :
    (resolventMat A ⟨y, η⟩).trace.im =
      ∑ i, η / ((hA.eigenvalues i - y) ^ 2 + η ^ 2) := by
  rw [smoothCount_trace_resolvent hA (z := ⟨y, η⟩) hη, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im]
  simp [Complex.normSq_apply, pow_two]

/-- Continuity of `y ↦ Im tr G_A(y + iη)`. -/
private lemma smoothCount_continuous_trace_im {A : Matrix n n ℂ} (hA : A.IsHermitian) {η : ℝ}
    (hη : η ≠ 0) : Continuous fun y : ℝ => (resolventMat A ⟨y, η⟩).trace.im := by
  have h : (fun y : ℝ => (resolventMat A ⟨y, η⟩).trace.im) =
      fun y => ∑ i, η / ((hA.eigenvalues i - y) ^ 2 + η ^ 2) :=
    funext (smoothCount_trace_im hA hη)
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
  have : (0 : ℝ) < η ^ 2 := by positivity
  nlinarith [sq_nonneg (hA.eigenvalues i - y)]

/-- Lemma 11.8, spectral form. -/
theorem smoothCount_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) {E₁ E₂ η : ℝ} (hη : 0 < η) :
    smoothCount E₁ E₂ η A = ∑ i, specF E₁ E₂ η (hA.eigenvalues i) := by
  unfold smoothCount
  simp_rw [smoothCount_trace_im hA hη.ne']
  have hcont : ∀ i, Continuous fun y : ℝ => η / ((hA.eigenvalues i - y) ^ 2 + η ^ 2) := by
    intro i
    refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
    positivity
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => (hcont i).intervalIntegrable _ _)]
  simp_rw [integral_poisson_eq_specF hη]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

/-- The path `y ↦ y + iη` in `ℂ` has derivative `1`. -/
private lemma smoothCount_hasDerivAt_path (η : ℝ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => (⟨y, η⟩ : ℂ)) 1 y := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ) + (η : ℂ) * Complex.I) 1 y :=
    (HasDerivAt.ofReal_comp (hasDerivAt_id y)).add_const _
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  apply Complex.ext <;> simp

/-- Lemma 11.9 (i): `p_A' = -p_A tr G_A`, with `p_A(y) = det(A - y - iη)`. -/
theorem hasDerivAt_det_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (y : ℝ) :
    HasDerivAt (fun y : ℝ => (A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det)
      (-(A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det * (resolventMat A ⟨y, η⟩).trace) y := by
  have hf : ∀ i ∈ (Finset.univ : Finset n),
      HasDerivAt (fun y : ℝ => ((hA.eigenvalues i : ℝ) : ℂ) - (⟨y, η⟩ : ℂ)) (-1) y :=
    fun i _ => (smoothCount_hasDerivAt_path η y).const_sub _
  have hprod := HasDerivAt.fun_finsetProd hf
  have hfun : (fun y : ℝ => (A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det) =
      fun y : ℝ => ∏ i, (((hA.eigenvalues i : ℝ) : ℂ) - (⟨y, η⟩ : ℂ)) :=
    funext fun y => smoothCount_det_sub hA _
  rw [hfun]
  refine hprod.congr_deriv ?_
  rw [smoothCount_det_sub hA, smoothCount_trace_resolvent hA (z := ⟨y, η⟩) hη, neg_mul,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : ((hA.eigenvalues i : ℝ) : ℂ) - (⟨y, η⟩ : ℂ) ≠ 0 := fun h => by
    exact hη (by simpa using congrArg Complex.im h)
  have h1 := Finset.mul_prod_erase Finset.univ
    (fun j => ((hA.eigenvalues j : ℝ) : ℂ) - (⟨y, η⟩ : ℂ)) (Finset.mem_univ i)
  rw [smul_neg, smul_eq_mul, mul_one, ← h1, mul_comm _ (∏ j ∈ Finset.univ.erase i, _),
    mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- Lemma 11.9 (ii), (11.17). -/
theorem smoothCount_sub_eq_log {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix n n ℂ}
    {B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) {E₁ E₂ η : ℝ} (hη : 0 < η)
    (hE : E₁ ≤ E₂) (D : ℝ → ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (hD : ∀ y ∈ Set.Icc E₁ E₂, D y * (B - (⟨y, η⟩ : ℂ) • (1 : Matrix m m ℂ)).det =
      κ * (A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det)
    (hcut : ∀ y ∈ Set.Icc E₁ E₂, D y ∈ Complex.slitPlane) :
    smoothCount E₁ E₂ η A - smoothCount E₁ E₂ η B =
      -π⁻¹ * (Complex.log (D E₂) - Complex.log (D E₁)).im := by
  have hpA : ∀ y : ℝ, (A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det ≠ 0 := fun y =>
    det_sub_smul_ne_zero hA (z := ⟨y, η⟩) hη.ne'
  have hpB : ∀ y : ℝ, (B - (⟨y, η⟩ : ℂ) • (1 : Matrix m m ℂ)).det ≠ 0 := fun y =>
    det_sub_smul_ne_zero hB (z := ⟨y, η⟩) hη.ne'
  set Dt : ℝ → ℂ := fun y => κ * (A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det /
    (B - (⟨y, η⟩ : ℂ) • (1 : Matrix m m ℂ)).det with hDt_def
  have hDt : ∀ y ∈ Set.Icc E₁ E₂, Dt y = D y := by
    intro y hy
    rw [hDt_def]
    simp only
    rw [div_eq_iff (hpB y), ← hD y hy]
  have hDt_ne : ∀ y, Dt y ≠ 0 := fun y =>
    div_ne_zero (mul_ne_zero hκ (hpA y)) (hpB y)
  have hderiv : ∀ y : ℝ, HasDerivAt Dt (Dt y * ((resolventMat B ⟨y, η⟩).trace -
      (resolventMat A ⟨y, η⟩).trace)) y := by
    intro y
    have h := ((hasDerivAt_det_sub hA hη.ne' y).const_mul κ).div
      (hasDerivAt_det_sub hB hη.ne' y) (hpB y)
    refine h.congr_deriv ?_
    rw [hDt_def]
    simp only
    have := hpB y
    field_simp
    ring
  have hlog : ∀ y ∈ Set.uIcc E₁ E₂, HasDerivAt (fun t => (Complex.log (Dt t)).im)
      ((resolventMat B ⟨y, η⟩).trace.im - (resolventMat A ⟨y, η⟩).trace.im) y := by
    intro y hy
    rw [Set.uIcc_of_le hE] at hy
    have hslit : Dt y ∈ Complex.slitPlane := by rw [hDt y hy]; exact hcut y hy
    have h := (hderiv y).clog_real hslit
    rw [mul_div_cancel_left₀ _ (hDt_ne y)] at h
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h
    simpa [Function.comp_def] using h2
  have hcontA := smoothCount_continuous_trace_im hA hη.ne'
  have hcontB := smoothCount_continuous_trace_im hB hη.ne'
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hlog
    ((hcontB.sub hcontA).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub (hcontB.intervalIntegrable _ _)
    (hcontA.intervalIntegrable _ _)] at hint
  have e2 : Dt E₂ = D E₂ := hDt E₂ ⟨hE, le_rfl⟩
  have e1 : Dt E₁ = D E₁ := hDt E₁ ⟨le_rfl, hE⟩
  simp only [e1, e2] at hint
  unfold smoothCount
  rw [Complex.sub_im, ← hint]
  ring

/-- Lemma 11.9 (ii), (11.18). -/
theorem abs_smoothCount_sub_le_of_log {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (D : ℝ → ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (hD : ∀ y ∈ Set.Icc E₁ E₂, D y * (B - (⟨y, η⟩ : ℂ) • (1 : Matrix m m ℂ)).det =
      κ * (A - (⟨y, η⟩ : ℂ) • (1 : Matrix n n ℂ)).det)
    (hcut : ∀ y ∈ Set.Icc E₁ E₂, D y ∈ Complex.slitPlane)
    (h₁ : ‖D E₁ - 1‖ ≤ 1 / 2) (h₂ : ‖D E₂ - 1‖ ≤ 1 / 2) :
    |smoothCount E₁ E₂ η A - smoothCount E₁ E₂ η B| ≤ 2 / π * (‖D E₁ - 1‖ + ‖D E₂ - 1‖) := by
  rw [smoothCount_sub_eq_log hA hB hη hE D κ hκ hD hcut]
  have e : ∀ w : ℂ, ‖w - 1‖ ≤ 1 / 2 → ‖Complex.log w‖ ≤ 2 * ‖w - 1‖ := fun w hw => by
    simpa using norm_clog_one_add_le (ζ := w - 1) hw
  have hb1 := e (D E₁) h₁
  have hb2 := e (D E₂) h₂
  have him : |(Complex.log (D E₂) - Complex.log (D E₁)).im| ≤
      ‖Complex.log (D E₂)‖ + ‖Complex.log (D E₁)‖ :=
    (Complex.abs_im_le_norm _).trans (norm_sub_le _ _)
  have hπ : 0 < π⁻¹ := inv_pos.mpr Real.pi_pos
  rw [neg_mul, abs_neg, abs_mul, abs_of_pos hπ]
  calc π⁻¹ * |(Complex.log (D E₂) - Complex.log (D E₁)).im|
      ≤ π⁻¹ * (2 * ‖D E₁ - 1‖ + 2 * ‖D E₂ - 1‖) :=
        mul_le_mul_of_nonneg_left (him.trans (by linarith)) hπ.le
    _ = 2 / π * (‖D E₁ - 1‖ + ‖D E₂ - 1‖) := by
        rw [div_eq_mul_inv, mul_comm 2 π⁻¹]
        ring

/-- Corollary 11.11 (i). -/
theorem smoothCount_add_entryMat {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {E₁ E₂ η : ℝ}
    (hη : 0 < η) (hE : E₁ ≤ E₂) (a b : n) (v : ℂ) :
    smoothCount E₁ E₂ η (Q + entryMat a b v) - smoothCount E₁ E₂ η Q =
      -π⁻¹ * (Complex.log (entryDet Q a b v ⟨E₂, η⟩) -
        Complex.log (entryDet Q a b v ⟨E₁, η⟩)).im := by
  refine smoothCount_sub_eq_log (hQ.add (entryMat_isHermitian a b v)) hQ hη hE
    (fun y => entryDet Q a b v ⟨y, η⟩) 1 one_ne_zero ?_ ?_
  · intro y _
    rw [one_mul, det_add_entryMat hQ (z := ⟨y, η⟩) hη, mul_comm]
  · intro y _
    exact entryDet_mem_slitPlane hQ (z := ⟨y, η⟩) hη a b v

end SmoothCountC

end Rigidity
