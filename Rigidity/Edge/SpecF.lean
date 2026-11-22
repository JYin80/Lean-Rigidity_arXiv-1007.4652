module

public import Mathlib

@[expose] public section

/-!
# The spectral window function `f`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For an interval `[E₁, E₂]` and `η > 0` the function
`f(λ) = π⁻¹ [arctan((E₂-λ)/η) - arctan((E₁-λ)/η)]` is the integral of the Poisson kernel
`η / ((λ - y)² + η²)` over `[E₁, E₂]`, divided by `π` (proof of Lemma 11.8).  It takes values in
`[0, 1)` (Lemma 11.8), is close to `1` inside the interval (Lemma 11.8 (a)), and decays like
`η / dist` and `η (E₂ - E₁) / dist²` outside it (Lemma 11.8 (b)).
-/

open Real

namespace Rigidity

/-- `f(λ) = π⁻¹ [arctan((E₂-λ)/η) - arctan((E₁-λ)/η)]` (Lemma 11.8). -/
noncomputable def specF (E₁ E₂ η lam : ℝ) : ℝ :=
  π⁻¹ * (Real.arctan ((E₂ - lam) / η) - Real.arctan ((E₁ - lam) / η))

/-- `∫_{E₁}^{E₂} η / ((λ - y)² + η²) dy = π f(λ)` (proof of Lemma 11.8). -/
theorem integral_poisson_eq_specF {E₁ E₂ η : ℝ} (hη : 0 < η) (lam : ℝ) :
    ∫ y in E₁..E₂, η / ((lam - y) ^ 2 + η ^ 2) = π * specF E₁ E₂ η lam := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.arctan ((y - lam) / η))
      (η / ((lam - y) ^ 2 + η ^ 2)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y - lam) / η) (1 / η) y := by
      simpa using ((hasDerivAt_id y).sub_const lam).div_const η
    have h2 := (Real.hasDerivAt_arctan ((y - lam) / η)).comp y h1
    refine h2.congr_deriv ?_
    have : (0 : ℝ) < (lam - y) ^ 2 + η ^ 2 := by positivity
    field_simp
    ring
  have hcont : Continuous (fun y : ℝ => η / ((lam - y) ^ 2 + η ^ 2)) := by
    refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    (hcont.intervalIntegrable _ _)]
  unfold specF
  have hπ : π * π⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  rw [← mul_assoc, hπ, one_mul]

/-- `f(λ) ∈ [0, 1)` (Lemma 11.8). -/
theorem specF_mem {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (lam : ℝ) :
    specF E₁ E₂ η lam ∈ Set.Ico 0 1 := by
  unfold specF
  have hle : Real.arctan ((E₁ - lam) / η) ≤ Real.arctan ((E₂ - lam) / η) :=
    Real.arctan_strictMono.monotone (by gcongr)
  have h1 := Real.arctan_lt_pi_div_two ((E₂ - lam) / η)
  have h2 := Real.neg_pi_div_two_lt_arctan ((E₁ - lam) / η)
  have hπ : 0 < π⁻¹ := inv_pos.mpr Real.pi_pos
  constructor
  · exact mul_nonneg hπ.le (by linarith)
  · rw [inv_mul_lt_iff₀ Real.pi_pos]
    linarith

/-- Lemma 11.8 (a). -/
theorem one_sub_le_specF {E₁ E₂ η lam : ℝ} (hη : 0 < η) (h₁ : E₁ < lam) (h₂ : lam < E₂) :
    1 - η / π * (1 / (E₂ - lam) + 1 / (lam - E₁)) ≤ specF E₁ E₂ η lam := by
  have hx₂ : 0 < (E₂ - lam) / η := div_pos (by linarith) hη
  have hx₁ : 0 < (lam - E₁) / η := div_pos (by linarith) hη
  have ha₂ := Real.arctan_inv_of_pos hx₂
  have ha₁ := Real.arctan_inv_of_pos hx₁
  have hb₂ := Real.arctan_le_self (inv_nonneg.mpr hx₂.le)
  have hb₁ := Real.arctan_le_self (inv_nonneg.mpr hx₁.le)
  have hneg : Real.arctan ((E₁ - lam) / η) = -Real.arctan ((lam - E₁) / η) := by
    rw [← Real.arctan_neg]
    congr 1
    ring
  have i₂ : ((E₂ - lam) / η)⁻¹ = η * (1 / (E₂ - lam)) := by
    rw [inv_div]; field_simp
  have i₁ : ((lam - E₁) / η)⁻¹ = η * (1 / (lam - E₁)) := by
    rw [inv_div]; field_simp
  unfold specF
  rw [hneg]
  have hπ : 0 < π := Real.pi_pos
  have key : π - η * (1 / (E₂ - lam) + 1 / (lam - E₁)) ≤
      Real.arctan ((E₂ - lam) / η) - -Real.arctan ((lam - E₁) / η) := by
    rw [i₂] at hb₂ ha₂
    rw [i₁] at hb₁ ha₁
    nlinarith
  have : 1 - η / π * (1 / (E₂ - lam) + 1 / (lam - E₁)) =
      π⁻¹ * (π - η * (1 / (E₂ - lam) + 1 / (lam - E₁))) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hπ.le)

/-- Lemma 11.8 (b), first bound. -/
theorem specF_le_inv {E₁ E₂ η lam : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (h : lam < E₁) :
    specF E₁ E₂ η lam ≤ η / π * (1 / (E₁ - lam)) := by
  have hb : 0 < (E₁ - lam) / η := div_pos (by linarith) hη
  have ha := Real.arctan_inv_of_pos hb
  have hb' := Real.arctan_le_self (inv_nonneg.mpr hb.le)
  have h1 := Real.arctan_lt_pi_div_two ((E₂ - lam) / η)
  have i : ((E₁ - lam) / η)⁻¹ = η * (1 / (E₁ - lam)) := by
    rw [inv_div]; field_simp
  rw [i] at hb' ha
  unfold specF
  have hπ : 0 < π := Real.pi_pos
  have : η / π * (1 / (E₁ - lam)) = π⁻¹ * (η * (1 / (E₁ - lam))) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hπ.le)

/-- Lemma 11.8 (b), second bound. -/
theorem specF_le_sq {E₁ E₂ η lam : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (h : lam < E₁) :
    specF E₁ E₂ η lam ≤ η / π * ((E₂ - E₁) / (E₁ - lam) ^ 2) := by
  set b : ℝ := (E₁ - lam) / η with hbdef
  set a : ℝ := (E₂ - lam) / η with hadef
  have hb : 0 < b := div_pos (by linarith) hη
  have hab : b ≤ a := by rw [hbdef, hadef]; gcongr
  have hmvt : Real.arctan a - Real.arctan b ≤ (1 / b ^ 2) * (a - b) := by
    refine Convex.image_sub_le_mul_sub_of_deriv_le (D := Set.Ici b) (convex_Ici b)
      Real.continuous_arctan.continuousOn
      (Real.differentiable_arctan.differentiableOn) (fun x hx => ?_) b
      (Set.mem_Ici.mpr le_rfl) a (Set.mem_Ici.mpr hab) hab
    rw [interior_Ici] at hx
    have hx' : b < x := hx
    rw [Real.deriv_arctan]
    have hxpos : 0 < x := hb.trans hx'
    have : b ^ 2 ≤ 1 + x ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) this
  have hπ : 0 < π := Real.pi_pos
  unfold specF
  have e : η / π * ((E₂ - E₁) / (E₁ - lam) ^ 2) = π⁻¹ * ((1 / b ^ 2) * (a - b)) := by
    simp only [hbdef, hadef]
    have : E₁ - lam ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hmvt (inv_nonneg.mpr hπ.le)

end Rigidity
