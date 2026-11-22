module

public import Rigidity.Semicircle.Basic
public import Rigidity.MainDefs

@[expose] public section

/-!
# The semicircle density and the Stieltjes representation of `m_sc`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

`rhoSc` is the semicircle density `ϱ_sc(x) = (4 - x²)₊^{1/2} / (2π)` of NP v1.1 (2.14).  This file
proves, for `Im z > 0`, the Stieltjes representation `m_sc(z) = ∫_{-2}^{2} ϱ_sc(x) / (x - z) dx`
and the total mass `∫_{-2}^{2} ϱ_sc = 1` (Lemma 3.3), and the boundary limit
`π⁻¹ Im m_sc(E + iη) → ϱ_sc(E)` as `η ↓ 0` for every real `E` (2.14).

The representation is obtained by the substitution `x = 2 cos θ`, which turns the integral into
`(2 m / π) ∫₀^π sin θ · sin θ / (1 + 2 m cos θ + m²) dθ` with `m = m_sc(z)`, followed by the
expansion `sin θ / (1 + 2 m cos θ + m²) = ∑ₖ (-m)ᵏ sin ((k + 1) θ)` and the orthogonality of the
sine functions on `[0, π]` (proof of Lemma 3.3).  The boundary limit uses the quadratic equation
`m² + z m + 1 = 0` of Lemma 3.1 (a): with `w = 2 m + z` one has `w² = z² - 4`, and
`(Im w)² = (|w²| - Re w²) / 2`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `ϱ_sc` is continuous. -/
private lemma stieltjes_rhoSc_continuous : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

/-- `ϱ_sc (2 cos θ) = sin θ / π` for `θ ∈ [0, π]` (proof of Lemma 3.3). -/
private lemma stieltjes_rhoSc_cos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π) :
    rhoSc (2 * cos θ) = sin θ / π := by
  have hs : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
  have h4 : 4 - (2 * cos θ) ^ 2 = (2 * sin θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  unfold rhoSc
  rw [h4, max_eq_left (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

/-- Geometric-series expansion of the Poisson-type kernel: for `‖m‖ < 1`,
`sin θ / (1 + 2 m cos θ + m²) = ∑ₙ (-m)ⁿ sin ((n + 1) θ)`. -/
private lemma stieltjes_hasSum_sin {m : ℂ} (hm : ‖m‖ < 1) (θ : ℝ) :
    HasSum (fun n : ℕ => (-m) ^ n * (Real.sin ((n + 1) * θ) : ℂ))
      ((Real.sin θ : ℂ) / (1 + 2 * m * (Real.cos θ : ℂ) + m ^ 2)) := by
  set u : ℂ := Complex.exp (θ * Complex.I) with hu
  set v : ℂ := Complex.exp (-(θ * Complex.I)) with hv
  have huv : u * v = 1 := by rw [hu, hv, ← Complex.exp_add]; simp
  have hnu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hnv : ‖v‖ = 1 := by
    have := Complex.norm_exp_ofReal_mul_I (-θ)
    simpa [hv, neg_mul] using this
  have hsin : (Real.sin θ : ℂ) = (v - u) * Complex.I / 2 := by
    rw [Complex.ofReal_sin, Complex.sin]
    simp only [hu, hv, neg_mul]
  have hcos : (Real.cos θ : ℂ) = (u + v) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
    simp only [hu, hv, neg_mul]
  have hterm : ∀ n : ℕ, (-m) ^ n * (Real.sin ((n + 1) * θ) : ℂ) =
      Complex.I / 2 * (v * (-(m * v)) ^ n - u * (-(m * u)) ^ n) := by
    intro n
    have e1 : (Real.sin ((n + 1) * θ) : ℂ) = (v ^ (n + 1) - u ^ (n + 1)) * Complex.I / 2 := by
      rw [Complex.ofReal_sin, Complex.sin, hu, hv, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [e1]
    ring
  have hu1 : ‖-(m * u)‖ < 1 := by rw [norm_neg, norm_mul, hnu]; simpa using hm
  have hv1 : ‖-(m * v)‖ < 1 := by rw [norm_neg, norm_mul, hnv]; simpa using hm
  have hsum := ((hasSum_geometric_of_norm_lt_one hv1).mul_left v).sub
    ((hasSum_geometric_of_norm_lt_one hu1).mul_left u) |>.mul_left (Complex.I / 2)
  simp_rw [← hterm] at hsum
  simp only [sub_neg_eq_add] at hsum
  convert hsum using 1
  have h1 : 1 + m * v ≠ 0 := by
    intro h
    have : ‖m * v‖ = 1 := by
      have : m * v = -1 := by linear_combination h
      rw [this]; simp
    rw [norm_mul, hnv] at this
    linarith
  have h2 : 1 + m * u ≠ 0 := by
    intro h
    have : ‖m * u‖ = 1 := by
      have : m * u = -1 := by linear_combination h
      rw [this]; simp
    rw [norm_mul, hnu] at this
    linarith
  have hD : (1 + 2 * m * (Real.cos θ : ℂ) + m ^ 2) = (1 + m * v) * (1 + m * u) := by
    rw [hcos]
    linear_combination (-m ^ 2) * huv
  rw [hD, hsin, ← div_eq_mul_inv, ← div_eq_mul_inv, div_sub_div _ _ h1 h2]
  ring

private lemma stieltjes_integral_cos_nat (k : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (k * θ) = if k = 0 then π else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos]
    simp [Real.sin_nat_mul_pi, hk.ne']

private lemma stieltjes_integral_sin_mul (n : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.sin θ * Real.sin ((n + 1) * θ) = if n = 0 then π / 2 else 0 := by
  have h : ∀ θ : ℝ, Real.sin θ * Real.sin ((n + 1) * θ) =
      (Real.cos (n * θ) - Real.cos (((n + 2 : ℕ) : ℝ) * θ)) / 2 := by
    intro θ
    have e1 : (n : ℝ) * θ = (n + 1) * θ - θ := by ring
    have e2 : ((n + 2 : ℕ) : ℝ) * θ = (n + 1) * θ + θ := by push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    stieltjes_integral_cos_nat, stieltjes_integral_cos_nat]
  · by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  · exact (by fun_prop : Continuous fun θ : ℝ => Real.cos (n * θ)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun θ : ℝ =>
      Real.cos (((n + 2 : ℕ) : ℝ) * θ)).intervalIntegrable _ _

/-- The orthogonality computation behind Lemma 3.3: for `‖m‖ < 1`,
`∫₀^π sin²θ / (1 + 2 m cos θ + m²) dθ = π / 2`. -/
private lemma stieltjes_integral_kernel {m : ℂ} (hm : ‖m‖ < 1) :
    ∫ θ in (0 : ℝ)..π,
      (Real.sin θ : ℂ) * ((Real.sin θ : ℂ) / (1 + 2 * m * (Real.cos θ : ℂ) + m ^ 2)) =
        ((π / 2 : ℝ) : ℂ) := by
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := π)
    (μ := volume)
    (F := fun (n : ℕ) (θ : ℝ) => (Real.sin θ : ℂ) * ((-m) ^ n * (Real.sin ((n + 1) * θ) : ℂ)))
    (f := fun θ : ℝ => (Real.sin θ : ℂ) *
      ((Real.sin θ : ℂ) / (1 + 2 * m * (Real.cos θ : ℂ) + m ^ 2)))
    (fun n _ => ‖m‖ ^ n)
    (fun n => (by fun_prop : Continuous fun θ : ℝ =>
      (Real.sin θ : ℂ) * ((-m) ^ n * (Real.sin ((n + 1) * θ) : ℂ))).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun θ _ => by
      rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := Real.abs_sin_le_one θ
      have h2 := Real.abs_sin_le_one ((n + 1) * θ)
      have h3 : 0 ≤ ‖m‖ ^ n := by positivity
      calc |Real.sin θ| * (‖m‖ ^ n * |Real.sin ((n + 1) * θ)|) ≤ 1 * (‖m‖ ^ n * 1) := by
            gcongr
        _ = ‖m‖ ^ n := by ring)
    (Filter.Eventually.of_forall fun θ _ => summable_geometric_of_lt_one (norm_nonneg m) hm)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ =>
      (stieltjes_hasSum_sin hm θ).mul_left (Real.sin θ : ℂ))
  have hI : ∀ n : ℕ, ∫ θ in (0 : ℝ)..π,
      (Real.sin θ : ℂ) * ((-m) ^ n * (Real.sin ((n + 1) * θ) : ℂ)) =
        (-m) ^ n * ((if n = 0 then π / 2 else 0 : ℝ) : ℂ) := by
    intro n
    have : ∀ θ : ℝ, (Real.sin θ : ℂ) * ((-m) ^ n * (Real.sin ((n + 1) * θ) : ℂ)) =
        (-m) ^ n * ((Real.sin θ * Real.sin ((n + 1) * θ) : ℝ) : ℂ) := by
      intro θ; push_cast; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      stieltjes_integral_sin_mul]
  have hsum := hasSum_single (f := fun n : ℕ => (-m) ^ n * ((if n = 0 then π / 2 else 0 : ℝ) : ℂ))
    0 (fun b hb => by simp [hb])
  simp only [← hI] at hsum
  have := hdom.unique hsum
  simpa using this

/-- Lemma 3.3: Stieltjes representation. -/
theorem msc_eq_integral {z : ℂ} (hz : 0 < z.im) :
    msc z = ∫ x in (-2 : ℝ)..2, (rhoSc x : ℂ) / ((x : ℂ) - z) := by
  have hm := msc_sq_add hz
  have hmi := msc_im_pos hz
  have hnm := norm_msc_lt_one hz
  set m := msc z with hmdef
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hmi
    simp at hmi
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    linarith
  set G : ℝ → ℂ := fun x => (rhoSc x : ℂ) / ((x : ℂ) - z) with hG
  have hGc : Continuous G :=
    (Complex.continuous_ofReal.comp stieltjes_rhoSc_continuous).div
      (Complex.continuous_ofReal.sub continuous_const) hne
  have hsub : (∫ θ in π..0, (2 * -Real.sin θ) • (G ∘ fun θ : ℝ => 2 * Real.cos θ) θ) =
      ∫ x in (2 * Real.cos π)..(2 * Real.cos 0), G x :=
    intervalIntegral.integral_deriv_smul_comp (a := π) (b := 0)
      (f := fun θ : ℝ => 2 * Real.cos θ) (f' := fun θ : ℝ => 2 * -Real.sin θ) (g := G)
      (fun θ _ => (Real.hasDerivAt_cos θ).const_mul 2) (by fun_prop) hGc
  rw [show 2 * Real.cos π = -2 by simp, show 2 * Real.cos 0 = 2 by simp] at hsub
  rw [← hsub, intervalIntegral.integral_symm (a := (0 : ℝ)) (b := π)]
  have hpt : ∀ θ ∈ Set.uIcc (0 : ℝ) π,
      (2 * -Real.sin θ) • (G ∘ fun θ : ℝ => 2 * Real.cos θ) θ =
      -(((2 / π : ℝ) : ℂ) * m *
        ((Real.sin θ : ℂ) * ((Real.sin θ : ℂ) / (1 + 2 * m * (Real.cos θ : ℂ) + m ^ 2)))) := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    obtain ⟨h0, h1⟩ := hθ
    simp only [Function.comp, hG]
    rw [stieltjes_rhoSc_cos h0 h1]
    have hD : (1 + 2 * m * (Real.cos θ : ℂ) + m ^ 2) = m * (2 * (Real.cos θ : ℂ) - z) := by
      linear_combination hm
    have hne' : (2 * (Real.cos θ : ℂ) - z) ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hx : (((2 * Real.cos θ : ℝ)) : ℂ) = 2 * (Real.cos θ : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hD, Complex.real_smul, hx]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, stieltjes_integral_kernel hnm]
  push_cast
  field_simp


/-- Lemma 3.3, total mass. -/
theorem integral_rhoSc : ∫ x in (-2 : ℝ)..2, rhoSc x = 1 := by
  have h1 : ∫ x in (-2 : ℝ)..2, rhoSc x = ∫ x in (-2 : ℝ)..2, π⁻¹ * √(1 - (x / 2) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have h4 : 4 - x ^ 2 = 2 ^ 2 * (1 - (x / 2) ^ 2) := by ring
    have hnn : 0 ≤ 1 - (x / 2) ^ 2 := by nlinarith
    simp only [rhoSc]
    rw [max_eq_left (by nlinarith), h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    field_simp
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x : ℝ => √(1 - x ^ 2)) (by norm_num : (2 : ℝ) ≠ 0)]
  have h2 : ((-2 : ℝ) / 2) = -1 := by norm_num
  have h3 : ((2 : ℝ) / 2) = 1 := by norm_num
  rw [h2, h3, integral_sqrt_one_sub_sq]
  simp only [smul_eq_mul]
  field_simp

end Rigidity
