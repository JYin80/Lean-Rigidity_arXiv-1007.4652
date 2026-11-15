import Mathlib

open MeasureTheory Real
open scoped ENNReal

/-!
# The Helffer–Sjöstrand formula

§3.5, Lemma 3.15; numbers refer to the blueprint NP v1.1 and the original paper is cited as
[EYY, …]. For a real `f ∈ C²` with compact support and an even cutoff
`χ ∈ C¹` with `χ = 1` on `[-1, 1]`, `χ = 0` outside `[-2, 2]` and `0 ≤ χ ≤ 1`,
`f(λ) = (2π)⁻¹ ∫∫ g(x, y) / (λ - x - i y) dx dy` (equation (3.10)), where
`g(x, y) = i y f''(x) χ(y) + i (f(x) + i y f'(x)) χ'(y)`; the integral is absolutely convergent,
with the dominating function of (HS′), and `g(x, -y) = conj g(x, y)`.

The double integral is the integral over `ℝ × ℝ` for the product measure. The proof applies
the divergence theorem on the rectangles `[-ρ, ρ] × [ε, 3]` and `[-ρ, ρ] × [-3, -ε]`,
which gives (HS3), and lets `ε ↓ 0` by dominated convergence.
-/

namespace Rigidity

/-- The integrand `g(x, y)` of Lemma 3.15. -/
noncomputable def hsG (f χ : ℝ → ℝ) (x y : ℝ) : ℂ :=
  Complex.I * y * deriv (deriv f) x * χ y + Complex.I * (f x + Complex.I * y * deriv f x) * deriv χ y

private theorem hs_den_ne {lam x y : ℝ} (hy : y ≠ 0) :
    (lam : ℂ) - x - Complex.I * y ≠ 0 := by
  intro h
  exact hy (by simpa using congrArg Complex.im h)

private theorem hs_norm_den (lam x y : ℝ) : |y| ≤ ‖(lam : ℂ) - x - Complex.I * y‖ := by
  have := Complex.abs_im_le_norm ((lam : ℂ) - x - Complex.I * y)
  simpa using this

private theorem hs_deriv_cut {χ : ℝ → ℝ} (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) {y : ℝ} (hy : |y| < 1 ∨ 2 < |y|) : deriv χ y = 0 := by
  rcases hy with hy | hy
  · have hev : χ =ᶠ[nhds y] fun _ => 1 :=
      Filter.mem_of_superset ((isOpen_lt continuous_abs continuous_const).mem_nhds
        (show y ∈ {b : ℝ | |b| < 1} from hy)) fun z hz => hχ1 z (le_of_lt hz)
    rw [hev.deriv_eq]; simp
  · have hev : χ =ᶠ[nhds y] fun _ => 0 :=
      Filter.mem_of_superset ((isOpen_lt continuous_const continuous_abs).mem_nhds
        (show y ∈ {b : ℝ | 2 < |b|} from hy)) fun z hz => hχ0 z hz
    rw [hev.deriv_eq]; simp

private theorem hs_support {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x, ρ ≤ |x| → f x = 0 ∧ deriv f x = 0 ∧ deriv (deriv f) x = 0 := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun x hx => ?_⟩
  have hx' : x ∉ tsupport f := fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self R]
  exact ⟨image_eq_zero_of_notMem_tsupport hx',
    image_eq_zero_of_notMem_tsupport fun h => hx' (tsupport_deriv_subset h),
    image_eq_zero_of_notMem_tsupport fun h => hx' (tsupport_deriv_subset (tsupport_deriv_subset h))⟩

private theorem hs_hsG_zero {f χ : ℝ → ℝ} (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) (x : ℝ) : hsG f χ x 0 = 0 := by
  simp [hsG, hs_deriv_cut hχ1 hχ0 (Or.inl (by norm_num : |(0 : ℝ)| < 1))]

/-- The pointwise bound (HS′), valid also on `y = 0`. -/
private theorem hs_bound_all {f χ : ℝ → ℝ}
    (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (lam x y : ℝ) :
    ‖hsG f χ x y / ((lam : ℂ) - x - Complex.I * y)‖ ≤
        |deriv (deriv f) x| * Set.indicator {y : ℝ | |y| ≤ 2} 1 y +
          |deriv χ y| * (|f x| + 2 * |deriv f x|) := by
  have hind : 0 ≤ Set.indicator {y : ℝ | |y| ≤ 2} (1 : ℝ → ℝ) y :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hy : y = 0
  · subst hy
    rw [hs_hsG_zero hχ1 hχ0, zero_div, norm_zero]
    positivity
  set D : ℂ := (lam : ℂ) - x - Complex.I * y with hD
  have hDy : |y| ≤ ‖D‖ := hs_norm_den lam x y
  have hy0 : 0 < |y| := abs_pos.2 hy
  have hD0 : 0 < ‖D‖ := hy0.trans_le hDy
  rw [hsG, add_div]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_div]
  · rw [div_le_iff₀ hD0]
    have h1 : |χ y| ≤ Set.indicator {y : ℝ | |y| ≤ 2} (1 : ℝ → ℝ) y := by
      by_cases h2 : |y| ≤ 2
      · rw [Set.indicator_of_mem (by exact h2), abs_of_nonneg (hχb y).1]
        exact (hχb y).2
      · rw [hχ0 y (not_le.1 h2), abs_zero]; exact hind
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    calc |y| * |deriv (deriv f) x| * |χ y|
        ≤ ‖D‖ * |deriv (deriv f) x| * Set.indicator {y : ℝ | |y| ≤ 2} 1 y := by gcongr
      _ = _ := by ring
  · by_cases hc : deriv χ y = 0
    · simp [hc]
    have h12 : 1 ≤ |y| ∧ |y| ≤ 2 := by
      by_contra h
      rw [not_and_or, not_le, not_le] at h
      exact hc (hs_deriv_cut hχ1 hχ0 h)
    have hD1 : 1 ≤ ‖D‖ := h12.1.trans hDy
    rw [div_le_iff₀ hD0]
    have hn : ‖(f x : ℂ) + Complex.I * y * deriv f x‖ ≤ |f x| + 2 * |deriv f x| := by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
      gcongr
      exact h12.2
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    calc ‖(f x : ℂ) + Complex.I * y * deriv f x‖ * |deriv χ y|
        ≤ (|f x| + 2 * |deriv f x|) * |deriv χ y| := by gcongr
      _ ≤ (|f x| + 2 * |deriv f x|) * |deriv χ y| * ‖D‖ := by
          have : 0 ≤ (|f x| + 2 * |deriv f x|) * |deriv χ y| := by positivity
          nlinarith
      _ = _ := by ring

private theorem hs_reg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧ Continuous (deriv (deriv f)) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv] at hf
  obtain ⟨h1, -, h2⟩ := hf
  rw [contDiff_one_iff_deriv] at h2
  exact ⟨h1, h2.1, h2.2⟩

private theorem hs_Gamma_integrable {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hχ : ContDiff ℝ 1 χ) (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) :
    Integrable (fun p : ℝ × ℝ => |deriv (deriv f) p.1| * Set.indicator {y : ℝ | |y| ≤ 2} 1 p.2 +
          |deriv χ p.2| * (|f p.1| + 2 * |deriv f p.1|)) := by
  obtain ⟨hd1, hd2, hc3⟩ := hs_reg hf
  have hc' : Continuous (deriv χ) := (contDiff_one_iff_deriv.1 hχ).2
  have i1 : Integrable (fun x => |deriv (deriv f) x|) :=
    hc3.abs.integrable_of_hasCompactSupport (hfc.deriv.deriv.comp_left abs_zero)
  have hset : {y : ℝ | |y| ≤ 2} = Set.Icc (-2) 2 := by ext y; simp [abs_le]
  have i2 : Integrable (Set.indicator {y : ℝ | |y| ≤ 2} (1 : ℝ → ℝ)) := by
    rw [hset]; exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hcs : HasCompactSupport (deriv χ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun y hy => ?_
    refine hs_deriv_cut hχ1 hχ0 (Or.inr ?_)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rw [lt_abs]; rcases hy with h | h
    · right; linarith
    · left; exact h
  have i3 : Integrable (fun y => |deriv χ y|) :=
    hc'.abs.integrable_of_hasCompactSupport (hcs.comp_left abs_zero)
  have i4 : Integrable (fun x => |f x| + 2 * |deriv f x|) :=
    (hd1.continuous.abs.integrable_of_hasCompactSupport (hfc.comp_left abs_zero)).add
      ((hd2.continuous.abs.integrable_of_hasCompactSupport
        (hfc.deriv.comp_left abs_zero)).const_mul 2)
  exact (i1.mul_prod i2).add ((i4.mul_prod i3).congr (ae_of_all _ fun p => mul_comm _ _))

private theorem hs_hsG_continuous {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ) :
    Continuous (fun p : ℝ × ℝ => hsG f χ p.1 p.2) := by
  obtain ⟨hd1, hd2, hc3⟩ := hs_reg hf
  have hc1 := hd1.continuous
  have hc2 := hd2.continuous
  have hχc := hχ.continuous
  have hc' : Continuous (deriv χ) := (contDiff_one_iff_deriv.1 hχ).2
  unfold hsG; fun_prop

private theorem hs_integrable {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hχ : ContDiff ℝ 1 χ) (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (lam : ℝ) :
    Integrable (fun p : ℝ × ℝ => hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2)) := by
  refine (hs_Gamma_integrable hf hfc hχ hχ1 hχ0).mono' ?_
    (ae_of_all _ fun p => hs_bound_all hχ1 hχ0 hχb lam p.1 p.2)
  exact ((hs_hsG_continuous hf hχ).measurable.div (by fun_prop)).aestronglyMeasurable

/-- `f̃ h` with `f̃(x, y) = (f(x) + i y f'(x)) χ(y)` and `h(x, y) = (λ - x - i y)⁻¹`. -/
private noncomputable def hsF (f χ : ℝ → ℝ) (lam : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((f p.1 : ℂ) + Complex.I * p.2 * ((deriv f p.1 : ℝ) : ℂ)) * (χ p.2 : ℂ) /
    ((lam : ℂ) - p.1 - Complex.I * p.2)

private theorem hsF_differentiableAt {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ)
    (lam : ℝ) {p : ℝ × ℝ} (hp : p.2 ≠ 0) : DifferentiableAt ℝ (hsF f χ lam) p := by
  obtain ⟨hd1, hd2, -⟩ := hs_reg hf
  have hχd : Differentiable ℝ χ := hχ.differentiable one_ne_zero
  have : hsF f χ lam = fun q : ℝ × ℝ =>
      ((f q.1 : ℂ) + Complex.I * q.2 * ((deriv f q.1 : ℝ) : ℂ)) * (χ q.2 : ℂ) *
        ((lam : ℂ) - q.1 - Complex.I * q.2)⁻¹ := funext fun q => div_eq_mul_inv _ _
  rw [this]
  exact DifferentiableAt.mul (by fun_prop) (DifferentiableAt.fun_inv (by fun_prop) (hs_den_ne hp))

/-- (HS1) and (HS2): `∂ₓF + i ∂ᵧF = g h` off the line `y = 0`, for `F = f̃ h`. -/
private theorem hsF_fderiv {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ)
    (lam : ℝ) {p : ℝ × ℝ} (hp : p.2 ≠ 0) :
    fderiv ℝ (hsF f χ lam) p (1, 0) + Complex.I * fderiv ℝ (hsF f χ lam) p (0, 1) =
      hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2) := by
  obtain ⟨x, y⟩ := p
  simp only at hp ⊢
  obtain ⟨hd1, hd2, -⟩ := hs_reg hf
  have hχd : Differentiable ℝ χ := hχ.differentiable one_ne_zero
  have hL := (hsF_differentiableAt hf hχ lam (p := (x, y)) hp).hasFDerivAt
  have hx := hL.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  have hy := hL.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  have hD0 := hs_den_ne (lam := lam) (x := x) hp
  have ex := (((hd1 x).hasDerivAt.ofReal_comp.add
    ((hd2 x).hasDerivAt.ofReal_comp.const_mul (Complex.I * y))).mul_const (χ y : ℂ)).div
    (((hasDerivAt_const x (lam : ℂ)).sub (hasDerivAt_id' x).ofReal_comp).sub_const
      (Complex.I * y)) hD0
  have ey := (((hasDerivAt_const y (f x : ℂ)).add
    (((hasDerivAt_id' y).ofReal_comp.const_mul Complex.I).mul_const ((deriv f x : ℝ) : ℂ))).mul
    (hχd y).hasDerivAt.ofReal_comp).div
    ((hasDerivAt_const y ((lam : ℂ) - x)).sub ((hasDerivAt_id' y).ofReal_comp.const_mul
      Complex.I)) hD0
  rw [hx.unique ex, hy.unique ey]
  simp only [hsG, Complex.ofReal_one, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, mul_one,
    zero_sub, zero_add]
  set D : ℂ := (lam : ℂ) - x - Complex.I * y with hD
  field_simp
  linear_combination ((χ y : ℂ) * (((deriv f x : ℝ) : ℂ) * D + ((f x : ℂ) +
    ((deriv f x : ℝ) : ℂ) * Complex.I * y))) * Complex.I_sq

/-- The divergence theorem on a rectangle that avoids the line `y = 0`, for the field
`(F, i F)` with `F = f̃ h`. -/
private theorem hs_rect {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ) (lam : ℝ)
    {a b : ℝ × ℝ} (hab : a ≤ b) (h0 : ∀ p ∈ Set.Icc a b, p.2 ≠ 0)
    (hi : IntegrableOn (fun p : ℝ × ℝ => hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2))
      (Set.Icc a b)) :
    ∫ p in Set.Icc a b, hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2) =
      (((∫ x in a.1..b.1, Complex.I * hsF f χ lam (x, b.2)) -
          ∫ x in a.1..b.1, Complex.I * hsF f χ lam (x, a.2)) +
        ∫ y in a.2..b.2, hsF f χ lam (b.1, y)) - ∫ y in a.2..b.2, hsF f χ lam (a.1, y) := by
  have hD : ∀ p ∈ Set.Icc a b, HasFDerivAt (hsF f χ lam) (fderiv ℝ (hsF f χ lam) p) p :=
    fun p hp => (hsF_differentiableAt hf hχ lam (h0 p hp)).hasFDerivAt
  have heq : Set.EqOn (fun p => fderiv ℝ (hsF f χ lam) p (1, 0) +
      (Complex.I • fderiv ℝ (hsF f χ lam) p) (0, 1))
      (fun p : ℝ × ℝ => hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2)) (Set.Icc a b) :=
    fun p hp => by
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact hsF_fderiv hf hχ lam (h0 p hp)
  have hsub : ∀ p ∈ Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2 \ (∅ : Set (ℝ × ℝ)), p ∈ Set.Icc a b :=
    fun p hp => ⟨⟨hp.1.1.1.le, hp.1.2.1.le⟩, ⟨hp.1.1.2.le, hp.1.2.2.le⟩⟩
  rw [← setIntegral_congr_fun measurableSet_Icc heq]
  exact integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (hsF f χ lam)
    (fun p => Complex.I * hsF f χ lam p) (fderiv ℝ (hsF f χ lam))
    (fun p => Complex.I • fderiv ℝ (hsF f χ lam) p) a b hab ∅ Set.countable_empty
    (fun p hp => (hD p hp).continuousAt.continuousWithinAt)
    (fun p hp => ((hD p hp).const_mul Complex.I).continuousAt.continuousWithinAt)
    (fun p hp => hD p (hsub p hp)) (fun p hp => (hD p (hsub p hp)).const_mul Complex.I)
    (hi.congr_fun heq.symm measurableSet_Icc)

/-- The boundary terms at heights `±ε` give `2π` times the right side of (HS3). -/
private theorem hs_boundary (f χ : ℝ → ℝ) (lam x ε : ℝ) (hε : 0 < ε) (h1 : χ ε = 1)
    (h2 : χ (-ε) = 1) :
    Complex.I * hsF f χ lam (x, -ε) - Complex.I * hsF f χ lam (x, ε) =
      ((2 * (f x * (ε / ((lam - x) ^ 2 + ε ^ 2))) +
        2 * (deriv f x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2))) : ℝ) : ℂ) := by
  have d1 := hs_den_ne (lam := lam) (x := x) (y := ε) hε.ne'
  have e : (lam : ℂ) - x - Complex.I * ((-ε : ℝ) : ℂ) = (lam : ℂ) - x + Complex.I * ε := by
    push_cast; ring
  have d2 := hs_den_ne (lam := lam) (x := x) (y := -ε) (neg_ne_zero.2 hε.ne')
  rw [e] at d2
  have d3 : ((lam : ℂ) - x) ^ 2 + (ε : ℂ) ^ 2 ≠ 0 := by
    have : (lam - x) ^ 2 + ε ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  simp only [hsF, h1, h2, e]
  push_cast
  field_simp
  linear_combination (-2 * (ε : ℂ) * ((f x : ℂ) + ((deriv f x : ℝ) : ℂ) * ((lam : ℂ) - x)) *
    ((lam : ℂ) - x) ^ 2) * Complex.I_sq

/-- `∫ f(x) ε / ((λ - x)² + ε²) dx → π f(λ)` as `ε ↓ 0` (substitution `x = λ - ε s`). -/
private theorem hs_poisson {f : ℝ → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f) (lam : ℝ) :
    Filter.Tendsto (fun ε => ∫ x, f x * (ε / ((lam - x) ^ 2 + ε ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (π * f lam)) := by
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfs
  have hk : Continuous fun s : ℝ => (1 + s ^ 2)⁻¹ :=
    (continuous_const.add (continuous_pow 2)).inv₀ fun s =>
      (by positivity : (0 : ℝ) < 1 + s ^ 2).ne'
  have hsub : ∀ ε : ℝ, 0 < ε → ∫ x, f x * (ε / ((lam - x) ^ 2 + ε ^ 2)) =
      ∫ s, f (lam - ε * s) * (1 + s ^ 2)⁻¹ := by
    intro ε hε
    set ψ : ℝ → ℝ := fun t => f (lam - t) * (ε / (t ^ 2 + ε ^ 2)) with hψ
    have e1 : ∫ x, f x * (ε / ((lam - x) ^ 2 + ε ^ 2)) = ∫ t, ψ t := by
      rw [← integral_sub_left_eq_self ψ (μ := volume) lam]
      congr 1; ext x; simp [hψ]
    have e2 : ∫ s, f (lam - ε * s) * (1 + s ^ 2)⁻¹ = ε * ∫ s, ψ (ε * s) := by
      rw [← integral_const_mul]; congr 1; ext s; simp only [hψ]; field_simp; ring
    rw [e1, e2, Measure.integral_comp_mul_left, abs_inv, abs_of_pos hε, smul_eq_mul]
    field_simp
  have hlim : Filter.Tendsto (fun ε => ∫ s, f (lam - ε * s) * (1 + s ^ 2)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ s, f lam * (1 + s ^ 2)⁻¹)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => C * (1 + s ^ 2)⁻¹) ?_ ?_
      (integrable_inv_one_add_sq.const_mul C) ?_
    · exact Filter.Eventually.of_forall fun ε =>
        ((hfc.comp (by fun_prop)).mul hk).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ε => ae_of_all _ fun s => ?_
      rw [norm_mul, norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + s ^ 2)]
      gcongr
      exact hC _
    · refine ae_of_all _ fun s => ?_
      have : Continuous fun ε : ℝ => f (lam - ε * s) * (1 + s ^ 2)⁻¹ :=
        (hfc.comp (by fun_prop)).mul continuous_const
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [integral_const_mul, integral_univ_inv_one_add_sq, mul_comm] at hlim
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => (hsub ε hε).symm)

/-- `∫ g(x) ε (λ - x) / ((λ - x)² + ε²) dx → 0` as `ε ↓ 0`. -/
private theorem hs_conj {g : ℝ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (lam : ℝ) :
    Filter.Tendsto (fun ε => ∫ x, g x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hint : Integrable fun x => |g x| :=
    hgc.abs.integrable_of_hasCompactSupport (hgs.comp_left abs_zero)
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (F := fun ε x => g x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2))) (f := fun _ => (0 : ℝ))
    (fun x => |g x|) ?_ ?_ hint ?_
  · simpa using this
  · exact Filter.Eventually.of_forall fun ε => (by fun_prop : Measurable fun x =>
      g x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2))).aestronglyMeasurable
  · filter_upwards [eventually_mem_nhdsWithin] with ε hε
    refine ae_of_all _ fun x => ?_
    have hε : 0 < ε := hε
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_div, abs_of_pos (by positivity : 0 < (lam - x) ^ 2 + ε ^ 2),
      div_le_one (by positivity), abs_mul, abs_of_pos hε]
    nlinarith [sq_nonneg (|lam - x| - ε), sq_abs (lam - x), abs_nonneg (lam - x)]
  · refine ae_of_all _ fun x => ?_
    by_cases ha : lam - x = 0
    · simp [ha]
    · have : ContinuousAt (fun ε : ℝ => g x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2))) 0 := by
        refine continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
        positivity
      simpa using this.tendsto.mono_left nhdsWithin_le_nhds

/-- Lemma 3.15: the Helffer–Sjöstrand formula (3.10), with absolute convergence. -/
theorem helfferSjostrand {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hχ : ContDiff ℝ 1 χ) (hχe : ∀ y, χ (-y) = χ y) (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (lam : ℝ) :
    Integrable (fun p : ℝ × ℝ => hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2)) ∧
      (f lam : ℂ) = (2 * π : ℂ)⁻¹ *
        ∫ p : ℝ × ℝ, hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2) := by
  set K : ℝ × ℝ → ℂ := fun p => hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2) with hKdef
  have hK : Integrable K := hs_integrable hf hfc hχ hχ1 hχ0 hχb lam
  refine ⟨hK, ?_⟩
  obtain ⟨hd1, hd2, hc3⟩ := hs_reg hf
  obtain ⟨ρ, hρ, hz⟩ := hs_support hfc
  have hK0 : ∀ p : ℝ × ℝ, (ρ ≤ |p.1| ∨ 2 < |p.2|) → K p = 0 := by
    rintro ⟨x, y⟩ h
    simp only [hKdef]
    rcases h with h | h
    · simp [hsG, (hz x h).1, (hz x h).2.1, (hz x h).2.2]
    · simp [hsG, hχ0 y h, hs_deriv_cut hχ1 hχ0 (Or.inr h)]
  -- the integrals over `|y| ≥ ε`
  set J : ℝ → ℂ := fun ε => ∫ p, Set.indicator {p : ℝ × ℝ | ε ≤ |p.2|} K p with hJ
  have hlim1 : Filter.Tendsto J (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ p, K p)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (hs_Gamma_integrable hf hfc hχ hχ1 hχ0) ?_
    · exact Filter.Eventually.of_forall fun ε =>
        hK.aestronglyMeasurable.indicator (measurableSet_le measurable_const (by fun_prop))
    · exact Filter.Eventually.of_forall fun ε => ae_of_all _ fun p =>
        (norm_indicator_le_norm_self K p).trans (hs_bound_all hχ1 hχ0 hχb lam p.1 p.2)
    · refine ae_of_all _ fun p => ?_
      by_cases hp : p.2 = 0
      · have : K p = 0 := by simp only [hKdef, hp, hs_hsG_zero hχ1 hχ0, zero_div]
        have h0 : ∀ ε : ℝ, Set.indicator {p : ℝ × ℝ | ε ≤ |p.2|} K p = 0 := fun ε => by
          by_cases hm : p ∈ {p : ℝ × ℝ | ε ≤ |p.2|}
          · rw [Set.indicator_of_mem hm, this]
          · rw [Set.indicator_of_notMem hm]
        simp only [h0, this]
        exact tendsto_const_nhds
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (abs_pos.2 hp)] with ε hε
        rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | ε ≤ |p.2|} from hε.2.le)]
  -- the boundary integrals
  set P : ℝ → ℝ → ℝ := fun ε x => 2 * (f x * (ε / ((lam - x) ^ 2 + ε ^ 2))) +
    2 * (deriv f x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2))) with hPdef
  have hdecomp : ∀ ε, 0 < ε → ε ≤ 1 → J ε = ((∫ x, P ε x : ℝ) : ℂ) := by
    intro ε hε hε1
    have hsplit : Set.indicator {p : ℝ × ℝ | ε ≤ |p.2|} K = fun p =>
        Set.indicator (Set.Icc (-ρ, ε) (ρ, 3)) K p +
          Set.indicator (Set.Icc (-ρ, -3) (ρ, -ε)) K p := by
      funext p
      obtain ⟨x, y⟩ := p
      by_cases h : ρ ≤ |x| ∨ 2 < |y|
      · simp [Set.indicator_apply, hK0 (x, y) h]
      · rw [not_or, not_le, not_lt, abs_lt] at h
        obtain ⟨hx, hy⟩ := h
        rw [abs_le] at hy
        rcases le_or_gt ε y with h1 | h1
        · have m1 : (x, y) ∈ {p : ℝ × ℝ | ε ≤ |p.2|} := show ε ≤ |y| from h1.trans (le_abs_self y)
          have m2 : (x, y) ∈ Set.Icc (-ρ, ε) (ρ, 3) := ⟨⟨hx.1.le, h1⟩, ⟨hx.2.le, by linarith⟩⟩
          have m3 : (x, y) ∉ Set.Icc (-ρ, -3) (ρ, -ε) := fun hm => by
            linarith [(Prod.mk_le_mk.1 hm.2).2]
          rw [Set.indicator_of_mem m1, Set.indicator_of_mem m2, Set.indicator_of_notMem m3,
            add_zero]
        rcases le_or_gt y (-ε) with h2 | h2
        · have m1 : (x, y) ∈ {p : ℝ × ℝ | ε ≤ |p.2|} :=
            show ε ≤ |y| from (le_neg.1 h2).trans (neg_le_abs y)
          have m2 : (x, y) ∈ Set.Icc (-ρ, -3) (ρ, -ε) := ⟨⟨hx.1.le, by linarith⟩, ⟨hx.2.le, h2⟩⟩
          have m3 : (x, y) ∉ Set.Icc (-ρ, ε) (ρ, 3) := fun hm => by
            linarith [(Prod.mk_le_mk.1 hm.1).2]
          rw [Set.indicator_of_mem m1, Set.indicator_of_mem m2, Set.indicator_of_notMem m3,
            zero_add]
        · have m1 : (x, y) ∉ {p : ℝ × ℝ | ε ≤ |p.2|} := fun hm => by
            have : ε ≤ |y| := hm
            rw [le_abs'] at this
            rcases this with h | h <;> linarith
          have m2 : (x, y) ∉ Set.Icc (-ρ, -3) (ρ, -ε) := fun hm => by
            linarith [(Prod.mk_le_mk.1 hm.2).2]
          have m3 : (x, y) ∉ Set.Icc (-ρ, ε) (ρ, 3) := fun hm => by
            linarith [(Prod.mk_le_mk.1 hm.1).2]
          rw [Set.indicator_of_notMem m1, Set.indicator_of_notMem m2, Set.indicator_of_notMem m3,
            zero_add]
    have hF3 : ∀ x, hsF f χ lam (x, 3) = 0 := fun x => by
      simp [hsF, hχ0 3 (by norm_num [abs_of_pos])]
    have hF3' : ∀ x, hsF f χ lam (x, -3) = 0 := fun x => by
      simp [hsF, hχ0 (-3) (by norm_num [abs_of_neg])]
    have hFρ : ∀ y, hsF f χ lam (ρ, y) = 0 := fun y => by
      have h := hz ρ (le_abs_self ρ)
      simp [hsF, h.1, h.2.1]
    have hFρ' : ∀ y, hsF f χ lam (-ρ, y) = 0 := fun y => by
      have h := hz (-ρ) (by rw [abs_neg]; exact le_abs_self ρ)
      simp [hsF, h.1, h.2.1]
    have hcont : ∀ e : ℝ, e ≠ 0 → Continuous fun x => Complex.I * hsF f χ lam (x, e) := by
      intro e he
      refine continuous_const.mul (continuous_iff_continuousAt.2 fun x => ?_)
      exact ContinuousAt.comp (g := hsF f χ lam) (f := fun t : ℝ => (t, e)) (x := x)
        (hsF_differentiableAt hf hχ lam (p := (x, e)) he).continuousAt (by fun_prop)
    rw [hJ]
    simp only
    rw [hsplit, integral_add (hK.indicator measurableSet_Icc) (hK.indicator measurableSet_Icc),
      integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
      hs_rect hf hχ lam (a := (-ρ, ε)) (b := (ρ, 3)) (Prod.mk_le_mk.2 ⟨by linarith, by linarith⟩)
        (fun p hp => (lt_of_lt_of_le hε (Prod.mk_le_mk.1 hp.1).2).ne') hK.integrableOn,
      hs_rect hf hχ lam (a := (-ρ, -3)) (b := (ρ, -ε)) (Prod.mk_le_mk.2 ⟨by linarith, by linarith⟩)
        (fun p hp => (lt_of_le_of_lt (Prod.mk_le_mk.1 hp.2).2 (neg_neg_of_pos hε)).ne)
        hK.integrableOn]
    simp only [hF3, hF3', hFρ, hFρ', mul_zero, intervalIntegral.integral_zero, sub_zero,
      zero_sub, add_zero]
    rw [neg_add_eq_sub, ← intervalIntegral.integral_sub
      ((hcont _ (neg_ne_zero.2 hε.ne')).intervalIntegrable _ _)
      ((hcont _ hε.ne').intervalIntegrable _ _)]
    have hb : ∀ x, Complex.I * hsF f χ lam (x, -ε) - Complex.I * hsF f χ lam (x, ε) =
        (P ε x : ℂ) := fun x =>
      hs_boundary f χ lam x ε hε (hχ1 ε (by rw [abs_of_pos hε]; exact hε1))
        (hχ1 (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hε1))
    rw [intervalIntegral.integral_congr fun x _ => hb x, intervalIntegral.integral_of_le
      (by linarith), setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_ofReal
    intro x hx
    have hxρ : ρ ≤ |x| := by
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [hPdef, (hz x hxρ).1, (hz x hxρ).2.1]
  -- the limit `ε ↓ 0`
  have hker : ∀ ε : ℝ, 0 < ε → Continuous fun x : ℝ => ε / ((lam - x) ^ 2 + ε ^ 2) :=
    fun ε hε => continuous_const.div (by fun_prop) fun x => by positivity
  have hker' : ∀ ε : ℝ, 0 < ε → Continuous fun x : ℝ => ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2) :=
    fun ε hε => (by fun_prop : Continuous fun x : ℝ => ε * (lam - x)).div (by fun_prop)
      fun x => by positivity
  have hPint : ∀ ε, 0 < ε → ∫ x, P ε x =
      2 * (∫ x, f x * (ε / ((lam - x) ^ 2 + ε ^ 2))) +
        2 * ∫ x, deriv f x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2)) := by
    intro ε hε
    have hA : Integrable fun x => f x * (ε / ((lam - x) ^ 2 + ε ^ 2)) :=
      (hd1.continuous.mul (hker ε hε)).integrable_of_hasCompactSupport hfc.mul_right
    have hB : Integrable fun x => deriv f x * (ε * (lam - x) / ((lam - x) ^ 2 + ε ^ 2)) :=
      (hd2.continuous.mul (hker' ε hε)).integrable_of_hasCompactSupport hfc.deriv.mul_right
    simp only [hPdef]
    rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul, integral_const_mul]
  have hlim2 : Filter.Tendsto (fun ε => ∫ x, P ε x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * (π * f lam) + 2 * 0)) :=
    (((hs_poisson hd1.continuous hfc lam).const_mul 2).add
      ((hs_conj hd2.continuous hfc.deriv lam).const_mul 2)).congr'
      (eventually_mem_nhdsWithin.mono fun ε hε => (hPint ε hε).symm)
  have hlim3 : Filter.Tendsto J (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((2 * (π * f lam) + 2 * 0 : ℝ)) : ℂ)) :=
    ((Complex.continuous_ofReal.tendsto _).comp hlim2).congr' (by
      filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε using (hdecomp ε hε.1 hε.2.le).symm)
  rw [tendsto_nhds_unique hlim1 hlim3]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  simp

/-- Lemma 3.15, (HS'): the dominating function. -/
theorem hsG_bound {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hχ : ContDiff ℝ 1 χ) (hχe : ∀ y, χ (-y) = χ y) (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) :
    (∀ lam x y : ℝ, y ≠ 0 → ‖hsG f χ x y / ((lam : ℂ) - x - Complex.I * y)‖ ≤
        |deriv (deriv f) x| * Set.indicator {y : ℝ | |y| ≤ 2} 1 y +
          |deriv χ y| * (|f x| + 2 * |deriv f x|)) ∧
      Integrable (fun p : ℝ × ℝ => |deriv (deriv f) p.1| * Set.indicator {y : ℝ | |y| ≤ 2} 1 p.2 +
          |deriv χ p.2| * (|f p.1| + 2 * |deriv f p.1|)) ∧
      ∀ x y, hsG f χ x (-y) = starRingEnd ℂ (hsG f χ x y) := by
  refine ⟨fun lam x y _ => hs_bound_all hχ1 hχ0 hχb lam x y,
    hs_Gamma_integrable hf hfc hχ hχ1 hχ0, fun x y => ?_⟩
  have hodd : deriv χ (-y) = -deriv χ y := by
    have : χ = fun t => χ (-t) := funext fun t => (hχe t).symm
    conv_lhs => rw [this]
    rw [deriv_comp_neg, neg_neg]
  simp only [hsG, hχe, hodd, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end Rigidity
