module

public import Rigidity.Counting.HelfferSjostrand
public import Rigidity.Ensemble.Basic
public import Rigidity.LocalLaw.Defs
public import Rigidity.Semicircle.Algebra
public import Rigidity.Semicircle.Basic
public import Rigidity.Semicircle.Density
public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# The counting function from the Stieltjes transform

Numbers without a prefix refer to the blueprint NP v1.1; results of Erdős–Yau–Yin
(arXiv:1007.4652) are cited as [EYY, …].

* `quinticStep` is the quintic step `𝗌` of §3.5.
* `countOf lam E = N⁻¹ #{j : λ_j ≤ E}` and `stieltjesOf lam z = N⁻¹ ∑_j (λ_j - z)⁻¹` for a family
  `lam : Fin N → ℝ`.
* `count_from_stieltjes` is Lemma 3.16: if `|m - m_sc| ≤ U/(N y)` on
  `[E₁ - η, E₂ + η] × [η, 2]` (hypothesis (3.11)), then the counting function and `n_sc` differ on
  `(E₁, E₂]` by at most `(10/N)(U log(2/η) + N η)`. The corresponding statement of the original
  is [EYY, Lemma 5.1]; the hypothesis here is (3.11).

The proof follows §3.5: the Helffer–Sjöstrand formula (Lemma 3.15) for the window
`f(x) = 𝗌((x - E₁ + η)/η) 𝗌((E₂ + η - x)/η)` and the cutoff `χ(y) = 𝗌(2 - |y|)`, reduced to the
upper half-plane by `g(x, -y) = conj g(x, y)`; the terms `T₁`, `T₂`, `T₃` of Steps 2–4, where
`T₃` is handled by the divergence theorem on `[E₁ - η, E₂ + η] × [η, 2]` together with the
Cauchy–Riemann equations for `Δ = m - m_sc`; and the removal of the smoothing (Step 6). The family
`lam` need not be ordered.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The quintic step `𝗌` of §3.5. -/
noncomputable def quinticStep (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5

/-- The derivative `𝗌'` of the quintic step: `30 t² (1 - t)²` on `(0, 1)`, `0` elsewhere. -/
private noncomputable def qs1 (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 0 else 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4

/-- The second derivative `𝗌''`: `60 t (1 - t) (1 - 2t)` on `(0, 1)`, `0` elsewhere. -/
private noncomputable def qs2 (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if 1 ≤ t then 0 else 60 * t - 180 * t ^ 2 + 120 * t ^ 3

/-- Gluing a derivative at a point from the two sides. -/
private theorem count_glue {f p q : ℝ → ℝ} {c d : ℝ} (hp : HasDerivAt p d c)
    (hq : HasDerivAt q d c) (hfp : ∀ᶠ t in 𝓝 c, t ≤ c → f t = p t)
    (hfq : ∀ᶠ t in 𝓝 c, c ≤ t → f t = q t) : HasDerivAt f d c := by
  have h1 : HasDerivWithinAt f d (Set.Iic c) c :=
    hp.hasDerivWithinAt.congr_of_eventuallyEq (eventually_nhdsWithin_iff.2 hfp)
      (hfp.self_of_nhds le_rfl)
  have h2 : HasDerivWithinAt f d (Set.Ici c) c :=
    hq.hasDerivWithinAt.congr_of_eventuallyEq (eventually_nhdsWithin_iff.2 hfq)
      (hfq.self_of_nhds le_rfl)
  have := h1.union h2
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- A function given by a polynomial piece on `(0, 1)` and constants outside, with matching
values and vanishing derivative at `0` and `1`, is differentiable everywhere. -/
private theorem count_piece {P P' : ℝ → ℝ} {A B : ℝ} (hP : ∀ t, HasDerivAt P (P' t) t)
    (h0 : P 0 = A) (h1 : P 1 = B) (h0' : P' 0 = 0) (h1' : P' 1 = 0) (t : ℝ) :
    HasDerivAt (fun t => if t ≤ 0 then A else if 1 ≤ t then B else P t)
      (if t ≤ 0 then 0 else if 1 ≤ t then 0 else P' t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [ite_eq_left ht.le]
    refine (hasDerivAt_const t A).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds ht] with s hs
    rw [ite_eq_left hs.le]
  · simp only [le_refl, ite_true]
    refine count_glue (hasDerivAt_const (0 : ℝ) A) (h0' ▸ hP 0) ?_ ?_
    · exact Eventually.of_forall fun s hs => by rw [ite_eq_left hs]
    · filter_upwards [gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs hs0
      rcases hs0.lt_or_eq with hs0 | rfl
      · rw [ite_eq_right (not_le.2 hs0), ite_eq_right (not_le.2 hs)]
      · rw [ite_eq_left le_rfl, h0]
  rcases lt_trichotomy t 1 with ht1 | rfl | ht1
  · rw [ite_eq_right (not_le.2 ht), ite_eq_right (not_le.2 ht1)]
    refine (hP t).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht, gt_mem_nhds ht1] with s hs hs1
    rw [ite_eq_right (not_le.2 hs), ite_eq_right (not_le.2 hs1)]
  · rw [ite_eq_right (by norm_num), ite_eq_left le_rfl]
    refine count_glue (h1' ▸ hP 1) (hasDerivAt_const (1 : ℝ) B) ?_ ?_
    · filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs hs1
      rcases hs1.lt_or_eq with hs1 | rfl
      · rw [ite_eq_right (not_le.2 hs), ite_eq_right (not_le.2 hs1)]
      · rw [ite_eq_right (by norm_num), ite_eq_left le_rfl, h1]
    · filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs hs1
      rw [ite_eq_right (not_le.2 hs), ite_eq_left hs1]
  · rw [ite_eq_right (not_le.2 ht), ite_eq_left ht1.le]
    refine (hasDerivAt_const t B).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht, lt_mem_nhds ht1] with s hs hs1
    rw [ite_eq_right (not_le.2 hs), ite_eq_left hs1.le]

private theorem qs_hasDerivAt (t : ℝ) : HasDerivAt quinticStep (qs1 t) t := by
  have := count_piece (P := fun t => 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5)
    (P' := fun t => 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4) (A := 0) (B := 1)
    (fun t => by
      have := ((((hasDerivAt_pow 3 t).const_mul 10).sub ((hasDerivAt_pow 4 t).const_mul 15)).add
        ((hasDerivAt_pow 5 t).const_mul 6))
      convert this using 1; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t
  exact this

private theorem qs1_hasDerivAt (t : ℝ) : HasDerivAt qs1 (qs2 t) t := by
  have := count_piece (P := fun t => 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4)
    (P' := fun t => 60 * t - 180 * t ^ 2 + 120 * t ^ 3) (A := 0) (B := 0)
    (fun t => by
      have := ((((hasDerivAt_pow 2 t).const_mul 30).sub ((hasDerivAt_pow 3 t).const_mul 60)).add
        ((hasDerivAt_pow 4 t).const_mul 30))
      convert this using 1; push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t
  exact this

private theorem qs_deriv : deriv quinticStep = qs1 := funext fun t => (qs_hasDerivAt t).deriv

private theorem qs1_deriv : deriv qs1 = qs2 := funext fun t => (qs1_hasDerivAt t).deriv

private theorem qs2_continuous : Continuous qs2 := by
  unfold qs2
  refine Continuous.if_le continuous_const
    (Continuous.if_le continuous_const (by fun_prop) continuous_const continuous_id ?_)
    continuous_id continuous_const ?_
  · intro t ht; subst ht; norm_num
  · intro t ht; rw [ht]; norm_num

private theorem qs_differentiable : Differentiable ℝ quinticStep :=
  fun t => (qs_hasDerivAt t).differentiableAt

private theorem qs1_differentiable : Differentiable ℝ qs1 :=
  fun t => (qs1_hasDerivAt t).differentiableAt

private theorem qs_continuous : Continuous quinticStep := qs_differentiable.continuous

private theorem qs1_continuous : Continuous qs1 := qs1_differentiable.continuous

private theorem qs_contDiff : ContDiff ℝ 2 quinticStep := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨qs_differentiable, by simp, ?_⟩
  rw [qs_deriv, contDiff_one_iff_deriv, qs1_deriv]
  exact ⟨qs1_differentiable, qs2_continuous⟩

private theorem qs_of_nonpos {t : ℝ} (ht : t ≤ 0) : quinticStep t = 0 := by
  simp [quinticStep, ht]

private theorem qs_of_one_le {t : ℝ} (ht : 1 ≤ t) : quinticStep t = 1 := by
  simp [quinticStep, ht, show ¬ t ≤ 0 by intro h; linarith]

private theorem qs1_of_nonpos {t : ℝ} (ht : t ≤ 0) : qs1 t = 0 := by simp [qs1, ht]

private theorem qs1_of_one_le {t : ℝ} (ht : 1 ≤ t) : qs1 t = 0 := by
  simp [qs1, ht, show ¬ t ≤ 0 by intro h; linarith]

private theorem qs2_of_nonpos {t : ℝ} (ht : t ≤ 0) : qs2 t = 0 := by simp [qs2, ht]

private theorem qs2_of_one_le {t : ℝ} (ht : 1 ≤ t) : qs2 t = 0 := by
  simp [qs2, ht, show ¬ t ≤ 0 by intro h; linarith]

private theorem qs_bounds (t : ℝ) : 0 ≤ quinticStep t ∧ quinticStep t ≤ 1 := by
  unfold quinticStep
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · push Not at h0 h1
    constructor
    · nlinarith [mul_nonneg (pow_nonneg h0.le 3)
        (by nlinarith [sq_nonneg (t - 5 / 4)] : (0 : ℝ) ≤ 10 - 15 * t + 6 * t ^ 2)]
    · nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) 3)
        (by nlinarith : (0 : ℝ) ≤ 6 * t ^ 2 + 3 * t + 1)]

private theorem qs1_nonneg (t : ℝ) : 0 ≤ qs1 t := by
  unfold qs1
  split_ifs
  · rfl
  · rfl
  · nlinarith [sq_nonneg (t * (1 - t))]

/-- `∫ |𝗌'| = 1`. -/
private theorem qs1_integral : ∫ t, |qs1 t| = 1 := by
  have hz : ∀ t ∉ Set.Ioc (0 : ℝ) 1, |qs1 t| = 0 := by
    intro t ht
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with ht | ht
    · rw [qs1_of_nonpos ht, abs_zero]
    · rw [qs1_of_one_le ht.le, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← intervalIntegral.integral_of_le
    zero_le_one]
  have : ∫ t in (0 : ℝ)..1, |qs1 t| =
      ∫ t in (0 : ℝ)..1, (30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [abs_of_nonneg (qs1_nonneg t)]
    unfold qs1
    split_ifs with h0 h1
    · have : t = 0 := le_antisymm h0 ht.1
      subst this; norm_num
    · have : t = 1 := le_antisymm ht.2 h1
      subst this; norm_num
    · rfl
  rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5)]
  · norm_num
  · intro t _
    have := ((((hasDerivAt_pow 3 t).const_mul 10).sub ((hasDerivAt_pow 4 t).const_mul 15)).add
      ((hasDerivAt_pow 5 t).const_mul 6))
    convert this using 1; push_cast; ring
  · exact (by fun_prop : Continuous fun t : ℝ => 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4)
      |>.intervalIntegrable _ _

/-- `∫ |𝗌''| = 2 𝗌'(1/2) = 15/4`. -/
private theorem qs2_integral : ∫ t, |qs2 t| = 15 / 4 := by
  have hz : ∀ t ∉ Set.Ioc (0 : ℝ) 1, |qs2 t| = 0 := by
    intro t ht
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with ht | ht
    · rw [qs2_of_nonpos ht, abs_zero]
    · rw [qs2_of_one_le ht.le, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← intervalIntegral.integral_of_le
    zero_le_one]
  have hc : Continuous fun t => |qs2 t| := qs2_continuous.abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hQ : ∀ t, HasDerivAt (fun t : ℝ => 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4)
      (60 * t - 180 * t ^ 2 + 120 * t ^ 3) t := fun t => by
    have := ((((hasDerivAt_pow 2 t).const_mul 30).sub ((hasDerivAt_pow 3 t).const_mul 60)).add
      ((hasDerivAt_pow 4 t).const_mul 30))
    convert this using 1; push_cast; ring
  have hQc : Continuous fun t : ℝ => 60 * t - 180 * t ^ 2 + 120 * t ^ 3 := by fun_prop
  have e1 : ∫ t in (0 : ℝ)..1 / 2, |qs2 t| = ∫ t in (0 : ℝ)..1 / 2,
      (60 * t - 180 * t ^ 2 + 120 * t ^ 3) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    obtain ⟨h0, h1⟩ := ht
    have hq : qs2 t = 60 * t - 180 * t ^ 2 + 120 * t ^ 3 := by
      unfold qs2
      split_ifs with a b
      · have : t = 0 := le_antisymm a h0
        subst this; norm_num
      · linarith
      · rfl
    rw [hq, abs_of_nonneg]
    nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - t))
      (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
  have e2 : ∫ t in (1 / 2 : ℝ)..1, |qs2 t| = ∫ t in (1 / 2 : ℝ)..1,
      -(60 * t - 180 * t ^ 2 + 120 * t ^ 3) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    obtain ⟨h0, h1⟩ := ht
    have hq : qs2 t = 60 * t - 180 * t ^ 2 + 120 * t ^ 3 := by
      unfold qs2
      split_ifs with a b
      · linarith
      · have : t = 1 := le_antisymm h1 b
        subst this; norm_num
      · rfl
    rw [hq, abs_of_nonpos]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ t) (by linarith : (0 : ℝ) ≤ 1 - t))
      (by linarith : (0 : ℝ) ≤ 2 * t - 1)]
  rw [e1, e2, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t) (hQc.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hQ t) (hQc.intervalIntegrable _ _)]
  norm_num

/-- `𝔫(E) = N⁻¹ #{j : λ_j ≤ E}` for a family of reals. -/
noncomputable def countOf {N : ℕ} (lam : Fin N → ℝ) (E : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ((Finset.univ.filter fun k => lam k ≤ E).card : ℝ)

/-- `m(z) = N⁻¹ ∑_j (λ_j - z)⁻¹` for a family of reals. -/
noncomputable def stieltjesOf {N : ℕ} (lam : Fin N → ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j, 1 / ((lam j : ℂ) - z)

/-! ### The cutoff `χ(y) = 𝗌(2 - |y|)` and the window `f` of the proof of Lemma 3.16 -/

/-- `χ(y) = 𝗌(2 - y) 𝗌(2 + y)`, which equals `𝗌(2 - |y|)`. -/
private noncomputable def chiC (y : ℝ) : ℝ := quinticStep (2 - y) * quinticStep (2 + y)

private theorem qs_integrable : Integrable fun t => |qs1 t| :=
  Integrable.of_integral_ne_zero (by rw [qs1_integral]; norm_num)

private theorem qs2_integrable : Integrable fun t => |qs2 t| :=
  Integrable.of_integral_ne_zero (by rw [qs2_integral]; norm_num)

/-- Affine substitution: `∫ g((x - c)/η) dx = η ∫ g`. -/
private theorem count_subst_right (g : ℝ → ℝ) (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ x, g ((x - c) / η) = η * ∫ t, g t := by
  rw [integral_sub_right_eq_self (fun x => g (x / η)) c, Measure.integral_comp_div g η,
    abs_of_pos hη, smul_eq_mul]

/-- Affine substitution: `∫ g((c - x)/η) dx = η ∫ g`. -/
private theorem count_subst_left (g : ℝ → ℝ) (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ x, g ((c - x) / η) = η * ∫ t, g t := by
  rw [integral_sub_left_eq_self (fun x => g (x / η)) volume c, Measure.integral_comp_div g η,
    abs_of_pos hη, smul_eq_mul]

private theorem chi_hasDerivAt (y : ℝ) : HasDerivAt chiC
    (-qs1 (2 - y) * quinticStep (2 + y) + quinticStep (2 - y) * qs1 (2 + y)) y := by
  have h1 := (qs_hasDerivAt (2 - y)).comp y ((hasDerivAt_id y).const_sub 2)
  have h2 := (qs_hasDerivAt (2 + y)).comp y ((hasDerivAt_id y).const_add 2)
  exact (h1.mul h2).congr_deriv (by simp only [Function.comp_apply]; ring)

private theorem chi_contDiff : ContDiff ℝ 1 chiC :=
  ((qs_contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (qs_contDiff.comp (contDiff_const.add contDiff_id))).of_le (by norm_num)

private theorem chi_even (y : ℝ) : chiC (-y) = chiC y := by
  simp only [chiC, sub_neg_eq_add, ← sub_eq_add_neg]; ring

private theorem chi_one (y : ℝ) (h : |y| ≤ 1) : chiC y = 1 := by
  rw [abs_le] at h
  rw [chiC, qs_of_one_le (by linarith), qs_of_one_le (by linarith), mul_one]

private theorem chi_zero (y : ℝ) (h : 2 < |y|) : chiC y = 0 := by
  rcases lt_abs.1 h with h | h
  · rw [chiC, qs_of_nonpos (by linarith), zero_mul]
  · rw [chiC, qs_of_nonpos (t := 2 + y) (by linarith), mul_zero]

private theorem chi_bounds (y : ℝ) : 0 ≤ chiC y ∧ chiC y ≤ 1 := by
  obtain ⟨a0, a1⟩ := qs_bounds (2 - y)
  obtain ⟨b0, b1⟩ := qs_bounds (2 + y)
  exact ⟨mul_nonneg a0 b0, by unfold chiC; nlinarith⟩

private theorem chi_deriv_of_nonneg {y : ℝ} (hy : 0 ≤ y) : deriv chiC y = -qs1 (2 - y) := by
  rw [(chi_hasDerivAt y).deriv, qs_of_one_le (t := 2 + y) (by linarith),
    qs1_of_one_le (t := 2 + y) (by linarith)]
  ring

private theorem chi_continuous : Continuous chiC := chi_contDiff.continuous

private theorem chi_deriv_continuous : Continuous (deriv chiC) :=
  chi_contDiff.continuous_deriv le_rfl

/-- The window `f(x) = 𝗌((x - E₁ + η)/η) 𝗌((E₂ + η - x)/η)`. -/
private noncomputable def winF (E₁ E₂ η x : ℝ) : ℝ :=
  quinticStep ((x - E₁ + η) / η) * quinticStep ((E₂ + η - x) / η)

/-- `f'`. -/
private noncomputable def winF1 (E₁ E₂ η x : ℝ) : ℝ :=
  (qs1 ((x - E₁ + η) / η) * quinticStep ((E₂ + η - x) / η) -
    quinticStep ((x - E₁ + η) / η) * qs1 ((E₂ + η - x) / η)) / η

/-- `f''`. -/
private noncomputable def winF2 (E₁ E₂ η x : ℝ) : ℝ :=
  (qs2 ((x - E₁ + η) / η) * quinticStep ((E₂ + η - x) / η) -
    2 * (qs1 ((x - E₁ + η) / η) * qs1 ((E₂ + η - x) / η)) +
    quinticStep ((x - E₁ + η) / η) * qs2 ((E₂ + η - x) / η)) / η ^ 2

private theorem count_u_hasDerivAt (E₁ η x : ℝ) :
    HasDerivAt (fun x => (x - E₁ + η) / η) (1 / η) x :=
  (((hasDerivAt_id x).sub_const E₁).add_const η).div_const η

private theorem count_v_hasDerivAt (E₂ η x : ℝ) :
    HasDerivAt (fun x => (E₂ + η - x) / η) (-1 / η) x :=
  ((hasDerivAt_id x).const_sub (E₂ + η)).div_const η

private theorem winF_hasDerivAt {E₁ E₂ η : ℝ} (hη : 0 < η) (x : ℝ) :
    HasDerivAt (winF E₁ E₂ η) (winF1 E₁ E₂ η x) x := by
  have h1 := (qs_hasDerivAt _).comp x (count_u_hasDerivAt E₁ η x)
  have h2 := (qs_hasDerivAt _).comp x (count_v_hasDerivAt E₂ η x)
  refine (h1.mul h2).congr_deriv ?_
  simp only [Function.comp_apply, winF1]
  field_simp
  ring

private theorem winF1_hasDerivAt {E₁ E₂ η : ℝ} (hη : 0 < η) (x : ℝ) :
    HasDerivAt (winF1 E₁ E₂ η) (winF2 E₁ E₂ η x) x := by
  have a1 := (qs_hasDerivAt _).comp x (count_u_hasDerivAt E₁ η x)
  have a2 := (qs_hasDerivAt _).comp x (count_v_hasDerivAt E₂ η x)
  have b1 := (qs1_hasDerivAt _).comp x (count_u_hasDerivAt E₁ η x)
  have b2 := (qs1_hasDerivAt _).comp x (count_v_hasDerivAt E₂ η x)
  refine (((b1.mul a2).sub (a1.mul b2)).div_const η).congr_deriv ?_
  simp only [Function.comp_apply, winF2]
  field_simp
  ring

private theorem winF_deriv {E₁ E₂ η : ℝ} (hη : 0 < η) : deriv (winF E₁ E₂ η) = winF1 E₁ E₂ η :=
  funext fun x => (winF_hasDerivAt hη x).deriv

private theorem winF_deriv2 {E₁ E₂ η : ℝ} (hη : 0 < η) :
    deriv (deriv (winF E₁ E₂ η)) = winF2 E₁ E₂ η := by
  rw [winF_deriv hη]; exact funext fun x => (winF1_hasDerivAt hη x).deriv

private theorem winF_contDiff (E₁ E₂ η : ℝ) : ContDiff ℝ 2 (winF E₁ E₂ η) := by
  unfold winF
  exact (qs_contDiff.comp (by fun_prop)).mul (qs_contDiff.comp (by fun_prop))

private theorem winF1_continuous (E₁ E₂ η : ℝ) : Continuous (winF1 E₁ E₂ η) := by
  unfold winF1
  have := qs_continuous; have := qs1_continuous
  fun_prop

private theorem winF2_continuous (E₁ E₂ η : ℝ) : Continuous (winF2 E₁ E₂ η) := by
  unfold winF2
  have := qs_continuous; have := qs1_continuous; have := qs2_continuous
  fun_prop

/-- Outside `(E₁ - η, E₂ + η)` the window and its first two derivatives vanish. -/
private theorem winF_out {E₁ E₂ η x : ℝ} (hη : 0 < η) (hx : x ≤ E₁ - η ∨ E₂ + η ≤ x) :
    winF E₁ E₂ η x = 0 ∧ winF1 E₁ E₂ η x = 0 ∧ winF2 E₁ E₂ η x = 0 := by
  rcases hx with hx | hx
  · have hu : (x - E₁ + η) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    simp [winF, winF1, winF2, qs_of_nonpos hu, qs1_of_nonpos hu, qs2_of_nonpos hu]
  · have hv : (E₂ + η - x) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    simp [winF, winF1, winF2, qs_of_nonpos hv, qs1_of_nonpos hv, qs2_of_nonpos hv]

private theorem winF_out' {E₁ E₂ η x : ℝ} (hη : 0 < η) (hx : x ∉ Set.Icc (E₁ - η) (E₂ + η)) :
    winF E₁ E₂ η x = 0 ∧ winF1 E₁ E₂ η x = 0 ∧ winF2 E₁ E₂ η x = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  exact winF_out hη (hx.imp le_of_lt le_of_lt)

private theorem winF_bounds (E₁ E₂ η x : ℝ) : 0 ≤ winF E₁ E₂ η x ∧ winF E₁ E₂ η x ≤ 1 := by
  obtain ⟨a0, a1⟩ := qs_bounds ((x - E₁ + η) / η)
  obtain ⟨b0, b1⟩ := qs_bounds ((E₂ + η - x) / η)
  exact ⟨mul_nonneg a0 b0, by unfold winF; nlinarith⟩

private theorem winF_one {E₁ E₂ η x : ℝ} (hη : 0 < η) (hx : x ∈ Set.Icc E₁ E₂) :
    winF E₁ E₂ η x = 1 := by
  rw [winF, qs_of_one_le, qs_of_one_le, mul_one]
  · rw [le_div_iff₀ hη]; linarith [hx.2]
  · rw [le_div_iff₀ hη]; linarith [hx.1]

private theorem winF_hasCompactSupport {E₁ E₂ η : ℝ} (hη : 0 < η) :
    HasCompactSupport (winF E₁ E₂ η) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => (winF_out' hη hx).1

private theorem winF1_abs_le {E₁ E₂ η : ℝ} (hη : 0 < η) (x : ℝ) :
    |winF1 E₁ E₂ η x| ≤ |qs1 ((x - E₁ + η) / η)| / η + |qs1 ((E₂ + η - x) / η)| / η := by
  obtain ⟨a0, a1⟩ := qs_bounds ((x - E₁ + η) / η)
  obtain ⟨b0, b1⟩ := qs_bounds ((E₂ + η - x) / η)
  rw [winF1, abs_div, abs_of_pos hη, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hη.le
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg b0]; exact mul_le_of_le_one_right (abs_nonneg _) b1
  · rw [abs_mul, abs_of_nonneg a0]; exact mul_le_of_le_one_left (abs_nonneg _) a1

private theorem winF2_abs_le {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ < E₂) (x : ℝ) :
    |winF2 E₁ E₂ η x| ≤ |qs2 ((x - E₁ + η) / η)| / η ^ 2 + |qs2 ((E₂ + η - x) / η)| / η ^ 2 := by
  obtain ⟨a0, a1⟩ := qs_bounds ((x - E₁ + η) / η)
  obtain ⟨b0, b1⟩ := qs_bounds ((E₂ + η - x) / η)
  have hc : qs1 ((x - E₁ + η) / η) * qs1 ((E₂ + η - x) / η) = 0 := by
    rcases le_or_gt x E₂ with hx | hx
    · rw [qs1_of_one_le (t := (E₂ + η - x) / η) (by rw [le_div_iff₀ hη]; linarith), mul_zero]
    · rw [qs1_of_one_le (t := (x - E₁ + η) / η) (by rw [le_div_iff₀ hη]; linarith), zero_mul]
  rw [winF2, hc, mul_zero, sub_zero, abs_div, abs_of_pos (by positivity : 0 < η ^ 2), ← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg b0]; exact mul_le_of_le_one_right (abs_nonneg _) b1
  · rw [abs_mul, abs_of_nonneg a0]; exact mul_le_of_le_one_left (abs_nonneg _) a1

/-- (Tf): `∫ |f| ≤ E₂ - E₁ + 2η`. -/
private theorem winF_int_le {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ < E₂) :
    ∫ x, |winF E₁ E₂ η x| ≤ E₂ - E₁ + 2 * η := by
  have hz : ∀ x ∉ Set.Icc (E₁ - η) (E₂ + η), |winF E₁ E₂ η x| = 0 := fun x hx => by
    rw [(winF_out' hη hx).1, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (E₁ - η) (E₂ + η))
    (f := fun x => |winF E₁ E₂ η x|) (C := 1) (by simp) fun x _ => by
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg (winF_bounds E₁ E₂ η x).1]
      exact (winF_bounds E₁ E₂ η x).2
  rw [Real.volume_real_Icc_of_le (by linarith), one_mul] at this
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this.trans (by linarith))

/-- (Tf): `∫ |f'| ≤ 2`. -/
private theorem winF1_int_le {E₁ E₂ η : ℝ} (hη : 0 < η) :
    ∫ x, |winF1 E₁ E₂ η x| ≤ 2 := by
  have hi1 : Integrable fun x => |qs1 ((x - E₁ + η) / η)| / η := by
    have := (qs_integrable.comp_div hη.ne').comp_sub_right (E₁ - η)
    refine (this.div_const η).congr (Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hi2 : Integrable fun x => |qs1 ((E₂ + η - x) / η)| / η := by
    have := (qs_integrable.comp_div hη.ne').comp_sub_left (E₂ + η)
    exact this.div_const η
  calc ∫ x, |winF1 E₁ E₂ η x|
      ≤ ∫ x, (|qs1 ((x - E₁ + η) / η)| / η + |qs1 ((E₂ + η - x) / η)| / η) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hi1.add hi2)
          (Eventually.of_forall fun x => winF1_abs_le hη x)
    _ = 2 := by
        rw [integral_add hi1 hi2, integral_div, integral_div]
        have e1 := count_subst_right (fun t => |qs1 t|) (E₁ - η) hη
        have e2 := count_subst_left (fun t => |qs1 t|) (E₂ + η) hη
        rw [show (fun x => |qs1 ((x - E₁ + η) / η)|) = fun x => |qs1 ((x - (E₁ - η)) / η)| from
          funext fun x => by ring_nf]
        rw [e1, e2, qs1_integral]
        field_simp
        norm_num

/-- (Tf): `∫ |f''| ≤ 2 · (15/4) / η`. -/
private theorem winF2_int_le {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ < E₂) :
    ∫ x, |winF2 E₁ E₂ η x| ≤ 15 / (2 * η) := by
  have hi1 : Integrable fun x => |qs2 ((x - (E₁ - η)) / η)| / η ^ 2 :=
    ((qs2_integrable.comp_div hη.ne').comp_sub_right (E₁ - η)).div_const _
  have hi2 : Integrable fun x => |qs2 ((E₂ + η - x) / η)| / η ^ 2 :=
    ((qs2_integrable.comp_div hη.ne').comp_sub_left (E₂ + η)).div_const _
  calc ∫ x, |winF2 E₁ E₂ η x|
      ≤ ∫ x, (|qs2 ((x - (E₁ - η)) / η)| / η ^ 2 + |qs2 ((E₂ + η - x) / η)| / η ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hi1.add hi2)
          (Eventually.of_forall fun x => by
            have := winF2_abs_le hη hE x
            rwa [show x - E₁ + η = x - (E₁ - η) by ring] at this)
    _ = 15 / (2 * η) := by
        rw [integral_add hi1 hi2, integral_div, integral_div,
          count_subst_right (fun t => |qs2 t|) (E₁ - η) hη,
          count_subst_left (fun t => |qs2 t|) (E₂ + η) hη, qs2_integral]
        field_simp
        norm_num

/-! ### The Helffer–Sjöstrand formula on the upper half-plane -/

/-- `f(λ) = π⁻¹ ∫_{y > 0} Re [g(x, y) / (λ - x - i y)] dx dy`: Lemma 3.15 together with
`g(x, -y) = conj g(x, y)`. -/
private theorem count_hs_half {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hχ : ContDiff ℝ 1 χ) (hχe : ∀ y, χ (-y) = χ y) (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1)
    (hχ0 : ∀ y, 2 < |y| → χ y = 0) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (lam : ℝ) :
    f lam = π⁻¹ * ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2)).re) p := by
  obtain ⟨hK, hfl⟩ := helfferSjostrand hf hfc hχ hχe hχ1 hχ0 hχb lam
  obtain ⟨-, -, hconj⟩ := hsG_bound hf hfc hχ hχe hχ1 hχ0 hχb
  set K : ℝ × ℝ → ℂ := fun p => hsG f χ p.1 p.2 / ((lam : ℂ) - p.1 - Complex.I * p.2) with hKdef
  have hd0 : deriv χ 0 = 0 := by
    have : χ =ᶠ[𝓝 0] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with y hy
      exact hχ1 y (abs_le.2 ⟨hy.1.le, hy.2.le⟩)
    rw [this.deriv_eq, deriv_const]
  have hK0 : ∀ x, K (x, 0) = 0 := fun x => by simp [hKdef, hsG, hd0]
  have hKneg : ∀ x y, K (x, -y) = starRingEnd ℂ (K (x, y)) := fun x y => by
    simp only [hKdef]
    rw [hconj, map_div₀]
    congr 1
    simp only [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I]
    push_cast; ring
  have hR : Integrable fun p => (K p).re := hK.re
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  have hT : MeasurableSet {p : ℝ × ℝ | p.2 < 0} := measurableSet_lt measurable_snd measurable_const
  have hsplit : ∫ p, (K p).re = (∫ p, Set.indicator {p : ℝ × ℝ | 0 < p.2} (fun p => (K p).re) p) +
      ∫ p, Set.indicator {p : ℝ × ℝ | p.2 < 0} (fun p => (K p).re) p := by
    rw [← integral_add (hR.indicator hS) (hR.indicator hT)]
    congr 1; funext p
    obtain ⟨x, y⟩ := p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rcases lt_trichotomy y 0 with h | rfl | h
    · simp [h, h.not_gt]
    · simp [hK0]
    · simp [h, h.not_gt]
  have hrefl : ∫ p, Set.indicator {p : ℝ × ℝ | p.2 < 0} (fun p => (K p).re) p =
      ∫ p, Set.indicator {p : ℝ × ℝ | 0 < p.2} (fun p => (K p).re) p := by
    have h1 := hR.indicator hT
    have h2 := hR.indicator hS
    rw [Measure.volume_eq_prod] at h1 h2 ⊢
    rw [integral_prod _ h1, integral_prod _ h2]
    congr 1; funext x
    rw [← integral_neg_eq_self]
    congr 1; funext y
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, neg_lt_zero, hKneg, Complex.conj_re]
  have hre := congrArg Complex.re hfl
  rw [show (2 * π : ℂ)⁻¹ = (((2 * π)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
    Complex.ofReal_re] at hre
  rw [hre, show (∫ p, K p).re = ∫ p, (K p).re from (integral_re hK).symm, hsplit, hrefl]
  ring

private theorem count_reg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous f ∧ Continuous (deriv f) ∧ Continuous (deriv (deriv f)) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).1 hf
  exact ⟨hf.continuous, h.2.2.continuous, h.2.2.continuous_deriv le_rfl⟩

private theorem count_hsG_continuous {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ) :
    Continuous fun p : ℝ × ℝ => hsG f χ p.1 p.2 := by
  obtain ⟨h0, h1, h2⟩ := count_reg hf
  have h3 : Continuous χ := hχ.continuous
  have h4 : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  unfold hsG
  fun_prop

private theorem count_den (lam x y : ℝ) :
    (lam : ℂ) - x - Complex.I * y = (lam : ℂ) - (x + y * Complex.I) := by ring

private theorem rhoSc_eq_zero {x : ℝ} (hx : x ∉ Set.Ioo (-2 : ℝ) 2) : rhoSc x = 0 := by
  obtain ⟨-, -, hb, hpos, -⟩ := rhoSc_props
  exact le_antisymm (not_lt.1 fun h => hx ((hpos x).1 h)) (hb x).1

private theorem rhoSc_integrable : Integrable rhoSc :=
  rhoSc_props.1.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc
    (a := -2) (b := 2)) fun _ hx => rhoSc_eq_zero fun h => hx (Set.Ioo_subset_Icc_self h))

/-- Lemma 3.3 written as an integral over `ℝ`. -/
private theorem count_msc_integral {z : ℂ} (hz : 0 < z.im) :
    ∫ x : ℝ, (rhoSc x : ℂ) / ((x : ℂ) - z) = msc z := by
  rw [msc_eq_integral hz, intervalIntegral.integral_of_le (by norm_num),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [rhoSc_eq_zero fun h => hx (Set.Ioo_subset_Ioc_self h), Complex.ofReal_zero, zero_div]

private theorem count_cauchy_integrable {z : ℂ} (hz : 0 < z.im) :
    Integrable fun x : ℝ => (rhoSc x : ℂ) / ((x : ℂ) - z) := by
  have hne : ∀ x : ℝ, (x : ℂ) - z ≠ 0 := fun x h => by
    have := congrArg Complex.im h
    simp at this; linarith
  refine Continuous.integrable_of_hasCompactSupport
    ((Complex.continuous_ofReal.comp rhoSc_props.1).div (by fun_prop) hne)
    (HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun x hx => ?_)
  simp [rhoSc_eq_zero fun h => hx (Set.Ioo_subset_Icc_self h)]

/-- Averaging the half-plane formula over the `λ_j`. -/
private theorem count_avg {N : ℕ} (lam : Fin N → ℝ) {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hχ : ContDiff ℝ 1 χ) (hχe : ∀ y, χ (-y) = χ y)
    (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1) (hχ0 : ∀ y, 2 < |y| → χ y = 0)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * stieltjesOf lam (p.1 + p.2 * Complex.I)).re) p) ∧
    (N : ℝ)⁻¹ * ∑ j, f (lam j) = π⁻¹ * ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * stieltjesOf lam (p.1 + p.2 * Complex.I)).re) p := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  set R : ℝ → ℝ × ℝ → ℝ := fun l => Set.indicator {p : ℝ × ℝ | 0 < p.2}
    (fun p => (hsG f χ p.1 p.2 / ((l : ℂ) - p.1 - Complex.I * p.2)).re) with hRdef
  have hRi : ∀ l, Integrable (R l) := fun l =>
    (helfferSjostrand hf hfc hχ hχe hχ1 hχ0 hχb l).1.re.indicator hS
  have key : (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * stieltjesOf lam (p.1 + p.2 * Complex.I)).re) p) =
      fun p => ∑ j, (N : ℝ)⁻¹ * R (lam j) p := by
    funext p
    simp only [hRdef, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs
    · simp only [stieltjesOf, Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.re_ofReal_mul, count_den]
      congr 1
      push_cast
      ring
    · simp
  rw [key]
  refine ⟨integrable_finsetSum _ fun j _ => (hRi (lam j)).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun j _ => (hRi (lam j)).const_mul _, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, count_hs_half hf hfc hχ hχe hχ1 hχ0 hχb (lam j)]
  ring

/-- Integrating the half-plane formula against `ρ_sc` (Fubini, dominated by `Γ ρ_sc`). -/
private theorem count_sc {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hχ : ContDiff ℝ 1 χ) (hχe : ∀ y, χ (-y) = χ y)
    (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1) (hχ0 : ∀ y, 2 < |y| → χ y = 0)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * msc (p.1 + p.2 * Complex.I)).re) p) ∧
    ∫ l, f l * rhoSc l = π⁻¹ * ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * msc (p.1 + p.2 * Complex.I)).re) p := by
  obtain ⟨hΓb, hΓi, -⟩ := hsG_bound hf hfc hχ hχe hχ1 hχ0 hχb
  set F : ℝ × (ℝ × ℝ) → ℝ := fun q => rhoSc q.1 * Set.indicator {q : ℝ × (ℝ × ℝ) | 0 < q.2.2}
    (fun q => (hsG f χ q.2.1 q.2.2 / ((q.1 : ℂ) - q.2.1 - Complex.I * q.2.2)).re) q with hFdef
  have hFm : Measurable F := by
    refine (rhoSc_props.1.measurable.comp measurable_fst).mul (Measurable.indicator ?_ ?_)
    · exact Complex.measurable_re.comp
        (((count_hsG_continuous hf hχ).measurable.comp measurable_snd).div (by fun_prop))
    · exact measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)
  have hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    refine (rhoSc_integrable.mul_prod hΓi).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    obtain ⟨l, x, y⟩ := q
    have hρ := (rhoSc_props.2.2.1 l).1
    have hΓ0 : 0 ≤ |deriv (deriv f) x| * Set.indicator {y : ℝ | |y| ≤ 2} 1 y +
        |deriv χ y| * (|f x| + 2 * |deriv f x|) :=
      add_nonneg (mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (mul_nonneg (abs_nonneg _) (by positivity))
    simp only [hFdef]
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (show (l, x, y) ∈ {q : ℝ × (ℝ × ℝ) | 0 < q.2.2} from hy),
        norm_mul, Real.norm_of_nonneg hρ]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hΓb l x y hy.ne')) hρ
    · rw [Set.indicator_of_notMem (show (l, x, y) ∉ {q : ℝ × (ℝ × ℝ) | 0 < q.2.2} from hy),
        mul_zero, norm_zero]
      exact mul_nonneg hρ hΓ0
  have hin : ∀ p : ℝ × ℝ, ∫ l, F (l, p) = Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * msc (p.1 + p.2 * Complex.I)).re) p := by
    rintro ⟨x, y⟩
    simp only [hFdef, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hy
    · have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
      have e : ∀ l : ℝ, rhoSc l * (hsG f χ x y / ((l : ℂ) - x - Complex.I * y)).re =
          (hsG f χ x y * ((rhoSc l : ℂ) / ((l : ℂ) - (x + y * Complex.I)))).re := fun l => by
        rw [← Complex.re_ofReal_mul, count_den]
        congr 1
        ring
      simp only [e]
      have hre : ∫ l : ℝ, (hsG f χ x y * ((rhoSc l : ℂ) / ((l : ℂ) - (x + y * Complex.I)))).re =
          (∫ l : ℝ, hsG f χ x y * ((rhoSc l : ℂ) / ((l : ℂ) - (x + y * Complex.I)))).re :=
        integral_re ((count_cauchy_integrable hz).const_mul _)
      rw [hre, integral_const_mul, count_msc_integral hz]
    · simp
  refine ⟨hF.integral_prod_right.congr (Eventually.of_forall hin), ?_⟩
  have e1 : ∀ l, f l * rhoSc l = π⁻¹ * ∫ p, F (l, p) := fun l => by
    simp only [hFdef]
    rw [integral_const_mul, count_hs_half hf hfc hχ hχe hχ1 hχ0 hχb l]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    ring
  simp only [e1]
  rw [integral_const_mul, integral_integral_swap (f := fun l p => F (l, p)) hF]
  simp only [hin]

/-- Step 1 of the proof of Lemma 3.16: `D = π⁻¹ ∫_{y > 0} Re [g Δ]` with `Δ = m - m_sc`. -/
private theorem count_D {N : ℕ} (lam : Fin N → ℝ) {f χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hχ : ContDiff ℝ 1 χ) (hχe : ∀ y, χ (-y) = χ y)
    (hχ1 : ∀ y, |y| ≤ 1 → χ y = 1) (hχ0 : ∀ y, 2 < |y| → χ y = 0)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * (stieltjesOf lam (p.1 + p.2 * Complex.I) -
        msc (p.1 + p.2 * Complex.I))).re) p) ∧
    (N : ℝ)⁻¹ * ∑ j, f (lam j) - ∫ l, f l * rhoSc l =
      π⁻¹ * ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2}
        (fun p => (hsG f χ p.1 p.2 * (stieltjesOf lam (p.1 + p.2 * Complex.I) -
          msc (p.1 + p.2 * Complex.I))).re) p := by
  obtain ⟨hBi, hB⟩ := count_avg lam hf hfc hχ hχe hχ1 hχ0 hχb
  obtain ⟨hCi, hC⟩ := count_sc hf hfc hχ hχe hχ1 hχ0 hχb
  have e : (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG f χ p.1 p.2 * (stieltjesOf lam (p.1 + p.2 * Complex.I) -
        msc (p.1 + p.2 * Complex.I))).re) p) = fun p =>
      Set.indicator {p : ℝ × ℝ | 0 < p.2}
        (fun p => (hsG f χ p.1 p.2 * stieltjesOf lam (p.1 + p.2 * Complex.I)).re) p -
      Set.indicator {p : ℝ × ℝ | 0 < p.2}
        (fun p => (hsG f χ p.1 p.2 * msc (p.1 + p.2 * Complex.I)).re) p := by
    funext p
    simp only [Set.indicator_apply]
    split_ifs
    · simp only [mul_sub, Complex.sub_re]
    · simp
  rw [e]
  refine ⟨hBi.sub hCi, ?_⟩
  rw [integral_sub hBi hCi, hB, hC]
  ring

/-- `Re [g(x, y) w] = -y f'' χ Im w - χ' (f Im w + y f' Re w)`. -/
private theorem count_re_hsG (f χ : ℝ → ℝ) (x y : ℝ) (w : ℂ) :
    (hsG f χ x y * w).re = -(y * deriv (deriv f) x * χ y * w.im) -
      deriv χ y * (f x * w.im + y * deriv f x * w.re) := by
  simp only [hsG, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `Im m(x + i y) = N⁻¹ ∑_j y / ((λ_j - x)² + y²)`. -/
private theorem count_im_stieltjes {N : ℕ} (lam : Fin N → ℝ) (x y : ℝ) :
    (stieltjesOf lam (x + y * Complex.I)).im =
      (N : ℝ)⁻¹ * ∑ j, y / ((lam j - x) ^ 2 + y ^ 2) := by
  rw [stieltjesOf, show (N : ℂ)⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf

/-! ### Specialization to the window `f` and the cutoff `χ` -/

/-- The hypothesis (3.11) of Lemma 3.16. -/
private def BoxBound {N : ℕ} (lam : Fin N → ℝ) (E₁ E₂ η U : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (E₁ - η) (E₂ + η), ∀ y ∈ Set.Icc η 2,
    ‖stieltjesOf lam (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ U / (N * y)

/-- `Δ(x + i y) = m(x + i y) - m_sc(x + i y)`. -/
private noncomputable def dl {N : ℕ} (lam : Fin N → ℝ) (x y : ℝ) : ℂ :=
  stieltjesOf lam (x + y * Complex.I) - msc (x + y * Complex.I)

private theorem stieltjesOf_differentiableAt {N : ℕ} (lam : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (stieltjesOf lam) z := by
  have hne : ∀ j, (lam j : ℂ) - z ≠ 0 := fun j h => by
    have := congrArg Complex.im h
    simp at this; linarith
  unfold stieltjesOf
  refine (differentiableAt_const _).mul ?_
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact (differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id)
    (hne j)

private theorem msc_differentiableAt {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ msc z :=
  differentiableOn_msc.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)

private theorem dl_continuousOn {N : ℕ} (lam : Fin N → ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => dl lam p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  have hz : 0 < ((p.1 : ℂ) + p.2 * Complex.I).im := by simpa using hp
  have h1 : ContinuousAt (fun w => stieltjesOf lam w - msc w) ((p.1 : ℂ) + p.2 * Complex.I) :=
    ((stieltjesOf_differentiableAt lam hz).sub (msc_differentiableAt hz)).continuousAt
  exact (h1.comp (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I)
    (by fun_prop)).continuousWithinAt

private theorem count_pos_im {x y : ℝ} (hy : 0 < y) : 0 < ((x : ℂ) + y * Complex.I).im := by
  simpa using hy

/-- Step 3 of the proof of Lemma 3.16: `y |Im Δ(x + i y)| ≤ 2η + U/N` for `0 < y ≤ η`. -/
private theorem count_small_y {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (h : BoxBound lam E₁ E₂ η U) {x y : ℝ}
    (hx : x ∈ Set.Icc (E₁ - η) (E₂ + η)) (hy : 0 < y) (hyη : y ≤ η) :
    y * |(dl lam x y).im| ≤ 2 * η + U / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : y * (stieltjesOf lam (x + y * Complex.I)).im ≤
      η * (stieltjesOf lam (x + η * Complex.I)).im := by
    rw [count_im_stieltjes, count_im_stieltjes]
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have t : y * (y / ((lam j - x) ^ 2 + y ^ 2)) ≤ η * (η / ((lam j - x) ^ 2 + η ^ 2)) := by
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : y * y ≤ η * η := mul_self_le_mul_self hy.le hyη
      nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg (lam j - x))]
    have := mul_le_mul_of_nonneg_left t (inv_nonneg.2 hNR.le)
    calc _ = (N : ℝ)⁻¹ * (y * (y / ((lam j - x) ^ 2 + y ^ 2))) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hmpos : 0 ≤ (stieltjesOf lam (x + y * Complex.I)).im := by
    rw [count_im_stieltjes]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity)
  have hsc := msc_im_pos (count_pos_im (x := x) hy)
  have hsc1 : (msc (x + y * Complex.I)).im ≤ 1 :=
    (Complex.im_le_norm _).trans (msc_bounds (count_pos_im (x := x) hy)).2.1
  have hη1 : (stieltjesOf lam (x + η * Complex.I)).im ≤ 1 + U / (N * η) := by
    have hb := h x hx η ⟨le_rfl, hη2⟩
    have e : (stieltjesOf lam (x + η * Complex.I)).im = (msc (x + η * Complex.I)).im +
        (stieltjesOf lam (x + η * Complex.I) - msc (x + η * Complex.I)).im := by
      rw [Complex.sub_im]; ring
    rw [e]
    exact add_le_add ((Complex.im_le_norm _).trans (msc_bounds (count_pos_im (x := x) hη)).2.1)
      ((Complex.im_le_norm _).trans hb)
  have habs : |(dl lam x y).im| ≤ (stieltjesOf lam (x + y * Complex.I)).im +
      (msc (x + y * Complex.I)).im := by
    rw [dl, Complex.sub_im, abs_le]; constructor <;> linarith
  calc y * |(dl lam x y).im|
      ≤ y * (stieltjesOf lam (x + y * Complex.I)).im + y * (msc (x + y * Complex.I)).im := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left habs hy.le
    _ ≤ η * (1 + U / (N * η)) + η := by
        refine add_le_add (hmono.trans (mul_le_mul_of_nonneg_left hη1 hη.le)) ?_
        nlinarith
    _ = 2 * η + U / N := by field_simp; ring

/-- `|f(t) - 𝟙(E₁ < t ≤ E₂)| ≤ 𝟙_{[E₁ - η, E₁]}(t) + 𝟙_{[E₂, E₂ + η]}(t)`. -/
private theorem winF_step {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ < E₂) (t : ℝ) :
    |winF E₁ E₂ η t - ((if t ≤ E₂ then 1 else 0) - (if t ≤ E₁ then 1 else 0))| ≤
      Set.indicator (Set.Icc (E₁ - η) E₁) 1 t + Set.indicator (Set.Icc E₂ (E₂ + η)) 1 t := by
  have h0 : 0 ≤ Set.indicator (Set.Icc (E₁ - η) E₁) (1 : ℝ → ℝ) t :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have h0' : 0 ≤ Set.indicator (Set.Icc E₂ (E₂ + η)) (1 : ℝ → ℝ) t :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  obtain ⟨f0, f1⟩ := winF_bounds E₁ E₂ η t
  rcases le_or_gt t E₁ with h1 | h1
  · rw [ite_eq_left (h1.trans hE.le), ite_eq_left h1, sub_self, sub_zero, abs_of_nonneg f0]
    rcases le_or_gt t (E₁ - η) with h2 | h2
    · rw [(winF_out hη (Or.inl h2)).1]; positivity
    · rw [Set.indicator_of_mem (show t ∈ Set.Icc (E₁ - η) E₁ from ⟨h2.le, h1⟩), Pi.one_apply]
      linarith
  rcases le_or_gt t E₂ with h3 | h3
  · rw [ite_eq_left h3, ite_eq_right (not_le.2 h1), winF_one hη ⟨h1.le, h3⟩]; norm_num; positivity
  · rw [ite_eq_right (not_le.2 h3), ite_eq_right (not_le.2 h1), sub_self, sub_zero,
      abs_of_nonneg f0]
    rcases le_or_gt (E₂ + η) t with h4 | h4
    · rw [(winF_out hη (Or.inr h4)).1]; positivity
    · rw [Set.indicator_of_mem (show t ∈ Set.Icc E₂ (E₂ + η) from ⟨h3.le, h4.le⟩), Pi.one_apply]
      linarith

/-- `Im m(x + iη) ≤ 1 + U/(Nη)` on the box. -/
private theorem count_im_le {N : ℕ} (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ} (hη : 0 < η) (hη2 : η ≤ 2)
    (h : BoxBound lam E₁ E₂ η U) {x : ℝ} (hx : x ∈ Set.Icc (E₁ - η) (E₂ + η)) :
    (stieltjesOf lam (x + η * Complex.I)).im ≤ 1 + U / (N * η) := by
  have hb := h x hx η ⟨le_rfl, hη2⟩
  have e : (stieltjesOf lam (x + η * Complex.I)).im = (msc (x + η * Complex.I)).im +
      (stieltjesOf lam (x + η * Complex.I) - msc (x + η * Complex.I)).im := by
    rw [Complex.sub_im]; ring
  rw [e]
  exact add_le_add ((Complex.im_le_norm _).trans (msc_bounds (count_pos_im (x := x) hη)).2.1)
    ((Complex.im_le_norm _).trans hb)

private theorem count_ind_le {s : Set ℝ} {E η t : ℝ} (hη : 0 < η)
    (hs : ∀ t ∈ s, |t - E| ≤ η) : s.indicator 1 t ≤ 2 * η * (η / ((t - E) ^ 2 + η ^ 2)) := by
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Pi.one_apply, mul_div_assoc', le_div_iff₀ (by positivity)]
    have h1 := hs t ht
    have h2 : (t - E) ^ 2 ≤ η ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith
  · rw [Set.indicator_of_notMem ht]; positivity

private theorem countOf_eq_sum {N : ℕ} (lam : Fin N → ℝ) (E : ℝ) :
    countOf lam E = (N : ℝ)⁻¹ * ∑ j, (if lam j ≤ E then (1 : ℝ) else 0) := by
  rw [countOf, Finset.card_filter]
  push_cast
  rfl

/-- Step 6 of the proof of Lemma 3.16, eigenvalue side. -/
private theorem count_step6 {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ}
    (hE : E₁ < E₂) (hη : 0 < η) (hη2 : η ≤ 2) (h : BoxBound lam E₁ E₂ η U) :
    |(N : ℝ)⁻¹ * ∑ j, winF E₁ E₂ η (lam j) - (countOf lam E₂ - countOf lam E₁)| ≤
      4 * η + 4 * U / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∀ E ∈ Set.Icc (E₁ - η) (E₂ + η), (N : ℝ)⁻¹ * ∑ j,
      2 * η * (η / ((lam j - E) ^ 2 + η ^ 2)) ≤ 2 * η + 2 * U / N := fun E hE' => by
    have := count_im_le lam hη hη2 h hE'
    rw [count_im_stieltjes] at this
    calc (N : ℝ)⁻¹ * ∑ j, 2 * η * (η / ((lam j - E) ^ 2 + η ^ 2))
        = 2 * η * ((N : ℝ)⁻¹ * ∑ j, η / ((lam j - E) ^ 2 + η ^ 2)) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 * η * (1 + U / (N * η)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * η + 2 * U / N := by field_simp
  have e : (N : ℝ)⁻¹ * ∑ j, winF E₁ E₂ η (lam j) - (countOf lam E₂ - countOf lam E₁) =
      (N : ℝ)⁻¹ * ∑ j, (winF E₁ E₂ η (lam j) -
        ((if lam j ≤ E₂ then 1 else 0) - (if lam j ≤ E₁ then 1 else 0))) := by
    rw [countOf_eq_sum, countOf_eq_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hNR)]
  calc (N : ℝ)⁻¹ * |∑ j, (winF E₁ E₂ η (lam j) -
        ((if lam j ≤ E₂ then 1 else 0) - (if lam j ≤ E₁ then 1 else 0)))|
      ≤ (N : ℝ)⁻¹ * ∑ j, (2 * η * (η / ((lam j - E₁) ^ 2 + η ^ 2)) +
          2 * η * (η / ((lam j - E₂) ^ 2 + η ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => (winF_step hη hE (lam j)).trans (add_le_add ?_ ?_)))
          (inv_nonneg.2 hNR.le)
        · exact count_ind_le hη fun t ht => abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · exact count_ind_le hη fun t ht => abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    _ ≤ 4 * η + 4 * U / N := by
        rw [Finset.sum_add_distrib, mul_add]
        have h1 := hsum E₁ ⟨by linarith, by linarith⟩
        have h2 := hsum E₂ ⟨by linarith, by linarith⟩
        refine (add_le_add h1 h2).trans (le_of_eq ?_)
        ring

private theorem rhoSc_hasCompactSupport : HasCompactSupport rhoSc :=
  HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun _ hx =>
    rhoSc_eq_zero fun h => hx (Set.Ioo_subset_Icc_self h)

private theorem nsc_eq_integral (E : ℝ) :
    nsc E = ∫ l, (if l ≤ E then (1 : ℝ) else 0) * rhoSc l := by
  rw [nsc, ← integral_indicator measurableSet_Iic]
  congr 1; funext l
  simp only [Set.indicator_apply, Set.mem_Iic]
  split_ifs <;> simp

private theorem count_ind_integrable (a b : ℝ) :
    Integrable (Set.indicator (Set.Icc a b) (1 : ℝ → ℝ)) :=
  (integrableOn_const (C := (1 : ℝ)) (by simp)).integrable_indicator measurableSet_Icc

/-- Step 6 of the proof of Lemma 3.16, semicircle side. -/
private theorem count_step6_sc {E₁ E₂ η : ℝ} (hE : E₁ < E₂) (hη : 0 < η) :
    |(∫ l, winF E₁ E₂ η l * rhoSc l) - (nsc E₂ - nsc E₁)| ≤ 2 * η / π := by
  have hstep : ∀ E, Integrable fun l => (if l ≤ E then (1 : ℝ) else 0) * rhoSc l := fun E => by
    refine (rhoSc_integrable.indicator (measurableSet_Iic (a := E))).congr
      (Eventually.of_forall fun l => ?_)
    simp only [Set.indicator_apply, Set.mem_Iic]
    split_ifs <;> simp
  have hfρ : Integrable fun l => winF E₁ E₂ η l * rhoSc l :=
    ((winF_contDiff E₁ E₂ η).continuous.mul rhoSc_props.1).integrable_of_hasCompactSupport
      rhoSc_hasCompactSupport.mul_left
  have hd : Integrable fun l => (if l ≤ E₂ then (1 : ℝ) else 0) * rhoSc l -
      (if l ≤ E₁ then (1 : ℝ) else 0) * rhoSc l := (hstep E₂).sub (hstep E₁)
  rw [nsc_eq_integral, nsc_eq_integral, ← integral_sub (hstep E₂) (hstep E₁),
    ← integral_sub hfρ hd]
  have hg := ((count_ind_integrable (E₁ - η) E₁).add
    (count_ind_integrable E₂ (E₂ + η))).const_mul π⁻¹
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun l => ?_)).trans ?_
  · obtain ⟨-, -, hb, -, -⟩ := rhoSc_props
    rw [Real.norm_eq_abs, ← sub_mul, ← sub_mul, abs_mul, abs_of_nonneg (hb l).1]
    have := winF_step hη hE l
    calc _ ≤ (Set.indicator (Set.Icc (E₁ - η) E₁) 1 l + Set.indicator (Set.Icc E₂ (E₂ + η)) 1 l) *
          (1 / π) := mul_le_mul this (hb l).2 (hb l).1
            (add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
              (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
      _ = _ := by simp only [Pi.add_apply]; ring
  · rw [integral_const_mul, Pi.add_def,
      integral_add (count_ind_integrable _ _) (count_ind_integrable _ _),
      integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)]
    apply le_of_eq; ring

private theorem dl_differentiableAt {N : ℕ} (lam : Fin N → ℝ) {p : ℝ × ℝ} (hp : 0 < p.2) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => dl lam p.1 p.2) p := by
  have hz := count_pos_im (x := p.1) hp
  have hw : DifferentiableAt ℂ (fun w => stieltjesOf lam w - msc w) (p.1 + p.2 * Complex.I) :=
    (stieltjesOf_differentiableAt lam hz).sub (msc_differentiableAt hz)
  exact (hw.restrictScalars ℝ).comp p (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I)
    (by fun_prop)

/-- `x ↦ Δ(x + i y)` has derivative `Δ'(x + i y)`. -/
private theorem dl_hasDerivAt_x {N : ℕ} (lam : Fin N → ℝ) {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => dl lam x y)
      (deriv (fun w => stieltjesOf lam w - msc w) (x + y * Complex.I)) x := by
  have hz := count_pos_im (x := x) hy
  have hw : DifferentiableAt ℂ (fun w => stieltjesOf lam w - msc w) (x + y * Complex.I) :=
    (stieltjesOf_differentiableAt lam hz).sub (msc_differentiableAt hz)
  have hi : HasDerivAt (fun x : ℝ => (x : ℂ) + y * Complex.I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * Complex.I)
  have := hw.hasDerivAt.comp x hi
  rw [mul_one] at this
  exact this

/-- `y ↦ Δ(x + i y)` has derivative `i Δ'(x + i y)`. -/
private theorem dl_hasDerivAt_y {N : ℕ} (lam : Fin N → ℝ) {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => dl lam x y)
      (deriv (fun w => stieltjesOf lam w - msc w) (x + y * Complex.I) * Complex.I) y := by
  have hz := count_pos_im (x := x) hy
  have hw : DifferentiableAt ℂ (fun w => stieltjesOf lam w - msc w) (x + y * Complex.I) :=
    (stieltjesOf_differentiableAt lam hz).sub (msc_differentiableAt hz)
  have hi : HasDerivAt (fun y : ℝ => (x : ℂ) + y * Complex.I) Complex.I y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)
  exact hw.hasDerivAt.comp y hi

private theorem chi_hasDerivAt' (y : ℝ) : HasDerivAt chiC (deriv chiC y) y :=
  ((chi_contDiff.differentiable one_ne_zero) y).hasDerivAt

private theorem winF1_differentiable {E₁ E₂ η : ℝ} (hη : 0 < η) :
    Differentiable ℝ (winF1 E₁ E₂ η) := fun x => (winF1_hasDerivAt hη x).differentiableAt

private theorem chi_differentiable : Differentiable ℝ chiC :=
  chi_contDiff.differentiable one_ne_zero

/-- The divergence theorem on `[E₁ - η, E₂ + η] × [η, 2]` for the field
`(-i y χ f' Δ, y χ f' Δ)` (Step 4 of the proof of Lemma 3.16; the Cauchy–Riemann equations make
the `Δ'` terms cancel). -/
private theorem count_div {N : ℕ} (lam : Fin N → ℝ) {E₁ E₂ η : ℝ} (hE : E₁ < E₂) (hη : 0 < η)
    (hη' : η ≤ 1 / 2) :
    ∫ p in Set.Icc ((E₁ - η, η) : ℝ × ℝ) (E₂ + η, 2),
      (-Complex.I * ((p.2 * chiC p.2 * winF2 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 +
        (((chiC p.2 + p.2 * deriv chiC p.2) * winF1 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2) =
      -∫ x in (E₁ - η)..(E₂ + η), ((η * winF1 E₁ E₂ η x : ℝ) : ℂ) * dl lam x η := by
  set Fc : ℝ × ℝ → ℂ := fun p =>
    -Complex.I * (((p.2 * chiC p.2 * winF1 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2) with hFc
  set Gc : ℝ × ℝ → ℂ := fun p =>
    ((p.2 * chiC p.2 * winF1 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 with hGc
  have hd1 := winF1_differentiable (E₁ := E₁) (E₂ := E₂) hη
  have hd2 := chi_differentiable
  have hFd : ∀ p : ℝ × ℝ, 0 < p.2 → DifferentiableAt ℝ Fc p := fun p hp => by
    have := dl_differentiableAt lam hp
    simp only [hFc]
    fun_prop
  have hGd : ∀ p : ℝ × ℝ, 0 < p.2 → DifferentiableAt ℝ Gc p := fun p hp => by
    have := dl_differentiableAt lam hp
    simp only [hGc]
    fun_prop
  have hpos : ∀ p ∈ Set.Icc ((E₁ - η, η) : ℝ × ℝ) (E₂ + η, 2), 0 < p.2 :=
    fun p hp => lt_of_lt_of_le hη hp.1.2
  have hdiv : ∀ p : ℝ × ℝ, 0 < p.2 → fderiv ℝ Fc p (1, 0) + fderiv ℝ Gc p (0, 1) =
      -Complex.I * ((p.2 * chiC p.2 * winF2 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 +
        (((chiC p.2 + p.2 * deriv chiC p.2) * winF1 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 := by
    rintro ⟨x, y⟩ hy
    simp only at hy ⊢
    have hx := (hFd (x, y) hy).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    have hy' := (hGd (x, y) hy).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    have ex : HasDerivAt (fun x => Fc (x, y)) (-Complex.I *
        (((y * chiC y * winF2 E₁ E₂ η x : ℝ) : ℂ) * dl lam x y +
          ((y * chiC y * winF1 E₁ E₂ η x : ℝ) : ℂ) *
            deriv (fun w => stieltjesOf lam w - msc w) (x + y * Complex.I))) x := by
      have h0 := ((((winF1_hasDerivAt (E₁ := E₁) (E₂ := E₂) hη x).const_mul
        (y * chiC y)).ofReal_comp).mul (dl_hasDerivAt_x lam hy)).const_mul (-Complex.I)
      refine h0.congr_deriv ?_
      push_cast; ring
    have ey : HasDerivAt (fun y => Gc (x, y))
        ((((chiC y + y * deriv chiC y) * winF1 E₁ E₂ η x : ℝ) : ℂ) * dl lam x y +
          ((y * chiC y * winF1 E₁ E₂ η x : ℝ) : ℂ) *
            (deriv (fun w => stieltjesOf lam w - msc w) (x + y * Complex.I) * Complex.I)) y := by
      have h0 := ((((hasDerivAt_id' y).mul (chi_hasDerivAt' y)).mul_const
        (winF1 E₁ E₂ η x)).ofReal_comp).mul (dl_hasDerivAt_y lam (x := x) hy)
      refine h0.congr_deriv ?_
      simp only [Pi.mul_apply]
      push_cast; ring
    have e1 : fderiv ℝ Fc (x, y) (1, 0) = _ := hx.unique ex
    have e2 : fderiv ℝ Gc (x, y) (0, 1) = _ := hy'.unique ey
    rw [e1, e2]
    ring
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      -Complex.I * ((p.2 * chiC p.2 * winF2 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 +
        (((chiC p.2 + p.2 * deriv chiC p.2) * winF1 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2)
      (Set.Icc ((E₁ - η, η) : ℝ × ℝ) (E₂ + η, 2)) := by
    have hdl := (dl_continuousOn lam).mono fun p hp => hpos p hp
    have c1 := winF1_continuous E₁ E₂ η
    have c2 := winF2_continuous E₁ E₂ η
    have c3 := chi_continuous
    have c4 := chi_deriv_continuous
    refine ContinuousOn.add (ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) hdl)
      (ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) hdl)
  have hle : ((E₁ - η, η) : ℝ × ℝ) ≤ (E₂ + η, 2) := ⟨by simp; linarith, by simp; linarith⟩
  have key := integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le Fc Gc
    (fderiv ℝ Fc) (fderiv ℝ Gc) _ _ hle ∅ Set.countable_empty
    (fun p hp => (hFd p (hpos p hp)).continuousAt.continuousWithinAt)
    (fun p hp => (hGd p (hpos p hp)).continuousAt.continuousWithinAt)
    (fun p hp => (hFd p (lt_trans hη hp.1.2.1)).hasFDerivAt)
    (fun p hp => (hGd p (lt_trans hη hp.1.2.1)).hasFDerivAt)
    ((hcont.integrableOn_compact isCompact_Icc).congr_fun
      (fun p hp => (hdiv p (hpos p hp)).symm) measurableSet_Icc)
  rw [setIntegral_congr_fun measurableSet_Icc (fun p hp => hdiv p (hpos p hp))] at key
  rw [key]
  have hχ2 : chiC 2 = 0 := by simp [chiC, qs_of_nonpos]
  have hχη : chiC η = 1 := chi_one η (by rw [abs_of_pos hη]; linarith)
  have hf1a : winF1 E₁ E₂ η (E₁ - η) = 0 := (winF_out hη (Or.inl le_rfl)).2.1
  have hf1b : winF1 E₁ E₂ η (E₂ + η) = 0 := (winF_out hη (Or.inr le_rfl)).2.1
  simp only [hFc, hGc, hχ2, hχη, hf1a, hf1b, mul_zero, zero_mul, Complex.ofReal_zero,
    intervalIntegral.integral_zero, mul_one, sub_zero, zero_sub, add_zero]

private theorem winF1_integrable {E₁ E₂ η : ℝ} (hη : 0 < η) : Integrable (winF1 E₁ E₂ η) :=
  (winF1_continuous E₁ E₂ η).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun _ hx => (winF_out' hη hx).2.1)

private theorem winF2_integrable {E₁ E₂ η : ℝ} (hη : 0 < η) : Integrable (winF2 E₁ E₂ η) :=
  (winF2_continuous E₁ E₂ η).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun _ hx => (winF_out' hη hx).2.2)

private theorem winF_integrable {E₁ E₂ η : ℝ} (hη : 0 < η) : Integrable (winF E₁ E₂ η) :=
  (winF_contDiff E₁ E₂ η).continuous.integrable_of_hasCompactSupport (winF_hasCompactSupport hη)

/-- (Tχ): `∫_{y > 0} |χ'(y)| dy ≤ 1`. -/
private theorem chi_int :
    Integrable (Set.indicator (Set.Ioi 0) fun y => |deriv chiC y|) ∧
      ∫ y, Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y ≤ 1 := by
  have hb : ∀ y, ‖Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y‖ ≤ |qs1 (2 - y)| :=
    fun y => by
      by_cases hy : y ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hy, chi_deriv_of_nonneg (le_of_lt hy), Real.norm_eq_abs,
          abs_abs, abs_neg]
      · rw [Set.indicator_of_notMem hy, norm_zero]; exact abs_nonneg _
  have hq : Integrable fun y => |qs1 (2 - y)| := qs_integrable.comp_sub_left 2
  have hi : Integrable (Set.indicator (Set.Ioi 0) fun y => |deriv chiC y|) :=
    hq.mono'
      ((chi_deriv_continuous.abs.measurable.indicator measurableSet_Ioi).aestronglyMeasurable)
      (Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  calc ∫ y, Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y ≤ ∫ y, |qs1 (2 - y)| :=
        integral_mono_of_nonneg (Eventually.of_forall fun y =>
          Set.indicator_nonneg (fun _ _ => abs_nonneg _) y) hq
          (Eventually.of_forall fun y => (le_abs_self _).trans (by simpa using hb y))
    _ = 1 := by rw [integral_sub_left_eq_self (fun y => |qs1 y|) volume 2, qs1_integral]

/-- `ψ(y) = 𝟙_{[η, 2]}(y) / y + 𝟙_{y > 0} |χ'(y)|`, with `∫ ψ ≤ log(2/η) + 1`. -/
private theorem count_psi {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) :
    Integrable (fun y => Set.indicator (Set.Icc η 2) (fun y => y⁻¹) y +
      Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y) ∧
    ∫ y, (Set.indicator (Set.Icc η 2) (fun y => y⁻¹) y +
      Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y) ≤ Real.log (2 / η) + 1 := by
  obtain ⟨hci, hc⟩ := chi_int
  have h1 : Integrable (Set.indicator (Set.Icc η 2) fun y : ℝ => y⁻¹) :=
    ((continuousOn_inv₀.mono fun y (hy : y ∈ Set.Icc η 2) =>
      ne_of_gt (lt_of_lt_of_le hη hy.1)).integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine ⟨h1.add hci, ?_⟩
  rw [integral_add h1 hci, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hη2, integral_inv_of_pos hη (by norm_num)]
  linarith

/-- Step 4 of the proof of Lemma 3.16: `|∫_{y ≥ η} y f'' χ Im Δ| ≤ 2 (U/N) (log(2/η) + 2)`. -/
private theorem count_T3 {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ}
    (hE : E₁ < E₂) (hη : 0 < η) (hη' : η ≤ 1 / 2) (hU : 0 ≤ U) (h : BoxBound lam E₁ E₂ η U) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | η ≤ p.2}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * chiC p.2 * (dl lam p.1 p.2).im)) p) ∧
    |∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | η ≤ p.2}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * chiC p.2 * (dl lam p.1 p.2).im)) p| ≤
      2 * (U / N) * (Real.log (2 / η) + 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set A := Set.Icc ((E₁ - η, η) : ℝ × ℝ) (E₂ + η, 2) with hA
  set g : ℝ × ℝ → ℝ := fun p => -(p.2 * winF2 E₁ E₂ η p.1 * chiC p.2 * (dl lam p.1 p.2).im)
    with hg
  have hpos : ∀ p ∈ A, 0 < p.2 := fun p hp => lt_of_lt_of_le hη hp.1.2
  have heq : (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | η ≤ p.2} g p) = A.indicator g := by
    funext p
    by_cases hp : p ∈ A
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | η ≤ p.2} from
        hp.1.2)]
    · rw [Set.indicator_of_notMem hp]
      by_cases hp2 : η ≤ p.2
      · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | η ≤ p.2} from hp2)]
        simp only [hA, Set.mem_Icc, Prod.le_def, not_and_or, not_le] at hp
        rcases le_or_gt p.2 2 with h2 | h2
        · have hx : p.1 ∉ Set.Icc (E₁ - η) (E₂ + η) := by
            rw [Set.mem_Icc, not_and_or, not_le, not_le]
            rcases hp with (hp | hp) | (hp | hp)
            · exact Or.inl hp
            · linarith
            · exact Or.inr hp
            · linarith
          simp [hg, (winF_out' hη hx).2.2]
        · simp [hg, chi_zero p.2 (by rw [abs_of_pos (by linarith)]; exact h2)]
      · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | η ≤ p.2} from hp2)]
  have hdl := (dl_continuousOn lam).mono hpos
  have c1 := winF1_continuous E₁ E₂ η
  have c2 := winF2_continuous E₁ E₂ η
  have c3 := chi_continuous
  have c4 := chi_deriv_continuous
  have hgc : ContinuousOn g A := by
    have := Complex.continuous_im.comp_continuousOn hdl
    simp only [hg]
    exact (((Continuous.continuousOn (by fun_prop)).mul this)).neg
  have hgi : Integrable (A.indicator g) :=
    (hgc.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  rw [heq]
  refine ⟨hgi, ?_⟩
  rw [integral_indicator measurableSet_Icc]
  -- complex form
  set W : ℝ × ℝ → ℂ := fun p =>
    Complex.I * ((p.2 * chiC p.2 * winF2 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 with hW
  set C : ℝ × ℝ → ℂ := fun p =>
    (((chiC p.2 + p.2 * deriv chiC p.2) * winF1 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 with hC
  have hWc : ContinuousOn W A := ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) hdl
  have hCc : ContinuousOn C A := ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) hdl
  have hWi : IntegrableOn W A := hWc.integrableOn_compact isCompact_Icc
  have hCi : IntegrableOn C A := hCc.integrableOn_compact isCompact_Icc
  have hgW : ∀ p, g p = (W p).re := fun p => by
    simp only [hg, hW, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hdiv := count_div lam hE hη hη'
  set B := ∫ x in (E₁ - η)..(E₂ + η), ((η * winF1 E₁ E₂ η x : ℝ) : ℂ) * dl lam x η with hB
  have hWCB : ∫ p in A, W p = (∫ p in A, C p) + B := by
    have e : ∀ p, W p = C p - (-Complex.I * ((p.2 * chiC p.2 * winF2 E₁ E₂ η p.1 : ℝ) : ℂ) *
        dl lam p.1 p.2 + C p) := fun p => by simp only [hW, hC]; ring
    have hsum : IntegrableOn (fun p : ℝ × ℝ =>
        -Complex.I * ((p.2 * chiC p.2 * winF2 E₁ E₂ η p.1 : ℝ) : ℂ) * dl lam p.1 p.2 + C p) A :=
      (hWi.neg.congr_fun (fun p _ => by simp only [hW, Pi.neg_apply]; ring)
        measurableSet_Icc).add hCi
    simp only [e]
    rw [integral_sub hCi hsum, hdiv]
    ring
  have hre : ∫ p in A, g p = (∫ p in A, W p).re := by
    simp only [hgW]
    exact integral_re hWi
  rw [hre, hWCB]
  -- the two bounds
  have hf1i : Integrable fun x => |winF1 E₁ E₂ η x| := (winF1_integrable hη).abs
  have hf1 := winF1_int_le (E₁ := E₁) (E₂ := E₂) hη
  have hf1n : 0 ≤ ∫ x, |winF1 E₁ E₂ η x| := integral_nonneg fun _ => abs_nonneg _
  have hBb : ‖B‖ ≤ 2 * (U / N) := by
    have hab : E₁ - η ≤ E₂ + η := by linarith
    refine (intervalIntegral.norm_integral_le_of_norm_le hab (g := fun x => U / N *
        |winF1 E₁ E₂ η x|) (Eventually.of_forall fun x hx => ?_)
        ((hf1i.const_mul _).intervalIntegrable)).trans ?_
    · have hb := h x ⟨hx.1.le, hx.2⟩ η ⟨le_rfl, by linarith⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hη]
      calc η * |winF1 E₁ E₂ η x| * ‖dl lam x η‖ ≤ η * |winF1 E₁ E₂ η x| * (U / (N * η)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = U / N * |winF1 E₁ E₂ η x| := by field_simp
    · rw [intervalIntegral.integral_of_le hab, integral_const_mul]
      have := setIntegral_le_integral (s := Set.Ioc (E₁ - η) (E₂ + η)) hf1i
        (Eventually.of_forall fun x => abs_nonneg (winF1 E₁ E₂ η x))
      have hu : 0 ≤ U / N := by positivity
      nlinarith
  obtain ⟨hψi, hψ⟩ := count_psi hη (by linarith)
  have hCb : ‖∫ p in A, C p‖ ≤ 2 * (U / N) * (Real.log (2 / η) + 1) := by
    set G : ℝ × ℝ → ℝ := fun p => (U / N * |winF1 E₁ E₂ η p.1|) *
      (Set.indicator (Set.Icc η 2) (fun y => y⁻¹) p.2 +
        Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) p.2) with hG
    have hGi : Integrable G := by
      rw [Measure.volume_eq_prod]
      exact (hf1i.const_mul _).mul_prod hψi
    have hpt : ∀ p ∈ A, ‖C p‖ ≤ G p := fun p hp => by
      obtain ⟨⟨hx1, hy1⟩, ⟨hx2, hy2⟩⟩ := hp
      simp only at hx1 hy1 hx2 hy2
      have hy0 : 0 < p.2 := lt_of_lt_of_le hη hy1
      have hb := h p.1 ⟨hx1, hx2⟩ p.2 ⟨hy1, hy2⟩
      obtain ⟨χ0, χ1⟩ := chi_bounds p.2
      have habs : |(chiC p.2 + p.2 * deriv chiC p.2) * winF1 E₁ E₂ η p.1| ≤
          (chiC p.2 + p.2 * |deriv chiC p.2|) * |winF1 E₁ E₂ η p.1| := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans ?_) (abs_nonneg _)
        rw [abs_of_nonneg χ0, abs_mul, abs_of_pos hy0]
      simp only [hC, hG, Set.indicator_of_mem (show p.2 ∈ Set.Icc η 2 from ⟨hy1, hy2⟩),
        Set.indicator_of_mem (show p.2 ∈ Set.Ioi (0 : ℝ) from hy0)]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |(chiC p.2 + p.2 * deriv chiC p.2) * winF1 E₁ E₂ η p.1| * ‖dl lam p.1 p.2‖
          ≤ (chiC p.2 + p.2 * |deriv chiC p.2|) * |winF1 E₁ E₂ η p.1| * (U / (N * p.2)) :=
            mul_le_mul habs hb (norm_nonneg _) (by positivity)
        _ = U / N * |winF1 E₁ E₂ η p.1| * (chiC p.2 * p.2⁻¹ + |deriv chiC p.2|) := by
            field_simp
        _ ≤ U / N * |winF1 E₁ E₂ η p.1| * (p.2⁻¹ + |deriv chiC p.2|) := by
            gcongr
            exact mul_le_of_le_one_left (inv_nonneg.2 hy0.le) χ1
    have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg (by positivity) (add_nonneg
      (Set.indicator_nonneg (fun y (hy : y ∈ Set.Icc η 2) => inv_nonneg.2 (le_trans hη.le hy.1)) _)
      (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _))
    calc ‖∫ p in A, C p‖ ≤ ∫ p in A, G p :=
          norm_integral_le_of_norm_le hGi.integrableOn
            ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hpt))
      _ ≤ ∫ p, G p := setIntegral_le_integral hGi (Eventually.of_forall hG0)
      _ = (U / N * ∫ x, |winF1 E₁ E₂ η x|) * (Real.log (2 / η) + 1 - (Real.log (2 / η) + 1 -
            ∫ y, (Set.indicator (Set.Icc η 2) (fun y => y⁻¹) y +
              Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y))) := by
          have e : ∫ p, G p = (∫ x, U / N * |winF1 E₁ E₂ η x|) *
              ∫ y, (Set.indicator (Set.Icc η 2) (fun y => y⁻¹) y +
                Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y) := by
            rw [Measure.volume_eq_prod]
            exact integral_prod_mul (fun x => U / N * |winF1 E₁ E₂ η x|) (fun y =>
              Set.indicator (Set.Icc η 2) (fun y => y⁻¹) y +
                Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y)
          rw [e, integral_const_mul]
          ring
      _ ≤ (U / N * 2) * (Real.log (2 / η) + 1) := by
          have hu : 0 ≤ U / N := by positivity
          have hψ0 : 0 ≤ ∫ y, (Set.indicator (Set.Icc η 2) (fun y => y⁻¹) y +
              Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y) :=
            integral_nonneg fun y => add_nonneg
              (Set.indicator_nonneg (fun y (hy : y ∈ Set.Icc η 2) =>
                inv_nonneg.2 (le_trans hη.le hy.1)) _)
              (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
          refine mul_le_mul (mul_le_mul_of_nonneg_left hf1 hu) (by linarith) (by linarith)
            (by positivity)
      _ = 2 * (U / N) * (Real.log (2 / η) + 1) := by ring
  calc |((∫ p in A, C p) + B).re| ≤ ‖(∫ p in A, C p) + B‖ := Complex.abs_re_le_norm _
    _ ≤ ‖∫ p in A, C p‖ + ‖B‖ := norm_add_le _ _
    _ ≤ 2 * (U / N) * (Real.log (2 / η) + 1) + 2 * (U / N) := add_le_add hCb hBb
    _ = 2 * (U / N) * (Real.log (2 / η) + 2) := by ring

/-- Step 2 of the proof of Lemma 3.16: the `χ'` terms, `|T₁| ≤ (U/N)(∫|f| + ∫|f'|)`. -/
private theorem count_T1 {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ}
    (hE : E₁ < E₂) (hη : 0 < η) (hη2 : η ≤ 1) (hU : 0 ≤ U) (h : BoxBound lam E₁ E₂ η U) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => -(deriv chiC p.2 * (winF E₁ E₂ η p.1 * (dl lam p.1 p.2).im +
        p.2 * winF1 E₁ E₂ η p.1 * (dl lam p.1 p.2).re))) p) ∧
    |∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => -(deriv chiC p.2 * (winF E₁ E₂ η p.1 * (dl lam p.1 p.2).im +
        p.2 * winF1 E₁ E₂ η p.1 * (dl lam p.1 p.2).re))) p| ≤
      U / N * (E₂ - E₁ + 2 * η + 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 ≤ U / N := by positivity
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  obtain ⟨hci, hc⟩ := chi_int
  set G : ℝ × ℝ → ℝ := fun p => (U / N * (|winF E₁ E₂ η p.1| + |winF1 E₁ E₂ η p.1|)) *
    Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) p.2 with hG
  have hfi : Integrable fun x => U / N * (|winF E₁ E₂ η x| + |winF1 E₁ E₂ η x|) :=
    ((winF_integrable hη).abs.add (winF1_integrable hη).abs).const_mul _
  have hGi : Integrable G := by
    rw [Measure.volume_eq_prod]; exact hfi.mul_prod hci
  have hdl := dl_continuousOn lam
  have c0 := (winF_contDiff E₁ E₂ η).continuous
  have c1 := winF1_continuous E₁ E₂ η
  have c4 := chi_deriv_continuous
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => -(deriv chiC p.2 * (winF E₁ E₂ η p.1 * (dl lam p.1 p.2).im +
        p.2 * winF1 E₁ E₂ η p.1 * (dl lam p.1 p.2).re))) p) := by
    refine (aestronglyMeasurable_indicator_iff hS).2 (ContinuousOn.aestronglyMeasurable ?_ hS)
    have him := Complex.continuous_im.comp_continuousOn hdl
    have hre := Complex.continuous_re.comp_continuousOn hdl
    exact ((Continuous.continuousOn (by fun_prop)).mul
      (((Continuous.continuousOn (by fun_prop)).mul him).add
        ((Continuous.continuousOn (by fun_prop)).mul hre))).neg
  have hpt : ∀ p : ℝ × ℝ, ‖Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => -(deriv chiC p.2 * (winF E₁ E₂ η p.1 * (dl lam p.1 p.2).im +
        p.2 * winF1 E₁ E₂ η p.1 * (dl lam p.1 p.2).re))) p‖ ≤ G p := fun p => by
    obtain ⟨x, y⟩ := p
    have hG0 : 0 ≤ G (x, y) := mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | 0 < p.2} from hy)]
      simp only [hG, Set.indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from hy)]
      by_cases hx : x ∈ Set.Icc (E₁ - η) (E₂ + η)
      · by_cases hy12 : 1 ≤ y ∧ y ≤ 2
        · have hb := h x hx y ⟨by linarith [hy12.1], hy12.2⟩
          have hb1 : ‖dl lam x y‖ ≤ U / N := hb.trans (by
            rw [div_le_div_iff₀ (by positivity) hNR]
            nlinarith [mul_nonneg (mul_nonneg hU hNR.le) (sub_nonneg.2 hy12.1)])
          have hb2 : y * ‖dl lam x y‖ ≤ U / N := by
            calc y * ‖dl lam x y‖ ≤ y * (U / (N * y)) := mul_le_mul_of_nonneg_left hb hy.le
              _ = U / N := by field_simp
          rw [Real.norm_eq_abs, abs_neg, abs_mul, mul_comm]
          refine mul_le_mul ?_ le_rfl (abs_nonneg _) (by positivity)
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hy, mul_add]
          have i1 := Complex.abs_im_le_norm (dl lam x y)
          have i2 := Complex.abs_re_le_norm (dl lam x y)
          refine add_le_add ?_ ?_
          · calc |winF E₁ E₂ η x| * |(dl lam x y).im| ≤ |winF E₁ E₂ η x| * (U / N) :=
                  mul_le_mul_of_nonneg_left (i1.trans hb1) (abs_nonneg _)
              _ = _ := by ring
          · calc y * |winF1 E₁ E₂ η x| * |(dl lam x y).re|
                ≤ |winF1 E₁ E₂ η x| * (y * ‖dl lam x y‖) := by
                  rw [mul_comm y, mul_assoc]
                  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left i2 hy.le)
                    (abs_nonneg _)
              _ ≤ |winF1 E₁ E₂ η x| * (U / N) := mul_le_mul_of_nonneg_left hb2 (abs_nonneg _)
              _ = _ := by ring
        · have h0 : deriv chiC y = 0 := by
            rw [chi_deriv_of_nonneg hy.le, neg_eq_zero]
            rcases not_and_or.1 hy12 with h1 | h1
            · exact qs1_of_one_le (by linarith [not_le.1 h1])
            · exact qs1_of_nonpos (by linarith [not_le.1 h1])
          rw [h0]; simp only [zero_mul, neg_zero, norm_zero, abs_zero, mul_zero]; rfl
      · obtain ⟨f0, f1, -⟩ := winF_out' hη hx
        rw [f0, f1]; simp only [zero_mul, mul_zero, zero_add, neg_zero, norm_zero]
        exact mul_nonneg (by positivity) (abs_nonneg _)
    · rw [Set.indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 < p.2} from hy), norm_zero]
      exact hG0
  refine ⟨hGi.mono' hm (Eventually.of_forall hpt), ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hGi (Eventually.of_forall hpt)).trans ?_
  have e : ∫ p, G p = (∫ x, U / N * (|winF E₁ E₂ η x| + |winF1 E₁ E₂ η x|)) *
      ∫ y, Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (fun x => U / N * (|winF E₁ E₂ η x| + |winF1 E₁ E₂ η x|))
      (fun y => Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y)
  rw [e, integral_const_mul, integral_add (winF_integrable hη).abs (winF1_integrable hη).abs]
  have h0 := winF_int_le (E₁ := E₁) (E₂ := E₂) hη hE
  have h1 := winF1_int_le (E₁ := E₁) (E₂ := E₂) hη
  have hn : 0 ≤ (∫ x, |winF E₁ E₂ η x|) + ∫ x, |winF1 E₁ E₂ η x| :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hc0 : 0 ≤ ∫ y, Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y :=
    integral_nonneg fun y => Set.indicator_nonneg (fun _ _ => abs_nonneg _) y
  calc U / N * ((∫ x, |winF E₁ E₂ η x|) + ∫ x, |winF1 E₁ E₂ η x|) *
        ∫ y, Set.indicator (Set.Ioi 0) (fun y => |deriv chiC y|) y
      ≤ U / N * (E₂ - E₁ + 2 * η + 2) * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hu) hc hc0 (by positivity)
    _ = _ := mul_one _

/-- Step 3 of the proof of Lemma 3.16: `|T₂| ≤ η (15/(2η)) (2η + U/N)`. -/
private theorem count_T2 {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ}
    (hE : E₁ < E₂) (hη : 0 < η) (hη2 : η ≤ 2) (hU : 0 ≤ U) (h : BoxBound lam E₁ E₂ η U) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * (dl lam p.1 p.2).im)) p) ∧
    |∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * (dl lam p.1 p.2).im)) p| ≤
      15 * η + 15 / 2 * (U / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 ≤ U / N := by positivity
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η} := measurable_snd measurableSet_Ioo
  set c := 2 * η + U / N with hc
  set G : ℝ × ℝ → ℝ := fun p => |winF2 E₁ E₂ η p.1| *
    Set.indicator (Set.Ioo 0 η) (fun _ => c) p.2 with hG
  have hci : Integrable (Set.indicator (Set.Ioo 0 η) fun _ : ℝ => c) :=
    (integrableOn_const (C := c) (by simp)).integrable_indicator measurableSet_Ioo
  have hGi : Integrable G := by
    rw [Measure.volume_eq_prod]; exact (winF2_integrable hη).abs.mul_prod hci
  have hdl := dl_continuousOn lam
  have c2 := winF2_continuous E₁ E₂ η
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * (dl lam p.1 p.2).im)) p) := by
    refine (aestronglyMeasurable_indicator_iff hS).2 (ContinuousOn.aestronglyMeasurable ?_ hS)
    have him := Complex.continuous_im.comp_continuousOn
      (hdl.mono fun p (hp : p ∈ {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}) => hp.1)
    exact ((Continuous.continuousOn (by fun_prop)).mul him).neg
  have hpt : ∀ p : ℝ × ℝ, ‖Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * (dl lam p.1 p.2).im)) p‖ ≤ G p := fun p => by
    obtain ⟨x, y⟩ := p
    by_cases hy : y ∈ Set.Ioo 0 η
    · rw [Set.indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η} from hy)]
      simp only [hG, Set.indicator_of_mem hy]
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_pos hy.1]
      by_cases hx : x ∈ Set.Icc (E₁ - η) (E₂ + η)
      · have := count_small_y hN lam hη hη2 h hx hy.1 hy.2.le
        calc y * |winF2 E₁ E₂ η x| * |(dl lam x y).im| =
            |winF2 E₁ E₂ η x| * (y * |(dl lam x y).im|) := by ring
          _ ≤ |winF2 E₁ E₂ η x| * c := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      · rw [(winF_out' hη hx).2.2]; simp
    · rw [Set.indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η} from hy),
        norm_zero]
      exact mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => by positivity) _)
  refine ⟨hGi.mono' hm (Eventually.of_forall hpt), ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hGi (Eventually.of_forall hpt)).trans ?_
  have e : ∫ p, G p = (∫ x, |winF2 E₁ E₂ η x|) *
      ∫ y, Set.indicator (Set.Ioo 0 η) (fun _ => c) y := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (fun x => |winF2 E₁ E₂ η x|)
      (fun y => Set.indicator (Set.Ioo 0 η) (fun _ => c) y)
  rw [e, integral_indicator_const c measurableSet_Ioo, Real.volume_real_Ioo_of_le hη.le,
    smul_eq_mul, sub_zero]
  have h2 := winF2_int_le (E₁ := E₁) (E₂ := E₂) hη hE
  calc (∫ x, |winF2 E₁ E₂ η x|) * (η * c) ≤ 15 / (2 * η) * (η * c) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 15 * η + 15 / 2 * (U / N) := by rw [hc]; field_simp

/-- `Re [g Δ] = T₁ + T₂ + T₃` pointwise on the upper half-plane (Step 1 of the proof of
Lemma 3.16; `χ = 1` on `(0, η)`). -/
private theorem count_decomp {N : ℕ} (lam : Fin N → ℝ) {E₁ E₂ η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (p : ℝ × ℝ) :
    Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => (hsG (winF E₁ E₂ η) chiC p.1 p.2 * (stieltjesOf lam (p.1 + p.2 * Complex.I) -
        msc (p.1 + p.2 * Complex.I))).re) p =
    Set.indicator {p : ℝ × ℝ | 0 < p.2}
      (fun p => -(deriv chiC p.2 * (winF E₁ E₂ η p.1 * (dl lam p.1 p.2).im +
        p.2 * winF1 E₁ E₂ η p.1 * (dl lam p.1 p.2).re))) p +
    Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * (dl lam p.1 p.2).im)) p +
    Set.indicator {p : ℝ × ℝ | η ≤ p.2}
      (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * chiC p.2 * (dl lam p.1 p.2).im)) p := by
  obtain ⟨x, y⟩ := p
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioo]
  rw [count_re_hsG, winF_deriv2 hη, winF_deriv hη]
  simp only [dl]
  by_cases hy : 0 < y
  · by_cases hyη : y < η
    · rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left ⟨hy, hyη⟩, ite_eq_right (not_le.2 hyη),
        chi_one y (by rw [abs_of_pos hy]; linarith)]
      ring
    · rw [ite_eq_left hy, ite_eq_left hy, ite_eq_right (fun h => hyη h.2),
        ite_eq_left (not_lt.1 hyη)]
      ring
  · rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right (fun h => hy h.1),
      ite_eq_right (fun h => hy (lt_of_lt_of_le hη h))]
    ring

/-- Lemma 3.16: the counting function from the Stieltjes transform. -/
theorem count_from_stieltjes {N : ℕ} (hN : 0 < N) (lam : Fin N → ℝ) {E₁ E₂ η U : ℝ}
    (hE : E₁ < E₂) (hE8 : E₂ - E₁ ≤ 8) (hη : 0 < η) (hη' : η ≤ 1 / 2) (hU : 1 ≤ U)
    (h : ∀ x ∈ Set.Icc (E₁ - η) (E₂ + η), ∀ y ∈ Set.Icc η 2,
      ‖stieltjesOf lam (x + y * Complex.I) - msc (x + y * Complex.I)‖ ≤ U / (N * y)) :
    |(countOf lam E₂ - countOf lam E₁) - (nsc E₂ - nsc E₁)| ≤
      10 / N * (U * Real.log (2 / η) + N * η) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : 0 ≤ U := by linarith
  have hu : 0 ≤ U / N := by positivity
  have hη1 : η ≤ 1 := by linarith
  have hη2 : η ≤ 2 := by linarith
  have hB : BoxBound lam E₁ E₂ η U := h
  obtain ⟨hHi, hD⟩ := count_D lam (winF_contDiff E₁ E₂ η) (winF_hasCompactSupport hη)
    chi_contDiff chi_even chi_one chi_zero chi_bounds
  obtain ⟨h1i, h1⟩ := count_T1 hN lam hE hη hη1 hU0 hB
  obtain ⟨h2i, h2⟩ := count_T2 hN lam hE hη hη2 hU0 hB
  obtain ⟨h3i, h3⟩ := count_T3 hN lam hE hη hη' hU0 hB
  rw [integral_congr_ae (Eventually.of_forall (count_decomp lam (E₁ := E₁) (E₂ := E₂) hη hη1)),
    integral_add (h1i.fun_add h2i) h3i, integral_add h1i h2i] at hD
  have hc := count_step6 hN lam hE hη hη2 hB
  have hs := count_step6_sc (E₁ := E₁) (E₂ := E₂) hE hη
  have hL : 1.38 ≤ Real.log (2 / η) := by
    have h4 : Real.log 4 ≤ Real.log (2 / η) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hη]; linarith)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hπ : π⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) Real.pi_gt_three.le
  have hπ0 : 0 < π⁻¹ := inv_pos.2 Real.pi_pos
  set I1 := ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2}
    (fun p => -(deriv chiC p.2 * (winF E₁ E₂ η p.1 * (dl lam p.1 p.2).im +
      p.2 * winF1 E₁ E₂ η p.1 * (dl lam p.1 p.2).re))) p
  set I2 := ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 η}
    (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * (dl lam p.1 p.2).im)) p
  set I3 := ∫ p : ℝ × ℝ, Set.indicator {p : ℝ × ℝ | η ≤ p.2}
    (fun p => -(p.2 * winF2 E₁ E₂ η p.1 * chiC p.2 * (dl lam p.1 p.2).im)) p
  set L := Real.log (2 / η)
  set X := U / N * (E₂ - E₁ + 2 * η + 2) + (15 * η + 15 / 2 * (U / N)) + 2 * (U / N) * (L + 2)
  have hI : |I1 + I2 + I3| ≤ X :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hI
  have hDb : |(N : ℝ)⁻¹ * ∑ j, winF E₁ E₂ η (lam j) - ∫ l, winF E₁ E₂ η l * rhoSc l| ≤
      3⁻¹ * X := by
    rw [hD, abs_mul, abs_of_pos hπ0]
    exact mul_le_mul hπ hI (abs_nonneg _) (by norm_num)
  have hs' : 2 * η / π ≤ 2 * η / 3 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) Real.pi_gt_three.le
  have hX : U / N * (E₂ - E₁ + 2 * η + 2) ≤ U / N * 11 :=
    mul_le_mul_of_nonneg_left (by linarith) hu
  have huL : U / N * 1.38 ≤ U / N * L := mul_le_mul_of_nonneg_left hL hu
  have hR : 10 / N * (U * L + N * η) = 10 * (U / N * L) + 10 * η := by
    field_simp
  rw [hR]
  obtain ⟨c1, c2⟩ := abs_le.1 hc
  obtain ⟨d1, d2⟩ := abs_le.1 hDb
  obtain ⟨e1, e2⟩ := abs_le.1 hs
  have hXv : X = U / N * (E₂ - E₁ + 2 * η + 2) + (15 * η + 15 / 2 * (U / N)) +
      2 * (U / N) * (L + 2) := rfl
  have hX' : X ≤ 45 / 2 * (U / N) + 15 * η + 2 * (U / N * L) := by rw [hXv]; linarith
  have hfin : 4 * η + 4 * U / N + 3⁻¹ * X + 2 * η / 3 ≤ 10 * (U / N * L) + 10 * η := by
    have : 4 * U / N = 4 * (U / N) := by ring
    rw [this]; linarith
  rw [abs_le]
  constructor <;> linarith

end Rigidity
