module

public import Rigidity.Semicircle.Stieltjes
public import Rigidity.MainDefs

@[expose] public section

/-!
# The semicircle distribution function and the classical locations

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file defines the semicircle distribution function `n_sc(E) = ∫_{-∞}^E ϱ_sc` and the
classical locations `γ_j = inf {x : N n_sc(x) ≥ j}` (NP v1.1, Section 2), indexed by `k = j - 1`
in `Fin N`.  It proves the elementary statements of Lemma 3.4: part (a) on `ϱ_sc` and `n_sc`
(`rhoSc_props`, `nsc_props`) and the part of (c) not involving the reflection `γ_{N-j} = -γ_j`
(`nsc_gamma`, `gamma_last`, `gamma_mem`).

`ϱ_sc` is continuous with support in `[-2, 2]` and total mass `1` (Lemma 3.3), so `n_sc` is a
continuous nondecreasing function from `0` to `1`, strictly increasing on `[-2, 2]`.  The set
`{x : N n_sc(x) ≥ k + 1}` is then a nonempty closed up-set contained in `(-2, ∞)`, whose least
element `γ` satisfies `N n_sc(γ) = k + 1` by continuity.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `ϱ_sc` is continuous. -/
private lemma density_rhoSc_continuous : Continuous rhoSc := by
  unfold rhoSc
  fun_prop

/-- `ϱ_sc` is nonnegative. -/
private lemma density_rhoSc_nonneg (x : ℝ) : 0 ≤ rhoSc x := by
  unfold rhoSc
  positivity

/-- `ϱ_sc ≤ 1 / π`, since `√((4 - x²)₊) ≤ 2`. -/
private lemma density_rhoSc_le (x : ℝ) : rhoSc x ≤ 1 / π := by
  unfold rhoSc
  have h2 : Real.sqrt (max (4 - x ^ 2) 0) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    refine max_le ?_ (by norm_num)
    nlinarith [sq_nonneg x]
  calc (2 * π)⁻¹ * Real.sqrt (max (4 - x ^ 2) 0) ≤ (2 * π)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / π := by field_simp

/-- `ϱ_sc x > 0` exactly for `|x| < 2`. -/
private lemma density_rhoSc_pos_iff (x : ℝ) : 0 < rhoSc x ↔ x ∈ Set.Ioo (-2 : ℝ) 2 := by
  unfold rhoSc
  have hπ : 0 < (2 * π)⁻¹ := by positivity
  rw [mul_pos_iff_of_pos_left hπ, Real.sqrt_pos, lt_max_iff]
  constructor
  · rintro (h | h)
    · constructor <;> nlinarith
    · exact absurd h (lt_irrefl _)
  · rintro ⟨h1, h2⟩
    left
    nlinarith

/-- `ϱ_sc` vanishes outside `(-2, 2)`. -/
private lemma density_rhoSc_eq_zero {x : ℝ} (hx : x ∉ Set.Ioo (-2 : ℝ) 2) : rhoSc x = 0 :=
  le_antisymm (not_lt.mp fun h => hx ((density_rhoSc_pos_iff x).mp h)) (density_rhoSc_nonneg x)

/-- `ϱ_sc` is integrable on `ℝ`, being continuous with support in `[-2, 2]`. -/
private lemma density_rhoSc_integrable : Integrable rhoSc := by
  refine density_rhoSc_continuous.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => ?_
  exact density_rhoSc_eq_zero fun h => hx ⟨h.1.le, h.2.le⟩

private lemma density_rhoSc_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable rhoSc volume a b :=
  density_rhoSc_continuous.intervalIntegrable a b

/-- `n_sc b - n_sc a = ∫_a^b ϱ_sc`. -/
private lemma density_nsc_sub (a b : ℝ) : nsc b - nsc a = ∫ x in a..b, rhoSc x :=
  intervalIntegral.integral_Iic_sub_Iic density_rhoSc_integrable.integrableOn
    density_rhoSc_integrable.integrableOn

private lemma density_nsc_eq (E : ℝ) : nsc E = nsc 0 + ∫ x in (0 : ℝ)..E, rhoSc x := by
  rw [← density_nsc_sub]; ring

private lemma density_nsc_continuous : Continuous nsc := by
  have : nsc = fun E => nsc 0 + ∫ x in (0 : ℝ)..E, rhoSc x := funext density_nsc_eq
  rw [this]
  exact continuous_const.add (intervalIntegral.continuous_primitive
    (fun a b => density_rhoSc_intervalIntegrable a b) 0)

private lemma density_nsc_hasDerivAt (E : ℝ) : HasDerivAt nsc (rhoSc E) E := by
  have h := (density_rhoSc_continuous.integral_hasStrictDerivAt 0 E).hasDerivAt.const_add (nsc 0)
  have : nsc = fun E => nsc 0 + ∫ x in (0 : ℝ)..E, rhoSc x := funext density_nsc_eq
  rw [this]
  exact h

private lemma density_nsc_mono : Monotone nsc := by
  intro a b hab
  have := density_nsc_sub a b
  have h0 : 0 ≤ ∫ x in a..b, rhoSc x :=
    intervalIntegral.integral_nonneg hab fun x _ => density_rhoSc_nonneg x
  linarith

private lemma density_nsc_lipschitz (E E' : ℝ) : |nsc E - nsc E'| ≤ |E - E'| / π := by
  rw [density_nsc_sub]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := E') (b := E) (f := rhoSc)
    (C := 1 / π) (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (density_rhoSc_nonneg x)]
      exact density_rhoSc_le x)
  rw [Real.norm_eq_abs] at h
  calc |∫ x in E'..E, rhoSc x| ≤ 1 / π * |E - E'| := h
    _ = |E - E'| / π := by ring

private lemma density_nsc_of_le {E : ℝ} (hE : E ≤ -2) : nsc E = 0 := by
  unfold nsc
  refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
  exact density_rhoSc_eq_zero fun h => by
    have : x ≤ E := hx
    linarith [h.1]

private lemma density_nsc_two : nsc 2 = 1 := by
  have h := density_nsc_sub (-2) 2
  rw [density_nsc_of_le le_rfl, integral_rhoSc] at h
  linarith

private lemma density_nsc_of_ge {E : ℝ} (hE : 2 ≤ E) : nsc E = 1 := by
  have h := density_nsc_sub 2 E
  have h0 : ∫ x in (2 : ℝ)..E, rhoSc x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro x hx
      rw [Set.uIcc_of_le hE] at hx
      exact density_rhoSc_eq_zero fun h => by linarith [h.2, hx.1]
  rw [h0, density_nsc_two] at h
  linarith

private lemma density_nsc_strictMonoOn : StrictMonoOn nsc (Set.Icc (-2) 2) := by
  intro a ha b hb hab
  have h := density_nsc_sub a b
  have h0 : 0 < ∫ x in a..b, rhoSc x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (density_rhoSc_intervalIntegrable a b)
      (fun x hx => (density_rhoSc_pos_iff x).mpr
        ⟨by linarith [ha.1, hx.1], by linarith [hb.2, hx.2]⟩)
      hab
  linarith

/-- The total mass of `ϱ_sc` over `ℝ` is `1`. -/
private lemma density_integral_univ : ∫ x, rhoSc x = 1 := by
  have h2 : ∫ x in Set.Ioi (2 : ℝ), rhoSc x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact density_rhoSc_eq_zero fun h => by
      have : (2 : ℝ) < x := hx
      linarith [h.2]
  rw [← intervalIntegral.integral_Iic_add_Ioi density_rhoSc_integrable.integrableOn
    density_rhoSc_integrable.integrableOn (b := 2), h2]
  have := density_nsc_two
  unfold nsc at this
  linarith

private lemma density_nsc_neg (E : ℝ) : nsc (-E) = 1 - nsc E := by
  have h1 : nsc (-E) = ∫ x in Set.Ioi E, rhoSc x := by
    unfold nsc
    have := integral_comp_neg_Iic (-E) rhoSc
    rw [neg_neg] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
    simp only [rhoSc, neg_sq]
  have h2 := intervalIntegral.integral_Iic_add_Ioi (b := E) density_rhoSc_integrable.integrableOn
    density_rhoSc_integrable.integrableOn
  rw [density_integral_univ] at h2
  unfold nsc at h1 ⊢
  linarith

/-- `2` belongs to the defining set of `γ_{k+1}`. -/
private lemma density_two_mem {N : ℕ} (k : Fin N) :
    (2 : ℝ) ∈ {x : ℝ | (k.val + 1 : ℝ) ≤ N * nsc x} := by
  change (k.val + 1 : ℝ) ≤ N * nsc 2
  rw [density_nsc_two, mul_one]
  exact_mod_cast Nat.succ_le_of_lt k.isLt

/-- For `k : Fin N` the defining set of `γ_{k+1}` is nonempty. -/
private lemma density_gamma_nonempty {N : ℕ} (k : Fin N) :
    ({x : ℝ | (k.val + 1 : ℝ) ≤ N * nsc x}).Nonempty :=
  ⟨2, density_two_mem k⟩

/-- The defining set of `γ_{k+1}` is bounded below by `-2`. -/
private lemma density_gamma_bddBelow {N : ℕ} (k : Fin N) :
    BddBelow {x : ℝ | (k.val + 1 : ℝ) ≤ N * nsc x} := by
  refine ⟨-2, fun x hx => ?_⟩
  by_contra h
  have h0 : nsc x = 0 := density_nsc_of_le (not_le.mp h).le
  have : (k.val + 1 : ℝ) ≤ N * nsc x := hx
  rw [h0, mul_zero] at this
  have : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  linarith

/-- The defining set of `γ_{k+1}` is closed. -/
private lemma density_gamma_isClosed {N : ℕ} (k : Fin N) :
    IsClosed {x : ℝ | (k.val + 1 : ℝ) ≤ N * nsc x} :=
  isClosed_Ici.preimage (continuous_const.mul density_nsc_continuous)

/-- The infimum is attained: `N n_sc(γ_{k+1}) ≥ k + 1`. -/
private lemma density_le_nsc_gamma {N : ℕ} (k : Fin N) :
    (k.val + 1 : ℝ) ≤ N * nsc (gamma N k) :=
  (density_gamma_isClosed k).csInf_mem (density_gamma_nonempty k) (density_gamma_bddBelow k)

theorem nsc_gamma {N : ℕ} (k : Fin N) : (N : ℝ) * nsc (gamma N k) = k.val + 1 := by
  refine le_antisymm ?_ (density_le_nsc_gamma k)
  by_contra hlt
  rw [not_le] at hlt
  set γ := gamma N k with hγ
  have hcont : Continuous fun x => (N : ℝ) * nsc x := continuous_const.mul density_nsc_continuous
  have hev : ∀ᶠ x in 𝓝 γ, (k.val + 1 : ℝ) < N * nsc x :=
    hcont.continuousAt.eventually (lt_mem_nhds hlt)
  obtain ⟨x, hx, hxγ⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Iio γ ∈ 𝓝[<] γ)).exists
  have hmem : x ∈ {x : ℝ | (k.val + 1 : ℝ) ≤ N * nsc x} := hx.le
  have := csInf_le (density_gamma_bddBelow k) hmem
  exact absurd hxγ (not_lt.mpr this)

/-- `γ_{k+1} ∈ (-2, 2]`. -/
private lemma density_gamma_mem {N : ℕ} (k : Fin N) : gamma N k ∈ Set.Ioc (-2) 2 := by
  constructor
  · by_contra h
    have h0 : nsc (gamma N k) = 0 := density_nsc_of_le (not_lt.mp h)
    have h1 := nsc_gamma k
    rw [h0, mul_zero] at h1
    have : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    linarith
  · exact csInf_le (density_gamma_bddBelow k) (density_two_mem k)

theorem gamma_last {N : ℕ} (hN : 0 < N) : gamma N ⟨N - 1, by omega⟩ = 2 := by
  set k : Fin N := ⟨N - 1, by omega⟩ with hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hk1 : (k.val + 1 : ℝ) = N := by
    have : k.val + 1 = N := by simp [hk]; omega
    exact_mod_cast this
  have h1 : nsc (gamma N k) = 1 := by
    have := nsc_gamma k
    rw [hk1] at this
    field_simp at this
    linarith
  obtain ⟨hlo, hhi⟩ := density_gamma_mem k
  by_contra hne
  have hlt : gamma N k < 2 := lt_of_le_of_ne hhi hne
  have := density_nsc_strictMonoOn ⟨hlo.le, hhi⟩ ⟨by norm_num, le_rfl⟩ hlt
  rw [h1, density_nsc_two] at this
  exact lt_irrefl _ this

theorem gamma_mem {N : ℕ} (k : Fin N) : gamma N k ∈ Set.Ioc (-2) 2 := by
  exact density_gamma_mem k

/-- Lemma 3.4 (a), the statements on `ρ_sc`. -/
theorem rhoSc_props :
    Continuous rhoSc ∧ (∀ x, rhoSc (-x) = rhoSc x) ∧ (∀ x, 0 ≤ rhoSc x ∧ rhoSc x ≤ 1 / π) ∧
      (∀ x, 0 < rhoSc x ↔ x ∈ Set.Ioo (-2 : ℝ) 2) ∧ AntitoneOn rhoSc (Set.Ici 0) := by
  refine ⟨density_rhoSc_continuous, fun x => by simp only [rhoSc, neg_sq],
    fun x => ⟨density_rhoSc_nonneg x, density_rhoSc_le x⟩, density_rhoSc_pos_iff, ?_⟩
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  unfold rhoSc
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (max_le_max ?_ le_rfl)) (by positivity)
  nlinarith

/-- Lemma 3.4 (a), the statements on `n_sc`. -/
theorem nsc_props :
    (∀ E, HasDerivAt nsc (rhoSc E) E) ∧ Monotone nsc ∧
      (∀ E E', |nsc E - nsc E'| ≤ |E - E'| / π) ∧ (∀ E ≤ -2, nsc E = 0) ∧
      (∀ E, 2 ≤ E → nsc E = 1) ∧ StrictMonoOn nsc (Set.Icc (-2) 2) ∧
      (∀ E, nsc (-E) = 1 - nsc E) ∧ nsc 0 = 1 / 2 := by
  refine ⟨density_nsc_hasDerivAt, density_nsc_mono, density_nsc_lipschitz,
    fun E hE => density_nsc_of_le hE, fun E hE => density_nsc_of_ge hE,
    density_nsc_strictMonoOn, density_nsc_neg, ?_⟩
  have := density_nsc_neg 0
  rw [neg_zero] at this
  linarith

end Rigidity
