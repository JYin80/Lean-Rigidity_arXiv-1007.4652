module

public import Rigidity.Ensemble.Basic
public import Rigidity.Resolvent.Basic
public import Rigidity.Probability.Moments
public import Rigidity.Probability.Split

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-!
# Calculus of partial integration over rows

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file formalizes Lemma 6.3 (F0)–(F5) of Section 6.1. `PolyGrowth f` is membership in the class
`𝒜` of (6.3), `rowsQ T` is the set `𝒬(T)` of coordinates in the rows `T`, `rowInt M T f` is the
partial integral `P_T f` of (6.4) (with value `0` on a non-integrable slice, Lemma 4.7 (c)) and
`rowNorm M T q f` is `‖f‖_{q,T}` of (6.4). Over the rows `T` the coordinates are integrated against
the product of the entry laws of the ensemble `M`; the other coordinates are held fixed.

* (F0): `PolyGrowth.add`, `PolyGrowth.mul`, `PolyGrowth.conj`, `PolyGrowth.rpow`,
  `rowInt_polyGrowth`;
* (F1): `integral_rowInt`, `rowInt_rowInt`;
* (F2): `rowInt_mul_left`, `integral_indicator_rowInt`;
* (F3): `rowNorm_prod_le`, `rowNorm_add_le`, `rowNorm_rowInt_le`;
* (F4): `rowInt_freeze`.

Every statement holds at every point `x` of the product space, not only almost surely.
-/

/-- The class `𝒜` of (6.3): measurable functions of polynomial growth in `|x|₁`. -/
def PolyGrowth {N : ℕ} (f : (Pair N → 𝕜) → ℂ) : Prop :=
  Measurable f ∧ ∃ c : ℝ, ∃ m : ℕ, ∀ x, ‖f x‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m

/-- The coordinates in the rows `T`, `𝒬(T)` (§4.3). -/
def rowsQ {N : ℕ} (T : Finset (Fin N)) : Set (Pair N) := {p | p.1.1 ∈ T ∨ p.1.2 ∈ T}

instance {N : ℕ} (T : Finset (Fin N)) : DecidablePred (· ∈ rowsQ T) := fun p => by
  unfold rowsQ; infer_instance

/-- `P_T f`: integration over the rows `T` (6.4). -/
noncomputable def rowInt {N : ℕ} (M : Ensemble 𝕜 N) (T : Finset (Fin N))
    (f : (Pair N → 𝕜) → ℂ) (x : Pair N → 𝕜) : ℂ :=
  partialInt M.law (rowsQ T) f x

/-- `‖f‖_{q,T} = (P_T |f|^q)^{1/q}` (6.4). -/
noncomputable def rowNorm {N : ℕ} (M : Ensemble 𝕜 N) (T : Finset (Fin N)) (q : ℝ)
    (f : (Pair N → 𝕜) → ℂ) (x : Pair N → 𝕜) : ℝ :=
  (partialLInt M.law (rowsQ T) (fun w => ‖f w‖ₑ ^ q) x).toReal ^ (1 / q)

/-- `Φ_*(z)² = 1/N + (Nη)⁻¹ (Im m + p/(Nη))` of (6.2). -/
noncomputable def phiStarSq {N : ℕ} (p : ℝ) (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  1 / N + 1 / (N * z.im) * ((stieltjesEmp (toMatrix x) z).im + p / (N * z.im))

/-! ### 1. The class `𝒜` -/

namespace PolyGrowth

variable {N : ℕ} {f g : (Pair N → 𝕜) → ℂ}

/-- The constant in (6.3) may be taken nonnegative. -/
private lemma exists_nonneg (hf : PolyGrowth f) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ m : ℕ, ∀ x, ‖f x‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m := by
  obtain ⟨-, c, m, h⟩ := hf
  refine ⟨|c|, abs_nonneg c, m, fun x => (h x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)

private lemma one_le_base (x : Pair N → 𝕜) : 1 ≤ 1 + ∑ p, ‖x p‖ :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- (F0): `𝒜` is closed under addition. -/
theorem add (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x + g x) := by
  obtain ⟨c, hc, m, hfb⟩ := hf.exists_nonneg
  obtain ⟨c', hc', m', hgb⟩ := hg.exists_nonneg
  refine ⟨hf.1.add hg.1, c + c', max m m', fun x => ?_⟩
  have hA := one_le_base x
  calc ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ c * (1 + ∑ p, ‖x p‖) ^ m + c' * (1 + ∑ p, ‖x p‖) ^ m' := add_le_add (hfb x) (hgb x)
    _ ≤ c * (1 + ∑ p, ‖x p‖) ^ max m m' + c' * (1 + ∑ p, ‖x p‖) ^ max m m' := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = (c + c') * (1 + ∑ p, ‖x p‖) ^ max m m' := by ring

/-- (F0): `𝒜` is closed under multiplication. -/
theorem mul (hf : PolyGrowth f) (hg : PolyGrowth g) : PolyGrowth (fun x => f x * g x) := by
  obtain ⟨c, hc, m, hfb⟩ := hf.exists_nonneg
  obtain ⟨c', hc', m', hgb⟩ := hg.exists_nonneg
  refine ⟨hf.1.mul hg.1, c * c', m + m', fun x => ?_⟩
  calc ‖f x * g x‖ = ‖f x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ (c * (1 + ∑ p, ‖x p‖) ^ m) * (c' * (1 + ∑ p, ‖x p‖) ^ m') :=
        mul_le_mul (hfb x) (hgb x) (norm_nonneg _) (by positivity)
    _ = c * c' * (1 + ∑ p, ‖x p‖) ^ (m + m') := by ring

/-- (F0): `𝒜` is closed under complex conjugation. -/
theorem conj (hf : PolyGrowth f) : PolyGrowth (fun x => starRingEnd ℂ (f x)) := by
  obtain ⟨hm, c, m, hb⟩ := hf
  refine ⟨Complex.continuous_conj.measurable.comp hm, c, m, fun x => ?_⟩
  simpa using hb x

/-- (F0): `𝒜` is closed under `f ↦ |f|^q`, `q > 0`; the function `|f|^q` is real-valued and is
viewed in `ℂ`. -/
theorem rpow (hf : PolyGrowth f) {q : ℝ} (hq : 0 < q) :
    PolyGrowth (fun x => ((‖f x‖ ^ q : ℝ) : ℂ)) := by
  obtain ⟨c, hc, m, hb⟩ := hf.exists_nonneg
  refine ⟨Complex.measurable_ofReal.comp (hf.1.norm.pow_const q),
    c ^ q, ⌈(m : ℝ) * q⌉₊, fun x => ?_⟩
  have hA := one_le_base x
  have hA0 : 0 ≤ 1 + ∑ p, ‖x p‖ := by linarith
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc ‖f x‖ ^ q ≤ (c * (1 + ∑ p, ‖x p‖) ^ m) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) (hb x) hq.le
    _ = c ^ q * (1 + ∑ p, ‖x p‖) ^ ((m : ℝ) * q) := by
        rw [Real.mul_rpow hc (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hA0]
    _ ≤ c ^ q * (1 + ∑ p, ‖x p‖) ^ (⌈(m : ℝ) * q⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _
    _ = c ^ q * (1 + ∑ p, ‖x p‖) ^ ⌈(m : ℝ) * q⌉₊ := by rw [Real.rpow_natCast]

end PolyGrowth

/-! ### 2. Moments of the entries and integrable slices -/

section Slices

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `1 + ∑ aᵢ ≤ ∏ (1 + aᵢ)` for nonnegative `aᵢ`. -/
private lemma one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
    have h2 := ha i
    nlinarith [mul_nonneg h2 h1, mul_nonneg h2 (sub_nonneg.2 ih)]

/-- `(1 + a)^m ≤ 2^m (1 + a^m)` for `a ≥ 0`. -/
private lemma one_add_pow_le {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (1 + a) ^ m ≤ 2 ^ m * (1 + a ^ m) := by
  have hp : 0 ≤ a ^ m := pow_nonneg ha m
  by_cases h : a ≤ 1
  · calc (1 + a) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + a ^ m) := le_mul_of_one_le_right (by positivity) (by linarith)
  · replace h := not_le.1 h
    calc (1 + a) ^ m ≤ (2 * a) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * a ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + a ^ m) := by gcongr; linarith

/-- Every power of `1 + |y|` is integrable against an entry law (Lemma 4.1 (a)). -/
private lemma integrable_one_add_norm_pow {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) (p : Pair N) (m : ℕ) :
    Integrable (fun y : 𝕜 => (1 + ‖y‖) ^ m) (M.law p) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hϑ' : 0 < min ϑ 1 := lt_min hϑ one_pos
    have hM' := Ensemble.Assumptions.mono M hM hϑ' (min_le_left _ _) le_rfl le_rfl le_rfl
    have hmom := (moments_bound hϑ' (min_le_right _ _) (μ := M.law p)
      (s := Real.sqrt (M.varPair p)) (Real.sqrt_nonneg _) (hM'.subexp p)
      (q := (m : ℝ)) (by exact_mod_cast hm)).1
    simp only [Real.rpow_natCast] at hmom
    have hdom : Integrable (fun y : 𝕜 => (2 : ℝ) ^ m * (1 + ‖y‖ ^ m)) (M.law p) :=
      ((integrable_const (1 : ℝ)).add hmom).const_mul _
    refine hdom.mono' ((measurable_const.add measurable_norm).pow_const m).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact one_add_pow_le (norm_nonneg y) m

variable (J : Set (Pair N)) [DecidablePred (· ∈ J)]

/-- `piMerge` is jointly measurable in `(x, y)`. -/
private lemma measurable_merge :
    Measurable (fun p : (Pair N → 𝕜) × (J → 𝕜) => piMerge J p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ J
  · have : (fun p : (Pair N → 𝕜) × (J → 𝕜) => piMerge J p.1 p.2 i) = fun p => p.2 ⟨i, h⟩ := by
      funext p
      simp [piMerge, h]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_snd
  · have : (fun p : (Pair N → 𝕜) × (J → 𝕜) => piMerge J p.1 p.2 i) = fun p => p.1 i := by
      funext p
      simp [piMerge, h]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst

/-- For fixed `x`, `y ↦ piMerge J x y` is measurable. -/
private lemma measurable_merge_right (x : Pair N → 𝕜) :
    Measurable (fun y : J → 𝕜 => piMerge J x y) :=
  (measurable_merge J).comp (measurable_const.prodMk measurable_id)

/-- The restriction to the coordinates in `J` is measure preserving. -/
private lemma measurePreserving_restrict :
    MeasurePreserving (fun (u : Pair N → 𝕜) (i : J) => u i) M.prodLaw
      (Measure.pi fun i : J => M.law i) :=
  measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd M.law (· ∈ J))

/-- The coordinates of `piMerge J x y` are bounded by those of `x` and `y`. -/
private lemma sum_norm_merge_le (x : Pair N → 𝕜) (y : J → 𝕜) :
    ∑ p, ‖piMerge J x y p‖ ≤ ∑ p, ‖x p‖ + ∑ q : J, ‖y q‖ := by
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun p => ‖piMerge J x y p‖)]
  have h1 : ∑ i : {p // p ∈ J}, ‖piMerge J x y i‖ = ∑ q : J, ‖y q‖ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [piMerge, i.2]
  have h2 : ∑ i : {p // ¬ p ∈ J}, ‖piMerge J x y i‖ ≤ ∑ p, ‖x p‖ := by
    have h3 : ∑ i : {p // ¬ p ∈ J}, ‖piMerge J x y i‖ = ∑ i : {p // ¬ p ∈ J}, ‖x i‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [piMerge, i.2]
    have h4 := Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun p => ‖x p‖)
    have h5 : 0 ≤ ∑ i : {p // p ∈ J}, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  linarith

/-- The polynomial bound along a slice `y ↦ f (piMerge J x y)`. -/
private lemma norm_merge_le {f : (Pair N → 𝕜) → ℂ} {c : ℝ} (hc : 0 ≤ c) {m : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m) (x : Pair N → 𝕜) (y : J → 𝕜) :
    ‖f (piMerge J x y)‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m := by
  have ha : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb : 0 ≤ ∑ q : J, ‖y q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : 1 + ∑ p, ‖piMerge J x y p‖ ≤ (1 + ∑ p, ‖x p‖) * (1 + ∑ q : J, ‖y q‖) := by
    nlinarith [sum_norm_merge_le J x y, mul_nonneg ha hb]
  have h2 : 1 + ∑ q : J, ‖y q‖ ≤ ∏ q : J, (1 + ‖y q‖) := by
    simpa using one_add_sum_le_prod_one_add Finset.univ (fun q : J => ‖y q‖)
      (fun _ => norm_nonneg _)
  have hs : 0 ≤ ∑ p, ‖piMerge J x y p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖f (piMerge J x y)‖ ≤ c * (1 + ∑ p, ‖piMerge J x y p‖) ^ m := hf _
    _ ≤ c * ((1 + ∑ p, ‖x p‖) * (∏ q : J, (1 + ‖y q‖))) ^ m := by
        gcongr
        exact h1.trans (by gcongr)
    _ = c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m := by
        rw [mul_pow, Finset.prod_pow]; ring

/-- The dominating function of a slice is integrable. -/
private lemma integrable_prod_one_add_pow {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) (m : ℕ) :
    Integrable (fun y : J → 𝕜 => ∏ q : J, (1 + ‖y q‖) ^ m) (Measure.pi fun p : J => M.law p) :=
  Integrable.fintype_prod (f := fun (_ : J) (z : 𝕜) => (1 + ‖z‖) ^ m)
    (μ := fun q : J => M.law q) fun q => integrable_one_add_norm_pow M hM hϑ q m

/-- Every slice of a function of `𝒜` is integrable (Lemma 6.3 (F0)). -/
private lemma integrable_slice {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (x : Pair N → 𝕜) :
    Integrable (fun y : J → 𝕜 => f (piMerge J x y)) (Measure.pi fun p : J => M.law p) := by
  obtain ⟨c, hc, m, hb⟩ := hf.exists_nonneg
  have hdom : Integrable (fun y : J → 𝕜 => c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m)
      (Measure.pi fun p : J => M.law p) :=
    (integrable_prod_one_add_pow M J hM hϑ m).const_mul _
  exact hdom.mono' (hf.1.comp (measurable_merge_right J x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => norm_merge_le J hc hb x y)

/-- Functions of `𝒜` are integrable (Lemma 6.3 (F0)). -/
private lemma integrable_polyGrowth {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) : Integrable f M.prodLaw := by
  obtain ⟨c, hc, m, hb⟩ := hf.exists_nonneg
  have hdom : Integrable (fun x : Pair N → 𝕜 => c * ∏ p, (1 + ‖x p‖) ^ m) M.prodLaw :=
    (Integrable.fintype_prod (f := fun (p : Pair N) (z : 𝕜) => (1 + ‖z‖) ^ m)
      (μ := M.law) fun p => integrable_one_add_norm_pow M hM hϑ p m).const_mul c
  refine hdom.mono' hf.1.aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hb x).trans ?_)
  have h : 1 + ∑ p, ‖x p‖ ≤ ∏ p, (1 + ‖x p‖) := by
    simpa using one_add_sum_le_prod_one_add Finset.univ (fun p => ‖x p‖) (fun _ => norm_nonneg _)
  rw [Finset.prod_pow]
  have h0 : 0 ≤ 1 + ∑ p, ‖x p‖ := (zero_le_one.trans (PolyGrowth.one_le_base x))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h m) hc

/-- The partial integral of a measurable function is measurable. -/
private lemma measurable_partialInt {f : (Pair N → 𝕜) → ℂ} (hf : Measurable f) :
    Measurable (partialInt M.law J f) :=
  (StronglyMeasurable.integral_prod_right'
    (f := fun p : (Pair N → 𝕜) × (J → 𝕜) => f (piMerge J p.1 p.2))
    (hf.comp (measurable_merge J)).stronglyMeasurable).measurable

end Slices

/-! ### 3. Fubini (F1) -/

/-- Lemma 6.3 (F1): Fubini for row integrals. -/
theorem integral_rowInt {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (T : Finset (Fin N))
    {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) :
    PolyGrowth (rowInt M T f) ∧ ∫ x, rowInt M T f x ∂M.prodLaw = ∫ x, f x ∂M.prodLaw := by
  obtain ⟨c, hc, m, hb⟩ := hf.exists_nonneg
  refine ⟨⟨measurable_partialInt M (rowsQ T) hf.1,
    c * ∫ y, ∏ q : rowsQ T, (1 + ‖y q‖) ^ m ∂Measure.pi (fun p : rowsQ T => M.law p), m,
    fun x => ?_⟩, ?_⟩
  · calc ‖rowInt M T f x‖
        ≤ ∫ y, c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : rowsQ T, (1 + ‖y q‖) ^ m
          ∂Measure.pi (fun p : rowsQ T => M.law p) :=
          norm_integral_le_of_norm_le
            ((integrable_prod_one_add_pow M (rowsQ T) hM hϑ m).const_mul _)
            (Filter.Eventually.of_forall fun y => norm_merge_le (rowsQ T) hc hb x y)
      _ = c * (∫ y, ∏ q : rowsQ T, (1 + ‖y q‖) ^ m ∂Measure.pi (fun p : rowsQ T => M.law p)) *
          (1 + ∑ p, ‖x p‖) ^ m := by
          rw [integral_const_mul]; ring
  · exact (integral_partialInt M.law (rowsQ T) (integrable_polyGrowth M hM hϑ hf)).2.2

/-- (F0): the partial integral `P_T f` of a function of `𝒜` lies in `𝒜`. -/
theorem rowInt_polyGrowth {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (T : Finset (Fin N))
    {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) : PolyGrowth (rowInt M T f) :=
  (integral_rowInt M hM hϑ T hf).1

/-! ### 4. Factors independent of the rows (F2) -/

/-- Lemma 6.3 (F2): a factor `g` not depending on the rows `T` comes out of `P_T`. -/
theorem rowInt_mul_left {N : ℕ} (M : Ensemble 𝕜 N) (T : Finset (Fin N))
    {g : (Pair N → 𝕜) → ℂ} (hg : ∀ x x', (∀ p, p ∉ rowsQ T → x p = x' p) → g x = g x')
    (f : (Pair N → 𝕜) → ℂ) (x : Pair N → 𝕜) :
    rowInt M T (fun w => g w * f w) x = g x * rowInt M T f x := by
  unfold rowInt partialInt
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have : g (piMerge (rowsQ T) x y) = g x := hg _ _ fun p hp => by simp [piMerge, hp]
  simp only [this]

/-! ### 5. Irrelevant coordinates (F5) -/

section Irrelevant

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `𝒬` is monotone in the rows. -/
private lemma rowsQ_mono {T₁ T : Finset (Fin N)} (h : T₁ ⊆ T) : rowsQ T₁ ⊆ rowsQ T := by
  intro p hp
  simp only [rowsQ, Set.mem_ofPred_eq] at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (h hp)
  · exact Or.inr (h hp)

/-- The partial integral over `J` as an integral over the whole space. -/
private lemma partialInt_eq_integral (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    {f : (Pair N → 𝕜) → ℂ} (hf : Measurable f) (x : Pair N → 𝕜) :
    partialInt M.law J f x = ∫ u, f (piMerge J x (fun i : J => u i)) ∂M.prodLaw := by
  unfold partialInt
  have hmp := measurePreserving_restrict M J
  calc ∫ y, f (piMerge J x y) ∂Measure.pi (fun i : J => M.law i)
      = ∫ y, f (piMerge J x y)
          ∂(Measure.map (fun (u : Pair N → 𝕜) (i : J) => u i) M.prodLaw) := by rw [hmp.map_eq]
    _ = ∫ u, f (piMerge J x (fun i : J => u i)) ∂M.prodLaw :=
        integral_map hmp.measurable.aemeasurable
          (hf.comp (measurable_merge_right J x)).aestronglyMeasurable

end Irrelevant

/-! ### 5b. Iterated partial integrals (F1) -/

section Tower

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- Lemma 6.3 (F1): for `T₁ ⊆ T`, `P_T P_{T₁} f = P_T f`. -/
theorem rowInt_rowInt {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    {T₁ T : Finset (Fin N)} (hT : T₁ ⊆ T) {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) :
    rowInt M T (rowInt M T₁ f) = rowInt M T f := by
  funext x
  have hJ : rowsQ T₁ ⊆ rowsQ T := rowsQ_mono hT
  have hr := measurePreserving_restrict M (rowsQ T)
  have hrm : Measurable (fun (u : Pair N → 𝕜) (i : rowsQ T) => u i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  set h : (Pair N → 𝕜) → ℂ := fun u => f (piMerge (rowsQ T) x (fun i : rowsQ T => u i)) with hh_def
  have hh : Measurable h := hf.1.comp ((measurable_merge_right (rowsQ T) x).comp hrm)
  have hhint : Integrable h M.prodLaw :=
    (hr.integrable_comp (integrable_slice M (rowsQ T) hM hϑ hf x).aestronglyMeasurable).2
      (integrable_slice M (rowsQ T) hM hϑ hf x)
  have key : ∀ u : Pair N → 𝕜, partialInt M.law (rowsQ T₁) h u =
      partialInt M.law (rowsQ T₁) f (piMerge (rowsQ T) x (fun i : rowsQ T => u i)) := by
    intro u
    unfold partialInt
    congr 1
    funext w
    simp only [hh_def]
    congr 1
    funext i
    by_cases hi₁ : i ∈ rowsQ T₁
    · have hi : i ∈ rowsQ T := hJ hi₁
      simp [piMerge, hi₁, hi]
    · by_cases hi : i ∈ rowsQ T
      · simp [piMerge, hi₁, hi]
      · simp [piMerge, hi₁, hi]
  have hG : Measurable fun y : rowsQ T → 𝕜 =>
      partialInt M.law (rowsQ T₁) f (piMerge (rowsQ T) x y) :=
    (measurable_partialInt M (rowsQ T₁) hf.1).comp (measurable_merge_right (rowsQ T) x)
  calc rowInt M T (rowInt M T₁ f) x
      = ∫ y, partialInt M.law (rowsQ T₁) f (piMerge (rowsQ T) x y)
          ∂Measure.pi (fun p : rowsQ T => M.law p) := rfl
    _ = ∫ u, partialInt M.law (rowsQ T₁) f (piMerge (rowsQ T) x (fun i : rowsQ T => u i))
          ∂M.prodLaw := by
        rw [← hr.map_eq]
        exact integral_map hr.measurable.aemeasurable
          (by rw [hr.map_eq]; exact hG.aestronglyMeasurable)
    _ = ∫ u, partialInt M.law (rowsQ T₁) h u ∂M.prodLaw := by simp only [key]
    _ = ∫ u, h u ∂M.prodLaw := (integral_partialInt M.law (rowsQ T₁) hhint).2.2
    _ = rowInt M T f x := (partialInt_eq_integral M (rowsQ T) hf.1 x).symm

end Tower

/-! ### 6. Hölder, Minkowski and Jensen (F3) -/

section Norms

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `‖f‖_{q,T}` as an element of `[0, ∞]`. -/
private noncomputable def rowENorm (T : Finset (Fin N)) (q : ℝ) (f : (Pair N → 𝕜) → ℂ)
    (x : Pair N → 𝕜) : ℝ≥0∞ :=
  (partialLInt M.law (rowsQ T) (fun w => ‖f w‖ₑ ^ q) x) ^ (1 / q)

private lemma rowNorm_eq_toReal (T : Finset (Fin N)) (q : ℝ) (f : (Pair N → 𝕜) → ℂ)
    (x : Pair N → 𝕜) : rowNorm M T q f x = (rowENorm M T q f x).toReal := by
  unfold rowNorm rowENorm
  exact ENNReal.toReal_rpow _ _

/-- For `q > 0`, the `q`-th moment of a slice of a function of `𝒜` is finite. -/
private lemma lintegral_slice_lt_top {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) (J : Set (Pair N)) [DecidablePred (· ∈ J)] {f : (Pair N → 𝕜) → ℂ}
    (hf : PolyGrowth f) {q : ℝ} (hq : 0 < q) (x : Pair N → 𝕜) :
    ∫⁻ y, ‖f (piMerge J x y)‖ₑ ^ q ∂Measure.pi (fun p : J => M.law p) < ⊤ := by
  have h := ((integrable_slice M J hM hϑ (hf.rpow hq) x).norm).lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun y => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le, ofReal_norm]

private lemma rowENorm_lt_top {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (T : Finset (Fin N)) {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) {q : ℝ} (hq : 0 < q)
    (x : Pair N → 𝕜) : rowENorm M T q f x < ⊤ :=
  ENNReal.rpow_lt_top_of_nonneg (by positivity) (lintegral_slice_lt_top M hM hϑ _ hf hq x).ne

/-- Monotonicity of the `L^q` norm on a probability space. -/
private lemma lintegral_rpow_le_of_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {g : α → ℂ} (hg : AEStronglyMeasurable g ν) {q q' : ℝ} (hq : 0 < q)
    (hqq' : q ≤ q') :
    (∫⁻ y, ‖g y‖ₑ ^ q ∂ν) ^ (1 / q) ≤ (∫⁻ y, ‖g y‖ₑ ^ q' ∂ν) ^ (1 / q') := by
  have hq' : 0 < q' := hq.trans_le hqq'
  have h1 := eLpNorm_le_eLpNorm_of_exponent_le (f := g) (μ := ν) (p := ENNReal.ofReal q)
    (q := ENNReal.ofReal q') (ENNReal.ofReal_le_ofReal hqq')
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq').ne' ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal hq'.le] at h1
  exact h1

/-- The norm of a finite product is the product of the norms. -/
private lemma enorm_finset_prod {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ‖∏ i ∈ s, a i‖ₑ = ∏ i ∈ s, ‖a i‖ₑ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, enorm_mul, ih]

/-- Lemma 6.3 (F3), Hölder: for `q, q₁, …, qₙ ∈ [1, ∞)` with `∑ 1/qᵢ = 1/q`,
`‖f₁ ⋯ fₙ‖_{q,T} ≤ ∏ ‖fᵢ‖_{qᵢ,T}` pointwise. -/
theorem rowNorm_prod_le {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (T : Finset (Fin N))
    {ι : Type*} (s : Finset ι) (f : ι → (Pair N → 𝕜) → ℂ) {q : ℝ} (qs : ι → ℝ)
    (hq : 1 ≤ q) (hqs : ∀ i ∈ s, 1 ≤ qs i) (hsum : ∑ i ∈ s, 1 / qs i = 1 / q)
    (hf : ∀ i ∈ s, PolyGrowth (f i)) (x : Pair N → 𝕜) :
    rowNorm M T q (fun w => ∏ i ∈ s, f i w) x ≤ ∏ i ∈ s, rowNorm M T (qs i) (f i) x := by
  have hq0 : 0 < q := by linarith
  have hqs0 : ∀ i ∈ s, 0 < qs i := fun i hi => by linarith [hqs i hi]
  have hFm : ∀ i ∈ s, Measurable fun y : rowsQ T → 𝕜 => ‖f i (piMerge (rowsQ T) x y)‖ₑ :=
    fun i hi => ((hf i hi).1.comp (measurable_merge_right (rowsQ T) x)).enorm
  have hp : ∑ i ∈ s, q / qs i = 1 := by
    have : ∑ i ∈ s, q / qs i = q * ∑ i ∈ s, 1 / qs i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsum]
    field_simp
  have key : ∫⁻ y, ‖∏ i ∈ s, f i (piMerge (rowsQ T) x y)‖ₑ ^ q
        ∂Measure.pi (fun p : rowsQ T => M.law p) ≤
      ∏ i ∈ s, (∫⁻ y, ‖f i (piMerge (rowsQ T) x y)‖ₑ ^ qs i
        ∂Measure.pi (fun p : rowsQ T => M.law p)) ^ (q / qs i) := by
    have h1 := ENNReal.lintegral_prod_norm_pow_le s
      (μ := Measure.pi (fun p : rowsQ T => M.law p))
      (f := fun i y => ‖f i (piMerge (rowsQ T) x y)‖ₑ ^ qs i)
      (fun i hi => ((hFm i hi).pow_const _).aemeasurable) (p := fun i => q / qs i) hp
      (fun i hi => div_nonneg hq0.le (hqs0 i hi).le)
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) h1
    rw [enorm_finset_prod, ← ENNReal.prod_rpow_of_nonneg hq0.le]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [(hqs0 i hi).ne']
  have key2 : rowENorm M T q (fun w => ∏ i ∈ s, f i w) x ≤
      ∏ i ∈ s, rowENorm M T (qs i) (f i) x := by
    unfold rowENorm partialLInt
    calc (∫⁻ y, ‖∏ i ∈ s, f i (piMerge (rowsQ T) x y)‖ₑ ^ q
            ∂Measure.pi (fun p : rowsQ T => M.law p)) ^ (1 / q)
        ≤ (∏ i ∈ s, (∫⁻ y, ‖f i (piMerge (rowsQ T) x y)‖ₑ ^ qs i
            ∂Measure.pi (fun p : rowsQ T => M.law p)) ^ (q / qs i)) ^ (1 / q) :=
          ENNReal.rpow_le_rpow key (by positivity)
      _ = ∏ i ∈ s, (∫⁻ y, ‖f i (piMerge (rowsQ T) x y)‖ₑ ^ qs i
            ∂Measure.pi (fun p : rowsQ T => M.law p)) ^ (1 / qs i) := by
          rw [← ENNReal.prod_rpow_of_nonneg (by positivity)]
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp [(hqs0 i hi).ne']
  have hfin : ∏ i ∈ s, rowENorm M T (qs i) (f i) x ≠ ⊤ :=
    ENNReal.prod_ne_top fun i hi => (rowENorm_lt_top M hM hϑ T (hf i hi) (hqs0 i hi) x).ne
  rw [rowNorm_eq_toReal]
  calc (rowENorm M T q (fun w => ∏ i ∈ s, f i w) x).toReal
      ≤ (∏ i ∈ s, rowENorm M T (qs i) (f i) x).toReal := ENNReal.toReal_mono hfin key2
    _ = ∏ i ∈ s, rowNorm M T (qs i) (f i) x := by
        rw [ENNReal.toReal_prod]
        exact Finset.prod_congr rfl fun i _ => (rowNorm_eq_toReal M T _ _ x).symm

/-- Lemma 6.3 (F3), Minkowski: `‖f + g‖_{q,T} ≤ ‖f‖_{q,T} + ‖g‖_{q,T}` for `q ≥ 1`. -/
theorem rowNorm_add_le {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (T : Finset (Fin N))
    {f g : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (hg : PolyGrowth g) {q : ℝ} (hq : 1 ≤ q)
    (x : Pair N → 𝕜) :
    rowNorm M T q (fun w => f w + g w) x ≤ rowNorm M T q f x + rowNorm M T q g x := by
  have hq0 : 0 < q := by linarith
  have h1 : rowENorm M T q (fun w => f w + g w) x ≤ rowENorm M T q f x + rowENorm M T q g x := by
    unfold rowENorm partialLInt
    calc (∫⁻ y, ‖f (piMerge (rowsQ T) x y) + g (piMerge (rowsQ T) x y)‖ₑ ^ q
            ∂Measure.pi (fun p : rowsQ T => M.law p)) ^ (1 / q)
        ≤ (∫⁻ y, (‖f (piMerge (rowsQ T) x y)‖ₑ + ‖g (piMerge (rowsQ T) x y)‖ₑ) ^ q
            ∂Measure.pi (fun p : rowsQ T => M.law p)) ^ (1 / q) := by
          refine ENNReal.rpow_le_rpow (lintegral_mono fun y => ?_) (by positivity)
          exact ENNReal.rpow_le_rpow (enorm_add_le _ _) hq0.le
      _ ≤ _ := ENNReal.lintegral_Lp_add_le
          (f := fun y => ‖f (piMerge (rowsQ T) x y)‖ₑ) (g := fun y => ‖g (piMerge (rowsQ T) x y)‖ₑ)
          ((hf.1.comp (measurable_merge_right (rowsQ T) x)).enorm.aemeasurable)
          ((hg.1.comp (measurable_merge_right (rowsQ T) x)).enorm.aemeasurable) hq
  have hfin : rowENorm M T q f x + rowENorm M T q g x ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨(rowENorm_lt_top M hM hϑ T hf hq0 x).ne,
      (rowENorm_lt_top M hM hϑ T hg hq0 x).ne⟩
  rw [rowNorm_eq_toReal, rowNorm_eq_toReal, rowNorm_eq_toReal]
  calc _ ≤ (rowENorm M T q f x + rowENorm M T q g x).toReal := ENNReal.toReal_mono hfin h1
    _ = _ := ENNReal.toReal_add (rowENorm_lt_top M hM hϑ T hf hq0 x).ne
        (rowENorm_lt_top M hM hϑ T hg hq0 x).ne

/-- Lemma 6.3 (F3), Jensen: for `T₁ ⊆ T` and `q ≥ 1`, `‖P_{T₁} f‖_{q,T} ≤ ‖f‖_{q,T}`. -/
theorem rowNorm_rowInt_le {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) {T₁ T : Finset (Fin N)} (hT : T₁ ⊆ T)
    {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) {q : ℝ} (hq : 1 ≤ q) (x : Pair N → 𝕜) :
    rowNorm M T q (rowInt M T₁ f) x ≤ rowNorm M T q f x := by
  have hq0 : 0 < q := by linarith
  have hjensen : ∀ w : Pair N → 𝕜, ‖rowInt M T₁ f w‖ₑ ^ q ≤
      partialLInt M.law (rowsQ T₁) (fun w => ‖f w‖ₑ ^ q) w := by
    intro w
    have h1 := lintegral_rpow_le_of_le (Measure.pi fun p : rowsQ T₁ => M.law p)
      (g := fun y => f (piMerge (rowsQ T₁) w y))
      (hf.1.comp (measurable_merge_right (rowsQ T₁) w)).aestronglyMeasurable one_pos hq
    simp only [ENNReal.rpow_one, div_one] at h1
    calc ‖rowInt M T₁ f w‖ₑ ^ q
        ≤ (∫⁻ y, ‖f (piMerge (rowsQ T₁) w y)‖ₑ ∂Measure.pi fun p : rowsQ T₁ => M.law p) ^ q :=
          ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) hq0.le
      _ ≤ ((∫⁻ y, ‖f (piMerge (rowsQ T₁) w y)‖ₑ ^ q ∂Measure.pi fun p : rowsQ T₁ => M.law p) ^
            (1 / q)) ^ q := ENNReal.rpow_le_rpow h1 hq0.le
      _ = ∫⁻ y, ‖f (piMerge (rowsQ T₁) w y)‖ₑ ^ q ∂Measure.pi fun p : rowsQ T₁ => M.law p := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
  have hmeas : Measurable (fun w : Pair N → 𝕜 => ‖f w‖ₑ ^ q) := hf.1.enorm.pow_const q
  have h2 : partialLInt M.law (rowsQ T) (fun w => ‖rowInt M T₁ f w‖ₑ ^ q) x ≤
      partialLInt M.law (rowsQ T) (fun w => ‖f w‖ₑ ^ q) x :=
    calc partialLInt M.law (rowsQ T) (fun w => ‖rowInt M T₁ f w‖ₑ ^ q) x
        ≤ partialLInt M.law (rowsQ T)
            (partialLInt M.law (rowsQ T₁) (fun w => ‖f w‖ₑ ^ q)) x :=
          lintegral_mono fun y => hjensen _
      _ = partialLInt M.law (rowsQ T) (fun w => ‖f w‖ₑ ^ q) x :=
          congrFun (partialLInt_tower M.law (rowsQ T) (rowsQ_mono hT) hmeas) x
  unfold rowNorm
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (lintegral_slice_lt_top M hM hϑ _ hf hq0 x).ne h2) (by positivity)

end Norms

/-! ### 7. Freezing (F4) -/

/-- Lemma 6.3 (F4): for fixed `x`, on the probability space `(𝕜^{𝒬(T)}, 𝒫_{𝒬(T)})` the coordinate
functions `y ↦ y_p`, `p ∈ 𝒬(T)`, are independent with the laws of the entries, `P_T f (x)` is the
integral of `y ↦ f(x_{𝒬(T)ᶜ}, y)`, and `‖f‖_{q,T}(x)` is the `L^q`-norm of this function. -/
theorem rowInt_freeze {N : ℕ} (M : Ensemble 𝕜 N) (T : Finset (Fin N))
    {f : (Pair N → 𝕜) → ℂ} (hf : Measurable f) (x : Pair N → 𝕜) :
    rowInt M T f x = ∫ y, f (piMerge (rowsQ T) x y) ∂Measure.pi (fun p : rowsQ T => M.law p) ∧
      iIndepFun (fun (p : rowsQ T) (y : rowsQ T → 𝕜) => y p)
        (Measure.pi fun p : rowsQ T => M.law p) ∧
      (∀ p : rowsQ T, (Measure.pi fun p : rowsQ T => M.law p).map (fun y : rowsQ T → 𝕜 => y p) =
        M.law p) ∧
      ∀ q : ℝ, 1 ≤ q → rowNorm M T q f x =
        (eLpNorm (fun y => f (piMerge (rowsQ T) x y)) (ENNReal.ofReal q)
          (Measure.pi fun p : rowsQ T => M.law p)).toReal := by
  refine ⟨rfl, iIndepFun_pi (μ := fun p : rowsQ T => M.law p) (X := fun _ (z : 𝕜) => z)
    fun _ => aemeasurable_id,
    fun p => (measurePreserving_eval (fun p : rowsQ T => M.law p) p).map_eq, fun q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  have hm : AEStronglyMeasurable (fun y : rowsQ T → 𝕜 => f (piMerge (rowsQ T) x y))
      (Measure.pi fun p : rowsQ T => M.law p) :=
    (hf.comp (measurable_merge_right (rowsQ T) x)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top
    hm, ENNReal.toReal_ofReal hq0.le, ← ENNReal.toReal_rpow]
  rfl

/-! ### 8. Events not depending on the rows (F2) -/

/-- Lemma 6.3 (F2): `𝔼[1_Ξ f] = 𝔼[1_Ξ P_T f]` for an event `Ξ` not depending on the rows `T`. -/
theorem integral_indicator_rowInt {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (T : Finset (Fin N))
    {Ξ : Set (Pair N → 𝕜)} (hΞ : MeasurableSet Ξ)
    (hnd : ∀ x x', (∀ p, p ∉ rowsQ T → x p = x' p) → (x ∈ Ξ ↔ x' ∈ Ξ))
    {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) :
    ∫ x in Ξ, f x ∂M.prodLaw = ∫ x in Ξ, rowInt M T f x ∂M.prodLaw := by
  classical
  set g : (Pair N → 𝕜) → ℂ := Ξ.indicator fun _ => 1 with hg_def
  have hgm : Measurable g := measurable_const.indicator hΞ
  have hgC : ∀ x, ‖g x‖ ≤ 1 := fun x => by by_cases h : x ∈ Ξ <;> simp [g, h]
  have hg : ∀ x x', (∀ p, p ∉ rowsQ T → x p = x' p) → g x = g x' := fun x x' h => by
    have := hnd x x' h
    by_cases h1 : x ∈ Ξ
    · simp [g, h1, this.1 h1]
    · have h2 : x' ∉ Ξ := fun h2 => h1 (this.2 h2)
      simp [g, h1, h2]
  have e : ∀ F : (Pair N → 𝕜) → ℂ, (fun x => g x * F x) = Ξ.indicator F := by
    intro F
    funext x
    by_cases h : x ∈ Ξ <;> simp [g, h]
  have h := (integral_mul_partialInt M.law (rowsQ T) (integrable_polyGrowth M hM hϑ hf) hgm hgC
    hg).2
  rw [← integral_indicator hΞ, ← integral_indicator hΞ, ← e, ← e]
  exact h

end Rigidity
