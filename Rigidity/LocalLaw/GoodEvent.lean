import Rigidity.Ensemble.Basic
import Rigidity.Ensemble.Moments
import Rigidity.Probability.Decoupling
import Rigidity.Probability.Moments
import Rigidity.Probability.Split
import Rigidity.Resolvent.Basic
import Rigidity.Resolvent.Minor
import Rigidity.Resolvent.Schur
import Rigidity.Spectrum.Measurable
import Rigidity.Stability.Equations

/-!
# The good event at a fixed spectral parameter

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For an ensemble `ν ∈ ℰ_N(ϑ, δ₋, δ₊, C₀)` with product law `ℙ` on `Ω = 𝕜^{𝒫_N}`, this file proves:
* Lemma 4.1, ensemble form: `𝔼|h_ij|^q ≤ (C_ϑ q)^{q/ϑ} σ_ij^q` and
  `ℙ(∃ (i, j) ∈ 𝒫_N, |x_ij| > T σ_ij) ≤ N² ϑ⁻¹ e^{-T^ϑ}` for `T ≥ 1`;
* Definition 4.3: the good event `𝒢_κ(z)`, given by the conditions (G1)–(G4), and the control
  parameter `Ψ_m` of (4.10);
* Lemma 4.4: for `N ≥ 3`, `Im z > 0` and `κ ≥ κ_ϑ + log N`, the event `𝒢_κ(z)` is closed,
  `ℙ(𝒢_κ(z)ᶜ) ≤ 46 ϑ⁻¹ N⁴ e^{-κ}`, and on `𝒢_κ(z)` the bounds (4.11)–(4.13) hold.

The probability bound applies the large deviation bounds (4.3)–(4.6) of Lemma 4.2 on the slices
of the product law in the coordinates of one or two rows (Lemma 4.7 (b)): on such a slice the
entries of `G^{(i)}` and `G^{(ij)}` are constants and the entries of the rows are independent
coordinates.  The consequences (4.11)–(4.13) combine (G1)–(G4) with the Ward identity for the
minors (Lemma 3.5 (b)), the expansions (I2) and the bound (I5) of Lemma 3.6.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-! ### 1. Single entries -/

/-- The entry `h_kl` as a function of the coordinate `x_{{k,l}}` (Definition 2.2). -/
private def goodEvent_ent {N : ℕ} (k l : Fin N) (y : 𝕜) : 𝕜 :=
  if k < l then y else if l < k then star y else ((RCLike.re y : ℝ) : 𝕜)

private lemma goodEvent_toMatrix_apply {N : ℕ} (x : Pair N → 𝕜) (k l : Fin N) :
    toMatrix x k l = goodEvent_ent k l (x (Pair.mk' k l)) := rfl

private lemma goodEvent_norm_ent_le {N : ℕ} (k l : Fin N) (y : 𝕜) :
    ‖goodEvent_ent k l y‖ ≤ ‖y‖ := by
  unfold goodEvent_ent
  split_ifs
  · exact le_rfl
  · rw [norm_star]
  · rw [RCLike.norm_ofReal]
    exact RCLike.abs_re_le_norm y

private lemma goodEvent_continuous_ent {N : ℕ} (k l : Fin N) :
    Continuous (goodEvent_ent (𝕜 := 𝕜) k l) := by
  unfold goodEvent_ent
  split_ifs
  · exact continuous_id
  · exact continuous_star
  · exact RCLike.continuous_ofReal.comp RCLike.continuous_re

/-- Almost surely, `h_kl` is the coordinate `x_{{k,l}}` or its conjugate (real diagonal). -/
private lemma goodEvent_ent_ae {N : ℕ} {M : Ensemble 𝕜 N} (hR : M.DiagReal) (k l : Fin N) :
    ∀ᵐ y ∂M.law (Pair.mk' k l), goodEvent_ent k l y = if l < k then star y else y := by
  by_cases hkl : k < l
  · refine Eventually.of_forall fun y => ?_
    simp [goodEvent_ent, hkl, not_lt_of_gt hkl]
  by_cases hlk : l < k
  · refine Eventually.of_forall fun y => ?_
    simp [goodEvent_ent, hkl, hlk]
  have h : k = l := le_antisymm (not_lt.1 hlk) (not_lt.1 hkl)
  subst h
  filter_upwards [hR k] with y hy
  simp only [goodEvent_ent, lt_irrefl, ite_false]
  exact RCLike.ext (by simp) (by simp [hy])

/-- `‖toC y‖ = ‖y‖`. -/
private lemma goodEvent_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

private lemma goodEvent_toC_star (y : 𝕜) : toC (star y) = starRingEnd ℂ (toC y) := by
  apply Complex.ext <;> simp [toC]

private lemma goodEvent_continuous_toC : Continuous (toC : 𝕜 → ℂ) := by
  have : (toC : 𝕜 → ℂ) =
      fun y => ((RCLike.re y : ℝ) : ℂ) + ((RCLike.im y : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [toC]
  rw [this]
  fun_prop

/-- The Bochner integral commutes with `toC`. -/
private lemma goodEvent_integral_toC {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → 𝕜} (hf : Integrable f μ) : ∫ a, toC (f a) ∂μ = toC (∫ a, f a ∂μ) := by
  have hf' : Integrable (fun a => toC (f a)) μ :=
    hf.norm.mono' (goodEvent_continuous_toC.comp_aestronglyMeasurable hf.1)
      (Eventually.of_forall fun a => by rw [goodEvent_norm_toC])
  apply Complex.ext
  · have h1 := integral_re hf'
    have h2 := integral_re hf
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    change ∫ a, RCLike.re (f a) ∂μ = RCLike.re (∫ a, f a ∂μ)
    exact h2
  · have h1 := integral_im hf'
    have h2 := integral_im hf
    simp only [RCLike.im_to_complex] at h1
    rw [← h1]
    change ∫ a, RCLike.im (f a) ∂μ = RCLike.im (∫ a, f a ∂μ)
    exact h2

private lemma goodEvent_var_nonneg {N : ℕ} (M : Ensemble 𝕜 N) (k l : Fin N) : 0 ≤ M.var k l :=
  integral_nonneg fun _ => by positivity

private lemma goodEvent_var_comm {N : ℕ} (M : Ensemble 𝕜 N) (k l : Fin N) :
    M.var k l = M.var l k := by
  unfold Ensemble.var
  rw [Pair.mk'_comm]

private lemma goodEvent_sd_sq {N : ℕ} (M : Ensemble 𝕜 N) (k l : Fin N) :
    M.sd k l ^ 2 = M.var k l :=
  Real.sq_sqrt (goodEvent_var_nonneg M k l)

/-- Mean of an entry under the law of its coordinate (Remark 4.1). -/
private lemma goodEvent_integral_ent {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (k l : Fin N) :
    ∫ y, goodEvent_ent k l y ∂M.law (Pair.mk' k l) = 0 := by
  rw [integral_congr_ae (goodEvent_ent_ae h.diagReal k l)]
  split_ifs
  · simp only [RCLike.star_def]
    rw [integral_conj, h.meanZero, map_zero]
  · exact h.meanZero _

/-- Second moment of an entry under the law of its coordinate (Remark 4.1). -/
private lemma goodEvent_integral_norm_ent {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (k l : Fin N) :
    ∫ y, ‖goodEvent_ent k l y‖ ^ 2 ∂M.law (Pair.mk' k l) = M.var k l := by
  have hae : ∀ᵐ y ∂M.law (Pair.mk' k l), ‖goodEvent_ent k l y‖ ^ 2 = ‖y‖ ^ 2 := by
    filter_upwards [goodEvent_ent_ae h.diagReal k l] with y hy
    rw [hy]
    split_ifs <;> simp
  rw [integral_congr_ae hae]
  rfl

/-- Tail of an entry under the law of its coordinate (Remark 4.1). -/
private lemma goodEvent_tail_ent {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (k l : Fin N) {y : ℝ} (hy : 1 ≤ y) :
    M.law (Pair.mk' k l) {w | y * M.sd k l < ‖goodEvent_ent k l w‖} ≤
      ENNReal.ofReal (ϑ⁻¹ * Real.exp (-y ^ ϑ)) := by
  refine (measure_mono fun w hw => ?_).trans (h.subexp (Pair.mk' k l) y hy)
  exact lt_of_lt_of_le hw (goodEvent_norm_ent_le k l w)

private lemma goodEvent_integrable_ent {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (k l : Fin N) :
    Integrable (goodEvent_ent k l) (M.law (Pair.mk' k l)) := by
  have h1 := Ensemble.Assumptions.integrable_norm_pow M h hϑ (Pair.mk' k l) 1
  refine h1.mono' (goodEvent_continuous_ent k l).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  simpa using goodEvent_norm_ent_le k l y

/-- Lemma 4.1, ensemble form: moments of the entries. -/
theorem Ensemble.Assumptions.moment_le {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (p : Pair N) {q : ℝ} (hq : 1 ≤ q) :
    ∫ y, ‖y‖ ^ q ∂M.law p ≤ (cTheta ϑ⁻¹ * q) ^ (ϑ⁻¹ * q) * Real.sqrt (M.varPair p) ^ q := by
  have hb := (moments_bound hϑ hϑ1 (μ := M.law p) (Real.sqrt_nonneg (M.varPair p))
    (fun x hx => h.subexp p x hx) hq).2
  rwa [div_eq_inv_mul] at hb

/-- Lemma 4.1, ensemble form: the entry tail event. -/
theorem Ensemble.Assumptions.prodLaw_large_entry {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) {T : ℝ} (hT : 1 ≤ T) :
    M.prodLaw {x | ∃ p, T * Real.sqrt (M.varPair p) < ‖x p‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 * ϑ⁻¹ * Real.exp (-T ^ ϑ)) := by
  set c : ℝ := ϑ⁻¹ * Real.exp (-T ^ ϑ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hset : {x : Pair N → 𝕜 | ∃ p, T * Real.sqrt (M.varPair p) < ‖x p‖} =
      ⋃ p, Function.eval p ⁻¹' {y : 𝕜 | T * Real.sqrt (M.varPair p) < ‖y‖} := by
    ext x
    simp
  have hp : ∀ p, M.prodLaw (Function.eval p ⁻¹' {y : 𝕜 | T * Real.sqrt (M.varPair p) < ‖y‖}) ≤
      ENNReal.ofReal c := by
    intro p
    have hm : MeasurableSet {y : 𝕜 | T * Real.sqrt (M.varPair p) < ‖y‖} :=
      measurableSet_lt measurable_const measurable_norm
    rw [Ensemble.prodLaw, (measurePreserving_eval M.law p).measure_preimage hm.nullMeasurableSet]
    exact h.subexp p T hT
  have hcard : (Fintype.card (Pair N) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : Fintype.card (Pair N) ≤ Fintype.card (Fin N × Fin N) := Fintype.card_subtype_le _
    rw [Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast (show Fintype.card (Pair N) ≤ N ^ 2 by rw [sq]; exact this)
  rw [hset]
  calc M.prodLaw (⋃ p, Function.eval p ⁻¹' {y : 𝕜 | T * Real.sqrt (M.varPair p) < ‖y‖})
      ≤ ∑ p, M.prodLaw (Function.eval p ⁻¹' {y : 𝕜 | T * Real.sqrt (M.varPair p) < ‖y‖}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Pair N, ENNReal.ofReal c := Finset.sum_le_sum fun p _ => hp p
    _ = ENNReal.ofReal (Fintype.card (Pair N) * c) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * ϑ⁻¹ * Real.exp (-T ^ ϑ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hcard hc0

/-! ### 2. The good event and the control parameter -/

/-- The good event `𝒢_κ(z)` of Definition 4.3 (`a = 1/ϑ`). -/
def goodEvent {N : ℕ} (M : Ensemble 𝕜 N) (a κ : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  {x | (∀ k l, ‖toMatrix x k l‖ ≤ κ ^ a * M.sd k l) ∧
    (∀ i, ‖selfZ (toMatrix x) M.varMatrix z i‖ ≤ lossL2 a κ N *
      Real.sqrt (∑ k, ∑ l, M.var i k * ‖greenT (toMatrix x) {i} z k l‖ ^ 2 * M.var i l)) ∧
    (∀ i j, i ≠ j →
      ‖∑ k, toC (toMatrix x i k) * greenT (toMatrix x) {i} z k j‖ ≤
          lossL a κ * Real.sqrt (∑ k, M.var i k * ‖greenT (toMatrix x) {i} z k j‖ ^ 2) ∧
        ‖∑ k, greenT (toMatrix x) {i} z j k * toC (toMatrix x k i)‖ ≤
          lossL a κ * Real.sqrt (∑ k, ‖greenT (toMatrix x) {i} z j k‖ ^ 2 * M.var k i)) ∧
    (∀ i j, i ≠ j →
      ‖∑ k, ∑ l, toC (toMatrix x i k) * greenT (toMatrix x) {i, j} z k l * toC (toMatrix x l j)‖ ≤
        lossL a κ ^ 2 * Real.sqrt (∑ k, ∑ l, M.var i k * ‖greenT (toMatrix x) {i, j} z k l‖ ^ 2 *
          M.var l j))}

/-- `Ψ_m = √(Im m/(Nη)) + 1/(Nη) + N^{-1/2}` of (4.10). -/
noncomputable def ctrlPsiM {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  Real.sqrt ((stieltjesEmp (toMatrix x) z).im / (N * z.im)) + 1 / (N * z.im) + 1 / Real.sqrt N

/-! ### 3. Rows, slices and independent coordinates -/

/-- The coordinates in the rows `T`, `𝒬(T) = {(i, j) ∈ 𝒫_N : {i, j} ∩ T ≠ ∅}` (§4.3). -/
private def goodEvent_rows {N : ℕ} (T : Finset (Fin N)) : Set (Pair N) :=
  {p | p.1.1 ∈ T ∨ p.1.2 ∈ T}

private instance goodEvent_rows_dec {N : ℕ} (T : Finset (Fin N)) :
    DecidablePred (· ∈ goodEvent_rows T) :=
  fun p => inferInstanceAs (Decidable (p.1.1 ∈ T ∨ p.1.2 ∈ T))

private lemma goodEvent_mem_rows {N : ℕ} (T : Finset (Fin N)) (k l : Fin N) :
    Pair.mk' k l ∈ goodEvent_rows T ↔ k ∈ T ∨ l ∈ T := by
  unfold goodEvent_rows Pair.mk'
  split_ifs <;> simp [or_comm]

private lemma goodEvent_mk'_eq {N : ℕ} {k l k' l' : Fin N} (h : Pair.mk' k l = Pair.mk' k' l') :
    (k = k' ∧ l = l') ∨ (k = l' ∧ l = k') := by
  unfold Pair.mk' at h
  split_ifs at h <;> simp only [Subtype.mk.injEq, Prod.mk.injEq] at h <;> tauto

omit [RCLike 𝕜] in
private lemma goodEvent_piMerge_mem {N : ℕ} (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    (x : Pair N → 𝕜) (y : J → 𝕜) {p : Pair N} (hp : p ∈ J) :
    piMerge (α := fun _ => 𝕜) J x y p = y ⟨p, hp⟩ := by
  simp [piMerge, hp]

omit [RCLike 𝕜] in
private lemma goodEvent_piMerge_not_mem {N : ℕ} (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    (x : Pair N → 𝕜) (y : J → 𝕜) {p : Pair N} (hp : p ∉ J) :
    piMerge (α := fun _ => 𝕜) J x y p = x p := by
  simp [piMerge, hp]

/-- (R) of §4.3: `G^{(T)}` does not depend on the coordinates in the rows `T`. -/
private lemma goodEvent_greenT_piMerge {N : ℕ} (T : Finset (Fin N)) (x : Pair N → 𝕜)
    (y : goodEvent_rows T → 𝕜) (z : ℂ) :
    greenT (toMatrix (piMerge (α := fun _ => 𝕜) (goodEvent_rows T) x y)) T z =
      greenT (toMatrix x) T z := by
  have hm : minor (toMatrix (piMerge (α := fun _ => 𝕜) (goodEvent_rows T) x y)) T =
      minor (toMatrix x) T := by
    ext k l
    simp only [minor, Matrix.submatrix_apply, goodEvent_toMatrix_apply]
    rw [goodEvent_piMerge_not_mem _ _ _ (by
      rw [goodEvent_mem_rows, not_or]
      exact ⟨k.2, l.2⟩)]
  unfold greenT greenMinor
  rw [hm]

private lemma goodEvent_toMatrix_piMerge {N : ℕ} (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    (x : Pair N → 𝕜) (y : J → 𝕜) {k l : Fin N} (h : Pair.mk' k l ∈ J) :
    toMatrix (piMerge (α := fun _ => 𝕜) J x y) k l = goodEvent_ent k l (y ⟨Pair.mk' k l, h⟩) := by
  rw [goodEvent_toMatrix_apply, goodEvent_piMerge_mem J x y h]

/-- Distinct coordinates are independent under the product law (Lemma 4.7 (a)). -/
private lemma goodEvent_iIndep {N : ℕ} (M : Ensemble 𝕜 N) (J : Set (Pair N))
    [DecidablePred (· ∈ J)] {ι : Type*} (c : ι → J) (hc : Function.Injective c)
    (f : ι → 𝕜 → ℂ) (hf : ∀ a, Measurable (f a)) :
    iIndepFun (fun a (y : J → 𝕜) => f a (y (c a))) (Measure.pi fun p : J => M.law p) := by
  have h0 := iIndepFun_pi (μ := fun p : J => M.law p) (X := fun _ (y : 𝕜) => y)
    (fun _ => aemeasurable_id)
  exact (h0.precomp hc).comp (fun a => f a) hf

/-- A family of entries in distinct coordinates of `J` satisfies (4.1) under the product law on
`J` (Remark 4.1). -/
private lemma goodEvent_ldhyp {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    {n : ℕ} (k l : Fin n → Fin N) (hJ : ∀ a, Pair.mk' (k a) (l a) ∈ J)
    (hinj : Function.Injective fun a => Pair.mk' (k a) (l a)) :
    LDHyp (Measure.pi fun p : J => M.law p) ϑ
      (fun a y => toC (goodEvent_ent (k a) (l a) (y ⟨Pair.mk' (k a) (l a), hJ a⟩)))
      (fun a => M.sd (k a) (l a)) := by
  have hm : ∀ a, Measurable (fun w : 𝕜 => toC (goodEvent_ent (k a) (l a) w)) := fun a =>
    (goodEvent_continuous_toC.comp (goodEvent_continuous_ent _ _)).measurable
  refine ⟨?_, fun a => (hm a).comp (measurable_pi_apply _), fun a => ?_,
    fun a => Real.sqrt_nonneg _, fun a => ?_, fun a x hx => ?_⟩
  · exact goodEvent_iIndep M J (fun a => ⟨Pair.mk' (k a) (l a), hJ a⟩)
      (fun a b hab => hinj (congrArg Subtype.val hab)) _ hm
  · rw [integral_comp_eval (μ := fun p : J => M.law p) (i := ⟨_, hJ a⟩)
      (f := fun w => toC (goodEvent_ent (k a) (l a) w)) (hm a).aestronglyMeasurable]
    change ∫ w, toC (goodEvent_ent (k a) (l a) w) ∂M.law (Pair.mk' (k a) (l a)) = 0
    rw [goodEvent_integral_toC (goodEvent_integrable_ent h hϑ _ _), goodEvent_integral_ent h]
    apply Complex.ext <;> simp [toC]
  · rw [integral_comp_eval (μ := fun p : J => M.law p) (i := ⟨_, hJ a⟩)
      (f := fun w => ‖toC (goodEvent_ent (k a) (l a) w)‖ ^ 2)
      ((hm a).norm.pow_const 2).aestronglyMeasurable]
    change ∫ w, ‖toC (goodEvent_ent (k a) (l a) w)‖ ^ 2 ∂M.law (Pair.mk' (k a) (l a)) = _
    simp only [goodEvent_norm_toC]
    rw [goodEvent_integral_norm_ent h, goodEvent_sd_sq]
  · have hmeas : MeasurableSet
        {w : 𝕜 | x * M.sd (k a) (l a) < ‖toC (goodEvent_ent (k a) (l a) w)‖} :=
      measurableSet_lt measurable_const (hm a).norm
    have hpre : {y : J → 𝕜 | x * M.sd (k a) (l a) <
          ‖toC (goodEvent_ent (k a) (l a) (y ⟨Pair.mk' (k a) (l a), hJ a⟩))‖} =
        Function.eval (⟨Pair.mk' (k a) (l a), hJ a⟩ : J) ⁻¹'
          {w : 𝕜 | x * M.sd (k a) (l a) < ‖toC (goodEvent_ent (k a) (l a) w)‖} := rfl
    rw [hpre, (measurePreserving_eval (fun p : J => M.law p) _).measure_preimage
      hmeas.nullMeasurableSet]
    change M.law (Pair.mk' (k a) (l a)) _ ≤ _
    simp only [goodEvent_norm_toC]
    exact goodEvent_tail_ent h _ _ hx

/-! ### 4. Continuity -/

private lemma goodEvent_cont_entry {N : ℕ} (k l : Fin N) :
    Continuous fun x : Pair N → 𝕜 => toC (toMatrix x k l) :=
  goodEvent_continuous_toC.comp ((goodEvent_continuous_ent k l).comp (continuous_apply _))

private lemma goodEvent_cont_greenT {N : ℕ} {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N))
    (k l : Fin N) : Continuous fun x : Pair N → 𝕜 => greenT (toMatrix x) T z k l := by
  have h1 : Continuous fun x : Pair N → 𝕜 =>
      ((x, ⟨z, hz⟩) : (Pair N → 𝕜) × {z : ℂ // 0 < z.im}) :=
    continuous_id.prodMk continuous_const
  exact ((continuous_greenT (𝕜 := 𝕜) T k l).comp h1).congr fun x => rfl

private lemma goodEvent_cont_selfZ {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im)
    (i : Fin N) : Continuous fun x : Pair N → 𝕜 => selfZ (toMatrix x) M.varMatrix z i := by
  have hC := goodEvent_cont_entry (𝕜 := 𝕜) (N := N)
  have hG := goodEvent_cont_greenT (𝕜 := 𝕜) (N := N) hz
  unfold selfZ
  exact (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((hC i k).mul (hG _ k l)).mul (hC l i)).sub
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hG _ k k))

/-! ### 5. The four row events on the slices -/

private lemma goodEvent_col_mem {N : ℕ} (i k : Fin N) :
    Pair.mk' k i ∈ goodEvent_rows ({i} : Finset (Fin N)) :=
  (goodEvent_mem_rows _ _ _).2 (Or.inr (Finset.mem_singleton_self i))

private lemma goodEvent_col_inj {N : ℕ} (i : Fin N) :
    Function.Injective fun k : Fin N => Pair.mk' k i := by
  intro k k' h
  rcases goodEvent_mk'_eq h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exact h1.trans h2

private lemma goodEvent_slice_col {N : ℕ} (i : Fin N) (x : Pair N → 𝕜)
    (y : goodEvent_rows ({i} : Finset (Fin N)) → 𝕜) (k : Fin N) :
    toC (toMatrix (piMerge (α := fun _ => 𝕜) (goodEvent_rows {i}) x y) k i) =
      toC (goodEvent_ent k i (y ⟨Pair.mk' k i, goodEvent_col_mem i k⟩)) := by
  rw [goodEvent_toMatrix_piMerge]

private lemma goodEvent_slice_row {N : ℕ} (i : Fin N) (x : Pair N → 𝕜)
    (y : goodEvent_rows ({i} : Finset (Fin N)) → 𝕜) (k : Fin N) :
    toC (toMatrix (piMerge (α := fun _ => 𝕜) (goodEvent_rows {i}) x y) i k) =
      starRingEnd ℂ (toC (goodEvent_ent k i (y ⟨Pair.mk' k i, goodEvent_col_mem i k⟩))) := by
  rw [← (toMatrix_isHermitian _).apply i k, goodEvent_toC_star, goodEvent_slice_col]

/-- The column family `(h_ki)_k` on the slice of row `i` satisfies (4.1) with `s_k = σ_ki`. -/
private lemma goodEvent_ldhyp_col {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (i : Fin N) :
    LDHyp (Measure.pi fun p : goodEvent_rows ({i} : Finset (Fin N)) => M.law p) ϑ
      (fun k y => toC (goodEvent_ent k i (y ⟨Pair.mk' k i, goodEvent_col_mem i k⟩)))
      (fun k => M.sd k i) :=
  goodEvent_ldhyp h hϑ _ (fun a => a) (fun _ => i) (goodEvent_col_mem i) (goodEvent_col_inj i)

/-- Probability of the failure of the first inequality of (G3) (proof of Lemma 4.4). -/
private lemma goodEvent_prob_G3a {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hN : 1 ≤ N) {z : ℂ}
    (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) (i j : Fin N) :
    M.prodLaw {x | lossL ϑ⁻¹ κ * Real.sqrt (∑ k, M.var i k * ‖greenT (toMatrix x) {i} z k j‖ ^ 2) <
      ‖∑ k, toC (toMatrix x i k) * greenT (toMatrix x) {i} z k j‖} ≤
      ENNReal.ofReal ((4 + N / ϑ) * Real.exp (-κ)) := by
  have hX := goodEvent_ldhyp_col h hϑ i
  have hC := goodEvent_cont_entry (𝕜 := 𝕜) (N := N)
  have hG := goodEvent_cont_greenT (𝕜 := 𝕜) (N := N) hz
  unfold Ensemble.prodLaw
  refine measure_le_of_slices M.law (goodEvent_rows {i})
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet fun x => ?_
  refine (measure_mono fun y hy => ?_).trans
    (ld_linear hX.conj hϑ hϑ1 hN (fun k => greenT (toMatrix x) {i} z k j) hκ)
  simp only [Set.mem_ofPred_eq, goodEvent_greenT_piMerge, goodEvent_slice_row] at hy ⊢
  have e1 : ∑ k, ‖greenT (toMatrix x) {i} z k j‖ ^ 2 * M.sd k i ^ 2 =
      ∑ k, M.var i k * ‖greenT (toMatrix x) {i} z k j‖ ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [goodEvent_sd_sq, goodEvent_var_comm, mul_comm]
  rw [e1]
  refine lt_of_lt_of_eq hy ?_
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Probability of the failure of the second inequality of (G3) (proof of Lemma 4.4). -/
private lemma goodEvent_prob_G3b {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hN : 1 ≤ N) {z : ℂ}
    (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) (i j : Fin N) :
    M.prodLaw {x | lossL ϑ⁻¹ κ * Real.sqrt (∑ k, ‖greenT (toMatrix x) {i} z j k‖ ^ 2 * M.var k i) <
      ‖∑ k, greenT (toMatrix x) {i} z j k * toC (toMatrix x k i)‖} ≤
      ENNReal.ofReal ((4 + N / ϑ) * Real.exp (-κ)) := by
  have hX := goodEvent_ldhyp_col h hϑ i
  have hC := goodEvent_cont_entry (𝕜 := 𝕜) (N := N)
  have hG := goodEvent_cont_greenT (𝕜 := 𝕜) (N := N) hz
  unfold Ensemble.prodLaw
  refine measure_le_of_slices M.law (goodEvent_rows {i})
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet fun x => ?_
  refine (measure_mono fun y hy => ?_).trans
    (ld_linear hX hϑ hϑ1 hN (fun k => greenT (toMatrix x) {i} z j k) hκ)
  simp only [Set.mem_ofPred_eq, goodEvent_greenT_piMerge, goodEvent_slice_col] at hy ⊢
  have e1 : ∑ k, ‖greenT (toMatrix x) {i} z j k‖ ^ 2 * M.sd k i ^ 2 =
      ∑ k, ‖greenT (toMatrix x) {i} z j k‖ ^ 2 * M.var k i :=
    Finset.sum_congr rfl fun k _ => by rw [goodEvent_sd_sq]
  rw [e1]
  exact hy

/-- `ℓ(κ)² ≤ ℓ₂(κ, n) / 2` (Remark 4.2 (iii)). -/
private lemma goodEvent_lossL_sq_le (a κ : ℝ) (n : ℕ) : lossL a κ ^ 2 ≤ lossL2 a κ n / 2 := by
  have h1 := lossL_sq_le_lossL2 a κ n
  have h0 : 0 ≤ lossL2 a κ n := by unfold lossL2; positivity
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc lossL a κ ^ 2 ≤ (2 * Real.sqrt 2)⁻¹ * lossL2 a κ n := h1
    _ ≤ 2⁻¹ * lossL2 a κ n := by
        gcongr
        linarith
    _ = lossL2 a κ n / 2 := by ring

/-- Probability of the failure of (G2) (proof of Lemma 4.4). -/
private lemma goodEvent_prob_G2 {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hN : 1 ≤ N) {z : ℂ}
    (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) (i : Fin N) :
    M.prodLaw {x | lossL2 ϑ⁻¹ κ N *
        Real.sqrt (∑ k, ∑ l, M.var i k * ‖greenT (toMatrix x) {i} z k l‖ ^ 2 * M.var i l) <
      ‖selfZ (toMatrix x) M.varMatrix z i‖} ≤
      ENNReal.ofReal ((4 + N / ϑ) * Real.exp (-κ) +
        20 * N ^ 2 * Nat.clog 2 (2 * N) / ϑ * Real.exp (-κ)) := by
  have hX := goodEvent_ldhyp_col h hϑ i
  have hC := goodEvent_cont_entry (𝕜 := 𝕜) (N := N)
  have hG := goodEvent_cont_greenT (𝕜 := 𝕜) (N := N) hz
  have hZ := goodEvent_cont_selfZ M hz i
  unfold Ensemble.prodLaw
  refine measure_le_of_slices M.law (goodEvent_rows {i})
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet fun x => ?_
  have hD := ld_diag hX hϑ hϑ1 hN (fun k => greenT (toMatrix x) {i} z k k) hκ
  have hO := ld_offdiag hX hϑ hϑ1 hN (greenT (toMatrix x) {i} z) hκ
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine (measure_mono fun y hy => ?_).trans ((measure_union_le _ _).trans (add_le_add hD hO))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only [Set.mem_ofPred_eq] at hy
  unfold selfZ at hy
  simp only [goodEvent_greenT_piMerge, goodEvent_slice_row, goodEvent_slice_col,
    Ensemble.varMatrix, Matrix.of_apply] at hy
  set G := greenT (toMatrix x) {i} z with hGdef
  set X : Fin N → ℂ := fun k => toC (goodEvent_ent k i (y ⟨Pair.mk' k i, goodEvent_col_mem i k⟩))
    with hXdef
  set ℓ := lossL ϑ⁻¹ κ
  set ℓ₂ := lossL2 ϑ⁻¹ κ N
  have hsplit : ∀ k, ∑ l, starRingEnd ℂ (X k) * G k l * X l =
      starRingEnd ℂ (X k) * G k k * X k +
        ∑ l, (if k = l then 0 else starRingEnd ℂ (X k) * G k l * X l) := by
    intro k
    have e : ∀ l, starRingEnd ℂ (X k) * G k l * X l =
        (if k = l then starRingEnd ℂ (X k) * G k k * X k else 0) +
          (if k = l then 0 else starRingEnd ℂ (X k) * G k l * X l) := by
      intro l
      split_ifs with hkl
      · subst hkl; simp
      · simp
    rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  have hZeq : ∑ k, ∑ l, starRingEnd ℂ (X k) * G k l * X l - ∑ k, (M.var i k : ℂ) * G k k =
      ∑ k, G k k * (((‖X k‖ ^ 2 : ℝ) : ℂ) - ((M.sd k i ^ 2 : ℝ) : ℂ)) +
        ∑ k, ∑ l, (if k = l then 0 else starRingEnd ℂ (X k) * G k l * X l) := by
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
      show ∀ A B C : ℂ, A + B - C = (A - C) + B from fun A B C => by ring,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc := Complex.conj_mul' (X k)
    rw [goodEvent_sd_sq, goodEvent_var_comm]
    push_cast
    linear_combination G k k * hc
  have hy' : ℓ₂ * Real.sqrt (∑ k, ∑ l, M.var i k * ‖G k l‖ ^ 2 * M.var i l) <
      ‖∑ k, ∑ l, starRingEnd ℂ (X k) * G k l * X l - ∑ k, (M.var i k : ℂ) * G k k‖ := hy
  rw [hZeq] at hy'
  have hA : ∑ k, ‖G k k‖ ^ 2 * M.sd k i ^ 4 ≤
      ∑ k, ∑ l, M.var i k * ‖G k l‖ ^ 2 * M.var i l := by
    refine Finset.sum_le_sum fun k _ => ?_
    have e : ‖G k k‖ ^ 2 * M.sd k i ^ 4 = M.var i k * ‖G k k‖ ^ 2 * M.var i k := by
      rw [show M.sd k i ^ 4 = (M.sd k i ^ 2) ^ 2 by ring, goodEvent_sd_sq, goodEvent_var_comm]
      ring
    rw [e]
    exact Finset.single_le_sum (f := fun l => M.var i k * ‖G k l‖ ^ 2 * M.var i l)
      (fun l _ => mul_nonneg (mul_nonneg (goodEvent_var_nonneg M i k) (by positivity))
        (goodEvent_var_nonneg M i l)) (Finset.mem_univ k)
  have hB : (∑ k, ∑ l, if k = l then 0 else M.sd k i ^ 2 * ‖G k l‖ ^ 2 * M.sd l i ^ 2) ≤
      ∑ k, ∑ l, M.var i k * ‖G k l‖ ^ 2 * M.var i l := by
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
    split_ifs
    · exact mul_nonneg (mul_nonneg (goodEvent_var_nonneg M i k) (by positivity))
        (goodEvent_var_nonneg M i l)
    · rw [goodEvent_sd_sq, goodEvent_sd_sq, goodEvent_var_comm M k i, goodEvent_var_comm M l i]
  have hℓ := goodEvent_lossL_sq_le ϑ⁻¹ κ N
  have hℓ0 : 0 ≤ ℓ ^ 2 := sq_nonneg _
  have hℓ₂ : 0 ≤ ℓ₂ := by
    change 0 ≤ lossL2 ϑ⁻¹ κ N
    unfold lossL2
    positivity
  have key : ‖∑ k, G k k * (((‖X k‖ ^ 2 : ℝ) : ℂ) - ((M.sd k i ^ 2 : ℝ) : ℂ)) +
      ∑ k, ∑ l, (if k = l then 0 else starRingEnd ℂ (X k) * G k l * X l)‖ ≤
      ℓ₂ * Real.sqrt (∑ k, ∑ l, M.var i k * ‖G k l‖ ^ 2 * M.var i l) := by
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ k, G k k * (((‖X k‖ ^ 2 : ℝ) : ℂ) - ((M.sd k i ^ 2 : ℝ) : ℂ))‖ ≤
        ℓ₂ / 2 * Real.sqrt (∑ k, ∑ l, M.var i k * ‖G k l‖ ^ 2 * M.var i l) := by
      refine le_trans ?_ (mul_le_mul hℓ (Real.sqrt_le_sqrt hA) (Real.sqrt_nonneg _)
        (by positivity))
      exact hc1
    have h2 : ‖∑ k, ∑ l, (if k = l then 0 else starRingEnd ℂ (X k) * G k l * X l)‖ ≤
        ℓ₂ / 2 * Real.sqrt (∑ k, ∑ l, M.var i k * ‖G k l‖ ^ 2 * M.var i l) :=
      hc2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (by positivity))
    linarith
  exact absurd hy' (not_lt.2 key)

/-- A sum over `Fin N` of a function vanishing on `S` is a sum over the complement of `S`,
enumerated by `e`. -/
private lemma goodEvent_sum_compl {N : ℕ} {β : Type*} [AddCommMonoid β] (S : Finset (Fin N))
    {m : ℕ} (e : Fin m ≃ ↥Sᶜ) (f : Fin N → β) (hf : ∀ k ∈ S, f k = 0) :
    ∑ k, f k = ∑ a, f (e a) := by
  rw [← Finset.sum_compl_add_sum S f, Finset.sum_eq_zero hf, add_zero,
    ← Finset.sum_coe_sort Sᶜ f]
  exact (Equiv.sum_comp e (fun k : ↥Sᶜ => f k)).symm

private lemma goodEvent_sum_compl₂ {N : ℕ} {β : Type*} [AddCommMonoid β] (S : Finset (Fin N))
    {m : ℕ} (e : Fin m ≃ ↥Sᶜ) (F : Fin N → Fin N → β)
    (hF : ∀ k l, k ∈ S ∨ l ∈ S → F k l = 0) :
    ∑ k, ∑ l, F k l = ∑ a, ∑ b, F (e a) (e b) := by
  rw [goodEvent_sum_compl S e (fun k => ∑ l, F k l)
    (fun k hk => Finset.sum_eq_zero fun l _ => hF k l (Or.inl hk))]
  exact Finset.sum_congr rfl fun a _ => goodEvent_sum_compl S e _ fun l hl => hF _ l (Or.inr hl)

private lemma goodEvent_greenT_mem {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (T : Finset (Fin N))
    (z : ℂ) {k l : Fin N} (h : k ∈ T ∨ l ∈ T) : greenT A T z k l = 0 := by
  rcases h with h | h <;> simp [greenT, h]

/-- Probability of the failure of (G4) (proof of Lemma 4.4). -/
private lemma goodEvent_prob_G4 {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hN : 3 ≤ N) {z : ℂ}
    (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) {i j : Fin N} (hij : i ≠ j) :
    M.prodLaw {x | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ k, ∑ l, M.var i k *
          ‖greenT (toMatrix x) {i, j} z k l‖ ^ 2 * M.var l j) <
      ‖∑ k, ∑ l, toC (toMatrix x i k) * greenT (toMatrix x) {i, j} z k l * toC (toMatrix x l j)‖} ≤
      ENNReal.ofReal (10 * N ^ 2 / ϑ * Real.exp (-κ)) := by
  set S : Finset (Fin N) := {i, j} with hS
  have hiS : i ∈ S := Finset.mem_insert_self i {j}
  have hjS : j ∈ S := Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  have hcard : Fintype.card ↥Sᶜ = N - 2 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, Finset.card_pair hij]
  set e : Fin (N - 2) ≃ ↥Sᶜ := (Fintype.equivFinOfCardEq hcard).symm
  have heS : ∀ a, (e a : Fin N) ∉ S := fun a => Finset.mem_compl.1 (e a).2
  have hn : 1 ≤ N - 2 := by omega
  have hJX : ∀ a : Fin (N - 2), Pair.mk' i (e a : Fin N) ∈ goodEvent_rows S :=
    fun a => (goodEvent_mem_rows _ _ _).2 (Or.inl hiS)
  have hJY : ∀ b : Fin (N - 2), Pair.mk' (e b : Fin N) j ∈ goodEvent_rows S :=
    fun b => (goodEvent_mem_rows _ _ _).2 (Or.inr hjS)
  have hne : ∀ a, (e a : Fin N) ≠ i ∧ (e a : Fin N) ≠ j :=
    fun a => ⟨fun h' => heS a (h' ▸ hiS), fun h' => heS a (h' ▸ hjS)⟩
  have heinj : ∀ a b, (e a : Fin N) = e b → a = b := fun a b h' => e.injective (Subtype.ext h')
  have hinjX : Function.Injective fun a => Pair.mk' i (e a : Fin N) := by
    intro a b h'
    rcases goodEvent_mk'_eq h' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact heinj a b h2
    · exact absurd h1.symm (hne b).1
  have hinjY : Function.Injective fun b => Pair.mk' (e b : Fin N) j := by
    intro a b h'
    rcases goodEvent_mk'_eq h' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact heinj a b h1
    · exact absurd h1 (hne a).2
  have hX : LDHyp (Measure.pi fun p : goodEvent_rows S => M.law p) ϑ
      (fun a y => toC (goodEvent_ent i (e a : Fin N) (y ⟨Pair.mk' i (e a : Fin N), hJX a⟩)))
      (fun a => M.sd i (e a)) :=
    goodEvent_ldhyp h hϑ _ (fun _ => i) (fun a => (e a : Fin N)) hJX hinjX
  have hY : LDHyp (Measure.pi fun p : goodEvent_rows S => M.law p) ϑ
      (fun b y => toC (goodEvent_ent (e b : Fin N) j (y ⟨Pair.mk' (e b : Fin N) j, hJY b⟩)))
      (fun b => M.sd (e b) j) :=
    goodEvent_ldhyp h hϑ _ (fun b => (e b : Fin N)) (fun _ => j) hJY hinjY
  have hc : Function.Injective (Sum.elim
      (fun a => (⟨Pair.mk' i (e a : Fin N), hJX a⟩ : goodEvent_rows S))
      (fun b => (⟨Pair.mk' (e b : Fin N) j, hJY b⟩ : goodEvent_rows S))) := by
    rintro (a | a) (b | b) h'
    · exact congrArg Sum.inl (hinjX (congrArg Subtype.val h'))
    · exfalso
      rcases goodEvent_mk'_eq (congrArg Subtype.val h') with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact (hne b).1 h1.symm
      · exact hij h1
    · exfalso
      rcases goodEvent_mk'_eq (congrArg Subtype.val h') with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact (hne a).1 h1
      · exact hij h2.symm
    · exact congrArg Sum.inr (hinjY (congrArg Subtype.val h'))
  have hXY := goodEvent_iIndep M (goodEvent_rows S) _ hc
    (Sum.elim (fun a w => toC (goodEvent_ent i (e a : Fin N) w))
      (fun b w => toC (goodEvent_ent (e b : Fin N) j w)))
    (by
      rintro (a | b)
      · exact (goodEvent_continuous_toC.comp (goodEvent_continuous_ent _ _)).measurable
      · exact (goodEvent_continuous_toC.comp (goodEvent_continuous_ent _ _)).measurable)
  have hXY' : iIndepFun (Sum.elim
      (fun a (y : goodEvent_rows S → 𝕜) =>
        toC (goodEvent_ent i (e a : Fin N) (y ⟨Pair.mk' i (e a : Fin N), hJX a⟩)))
      (fun b (y : goodEvent_rows S → 𝕜) =>
        toC (goodEvent_ent (e b : Fin N) j (y ⟨Pair.mk' (e b : Fin N) j, hJY b⟩))))
      (Measure.pi fun p : goodEvent_rows S => M.law p) := by
    convert hXY using 1
    funext u
    cases u <;> rfl
  have hκ' : kappaTheta ϑ⁻¹ + Real.log ((N - 2 : ℕ) : ℝ) ≤ κ := by
    have h1 : (0 : ℝ) < ((N - 2 : ℕ) : ℝ) := by exact_mod_cast hn
    have h2 : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 2
    linarith [Real.log_le_log h1 h2]
  have hC := goodEvent_cont_entry (𝕜 := 𝕜) (N := N)
  have hG := goodEvent_cont_greenT (𝕜 := 𝕜) (N := N) hz
  unfold Ensemble.prodLaw
  refine measure_le_of_slices M.law (goodEvent_rows S)
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet fun x => ?_
  refine (measure_mono fun y hy => ?_).trans ((ld_bilinear hX hϑ hϑ1 hn hn le_rfl hY hXY'
    (fun a b => greenT (toMatrix x) S z (e a) (e b)) hκ').trans ?_)
  · simp only [Set.mem_ofPred_eq, goodEvent_greenT_piMerge] at hy ⊢
    have e1 : ∑ a, ∑ b, M.sd i (e a) ^ 2 * ‖greenT (toMatrix x) S z (e a) (e b)‖ ^ 2 *
        M.sd (e b) j ^ 2 =
        ∑ k, ∑ l, M.var i k * ‖greenT (toMatrix x) S z k l‖ ^ 2 * M.var l j := by
      rw [goodEvent_sum_compl₂ S e (fun k l => M.var i k * ‖greenT (toMatrix x) S z k l‖ ^ 2 *
        M.var l j) (fun k l hkl => by simp [goodEvent_greenT_mem _ _ _ hkl])]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [goodEvent_sd_sq, goodEvent_sd_sq]
    have e2 : ∑ k, ∑ l, toC (toMatrix (piMerge (α := fun _ => 𝕜) (goodEvent_rows S) x y) i k) *
        greenT (toMatrix x) S z k l *
          toC (toMatrix (piMerge (α := fun _ => 𝕜) (goodEvent_rows S) x y) l j) =
        ∑ a, ∑ b, toC (goodEvent_ent i (e a : Fin N) (y ⟨Pair.mk' i (e a : Fin N), hJX a⟩)) *
          greenT (toMatrix x) S z (e a) (e b) *
            toC (goodEvent_ent (e b : Fin N) j (y ⟨Pair.mk' (e b : Fin N) j, hJY b⟩)) := by
      rw [goodEvent_sum_compl₂ S e _ (fun k l hkl => by simp [goodEvent_greenT_mem _ _ _ hkl])]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [goodEvent_toMatrix_piMerge _ _ _ (hJX a), goodEvent_toMatrix_piMerge _ _ _ (hJY b)]
    rw [e1, ← e2]
    exact hy
  · apply ENNReal.ofReal_le_ofReal
    have h2 : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 2
    have h0 : (0 : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    gcongr

/-! ### 6. The probability of the good event -/

/-- The event where (G2) fails at the index `i`. -/
private def goodEvent_bad2 {N : ℕ} (M : Ensemble 𝕜 N) (a κ : ℝ) (z : ℂ) (i : Fin N) :
    Set (Pair N → 𝕜) :=
  {x | lossL2 a κ N *
      Real.sqrt (∑ k, ∑ l, M.var i k * ‖greenT (toMatrix x) {i} z k l‖ ^ 2 * M.var i l) <
    ‖selfZ (toMatrix x) M.varMatrix z i‖}

/-- The event where (G3) or (G4) fails at the pair `(i, j)`, `i ≠ j`. -/
private def goodEvent_bad34 {N : ℕ} (M : Ensemble 𝕜 N) (a κ : ℝ) (z : ℂ) (i j : Fin N) :
    Set (Pair N → 𝕜) :=
  {x | lossL a κ * Real.sqrt (∑ k, M.var i k * ‖greenT (toMatrix x) {i} z k j‖ ^ 2) <
      ‖∑ k, toC (toMatrix x i k) * greenT (toMatrix x) {i} z k j‖} ∪
    {x | lossL a κ * Real.sqrt (∑ k, ‖greenT (toMatrix x) {i} z j k‖ ^ 2 * M.var k i) <
      ‖∑ k, greenT (toMatrix x) {i} z j k * toC (toMatrix x k i)‖} ∪
    {x | i ≠ j ∧ lossL a κ ^ 2 * Real.sqrt (∑ k, ∑ l, M.var i k *
          ‖greenT (toMatrix x) {i, j} z k l‖ ^ 2 * M.var l j) <
      ‖∑ k, ∑ l, toC (toMatrix x i k) * greenT (toMatrix x) {i, j} z k l * toC (toMatrix x l j)‖}

private lemma goodEvent_compl_subset {N : ℕ} (M : Ensemble 𝕜 N) (a κ : ℝ) (z : ℂ) :
    (goodEvent M a κ z)ᶜ ⊆ {x | ∃ p, κ ^ a * Real.sqrt (M.varPair p) < ‖x p‖} ∪
      (⋃ i, goodEvent_bad2 M a κ z i) ∪ ⋃ i, ⋃ j, goodEvent_bad34 M a κ z i j := by
  intro x hx
  rw [Set.mem_compl_iff] at hx
  by_contra hc
  apply hx
  simp only [goodEvent_bad2, goodEvent_bad34, Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq,
    not_or, not_exists, not_lt, not_and] at hc
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
  refine ⟨fun k l => ?_, hc2, fun i j hij => ⟨(hc3 i j).1.1, (hc3 i j).1.2⟩,
    fun i j hij => (hc3 i j).2 hij⟩
  rw [goodEvent_toMatrix_apply]
  exact (goodEvent_norm_ent_le k l _).trans (hc1 (Pair.mk' k l))

private lemma goodEvent_iUnion_le {α ι : Type*} [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (B : ι → Set α) {c : ℝ} (h : ∀ a, μ (B a) ≤ ENNReal.ofReal c) :
    μ (⋃ a, B a) ≤ ENNReal.ofReal (Fintype.card ι * c) := by
  calc μ (⋃ a, B a) ≤ ∑ a, μ (B a) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : ι, ENNReal.ofReal c := Finset.sum_le_sum fun a _ => h a
    _ = ENNReal.ofReal (Fintype.card ι * c) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- `κ ≥ κ_ϑ + log N` forces `κ ≥ 1`. -/
private lemma goodEvent_one_le_kappa {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) : 1 ≤ κ := by
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have h1 : 0 ≤ Real.log ϑ⁻¹ := Real.log_nonneg ha
  have h2 : 1 ≤ Real.log (4 * cTheta ϑ⁻¹) := by
    rw [Real.le_log_iff_exp_le (by unfold cTheta; positivity)]
    unfold cTheta
    have := Real.exp_one_lt_d9
    nlinarith
  have h3 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold kappaTheta at hκ
  nlinarith

/-- `⌈log₂ 2n⌉ ≤ n` for `n ≥ 1`. -/
private lemma goodEvent_clog_le {N : ℕ} (hN : 1 ≤ N) : Nat.clog 2 (2 * N) ≤ N := by
  apply Nat.clog_le_of_le_pow
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have := Nat.lt_two_pow_self (n := m)
  rw [pow_succ]
  omega

/-- Lemma 4.4: the probability bound `ℙ(𝒢_κ(z)ᶜ) ≤ 46 ϑ⁻¹ N⁴ e^{-κ}`. -/
private lemma goodEvent_prob {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (h : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hN : 3 ≤ N) {z : ℂ}
    (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) :
    M.prodLaw (goodEvent M ϑ⁻¹ κ z)ᶜ ≤ ENNReal.ofReal (46 / ϑ * N ^ 4 * Real.exp (-κ)) := by
  have hN1 : 1 ≤ N := by omega
  have hκ1 := goodEvent_one_le_kappa hϑ hϑ1 hN1 hκ
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hE : 0 < Real.exp (-κ) := Real.exp_pos _
  set E := Real.exp (-κ) with hEdef
  set a := ϑ⁻¹ with hadef
  have hdiv : (N : ℝ) / ϑ = N * a := div_eq_mul_inv _ _
  have h1 : M.prodLaw {x | ∃ p, κ ^ a * Real.sqrt (M.varPair p) < ‖x p‖} ≤
      ENNReal.ofReal (N ^ 2 * a * E) := by
    have := h.prodLaw_large_entry hϑ (T := κ ^ ϑ⁻¹) (Real.one_le_rpow hκ1 (inv_nonneg.2 hϑ.le))
    rwa [Real.rpow_inv_rpow (by linarith) hϑ.ne'] at this
  have h2 : ∀ i, M.prodLaw (goodEvent_bad2 M a κ z i) ≤ ENNReal.ofReal (25 * N ^ 3 * a * E) := by
    intro i
    refine (goodEvent_prob_G2 h hϑ hϑ1 hN1 hz hκ i).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : (Nat.clog 2 (2 * N) : ℝ) ≤ N := by exact_mod_cast goodEvent_clog_le hN1
    have hc0 : (0 : ℝ) ≤ Nat.clog 2 (2 * N) := Nat.cast_nonneg _
    simp only [div_eq_mul_inv]
    rw [← hadef]
    have t1 : (N : ℝ) ^ 2 * Nat.clog 2 (2 * N) ≤ N ^ 3 := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    have t2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
    have t3 : (N : ℝ) ≤ N ^ 3 := by nlinarith
    have t4 : (4 : ℝ) + N * a + 20 * N ^ 2 * Nat.clog 2 (2 * N) * a ≤ 25 * N ^ 3 * a := by
      have u1 := mul_le_mul_of_nonneg_right t1 (show 0 ≤ a by linarith)
      have u2 := mul_le_mul_of_nonneg_right t3 (show 0 ≤ a by linarith)
      have u3 : (1 : ℝ) ≤ N ^ 3 := by nlinarith
      have u4 := mul_le_mul_of_nonneg_right u3 (show 0 ≤ a by linarith)
      nlinarith
    have t5 := mul_le_mul_of_nonneg_right t4 hE.le
    linarith
  have h3 : ∀ i j, M.prodLaw (goodEvent_bad34 M a κ z i j) ≤
      ENNReal.ofReal (20 * N ^ 2 * a * E) := by
    intro i j
    have h4 : M.prodLaw {x | i ≠ j ∧ lossL a κ ^ 2 * Real.sqrt (∑ k, ∑ l, M.var i k *
          ‖greenT (toMatrix x) {i, j} z k l‖ ^ 2 * M.var l j) <
        ‖∑ k, ∑ l, toC (toMatrix x i k) * greenT (toMatrix x) {i, j} z k l *
          toC (toMatrix x l j)‖} ≤ ENNReal.ofReal (10 * N ^ 2 / ϑ * E) := by
      by_cases hij : i = j
      · simp [hij]
      · refine (measure_mono ?_).trans (goodEvent_prob_G4 h hϑ hϑ1 hN hz hκ hij)
        intro x hx
        exact hx.2
    refine (measure_union_le _ _).trans ((add_le_add ((measure_union_le _ _).trans
      (add_le_add (goodEvent_prob_G3a h hϑ hϑ1 hN1 hz hκ i j)
        (goodEvent_prob_G3b h hϑ hϑ1 hN1 hz hκ i j))) h4).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [div_eq_mul_inv]
    rw [← hadef]
    have t2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
    have t3 : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have t4 : (4 + N * a) + (4 + N * a) + 10 * N ^ 2 * a ≤ 20 * N ^ 2 * a := by
      have u2 := mul_le_mul_of_nonneg_right t3 (show 0 ≤ a by linarith)
      have u4 := mul_le_mul_of_nonneg_right t2 (show 0 ≤ a by linarith)
      nlinarith
    have t5 := mul_le_mul_of_nonneg_right t4 hE.le
    linarith
  refine (measure_mono (goodEvent_compl_subset M a κ z)).trans ((measure_union_le _ _).trans
    ((add_le_add (measure_union_le _ _) le_rfl).trans ?_))
  refine (add_le_add (add_le_add h1 (goodEvent_iUnion_le _ _ h2))
    (goodEvent_iUnion_le _ _ fun i => goodEvent_iUnion_le _ _ (h3 i))).trans ?_
  simp only [Fintype.card_fin]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [show (46 : ℝ) / ϑ = 46 * a by rw [div_eq_mul_inv]]
  have hN2 : (N : ℝ) ^ 2 ≤ N ^ 4 := by
    have : (1 : ℝ) ≤ N ^ 2 := by nlinarith
    nlinarith
  have haE : 0 ≤ a * E := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hN2 haE]

/-! ### 7. Ward bounds for the minors -/

private lemma goodEvent_greenT_im_nonneg {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (l : Fin N) :
    0 ≤ (greenT A T z l l).im := by
  by_cases hl : l ∈ T
  · simp [greenT, hl]
  · have := green_im_diag_pos (A := minor A T) (hA.submatrix _) hz ⟨l, hl⟩
    simp only [greenT, Matrix.of_apply, hl, not_false_eq_true, and_self, dite_true, greenMinor]
    exact this.le

/-- Lemma 3.5 (b) for the minor `H^{(T)}`, row and column `l` (both sides vanish for `l ∈ T`). -/
private lemma goodEvent_ward {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (l : Fin N) :
    ∑ k, ‖greenT A T z l k‖ ^ 2 = (greenT A T z l l).im / z.im ∧
      ∑ k, ‖greenT A T z k l‖ ^ 2 = (greenT A T z l l).im / z.im := by
  by_cases hl : l ∈ T
  · simp [greenT, hl]
  have hw := ward (A := minor A T) (hA.submatrix _) hz ⟨l, hl⟩
  have e : ∀ f : Fin N → ℝ, (∀ k, k ∈ T → f k = 0) →
      ∑ k, f k = ∑ k : {k // k ∉ T}, f k := by
    intro f hf
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k => k ∉ T) f]
    have : ∑ k : {k // ¬ k ∉ T}, f k = 0 := Finset.sum_eq_zero fun k _ => hf k (not_not.1 k.2)
    rw [this, add_zero]
  have gl : greenT A T z l l = green (minor A T) z ⟨l, hl⟩ ⟨l, hl⟩ := by
    simp [greenT, hl, greenMinor]
  refine ⟨?_, ?_⟩
  · rw [e _ (fun k hk => by simp [greenT, hk]), gl, ← hw.1]
    exact Finset.sum_congr rfl fun k _ => by simp [greenT, hl, k.2, greenMinor]
  · rw [e (fun k => ‖greenT A T z k l‖ ^ 2) (fun k hk => by simp [greenT, hk]), gl, ← hw.2]
    exact Finset.sum_congr rfl fun k _ => by simp [greenT, hl, k.2, greenMinor]

/-- (W) of the proof of Lemma 4.4, for weights `0 ≤ w_k ≤ c`. -/
private lemma goodEvent_wardW {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) {c : ℝ} (w : Fin N → ℝ) (hw : ∀ k, w k ≤ c)
    (l : Fin N) :
    ∑ k, w k * ‖greenT A T z k l‖ ^ 2 ≤ c * ((greenT A T z l l).im / z.im) ∧
      ∑ k, ‖greenT A T z l k‖ ^ 2 * w k ≤ c * ((greenT A T z l l).im / z.im) := by
  obtain ⟨h1, h2⟩ := goodEvent_ward hA hz T l
  constructor
  · rw [← h2, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hw k) (sq_nonneg _)
  · rw [← h1, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hw k) (sq_nonneg _)

/-- `∑_l Im G^{(T)}_ll = N Im m^{(T)} ≤ N (Im m + |T|/(Nη))` by (I5). -/
private lemma goodEvent_sum_im_le {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (hN : 0 < N) (T : Finset (Fin N)) :
    ∑ l, (greenT A T z l l).im ≤ N * ((stieltjesEmp A z).im + T.card / (N * z.im)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (stieltjesT A T z).im = (N : ℝ)⁻¹ * ∑ l, (greenT A T z l l).im := by
    unfold stieltjesT
    rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul,
      Complex.im_sum]
  have h2 := norm_stieltjesT_sub_le hA hz T
  have h3 := Complex.abs_im_le_norm (stieltjesT A T z - stieltjesEmp A z)
  rw [Complex.sub_im] at h3
  have h4 := le_abs_self ((stieltjesT A T z).im - (stieltjesEmp A z).im)
  have h5 : (N : ℝ)⁻¹ * ∑ l, (greenT A T z l l).im ≤
      (stieltjesEmp A z).im + T.card / (N * z.im) := by
    linarith
  rw [inv_mul_le_iff₀ hn] at h5
  exact h5

private lemma goodEvent_im_stieltjesEmp_nonneg {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) : 0 ≤ (stieltjesEmp A z).im := by
  unfold stieltjesEmp
  rw [Fintype.card_fin, show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.im_ofReal_mul, Matrix.trace, Complex.im_sum]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun l _ => (green_im_diag_pos hA hz l).le)

/-- (W′) of the proof of Lemma 4.4, for weights `0 ≤ w₁, w₂ ≤ C₀/N`. -/
private lemma goodEvent_wardW2 {N : ℕ} (hN : 0 < N) {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (w₁ w₂ : Fin N → ℝ) (h₁0 : ∀ k, 0 ≤ w₁ k) (h₁ : ∀ k, w₁ k ≤ C₀ / N)
    (h₂ : ∀ k, w₂ k ≤ C₀ / N) :
    ∑ k, ∑ l, w₁ k * ‖greenT A T z k l‖ ^ 2 * w₂ l ≤
      C₀ ^ 2 * ((stieltjesEmp A z).im / (N * z.im) + T.card / (N * z.im) ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 ≤ C₀ / N := by positivity
  have hW := fun l => (goodEvent_wardW hA hz T w₁ h₁ l).1
  have him := goodEvent_greenT_im_nonneg hA hz T
  calc ∑ k, ∑ l, w₁ k * ‖greenT A T z k l‖ ^ 2 * w₂ l
      = ∑ l, w₂ l * ∑ k, w₁ k * ‖greenT A T z k l‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ l, C₀ / N * (C₀ / N * ((greenT A T z l l).im / z.im)) :=
        Finset.sum_le_sum fun l _ => mul_le_mul (h₂ l) (hW l)
          (Finset.sum_nonneg fun k _ => mul_nonneg (h₁0 k) (sq_nonneg _)) hc
    _ = C₀ ^ 2 / N ^ 2 / z.im * ∑ l, (greenT A T z l l).im := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        field_simp
    _ ≤ C₀ ^ 2 / N ^ 2 / z.im * (N * ((stieltjesEmp A z).im + T.card / (N * z.im))) :=
        mul_le_mul_of_nonneg_left (goodEvent_sum_im_le hA hz hN T) (by positivity)
    _ = C₀ ^ 2 * ((stieltjesEmp A z).im / (N * z.im) + T.card / (N * z.im) ^ 2) := by
        field_simp

/-- `√(C² (u + c v²)) ≤ C (√u + 2v)` for `0 ≤ c ≤ 4`. -/
private lemma goodEvent_sqrt_le {C u v c : ℝ} (hC : 0 ≤ C) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc : c ≤ 4) :
    Real.sqrt (C ^ 2 * (u + c * v ^ 2)) ≤ C * (Real.sqrt u + 2 * v) := by
  rw [Real.sqrt_le_left (by positivity)]
  have hs := Real.sq_sqrt hu
  have hs0 := Real.sqrt_nonneg u
  have key : 0 ≤ C ^ 2 * (4 * v * Real.sqrt u + (4 - c) * v ^ 2) :=
    mul_nonneg (sq_nonneg C) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv) hs0)
      (mul_nonneg (by linarith) (sq_nonneg v)))
  nlinarith [key, hs]

/-! ### 8. Consequences of the good event -/

/-- (4.11)–(4.13) of Lemma 4.4 at a point of `𝒢_κ(z)`. -/
private lemma goodEvent_consequences {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) (hN : 3 ≤ N)
    {z : ℂ} (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ)
    {x : Pair N → 𝕜} (hx : x ∈ goodEvent M ϑ⁻¹ κ z) {i j : Fin N} (hij : i ≠ j) :
    ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ 2 * C₀ * lossL2 ϑ⁻¹ κ N * ctrlPsiM x z ∧
      ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
        2 * C₀ ^ 2 * lossL ϑ⁻¹ κ ^ 2 * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 ∧
      ‖green (toMatrix x) z i j‖ ≤ 3 * C₀ * lossL ϑ⁻¹ κ ^ 2 * ‖green (toMatrix x) z i i‖ *
        ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z := by
  obtain ⟨hG1, hG2, hG3, hG4⟩ := hx
  have hN0 : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hN0
  have hA := toMatrix_isHermitian x
  have hκ1 := goodEvent_one_le_kappa hϑ hϑ1 hN1 hκ
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  set A := toMatrix x with hAdef
  set a := ϑ⁻¹ with hadef
  set ℓ := lossL a κ with hℓdef
  set ℓ₂ := lossL2 a κ N with hℓ₂def
  set u := (stieltjesEmp A z).im / (N * z.im) with hudef
  set v := 1 / (N * z.im) with hvdef
  set w := 1 / Real.sqrt N with hwdef
  have hC0 : 0 ≤ C₀ := by linarith
  have hu : 0 ≤ u := div_nonneg (goodEvent_im_stieltjesEmp_nonneg hA hz) (by positivity)
  have hv : 0 < v := by positivity
  have hw : 0 < w := by positivity
  have hw2 : w ^ 2 = 1 / N := by
    rw [hwdef, div_pow, Real.sq_sqrt hn.le, one_pow]
  have hv2 : v ^ 2 = 1 / (N * z.im) ^ 2 := by rw [hvdef, div_pow, one_pow]
  have hΨ : ctrlPsiM x z = Real.sqrt u + v + w := rfl
  have hsu := Real.sqrt_nonneg u
  -- loss factors
  have hκa : κ ^ a ≤ ℓ := by
    have h1 : κ ^ a ≤ κ ^ (a + 1 / 2) := Real.rpow_le_rpow_of_exponent_le hκ1 (by linarith)
    have h2 : 0 ≤ κ ^ (a + 1 / 2) := by positivity
    rw [hℓdef, lossL]
    linarith
  have hℓ1 : 1 ≤ ℓ := by
    have : 1 ≤ κ ^ (a + 1 / 2) := Real.one_le_rpow hκ1 (by linarith)
    rw [hℓdef, lossL]
    linarith
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hℓ₂ : ℓ ^ 2 ≤ ℓ₂ := by
    have := goodEvent_lossL_sq_le a κ N
    have h0 : 0 ≤ ℓ₂ := by rw [hℓ₂def]; unfold lossL2; positivity
    linarith
  clear_value u v w ℓ ℓ₂ a A
  -- variances
  have hvar0 := goodEvent_var_nonneg M
  have hvarC : ∀ k l, M.var k l ≤ C₀ / N := hM.boundC
  have hBij : ∀ k l, M.varMatrix k l = M.var k l := fun _ _ => rfl
  -- entries
  have hent : ∀ k l, ‖toC (A k l)‖ ≤ κ ^ a * (C₀ * w) := by
    intro k l
    rw [goodEvent_norm_toC]
    refine (hG1 k l).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h1 : M.sd k l ≤ Real.sqrt (C₀ / N) := Real.sqrt_le_sqrt (hvarC k l)
    refine h1.trans ?_
    rw [Real.sqrt_le_left (by positivity), mul_pow, hw2]
    rw [div_eq_mul_one_div C₀]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have hGii : green A z i i ≠ 0 := fun h0 => by
    have := green_im_diag_pos hA hz i
    rw [h0, Complex.zero_im] at this
    exact lt_irrefl _ this
  refine ⟨?_, ?_, ?_⟩
  · -- (4.11)
    have hR := goodEvent_wardW2 hN0 hA hz {i} hC0 (fun k => M.var i k) (fun l => M.var i l)
      (hvar0 i) (hvarC i) (hvarC i)
    rw [Finset.card_singleton, Nat.cast_one, ← hudef, ← hv2,
      show v ^ 2 = 1 * v ^ 2 by ring] at hR
    have hR' : Real.sqrt (∑ k, ∑ l, M.var i k * ‖greenT A {i} z k l‖ ^ 2 * M.var i l) ≤
        C₀ * (Real.sqrt u + 2 * v) :=
      (Real.sqrt_le_sqrt hR).trans (goodEvent_sqrt_le hC0 hu hv.le (by norm_num))
    have hZ := hG2 i
    unfold selfX
    calc ‖toC (A i i) - selfZ A M.varMatrix z i‖
        ≤ ‖toC (A i i)‖ + ‖selfZ A M.varMatrix z i‖ := norm_sub_le _ _
      _ ≤ κ ^ a * (C₀ * w) + ℓ₂ * (C₀ * (Real.sqrt u + 2 * v)) :=
          add_le_add (hent i i) (hZ.trans (mul_le_mul_of_nonneg_left hR'
            (by linarith [sq_nonneg ℓ])))
      _ ≤ ℓ₂ * (C₀ * w) + ℓ₂ * (C₀ * (Real.sqrt u + 2 * v)) := by
          gcongr
          linarith
      _ ≤ 2 * C₀ * ℓ₂ * ctrlPsiM x z := by
          rw [hΨ]
          have h0 : 0 ≤ ℓ₂ * C₀ := mul_nonneg (by linarith [sq_nonneg ℓ]) hC0
          have h1 := mul_nonneg h0 hsu
          have h2 := mul_nonneg h0 hw.le
          have h3 := mul_nonneg h0 hv.le
          linarith
  · -- (4.12)
    have hterm : ∀ k, ‖(if k = i then (0 : ℂ) else (M.varMatrix i k : ℂ) * green A z i k *
        green A z k i / green A z i i)‖ ≤
        C₀ / N * ‖green A z i i‖ * ℓ ^ 2 * (C₀ / N * ((greenT A {i} z k k).im / z.im)) := by
      intro k
      have hV0 : 0 ≤ C₀ / N * ((greenT A {i} z k k).im / z.im) :=
        mul_nonneg (by positivity) (div_nonneg (goodEvent_greenT_im_nonneg hA hz {i} k) hz.le)
      by_cases hki : k = i
      · simp only [hki, ↓reduceIte, norm_zero]
        rw [hki] at hV0
        exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hC0 hn.le) (norm_nonneg _))
          (sq_nonneg _)) hV0
      simp only [hki, ↓reduceIte]
      have hik : i ≠ k := Ne.symm hki
      obtain ⟨e1, -, e3⟩ := green_offdiag hA hz hik
      have hS1 := (hG3 i k hik).1
      have hS2 := (hG3 i k hik).2
      have hW := goodEvent_wardW hA hz {i} (fun l => M.var i l) (hvarC i) k
      have hW' := goodEvent_wardW hA hz {i} (fun l => M.var l i) (fun l => hvarC l i) k
      set V := C₀ / N * ((greenT A {i} z k k).im / z.im)
      have hS1' : ‖∑ l, toC (A i l) * greenT A {i} z l k‖ ≤ ℓ * Real.sqrt V :=
        hS1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hW.1) (by linarith))
      have hS2' : ‖∑ l, greenT A {i} z k l * toC (A l i)‖ ≤ ℓ * Real.sqrt V :=
        hS2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hW'.2) (by linarith))
      have heq : (M.varMatrix i k : ℂ) * green A z i k * green A z k i / green A z i i =
          (M.var i k : ℂ) * green A z i i * (∑ l, toC (A i l) * greenT A {i} z l k) *
            (∑ l, greenT A {i} z k l * toC (A l i)) := by
        rw [e1, e3, hBij]
        field_simp
      rw [heq, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hvar0 i k)]
      have hSS : ‖∑ l, toC (A i l) * greenT A {i} z l k‖ *
          ‖∑ l, greenT A {i} z k l * toC (A l i)‖ ≤ ℓ ^ 2 * V := by
        calc _ ≤ (ℓ * Real.sqrt V) * (ℓ * Real.sqrt V) :=
              mul_le_mul hS1' hS2' (norm_nonneg _) (by positivity)
          _ = ℓ ^ 2 * V := by
              rw [show (ℓ * Real.sqrt V) * (ℓ * Real.sqrt V) = ℓ ^ 2 * (Real.sqrt V) ^ 2 by ring,
                Real.sq_sqrt hV0]
      calc M.var i k * ‖green A z i i‖ * ‖∑ l, toC (A i l) * greenT A {i} z l k‖ *
            ‖∑ l, greenT A {i} z k l * toC (A l i)‖
          = M.var i k * ‖green A z i i‖ * (‖∑ l, toC (A i l) * greenT A {i} z l k‖ *
            ‖∑ l, greenT A {i} z k l * toC (A l i)‖) := by ring
        _ ≤ C₀ / N * ‖green A z i i‖ * (ℓ ^ 2 * V) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hvarC i k) (norm_nonneg _)) hSS
              (by positivity) (by positivity)
        _ = C₀ / N * ‖green A z i i‖ * ℓ ^ 2 * V := by ring
    have hsum := goodEvent_sum_im_le hA hz hN0 {i}
    rw [Finset.card_singleton, Nat.cast_one,
      show (stieltjesEmp A z).im = N * z.im * u by rw [hudef]; field_simp,
      show 1 / ((N : ℝ) * z.im) = v from hvdef.symm] at hsum
    have hPsi2 : w ^ 2 + u + v ^ 2 ≤ (Real.sqrt u + v + w) ^ 2 := by
      have := Real.sq_sqrt hu
      nlinarith [mul_nonneg hsu hv.le, mul_nonneg hsu hw.le, mul_nonneg hv.le hw.le]
    have hGn := norm_nonneg (green A z i i)
    unfold selfA
    calc ‖(M.varMatrix i i : ℂ) * green A z i i + ∑ k, (if k = i then (0 : ℂ) else
          (M.varMatrix i k : ℂ) * green A z i k * green A z k i / green A z i i)‖
        ≤ ‖(M.varMatrix i i : ℂ) * green A z i i‖ + ∑ k, ‖(if k = i then (0 : ℂ) else
          (M.varMatrix i k : ℂ) * green A z i k * green A z k i / green A z i i)‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ C₀ / N * ‖green A z i i‖ + ∑ k, C₀ / N * ‖green A z i i‖ * ℓ ^ 2 *
            (C₀ / N * ((greenT A {i} z k k).im / z.im)) := by
          refine add_le_add ?_ (Finset.sum_le_sum fun k _ => hterm k)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hBij, abs_of_nonneg (hvar0 i i)]
          exact mul_le_mul_of_nonneg_right (hvarC i i) hGn
      _ = C₀ / N * ‖green A z i i‖ + C₀ ^ 2 / N ^ 2 / z.im * ‖green A z i i‖ * ℓ ^ 2 *
            ∑ k, (greenT A {i} z k k).im := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          field_simp
      _ ≤ C₀ / N * ‖green A z i i‖ + C₀ ^ 2 / N ^ 2 / z.im * ‖green A z i i‖ * ℓ ^ 2 *
            (N * (N * z.im * u + v)) := by
          gcongr
      _ = C₀ * ‖green A z i i‖ * w ^ 2 + C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * (u + v ^ 2) := by
          rw [hw2, hv2, hvdef]
          field_simp
      _ ≤ C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * (w ^ 2 + u + v ^ 2) := by
          have h1 : C₀ ≤ C₀ ^ 2 * ℓ ^ 2 := by
            have e1 : C₀ ≤ C₀ ^ 2 := by nlinarith
            have e2 : 1 ≤ ℓ ^ 2 := one_le_pow₀ hℓ1
            calc C₀ ≤ C₀ ^ 2 := e1
              _ = C₀ ^ 2 * 1 := (mul_one _).symm
              _ ≤ C₀ ^ 2 * ℓ ^ 2 := mul_le_mul_of_nonneg_left e2 (sq_nonneg _)
          have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hGn (sq_nonneg w))
          calc C₀ * ‖green A z i i‖ * w ^ 2 + C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * (u + v ^ 2)
              = C₀ * (‖green A z i i‖ * w ^ 2) +
                C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * (u + v ^ 2) := by ring
            _ ≤ C₀ ^ 2 * ℓ ^ 2 * (‖green A z i i‖ * w ^ 2) +
                C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * (u + v ^ 2) := add_le_add_left h3 _
            _ = C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * (w ^ 2 + u + v ^ 2) := by ring
      _ ≤ 2 * C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ * ctrlPsiM x z ^ 2 := by
          have h0 : 0 ≤ C₀ ^ 2 * ℓ ^ 2 * ‖green A z i i‖ := by positivity
          rw [hΨ]
          have h2 : 0 ≤ (Real.sqrt u + v + w) ^ 2 := sq_nonneg _
          have h4 := mul_le_mul_of_nonneg_left hPsi2 h0
          have h5 := mul_nonneg h0 h2
          linarith
  · -- (4.13)
    obtain ⟨-, e2, -⟩ := green_offdiag hA hz hij
    have hR := goodEvent_wardW2 hN0 hA hz {i, j} hC0 (fun k => M.var i k) (fun l => M.var l j)
      (hvar0 i) (hvarC i) (fun l => hvarC l j)
    rw [Finset.card_pair hij, ← hudef, show ((2 : ℕ) : ℝ) / (N * z.im) ^ 2 = 2 * v ^ 2 by
      rw [hv2]; push_cast; ring] at hR
    have hR' : Real.sqrt (∑ k, ∑ l, M.var i k * ‖greenT A {i, j} z k l‖ ^ 2 * M.var l j) ≤
        C₀ * (Real.sqrt u + 2 * v) :=
      (Real.sqrt_le_sqrt hR).trans (goodEvent_sqrt_le hC0 hu hv.le (by norm_num))
    have hS4 := hG4 i j hij
    have hfac : ‖toC (A i j) -
        ∑ k, ∑ l, toC (A i k) * greenT A {i, j} z k l * toC (A l j)‖ ≤
        3 * C₀ * ℓ ^ 2 * ctrlPsiM x z := by
      calc _ ≤ ‖toC (A i j)‖ + ‖∑ k, ∑ l, toC (A i k) * greenT A {i, j} z k l * toC (A l j)‖ :=
            norm_sub_le _ _
        _ ≤ ℓ ^ 2 * (C₀ * w) + ℓ ^ 2 * (C₀ * (Real.sqrt u + 2 * v)) := by
            refine add_le_add ((hent i j).trans ?_)
              (hS4.trans (mul_le_mul_of_nonneg_left hR' (sq_nonneg _)))
            gcongr
            linarith
        _ ≤ 3 * C₀ * ℓ ^ 2 * ctrlPsiM x z := by
            rw [hΨ]
            have h0 : 0 ≤ ℓ ^ 2 * C₀ := mul_nonneg (sq_nonneg _) hC0
            have h1 := mul_nonneg h0 hsu
            have h2 := mul_nonneg h0 hw.le
            have h3 := mul_nonneg h0 hv.le
            linarith
    rw [e2, norm_mul, norm_mul, norm_neg]
    calc ‖green A z i i‖ * ‖greenT A {i} z j j‖ *
          ‖toC (A i j) - ∑ k, ∑ l, toC (A i k) * greenT A {i, j} z k l * toC (A l j)‖
        ≤ ‖green A z i i‖ * ‖greenT A {i} z j j‖ * (3 * C₀ * ℓ ^ 2 * ctrlPsiM x z) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = 3 * C₀ * ℓ ^ 2 * ‖green A z i i‖ * ‖greenT A {i} z j j‖ * ctrlPsiM x z := by ring

/-! ### 9. Lemma 4.4 -/

/-- Lemma 4.4: the good event is closed, has small complement, and gives (4.11)–(4.13). -/
theorem goodEvent_spec {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) (hN : 3 ≤ N)
    {z : ℂ} (hz : 0 < z.im) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ κ) :
    IsClosed (goodEvent M ϑ⁻¹ κ z) ∧
      M.prodLaw (goodEvent M ϑ⁻¹ κ z)ᶜ ≤ ENNReal.ofReal (46 / ϑ * N ^ 4 * Real.exp (-κ)) ∧
      ∀ x ∈ goodEvent M ϑ⁻¹ κ z, ∀ i j, i ≠ j →
        ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ 2 * C₀ * lossL2 ϑ⁻¹ κ N * ctrlPsiM x z ∧
        ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
          2 * C₀ ^ 2 * lossL ϑ⁻¹ κ ^ 2 * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 ∧
        ‖green (toMatrix x) z i j‖ ≤ 3 * C₀ * lossL ϑ⁻¹ κ ^ 2 * ‖green (toMatrix x) z i i‖ *
          ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z := by
  refine ⟨?_, goodEvent_prob hM hϑ hϑ1 hN hz hκ,
    fun x hx i j hij => goodEvent_consequences hM hϑ hϑ1 hC₀ hN hz hκ hx hij⟩
  have hE : ∀ k l : Fin N, Continuous fun x : Pair N → 𝕜 => toMatrix x k l :=
    fun k l => (goodEvent_continuous_ent k l).comp (continuous_apply _)
  have hC := goodEvent_cont_entry (𝕜 := 𝕜) (N := N)
  have hG := goodEvent_cont_greenT (𝕜 := 𝕜) (N := N) hz
  have hZ := goodEvent_cont_selfZ M hz
  unfold goodEvent
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter (isClosed_iInter fun k => isClosed_iInter fun l =>
    isClosed_le (by fun_prop) (by fun_prop)) (IsClosed.inter (isClosed_iInter fun i =>
      isClosed_le (by fun_prop) (by fun_prop)) (IsClosed.inter (isClosed_iInter fun i =>
        isClosed_iInter fun j => isClosed_iInter fun _ => IsClosed.inter
          (isClosed_le (by fun_prop) (by fun_prop)) (isClosed_le (by fun_prop) (by fun_prop)))
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le (by fun_prop) (by fun_prop))))

end Rigidity
