module

public import Rigidity.Fluctuation.Structure
public import Rigidity.Probability.LDMoment

@[expose] public section

/-!
# Conditional moments (NP v1.1, §6.2–6.3: (6.9), Lemma 6.4 (d), Lemma 6.5)

Numbers in this file refer to the blueprint NP v1.1.

`P_T f` is `rowInt M T f` and `‖f‖_{q,T}` is `rowNorm M T q f`; `M^L` is `schurM (toMatrix x) L z`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `C_m = max(C_ϑ^a, C_LD²)` of (6.9) (`a = 1/ϑ`). -/
noncomputable def faCm (a : ℝ) : ℝ := max (cTheta a ^ a) (cLD a ^ 2)

/-! ### 1. Entries of a point with the rows `T` replaced -/

section Entries

open ProbabilityTheory

variable {N : ℕ}

omit [RCLike 𝕜] in
/-- The coordinate `{i, j}` lies in the rows `T` exactly when `i` or `j` does. -/
private lemma moments_mk'_mem_rowsQ {T : Finset (Fin N)} {i j : Fin N} :
    Pair.mk' i j ∈ rowsQ T ↔ i ∈ T ∨ j ∈ T := by
  unfold Pair.mk' rowsQ
  by_cases h : i ≤ j
  · simp [h]
  · simp [h, or_comm]

omit [RCLike 𝕜] in
/-- Distinct entries of the row `c` are distinct coordinates. -/
private lemma moments_mk'_injective (c : Fin N) : Function.Injective (Pair.mk' c) := by
  intro a b h
  unfold Pair.mk' at h
  by_cases h1 : c ≤ a <;> by_cases h2 : c ≤ b <;>
    simp [h1, h2, Subtype.ext_iff, Prod.ext_iff] at h <;> omega

omit [RCLike 𝕜] in
/-- `𝒬` is monotone in the rows. -/
private lemma moments_rowsQ_mono {T₁ T : Finset (Fin N)} (h : T₁ ⊆ T) : rowsQ T₁ ⊆ rowsQ T := by
  intro p hp
  simp only [rowsQ, Set.mem_ofPred_eq] at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (h hp)
  · exact Or.inr (h hp)

/-- The coordinate `{c, k}` of the rows `T ∋ c`, as an element of `𝒬(T)`. -/
private abbrev moments_pk {T : Finset (Fin N)} {c : Fin N} (hc : c ∈ T) (k : Fin N) : rowsQ T :=
  ⟨Pair.mk' c k, moments_mk'_mem_rowsQ.2 (Or.inl hc)⟩

/-- `h_ck` as a function of the coordinate `x_{ck}`, for `k ≠ c`. -/
private def moments_coord (c k : Fin N) (u : 𝕜) : 𝕜 := if c < k then u else star u

private lemma moments_norm_coord (c k : Fin N) (u : 𝕜) : ‖moments_coord c k u‖ = ‖u‖ := by
  unfold moments_coord
  split_ifs
  · rfl
  · exact norm_star u

private lemma moments_continuous_coord (c k : Fin N) :
    Continuous (moments_coord c k : 𝕜 → 𝕜) := by
  unfold moments_coord
  split_ifs
  · exact continuous_id
  · exact continuous_star

/-- `h_ck` at the point equal to `x` outside the rows `T` and to `y` on them, for `c ∈ T`,
`k ≠ c`. -/
private lemma moments_toMatrix_merge_off {T : Finset (Fin N)} (x : Pair N → 𝕜)
    (y : rowsQ T → 𝕜) {c k : Fin N} (hc : c ∈ T) (hk : k ≠ c) :
    toMatrix (piMerge (rowsQ T) x y) c k = moments_coord c k (y (moments_pk hc k)) := by
  have hm : piMerge (rowsQ T) x y (Pair.mk' c k) = y (moments_pk hc k) := by
    simp [piMerge, moments_mk'_mem_rowsQ.2 (Or.inl hc)]
  unfold toMatrix moments_coord
  simp only [Matrix.of_apply]
  rcases lt_or_gt_of_ne hk.symm with h | h
  · simp [h, hm]
  · simp [not_lt.2 h.le, h, hm]

/-- `h_cc` at the point equal to `x` outside the rows `T` and to `y` on them, for `c ∈ T`. -/
private lemma moments_toMatrix_merge_diag {T : Finset (Fin N)} (x : Pair N → 𝕜)
    (y : rowsQ T → 𝕜) {c : Fin N} (hc : c ∈ T) :
    toMatrix (piMerge (rowsQ T) x y) c c = ((RCLike.re (y (moments_pk hc c)) : ℝ) : 𝕜) := by
  have hm : piMerge (rowsQ T) x y (Pair.mk' c c) = y (moments_pk hc c) := by
    simp [piMerge, moments_mk'_mem_rowsQ.2 (Or.inl hc)]
  unfold toMatrix
  simp [hm]

/-- `h_ij` with `i, j ∉ T` is unchanged when the rows `T` are replaced. -/
private lemma moments_toMatrix_merge_out {T : Finset (Fin N)} (x : Pair N → 𝕜)
    (y : rowsQ T → 𝕜) {i j : Fin N} (hi : i ∉ T) (hj : j ∉ T) :
    toMatrix (piMerge (rowsQ T) x y) i j = toMatrix x i j := by
  have hm : Pair.mk' i j ∉ rowsQ T := fun h => by
    rcases moments_mk'_mem_rowsQ.1 h with h | h <;> contradiction
  simp only [toMatrix, Matrix.of_apply, piMerge, hm, dite_false]

/-- `G^{(L)}` is unchanged when rows `T ⊆ L` are replaced. -/
private lemma moments_greenT_merge (M : Ensemble 𝕜 N) {T L : Finset (Fin N)} (hT : T ⊆ L)
    (z : ℂ) (x : Pair N → 𝕜) (y : rowsQ T → 𝕜) (k l : Fin N) :
    greenT (toMatrix (piMerge (rowsQ T) x y)) L z k l = greenT (toMatrix x) L z k l :=
  (noDep_greenT M 0 L z).1 k l _ _ fun p hp => by
    have : p ∉ rowsQ T := fun h => hp (moments_rowsQ_mono hT h)
    simp [piMerge, this]

/-- `G^{(L)}` vanishes when one of its indices lies in `L`. -/
private lemma moments_greenT_of_mem {A : Matrix (Fin N) (Fin N) 𝕜} {L : Finset (Fin N)} {z : ℂ}
    {k l : Fin N} (h : k ∈ L ∨ l ∈ L) : greenT A L z k l = 0 := by
  rcases h with h | h <;> simp [greenT, h]

/-- The map `y ↦ (x outside J, y on J)` is measurable. -/
private lemma moments_measurable_merge (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    (x : Pair N → 𝕜) : Measurable (piMerge J x) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ J
  · have : (fun y : J → 𝕜 => piMerge J x y i) = fun y => y ⟨i, h⟩ := by
      funext y; simp [piMerge, h]
    rw [this]
    exact measurable_pi_apply _
  · have : (fun y : J → 𝕜 => piMerge J x y i) = fun _ => x i := by
      funext y; simp [piMerge, h]
    rw [this]
    exact measurable_const

end Entries

/-! ### 2. The map `toC` -/

section ToC

private lemma moments_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

private lemma moments_continuous_toC : Continuous (toC : 𝕜 → ℂ) := by
  have : (toC : 𝕜 → ℂ) =
      fun y => ((RCLike.re y : ℝ) : ℂ) + ((RCLike.im y : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [toC]
  rw [this]
  fun_prop

private lemma moments_toC_star (y : 𝕜) : toC (star y) = starRingEnd ℂ (toC y) := by
  apply Complex.ext <;> simp [toC, RCLike.star_def]

private lemma moments_toC_ofReal (r : ℝ) : toC (RCLike.ofReal r : 𝕜) = (r : ℂ) := by
  apply Complex.ext <;> simp [toC]

private lemma moments_toC_zero : toC (0 : 𝕜) = 0 := by
  apply Complex.ext <;> simp [toC]

private lemma moments_toC_mul_star (c : 𝕜) : toC c * toC (star c) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [toC, RCLike.norm_sq_eq_def, RCLike.star_def]
  ring

/-- The integral commutes with `toC`. -/
private lemma moments_integral_toC {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) : ∫ a, toC (f a) ∂μ = toC (∫ a, f a ∂μ) := by
  have hre := integral_re hf
  have him := integral_im hf
  have h : (fun a => toC (f a)) =
      fun a => ((RCLike.re (f a) : ℝ) : ℂ) + ((RCLike.im (f a) : ℝ) : ℂ) * Complex.I := by
    funext a
    apply Complex.ext <;> simp [toC]
  rw [h, integral_add hf.re.ofReal (hf.im.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hre, him]
  apply Complex.ext <;> simp [toC]

/-- The entries `x ↦ h_ab(x)` are continuous. -/
private lemma moments_continuous_entry {N : ℕ} (a b : Fin N) :
    Continuous fun x : Pair N → 𝕜 => toC (toMatrix x a b) := by
  refine moments_continuous_toC.comp ?_
  unfold toMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact RCLike.continuous_ofReal.comp (RCLike.continuous_re.comp (continuous_apply _))

/-- For fixed `z` with `Im z > 0`, the entries `x ↦ G^{(T)}_ij(x)` are continuous. -/
private lemma moments_continuous_greenT {N : ℕ} {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N))
    (i j : Fin N) : Continuous fun x : Pair N → 𝕜 => greenT (toMatrix x) T z i j := by
  have h : Continuous fun x : Pair N → 𝕜 =>
      (fun q : (Pair N → 𝕜) × {z : ℂ // 0 < z.im} => greenT (toMatrix q.1) T q.2 i j)
        (x, ⟨z, hz⟩) :=
    (continuous_greenT T i j).comp (continuous_id.prodMk continuous_const)
  exact h

end ToC

/-! ### 3. Lemma 6.4 (d): the expectation in one row -/

section Expectation

open ProbabilityTheory

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `σ_ij² ≥ 0`. -/
private lemma moments_var_nonneg (i j : Fin N) : 0 ≤ M.var i j :=
  integral_nonneg fun _ => sq_nonneg _

/-- Every moment of an entry is finite: under (2.17) with `ϑ > 0` by Lemma 4.1 (a), and for
`ϑ ≤ 0` the right-hand side of (2.17) vanishes, so that the entry is bounded almost surely. -/
private lemma moments_integrable_norm_pow {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) (m : ℕ) : Integrable (fun y : 𝕜 => ‖y‖ ^ m) (M.law p) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  by_cases hϑ : 0 < ϑ
  · have hϑ' : 0 < min ϑ 1 := lt_min hϑ one_pos
    have hM' := Ensemble.Assumptions.mono M hM hϑ' (min_le_left _ _) le_rfl le_rfl le_rfl
    have hmom := (moments_bound hϑ' (min_le_right _ _) (μ := M.law p)
      (s := Real.sqrt (M.varPair p)) (Real.sqrt_nonneg _) (hM'.subexp p)
      (q := (m : ℝ)) (by exact_mod_cast hm)).1
    simpa only [Real.rpow_natCast] using hmom
  · have hϑ0 : ϑ⁻¹ ≤ 0 := inv_nonpos.2 (not_lt.1 hϑ)
    have h0 : M.law p {y | 1 * Real.sqrt (M.varPair p) < ‖y‖} = 0 := by
      refine le_antisymm ((hM.subexp p 1 le_rfl).trans ?_) zero_le
      refine le_of_eq (ENNReal.ofReal_of_nonpos ?_)
      nlinarith [Real.exp_pos (-((1 : ℝ) ^ ϑ))]
    have hae : ∀ᵐ y ∂M.law p, ‖y‖ ≤ Real.sqrt (M.varPair p) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with y hy
      simpa using hy
    refine (integrable_const ((Real.sqrt (M.varPair p)) ^ m)).mono'
      (measurable_norm.pow_const m).aestronglyMeasurable ?_
    filter_upwards [hae] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hy m

/-- A function of one coordinate of the product law is integrable when it is integrable against
the entry law. -/
private lemma moments_integrable_coord (T : Finset (Fin N)) (p : rowsQ T) {E : Type*}
    [NormedAddCommGroup E] {g : 𝕜 → E} (hg : Integrable g (M.law p)) :
    Integrable (fun y : rowsQ T → 𝕜 => g (y p)) (Measure.pi fun q : rowsQ T => M.law q) :=
  (measurePreserving_eval (fun q : rowsQ T => M.law q) p).integrable_comp_of_integrable hg

/-- The integral of a function of one coordinate of the product law is the integral against the
entry law. -/
private lemma moments_integral_coord (T : Finset (Fin N)) (p : rowsQ T) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : 𝕜 → E}
    (hg : AEStronglyMeasurable g (M.law p)) :
    ∫ y : rowsQ T → 𝕜, g (y p) ∂(Measure.pi fun q : rowsQ T => M.law q) =
      ∫ u, g u ∂M.law p := by
  have hmp := measurePreserving_eval (fun q : rowsQ T => M.law q) p
  calc ∫ y : rowsQ T → 𝕜, g (y p) ∂(Measure.pi fun q : rowsQ T => M.law q)
      = ∫ u, g u ∂((Measure.pi fun q : rowsQ T => M.law q).map (Function.eval p)) :=
        (integral_map hmp.measurable.aemeasurable (by rwa [hmp.map_eq])).symm
    _ = ∫ u, g u ∂M.law p := by rw [hmp.map_eq]

/-- A continuous function of an entry with the same norm is integrable against the entry law. -/
private lemma moments_integrable_toC_comp {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) {f : 𝕜 → 𝕜} (hf : Continuous f) (hn : ∀ u, ‖f u‖ = ‖u‖) :
    Integrable (fun u => toC (f u)) (M.law p) := by
  refine (moments_integrable_norm_pow M hM p 1).mono'
    (moments_continuous_toC.comp hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [moments_norm_toC, hn, pow_one]

/-- `∫ h_ck = 0` for a mean-zero entry, with `h_ck` the coordinate or its conjugate. -/
private lemma moments_integral_coord_zero (hM0 : M.MeanZero) (c k : Fin N) (p : Pair N) :
    ∫ u, moments_coord c k u ∂M.law p = 0 := by
  unfold moments_coord
  split_ifs
  · exact hM0 p
  · have : ∫ u, star u ∂M.law p = star (∫ u, u ∂M.law p) := integral_conj
    rw [this, hM0 p, star_zero]

/-- `h_ci` as a random variable on the rows `T ∋ c`. -/
private noncomputable def moments_ua {T : Finset (Fin N)} {c : Fin N} (hc : c ∈ T) (i : Fin N)
    (y : rowsQ T → 𝕜) : ℂ :=
  toC (moments_coord c i (y (moments_pk hc i)))

/-- `h_ic` as a random variable on the rows `T ∋ c`. -/
private noncomputable def moments_va {T : Finset (Fin N)} {c : Fin N} (hc : c ∈ T) (i : Fin N)
    (y : rowsQ T → 𝕜) : ℂ :=
  toC (star (moments_coord c i (y (moments_pk hc i))))

/-- The expectation of a quadratic form `∑_{i,j} G_ij h_ci h_jc` in the rows `T ∋ c`: the
off-diagonal terms vanish by independence and mean zero, and `E|h_ci|² = σ_ci²`; the
matrix `G` is arbitrary. -/
private lemma moments_integral_quadratic {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    {T : Finset (Fin N)} {c : Fin N} (hc : c ∈ T) (G : Fin N → Fin N → ℂ) :
    Integrable (fun y : rowsQ T → 𝕜 => ∑ i, ∑ j, G i j * (moments_ua hc i y * moments_va hc j y))
        (Measure.pi fun p : rowsQ T => M.law p) ∧
    ∫ y : rowsQ T → 𝕜, ∑ i, ∑ j, G i j * (moments_ua hc i y * moments_va hc j y)
        ∂(Measure.pi fun p : rowsQ T => M.law p) =
      ∑ i, (M.var c i : ℂ) * G i i := by
  set ν := Measure.pi fun p : rowsQ T => M.law p with hν
  have hind : iIndepFun (fun (p : rowsQ T) (y : rowsQ T → 𝕜) => y p) ν :=
    iIndepFun_pi (μ := fun p : rowsQ T => M.law p) (X := fun _ (z : 𝕜) => z)
      fun _ => aemeasurable_id
  have hφc : ∀ i, Continuous fun u : 𝕜 => toC (moments_coord c i u) := fun i =>
    moments_continuous_toC.comp (moments_continuous_coord c i)
  have hψc : ∀ i, Continuous fun u : 𝕜 => toC (star (moments_coord c i u)) := fun i =>
    moments_continuous_toC.comp (continuous_star.comp (moments_continuous_coord c i))
  have hua_cont : ∀ i, Continuous (moments_ua hc i) := fun i =>
    (hφc i).comp (continuous_apply _)
  have hva_cont : ∀ i, Continuous (moments_va hc i) := fun i =>
    (hψc i).comp (continuous_apply _)
  have hφi : ∀ i, Integrable (fun u : 𝕜 => toC (moments_coord c i u))
      (M.law (moments_pk hc i)) := fun i =>
    moments_integrable_toC_comp M hM _ (moments_continuous_coord c i) (moments_norm_coord c i)
  have hψi : ∀ i, Integrable (fun u : 𝕜 => toC (star (moments_coord c i u)))
      (M.law (moments_pk hc i)) := fun i =>
    moments_integrable_toC_comp M hM _ (continuous_star.comp (moments_continuous_coord c i))
      (fun u => by rw [norm_star, moments_norm_coord])
  have hua_int : ∀ i, Integrable (moments_ua hc i) ν := fun i =>
    moments_integrable_coord M T (moments_pk hc i) (hφi i)
  have hva_int : ∀ i, Integrable (moments_va hc i) ν := fun i =>
    moments_integrable_coord M T (moments_pk hc i) (hψi i)
  have hcoord_int : ∀ i, Integrable (moments_coord c i) (M.law (moments_pk hc i)) := fun i =>
    (moments_integrable_norm_pow M hM _ 1).mono'
      (moments_continuous_coord c i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [moments_norm_coord, pow_one])
  have hua_mean : ∀ i, ∫ y, moments_ua hc i y ∂ν = 0 := fun i => by
    unfold moments_ua
    rw [moments_integral_coord M T (moments_pk hc i) (hφc i).aestronglyMeasurable,
      moments_integral_toC (hcoord_int i), moments_integral_coord_zero M hM.meanZero,
      moments_toC_zero]
  have hindep : ∀ i j, i ≠ j → IndepFun (moments_ua hc i) (moments_va hc j) ν :=
      fun i j hij => by
    have hne : moments_pk hc i ≠ moments_pk hc j := fun h =>
      hij (moments_mk'_injective c (congrArg Subtype.val h))
    exact (hind.indepFun hne).comp (hφc i).measurable (hψc j).measurable
  have hoff : ∀ i j, i ≠ j → ∫ y, moments_ua hc i y * moments_va hc j y ∂ν = 0 :=
      fun i j hij => by
    rw [(hindep i j hij).integral_fun_mul_eq_mul_integral (hua_cont i).aestronglyMeasurable
      (hva_cont j).aestronglyMeasurable, hua_mean, zero_mul]
  have hoff_int : ∀ i j, i ≠ j → Integrable (fun y => moments_ua hc i y * moments_va hc j y) ν :=
    fun i j hij => (hindep i j hij).integrable_mul (hua_int i) (hva_int j)
  have hdiag_eq : ∀ (i : Fin N) (y : rowsQ T → 𝕜),
      moments_ua hc i y * moments_va hc i y = (((‖y (moments_pk hc i)‖ ^ 2 : ℝ)) : ℂ) :=
    fun i y => by
    unfold moments_ua moments_va
    rw [moments_toC_mul_star, moments_norm_coord]
  have hdiag_int : ∀ i, Integrable (fun y => moments_ua hc i y * moments_va hc i y) ν :=
      fun i => by
    have hg : Integrable (fun u : 𝕜 => (((‖u‖ ^ 2 : ℝ)) : ℂ)) (M.law (moments_pk hc i)) :=
      (moments_integrable_norm_pow M hM _ 2).ofReal
    exact (moments_integrable_coord M T (moments_pk hc i) hg).congr
      (Filter.Eventually.of_forall fun y => (hdiag_eq i y).symm)
  have hdiag : ∀ i, ∫ y, moments_ua hc i y * moments_va hc i y ∂ν = (M.var c i : ℂ) :=
      fun i => by
    simp only [hdiag_eq]
    rw [integral_complex_ofReal]
    have h := moments_integral_coord M T (moments_pk hc i) (g := fun u : 𝕜 => ‖u‖ ^ 2)
      (measurable_norm.pow_const 2).aestronglyMeasurable
    have h' : ∫ y : rowsQ T → 𝕜, ‖y (moments_pk hc i)‖ ^ 2 ∂ν = M.var c i := h
    rw [h']
  have hterm_int : ∀ i j, Integrable
      (fun y => G i j * (moments_ua hc i y * moments_va hc j y)) ν := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact (hdiag_int i).const_mul _
    · exact (hoff_int i j hij).const_mul _
  have hterm : ∀ i j, ∫ y, G i j * (moments_ua hc i y * moments_va hc j y) ∂ν =
      if i = j then (M.var c i : ℂ) * G i i else 0 := fun i j => by
    rw [integral_const_mul]
    split_ifs with hij
    · subst hij
      rw [hdiag]
      ring
    · rw [hoff i j hij, mul_zero]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm_int i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm_int i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hterm_int i j]
  simp only [hterm]
  simp

/-- The real part of a mean-zero entry has expectation `0`. -/
private lemma moments_integral_re_zero {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) : ∫ u : 𝕜, ((RCLike.re u : ℝ) : ℂ) ∂M.law p = 0 := by
  have hint : Integrable (fun u : 𝕜 => u) (M.law p) :=
    (moments_integrable_norm_pow M hM p 1).mono' aestronglyMeasurable_id
      (Filter.Eventually.of_forall fun u => by rw [pow_one])
  rw [integral_complex_ofReal, integral_re hint, hM.meanZero p]
  simp

/-- The real part of an entry is integrable against the entry law. -/
private lemma moments_integrable_re {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) : Integrable (fun u : 𝕜 => ((RCLike.re u : ℝ) : ℂ)) (M.law p) :=
  (moments_integrable_norm_pow M hM p 1).mono'
    (Complex.continuous_ofReal.comp RCLike.continuous_re).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Complex.norm_real, Real.norm_eq_abs, pow_one]
      exact RCLike.abs_re_le_norm u)

end Expectation

/-- Lemma 6.4 (d) for a general index set `L ∋ a`: `P_a M_aa = -z - m_a^{(L)}` and
`Q_a M_aa = h_aa - Z_a^{(L)}`. -/
theorem rowInt_schurM_diag {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) {a : Fin N} (ha : a ∈ L) (x : Pair N → 𝕜) :
    rowInt M {a} (fun w => schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩) x = -z - mL M L z a x ∧
      schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩ -
          rowInt M {a} (fun w => schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩) x =
        toC (toMatrix x a a) - selfZL M L z a x := by
  have _ := hϑ
  have _ := hz
  have haa : a ∈ ({a} : Finset (Fin N)) := Finset.mem_singleton_self a
  have hsub : ({a} : Finset (Fin N)) ⊆ L := Finset.singleton_subset_iff.2 ha
  set ν := Measure.pi fun p : rowsQ ({a} : Finset (Fin N)) => M.law p with hν
  have hslice : ∀ y : rowsQ ({a} : Finset (Fin N)) → 𝕜,
      schurM (toMatrix (piMerge (rowsQ {a}) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩ =
        ((RCLike.re (y (moments_pk haa a)) : ℝ) : ℂ) - z -
          ∑ i, ∑ j, greenT (toMatrix x) L z i j *
            (moments_ua haa i y * moments_va haa j y) := fun y => by
    have hAw := toMatrix_isHermitian (piMerge (rowsQ {a}) x y)
    simp only [schurM, Matrix.of_apply, ite_true]
    rw [moments_toMatrix_merge_diag x y haa, moments_toC_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [moments_greenT_merge M hsub]
    by_cases h : i ∈ L ∨ j ∈ L
    · simp [moments_greenT_of_mem h]
    · obtain ⟨h1, h2⟩ := not_or.1 h
      have hia : i ≠ a := fun e => h1 (e ▸ ha)
      have hja : j ≠ a := fun e => h2 (e ▸ ha)
      have hb : toMatrix (piMerge (rowsQ {a}) x y) j a =
          star (toMatrix (piMerge (rowsQ {a}) x y) a j) := (hAw.apply j a).symm
      rw [moments_toMatrix_merge_off x y haa hia, hb, moments_toMatrix_merge_off x y haa hja]
      unfold moments_ua moments_va
      ring
  have hrow : rowInt M {a} (fun w => schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩) x =
      -z - mL M L z a x := by
    change ∫ y, schurM (toMatrix (piMerge (rowsQ {a}) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩ ∂ν = _
    simp only [hslice]
    obtain ⟨hSint, hSval⟩ := moments_integral_quadratic M hM haa (greenT (toMatrix x) L z)
    have hSint' : Integrable (fun y : rowsQ ({a} : Finset (Fin N)) → 𝕜 =>
        ∑ i, ∑ j, greenT (toMatrix x) L z i j * (moments_ua haa i y * moments_va haa j y)) ν :=
      hSint
    have hSval' : ∫ y : rowsQ ({a} : Finset (Fin N)) → 𝕜,
        ∑ i, ∑ j, greenT (toMatrix x) L z i j * (moments_ua haa i y * moments_va haa j y) ∂ν =
        ∑ i, (M.var a i : ℂ) * greenT (toMatrix x) L z i i := hSval
    have hAint : Integrable (fun y : rowsQ ({a} : Finset (Fin N)) → 𝕜 =>
        ((RCLike.re (y (moments_pk haa a)) : ℝ) : ℂ)) ν :=
      moments_integrable_coord M {a} _ (moments_integrable_re M hM _)
    have hAval : ∫ y : rowsQ ({a} : Finset (Fin N)) → 𝕜,
        ((RCLike.re (y (moments_pk haa a)) : ℝ) : ℂ) ∂ν = 0 :=
      (moments_integral_coord M {a} (moments_pk haa a)
        (g := fun u : 𝕜 => ((RCLike.re u : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp RCLike.continuous_re).aestronglyMeasurable).trans
        (moments_integral_re_zero M hM _)
    have hAz : Integrable (fun y : rowsQ ({a} : Finset (Fin N)) → 𝕜 =>
        ((RCLike.re (y (moments_pk haa a)) : ℝ) : ℂ) - z) ν :=
      hAint.sub (integrable_const z)
    rw [integral_sub hAz hSint', integral_sub hAint (integrable_const z), hAval, hSval',
      integral_const]
    simp [mL]
  refine ⟨hrow, ?_⟩
  rw [hrow]
  simp only [schurM, selfZL, mL, Matrix.of_apply, ite_true]
  ring

/-! ### 4. The families of Lemma 4.3 in one row -/

section Families

open ProbabilityTheory

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- The family `(h_ck)_{k}` on the rows `T ∋ c`, with the entries `k ∈ L` replaced by `0`. -/
private noncomputable def moments_X {T : Finset (Fin N)} {c : Fin N} (hc : c ∈ T)
    (L : Finset (Fin N)) (k : Fin N) (y : rowsQ T → 𝕜) : ℂ :=
  if k ∈ L then 0 else moments_ua hc k y

/-- The scales `σ_ck`, `k ∉ L`, and `0` for `k ∈ L`. -/
private noncomputable def moments_s (L : Finset (Fin N)) (c k : Fin N) : ℝ :=
  if k ∈ L then 0 else Real.sqrt (M.var c k)

private lemma moments_s_nonneg (L : Finset (Fin N)) (c k : Fin N) : 0 ≤ moments_s M L c k := by
  unfold moments_s
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

/-- `s_k² ≤ C₀/N` by (C). -/
private lemma moments_s_sq_le {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (L : Finset (Fin N)) (c k : Fin N) : moments_s M L c k ^ 2 ≤ C₀ / N := by
  unfold moments_s
  split_ifs
  · rw [sq, zero_mul]
    exact (moments_var_nonneg M c k).trans (hM.boundC c k)
  · rw [Real.sq_sqrt (moments_var_nonneg M c k)]
    exact hM.boundC c k

/-- The family `(h_ck)_{k ∉ L}` on the rows `T ∋ c`, `c ∈ L`, satisfies (4.1) with the scales
`σ_ck`. -/
private lemma moments_ldHyp {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    {T : Finset (Fin N)} {c : Fin N} (hc : c ∈ T) (L : Finset (Fin N)) :
    LDHyp (Measure.pi fun p : rowsQ T => M.law p) ϑ (moments_X hc L) (moments_s M L c) := by
  set ν := Measure.pi fun p : rowsQ T => M.law p with hν
  have hind : iIndepFun (fun (p : rowsQ T) (y : rowsQ T → 𝕜) => y p) ν :=
    iIndepFun_pi (μ := fun p : rowsQ T => M.law p) (X := fun _ (z : 𝕜) => z)
      fun _ => aemeasurable_id
  have hinj : Function.Injective (moments_pk (T := T) hc) := fun i j h =>
    moments_mk'_injective c (congrArg Subtype.val h)
  have hφc : ∀ k, Continuous fun u : 𝕜 => toC (moments_coord c k u) := fun k =>
    moments_continuous_toC.comp (moments_continuous_coord c k)
  set g : Fin N → 𝕜 → ℂ := fun k u => if k ∈ L then 0 else toC (moments_coord c k u) with hg
  have hgm : ∀ k, Measurable (g k) := fun k => by
    by_cases h : k ∈ L
    · simp only [hg, h, ite_true]; exact measurable_const
    · simp only [hg, h, ite_false]; exact (hφc k).measurable
  have hXg : moments_X hc L = fun k => g k ∘ fun y : rowsQ T → 𝕜 => y (moments_pk hc k) := by
    funext k y
    simp only [moments_X, moments_ua, hg, Function.comp]
  have hcoord_int : ∀ k, Integrable (moments_coord c k) (M.law (moments_pk hc k)) := fun k =>
    (moments_integrable_norm_pow M hM _ 1).mono'
      (moments_continuous_coord c k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [moments_norm_coord, pow_one])
  refine ⟨?_, fun k => ?_, fun k => ?_, moments_s_nonneg M L c, fun k => ?_, fun k t ht => ?_⟩
  · rw [hXg]
    exact (hind.precomp hinj).comp g hgm
  · rw [hXg]
    exact (hgm k).comp (measurable_pi_apply _)
  · by_cases h : k ∈ L
    · simp [moments_X, h]
    · simp only [moments_X, h, ite_false, moments_ua]
      rw [moments_integral_coord M T (moments_pk hc k) (hφc k).aestronglyMeasurable,
        moments_integral_toC (hcoord_int k), moments_integral_coord_zero M hM.meanZero,
        moments_toC_zero]
  · by_cases h : k ∈ L
    · simp [moments_X, moments_s, h]
    · simp only [moments_X, moments_s, h, ite_false, moments_ua]
      rw [Real.sq_sqrt (moments_var_nonneg M c k)]
      have e : ∀ y : rowsQ T → 𝕜, ‖toC (moments_coord c k (y (moments_pk hc k)))‖ ^ 2 =
          ‖y (moments_pk hc k)‖ ^ 2 := fun y => by rw [moments_norm_toC, moments_norm_coord]
      simp only [e]
      exact moments_integral_coord M T (moments_pk hc k) (g := fun u : 𝕜 => ‖u‖ ^ 2)
        (measurable_norm.pow_const 2).aestronglyMeasurable
  · by_cases h : k ∈ L
    · simp [moments_X, moments_s, h]
    · simp only [moments_X, moments_s, h, ite_false, moments_ua]
      have hm : MeasurableSet {u : 𝕜 | t * Real.sqrt (M.varPair (moments_pk hc k)) < ‖u‖} :=
        measurableSet_lt measurable_const measurable_norm
      have e : {y : rowsQ T → 𝕜 |
          t * Real.sqrt (M.var c k) < ‖toC (moments_coord c k (y (moments_pk hc k)))‖} =
          Function.eval (moments_pk hc k) ⁻¹'
            {u : 𝕜 | t * Real.sqrt (M.varPair (moments_pk hc k)) < ‖u‖} := by
        ext y
        simp [moments_norm_toC, moments_norm_coord, Ensemble.var]
      rw [e, (measurePreserving_eval (fun p : rowsQ T => M.law p) _).measure_preimage
        hm.nullMeasurableSet]
      exact hM.subexp _ t ht

end Families

/-! ### 5. `L^q` norms on the rows, entry moments and the Ward bound (6.11) -/

section Norms

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- An `L^q` bound from a bound on `∫ |f|^q`. -/
private lemma moments_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) {q R : ℝ} (hq : 0 < q)
    (h : ∫⁻ y, ‖f y‖ₑ ^ q ∂μ ≤ ENNReal.ofReal R ^ q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal R := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]
  calc (∫⁻ y, ‖f y‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (ENNReal.ofReal R ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal R := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- A bound on `∫ |f|^q` from an `L^q` bound. -/
private lemma moments_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 0 < q) {c : ℝ≥0∞}
    (h : eLpNorm f (ENNReal.ofReal q) μ ≤ c) : ∫⁻ y, ‖f y‖ₑ ^ q ∂μ ≤ c ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le] at h
  calc ∫⁻ y, ‖f y‖ₑ ^ q ∂μ = ((∫⁻ y, ‖f y‖ₑ ^ q ∂μ) ^ (1 / q)) ^ q := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
    _ ≤ c ^ q := ENNReal.rpow_le_rpow h hq.le

/-- Lemma 4.1 (a) for one coordinate of the rows `T`:
`‖y_p‖_{L^q} ≤ (C_ϑ q)^{1/ϑ} σ_p`. -/
private lemma moments_eLpNorm_coord {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (T : Finset (Fin N)) (p : rowsQ T) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun y : rowsQ T → 𝕜 => y p) (ENNReal.ofReal q)
        (Measure.pi fun p : rowsQ T => M.law p) ≤
      ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.varPair p)) := by
  have hq0 : 0 < q := by linarith
  have hmp := measurePreserving_eval (fun p : rowsQ T => M.law p) p
  have h1 : eLpNorm (fun y : rowsQ T → 𝕜 => y p) (ENNReal.ofReal q)
      (Measure.pi fun p : rowsQ T => M.law p) = eLpNorm (fun u : 𝕜 => u) (ENNReal.ofReal q)
        (M.law p) :=
    eLpNorm_comp_measurePreserving (g := fun u : 𝕜 => u) aestronglyMeasurable_id hmp
  rw [h1]
  obtain ⟨hint, hb⟩ := moments_bound hϑ hϑ1 (μ := M.law p) (Real.sqrt_nonneg (M.varPair p))
    (fun t ht => hM.subexp p t ht) hq
  have hC : 0 ≤ cTheta ϑ⁻¹ * q := by unfold cTheta; have := inv_pos.2 hϑ; positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top
    continuous_id'.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  have hl : ∫⁻ u, ‖u‖ₑ ^ q ∂M.law p = ENNReal.ofReal (∫ u, ‖u‖ ^ q ∂M.law p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => by positivity)]
    refine lintegral_congr fun u => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le, ofReal_norm]
  rw [hl, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun u => by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ u, ‖u‖ ^ q ∂M.law p) ^ (1 / q)
      ≤ ((cTheta ϑ⁻¹ * q) ^ (q / ϑ) * Real.sqrt (M.varPair p) ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (integral_nonneg fun u => by positivity) hb (by positivity)
    _ = (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.varPair p) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hC _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _),
          ← Real.rpow_mul hC, ← Real.rpow_mul (Real.sqrt_nonneg _),
          mul_one_div_cancel hq0.ne', Real.rpow_one]
        congr 1
        congr 1
        field_simp

/-- Lemma 3.5 (b) for the minor `H^{(L)}`, column form:
`∑_k |G^{(L)}_kl|² = Im G^{(L)}_ll / η`. -/
private lemma moments_ward_col {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N)) (x : Pair N → 𝕜)
    (l : Fin N) :
    ∑ k, ‖greenT (toMatrix x) L z k l‖ ^ 2 = (greenT (toMatrix x) L z l l).im / z.im := by
  by_cases hl : l ∈ L
  · simp [moments_greenT_of_mem (Or.inr hl)]
  have hP : (minor (toMatrix x) L).IsHermitian :=
    (toMatrix_isHermitian x).submatrix (Subtype.val : {i // i ∉ L} → Fin N)
  have hw := (ward hP hz ⟨l, hl⟩).2
  have e1 : ∑ k, ‖greenT (toMatrix x) L z k l‖ ^ 2 =
      ∑ k ∈ Finset.univ.filter (fun k => k ∉ L), ‖greenT (toMatrix x) L z k l‖ ^ 2 :=
    (Finset.sum_filter_of_ne (p := fun k => k ∉ L) fun k _ hk hkL => hk (by
      simp [moments_greenT_of_mem (A := toMatrix x) (z := z) (l := l) (Or.inl hkL)])).symm
  have e2 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ L), ‖greenT (toMatrix x) L z k l‖ ^ 2 =
      ∑ k : {k // k ∉ L}, ‖greenT (toMatrix x) L z k l‖ ^ 2 :=
    Finset.sum_subtype _ (by simp) _
  have e : ∀ k : {k // k ∉ L},
      greenT (toMatrix x) L z k l = green (minor (toMatrix x) L) z k ⟨l, hl⟩ :=
    fun k => by simp [greenT, greenMinor, k.2, hl]
  rw [e1, e2]
  simp only [e]
  rw [hw]
  simp [greenT, greenMinor, hl]

/-- `Im G^{(T)}_kk ≥ 0`. -/
private lemma moments_greenT_im_nonneg {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N))
    (x : Pair N → 𝕜) (k : Fin N) : 0 ≤ (greenT (toMatrix x) L z k k).im := by
  by_cases hk : k ∈ L
  · simp [moments_greenT_of_mem (Or.inl hk)]
  have hP : (minor (toMatrix x) L).IsHermitian :=
    (toMatrix_isHermitian x).submatrix (Subtype.val : {i // i ∉ L} → Fin N)
  have : greenT (toMatrix x) L z k k = green (minor (toMatrix x) L) z ⟨k, hk⟩ ⟨k, hk⟩ := by
    simp [greenT, greenMinor, hk]
  rw [this]
  exact (green_im_diag_pos hP hz _).le

/-- `Im m^{(L)} ≥ 0`. -/
private lemma moments_I_nonneg {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N)) (x : Pair N → 𝕜) :
    0 ≤ (stieltjesT (toMatrix x) L z).im / (N * z.im) := by
  have : (stieltjesT (toMatrix x) L z).im = (N : ℝ)⁻¹ * ∑ l, (greenT (toMatrix x) L z l l).im := by
    simp [stieltjesT, Complex.im_sum]
  rw [this]
  exact div_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun l _ => moments_greenT_im_nonneg hz L x l)) (by positivity)

/-- `Φ_L ≥ 0`. -/
private lemma moments_phiL_nonneg {C₀ : ℝ} (hC0 : 0 ≤ C₀) {z : ℂ}
    (L : Finset (Fin N)) (x : Pair N → 𝕜) : 0 ≤ phiL C₀ L z x := by
  unfold phiL
  have := Real.sqrt_nonneg ((stieltjesT (toMatrix x) L z).im / (N * z.im))
  positivity

/-- (6.11): `∑_{k,l ∉ L} σ_ck² |G^{(L)}_kl|² σ_ld² ≤ C₀² Im m^{(L)} / (Nη)`. -/
private lemma moments_ward {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) {z : ℂ}
    (hz : 0 < z.im) (L : Finset (Fin N)) (hN : 0 < N) (c d : Fin N) (x : Pair N → 𝕜) :
    ∑ k, ∑ l, moments_s M L c k ^ 2 * ‖greenT (toMatrix x) L z k l‖ ^ 2 *
        moments_s M L d l ^ 2 ≤
      C₀ ^ 2 * ((stieltjesT (toMatrix x) L z).im / (N * z.im)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C₀ / N := (moments_var_nonneg M c c).trans (hM.boundC c c)
  have hC0 : 0 ≤ C₀ := by
    have := mul_nonneg hC hNr.le
    rwa [div_mul_cancel₀ _ hNr.ne'] at this
  set G := greenT (toMatrix x) L z with hG
  have h1 : ∑ k, ∑ l, moments_s M L c k ^ 2 * ‖G k l‖ ^ 2 * moments_s M L d l ^ 2 ≤
      ∑ k, ∑ l, C₀ / N * ‖G k l‖ ^ 2 * moments_s M L d l ^ 2 :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
      gcongr
      exact moments_s_sq_le M hM L c k
  have h2 : ∑ k, ∑ l, C₀ / N * ‖G k l‖ ^ 2 * moments_s M L d l ^ 2 =
      C₀ / N * ∑ l, moments_s M L d l ^ 2 * (G l l).im / z.im := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_div_assoc, ← moments_ward_col hz L x l, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h3 : ∑ l, moments_s M L d l ^ 2 * (G l l).im / z.im ≤ ∑ l, C₀ / N * (G l l).im / z.im :=
    Finset.sum_le_sum fun l _ => by
      gcongr
      · exact moments_greenT_im_nonneg hz L x l
      · exact moments_s_sq_le M hM L d l
  have h4 : ∑ l, C₀ / N * (G l l).im / z.im =
      C₀ / N * N * ((stieltjesT (toMatrix x) L z).im / z.im) := by
    have : (stieltjesT (toMatrix x) L z).im = (N : ℝ)⁻¹ * ∑ l, (G l l).im := by
      simp [stieltjesT, hG, Complex.im_sum]
    calc ∑ l, C₀ / N * (G l l).im / z.im = C₀ / N / z.im * ∑ l, (G l l).im := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = _ := by
          rw [this]
          field_simp
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ C₀ / N * ∑ l, C₀ / N * (G l l).im / z.im := mul_le_mul_of_nonneg_left h3 hC
    _ = C₀ ^ 2 * ((stieltjesT (toMatrix x) L z).im / (N * z.im)) := by
        rw [h4]
        field_simp

end Norms

/-! ### 6. Constants -/

section Constants

private lemma moments_kappa_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ kappaTheta a := by
  unfold kappaTheta cTheta
  have h1 : 0 ≤ Real.log a := Real.log_nonneg ha
  have h2 : 0 ≤ Real.log (4 * (90 * a)) := Real.log_nonneg (by linarith)
  positivity

private lemma moments_one_le_cLD {a : ℝ} (ha : 1 ≤ a) : 1 ≤ cLD a := by
  unfold cLD
  have hk := moments_kappa_nonneg ha
  have : 1 ≤ (4 * a + 2 + kappaTheta a) ^ (2 * a + 1) :=
    Real.one_le_rpow (by linarith) (by linarith)
  linarith

private lemma moments_cTheta_le_faCm (a : ℝ) : cTheta a ^ a ≤ faCm a := le_max_left _ _

private lemma moments_cLD_sq_le_faCm (a : ℝ) : cLD a ^ 2 ≤ faCm a := le_max_right _ _

private lemma moments_cLD_le_faCm {a : ℝ} (ha : 1 ≤ a) : cLD a ≤ faCm a := by
  have h := moments_one_le_cLD ha
  nlinarith [moments_cLD_sq_le_faCm a]

/-- `(C_ϑ q)^a ≤ C_ϑ^a (q + ℓ)^e` for `a ≥ 1`, `q ≥ 1`, `ℓ ≥ 0`, `e ≥ a`. -/
private lemma moments_theta_le {a q ℓ e : ℝ} (ha : 1 ≤ a) (hq : 1 ≤ q) (hℓ : 0 ≤ ℓ)
    (he : a ≤ e) : (cTheta a * q) ^ a ≤ cTheta a ^ a * (q + ℓ) ^ e := by
  have hC : 0 ≤ cTheta a := by unfold cTheta; linarith
  rw [Real.mul_rpow hC (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hC _)
  calc q ^ a ≤ (q + ℓ) ^ a := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ (q + ℓ) ^ e := Real.rpow_le_rpow_of_exponent_le (by linarith) he

private lemma moments_faCm_nonneg {a : ℝ} (ha : 1 ≤ a) : 0 ≤ faCm a :=
  le_trans (by linarith [moments_one_le_cLD ha]) (moments_cLD_le_faCm ha)

end Constants

/-! ### 7. Lemma 6.5 (m2) -/

section M2

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `0 ≤ C₀` under (C). -/
private lemma moments_C₀_nonneg {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hN : 0 < N) :
    0 ≤ C₀ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C₀ / N :=
    (moments_var_nonneg M ⟨0, hN⟩ ⟨0, hN⟩).trans (hM.boundC ⟨0, hN⟩ ⟨0, hN⟩)
  have := mul_nonneg hC hNr.le
  rwa [div_mul_cancel₀ _ hNr.ne'] at this

/-- `Z_a^{(L)}` at the point equal to `x` outside the rows `L` and to `y` on them is the centred
quadratic form of Lemma 4.3 in the family `(h_ka)_{k ∉ L}`. -/
private lemma moments_selfZL_merge {z : ℂ} {L : Finset (Fin N)} {a : Fin N} (ha : a ∈ L)
    (x : Pair N → 𝕜) (y : rowsQ L → 𝕜) :
    selfZL M L z a (piMerge (rowsQ L) x y) =
      ∑ i, ∑ j, starRingEnd ℂ (starRingEnd ℂ (moments_X ha L i y)) *
          greenT (toMatrix x) L z i j * starRingEnd ℂ (moments_X ha L j y) -
        ∑ i, ((moments_s M L a i ^ 2 : ℝ) : ℂ) * greenT (toMatrix x) L z i i := by
  have hA := toMatrix_isHermitian (piMerge (rowsQ L) x y)
  unfold selfZL
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [moments_greenT_merge M subset_rfl]
    by_cases h : i ∈ L ∨ j ∈ L
    · simp [moments_greenT_of_mem h]
    · obtain ⟨h1, h2⟩ := not_or.1 h
      have hia : i ≠ a := fun e => h1 (e ▸ ha)
      have hja : j ≠ a := fun e => h2 (e ▸ ha)
      have hb : toMatrix (piMerge (rowsQ L) x y) j a =
          star (toMatrix (piMerge (rowsQ L) x y) a j) := (hA.apply j a).symm
      rw [hb, moments_toMatrix_merge_off x y ha hia, moments_toMatrix_merge_off x y ha hja,
        moments_toC_star, Complex.conj_conj]
      simp [moments_X, moments_ua, h1, h2]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [moments_greenT_merge M subset_rfl]
    by_cases h : i ∈ L
    · simp [moments_greenT_of_mem (Or.inl h)]
    · simp [moments_s, h, Real.sq_sqrt (moments_var_nonneg M a i)]

/-- Lemma 6.5 (m2) as an `L^q` bound on the rows `L`. -/
private lemma moments_m2 {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) {z : ℂ} (hz : 0 < z.im) {L : Finset (Fin N)} {a : Fin N} (ha : a ∈ L)
    {q : ℝ} (hq : 2 ≤ q) (x : Pair N → 𝕜) :
    eLpNorm (fun y : rowsQ L → 𝕜 =>
        schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩ -
          rowInt M {a} (fun w' => schurM (toMatrix w') L z ⟨a, ha⟩ ⟨a, ha⟩)
            (piMerge (rowsQ L) x y)) (ENNReal.ofReal q) (Measure.pi fun p : rowsQ L => M.law p) ≤
      ENNReal.ofReal (faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 3 / 2) * phiL C₀ L z x) := by
  have hN : 0 < N := Fin.pos_iff_nonempty.2 ⟨a⟩
  have hN1 : 1 ≤ N := hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hC0 := moments_C₀_nonneg M hM hN
  set ν := Measure.pi fun p : rowsQ L => M.law p with hν
  set G := greenT (toMatrix x) L z with hG
  set e := 2 * ϑ⁻¹ + 3 / 2 with he
  set I := (stieltjesT (toMatrix x) L z).im / (N * z.im) with hI
  have hX := (moments_ldHyp M hM ha L).conj
  have hf : (fun y : rowsQ L → 𝕜 =>
        schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩ -
          rowInt M {a} (fun w' => schurM (toMatrix w') L z ⟨a, ha⟩ ⟨a, ha⟩)
            (piMerge (rowsQ L) x y)) =
      (fun y => ((RCLike.re (y (moments_pk ha a)) : ℝ) : ℂ)) -
        (fun y => ∑ i, ∑ j, starRingEnd ℂ (starRingEnd ℂ (moments_X ha L i y)) * G i j *
            starRingEnd ℂ (moments_X ha L j y) -
          ∑ i, ((moments_s M L a i ^ 2 : ℝ) : ℂ) * G i i) := by
    funext y
    rw [(rowInt_schurM_diag M hM hϑ hz L ha (piMerge (rowsQ L) x y)).2,
      moments_toMatrix_merge_diag x y ha, moments_toC_ofReal, moments_selfZL_merge M ha x y]
    rfl
  rw [hf]
  refine (eLpNorm_sub_le (by norm_num; linarith)).trans ?_
  have h1 : eLpNorm (fun y : rowsQ L → 𝕜 => ((RCLike.re (y (moments_pk ha a)) : ℝ) : ℂ))
      (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a a)) := by
    refine (eLpNorm_mono ((Complex.continuous_ofReal.comp
      (RCLike.continuous_re.comp (continuous_apply _))).aestronglyMeasurable) fun y => ?_).trans
      (moments_eLpNorm_coord M hM hϑ hϑ1 L (moments_pk ha a) (by linarith))
    change ‖((RCLike.re (y (moments_pk ha a)) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact RCLike.abs_re_le_norm _
  have h2 := ldm_quad hX hϑ hϑ1 hN1 hq G
  have hW := moments_ward M hM hz L hN a a x
  have hsW : Real.sqrt (∑ i, ∑ j, moments_s M L a i ^ 2 * ‖G i j‖ ^ 2 * moments_s M L a j ^ 2) ≤
      C₀ * Real.sqrt I := by
    calc _ ≤ Real.sqrt (C₀ ^ 2 * I) := Real.sqrt_le_sqrt hW
      _ = C₀ * Real.sqrt I := by
          rw [Real.sqrt_mul' _ (moments_I_nonneg hz L x), Real.sqrt_sq hC0]
  have hT := moments_theta_le (ℓ := Real.log N) (e := e) ha1 (by linarith : (1 : ℝ) ≤ q) hlog
    (by rw [he]; linarith)
  have hvar : Real.sqrt (M.var a a) ≤ Real.sqrt (C₀ / N) := Real.sqrt_le_sqrt (hM.boundC a a)
  have hP : 0 ≤ (q + Real.log N) ^ e := Real.rpow_nonneg (by linarith) _
  have hlhs1 : 0 ≤ (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a a) :=
    mul_nonneg (Real.rpow_nonneg (by unfold cTheta; positivity) _) (Real.sqrt_nonneg _)
  have hlhs2 : 0 ≤ cLD ϑ⁻¹ * (q + Real.log N) ^ e *
      Real.sqrt (∑ i, ∑ j, moments_s M L a i ^ 2 * ‖G i j‖ ^ 2 * moments_s M L a j ^ 2) :=
    mul_nonneg (mul_nonneg (by linarith [moments_one_le_cLD ha1]) hP) (Real.sqrt_nonneg _)
  calc _ ≤ ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a a)) +
        ENNReal.ofReal (cLD ϑ⁻¹ * (q + Real.log N) ^ e *
          Real.sqrt (∑ i, ∑ j, moments_s M L a i ^ 2 * ‖G i j‖ ^ 2 * moments_s M L a j ^ 2)) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a a) +
        cLD ϑ⁻¹ * (q + Real.log N) ^ e *
          Real.sqrt (∑ i, ∑ j, moments_s M L a i ^ 2 * ‖G i j‖ ^ 2 * moments_s M L a j ^ 2)) :=
        (ENNReal.ofReal_add hlhs1 hlhs2).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hcm1 := moments_cTheta_le_faCm ϑ⁻¹
        have hcm2 := moments_cLD_le_faCm ha1
        have hct : 0 ≤ cTheta ϑ⁻¹ ^ ϑ⁻¹ := Real.rpow_nonneg (by unfold cTheta; positivity) _
        have hsq : 0 ≤ Real.sqrt (C₀ / N) := Real.sqrt_nonneg _
        have hsI : 0 ≤ Real.sqrt I := Real.sqrt_nonneg _
        have hfa := mul_nonneg (moments_faCm_nonneg ha1) hP
        unfold phiL
        rw [← hI]
        calc (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a a) + cLD ϑ⁻¹ * (q + Real.log N) ^ e *
              Real.sqrt (∑ i, ∑ j, moments_s M L a i ^ 2 * ‖G i j‖ ^ 2 * moments_s M L a j ^ 2)
            ≤ cTheta ϑ⁻¹ ^ ϑ⁻¹ * (q + Real.log N) ^ e * Real.sqrt (C₀ / N) +
              faCm ϑ⁻¹ * (q + Real.log N) ^ e * (C₀ * Real.sqrt I) := by
              gcongr
          _ ≤ faCm ϑ⁻¹ * (q + Real.log N) ^ e * Real.sqrt (C₀ / N) +
              faCm ϑ⁻¹ * (q + Real.log N) ^ e * (C₀ * Real.sqrt I) := by
              have := moments_faCm_nonneg ha1
              gcongr
          _ = _ := by ring

end M2

/-! ### 8. Lemma 6.5 (m1) -/

section M1

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `t^{q/2} = (√t)^q` in `[0, ∞]`. -/
private lemma moments_ofReal_rpow_half {t : ℝ} (ht : 0 ≤ t) (q : ℝ) :
    ENNReal.ofReal t ^ (q / 2) = ENNReal.ofReal (Real.sqrt t) ^ q := by
  conv_lhs => rw [← Real.sq_sqrt ht]
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- `B_ab = ∑_{k,l} h_ak G^{(L)}_kl h_lb`. -/
private noncomputable def moments_B (L : Finset (Fin N)) (z : ℂ) (a b : Fin N)
    (w : Pair N → 𝕜) : ℂ :=
  ∑ k, ∑ l, toC (toMatrix w a k) * greenT (toMatrix w) L z k l * toC (toMatrix w l b)

/-- `Y_k = ∑_l G^{(L)}_kl h_lb`. -/
private noncomputable def moments_Y (L : Finset (Fin N)) (z : ℂ) (b k : Fin N)
    (w : Pair N → 𝕜) : ℂ :=
  ∑ l, greenT (toMatrix w) L z k l * toC (toMatrix w l b)

/-- Integration over the row `a` of `B_ab`, `a ≠ b ∈ L`: by Lemma 4.3 (4.7) for the family
`(h_ak)_{k ∉ L}`, with the coefficients `Y_k`, which do not depend on the row `a`. -/
private lemma moments_B_row {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) {z : ℂ} {L : Finset (Fin N)} {a b : Fin N} (ha : a ∈ L) (hab : a ≠ b)
    {q : ℝ} (hq : 2 ≤ q) (w : Pair N → 𝕜) :
    partialLInt M.law (rowsQ {a}) (fun w' => ‖moments_B L z a b w'‖ₑ ^ q) w ≤
      ENNReal.ofReal (cLD ϑ⁻¹ * (q + Real.log N) ^ (ϑ⁻¹ + 1 / 2) *
        Real.sqrt (∑ k, ‖moments_Y L z b k w‖ ^ 2 * moments_s M L a k ^ 2)) ^ q := by
  have hN1 : 1 ≤ N := Fin.pos_iff_nonempty.2 ⟨a⟩
  have haa : a ∈ ({a} : Finset (Fin N)) := Finset.mem_singleton_self a
  have hsub : ({a} : Finset (Fin N)) ⊆ L := Finset.singleton_subset_iff.2 ha
  have hX := moments_ldHyp M hM haa L
  have hid : ∀ y : rowsQ ({a} : Finset (Fin N)) → 𝕜,
      moments_B L z a b (piMerge (rowsQ {a}) w y) =
        ∑ k, moments_Y L z b k w * moments_X haa L k y := fun y => by
    unfold moments_B moments_Y
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [moments_greenT_merge M hsub]
    by_cases h : k ∈ L ∨ l ∈ L
    · simp [moments_greenT_of_mem h]
    · obtain ⟨h1, h2⟩ := not_or.1 h
      have hka : k ≠ a := fun e => h1 (e ▸ ha)
      have hla : l ∉ ({a} : Finset (Fin N)) := by
        simp only [Finset.mem_singleton]; exact fun e => h2 (e ▸ ha)
      have hba : b ∉ ({a} : Finset (Fin N)) := by
        simp only [Finset.mem_singleton]; exact fun e => hab e.symm
      rw [moments_toMatrix_merge_off w y haa hka, moments_toMatrix_merge_out w y hla hba]
      simp only [moments_X, moments_ua, h1, ite_false]
      ring
  have hmeas : AEStronglyMeasurable (fun y : rowsQ ({a} : Finset (Fin N)) → 𝕜 =>
      ∑ k, moments_Y L z b k w * moments_X haa L k y)
      (Measure.pi fun p : rowsQ ({a} : Finset (Fin N)) => M.law p) :=
    (Finset.measurable_sum _ fun k _ => measurable_const.mul (hX.meas k)).aestronglyMeasurable
  have h := moments_lintegral_le hmeas (by linarith : (0 : ℝ) < q)
    (ldm_linear hX hϑ hϑ1 hN1 hq (fun k => moments_Y L z b k w))
  unfold partialLInt
  simp only [hid]
  exact h

/-- Lemma 6.5 (m1) as an `L^q` bound on the rows `L`. -/
private lemma moments_m1 {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) {z : ℂ} (hz : 0 < z.im) {L : Finset (Fin N)} {a b : Fin N} (ha : a ∈ L)
    (hb : b ∈ L) (hab : a ≠ b) {q : ℝ} (hq : 2 ≤ q) (x : Pair N → 𝕜) :
    eLpNorm (fun y : rowsQ L → 𝕜 =>
        schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨b, hb⟩) (ENNReal.ofReal q)
        (Measure.pi fun p : rowsQ L => M.law p) ≤
      ENNReal.ofReal (faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * phiL C₀ L z x) := by
  have hN : 0 < N := Fin.pos_iff_nonempty.2 ⟨a⟩
  have hN1 : 1 ≤ N := hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hq0 : (0 : ℝ) < q := by linarith
  have hC0 := moments_C₀_nonneg M hM hN
  have hsub : ({a} : Finset (Fin N)) ⊆ L := Finset.singleton_subset_iff.2 ha
  set ν := Measure.pi fun p : rowsQ L => M.law p with hν
  set G := greenT (toMatrix x) L z with hG
  set I := (stieltjesT (toMatrix x) L z).im / (N * z.im) with hI
  set K := cLD ϑ⁻¹ * (q + Real.log N) ^ (ϑ⁻¹ + 1 / 2) with hK
  set W := ∑ k, ∑ l, moments_s M L a k ^ 2 * ‖G k l‖ ^ 2 * moments_s M L b l ^ 2 with hW
  have hK0 : 0 ≤ K := mul_nonneg (by linarith [moments_one_le_cLD ha1])
    (Real.rpow_nonneg (by linarith) _)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by positivity
  have hba : b ≠ a := fun e => hab e.symm
  -- the coefficients `Y_k` on the rows `L`, as linear forms in the family `(h_lb)_{l ∉ L}`
  set Yh : Fin N → (rowsQ L → 𝕜) → ℂ :=
    fun k y => ∑ l, G k l * starRingEnd ℂ (moments_X hb L l y) with hYh
  have hXb := (moments_ldHyp M hM hb L).conj
  have hYid : ∀ k (y : rowsQ L → 𝕜), moments_Y L z b k (piMerge (rowsQ L) x y) = Yh k y :=
      fun k y => by
    have hA := toMatrix_isHermitian (piMerge (rowsQ L) x y)
    unfold moments_Y
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [moments_greenT_merge M subset_rfl]
    by_cases h : k ∈ L ∨ l ∈ L
    · simp [hG, moments_greenT_of_mem h]
    · obtain ⟨-, h2⟩ := not_or.1 h
      have hlb : l ≠ b := fun e => h2 (e ▸ hb)
      have he : toMatrix (piMerge (rowsQ L) x y) l b =
          star (toMatrix (piMerge (rowsQ L) x y) b l) := (hA.apply l b).symm
      rw [he, moments_toMatrix_merge_off x y hb hlb, moments_toC_star]
      simp [moments_X, moments_ua, h2, hG]
  have hYm : ∀ k, Measurable (Yh k) := fun k =>
    Finset.measurable_sum _ fun l _ => measurable_const.mul (hXb.meas l)
  have hYmeas : ∀ k, AEStronglyMeasurable (Yh k) ν := fun k => (hYm k).aestronglyMeasurable
  have hYb : ∀ k, eLpNorm (Yh k) (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal (K * Real.sqrt (∑ l, ‖G k l‖ ^ 2 * moments_s M L b l ^ 2)) := fun k =>
    ldm_linear hXb hϑ hϑ1 hN1 hq (fun l => G k l)
  -- Minkowski in `L^{q/2}`
  set S : (rowsQ L → 𝕜) → ℝ := fun y => ∑ k, ‖Yh k y‖ ^ 2 * moments_s M L a k ^ 2 with hS
  have hS0 : ∀ y, 0 ≤ S y := fun y => Finset.sum_nonneg fun k _ => by positivity
  have hSmeas : ∀ k, AEStronglyMeasurable
      (fun y => ‖Yh k y‖ ^ (2 : ℝ) * moments_s M L a k ^ 2) ν := fun k =>
    (((hYm k).norm.pow_const (2 : ℝ)).mul_const _).aestronglyMeasurable
  have hq2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (q / 2) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hSk : ∀ k, eLpNorm (fun y => ‖Yh k y‖ ^ (2 : ℝ) * moments_s M L a k ^ 2)
      (ENNReal.ofReal (q / 2)) ν ≤ ENNReal.ofReal (moments_s M L a k ^ 2 *
        (K ^ 2 * ∑ l, ‖G k l‖ ^ 2 * moments_s M L b l ^ 2)) := fun k => by
    have e1 : (fun y => ‖Yh k y‖ ^ (2 : ℝ) * moments_s M L a k ^ 2) =
        (moments_s M L a k ^ 2) • (fun y => ‖Yh k y‖ ^ (2 : ℝ)) := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hsum0 : 0 ≤ ∑ l, ‖G k l‖ ^ 2 * moments_s M L b l ^ 2 :=
      Finset.sum_nonneg fun l _ => by positivity
    rw [e1, eLpNorm_const_smul, eLpNorm_norm_rpow _ (hYmeas k) two_pos,
      ← ENNReal.ofReal_mul (by linarith), div_mul_cancel₀ _ two_ne_zero,
      Real.enorm_of_nonneg (by positivity)]
    calc ENNReal.ofReal (moments_s M L a k ^ 2) * eLpNorm (Yh k) (ENNReal.ofReal q) ν ^ (2 : ℝ)
        ≤ ENNReal.ofReal (moments_s M L a k ^ 2) *
            ENNReal.ofReal (K * Real.sqrt (∑ l, ‖G k l‖ ^ 2 * moments_s M L b l ^ 2)) ^ (2 : ℝ) :=
          by gcongr; exact hYb k
      _ = _ := by
          rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (by positivity), mul_pow, Real.sq_sqrt hsum0]
  have hSnorm : eLpNorm (fun y => S y) (ENNReal.ofReal (q / 2)) ν ≤ ENNReal.ofReal (K ^ 2 * W) := by
    have e1 : (fun y => S y) = ∑ k, fun y => ‖Yh k y‖ ^ (2 : ℝ) * moments_s M L a k ^ 2 := by
      funext y
      simp only [hS, Finset.sum_apply, Real.rpow_two]
    rw [e1]
    refine (eLpNorm_sum_le hq2).trans ?_
    refine (Finset.sum_le_sum fun k _ => hSk k).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by
      have : 0 ≤ ∑ l, ‖G k l‖ ^ 2 * moments_s M L b l ^ 2 :=
        Finset.sum_nonneg fun l _ => by positivity
      positivity]
    congr 1
    rw [hW, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hSint : ∫⁻ y, ENNReal.ofReal (S y) ^ (q / 2) ∂ν ≤ ENNReal.ofReal (K ^ 2 * W) ^ (q / 2) := by
    have h := moments_lintegral_le (f := fun y => S y)
      (by
        have : (fun y => S y) = ∑ k, fun y => ‖Yh k y‖ ^ (2 : ℝ) * moments_s M L a k ^ 2 := by
          funext y
          simp only [hS, Finset.sum_apply, Real.rpow_two]
        rw [this]
        exact Finset.aestronglyMeasurable_sum _ fun k _ => hSmeas k)
      (by linarith : (0 : ℝ) < q / 2) hSnorm
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) h
    rw [Real.enorm_of_nonneg (hS0 y)]
  -- the row `a` integrated first
  have hBc : Continuous (moments_B (𝕜 := 𝕜) L z a b) :=
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
      ((moments_continuous_entry a k).mul (moments_continuous_greenT hz L k l)).mul
        (moments_continuous_entry l b)
  have hBmeas : Measurable fun w : Pair N → 𝕜 => ‖moments_B L z a b w‖ₑ ^ q :=
    hBc.measurable.enorm.pow_const q
  have hBint : ∫⁻ y, ‖moments_B L z a b (piMerge (rowsQ L) x y)‖ₑ ^ q ∂ν ≤
      ENNReal.ofReal (K ^ 2 * Real.sqrt W) ^ q := by
    have htower := congrFun (partialLInt_tower M.law (rowsQ L) (moments_rowsQ_mono hsub)
      hBmeas) x
    change partialLInt M.law (rowsQ L) (fun w => ‖moments_B L z a b w‖ₑ ^ q) x ≤ _
    rw [← htower]
    unfold partialLInt
    calc ∫⁻ y, ∫⁻ y', ‖moments_B L z a b (piMerge (rowsQ {a}) (piMerge (rowsQ L) x y) y')‖ₑ ^ q
          ∂(Measure.pi fun p : rowsQ ({a} : Finset (Fin N)) => M.law p) ∂ν
        ≤ ∫⁻ y, ENNReal.ofReal (K * Real.sqrt (S y)) ^ q ∂ν := by
          refine lintegral_mono fun y => ?_
          have h := moments_B_row M hM hϑ hϑ1 (z := z) ha hab hq (piMerge (rowsQ L) x y)
          unfold partialLInt at h
          refine h.trans (le_of_eq ?_)
          simp only [hS, hYid, hK]
      _ = ∫⁻ y, ENNReal.ofReal (K ^ 2) ^ (q / 2) * ENNReal.ofReal (S y) ^ (q / 2) ∂ν := by
          refine lintegral_congr fun y => ?_
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.ofReal_mul (by positivity),
            moments_ofReal_rpow_half (by have := hS0 y; positivity),
            Real.sqrt_mul' _ (hS0 y), Real.sqrt_sq hK0]
      _ = ENNReal.ofReal (K ^ 2) ^ (q / 2) * ∫⁻ y, ENNReal.ofReal (S y) ^ (q / 2) ∂ν :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofReal_ne_top)
      _ ≤ ENNReal.ofReal (K ^ 2) ^ (q / 2) * ENNReal.ofReal (K ^ 2 * W) ^ (q / 2) :=
          by gcongr
      _ = ENNReal.ofReal (K ^ 2 * Real.sqrt W) ^ q := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.ofReal_mul (by positivity),
            moments_ofReal_rpow_half (by positivity)]
          congr 2
          rw [← mul_assoc, Real.sqrt_mul' _ hW0, Real.sqrt_mul_self (by positivity)]
  have hB : eLpNorm (fun y => moments_B L z a b (piMerge (rowsQ L) x y)) (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal (K ^ 2 * Real.sqrt W) :=
    moments_eLpNorm_le (hBc.measurable.comp (moments_measurable_merge _ x)).aestronglyMeasurable
      hq0 hBint
  -- assembly: `M_ab = h_ab - B_ab`
  have hsch : ∀ w : Pair N → 𝕜, schurM (toMatrix w) L z ⟨a, ha⟩ ⟨b, hb⟩ =
      toC (toMatrix w a b) - moments_B L z a b w := fun w => by
    have hne : (⟨a, ha⟩ : L) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
    simp only [schurM, Matrix.of_apply, hne, ite_false, sub_zero, moments_B]
  have hf : (fun y : rowsQ L → 𝕜 =>
      schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨b, hb⟩) =
      (fun y => toC (moments_coord a b (y (moments_pk ha b)))) -
        (fun y => moments_B L z a b (piMerge (rowsQ L) x y)) := by
    funext y
    rw [hsch, moments_toMatrix_merge_off x y ha hba]
    rfl
  rw [hf]
  refine (eLpNorm_sub_le (by norm_num; linarith)).trans ?_
  have h1 : eLpNorm (fun y : rowsQ L → 𝕜 => toC (moments_coord a b (y (moments_pk ha b))))
      (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a b)) := by
    refine (eLpNorm_mono ((moments_continuous_toC.comp ((moments_continuous_coord a b).comp
      (continuous_apply _))).aestronglyMeasurable) fun y => ?_).trans
      (moments_eLpNorm_coord M hM hϑ hϑ1 L (moments_pk ha b) (by linarith))
    change ‖toC (moments_coord a b (y (moments_pk ha b)))‖ ≤ _
    rw [moments_norm_toC, moments_norm_coord]
  have hWb := moments_ward M hM hz L hN a b x
  have hsW : Real.sqrt W ≤ C₀ * Real.sqrt I := by
    calc _ ≤ Real.sqrt (C₀ ^ 2 * I) := Real.sqrt_le_sqrt hWb
      _ = C₀ * Real.sqrt I := by
          rw [Real.sqrt_mul' _ (moments_I_nonneg hz L x), Real.sqrt_sq hC0]
  have hK2 : K ^ 2 = cLD ϑ⁻¹ ^ 2 * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) := by
    rw [hK, mul_pow, ← Real.rpow_natCast ((q + Real.log N) ^ (ϑ⁻¹ + 1 / 2)),
      ← Real.rpow_mul (by linarith)]
    congr 2
    push_cast
    ring
  have hT := moments_theta_le (ℓ := Real.log N) (e := 2 * ϑ⁻¹ + 1) ha1
    (by linarith : (1 : ℝ) ≤ q) hlog (by linarith)
  have hvar : Real.sqrt (M.var a b) ≤ Real.sqrt (C₀ / N) := Real.sqrt_le_sqrt (hM.boundC a b)
  have hP : 0 ≤ (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) := Real.rpow_nonneg (by linarith) _
  have hlhs1 : 0 ≤ (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a b) :=
    mul_nonneg (Real.rpow_nonneg (by unfold cTheta; positivity) _) (Real.sqrt_nonneg _)
  have hlhs2 : 0 ≤ K ^ 2 * Real.sqrt W := by positivity
  calc _ ≤ ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a b)) +
        ENNReal.ofReal (K ^ 2 * Real.sqrt W) := add_le_add h1 hB
    _ = ENNReal.ofReal ((cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a b) +
        K ^ 2 * Real.sqrt W) := (ENNReal.ofReal_add hlhs1 hlhs2).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hcm1 := moments_cTheta_le_faCm ϑ⁻¹
        have hcm2 := moments_cLD_sq_le_faCm ϑ⁻¹
        have hct : 0 ≤ cTheta ϑ⁻¹ ^ ϑ⁻¹ := Real.rpow_nonneg (by unfold cTheta; positivity) _
        have hsq : 0 ≤ Real.sqrt (C₀ / N) := Real.sqrt_nonneg _
        have hsI : 0 ≤ Real.sqrt I := Real.sqrt_nonneg _
        have hfa := mul_nonneg (moments_faCm_nonneg ha1) hP
        unfold phiL
        rw [← hI, hK2]
        calc (cTheta ϑ⁻¹ * q) ^ ϑ⁻¹ * Real.sqrt (M.var a b) +
              cLD ϑ⁻¹ ^ 2 * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * Real.sqrt W
            ≤ cTheta ϑ⁻¹ ^ ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * Real.sqrt (C₀ / N) +
              faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * (C₀ * Real.sqrt I) := by
              gcongr
          _ ≤ faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * Real.sqrt (C₀ / N) +
              faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * (C₀ * Real.sqrt I) := by gcongr
          _ = _ := by ring

end M1

/-! ### 9. Lemma 6.5 -/

/-- A bound on `‖f‖_{q,T}(x)` from an `L^q` bound of the slice of `f` at `x` (Lemma 6.3 (F4)). -/
private lemma moments_rowNorm_le {N : ℕ} (M : Ensemble 𝕜 N) {T : Finset (Fin N)}
    {f : (Pair N → 𝕜) → ℂ} (hf : Measurable f) {q R : ℝ} (hq : 1 ≤ q) (hR : 0 ≤ R)
    (x : Pair N → 𝕜)
    (h : eLpNorm (fun y => f (piMerge (rowsQ T) x y)) (ENNReal.ofReal q)
      (Measure.pi fun p : rowsQ T => M.law p) ≤ ENNReal.ofReal R) :
    rowNorm M T q f x ≤ R := by
  rw [(rowInt_freeze M T hf x).2.2.2 q hq]
  exact ENNReal.toReal_le_of_le_ofReal hR h

/-- Lemma 6.5 (m1): conditional moments of the off-diagonal entries of `M^L`. -/
theorem rowNorm_schurM_offdiag_le {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {z : ℂ} (hz : 0 < z.im)
    {L : Finset (Fin N)} (hLN : L.card < N) {a b : Fin N} (ha : a ∈ L) (hb : b ∈ L)
    (hab : a ≠ b) {q : ℝ} (hq : 2 ≤ q) (x : Pair N → 𝕜) :
    rowNorm M L q (fun w => schurM (toMatrix w) L z ⟨a, ha⟩ ⟨b, hb⟩) x ≤
      faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * phiL C₀ L z x := by
  have _ := hLN
  have hN : 0 < N := Fin.pos_iff_nonempty.2 ⟨a⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hR : 0 ≤ faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) * phiL C₀ L z x :=
    mul_nonneg (mul_nonneg (moments_faCm_nonneg ha1)
      (Real.rpow_nonneg (by linarith [Real.log_nonneg hNr]) _))
      (moments_phiL_nonneg (moments_C₀_nonneg M hM hN) L x)
  exact moments_rowNorm_le M ((polyGrowth_schurM M C₀ hz L).1 a b ha hb).1.measurable
    (by linarith) hR x (moments_m1 M hM hϑ hϑ1 hz ha hb hab hq x)

/-- Lemma 6.5 (m2): conditional moments of `Q_a M_aa`. -/
theorem rowNorm_Q_schurM_diag_le {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {z : ℂ} (hz : 0 < z.im)
    {L : Finset (Fin N)} (hLN : L.card < N) {a : Fin N} (ha : a ∈ L) {q : ℝ} (hq : 2 ≤ q)
    (x : Pair N → 𝕜) :
    rowNorm M L q (fun w => schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩ -
        rowInt M {a} (fun w' => schurM (toMatrix w') L z ⟨a, ha⟩ ⟨a, ha⟩) w) x ≤
      faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 3 / 2) * phiL C₀ L z x := by
  have _ := hLN
  have hN : 0 < N := Fin.pos_iff_nonempty.2 ⟨a⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hR : 0 ≤ faCm ϑ⁻¹ * (q + Real.log N) ^ (2 * ϑ⁻¹ + 3 / 2) * phiL C₀ L z x :=
    mul_nonneg (mul_nonneg (moments_faCm_nonneg ha1)
      (Real.rpow_nonneg (by linarith [Real.log_nonneg hNr]) _))
      (moments_phiL_nonneg (moments_C₀_nonneg M hM hN) L x)
  have hS := polyGrowth_schurM M C₀ hz L
  have hm : Measurable (fun w => schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩ -
      rowInt M {a} (fun w' => schurM (toMatrix w') L z ⟨a, ha⟩ ⟨a, ha⟩) w) :=
    (hS.1 a a ha ha).1.measurable.sub
      (rowInt_polyGrowth M hM hϑ {a} (hS.1 a a ha ha).2).1
  exact moments_rowNorm_le M hm (by linarith) hR x (moments_m2 M hM hϑ hϑ1 hz ha hq x)

/-- `5^q + 1 ≤ 6^q` for `q ≥ 1`. -/
private lemma moments_five_add_one {q : ℝ} (hq : 1 ≤ q) : (5 : ℝ) ^ q + 1 ≤ 6 ^ q := by
  have h6 : (6 : ℝ) ^ q = 6 ^ (q - 1) * 6 := by
    rw [← Real.rpow_add_one (by norm_num : (6 : ℝ) ≠ 0)]; ring_nf
  have h5 : (5 : ℝ) ^ q = 5 ^ (q - 1) * 5 := by
    rw [← Real.rpow_add_one (by norm_num : (5 : ℝ) ≠ 0)]; ring_nf
  have h56 : (5 : ℝ) ^ (q - 1) ≤ 6 ^ (q - 1) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have h1 : (1 : ℝ) ≤ 6 ^ (q - 1) := Real.one_le_rpow (by norm_num) (by linarith)
  rw [h6, h5]
  nlinarith

/-- Lemma 6.5 (m3): conditional moments of `1/M_aa` at a point where (6.10) holds. -/
theorem rowNorm_inv_schurM_diag_le {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {z : ℂ} (hη : 1 / N ≤ z.im)
    {L : Finset (Fin N)} (hLN : L.card < N) {a : Fin N} (ha : a ∈ L) {qs : ℝ} (hqs : 2 ≤ qs)
    (x : Pair N → 𝕜) (h1 : 2 / 5 ≤ ‖z + mL M L z a x‖)
    (h2 : 5 * Real.exp 1 * faCm ϑ⁻¹ * ((qs + 1) * ⌈Real.log N⌉₊) ^ (2 * ϑ⁻¹ + 3 / 2) *
      phiL C₀ L z x ≤ 1) {q : ℝ} (hq1 : 1 ≤ q) (hq : q ≤ qs) :
    rowNorm M L q (fun w => 1 / schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩) x ≤ 6 := by
  have hL1 : 1 ≤ L.card := Finset.card_pos.2 ⟨a, ha⟩
  have hN2 : 2 ≤ N := by omega
  have hN : 0 < N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have ha1 : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hq0 : 0 < q := by linarith
  have hC0 := moments_C₀_nonneg M hM hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set c : ℕ := ⌈Real.log N⌉₊ with hc
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.one_le_ceil_iff.2 hlog
  have hcl : Real.log N ≤ c := Nat.le_ceil _
  set e := 2 * ϑ⁻¹ + 3 / 2 with he
  set q' := qs * c with hq'
  have hq'2 : 2 ≤ q' := by rw [hq']; nlinarith
  have hq'le : q' + Real.log N ≤ (qs + 1) * c := by rw [hq']; nlinarith
  set ν := Measure.pi fun p : rowsQ L => M.law p with hν
  set g : (rowsQ L → 𝕜) → ℂ := fun y =>
    schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩ -
      rowInt M {a} (fun w' => schurM (toMatrix w') L z ⟨a, ha⟩ ⟨a, ha⟩)
        (piMerge (rowsQ L) x y) with hg
  set R := faCm ϑ⁻¹ * (q' + Real.log N) ^ e * phiL C₀ L z x with hR
  have hm2 : eLpNorm g (ENNReal.ofReal q') ν ≤ ENNReal.ofReal R :=
    moments_m2 M hM hϑ hϑ1 hz ha hq'2 x
  have hΦ := moments_phiL_nonneg hC0 (z := z) L x
  have hfa := moments_faCm_nonneg ha1
  have hR0 : 0 ≤ R := mul_nonneg (mul_nonneg hfa (Real.rpow_nonneg (by linarith) _)) hΦ
  have h5R : 5 * R ≤ Real.exp (-1) := by
    have hpow : (q' + Real.log N) ^ e ≤ ((qs + 1) * c) ^ e :=
      Real.rpow_le_rpow (by linarith) hq'le (by rw [he]; positivity)
    have hE : 0 < Real.exp 1 := Real.exp_pos 1
    rw [Real.exp_neg, ← one_div, le_div_iff₀ hE, hR]
    have h2' : 5 * Real.exp 1 * faCm ϑ⁻¹ * ((qs + 1) * c) ^ e * phiL C₀ L z x ≤ 1 := h2
    calc 5 * (faCm ϑ⁻¹ * (q' + Real.log N) ^ e * phiL C₀ L z x) * Real.exp 1
        ≤ 5 * (faCm ϑ⁻¹ * ((qs + 1) * c) ^ e * phiL C₀ L z x) * Real.exp 1 := by gcongr
      _ ≤ 1 := by linarith
  -- Markov's inequality at the order `q'`
  set Ebad : Set (rowsQ L → 𝕜) := {y | ENNReal.ofReal (1 / 5) ≤ ‖g y‖ₑ} with hEbad
  have hq'0 : 0 < q' := by linarith
  have hMarkov : ν Ebad ≤ ENNReal.ofReal ((N : ℝ) ^ (-qs)) := by
    have h := meas_ge_le_mul_pow_eLpNorm_enorm ν (p := ENNReal.ofReal q') (f := g)
      (by simpa using hq'0) ENNReal.ofReal_ne_top (ε := ENNReal.ofReal (1 / 5))
      (by simp) (fun h => absurd h ENNReal.ofReal_ne_top)
    rw [ENNReal.toReal_ofReal hq'0.le, ← ENNReal.ofReal_inv_of_pos (by norm_num)] at h
    refine h.trans ?_
    calc ENNReal.ofReal (1 / 5)⁻¹ ^ q' * eLpNorm g (ENNReal.ofReal q') ν ^ q'
        ≤ ENNReal.ofReal (1 / 5)⁻¹ ^ q' * ENNReal.ofReal R ^ q' := by
          gcongr
      _ = ENNReal.ofReal (5 * R) ^ q' := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq'0.le, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ ENNReal.ofReal (Real.exp (-1)) ^ q' := by
          gcongr
      _ = ENNReal.ofReal (Real.exp (-q')) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq'0.le, ← Real.exp_mul]
          ring_nf
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-qs)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.rpow_def_of_pos hNpos]
          refine Real.exp_le_exp.2 ?_
          rw [hq']
          nlinarith
  -- the pointwise bound
  have hrow : ∀ y : rowsQ L → 𝕜,
      rowInt M {a} (fun w' => schurM (toMatrix w') L z ⟨a, ha⟩ ⟨a, ha⟩)
        (piMerge (rowsQ L) x y) = -z - mL M L z a x := fun y => by
    rw [(rowInt_schurM_diag M hM hϑ hz L ha (piMerge (rowsQ L) x y)).1,
      (noDep_greenT M C₀ L z).2.2.1 a _ x fun p hp => by simp [piMerge, hp]]
  have hηN : 1 / z.im ≤ N := (one_div_le hz hNpos).2 hη
  have hpt : ∀ y, ‖1 / schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩‖ₑ ^ q ≤
      ENNReal.ofReal (5 ^ q) + Ebad.indicator (fun _ => ENNReal.ofReal ((N : ℝ) ^ q)) y := by
    intro y
    set F := schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩ with hF
    have hFg : F = -(z + mL M L z a x) + g y := by
      rw [hg]; simp only; rw [hrow y, ← hF]; ring
    have hall : ‖1 / F‖ ≤ N :=
      ((schurM_inv hz L (piMerge (rowsQ L) x y)).2.1 a ha).2.2.trans hηN
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
    by_cases hy : y ∈ Ebad
    · rw [Set.indicator_of_mem hy]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      exact Real.rpow_le_rpow (norm_nonneg _) hall hq0.le
    · rw [Set.indicator_of_notMem hy, add_zero]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) ?_ hq0.le)
      have hgy : ‖g y‖ < 1 / 5 := by
        simp only [hEbad, Set.mem_ofPred_eq, not_le] at hy
        rw [← ofReal_norm] at hy
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).1 hy
      have hF5 : 1 / 5 ≤ ‖F‖ := by
        have : ‖z + mL M L z a x‖ ≤ ‖F‖ + ‖g y‖ := by
          have e : z + mL M L z a x = -F + g y := by rw [hFg]; ring
          rw [e]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
        linarith
      rw [norm_div, norm_one]
      rw [div_le_iff₀ (by linarith)]
      linarith
  have hint : ∫⁻ y, ‖1 / schurM (toMatrix (piMerge (rowsQ L) x y)) L z ⟨a, ha⟩ ⟨a, ha⟩‖ₑ ^ q ∂ν ≤
      ENNReal.ofReal (6 ^ q) := by
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (5 ^ q) +
          Ebad.indicator (fun _ => ENNReal.ofReal ((N : ℝ) ^ q)) y) ∂ν := lintegral_mono hpt
      _ = ENNReal.ofReal (5 ^ q) +
          ∫⁻ y, Ebad.indicator (fun _ => ENNReal.ofReal ((N : ℝ) ^ q)) y ∂ν := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (5 ^ q) + ENNReal.ofReal ((N : ℝ) ^ q) * ν Ebad := by
          gcongr
          exact lintegral_indicator_const_le _ _
      _ ≤ ENNReal.ofReal (5 ^ q) + ENNReal.ofReal ((N : ℝ) ^ q) *
          ENNReal.ofReal ((N : ℝ) ^ (-qs)) := by gcongr
      _ = ENNReal.ofReal (5 ^ q + (N : ℝ) ^ (q - qs)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hNpos,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
      _ ≤ ENNReal.ofReal (6 ^ q) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : (N : ℝ) ^ (q - qs) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
          linarith [moments_five_add_one hq1]
  have h6 : (partialLInt M.law (rowsQ L)
      (fun w => ‖1 / schurM (toMatrix w) L z ⟨a, ha⟩ ⟨a, ha⟩‖ₑ ^ q) x).toReal ≤ 6 ^ q :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hint
  unfold rowNorm
  calc _ ≤ ((6 : ℝ) ^ q) ^ (1 / q) := Real.rpow_le_rpow ENNReal.toReal_nonneg h6 (by positivity)
    _ = 6 := by rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hq0.ne', Real.rpow_one]

end Rigidity
