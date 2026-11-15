import Rigidity.Ensemble.Basic
import Rigidity.Flow.Gaussian
import Rigidity.Flow.Herm

/-!
# The Gaussian ensemble on the space of hermitian matrices

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

With `σ² = 2/(βN)` (`gaussVar`), `𝐆 = gaussH 𝕜 N` is the centred Gaussian measure on `𝓗 = Herm 𝕜 N`
with covariance `σ² Id` (§12.1, Lemma 14.C), `gbeLaw` is the law `λ_* 𝐆` of its eigenvalue vector,
`gbeEntryLaw` are the entry laws of Lemma 14.C (ii), `gbeEnsemble` is the Gaussian ensemble (GOE for
`𝕜 = ℝ`, GUE for `𝕜 = ℂ`) as an ensemble, and `Ensemble.hermLaw` is the law of `H(x)` on `𝓗`.
The file proves:
* Lemma 14.C (i): the density of `𝐆` with respect to the Lebesgue measure of `𝓗`;
* Lemma 14.C (ii): an ensemble with the entry laws `gbeEntryLaw` has law `𝐆` on `𝓗`;
* Lemma 14.C (iii): `𝐆` is invariant under `H ↦ U H U*` for `U ∈ U_β(N)`;
* Lemma 14.C (iv): `∫ |H|² d𝐆 = d σ² ≤ N + 1`, with `d = dim_ℝ 𝓗`;
* Lemma 13.B (b): the Gaussian tail bound for the entries of `V ∼ 𝐆`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `σ² = 2/(βN)` (§12.1). -/
noncomputable def gaussVar (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : ℝ := 2 / (betaF 𝕜 * N)

/-- `𝐆 = 𝐆_{N,β}`, the centred Gaussian measure on `𝓗` with covariance `σ² Id` (§12.1). -/
noncomputable def gaussH (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Measure (Herm 𝕜 N) :=
  gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)

/-- `μ = λ_* 𝐆` (§12.1). -/
noncomputable def gbeLaw (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Measure (Fin N → ℝ) :=
  (gaussH 𝕜 N).map eigVec

/-- The entry laws of `V ∼ 𝐆` (Lemma 14.C(ii)): `v_ii ∼ N(0, 2/(βN))` real, and for `i < j`,
`v_ij = ξ + η I` with `ξ, η ∼ N(0, 1/(βN))` independent (`η` is void for `𝕜 = ℝ`). -/
noncomputable def gbeEntryLaw (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (p : Pair N) : Measure 𝕜 :=
  if p.1.1 = p.1.2 then
    (ProbabilityTheory.gaussianReal 0 (2 / (betaF 𝕜 * N)).toNNReal).map fun a : ℝ => (a : 𝕜)
  else
    ((ProbabilityTheory.gaussianReal 0 (1 / (betaF 𝕜 * N)).toNNReal).prod
      (ProbabilityTheory.gaussianReal 0 (1 / (betaF 𝕜 * N)).toNNReal)).map
        fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I

/-- The Gaussian ensemble (GOE for `𝕜 = ℝ`, GUE for `𝕜 = ℂ`) as an ensemble (Lemma 14.C(iv)). -/
noncomputable def gbeEnsemble (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Ensemble 𝕜 N where
  law := gbeEntryLaw 𝕜 N
  isProb p := by
    unfold gbeEntryLaw
    split_ifs
    all_goals infer_instance

namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- The law of `H_0 = H(x)`, `x ∼ ℙ_ν`, on `𝓗`. -/
noncomputable def hermLaw : Measure (Herm 𝕜 N) := M.prodLaw.map Herm.ofPair

end Ensemble

/-! ### 1. Elementary facts -/

section Elementary

variable {N : ℕ}

private lemma betaF_pos' : 0 < betaF 𝕜 := by
  unfold betaF
  exact_mod_cast Module.finrank_pos

private lemma inv_var_nonneg (N : ℕ) : 0 ≤ 1 / (betaF 𝕜 * N) := by
  have := (betaF_pos' (𝕜 := 𝕜)).le
  positivity

private lemma gaussVar_nonneg (N : ℕ) : 0 ≤ gaussVar 𝕜 N := by
  have := (betaF_pos' (𝕜 := 𝕜)).le
  unfold gaussVar
  positivity

private lemma coe_var_diag (N : ℕ) :
    (((2 / (betaF 𝕜 * N)).toNNReal : NNReal) : ℝ) = gaussVar 𝕜 N := by
  have h : 0 ≤ 2 / (betaF 𝕜 * N) := gaussVar_nonneg N
  rw [Real.coe_toNNReal _ h]
  rfl

private lemma coe_var_off (N : ℕ) :
    (((1 / (betaF 𝕜 * N)).toNNReal : NNReal) : ℝ) = 1 / (betaF 𝕜 * N) :=
  Real.coe_toNNReal _ (inv_var_nonneg N)

private lemma gaussVar_eq_two_mul (N : ℕ) : gaussVar 𝕜 N = 2 * (1 / (betaF 𝕜 * N)) := by
  unfold gaussVar
  ring

/-- `(Im I)² Im(w)² = Im(w)²`: either `I = 0` and every imaginary part vanishes, or `Im I = 1`. -/
private lemma im_I_sq_mul (w : 𝕜) :
    RCLike.im (RCLike.I : 𝕜) ^ 2 * RCLike.im w ^ 2 = RCLike.im w ^ 2 := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · simp [RCLike.im_eq_zero h]
  · simp [h]

/-- `|a + b I|² = a² + (Im I)² b²` for real `a, b`. -/
private lemma norm_sq_ofReal_add_mul_I (a b : ℝ) :
    ‖(a : 𝕜) + (b : 𝕜) * RCLike.I‖ ^ 2 = a ^ 2 + RCLike.im (RCLike.I : 𝕜) ^ 2 * b ^ 2 := by
  rw [RCLike.norm_sq_eq_def]
  simp
  ring

private lemma mk'_of_le' {i j : Fin N} (h : i ≤ j) : Pair.mk' i j = ⟨(i, j), h⟩ := by
  simp [Pair.mk', h]

private lemma mk'_of_gt' {i j : Fin N} (h : j < i) : Pair.mk' i j = ⟨(j, i), h.le⟩ := by
  simp [Pair.mk', not_le.mpr h]

/-- A double sum over `Fin N × Fin N` as a sum over the pairs `i ≤ j`. -/
private lemma sum_sum_eq_sum_pair (g : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, g i j = ∑ p : Pair N,
      (g p.1.1 p.1.2 + if p.1.1 = p.1.2 then 0 else g p.1.2 p.1.1) := by
  rw [Finset.sum_add_distrib]
  have hS : ∀ F : Fin N × Fin N → ℝ, ∑ p : Pair N, F p.1 =
      ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => q.1 ≤ q.2), F q := fun F =>
    (Finset.sum_subtype _ (fun q => by simp) F).symm
  rw [hS (fun q => g q.1 q.2), hS (fun q => if q.1 = q.2 then 0 else g q.2 q.1),
    Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]
  have h2 : ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => q.1 ≤ q.2 ∧ ¬ q.1 = q.2),
      g q.2 q.1 = ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => ¬ q.1 ≤ q.2), g q.1 q.2 := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact not_le.mpr (lt_of_le_of_ne hq.1 hq.2)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨(not_le.mp hq).le, (not_le.mp hq).ne⟩
    · intro q _
      rfl
    · intro q _
      rfl
    · intro q _
      rfl
  rw [h2, Finset.sum_filter_add_sum_filter_not, Fintype.sum_prod_type]

end Elementary

/-! ### 2. Matrices of conjugates -/

section Conj

variable {N : ℕ}

end Conj

/-! ### 3. Characteristic functions -/

section CharFun

variable {N : ℕ}

/-- The characteristic function of `g_v` on `𝓗` is `T ↦ exp (-v |T|² / 2)`, for `v ≥ 0`. -/
private lemma charFun_gaussE_herm {v : ℝ} (hv : 0 ≤ v) (T : Herm 𝕜 N) :
    charFun (gaussE (Herm 𝕜 N) v) T = Complex.exp (-((v * ‖T‖ ^ 2 / 2 : ℝ) : ℂ)) := by
  unfold gaussE
  rw [charFun_map_smul, ProbabilityTheory.charFun_stdGaussian]
  congr 1
  have h0 : ‖Real.sqrt v • T‖ ^ 2 = v * ‖T‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hv]
  have h : ((‖Real.sqrt v • T‖ : ℝ) : ℂ) ^ 2 = (v : ℂ) * (‖T‖ : ℂ) ^ 2 := by
    exact_mod_cast h0
  rw [h]
  push_cast
  ring

/-- The contribution of the entry `x_p` to `⟨H(x), T⟩`. -/
private noncomputable def linCoord (T : Herm 𝕜 N) (p : Pair N) (z : 𝕜) : ℝ :=
  if p.1.1 = p.1.2 then RCLike.re (((RCLike.re z : ℝ) : 𝕜) * T.toMatrix p.1.1 p.1.2)
  else RCLike.re (z * T.toMatrix p.1.2 p.1.1) + RCLike.re (star z * T.toMatrix p.1.1 p.1.2)

/-- `⟨H(x), T⟩ = ∑_{p} ℓ_p(x_p)`. -/
private lemma inner_ofPair_eq_sum (x : Pair N → 𝕜) (T : Herm 𝕜 N) :
    inner ℝ (Herm.ofPair x) T = ∑ p : Pair N, linCoord T p (x p) := by
  rw [Herm.inner_eq_trace, Herm.toMatrix_ofPair]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  rw [sum_sum_eq_sum_pair (fun i j => RCLike.re (Rigidity.toMatrix x i j * T.toMatrix j i))]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only at hij ⊢
  rcases hij.lt_or_eq with h | rfl
  · have e1 : Pair.mk' i j = ⟨(i, j), hij⟩ := mk'_of_le' hij
    have e2 : Pair.mk' j i = ⟨(i, j), hij⟩ := mk'_of_gt' h
    simp [linCoord, Rigidity.toMatrix, h, h.ne, not_lt.mpr h.le, e1, e2]
  · have e : Pair.mk' i i = ⟨(i, i), hij⟩ := mk'_of_le' hij
    simp [linCoord, Rigidity.toMatrix, e]

/-- `|T|² = ∑_{p} w_p` with `w_ii = |t_ii|²`, `w_ij = |t_ij|² + |t_ji|²`. -/
private lemma norm_sq_eq_sum_pair (T : Herm 𝕜 N) :
    ‖T‖ ^ 2 = ∑ p : Pair N, (‖T.toMatrix p.1.1 p.1.2‖ ^ 2 +
      if p.1.1 = p.1.2 then 0 else ‖T.toMatrix p.1.2 p.1.1‖ ^ 2) := by
  rw [Herm.norm_sq_eq, sum_sum_eq_sum_pair (fun i j => ‖T.toMatrix i j‖ ^ 2)]

/-- The characteristic function of one entry law at the linear form `ℓ_p`. -/
private lemma integral_linCoord (T : Herm 𝕜 N) (p : Pair N) :
    ∫ z, Complex.exp ((linCoord T p z : ℂ) * Complex.I) ∂gbeEntryLaw 𝕜 N p =
      Complex.exp (-((gaussVar 𝕜 N / 2 * (‖T.toMatrix p.1.1 p.1.2‖ ^ 2 +
        if p.1.1 = p.1.2 then 0 else ‖T.toMatrix p.1.2 p.1.1‖ ^ 2) : ℝ) : ℂ)) := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only
  by_cases h : i = j
  · subst h
    simp only [gbeEntryLaw, linCoord, ite_true]
    rw [integral_map (RCLike.continuous_ofReal.measurable.aemeasurable)
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have e : ∀ a : ℝ, ((RCLike.re (((RCLike.re (a : 𝕜) : ℝ) : 𝕜) * T.toMatrix i i) : ℝ) : ℂ) *
        Complex.I = (RCLike.re (T.toMatrix i i) : ℂ) * (a : ℂ) * Complex.I := by
      intro a
      simp only [RCLike.ofReal_re, RCLike.re_ofReal_mul]
      push_cast
      ring
    simp_rw [e]
    rw [← charFun_apply_real, ProbabilityTheory.charFun_gaussianReal, coe_var_diag]
    have hre : ‖T.toMatrix i i‖ = |RCLike.re (T.toMatrix i i)| := by
      rw [← T.isHermitian.coe_re_apply_self i, RCLike.norm_ofReal, RCLike.ofReal_re]
    rw [hre, sq_abs, add_zero]
    congr 1
    push_cast
    ring
  · simp only [gbeEntryLaw, linCoord, h, ite_false]
    have hm : Measurable fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I := by fun_prop
    rw [integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    set w := T.toMatrix i j with hw
    have hji : T.toMatrix j i = star w := (T.isHermitian.apply j i).symm
    set c1 : ℝ := 2 * RCLike.re w
    set c2 : ℝ := 2 * (RCLike.im (RCLike.I : 𝕜) * RCLike.im w)
    have e : ∀ ab : ℝ × ℝ, Complex.exp (((RCLike.re (((ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I) *
        T.toMatrix j i) + RCLike.re (star ((ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I) * w) : ℝ) : ℂ) *
        Complex.I) = Complex.exp ((c1 : ℂ) * (ab.1 : ℂ) * Complex.I) *
          Complex.exp ((c2 : ℂ) * (ab.2 : ℂ) * Complex.I) := by
      intro ab
      rw [← Complex.exp_add, hji]
      congr 1
      simp only [c1, c2, RCLike.mul_re, map_add, map_neg, RCLike.ofReal_re,
        RCLike.ofReal_im, RCLike.mul_im, RCLike.I_re, RCLike.star_def, RCLike.conj_re,
        RCLike.conj_im, map_add, map_mul, RCLike.conj_ofReal, RCLike.conj_I]
      push_cast
      ring
    simp_rw [e]
    rw [integral_prod_mul (fun a : ℝ => Complex.exp ((c1 : ℂ) * (a : ℂ) * Complex.I))
      (fun b : ℝ => Complex.exp ((c2 : ℂ) * (b : ℂ) * Complex.I)), ← charFun_apply_real,
      ← charFun_apply_real, ProbabilityTheory.charFun_gaussianReal,
      ProbabilityTheory.charFun_gaussianReal, ← Complex.exp_add, coe_var_off, hji, norm_star]
    congr 1
    have hn : ‖w‖ ^ 2 = RCLike.re w ^ 2 + RCLike.im (RCLike.I : 𝕜) ^ 2 * RCLike.im w ^ 2 := by
      rw [im_I_sq_mul, RCLike.norm_sq_eq_def]
      ring
    rw [gaussVar_eq_two_mul, hn]
    simp only [c1, c2]
    push_cast
    ring

end CharFun

/-! ### 4. Entry variances -/

section Variance

/-- `∫ a² d N(0, v) = v`. -/
private lemma integral_sq_gaussianReal (v : NNReal) :
    ∫ a, a ^ 2 ∂ProbabilityTheory.gaussianReal 0 v = v := by
  have h := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := v)
  rw [ProbabilityTheory.variance_of_integral_eq_zero measurable_id.aemeasurable
    (by simp)] at h
  simpa using h

private lemma integrable_sq_gaussianReal (v : NNReal) :
    Integrable (fun a : ℝ => a ^ 2) (ProbabilityTheory.gaussianReal 0 v) := by
  simpa using (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

/-- Lemma 14.C (ii), (iv): `σ_ii² = 2/(βN)`, and `σ_ij² = (1 + (Im I)²)/(βN)` for `i < j`
(that is, `1/N` in both cases `β = 1, 2`). -/
private lemma varPair_gbeEnsemble (N : ℕ) (p : Pair N) :
    (gbeEnsemble 𝕜 N).varPair p = if p.1.1 = p.1.2 then gaussVar 𝕜 N
      else (1 + RCLike.im (RCLike.I : 𝕜) ^ 2) * (1 / (betaF 𝕜 * N)) := by
  unfold Ensemble.varPair
  change ∫ z, ‖z‖ ^ 2 ∂gbeEntryLaw 𝕜 N p = _
  unfold gbeEntryLaw
  split_ifs with h
  · rw [integral_map RCLike.continuous_ofReal.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [RCLike.norm_ofReal, sq_abs]
    rw [integral_sq_gaussianReal, coe_var_diag]
  · have hm : Measurable fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I := by fun_prop
    rw [integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp_rw [norm_sq_ofReal_add_mul_I]
    have hi := integrable_sq_gaussianReal (1 / (betaF 𝕜 * N)).toNNReal
    rw [integral_add (hi.comp_fst _) ((hi.comp_snd _).const_mul _), integral_const_mul,
      integral_fun_fst (fun a : ℝ => a ^ 2), integral_fun_snd (fun a : ℝ => a ^ 2),
      integral_sq_gaussianReal, coe_var_off]
    simp
    ring

end Variance

/-! ### 4. Lemma 14.C -/

/-- Lemma 14.C(ii): the Gaussian ensemble has law `𝐆` on `𝓗`. -/
theorem gbeEnsemble_hermLaw (N : ℕ) : (gbeEnsemble 𝕜 N).hermLaw = gaussH 𝕜 N := by
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  have hm := Herm.measurable_ofPair (𝕜 := 𝕜) N
  have : IsProbabilityMeasure (gbeEnsemble 𝕜 N).hermLaw := by
    unfold Ensemble.hermLaw
    exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  apply Measure.ext_of_charFun
  ext T
  rw [gaussH, charFun_gaussE_herm (gaussVar_nonneg N) T, charFun_apply, Ensemble.hermLaw,
    integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  have e : ∀ x : Pair N → 𝕜, Complex.exp ((inner ℝ (Herm.ofPair x) T : ℝ) * Complex.I) =
      ∏ p, Complex.exp ((linCoord T p (x p) : ℂ) * Complex.I) := by
    intro x
    rw [inner_ofPair_eq_sum, ← Complex.exp_sum]
    push_cast
    rw [Finset.sum_mul]
  simp_rw [e]
  rw [Ensemble.prodLaw, integral_fintype_prod_eq_prod (E := fun _ : Pair N => 𝕜)
    (fun p z => Complex.exp ((linCoord T p z : ℂ) * Complex.I))]
  change ∏ p, ∫ z, Complex.exp ((linCoord T p z : ℂ) * Complex.I) ∂gbeEntryLaw 𝕜 N p = _
  simp_rw [integral_linCoord]
  rw [← Complex.exp_sum, norm_sq_eq_sum_pair]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- Lemma 13.B(b): entry tails of `V ∼ 𝐆`. -/
theorem gbeEntryLaw_tail {N : ℕ} (p : Pair N) {y : ℝ} (hy : 0 ≤ y) :
    gbeEntryLaw 𝕜 N p {z | y * Real.sqrt ((gbeEnsemble 𝕜 N).varPair p) < ‖z‖} ≤
      ENNReal.ofReal (4 * Real.exp (-y ^ 2 / 2)) := by
  have hE := Real.exp_nonneg (-y ^ 2 / 2)
  rw [varPair_gbeEnsemble]
  unfold gbeEntryLaw
  by_cases h : p.1.1 = p.1.2
  · simp only [h, ite_true]
    have hms : MeasurableSet {z : 𝕜 | y * Real.sqrt (gaussVar 𝕜 N) < ‖z‖} :=
      measurableSet_lt measurable_const measurable_norm
    rw [Measure.map_apply RCLike.continuous_ofReal.measurable hms]
    have hset : (fun a : ℝ => (a : 𝕜)) ⁻¹' {z | y * Real.sqrt (gaussVar 𝕜 N) < ‖z‖} =
        {a : ℝ | y * Real.sqrt ((2 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} := by
      ext a
      rw [coe_var_diag]
      simp
    rw [hset]
    refine (gaussianReal_tail _ hy).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith
  · simp only [h, ite_false]
    have hc0 : 0 ≤ RCLike.im (RCLike.I : 𝕜) ^ 2 := sq_nonneg _
    have hv0 := inv_var_nonneg (𝕜 := 𝕜) N
    have hms : MeasurableSet {z : 𝕜 | y * Real.sqrt ((1 + RCLike.im (RCLike.I : 𝕜) ^ 2) *
        (1 / (betaF 𝕜 * N))) < ‖z‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hm : Measurable fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I := by fun_prop
    rw [Measure.map_apply hm hms]
    set g := ProbabilityTheory.gaussianReal 0 (1 / (betaF 𝕜 * N)).toNNReal with hg
    have hsub : (fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I) ⁻¹'
        {z : 𝕜 | y * Real.sqrt ((1 + RCLike.im (RCLike.I : 𝕜) ^ 2) * (1 / (betaF 𝕜 * N))) < ‖z‖} ⊆
        {a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} ×ˢ Set.univ ∪
          Set.univ ×ˢ {a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} := by
      rintro ⟨a, b⟩ hab
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hab
      by_contra hn
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, not_or,
        Set.mem_ofPred_eq, not_lt, coe_var_off] at hn
      have h1 := pow_lt_pow_left₀ hab (by positivity) two_ne_zero
      rw [norm_sq_ofReal_add_mul_I, mul_pow, Real.sq_sqrt (by positivity)] at h1
      have ha := pow_le_pow_left₀ (abs_nonneg a) hn.1 2
      have hb := pow_le_pow_left₀ (abs_nonneg b) hn.2 2
      rw [sq_abs, mul_pow, Real.sq_sqrt hv0] at ha hb
      nlinarith [mul_le_mul_of_nonneg_left hb hc0]
    calc _ ≤ (g.prod g) ({a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} ×ˢ
          Set.univ ∪
            Set.univ ×ˢ {a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|}) :=
          measure_mono hsub
      _ ≤ (g.prod g) ({a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} ×ˢ
          Set.univ) + (g.prod g) (Set.univ ×ˢ
            {a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|}) :=
          measure_union_le _ _
      _ = g {a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} +
          g {a : ℝ | y * Real.sqrt ((1 / (betaF 𝕜 * N)).toNNReal : ℝ) < |a|} := by
          rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-y ^ 2 / 2)) + ENNReal.ofReal (2 * Real.exp (-y ^ 2 / 2)) :=
          add_le_add (gaussianReal_tail _ hy) (gaussianReal_tail _ hy)
      _ = ENNReal.ofReal (4 * Real.exp (-y ^ 2 / 2)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end Rigidity
