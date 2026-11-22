module

public import Rigidity.Ensemble.Basic
public import Rigidity.Ensemble.Moments
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.Gaussian
public import Rigidity.Flow.GoodSet
public import Rigidity.Flow.Herm
public import Rigidity.Flow.Invariant
public import Rigidity.Flow.Mehler
public import Rigidity.LocalLaw.GoodEvent
public import Rigidity.Semicircle.Density
public import Rigidity.Semicircle.Locations
public import Rigidity.MainDefs

@[expose] public section

/-!
# The flow ensembles `H_t`, `H̃_t = κ_t H_t` and `Ṽ = κ_∞ V`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For an ensemble `ν` over `𝕜`, `H_t = e^{-t/2} H_0 + (1 - e^{-t})^{1/2} V` with `H_0 ∼ ν` and
`V ∼ 𝐆` independent (12.1).  The file defines the law of `H_t` on `𝓗` (`Ensemble.flowLaw`), the
law `ν_t` of `λ(H_t)` (`Ensemble.eigLaw`), `κ_t` and the ensemble `ν̃^t` of `H̃_t = κ_t H_t`
(13.1), and the parameters `(ϑ̃, δ̃₋, δ̃₊, C̃₀)` of Lemma 13.1.  It proves:
* Lemma 13.A for `H_t`: the entrywise flow ensemble with the Gaussian ensemble has the matrix law
  `law(H_t)`;
* Lemma 13.1 (a): `∑_i σ_{t,ij}² = κ_t⁻²`;
* Lemma 13.1 (b): `ν̃^t ∈ 𝓔_N(ϑ̃, δ̃₋, δ̃₊, C̃₀)` for every real `t ≥ 0`, `H̃_t` has the law of
  `H(x)` under `ℙ_{ν̃^t}`, and the case `t = ∞`, `Ṽ = κ_∞ V`;
* Lemma 13.1 (c): `1 ≥ κ_t ≥ (1 + 1/N)^{-1/2}`, `0 ≤ κ_t⁻¹ - 1 ≤ 1/(2N)`,
  `|λ_j(H) - λ_j(κ_t H)| ≤ |λ_j(κ_t H)|/(2N)` and `𝔫_{c x}(e) = 𝔫_x(e/c)` for `c > 0` (the
  identity `λ(c H) = c λ(H)` is `eigVec_smul`);
* §18, moments of `H_0`: `𝔼|H_0|^q < ∞` for every real `q ≥ 0`, and `𝔼|H_0|² = N`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- The law of `H_t = e^{-t/2} H_0 + (1 - e^{-t})^{1/2} V` (12.1). -/
noncomputable def flowLaw (t : ℝ) : Measure (Herm 𝕜 N) := ouLaw (gaussVar 𝕜 N) M.hermLaw t

/-- `κ_t` (13.1). -/
noncomputable def kappaT (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (t : ℝ) : ℝ :=
  (1 + (2 - betaF 𝕜) * ouS t / (betaF 𝕜 * N)) ^ (-(1 / 2 : ℝ))

/-- The ensemble `ν̃^t` of `H̃_t = κ_t H_t` (13.1), entrywise. -/
noncomputable def tildeFlow (t : ℝ) : Ensemble 𝕜 N :=
  (M.ouFlow (gbeEnsemble 𝕜 N) t).smul (kappaT 𝕜 N t)

end Ensemble

/-- The parameters `(ϑ̃, δ̃₋, δ̃₊, C̃₀)` of Lemma 13.1. -/
noncomputable def tildeTheta (ϑ : ℝ) : ℝ := min ϑ 1 / 14

noncomputable def tildeDelta (δ : ℝ) : ℝ := 3 / 4 * min δ 1

noncomputable def tildeC (C₀ : ℝ) : ℝ := max C₀ 2

/-! ### 1. The Gaussian ensemble, `κ_t`, and the entries of `H_t` -/

section Entries

variable {N : ℕ}

/-- `β = 1 + (Im I)²`, that is `β = 1` for `𝕜 = ℝ` and `β = 2` for `𝕜 = ℂ`. -/
private lemma ensembles_betaF_eq : betaF 𝕜 = 1 + RCLike.im (RCLike.I : 𝕜) ^ 2 := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · have hspan : Submodule.span ℝ ({1} : Set 𝕜) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro x
      rw [Submodule.mem_span_singleton]
      refine ⟨RCLike.re x, ?_⟩
      conv_rhs => rw [← RCLike.re_add_im x]
      simp [RCLike.real_smul_eq_coe_mul, h]
    have h1 : Module.finrank ℝ 𝕜 ≤ 1 := by
      have := finrank_span_le_card (R := ℝ) ({1} : Set 𝕜)
      rw [hspan, finrank_top] at this
      simpa using this
    have h0 : 0 < Module.finrank ℝ 𝕜 := Module.finrank_pos
    have : Module.finrank ℝ 𝕜 = 1 := by omega
    simp [betaF, h, this]
  · have hli : LinearIndependent ℝ ![(1 : 𝕜), RCLike.I] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have h1 := congrArg RCLike.re hab
      have h2 := congrArg RCLike.im hab
      have e1 : RCLike.re (a • (1 : 𝕜) + b • RCLike.I) = a := by
        simp [RCLike.real_smul_eq_coe_mul]
      have e2 : RCLike.im (a • (1 : 𝕜) + b • RCLike.I) = b := by
        simp [RCLike.real_smul_eq_coe_mul, h]
      rw [e1, map_zero] at h1
      rw [e2, map_zero] at h2
      exact ⟨h1, h2⟩
    have h2 := hli.fintype_card_le_finrank
    have h3 := RCLike.finrank_le_two 𝕜
    simp only [Fintype.card_fin] at h2
    have : Module.finrank ℝ 𝕜 = 2 := by omega
    rw [betaF, this, h]
    norm_num

/-- Elements of `𝓗` with the same real coordinates are equal. -/
private lemma ensembles_coord_ext {X Y : Herm 𝕜 N} (h : ∀ q, X.coord q = Y.coord q) : X = Y := by
  apply Subtype.ext
  apply PiLp.ext
  exact h

/-- `H(a x + b y) = a H(x) + b H(y)` entrywise, for real `a, b`. -/
private lemma ensembles_toMatrix_lin (a b : ℝ) (x y : Pair N → 𝕜) (i j : Fin N) :
    Rigidity.toMatrix (fun p => (a : 𝕜) * x p + (b : 𝕜) * y p) i j =
      (a : 𝕜) * Rigidity.toMatrix x i j + (b : 𝕜) * Rigidity.toMatrix y i j := by
  simp only [Rigidity.toMatrix, Matrix.of_apply]
  split_ifs
  · rfl
  · simp [star_add, star_mul', RCLike.star_def]
  · simp only [map_add, RCLike.re_ofReal_mul]
    push_cast
    ring

/-- `x ↦ H(x)` is `ℝ`-linear. -/
private lemma ensembles_ofPair_lin (a b : ℝ) (x y : Pair N → 𝕜) :
    Herm.ofPair (fun p => (a : 𝕜) * x p + (b : 𝕜) * y p) =
      a • Herm.ofPair x + b • Herm.ofPair y := by
  apply ensembles_coord_ext
  intro q
  change _ = a * (Herm.ofPair x).coord q + b * (Herm.ofPair y).coord q
  simp only [Herm.coord, Herm.ofPair, ensembles_toMatrix_lin]
  split_ifs <;> simp


/-- The ensemble of `c H` has the law `(c ·)_* law(H)` on `𝓗`. -/
private lemma ensembles_hermLaw_smul (M : Ensemble 𝕜 N) (c : ℝ) :
    (M.smul c).hermLaw = M.hermLaw.map fun H => c • H := by
  have hm := Herm.measurable_ofPair (𝕜 := 𝕜) N
  have hs : Measurable fun x : Pair N → 𝕜 => (c : 𝕜) • x := measurable_const_smul _
  unfold Ensemble.hermLaw
  rw [Ensemble.prodLaw_smul, Measure.map_map hm hs, Measure.map_map (measurable_const_smul _) hm]
  congr 1
  funext x
  have := ensembles_ofPair_lin (𝕜 := 𝕜) c 0 x 0
  simp only [Function.comp_apply, zero_smul, add_zero] at this ⊢
  rw [← this]
  congr 1
  funext p
  simp

/-- `1 ≤ β`. -/
private lemma ensembles_one_le_betaF : 1 ≤ betaF 𝕜 := by
  rw [ensembles_betaF_eq]; nlinarith [sq_nonneg (RCLike.im (RCLike.I : 𝕜))]

/-- `β ≤ 2`. -/
private lemma ensembles_betaF_le_two : betaF 𝕜 ≤ 2 := by
  rw [ensembles_betaF_eq]
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · simp [h]
  · simp [h]; norm_num

/-- `∫ a² dN(0, v) = v`. -/
private lemma ensembles_integral_sq_gaussianReal (v : NNReal) :
    ∫ a, a ^ 2 ∂ProbabilityTheory.gaussianReal 0 v = v := by
  have h := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := v)
  rw [ProbabilityTheory.variance_of_integral_eq_zero measurable_id.aemeasurable
    (by simp)] at h
  simpa using h

/-- `a ↦ a²` is integrable against `N(0, v)`. -/
private lemma ensembles_integrable_sq_gaussianReal (v : NNReal) :
    Integrable (fun a : ℝ => a ^ 2) (ProbabilityTheory.gaussianReal 0 v) := by
  simpa using (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

/-- `a ↦ a` is integrable against `N(0, v)`. -/
private lemma ensembles_integrable_gaussianReal (v : NNReal) :
    Integrable (fun a : ℝ => a) (ProbabilityTheory.gaussianReal 0 v) := by
  exact (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl

/-- `|a + b I|² = a² + (Im I)² b²` for real `a, b`. -/
private lemma ensembles_norm_sq_ofReal_add_mul_I (a b : ℝ) :
    ‖(a : 𝕜) + (b : 𝕜) * RCLike.I‖ ^ 2 = a ^ 2 + RCLike.im (RCLike.I : 𝕜) ^ 2 * b ^ 2 := by
  rw [RCLike.norm_sq_eq_def]
  simp
  ring

/-- The entry variances of the Gaussian ensemble: `τ_ii² = 2/(βN)`, `τ_ij² = 1/N` for `i < j`. -/
private lemma ensembles_varPair_gbe (p : Pair N) :
    (gbeEnsemble 𝕜 N).varPair p = if p.1.1 = p.1.2 then 2 / (betaF 𝕜 * N) else 1 / N := by
  unfold Ensemble.varPair
  change ∫ z, ‖z‖ ^ 2 ∂gbeEntryLaw 𝕜 N p = _
  have hβ : 0 < betaF 𝕜 := lt_of_lt_of_le one_pos ensembles_one_le_betaF
  unfold gbeEntryLaw
  split_ifs with h
  · rw [integral_map RCLike.continuous_ofReal.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [RCLike.norm_ofReal, sq_abs]
    rw [ensembles_integral_sq_gaussianReal, Real.coe_toNNReal _ (by positivity)]
  · have hm : Measurable fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I := by fun_prop
    rw [integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp_rw [ensembles_norm_sq_ofReal_add_mul_I]
    have hi := ensembles_integrable_sq_gaussianReal (1 / (betaF 𝕜 * N)).toNNReal
    rw [integral_add (hi.comp_fst _) ((hi.comp_snd _).const_mul _), integral_const_mul,
      integral_fun_fst (fun a : ℝ => a ^ 2), integral_fun_snd (fun a : ℝ => a ^ 2),
      ensembles_integral_sq_gaussianReal, Real.coe_toNNReal _ (by positivity)]
    simp only [probReal_univ, one_smul]
    have e : (1 / (betaF 𝕜 * N) + RCLike.im (RCLike.I : 𝕜) ^ 2 * (1 / (betaF 𝕜 * N))) =
        betaF 𝕜 * (1 / (betaF 𝕜 * N)) := by rw [ensembles_betaF_eq]; ring
    rw [e, mul_one_div, ← div_div, div_self hβ.ne']

/-- The second moment of each Gaussian entry is finite. -/
private lemma ensembles_integrable_sq_gbe (p : Pair N) :
    Integrable (fun y : 𝕜 => ‖y‖ ^ 2) ((gbeEnsemble 𝕜 N).law p) := by
  change Integrable _ (gbeEntryLaw 𝕜 N p)
  unfold gbeEntryLaw
  split_ifs with h
  · rw [integrable_map_measure (by fun_prop) RCLike.continuous_ofReal.measurable.aemeasurable]
    have := ensembles_integrable_sq_gaussianReal (2 / (betaF 𝕜 * N)).toNNReal
    refine this.congr (ae_of_all _ fun a => ?_)
    simp
  · have hm : Measurable fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I := by fun_prop
    rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
    have hi := ensembles_integrable_sq_gaussianReal (1 / (betaF 𝕜 * N)).toNNReal
    refine ((hi.comp_fst _).add ((hi.comp_snd _).const_mul (RCLike.im (RCLike.I : 𝕜) ^ 2))).congr
      (ae_of_all _ fun ab => ?_)
    simp only [Function.comp_apply, Pi.add_apply]
    rw [ensembles_norm_sq_ofReal_add_mul_I]

/-- The Gaussian entries are centred. -/
private lemma ensembles_meanZero_gbe : (gbeEnsemble 𝕜 N).MeanZero := by
  intro p
  change ∫ y, y ∂gbeEntryLaw 𝕜 N p = 0
  unfold gbeEntryLaw
  split_ifs with h
  · rw [integral_map RCLike.continuous_ofReal.measurable.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), integral_ofReal,
      ProbabilityTheory.integral_id_gaussianReal]
    simp
  · have hm : Measurable fun ab : ℝ × ℝ => (ab.1 : 𝕜) + (ab.2 : 𝕜) * RCLike.I := by fun_prop
    rw [integral_map hm.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    have hi := (ensembles_integrable_gaussianReal (1 / (betaF 𝕜 * N)).toNNReal).ofReal (𝕜 := 𝕜)
    rw [integral_add (hi.comp_fst _) ((hi.comp_snd _).mul_const _), integral_mul_const,
      integral_fun_fst (fun a : ℝ => (a : 𝕜)), integral_fun_snd (fun a : ℝ => (a : 𝕜)),
      integral_ofReal, ProbabilityTheory.integral_id_gaussianReal]
    simp

/-- The diagonal Gaussian entries are real. -/
private lemma ensembles_diagReal_gbe : (gbeEnsemble 𝕜 N).DiagReal := by
  intro i
  change ∀ᵐ y ∂gbeEntryLaw 𝕜 N (Pair.mk' i i), RCLike.im y = 0
  have hd : (Pair.mk' i i).1.1 = (Pair.mk' i i).1.2 := by simp [Pair.mk']
  simp only [gbeEntryLaw, hd, ite_true]
  have hm : MeasurableSet {y : 𝕜 | RCLike.im y = 0} :=
    measurableSet_eq_fun RCLike.continuous_im.measurable measurable_const
  rw [ae_map_iff RCLike.continuous_ofReal.measurable.aemeasurable hm]
  exact ae_of_all _ fun a => by simp

/-- `τ_ij² = N⁻¹ + [i = j] (2 - β)/(βN)`. -/
private lemma ensembles_var_gbe (i j : Fin N) :
    (gbeEnsemble 𝕜 N).var i j = 1 / N + if i = j then (2 - betaF 𝕜) / (betaF 𝕜 * N) else 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Fin.pos i)
  have hβ : 0 < betaF 𝕜 := lt_of_lt_of_le one_pos ensembles_one_le_betaF
  unfold Ensemble.var
  rw [ensembles_varPair_gbe]
  have hiff : (Pair.mk' i j).1.1 = (Pair.mk' i j).1.2 ↔ i = j := by
    unfold Pair.mk'
    split_ifs with h
    · simp
    · simp only
      exact ⟨fun h' => h'.symm, fun h' => h'.symm⟩
  simp only [hiff]
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    field_simp
    ring
  · simp only [h, ↓reduceIte, add_zero]

/-- `∑_i τ_ij² = 1 + (2 - β)/(βN)`. -/
private lemma ensembles_sum_var_gbe (j : Fin N) :
    ∑ i, (gbeEnsemble 𝕜 N).var i j = 1 + (2 - betaF 𝕜) / (betaF 𝕜 * N) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Fin.pos j)
  simp_rw [ensembles_var_gbe]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j]
  simp [Finset.card_univ, hN.ne']

/-- On `𝐞^⊥`, `⟨v, T v⟩ = (2 - β)/(βN) |v|²` for the variance matrix `T` of the Gaussian
ensemble. -/
private lemma ensembles_quad_gbe (v : Fin N → ℝ) (hv : ∑ i, v i = 0) :
    v ⬝ᵥ ((gbeEnsemble 𝕜 N).varMatrix *ᵥ v) =
      (2 - betaF 𝕜) / (betaF 𝕜 * N) * ∑ i, v i ^ 2 := by
  have hT : (gbeEnsemble 𝕜 N).varMatrix *ᵥ v = fun i => (2 - betaF 𝕜) / (betaF 𝕜 * N) * v i := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Ensemble.varMatrix, Matrix.of_apply, ensembles_var_gbe,
      add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hv, mul_zero, zero_add, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hT]
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `s_t ≥ 0` for `t ≥ 0`. -/
private lemma ensembles_ouS_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ouS t := by
  rw [ouS, sub_nonneg]; exact Real.exp_le_one_iff.2 (by linarith)

/-- `s_t ≤ 1`. -/
private lemma ensembles_ouS_le_one (t : ℝ) : ouS t ≤ 1 := by
  rw [ouS]; linarith [Real.exp_pos (-t)]

/-- `0 ≤ (2 - β)/(βN)`. -/
private lemma ensembles_rN_nonneg (N : ℕ) : 0 ≤ (2 - betaF 𝕜) / (betaF 𝕜 * N) := by
  have h1 := ensembles_one_le_betaF (𝕜 := 𝕜)
  have h2 := ensembles_betaF_le_two (𝕜 := 𝕜)
  apply div_nonneg (by linarith) (mul_nonneg (by linarith) (Nat.cast_nonneg N))

/-- `(2 - β)/(βN) ≤ 1/N`. -/
private lemma ensembles_rN_le (N : ℕ) : (2 - betaF 𝕜) / (betaF 𝕜 * N) ≤ 1 / N := by
  have h1 := ensembles_one_le_betaF (𝕜 := 𝕜)
  have h2 := ensembles_betaF_le_two (𝕜 := 𝕜)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [div_le_div_iff₀ (by positivity) hN']
  nlinarith

/-- `((1 + u)^{-1/2})² = (1 + u)⁻¹`. -/
private lemma ensembles_rpow_sq {u : ℝ} (hu : 0 ≤ u) :
    ((1 + u) ^ (-(1 / 2 : ℝ))) ^ 2 = (1 + u)⁻¹ := by
  rw [Real.rpow_neg (by linarith), inv_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by linarith)]

/-- `((1 + u)^{-1/2})⁻¹ = (1 + u)^{1/2}`. -/
private lemma ensembles_inv_rpow {u : ℝ} (hu : 0 ≤ u) :
    ((1 + u) ^ (-(1 / 2 : ℝ)))⁻¹ = Real.sqrt (1 + u) := by
  rw [Real.rpow_neg (by linarith), inv_inv, ← Real.sqrt_eq_rpow]

/-- `((1 + u)^{-1/2})⁻² = 1 + u`. -/
private lemma ensembles_inv_rpow_sq {u : ℝ} (hu : 0 ≤ u) :
    ((1 + u) ^ (-(1 / 2 : ℝ)))⁻¹ ^ 2 = 1 + u := by
  rw [ensembles_inv_rpow hu, Real.sq_sqrt (by linarith)]

/-- `(1 + u)^{-1/2} > 0`. -/
private lemma ensembles_rpow_pos {u : ℝ} (hu : 0 ≤ u) : 0 < (1 + u) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos (by linarith) _

/-- `r_t = (2 - β) s_t/(βN) ∈ [0, 1/N]`. -/
private lemma ensembles_rT_mem {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (2 - betaF 𝕜) * ouS t / (betaF 𝕜 * N) ∧ (2 - betaF 𝕜) * ouS t / (betaF 𝕜 * N) ≤ 1 / N := by
  have e : (2 - betaF 𝕜) * ouS t / (betaF 𝕜 * N) = ouS t * ((2 - betaF 𝕜) / (betaF 𝕜 * N)) := by
    ring
  have h0 := ensembles_rN_nonneg (𝕜 := 𝕜) N
  have h1 := ensembles_rN_le (𝕜 := 𝕜) N
  have hs0 := ensembles_ouS_nonneg ht
  have hs1 := ensembles_ouS_le_one t
  rw [e]
  exact ⟨mul_nonneg hs0 h0, by nlinarith⟩

/-- The entry variances of the flow ensemble: `σ_{t,ij}² = e^{-t} σ_ij² + s_t τ_ij²`. -/
private lemma ensembles_varPair_ouFlow {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) {M : Ensemble 𝕜 N}
    (hM : M.Assumptions ϑ δm δp C₀) {t : ℝ} (ht : 0 ≤ t) (p : Pair N) :
    (M.ouFlow (gbeEnsemble 𝕜 N) t).varPair p =
      Real.exp (-t) * M.varPair p + ouS t * (gbeEnsemble 𝕜 N).varPair p :=
  M.varPair_ouFlow _ t ht hM.meanZero ensembles_meanZero_gbe p
    (Ensemble.Assumptions.integrable_norm_pow M hM hϑ p 2)
    (ensembles_integrable_sq_gbe p)

/-- `e² ≤ 14`. -/
private lemma ensembles_exp_two_le : Real.exp 2 ≤ 14 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1]

/-- `5e ≤ 14`. -/
private lemma ensembles_exp_one_le : Real.exp 1 ≤ 14 / 5 := by
  have h := Real.exp_one_lt_d9
  norm_num at h ⊢
  linarith

/-- The tail bound (T) of Lemma 13.1 for `1 ≤ x < 2`: the right side is at least `1`. -/
private lemma ensembles_tail_small {ϑb x : ℝ} (h0 : 0 < ϑb) (h1 : ϑb ≤ 1) (hx : 1 ≤ x)
    (hx2 : x < 2) : 1 ≤ (ϑb / 14)⁻¹ * Real.exp (-(x ^ (ϑb / 14))) := by
  have hxe : x ^ (ϑb / 14) ≤ x := by
    calc x ^ (ϑb / 14) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = x := Real.rpow_one x
  have hE : Real.exp (-2) ≤ Real.exp (-(x ^ (ϑb / 14))) := Real.exp_le_exp.mpr (by linarith)
  have hI : 14 ≤ (ϑb / 14)⁻¹ := by
    rw [inv_div, le_div_iff₀ h0]
    linarith
  have h2 : 1 ≤ 14 * Real.exp (-2) := by
    have := ensembles_exp_two_le
    have e : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-2)]
  calc (1 : ℝ) ≤ 14 * Real.exp (-2) := h2
    _ ≤ (ϑb / 14)⁻¹ * Real.exp (-(x ^ (ϑb / 14))) :=
        mul_le_mul hI hE (Real.exp_pos _).le (by linarith)

/-- The tail bound (T) of Lemma 13.1 for `x ≥ 2`, as an inequality between the two tail terms
and `ϑ̃⁻¹ e^{-x^{ϑ̃}}`, with `ϑ̄ = min(ϑ, 1)` and `ϑ̃ = ϑ̄/14`. -/
private lemma ensembles_tail_large {ϑb x : ℝ} (h0 : 0 < ϑb) (h1 : ϑb ≤ 1) (hx : 2 ≤ x) :
    ϑb⁻¹ * Real.exp (-((x / 2) ^ ϑb)) + 4 * Real.exp (-(x / 2) ^ 2 / 2) ≤
      (ϑb / 14)⁻¹ * Real.exp (-(x ^ (ϑb / 14))) := by
  have hx0 : 0 ≤ x := by linarith
  set y := x ^ (ϑb / 2) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by linarith)
  have hxy : x ^ ϑb = y ^ 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have h2ϑ : (2 : ℝ) ^ ϑb ≤ 2 := by
    calc (2 : ℝ) ^ ϑb ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 := Real.rpow_one 2
  have h2ϑ0 : 0 < (2 : ℝ) ^ ϑb := Real.rpow_pos_of_pos (by norm_num) _
  have hA : y - 1 ≤ (x / 2) ^ ϑb := by
    rw [Real.div_rpow hx0 (by norm_num), hxy]
    have : y ^ 2 / 2 ≤ y ^ 2 / 2 ^ ϑb :=
      div_le_div_of_nonneg_left (by positivity) h2ϑ0 h2ϑ
    nlinarith [sq_nonneg (y - 1)]
  have hB : y - 1 ≤ (x / 2) ^ 2 / 2 := by
    set u := Real.sqrt x with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg x
    have hux : u ^ 2 = x := Real.sq_sqrt hx0
    have hyu : y ≤ u := by
      rw [hy, hu, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [← hux]
    nlinarith [sq_nonneg (u ^ 2 - 8 / 5), sq_nonneg (u - 5 / 4)]
  have hC : x ^ (ϑb / 14) ≤ y := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hI : 1 ≤ ϑb⁻¹ := one_le_inv₀ h0 |>.mpr h1
  have hE1 : Real.exp (-((x / 2) ^ ϑb)) ≤ Real.exp 1 * Real.exp (-y) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hE2 : Real.exp (-(x / 2) ^ 2 / 2) ≤ Real.exp 1 * Real.exp (-y) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hE3 : Real.exp (-y) ≤ Real.exp (-(x ^ (ϑb / 14))) := Real.exp_le_exp.mpr (by linarith)
  have he := ensembles_exp_one_le
  have hepos := Real.exp_pos 1
  have hypos := Real.exp_pos (-y)
  have hinv : (ϑb / 14)⁻¹ = 14 * ϑb⁻¹ := by rw [inv_div]; ring
  rw [hinv]
  set E := Real.exp (-y)
  set F := Real.exp (-(x ^ (ϑb / 14)))
  set I := ϑb⁻¹
  set e := Real.exp 1
  calc I * Real.exp (-((x / 2) ^ ϑb)) + 4 * Real.exp (-(x / 2) ^ 2 / 2)
      ≤ I * (e * E) + 4 * (e * E) := by gcongr
    _ ≤ I * (e * E) + 4 * I * (e * E) := by nlinarith [mul_pos hepos hypos]
    _ = 5 * e * (I * E) := by ring
    _ ≤ 14 * (I * E) := by nlinarith [mul_pos (lt_of_lt_of_le one_pos hI) hypos]
    _ ≤ 14 * I * F := by nlinarith [lt_of_lt_of_le one_pos hI]

/-- The Gaussian tail of Lemma 13.B (b) against `ϑ̃⁻¹ e^{-x^{ϑ̃}}`, for `x ≥ 1`. -/
private lemma ensembles_tail_gauss {ϑb x : ℝ} (h0 : 0 < ϑb) (h1 : ϑb ≤ 1) (hx : 1 ≤ x) :
    4 * Real.exp (-x ^ 2 / 2) ≤ (ϑb / 14)⁻¹ * Real.exp (-(x ^ (ϑb / 14))) := by
  have hxe : x ^ (ϑb / 14) ≤ x := by
    calc x ^ (ϑb / 14) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = x := Real.rpow_one x
  have hI : 14 ≤ (ϑb / 14)⁻¹ := by
    rw [inv_div, le_div_iff₀ h0]
    linarith
  have hE : Real.exp (-x ^ 2 / 2) ≤ Real.exp 1 * Real.exp (-(x ^ (ϑb / 14))) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x - 1)])
  have he := ensembles_exp_one_le
  have hF := Real.exp_pos (-(x ^ (ϑb / 14)))
  calc 4 * Real.exp (-x ^ 2 / 2) ≤ 4 * (Real.exp 1 * Real.exp (-(x ^ (ϑb / 14)))) := by gcongr
    _ ≤ 14 * Real.exp (-(x ^ (ϑb / 14))) := by nlinarith
    _ ≤ (ϑb / 14)⁻¹ * Real.exp (-(x ^ (ϑb / 14))) := by gcongr


/-- Multiplication by a real scalar is measurable. -/
private lemma ensembles_measurable_mul (c : ℝ) : Measurable fun y : 𝕜 => (c : 𝕜) * y :=
  measurable_const.mul measurable_id

/-- A finite second moment gives a finite first moment. -/
private lemma ensembles_integrable_of_sq {μ : Measure 𝕜} [IsProbabilityMeasure μ]
    (hi : Integrable (fun y : 𝕜 => ‖y‖ ^ 2) μ) : Integrable (fun y : 𝕜 => y) μ := by
  refine (hi.add (integrable_const (1 : ℝ))).mono' aestronglyMeasurable_id
    (ae_of_all _ fun y => ?_)
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 1)]

/-- Mean and integrability of a real multiple of an entry. -/
private lemma ensembles_integral_smul (M : Ensemble 𝕜 N) (c : ℝ) (p : Pair N)
    (hi : Integrable (fun y : 𝕜 => y) (M.law p)) :
    Integrable (fun y : 𝕜 => y) ((M.smul c).law p) ∧
      ∫ y, y ∂(M.smul c).law p = (c : 𝕜) * ∫ y, y ∂M.law p := by
  change Integrable (fun y : 𝕜 => y) ((M.law p).map _) ∧ ∫ y, y ∂(M.law p).map _ = _
  refine ⟨?_, ?_⟩
  · rw [integrable_map_measure (g := fun y : 𝕜 => y) (by fun_prop)
      (ensembles_measurable_mul c).aemeasurable]
    exact hi.const_mul _
  · rw [integral_map (ensembles_measurable_mul c).aemeasurable (by fun_prop), integral_const_mul]

/-- Lemma 13.1 (a): the entries of `H_t` are centred. -/
private lemma ensembles_meanZero_ouFlow {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) {M : Ensemble 𝕜 N}
    (hM : M.Assumptions ϑ δm δp C₀) (t : ℝ) : (M.ouFlow (gbeEnsemble 𝕜 N) t).MeanZero := by
  intro p
  set a : ℝ := Real.exp (-t / 2)
  set b : ℝ := Real.sqrt (1 - Real.exp (-t))
  obtain ⟨hμ1, hμ0⟩ := ensembles_integral_smul M a p
    (ensembles_integrable_of_sq (Ensemble.Assumptions.integrable_norm_pow M hM hϑ p 2))
  obtain ⟨hν1, hν0⟩ := ensembles_integral_smul (gbeEnsemble 𝕜 N) b p
    (ensembles_integrable_of_sq (ensembles_integrable_sq_gbe p))
  change ∫ y, y ∂((M.smul a).law p ∗ ((gbeEnsemble 𝕜 N).smul b).law p) = 0
  have hadd : Measurable fun z : 𝕜 × 𝕜 => z.1 + z.2 := measurable_fst.add measurable_snd
  unfold Measure.conv
  rw [integral_map hadd.aemeasurable (by fun_prop),
    integral_add (hμ1.comp_fst _) (hν1.comp_snd _),
    integral_fun_fst (fun y : 𝕜 => y), integral_fun_snd (fun y : 𝕜 => y), hμ0, hν0,
    hM.meanZero p, ensembles_meanZero_gbe p]
  simp

/-- Real multiples keep real diagonal entries. -/
private lemma ensembles_ae_im_map {μ : Measure 𝕜} (c : ℝ) (h : ∀ᵐ y ∂μ, RCLike.im y = 0) :
    ∀ᵐ y ∂μ.map (fun y : 𝕜 => (c : 𝕜) * y), RCLike.im y = 0 := by
  have hm : MeasurableSet {y : 𝕜 | RCLike.im y = 0} :=
    measurableSet_eq_fun RCLike.continuous_im.measurable measurable_const
  rw [ae_map_iff (ensembles_measurable_mul c).aemeasurable hm]
  filter_upwards [h] with y hy
  simp [hy]

/-- Lemma 13.1 (b): the diagonal entries of `H_t` are real. -/
private lemma ensembles_diagReal_ouFlow {M : Ensemble 𝕜 N} (hR : M.DiagReal) (t : ℝ) :
    (M.ouFlow (gbeEnsemble 𝕜 N) t).DiagReal := by
  intro i
  set a : ℝ := Real.exp (-t / 2)
  set b : ℝ := Real.sqrt (1 - Real.exp (-t))
  change ∀ᵐ y ∂((M.smul a).law (Pair.mk' i i) ∗
    ((gbeEnsemble 𝕜 N).smul b).law (Pair.mk' i i)), RCLike.im y = 0
  have hadd : Measurable fun z : 𝕜 × 𝕜 => z.1 + z.2 := measurable_fst.add measurable_snd
  have hm : MeasurableSet {y : 𝕜 | RCLike.im y = 0} :=
    measurableSet_eq_fun RCLike.continuous_im.measurable measurable_const
  unfold Measure.conv
  rw [ae_map_iff hadd.aemeasurable hm]
  have h1 := ensembles_ae_im_map a (hR i)
  have h2 := ensembles_ae_im_map b (ensembles_diagReal_gbe (N := N) (𝕜 := 𝕜) i)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
    Measure.quasiMeasurePreserving_snd.ae h2] with z hz1 hz2
  simp [hz1, hz2]

/-- Lemma 13.1 (b), (D): the tail bound (T) for the entries of `H_t`, with `ϑ̃`. -/
private lemma ensembles_subexp_ouFlow {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) {M : Ensemble 𝕜 N}
    (hM : M.Assumptions ϑ δm δp C₀) {t : ℝ} (ht : 0 ≤ t) :
    (M.ouFlow (gbeEnsemble 𝕜 N) t).SubexpDecay (tildeTheta ϑ) := by
  intro p x hx
  set G := gbeEnsemble 𝕜 N
  set ϑb := min ϑ 1 with hϑb
  have hϑb0 : 0 < ϑb := lt_min hϑ one_pos
  have hϑb1 : ϑb ≤ 1 := min_le_right _ _
  have hMb : M.Assumptions ϑb δm δp C₀ :=
    Ensemble.Assumptions.mono M hM hϑb0 (min_le_left _ _) le_rfl le_rfl le_rfl
  change _ ≤ ENNReal.ofReal ((ϑb / 14)⁻¹ * Real.exp (-(x ^ (ϑb / 14))))
  set σt := Real.sqrt ((M.ouFlow G t).varPair p) with hσt
  have hσt0 : 0 ≤ σt := Real.sqrt_nonneg _
  rcases lt_or_ge x 2 with hx2 | hx2
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (ensembles_tail_small hϑb0 hϑb1 hx hx2)
  set a : ℝ := Real.exp (-t / 2) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-t)) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hs0 : 0 ≤ 1 - Real.exp (-t) := by
    rw [sub_nonneg]; exact Real.exp_le_one_iff.2 (by linarith)
  have hvar := ensembles_varPair_ouFlow hϑ hM ht p
  have hV0 : 0 ≤ M.varPair p := integral_nonneg fun y => by positivity
  have hT0 : 0 ≤ G.varPair p := integral_nonneg fun y => by positivity
  have hσa : a * Real.sqrt (M.varPair p) ≤ σt := by
    have e : a * Real.sqrt (M.varPair p) = Real.sqrt (Real.exp (-t) * M.varPair p) := by
      rw [Real.sqrt_mul (Real.exp_pos _).le, ha, ← Real.exp_half]
    rw [e, hσt, hvar]
    exact Real.sqrt_le_sqrt (by have := ensembles_ouS_nonneg ht; nlinarith)
  have hσb : b * Real.sqrt (G.varPair p) ≤ σt := by
    rw [hb, ← Real.sqrt_mul hs0, hσt, hvar]
    exact Real.sqrt_le_sqrt (by
      have := Real.exp_pos (-t)
      unfold ouS
      nlinarith)
  -- the two events
  set A : Set 𝕜 := {y | x * σt / 2 < ‖(a : 𝕜) * y‖} with hA
  set B : Set 𝕜 := {z | x * σt / 2 < ‖(b : 𝕜) * z‖} with hB
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const ((ensembles_measurable_mul a).norm)
  have hBm : MeasurableSet B :=
    measurableSet_lt measurable_const ((ensembles_measurable_mul b).norm)
  have hS : MeasurableSet {y : 𝕜 | x * σt < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hadd : Measurable fun z : 𝕜 × 𝕜 => z.1 + z.2 := measurable_fst.add measurable_snd
  have hsplit : (M.ouFlow G t).law p {y | x * σt < ‖y‖} ≤ M.law p A + G.law p B := by
    change ((M.smul a).law p ∗ (G.smul b).law p) _ ≤ _
    unfold Measure.conv
    rw [Measure.map_apply hadd hS]
    have hsub : (fun z : 𝕜 × 𝕜 => z.1 + z.2) ⁻¹' {y | x * σt < ‖y‖} ⊆
        {u : 𝕜 | x * σt / 2 < ‖u‖} ×ˢ Set.univ ∪ Set.univ ×ˢ {w : 𝕜 | x * σt / 2 < ‖w‖} := by
      rintro ⟨u, w⟩ huw
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at huw
      by_contra hn
      simp only [Set.mem_union, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true,
        true_and, not_or, not_lt] at hn
      have := norm_add_le u w
      linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]
    have hu : MeasurableSet {u : 𝕜 | x * σt / 2 < ‖u‖} :=
      measurableSet_lt measurable_const measurable_norm
    change (M.law p).map _ _ + (G.law p).map _ _ ≤ _
    rw [Measure.map_apply (ensembles_measurable_mul a) hu,
      Measure.map_apply (ensembles_measurable_mul b) hu]
    rfl
  have hAb : M.law p A ≤ ENNReal.ofReal (ϑb⁻¹ * Real.exp (-((x / 2) ^ ϑb))) := by
    rcases hV0.eq_or_lt with hV | hV
    · have h0 := Ensemble.Assumptions.law_ne_zero M hM p hV.symm
      refine le_trans (measure_mono ?_) (h0.le.trans zero_le)
      intro y hy
      simp only [hA, Set.mem_ofPred_eq] at hy
      simp only [Set.mem_ofPred_eq]
      rintro rfl
      simp only [mul_zero, norm_zero] at hy
      nlinarith
    · have hσ : 0 < Real.sqrt (M.varPair p) := Real.sqrt_pos.mpr hV
      refine le_trans (measure_mono ?_) (hMb.subexp p (x / 2) (by linarith))
      intro y hy
      simp only [hA, Set.mem_ofPred_eq, norm_mul, RCLike.norm_ofReal, abs_of_pos ha0] at hy
      simp only [Set.mem_ofPred_eq]
      by_contra hn
      rw [not_lt] at hn
      nlinarith [mul_le_mul_of_nonneg_left hn ha0.le]
  have hBb : G.law p B ≤ ENNReal.ofReal (4 * Real.exp (-(x / 2) ^ 2 / 2)) := by
    rcases hb0.eq_or_lt with hb' | hb'
    · have : B = ∅ := by
        ext z
        simp only [hB, ← hb', RCLike.ofReal_zero, zero_mul, norm_zero, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_lt]
        nlinarith
      rw [this, measure_empty]
      exact zero_le
    · refine le_trans (measure_mono ?_) (gbeEntryLaw_tail p (y := x / 2) (by linarith))
      intro z hz
      simp only [hB, Set.mem_ofPred_eq, norm_mul, RCLike.norm_ofReal, abs_of_pos hb'] at hz
      simp only [Set.mem_ofPred_eq]
      by_contra hn
      rw [not_lt] at hn
      nlinarith [mul_le_mul_of_nonneg_left hn hb'.le]
  refine hsplit.trans ((add_le_add hAb hBb).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (ensembles_tail_large hϑb0 hϑb1 hx2)

end Entries

/-! ### 2. Lemma 13.A for `H_t`, Lemma 13.1 (a), (b) -/

/-- Lemma 13.A for `H_t`: the entrywise flow ensemble has matrix law `law(H_t)`. -/
theorem Ensemble.ouFlow_gbe_hermLaw {N : ℕ} (M : Ensemble 𝕜 N) (t : ℝ) :
    (M.ouFlow (gbeEnsemble 𝕜 N) t).hermLaw = M.flowLaw t := by
  set G := gbeEnsemble 𝕜 N
  set a : ℝ := Real.exp (-t / 2)
  set b : ℝ := Real.sqrt (1 - Real.exp (-t))
  have hm := Herm.measurable_ofPair (𝕜 := 𝕜) N
  have hadd : Measurable fun z : 𝕜 × 𝕜 => z.1 + z.2 := measurable_fst.add measurable_snd
  have hpi : Measure.pi (fun p => (M.ouFlow G t).law p) =
      (Measure.pi fun p => ((M.smul a).law p).prod ((G.smul b).law p)).map
        fun w p => (w p).1 + (w p).2 := by
    rw [Measure.pi_map_pi (fun p => hadd.aemeasurable)]
    rfl
  have he := (measurePreserving_arrowProdEquivProdArrow 𝕜 𝕜 (Pair N) (fun p => (M.smul a).law p)
    (fun p => (G.smul b).law p)).symm
  have hsa : Measurable fun x : Pair N → 𝕜 => (a : 𝕜) • x := measurable_const_smul _
  have hsb : Measurable fun x : Pair N → 𝕜 => (b : 𝕜) • x := measurable_const_smul _
  have hlin : Measurable fun w : Pair N → 𝕜 × 𝕜 => fun p => (w p).1 + (w p).2 := by fun_prop
  have hL : (M.ouFlow G t).hermLaw = (M.prodLaw.prod G.prodLaw).map
      fun z => a • Herm.ofPair z.1 + b • Herm.ofPair z.2 := by
    unfold Ensemble.hermLaw
    rw [show (M.ouFlow G t).prodLaw = Measure.pi (fun p => (M.ouFlow G t).law p) from rfl, hpi,
      ← he.map_eq, Measure.map_map hlin he.measurable]
    rw [show Measure.pi (fun p => (M.smul a).law p) = (M.smul a).prodLaw from rfl,
      show Measure.pi (fun p => (G.smul b).law p) = (G.smul b).prodLaw from rfl,
      Ensemble.prodLaw_smul, Ensemble.prodLaw_smul, Measure.map_prod_map _ _ hsa hsb,
      Measure.map_map (hlin.comp he.measurable) (hsa.prodMap hsb),
      Measure.map_map hm ((hlin.comp he.measurable).comp (hsa.prodMap hsb))]
    congr 1
    funext z
    rw [← ensembles_ofPair_lin]
    rfl
  have hR : ouLaw (gaussVar 𝕜 N) M.hermLaw t = (M.prodLaw.prod G.prodLaw).map
      fun z => a • Herm.ofPair z.1 + b • Herm.ofPair z.2 := by
    unfold ouLaw
    rw [show gaussE (Herm 𝕜 N) (gaussVar 𝕜 N) = gaussH 𝕜 N from rfl, ← gbeEnsemble_hermLaw]
    unfold Ensemble.hermLaw
    rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (by fun_prop) (hm.prodMap hm)]
    rfl
  rw [hL, Ensemble.flowLaw, hR]

/-- Lemma 13.1 (a): `∑_i σ²_{t,ij} = κ_t⁻²`. -/
theorem Ensemble.sum_var_ouFlow {N : ℕ} (hN : 0 < N) {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    {M : Ensemble 𝕜 N} (hM : M.Assumptions ϑ δm δp C₀) {t : ℝ} (ht : 0 ≤ t) (j : Fin N) :
    ∑ i, (M.ouFlow (gbeEnsemble 𝕜 N) t).var i j = (Ensemble.kappaT 𝕜 N t)⁻¹ ^ 2 := by
  have hv : ∀ i, (M.ouFlow (gbeEnsemble 𝕜 N) t).var i j =
      Real.exp (-t) * M.var i j + ouS t * (gbeEnsemble 𝕜 N).var i j := fun i =>
    ensembles_varPair_ouFlow hϑ hM ht _
  simp_rw [hv]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hM.sumA j,
    ensembles_sum_var_gbe, Ensemble.kappaT, ensembles_inv_rpow_sq (ensembles_rT_mem ht).1, ouS]
  ring

/-- Lemma 13.1 (b): `ν̃^t ∈ 𝓔_N(ϑ̃, δ̃₋, δ̃₊, C̃₀)` for every `t ≥ 0`. -/
theorem Ensemble.tildeFlow_assumptions {N : ℕ} (hN : 3 ≤ N) {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    (hδm : 0 < δm) (hδp : 0 < δp) (hC₀ : 0 < C₀) {M : Ensemble 𝕜 N}
    (hM : M.Assumptions ϑ δm δp C₀) {t : ℝ} (ht : 0 ≤ t) :
    (M.tildeFlow t).Assumptions (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀) := by
  have hN0 : 0 < N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) / N ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hNr
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hr0, hr1⟩ := ensembles_rT_mem (𝕜 := 𝕜) (N := N) ht
  set r := (2 - betaF 𝕜) * ouS t / (betaF 𝕜 * N) with hr
  set κ := Ensemble.kappaT 𝕜 N t with hκ
  have hκ2 : κ ^ 2 = (1 + r)⁻¹ := ensembles_rpow_sq hr0
  have hκ0 : 0 < κ := ensembles_rpow_pos hr0
  have hs0 := ensembles_ouS_nonneg ht
  have hs1 := ensembles_ouS_le_one t
  have he : Real.exp (-t) = 1 - ouS t := by unfold ouS; ring
  have hcond := Ensemble.smul_conditions (M.ouFlow (gbeEnsemble 𝕜 N) t) κ
    (ensembles_meanZero_ouFlow hϑ hM t) (ensembles_diagReal_ouFlow hM.diagReal t)
    (ensembles_subexp_ouFlow hϑ hM ht)
  have hvar : ∀ i j, (M.tildeFlow t).var i j =
      κ ^ 2 * (Real.exp (-t) * M.var i j + ouS t * (gbeEnsemble 𝕜 N).var i j) := fun i j => by
    unfold Ensemble.tildeFlow Ensemble.var
    rw [Ensemble.varPair_smul, ensembles_varPair_ouFlow hϑ hM ht]
  refine ⟨hcond.1, hcond.2.1, ?_, ?_, ?_, hcond.2.2⟩
  · intro j
    have hs := Ensemble.sum_var_ouFlow hN0 hϑ hM ht j
    have hv : ∀ i, (M.tildeFlow t).var i j = κ ^ 2 * (M.ouFlow (gbeEnsemble 𝕜 N) t).var i j :=
      fun i => Ensemble.varPair_smul _ κ _
    simp_rw [hv]
    rw [← Finset.mul_sum, hs, ← mul_pow, mul_inv_cancel₀ hκ0.ne', one_pow]
  · intro v hv
    obtain ⟨hq1, hq2⟩ := hM.specB v hv
    set S := ∑ i, v i ^ 2 with hS
    set q := v ⬝ᵥ (M.varMatrix *ᵥ v) with hq
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hmat : (M.tildeFlow t).varMatrix =
        κ ^ 2 • (Real.exp (-t) • M.varMatrix + ouS t • (gbeEnsemble 𝕜 N).varMatrix) := by
      ext i j
      simp only [Ensemble.varMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
        smul_eq_mul, hvar]
    have hquad : v ⬝ᵥ ((M.tildeFlow t).varMatrix *ᵥ v) = (Real.exp (-t) * q + r * S) / (1 + r) := by
      rw [hmat, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul, ensembles_quad_gbe v hv,
        hκ2, smul_eq_mul, smul_eq_mul, smul_eq_mul, inv_mul_eq_div, hr]
      ring
    rw [hquad]
    set dm := min δm 1 with hdm
    set dp := min δp 1 with hdp
    have hdm0 : 0 < dm := lt_min hδm one_pos
    have hdp0 : 0 < dp := lt_min hδp one_pos
    have hdm1 : dm ≤ 1 := min_le_right _ _
    have hdp1 : dp ≤ 1 := min_le_right _ _
    have hdmδ : dm ≤ δm := min_le_left _ _
    have hdpδ : dp ≤ δp := min_le_left _ _
    have hq1' : (-1 + dm) * S ≤ q := le_trans (by nlinarith) hq1
    have hq2' : q ≤ (1 - dp) * S := le_trans hq2 (by nlinarith)
    have hpos : 0 < 1 + r := by linarith
    have hr3 : r ≤ 1 / 3 := hr1.trans hN1
    have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have heq1 := mul_le_mul_of_nonneg_left hq1' he0
    have heq2 := mul_le_mul_of_nonneg_left hq2' he0
    unfold tildeDelta
    rw [← hdm, ← hdp, le_div_iff₀ hpos, div_le_iff₀ hpos]
    rw [he] at heq1 heq2 ⊢
    constructor
    · nlinarith [mul_nonneg (mul_nonneg hdm0.le (by linarith : (0 : ℝ) ≤ 1 / 3 - r)) hS0,
        mul_nonneg (mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - dm)) hS0, mul_nonneg hr0 hS0]
    · nlinarith [mul_nonneg (mul_nonneg hdp0.le (by linarith : (0 : ℝ) ≤ 1 / 3 - r)) hS0,
        mul_nonneg (mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - dp)) hS0, mul_nonneg hr0 hS0]
  · intro i j
    rw [hvar]
    unfold tildeC
    have hC : C₀ / N ≤ max C₀ 2 / N := div_le_div_of_nonneg_right (le_max_left _ _) hNpos.le
    have hτ : (gbeEnsemble 𝕜 N).var i j ≤ max C₀ 2 / N := by
      rw [ensembles_var_gbe]
      have h1 := ensembles_rN_le (𝕜 := 𝕜) N
      have h2 : (2 : ℝ) / N ≤ max C₀ 2 / N := div_le_div_of_nonneg_right (le_max_right _ _) hNpos.le
      have h3 : (2 : ℝ) / N = 1 / N + 1 / N := by ring
      split_ifs <;> linarith [ensembles_rN_nonneg (𝕜 := 𝕜) N, one_div_nonneg.mpr hNpos.le]
    have hσ := (hM.boundC i j).trans hC
    have hX0 : 0 ≤ Real.exp (-t) * M.var i j + ouS t * (gbeEnsemble 𝕜 N).var i j := by
      have h1 : 0 ≤ M.var i j := integral_nonneg fun y => by positivity
      have h2 : 0 ≤ (gbeEnsemble 𝕜 N).var i j := integral_nonneg fun y => by positivity
      positivity
    have hX : Real.exp (-t) * M.var i j + ouS t * (gbeEnsemble 𝕜 N).var i j ≤ max C₀ 2 / N := by
      rw [he]
      nlinarith
    have hκ1 : κ ^ 2 ≤ 1 := by rw [hκ2]; exact inv_le_one_of_one_le₀ (by linarith)
    nlinarith

/-- Lemma 13.1 (b): `H̃_t = κ_t H_t` has the law of `H(x)` under `ℙ_{ν̃^t}`. -/
theorem Ensemble.tildeFlow_hermLaw {N : ℕ} (M : Ensemble 𝕜 N) (t : ℝ) :
    (M.tildeFlow t).hermLaw = (M.flowLaw t).map fun H => Ensemble.kappaT 𝕜 N t • H := by
  unfold Ensemble.tildeFlow
  rw [ensembles_hermLaw_smul, Ensemble.ouFlow_gbe_hermLaw]

/-- Lemma 13.1 (b), `t = ∞`: `Ṽ = κ_∞ V` is in the same class. -/
theorem gbeTilde_assumptions {N : ℕ} (hN : 3 ≤ N) {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    (hδm : 0 < δm) (hδp : 0 < δp) (hC₀ : 0 < C₀) :
    ((gbeEnsemble 𝕜 N).smul ((1 + (2 - betaF 𝕜) / (betaF 𝕜 * N)) ^ (-(1 / 2 : ℝ)))).Assumptions
      (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀) := by
  have hN0 : 0 < N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) / N ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hNr
  have hNpos : (0 : ℝ) < N := by linarith
  have hr0 := ensembles_rN_nonneg (𝕜 := 𝕜) N
  have hr1 := ensembles_rN_le (𝕜 := 𝕜) N
  set r := (2 - betaF 𝕜) / (betaF 𝕜 * N) with hr
  set c := (1 + r) ^ (-(1 / 2 : ℝ)) with hc
  have hc2 : c ^ 2 = (1 + r)⁻¹ := ensembles_rpow_sq hr0
  have hpos : 0 < 1 + r := by linarith
  set ϑb := min ϑ 1 with hϑb
  have hϑb0 : 0 < ϑb := lt_min hϑ one_pos
  have hϑb1 : ϑb ≤ 1 := min_le_right _ _
  have hD : (gbeEnsemble 𝕜 N).SubexpDecay (tildeTheta ϑ) := by
    intro p x hx
    refine (gbeEntryLaw_tail p (y := x) (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact ensembles_tail_gauss hϑb0 hϑb1 hx
  have hcond := Ensemble.smul_conditions (gbeEnsemble 𝕜 N) c ensembles_meanZero_gbe
    ensembles_diagReal_gbe hD
  have hvar : ∀ i j, ((gbeEnsemble 𝕜 N).smul c).var i j = c ^ 2 * (gbeEnsemble 𝕜 N).var i j :=
    fun i j => Ensemble.varPair_smul _ c _
  refine ⟨hcond.1, hcond.2.1, ?_, ?_, ?_, hcond.2.2⟩
  · intro j
    simp_rw [hvar]
    rw [← Finset.mul_sum, ensembles_sum_var_gbe, hc2, inv_mul_cancel₀ hpos.ne']
  · intro v hv
    set S := ∑ i, v i ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hmat : ((gbeEnsemble 𝕜 N).smul c).varMatrix = c ^ 2 • (gbeEnsemble 𝕜 N).varMatrix := by
      ext i j
      simp only [Ensemble.varMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hvar]
    rw [hmat, Matrix.smul_mulVec, dotProduct_smul, ensembles_quad_gbe v hv, hc2, smul_eq_mul,
      ← hr, inv_mul_eq_div]
    unfold tildeDelta
    have hdm0 : 0 < min δm 1 := lt_min hδm one_pos
    have hdp0 : 0 < min δp 1 := lt_min hδp one_pos
    have hdm1 : min δm 1 ≤ 1 := min_le_right _ _
    have hdp1 : min δp 1 ≤ 1 := min_le_right _ _
    have hr3 : r ≤ 1 / 3 := hr1.trans hN1
    rw [le_div_iff₀ hpos, div_le_iff₀ hpos]
    constructor
    · nlinarith [mul_nonneg hr0 hS0, mul_nonneg (mul_nonneg hr0 hS0) hdm0.le]
    · nlinarith [mul_nonneg (mul_nonneg hdp0.le (by linarith : (0 : ℝ) ≤ 1 / 3 - r)) hS0,
        mul_nonneg (mul_nonneg hdp0.le hr0) hS0]
  · intro i j
    rw [hvar]
    unfold tildeC
    have hτ : (gbeEnsemble 𝕜 N).var i j ≤ max C₀ 2 / N := by
      rw [ensembles_var_gbe]
      have h2 : (2 : ℝ) / N ≤ max C₀ 2 / N := div_le_div_of_nonneg_right (le_max_right _ _) hNpos.le
      have h3 : (2 : ℝ) / N = 1 / N + 1 / N := by ring
      split_ifs <;> linarith [one_div_nonneg.mpr hNpos.le]
    have hτ0 : 0 ≤ (gbeEnsemble 𝕜 N).var i j := integral_nonneg fun y => by positivity
    have hc1 : c ^ 2 ≤ 1 := by rw [hc2]; exact inv_le_one_of_one_le₀ (by linarith)
    nlinarith


/-! ### 3. Lemma 13.1 (c) and the moments of `H_0` (§18) -/

/-- Lemma 13.1 (c): `1 ≥ κ_t ≥ (1 + 1/N)^{-1/2}` and `0 ≤ κ_t⁻¹ - 1 ≤ 1/(2N)`. -/
theorem kappaT_bounds {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    Ensemble.kappaT 𝕜 N t ≤ 1 ∧ (1 + 1 / (N : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ Ensemble.kappaT 𝕜 N t ∧
      0 ≤ (Ensemble.kappaT 𝕜 N t)⁻¹ - 1 ∧ (Ensemble.kappaT 𝕜 N t)⁻¹ - 1 ≤ 1 / (2 * N) := by
  obtain ⟨h0, h1⟩ := ensembles_rT_mem (𝕜 := 𝕜) (N := N) ht
  set r := (2 - betaF 𝕜) * ouS t / (betaF 𝕜 * N) with hr
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : Ensemble.kappaT 𝕜 N t = (1 + r) ^ (-(1 / 2 : ℝ)) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hk]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  · rw [hk]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  · rw [hk, ensembles_inv_rpow h0, sub_nonneg]
    exact Real.one_le_sqrt.mpr (by linarith)
  · rw [hk, ensembles_inv_rpow h0, sub_le_iff_le_add]
    have h2 : r / 2 ≤ 1 / (2 * N) := by
      have e : (1 : ℝ) / (2 * N) = 1 / N / 2 := by ring
      rw [e]
      linarith
    have h3 : Real.sqrt (1 + r) ≤ 1 + r / 2 := by
      calc Real.sqrt (1 + r) ≤ Real.sqrt ((1 + r / 2) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])
        _ = 1 + r / 2 := Real.sqrt_sq (by linarith)
    linarith

/-- Lemma 13.1 (c): `𝔫_{c x}(e) = 𝔫_x(e/c)` for `c > 0`. -/
theorem empCount_smul {N : ℕ} (x : Fin N → ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ) :
    empCount (c • x) e = empCount x (e / c) := by
  unfold empCount
  congr 3
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply, smul_eq_mul]
  rw [le_div_iff₀ hc, mul_comm]

section Moments

variable {N : ℕ}

/-- `|h_ij| ≤ |x_{min(i,j), max(i,j)}|` for the entries of `H(x)`. -/
private lemma ensembles_norm_toMatrix_le (x : Pair N → 𝕜) (i j : Fin N) :
    ‖Rigidity.toMatrix x i j‖ ≤ ‖x (Pair.mk' i j)‖ := by
  simp only [Rigidity.toMatrix, Matrix.of_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_star]
  · rw [RCLike.norm_ofReal]
    exact RCLike.abs_re_le_norm _

/-- `|H(x)|² ≤ ∑_{i,j} |x_{min(i,j), max(i,j)}|²`. -/
private lemma ensembles_norm_sq_ofPair_le (x : Pair N → 𝕜) :
    ‖Herm.ofPair x‖ ^ 2 ≤ ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2 := by
  rw [Herm.norm_sq_eq, Herm.toMatrix_ofPair, Fintype.sum_prod_type]
  gcongr with i _ j _
  exact ensembles_norm_toMatrix_le x i j

end Moments

/-- §18, moments of `H_0`: `𝔼|H_0|^q < ∞` for every real `q ≥ 0`. -/
theorem Ensemble.integrable_norm_pow_hermLaw {N : ℕ} {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    {M : Ensemble 𝕜 N} (hM : M.Assumptions ϑ δm δp C₀) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun H : Herm 𝕜 N => ‖H‖ ^ q) M.hermLaw := by
  have hm := Herm.measurable_ofPair (𝕜 := 𝕜) N
  unfold Ensemble.hermLaw
  rw [integrable_map_measure (by fun_prop) hm.aemeasurable]
  set m : ℕ := ⌈q⌉₊ + 1 with hmdef
  have hm1 : (1 : ℝ) ≤ m := by rw [hmdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈q⌉₊]
  have hqm : q ≤ 2 * m := by
    have := Nat.le_ceil q
    rw [hmdef]; push_cast; linarith
  set C : ℝ := (Fintype.card (Fin N × Fin N) : ℝ) ^ ((m : ℝ) - 1) with hC
  have hC0 : 0 ≤ C := by positivity
  set g : (Pair N → 𝕜) → ℝ := fun x =>
    1 + C * ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ (2 * m) with hg
  have hgi : Integrable g M.prodLaw := by
    refine (integrable_const _).add ((integrable_finsetSum _ fun ij _ => ?_).const_mul C)
    exact integrable_comp_eval (μ := M.law) (f := fun y : 𝕜 => ‖y‖ ^ (2 * m))
      (Ensemble.Assumptions.integrable_norm_pow M hM hϑ _ (2 * m))
  refine hgi.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs]
  set h := ‖Herm.ofPair x‖ with hh
  have h0 : 0 ≤ h := norm_nonneg _
  rw [abs_of_nonneg (Real.rpow_nonneg h0 q)]
  have hsum := ensembles_norm_sq_ofPair_le x
  rw [← hh] at hsum
  -- `h^q ≤ 1 + (h²)^m`
  have h1 : h ^ q ≤ 1 + (h ^ 2) ^ m := by
    rcases le_or_gt h 1 with hle | hgt
    · have := Real.rpow_le_one h0 hle hq
      have : 0 ≤ (h ^ 2) ^ m := by positivity
      linarith
    · have : h ^ q ≤ h ^ ((2 * m : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hgt.le (by push_cast; linarith)
      rw [Real.rpow_natCast, pow_mul] at this
      linarith
  -- `(h²)^m ≤ C ∑ |x_ij|^{2m}`
  have h2 : (h ^ 2) ^ m ≤ C * ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ (2 * m) := by
    have hp := Real.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset (Fin N × Fin N))
      (fun ij => ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2) hm1
    simp only [abs_pow, abs_norm, Finset.card_univ] at hp
    have e1 : ∀ ij : Fin N × Fin N, (‖x (Pair.mk' ij.1 ij.2)‖ ^ 2) ^ (m : ℝ) =
        ‖x (Pair.mk' ij.1 ij.2)‖ ^ (2 * m) := fun ij => by
      rw [Real.rpow_natCast, ← pow_mul]
    simp_rw [e1] at hp
    calc (h ^ 2) ^ m = (h ^ 2) ^ (m : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2) ^ (m : ℝ) :=
          Real.rpow_le_rpow (by positivity) hsum (by linarith)
      _ ≤ C * ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ (2 * m) := hp
  simp only [hg]
  linarith

/-- §18, moments of `H_0`: `𝔼|H_0|² = ∑_{i,j} σ_ij² = N` by (A). -/
theorem Ensemble.integral_norm_sq_hermLaw {N : ℕ} {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    {M : Ensemble 𝕜 N} (hM : M.Assumptions ϑ δm δp C₀) :
    ∫ H, ‖H‖ ^ 2 ∂M.hermLaw = N := by
  have hm := Herm.measurable_ofPair (𝕜 := 𝕜) N
  unfold Ensemble.hermLaw
  rw [integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [Herm.norm_sq_eq, Herm.toMatrix_ofPair]
  have hint : ∀ i j : Fin N, Integrable (fun x : Pair N → 𝕜 => ‖Rigidity.toMatrix x i j‖ ^ 2)
      M.prodLaw := fun i j => by
    refine (integrable_comp_eval (μ := M.law) (f := fun y : 𝕜 => ‖y‖ ^ 2)
      (Ensemble.Assumptions.integrable_norm_pow M hM hϑ (Pair.mk' i j) 2)).mono'
      ?_ (ae_of_all _ fun x => ?_)
    · have : Continuous fun x : Pair N → 𝕜 => Rigidity.toMatrix x i j := by
        simp only [Rigidity.toMatrix, Matrix.of_apply]
        split_ifs
        · exact continuous_apply _
        · exact continuous_star.comp (continuous_apply _)
        · exact RCLike.continuous_ofReal.comp (RCLike.continuous_re.comp (continuous_apply _))
      exact (this.norm.pow 2).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (ensembles_norm_toMatrix_le x i j) 2
  have hent : ∀ i j : Fin N, ∫ x, ‖Rigidity.toMatrix x i j‖ ^ 2 ∂M.prodLaw = M.var i j := by
    intro i j
    have hae : (fun x : Pair N → 𝕜 => ‖Rigidity.toMatrix x i j‖ ^ 2) =ᵐ[M.prodLaw]
        fun x => ‖x (Pair.mk' i j)‖ ^ 2 := by
      by_cases hij : i = j
      · subst hij
        have hR : ∀ᵐ x ∂M.prodLaw, RCLike.im (x (Pair.mk' i i)) = 0 := by
          have := hM.diagReal i
          rw [← (measurePreserving_eval M.law (Pair.mk' i i)).map_eq] at this
          exact ae_of_ae_map (measurable_pi_apply _).aemeasurable this
        filter_upwards [hR] with x hx
        simp only [Rigidity.toMatrix, Matrix.of_apply, lt_irrefl, ite_false,
          RCLike.norm_ofReal, sq_abs]
        rw [RCLike.norm_sq_eq_def, hx]
        ring
      · refine ae_of_all _ fun x => ?_
        simp only
        rcases lt_or_gt_of_ne hij with h | h
        · simp [Rigidity.toMatrix, h]
        · simp [Rigidity.toMatrix, h, not_lt.mpr h.le]
    rw [integral_congr_ae hae]
    unfold Ensemble.prodLaw
    rw [integral_comp_eval (μ := M.law) (f := fun y : 𝕜 => ‖y‖ ^ 2) (by fun_prop)]
    rfl
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, hent]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => hM.sumA j]
  simp

end Rigidity
