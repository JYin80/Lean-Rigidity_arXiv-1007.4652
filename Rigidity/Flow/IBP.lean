import Rigidity.Flow.Chamber

/-!
# Integration by parts on the Weyl chamber against the Gaussian β-ensemble weight

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

With `Δ(x) = ∏_{i<j} (x_j - x_i)` (`vandermonde`), the weight `w = Δ^β e^{-βN|x|²/4}`
(`gbeWeight`) and the measure `μ* = Z_β⁻¹ w 𝟙_Σ dx` (`muStar`) of (16.1), this file
proves the divergence identity (16.3), `div (w ∇φ) = βN w Lφ` on the open Weyl chamber
(`divergence_weight_grad`), and the integration by parts formula of Corollary 16.2, (16.4),
`∫ k Lφ dμ* = -(βN)⁻¹ ∫ ∇k·∇φ dμ*` (`integral_mul_dysonGen_muStar`), obtained from the divergence
theorem of Lemma 16.1 (`integral_divergence_chamber`) applied to the field `k w ∇φ`, which vanishes
on the walls of the chamber because `w` does.

The weight is `Δ ^ β` with the real power, so it is `C¹` on `ℝ^N` for `β ≥ 1`; on the chamber it
agrees with the polynomial-times-Gaussian weight of NP for `β ∈ {1, 2}`. The theorem of
Corollary 16.2 holds for every real `β ≥ 1`. Normalisation of `μ*` is not needed there: if
`Z_β ∈ {0, ∞}` then `μ* = 0` and both sides vanish.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The Vandermonde product `Δ(x) = ∏_{i<j} (x_j - x_i)` (§16). -/
def vandermonde {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∏ p : {q : Fin N × Fin N // q.1 < q.2}, (x p.1.2 - x p.1.1)

/-- The weight `w(x) = Δ(x)^β e^{-βN|x|²/4}` (16.1). -/
noncomputable def gbeWeight (β : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  vandermonde x ^ β * Real.exp (-(β * N / 4) * ∑ i, x i ^ 2)

/-- `μ* = Z_β⁻¹ w 𝟙_Σ dx` (16.1). -/
noncomputable def muStar (β : ℝ) (N : ℕ) : Measure (Fin N → ℝ) :=
  (∫⁻ x in chamber N, ENNReal.ofReal (gbeWeight β N x))⁻¹ •
    (volume.restrict (chamber N)).withDensity fun x => ENNReal.ofReal (gbeWeight β N x)

private lemma vandermonde_contDiff {N : ℕ} : ContDiff ℝ 1 (vandermonde (N := N)) := by
  unfold vandermonde
  exact contDiff_prod (fun p _ => by fun_prop)

private lemma gbeWeight_contDiff {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) : ContDiff ℝ 1 (gbeWeight β N) := by
  unfold gbeWeight
  have h2 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun x : Fin N → ℝ => vandermonde x ^ β) :=
    ContDiff.rpow_const_of_le (m := 1) (by simpa using vandermonde_contDiff) (by simpa using hβ)
  have h3 : ContDiff ℝ 1 (fun x : Fin N → ℝ => vandermonde x ^ β) := by simpa using h2
  exact h3.mul (by fun_prop)

private lemma vandermonde_pos {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    0 < vandermonde x := by
  unfold vandermonde
  exact Finset.prod_pos fun p _ => sub_pos.2 (hx p.2)

private lemma gbeWeight_pos {N : ℕ} {β : ℝ} {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    0 < gbeWeight β N x :=
  mul_pos (Real.rpow_pos_of_pos (vandermonde_pos hx) β) (Real.exp_pos _)

private lemma vandermonde_eq_zero_of_wall {N : ℕ} {x : Fin N → ℝ}
    (hx : x ∈ closure (chamber N) \ chamber N) : vandermonde x = 0 := by
  rw [closure_chamber] at hx
  obtain ⟨hmono, hnot⟩ := hx
  by_contra hV
  apply hnot
  intro a b hab
  have hne : x b - x a ≠ 0 := by
    have := (Finset.prod_ne_zero_iff.1 hV) ⟨(a, b), hab⟩ (Finset.mem_univ _)
    simpa using this
  exact lt_of_le_of_ne (hmono hab.le) (fun h => hne (by rw [h]; ring))

private lemma gbeWeight_eq_zero_of_wall {N : ℕ} {β : ℝ} (hβ : 0 < β) {x : Fin N → ℝ}
    (hx : x ∈ closure (chamber N) \ chamber N) : gbeWeight β N x = 0 := by
  unfold gbeWeight
  rw [vandermonde_eq_zero_of_wall hx, Real.zero_rpow hβ.ne', zero_mul]

private lemma sum_pairs_inv {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      (x p.1.2 - x p.1.1)⁻¹ * ((if p.1.2 = i then (1 : ℝ) else 0) - (if p.1.1 = i then 1 else 0)) =
    ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun q : Fin N × Fin N => q.1 < q.2) (by simp)
    (fun q => (x q.2 - x q.1)⁻¹ * ((if q.2 = i then (1 : ℝ) else 0) - (if q.1 = i then 1 else 0)))]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hpt : ∀ a b : Fin N, (if a < b then (x b - x a)⁻¹ *
        ((if b = i then (1 : ℝ) else 0) - (if a = i then 1 else 0)) else 0) =
      (if b = i then (if a < b then (x b - x a)⁻¹ else 0) else 0) -
      (if a = i then (if a < b then (x b - x a)⁻¹ else 0) else 0) := by
    intro a b
    split_ifs <;> simp_all
  simp only [hpt, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a = i then (if a < b then (x b - x a)⁻¹ else 0) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have herase : ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ =
      ∑ j, (if j < i then (x i - x j)⁻¹ else 0) + ∑ j, (if i < j then (x i - x j)⁻¹ else 0) := by
    rw [← Finset.filter_ne', Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy j i with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  rw [herase, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [show x i - x j = -(x j - x i) by ring, inv_neg]
  · simp

private lemma hasFDerivAt_sumSq {N : ℕ} (x : Fin N → ℝ) :
    HasFDerivAt (fun y : Fin N → ℝ => ∑ i, y i ^ 2)
      (∑ i, (2 * x i) • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) x := by
  have hsq : ∀ i : Fin N, HasFDerivAt (fun y : Fin N → ℝ => y i ^ 2)
      ((2 * x i) • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) x := fun i => by
    have := (hasFDerivAt_apply (𝕜 := ℝ) i x).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) i x)
    simpa [pow_two, two_mul, add_smul] using this
  exact HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hsq i)

private lemma gbeWeight_hasFDerivAt {N : ℕ} (β : ℝ) {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    ∃ L : (Fin N → ℝ) →L[ℝ] ℝ, HasFDerivAt (gbeWeight β N) L x ∧ ∀ i : Fin N,
      L (Pi.single i 1) = gbeWeight β N x *
        (β * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ - β * N / 2 * x i) := by
  have hlog : ∀ p : {q : Fin N × Fin N // q.1 < q.2},
      HasFDerivAt (fun y : Fin N → ℝ => Real.log (y p.1.2 - y p.1.1))
        ((x p.1.2 - x p.1.1)⁻¹ •
          ((ContinuousLinearMap.proj p.1.2 : (Fin N → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj p.1.1))
        x := fun p =>
    ((hasFDerivAt_apply (𝕜 := ℝ) p.1.2 x).sub (hasFDerivAt_apply (𝕜 := ℝ) p.1.1 x)).log
      (ne_of_gt (sub_pos.2 (hx p.2)))
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun p _ => hlog p)
  have hsumsq := hasFDerivAt_sumSq x
  have hG := (hsum.const_mul β).add (hsumsq.const_mul (-(β * N / 4)))
  have hF := hG.exp
  have heq : gbeWeight β N =ᶠ[nhds x] fun y => Real.exp (β * ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      Real.log (y p.1.2 - y p.1.1) + -(β * N / 4) * ∑ i, y i ^ 2) := by
    filter_upwards [(isOpen_chamber N).mem_nhds hx] with y hy
    unfold gbeWeight
    rw [Real.rpow_def_of_pos (vandermonde_pos hy), ← Real.exp_add]
    congr 1
    unfold vandermonde
    rw [Real.log_prod (fun p _ => (sub_pos.2 (hy p.2)).ne')]
    ring
  refine ⟨_, hF.congr_of_eventuallyEq heq, fun i => ?_⟩
  rw [heq.eq_of_nhds]
  simp only [smul_apply, add_apply,
    sum_apply, sub_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, smul_eq_mul]
  rw [sum_pairs_inv x i]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Pi.add_apply]
  ring

private lemma pderiv_contDiff {N : ℕ} {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (i : Fin N) :
    ContDiff ℝ 1 (pderiv i φ) := by
  have h : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact h.clm_apply contDiff_const

private lemma fderiv_apply_eq {N : ℕ} {Z : (Fin N → ℝ) → Fin N → ℝ} {x : Fin N → ℝ}
    (hZ : ∀ j, DifferentiableAt ℝ (fun y => Z y j) x) (v : Fin N → ℝ) (i : Fin N) :
    fderiv ℝ Z x v i = fderiv ℝ (fun y => Z y i) x v := by
  have := fderiv_pi (φ := fun j y => Z y j) (x := x) hZ
  change fderiv ℝ (fun y j => Z y j) x v i = _
  rw [this]
  simp

/-- Identity (16.3): on `Σ_N` the divergence of the weighted gradient field `w ∇φ`, for `φ ∈ C²`,
is `div (w ∇φ) = βN w Lφ`. -/
theorem divergence_weight_grad {N : ℕ} {β : ℝ} (hβ : 0 < β) {φ : (Fin N → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    divergence (fun y i => gbeWeight β N y * pderiv i φ y) x =
      β * N * gbeWeight β N x * dysonGen β N φ x := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [divergence, dysonGen]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hβ0 : β ≠ 0 := hβ.ne'
  obtain ⟨L, hL, hLi⟩ := gbeWeight_hasFDerivAt β hx
  have hwd : DifferentiableAt ℝ (gbeWeight β N) x := hL.differentiableAt
  have hdφ : ∀ i, DifferentiableAt ℝ (pderiv i φ) x := fun i =>
    (pderiv_contDiff hφ i).differentiable (by norm_num) x
  have hdc : ∀ j : Fin N, DifferentiableAt ℝ
      (fun y => gbeWeight β N y * pderiv j φ y) x := fun j => hwd.mul (hdφ j)
  have hcomp : ∀ i : Fin N, fderiv ℝ (fun y i => gbeWeight β N y * pderiv i φ y) x
      (Pi.single i 1) i = gbeWeight β N x * pderiv i (pderiv i φ) x +
        pderiv i φ x * (gbeWeight β N x *
          (β * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ - β * N / 2 * x i)) := by
    intro i
    rw [fderiv_apply_eq (Z := fun y i => gbeWeight β N y * pderiv i φ y) hdc]
    rw [(hL.fun_mul (hdφ i).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, hLi]
    rfl
  unfold divergence
  simp only [hcomp]
  unfold dysonGen
  have h1 : β * N * gbeWeight β N x * ((β * N)⁻¹ * ∑ i, pderiv i (pderiv i φ) x) =
      ∑ i, gbeWeight β N x * pderiv i (pderiv i φ) x := by
    rw [← Finset.mul_sum]
    field_simp
  have h2 : β * N * gbeWeight β N x * ∑ i, (-x i / 2 + (N : ℝ)⁻¹ *
      ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) * pderiv i φ x =
      ∑ i, pderiv i φ x * (gbeWeight β N x *
        (β * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ - β * N / 2 * x i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  rw [mul_add, h1, h2, Finset.sum_add_distrib]

private lemma divergence_mul_field {N : ℕ} {k : (Fin N → ℝ) → ℝ}
    {Z : (Fin N → ℝ) → Fin N → ℝ} {x : Fin N → ℝ} (hk : DifferentiableAt ℝ k x)
    (hZ : ∀ j, DifferentiableAt ℝ (fun y => Z y j) x) :
    divergence (fun y i => k y * Z y i) x =
      k x * divergence Z x + ∑ i, pderiv i k x * Z x i := by
  have hc : ∀ j, DifferentiableAt ℝ (fun y => k y * Z y j) x := fun j => hk.mul (hZ j)
  unfold divergence
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_apply_eq (Z := fun y i => k y * Z y i) hc, fderiv_apply_eq hZ,
    (hk.hasFDerivAt.fun_mul (hZ i).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, pderiv]
  ring

/-- The normalising constant `Z_β = ∫_Σ w`. -/
private noncomputable def zStar (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in chamber N, ENNReal.ofReal (gbeWeight β N x)

/-- The unnormalised measure `w 𝟙_Σ dx`. -/
private noncomputable def nuStar (β : ℝ) (N : ℕ) : Measure (Fin N → ℝ) :=
  (volume.restrict (chamber N)).withDensity fun x => ENNReal.ofReal (gbeWeight β N x)

private lemma muStar_eq (β : ℝ) (N : ℕ) : muStar β N = (zStar β N)⁻¹ • nuStar β N := rfl

private lemma measurable_ofReal_gbeWeight {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) :
    Measurable fun x : Fin N → ℝ => ENNReal.ofReal (gbeWeight β N x) :=
  ENNReal.measurable_ofReal.comp (gbeWeight_contDiff hβ).continuous.measurable

private lemma integrable_nuStar_iff {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) (g : (Fin N → ℝ) → ℝ) :
    Integrable g (nuStar β N) ↔ IntegrableOn (fun x => gbeWeight β N x * g x) (chamber N) := by
  unfold nuStar
  rw [integrable_withDensity_iff_integrable_smul' (measurable_ofReal_gbeWeight hβ)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem (isOpen_chamber N).measurableSet] with y hy
  rw [ENNReal.toReal_ofReal (gbeWeight_pos hy).le, smul_eq_mul]

private lemma integral_nuStar {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) (g : (Fin N → ℝ) → ℝ) :
    ∫ x, g x ∂nuStar β N = ∫ x in chamber N, gbeWeight β N x * g x := by
  unfold nuStar
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_ofReal_gbeWeight hβ)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (isOpen_chamber N).measurableSet] with y hy
  rw [ENNReal.toReal_ofReal (gbeWeight_pos hy).le, smul_eq_mul]

private lemma integrable_muStar_iff {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) (hZ0 : zStar β N ≠ 0)
    (hZt : zStar β N ≠ ⊤) (g : (Fin N → ℝ) → ℝ) :
    Integrable g (muStar β N) ↔ IntegrableOn (fun x => gbeWeight β N x * g x) (chamber N) := by
  rw [muStar_eq, integrable_smul_measure (ENNReal.inv_ne_zero.2 hZt) (ENNReal.inv_ne_top.2 hZ0)]
  exact integrable_nuStar_iff hβ g

private lemma integral_muStar {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) (g : (Fin N → ℝ) → ℝ) :
    ∫ x, g x ∂muStar β N =
      ((zStar β N)⁻¹).toReal * ∫ x in chamber N, gbeWeight β N x * g x := by
  rw [muStar_eq, integral_smul_measure, integral_nuStar hβ, smul_eq_mul]

/-- On `Σ_N`, `div (k w ∇φ) = βN k w Lφ + w ∇k·∇φ`. -/
private lemma divergence_k_weight_grad {N : ℕ} {β : ℝ} (hβ : 0 < β) {φ k : (Fin N → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hk : ContDiff ℝ 1 k) {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    divergence (fun y i => k y * (gbeWeight β N y * pderiv i φ y)) x =
      β * N * (gbeWeight β N x * (k x * dysonGen β N φ x)) +
        gbeWeight β N x * ∑ i, pderiv i k x * pderiv i φ x := by
  obtain ⟨L, hL, -⟩ := gbeWeight_hasFDerivAt β hx
  have hwd : DifferentiableAt ℝ (gbeWeight β N) x := hL.differentiableAt
  have hdφ : ∀ i, DifferentiableAt ℝ (pderiv i φ) x := fun i =>
    (pderiv_contDiff hφ i).differentiable (by norm_num) x
  have hZ : ∀ j : Fin N, DifferentiableAt ℝ
      (fun y => gbeWeight β N y * pderiv j φ y) x := fun j => hwd.mul (hdφ j)
  rw [divergence_mul_field (Z := fun y i => gbeWeight β N y * pderiv i φ y)
    (hk.differentiable (by norm_num) x) hZ, divergence_weight_grad hβ hφ hx, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

private lemma abs_sum_le_card_mul_sqrt {N : ℕ} (a : Fin N → ℝ) :
    ∑ i, |a i| ≤ N * Real.sqrt (∑ i, a i ^ 2) := by
  have hb : ∀ i, |a i| ≤ Real.sqrt (∑ j, a j ^ 2) := fun i =>
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => a j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i))
  calc ∑ i, |a i| ≤ ∑ _i : Fin N, Real.sqrt (∑ j, a j ^ 2) := Finset.sum_le_sum fun i _ => hb i
    _ = N * Real.sqrt (∑ j, a j ^ 2) := by simp

/-- Corollary 16.2 (16.4): `∫ k Lφ dμ* = -(βN)⁻¹ ∫ ∇k·∇φ dμ*`. -/
theorem integral_mul_dysonGen_muStar {N : ℕ} {β : ℝ} (hβ : 1 ≤ β) {φ k : (Fin N → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hk : ContDiff ℝ 1 k)
    (h1 : Integrable (fun x => k x * Real.sqrt (∑ i, pderiv i φ x ^ 2)) (muStar β N))
    (h2 : Integrable (fun x => ∑ i, pderiv i k x * pderiv i φ x) (muStar β N))
    (h3 : Integrable (fun x => k x * dysonGen β N φ x) (muStar β N)) :
    ∫ x, k x * dysonGen β N φ x ∂muStar β N =
      -(β * N)⁻¹ * ∫ x, ∑ i, pderiv i k x * pderiv i φ x ∂muStar β N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [dysonGen]
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hmeas : MeasurableSet (chamber N) := (isOpen_chamber N).measurableSet
  by_cases hZ0 : zStar β N = 0
  · have hν : nuStar β N = 0 := by
      unfold nuStar
      have hae : (fun x => ENNReal.ofReal (gbeWeight β N x)) =ᵐ[volume.restrict (chamber N)] 0 :=
        (lintegral_eq_zero_iff (measurable_ofReal_gbeWeight hβ)).1 hZ0
      rw [withDensity_congr_ae hae, withDensity_zero]
    have : muStar β N = 0 := by rw [muStar_eq, hν, smul_zero]
    rw [this]
    simp
  by_cases hZt : zStar β N = ⊤
  · have : muStar β N = 0 := by rw [muStar_eq, hZt, ENNReal.inv_top, zero_smul]
    rw [this]
    simp
  have hint := integrable_muStar_iff hβ hZ0 hZt
  have hmu := integral_muStar (N := N) hβ
  have h1' := (hint _).1 h1
  have h2' := (hint _).1 h2
  have h3' := (hint _).1 h3
  -- the field `Y = k w ∇φ`
  set Y : (Fin N → ℝ) → Fin N → ℝ := fun y i => k y * (gbeWeight β N y * pderiv i φ y) with hYdef
  have hY : ContDiff ℝ 1 Y := contDiff_pi.2 fun i =>
    hk.mul ((gbeWeight_contDiff hβ).mul (pderiv_contDiff hφ i))
  have hwall : ∀ y ∈ closure (chamber N) \ chamber N, Y y = 0 := fun y hy => by
    funext i
    simp [hYdef, gbeWeight_eq_zero_of_wall hβ0 hy]
  have hdiv_eq : ∀ y ∈ chamber N, divergence Y y =
      β * N * (gbeWeight β N y * (k y * dysonGen β N φ y)) +
        gbeWeight β N y * ∑ i, pderiv i k y * pderiv i φ y := fun y hy =>
    divergence_k_weight_grad hβ0 hφ hk hy
  have hdiv0 : IntegrableOn (fun y => β * N * (gbeWeight β N y * (k y * dysonGen β N φ y)) +
      gbeWeight β N y * ∑ i, pderiv i k y * pderiv i φ y) (chamber N) :=
    (h3'.const_mul (β * N)).add h2'
  have hdiv : IntegrableOn (divergence Y) (chamber N) :=
    hdiv0.congr_fun (fun y hy => (hdiv_eq y hy).symm) hmeas
  have hsum : IntegrableOn (fun x => ∑ i, |Y x i|) (chamber N) := by
    refine Integrable.mono' (h1'.norm.const_mul (N : ℝ)) ?_ ?_
    · have hYc : Continuous Y := hY.continuous
      have hc : Continuous fun x => ∑ i, |Y x i| := by fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hmeas] with y hy
      have hw := gbeWeight_pos (β := β) hy
      have hle := abs_sum_le_card_mul_sqrt (fun i => pderiv i φ y)
      have hsq : 0 ≤ Real.sqrt (∑ i, pderiv i φ y ^ 2) := Real.sqrt_nonneg _
      have hrw : ∑ i, |Y y i| = |k y| * gbeWeight β N y * ∑ i, |pderiv i φ y| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hYdef, abs_mul, abs_of_pos hw]
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _), hrw,
        Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, abs_of_nonneg hsq]
      calc |k y| * gbeWeight β N y * ∑ i, |pderiv i φ y|
          ≤ |k y| * gbeWeight β N y * (N * Real.sqrt (∑ i, pderiv i φ y ^ 2)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = N * (gbeWeight β N y * (|k y| * Real.sqrt (∑ i, pderiv i φ y ^ 2))) := by ring
  have hzero := integral_divergence_chamber hY hwall hsum hdiv
  rw [setIntegral_congr_fun hmeas hdiv_eq, integral_add (h3'.const_mul (β * N)) h2',
    integral_const_mul] at hzero
  have hmain : ∫ x in chamber N, gbeWeight β N x * (k x * dysonGen β N φ x) =
      -(β * N)⁻¹ * ∫ x in chamber N, gbeWeight β N x * ∑ i, pderiv i k x * pderiv i φ x := by
    have key : ∀ A B : ℝ, β * N * A + B = 0 → A = -(β * N)⁻¹ * B := by
      intro A B h
      have hβN : β * N ≠ 0 := mul_ne_zero hβ0.ne' hN0
      have : A = -B / (β * N) := by
        field_simp
        linarith
      rw [this]
      ring
    exact key _ _ hzero
  rw [hmu, hmu, hmain]
  ring

end Rigidity
