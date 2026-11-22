module

public import Rigidity.Flow.Chamber
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.Givens
public import Rigidity.Flow.Herm
public import Rigidity.Flow.IBP
public import Rigidity.Flow.Invariant
public import Rigidity.Flow.MehlerSmooth

@[expose] public section

/-!
# The joint eigenvalue density of the Gaussian β-ensembles

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file proves Theorem 16.3: the law `μ = λ_* 𝐆` of the ordered eigenvalues of
`𝐆 = 𝐆_{N,β}` is the measure `μ* = Z_β⁻¹ Δ^β e^{-βN|x|²/4} 𝟙_Σ dx` of (16.1)
(`gbeLaw_eq_muStar`), and for every initial law `ρ` and `t > 0` the eigenvalue law `ν_t` of
`H_t` is absolutely continuous with respect to `μ` and does not charge `∂Σ = cl Σ \ Σ`
(`eigFlow_ac`).

The proof follows Theorem 16.3. For bounded continuous `θ` on `ℝ^N`, `Φ = θ ∘ λ` is invariant,
and so is `Φ_u = T_u Φ` (Lemma 15.1); `φ_u = Φ_u ∘ diag` satisfies `∂_u φ_u = L φ_u` on `Σ`,
(16.8) (Lemma 14.3 and Lemma 15.2), the first derivatives of `(u, H) ↦ Φ_u(H)` are bounded by
`C (1 + |H|²)` for `u ≥ u₁ > 0` (a bound of the type (16.7), from Lemma 14.F), so
`m(u) = ∫ φ_u dμ*` has derivative `∫ L φ_u dμ* = 0` by Corollary 16.2 with `k ≡ 1`. The limits
of `m` as `u ↓ 0` and `u → ∞` (Lemma 14.3) are `∫ θ dμ*` and `∫ θ dμ`.

Here `β = finrank ℝ 𝕜 ∈ {1, 2}`, and the statement also covers the trivial case `N = 0`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-! ### `diag : ℝ^N → 𝓗` as a continuous linear map -/

section Diag

variable {N : ℕ}

private theorem jointDensity_diag_add (x y : Fin N → ℝ) :
    Herm.diag (𝕜 := 𝕜) (x + y) = Herm.diag x + Herm.diag y := by
  apply Subtype.ext
  ext q
  obtain ⟨i, j, k⟩ := q
  change (Herm.diag (𝕜 := 𝕜) (x + y)).1 (i, j, k) =
    (Herm.diag (𝕜 := 𝕜) x).1 (i, j, k) + (Herm.diag (𝕜 := 𝕜) y).1 (i, j, k)
  simp only [Herm.diag, Herm.ofPair, Rigidity.toMatrix, Matrix.of_apply]
  split_ifs <;> simp

private theorem jointDensity_diag_smul (c : ℝ) (x : Fin N → ℝ) :
    Herm.diag (𝕜 := 𝕜) (c • x) = c • Herm.diag x := by
  apply Subtype.ext
  ext q
  obtain ⟨i, j, k⟩ := q
  change (Herm.diag (𝕜 := 𝕜) (c • x)).1 (i, j, k) = c * (Herm.diag (𝕜 := 𝕜) x).1 (i, j, k)
  simp only [Herm.diag, Herm.ofPair, Rigidity.toMatrix, Matrix.of_apply]
  split_ifs <;> simp

/-- `x ↦ diag x` as a continuous real-linear map `ℝ^N → 𝓗`. -/
private noncomputable def jointDensity_diagCLM : (Fin N → ℝ) →L[ℝ] Herm 𝕜 N :=
  LinearMap.toContinuousLinearMap
    { toFun := Herm.diag
      map_add' := jointDensity_diag_add
      map_smul' := jointDensity_diag_smul }

private theorem jointDensity_contDiff_diag {n : WithTop ℕ∞} :
    ContDiff ℝ n (Herm.diag (𝕜 := 𝕜) (N := N)) :=
  (jointDensity_diagCLM (𝕜 := 𝕜) (N := N)).contDiff

/-- `|diag x|² = ∑ x_i²` on the closed chamber. -/
private theorem jointDensity_norm_sq_diag {x : Fin N → ℝ} (hx : Monotone x) :
    ‖Herm.diag (𝕜 := 𝕜) x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [← sum_sq_eigVec, eigVec_diag hx]

end Diag

/-! ### The weight `w` and the measure `μ*` of (16.1) -/

section Weight

variable {N : ℕ}

private theorem jointDensity_one_le_betaF : 1 ≤ betaF 𝕜 := by
  unfold betaF
  exact_mod_cast Module.finrank_pos (R := ℝ) (M := 𝕜)

private theorem jointDensity_betaF_le_two : betaF 𝕜 ≤ 2 := by
  unfold betaF
  exact_mod_cast RCLike.finrank_le_two 𝕜

/-- `Δ(x)² ≤ (2|x|²)^P`, with `P` the number of pairs `i < j` (§16, before (16.2)). -/
private theorem jointDensity_vandermonde_sq_le (x : Fin N → ℝ) :
    vandermonde x ^ 2 ≤
      (2 * ∑ i, x i ^ 2) ^ Fintype.card {q : Fin N × Fin N // q.1 < q.2} := by
  unfold vandermonde
  rw [← Finset.prod_pow, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun p _ => sq_nonneg _) fun p _ => ?_
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  have h1 : x p.1.1 ^ 2 + x p.1.2 ^ 2 ≤ ∑ i, x i ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => x i ^ 2)
      (Finset.subset_univ {p.1.1, p.1.2}) fun i _ _ => sq_nonneg _
    rwa [Finset.sum_pair hne] at this
  nlinarith [sq_nonneg (x p.1.2 + x p.1.1)]

private theorem jointDensity_continuous_gbeWeight {β : ℝ} (hβ : 0 ≤ β) :
    Continuous (gbeWeight β N) := by
  unfold gbeWeight
  have hV : Continuous (vandermonde (N := N)) := by
    unfold vandermonde
    fun_prop
  exact (hV.rpow_const fun _ => Or.inr hβ).mul (by fun_prop)

private theorem jointDensity_gbeWeight_pos {β : ℝ} {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    0 < gbeWeight β N x := by
  unfold gbeWeight
  have hV : 0 < vandermonde x := Finset.prod_pos fun p _ => sub_pos.2 (hx p.2)
  exact mul_pos (Real.rpow_pos_of_pos hV β) (Real.exp_pos _)

/-- On `Σ`, `(1 + |x|²) w(x) ≤ K e^{-|x|²/8}` (§16, before (16.2)). -/
private theorem jointDensity_weight_le :
    ∃ K : ℝ, ∀ x ∈ chamber N,
      (1 + ∑ i, x i ^ 2) * gbeWeight (betaF 𝕜) N x ≤
        K * Real.exp (-(1 / 8) * ∑ i, x i ^ 2) := by
  set P := Fintype.card {q : Fin N × Fin N // q.1 < q.2}
  refine ⟨2 * 16 ^ (P + 1) * (P + 1).factorial * Real.exp (1 / 16), fun x hx => ?_⟩
  set S := ∑ i, x i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV : 0 < vandermonde x := Finset.prod_pos fun p _ => sub_pos.2 (hx p.2)
  have hβ1 := jointDensity_one_le_betaF (𝕜 := 𝕜)
  have h1 : vandermonde x ^ betaF 𝕜 ≤ 1 + vandermonde x ^ 2 := by
    rcases le_total (vandermonde x) 1 with h | h
    · have := Real.rpow_le_one hV.le h (by linarith)
      nlinarith [sq_nonneg (vandermonde x)]
    · have := Real.rpow_le_rpow_of_exponent_le h (jointDensity_betaF_le_two (𝕜 := 𝕜))
      rw [Real.rpow_two] at this
      linarith
  have h2 := jointDensity_vandermonde_sq_le x
  have h3 : Real.exp (-(betaF 𝕜 * N / 4) * S) ≤ Real.exp (-(1 / 4) * S) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [hS]
    · apply Real.exp_le_exp.2
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (1 : ℝ) ≤ betaF 𝕜 * N := by nlinarith
      nlinarith
  set τ := 1 + 2 * S with hτdef
  have hτ : 0 ≤ τ := by positivity
  have h4 : (1 + S) * (1 + (2 * S) ^ P) ≤ 2 * τ ^ (P + 1) := by
    have a1 : 1 + S ≤ τ := by linarith
    have a2 : 1 + (2 * S) ^ P ≤ 2 * τ ^ P := by
      have : (1 : ℝ) ≤ τ ^ P := one_le_pow₀ (by linarith)
      have : (2 * S) ^ P ≤ τ ^ P := pow_le_pow_left₀ (by positivity) (by linarith) P
      linarith
    calc (1 + S) * (1 + (2 * S) ^ P) ≤ τ * (2 * τ ^ P) :=
          mul_le_mul a1 a2 (by positivity) hτ
      _ = 2 * τ ^ (P + 1) := by ring
  have h5 : τ ^ (P + 1) ≤
      16 ^ (P + 1) * (P + 1).factorial * Real.exp (1 / 16) * Real.exp (S / 8) := by
    have := Real.pow_div_factorial_le_exp (τ / 16) (by positivity) (P + 1)
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at this
    have e : Real.exp (τ / 16) = Real.exp (1 / 16) * Real.exp (S / 8) := by
      rw [← Real.exp_add]
      congr 1
      rw [hτdef]
      ring
    rw [e] at this
    linarith
  have hw : gbeWeight (betaF 𝕜) N x ≤ (1 + (2 * S) ^ P) * Real.exp (-(1 / 4) * S) := by
    unfold gbeWeight
    exact mul_le_mul (h1.trans (by linarith)) h3 (Real.exp_pos _).le (by positivity)
  have e2 : Real.exp (S / 8) * Real.exp (-(1 / 4) * S) = Real.exp (-(1 / 8) * S) := by
    rw [← Real.exp_add]
    ring_nf
  calc (1 + S) * gbeWeight (betaF 𝕜) N x
      ≤ (1 + S) * ((1 + (2 * S) ^ P) * Real.exp (-(1 / 4) * S)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = ((1 + S) * (1 + (2 * S) ^ P)) * Real.exp (-(1 / 4) * S) := by ring
    _ ≤ (2 * (16 ^ (P + 1) * (P + 1).factorial * Real.exp (1 / 16) * Real.exp (S / 8))) *
          Real.exp (-(1 / 4) * S) := by
        exact mul_le_mul_of_nonneg_right (by linarith [h4, h5]) (Real.exp_pos _).le
    _ = 2 * 16 ^ (P + 1) * (P + 1).factorial * Real.exp (1 / 16) *
          (Real.exp (S / 8) * Real.exp (-(1 / 4) * S)) := by ring
    _ = _ := by rw [e2]

/-- (16.2) with `m = 2`: `(1 + |x|²) w ∈ L¹(Σ)`. -/
private theorem jointDensity_integrableOn :
    IntegrableOn (fun x : Fin N → ℝ => (1 + ∑ i, x i ^ 2) * gbeWeight (betaF 𝕜) N x)
      (chamber N) := by
  obtain ⟨K, hK⟩ := jointDensity_weight_le (𝕜 := 𝕜) (N := N)
  have hg : Integrable (fun x : Fin N → ℝ => K * ∏ i, Real.exp (-(1 / 8) * x i ^ 2)) := by
    refine Integrable.const_mul ?_ K
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ t => Real.exp (-(1 / 8) * t ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by norm_num)
  have hc : Continuous fun x : Fin N → ℝ => (1 + ∑ i, x i ^ 2) * gbeWeight (betaF 𝕜) N x :=
    (by fun_prop : Continuous fun x : Fin N → ℝ => 1 + ∑ i, x i ^ 2).mul
      (jointDensity_continuous_gbeWeight (by linarith [jointDensity_one_le_betaF (𝕜 := 𝕜)]))
  refine hg.integrableOn.mono' hc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (isOpen_chamber N).measurableSet] with x hx
  have hpos := jointDensity_gbeWeight_pos (β := betaF 𝕜) hx
  have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine (hK x hx).trans (le_of_eq ?_)
  rw [Finset.mul_sum, Real.exp_sum]

private theorem jointDensity_integrableOn_weight :
    IntegrableOn (gbeWeight (betaF 𝕜) N) (chamber N) := by
  refine (jointDensity_integrableOn (𝕜 := 𝕜)).mono'
    (jointDensity_continuous_gbeWeight
      (by linarith [jointDensity_one_le_betaF (𝕜 := 𝕜)])).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (isOpen_chamber N).measurableSet] with x hx
  have hpos := jointDensity_gbeWeight_pos (β := betaF 𝕜) hx
  have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  nlinarith

private theorem jointDensity_measurable_ofReal_weight :
    Measurable fun x : Fin N → ℝ => ENNReal.ofReal (gbeWeight (betaF 𝕜) N x) :=
  ENNReal.measurable_ofReal.comp (jointDensity_continuous_gbeWeight
    (by linarith [jointDensity_one_le_betaF (𝕜 := 𝕜)])).measurable

/-- `Z_β < ∞` (16.1). -/
private theorem jointDensity_zStar_lt_top :
    ∫⁻ x in chamber N, ENNReal.ofReal (gbeWeight (betaF 𝕜) N x) < ⊤ :=
  (jointDensity_integrableOn_weight (𝕜 := 𝕜)).lintegral_lt_top

/-- `Z_β > 0` (16.1): `w > 0` on the nonempty open set `Σ`. -/
private theorem jointDensity_zStar_ne_zero :
    ∫⁻ x in chamber N, ENNReal.ofReal (gbeWeight (betaF 𝕜) N x) ≠ 0 := by
  have hmeas : MeasurableSet (chamber N) := (isOpen_chamber N).measurableSet
  have hne : (chamber N).Nonempty :=
    ⟨fun i => (i : ℝ), fun i j hij => by
      change ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)
      exact_mod_cast hij⟩
  have hpos : 0 < volume (chamber N) := (isOpen_chamber N).measure_pos volume hne
  intro h0
  rw [lintegral_eq_zero_iff (jointDensity_measurable_ofReal_weight (𝕜 := 𝕜))] at h0
  have hae : ∀ᵐ x ∂volume.restrict (chamber N), False := by
    filter_upwards [h0, ae_restrict_mem hmeas] with x hx hxS
    have := jointDensity_gbeWeight_pos (β := betaF 𝕜) hxS
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hae
  exact hpos.ne' hae

/-- `μ*` is a probability measure (16.1). -/
private theorem jointDensity_isProbabilityMeasure_muStar :
    IsProbabilityMeasure (muStar (betaF 𝕜) N) := by
  refine ⟨?_⟩
  rw [muStar, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel jointDensity_zStar_ne_zero jointDensity_zStar_lt_top.ne

/-- `μ*` is carried by `Σ`. -/
private theorem jointDensity_ae_muStar {β : ℝ} : ∀ᵐ x ∂muStar β N, x ∈ chamber N := by
  unfold muStar
  refine Measure.ae_smul_measure ?_ _
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (isOpen_chamber N).measurableSet)

/-- `μ*(∂Σ) = 0`. -/
private theorem jointDensity_muStar_boundary {β : ℝ} :
    muStar β N (closure (chamber N) \ chamber N) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [jointDensity_ae_muStar] with x hx h
  exact h.2 hx

/-- (16.2) with `m = 2`: `|x|² ∈ L¹(μ*)`. -/
private theorem jointDensity_integrable_sumSq :
    Integrable (fun x : Fin N → ℝ => ∑ i, x i ^ 2) (muStar (betaF 𝕜) N) := by
  unfold muStar
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 jointDensity_zStar_ne_zero)
  rw [integrable_withDensity_iff_integrable_smul' (jointDensity_measurable_ofReal_weight (𝕜 := 𝕜))
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine (jointDensity_integrableOn (𝕜 := 𝕜)).mono' ?_ ?_
  · exact (jointDensity_measurable_ofReal_weight (𝕜 := 𝕜)).ennreal_toReal.aestronglyMeasurable.smul
      (by fun_prop : Continuous fun x : Fin N → ℝ => ∑ i, x i ^ 2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (isOpen_chamber N).measurableSet] with x hx
    have hpos := jointDensity_gbeWeight_pos (β := betaF 𝕜) hx
    have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [ENNReal.toReal_ofReal hpos.le, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    nlinarith

end Weight

/-! ### The Mehler semigroup on bounded Borel data: first derivatives and their bound -/

section Mehler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem jointDensity_moments (v : ℝ) (m : ℕ) :
    Integrable (fun w : E => ‖w‖ ^ m) (gaussE E v) := by
  simpa using integrable_norm_rpow_gaussE (E := E) v m (Nat.cast_nonneg m)

/-- A bound of the type (16.7), from Lemma 14.F(c): for `|Φ| ≤ C` and `u ≥ u₁ > 0`, the
derivative of `(u, y) ↦ T_u Φ(y)` is bounded by `A (1 + |y|²)`. -/
private theorem jointDensity_norm_fderiv_mehler_le {v : ℝ} (hv : 0 < v) {Φ : E → ℝ}
    (hΦ : Measurable Φ) {C : ℝ} (hC : ∀ y, |Φ y| ≤ C) {u₁ : ℝ} (hu₁ : 0 < u₁) :
    ∃ A, ∀ u, u₁ ≤ u → ∀ y : E,
      ‖fderiv ℝ (fun p : ℝ × E => mehler v p.1 Φ p.2) (u, y)‖ ≤ A * (1 + ‖y‖ ^ 2) := by
  have := gaussE_isProbabilityMeasure (E := E) v
  set d : ℝ := (Module.finrank ℝ E : ℝ)
  set c₁ := max (mehlerKernelBoundsCHat v (Module.finrank ℝ E) 1) 0
  set κ := mehlerKernelBoundsKappa v u₁
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hc₁ : 0 ≤ c₁ := le_max_right _ _
  set A := C * 2 * c₁ * κ ^ 2 with hAdef
  have hA : 0 ≤ A := by positivity
  have hd : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨A * (16 + 2 * d * v), fun u hu y => ?_⟩
  have hu0 : 0 < u := hu₁.trans_le hu
  set Ψ : ℝ × E → ℝ := fun p => ∫ w, mehlerKernel v p.1 p.2 w * Φ w ∂gaussE E v
  have hΩ : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := isOpen_Ioi.prod isOpen_univ
  have hx : (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) := ⟨hu0, trivial⟩
  have heq : (fun p : ℝ × E => mehler v p.1 Φ p.2) =ᶠ[𝓝 (u, y)] Ψ := by
    filter_upwards [hΩ.mem_nhds hx] with p hp
    rw [mehler_eq_integral_kernel hv hp.1 hΦ]
    simp_rw [mul_comm (Φ _)]
    rfl
  have h1 : ‖fderiv ℝ Ψ (u, y)‖ = ‖iteratedFDeriv ℝ 1 Ψ (u, y)‖ := by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Ψ) (x := (u, y)) (n := 0)
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  obtain ⟨hI, hD⟩ := iteratedFDeriv_kernelIntegral hv (jointDensity_moments v) hΦ hC 1 hx
  rw [heq.fderiv_eq, h1, hD]
  set F := fun w => Φ w • iteratedFDeriv ℝ 1 (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) (u, y)
  set f : E → ℝ := fun w => (1 + ‖y‖ + ‖w‖) ^ 2 with hfdef
  -- pointwise bound by Lemma 14.F(c)
  have hpt : ∀ w, ‖F w‖ₑ ≤
      ENNReal.ofReal A * (ENNReal.ofReal (f w) * ENNReal.ofReal (mehlerKernel v u y w)) := by
    intro w
    have hK := mehlerKernel_pos v hu0 y w
    have hDK := norm_iteratedFDeriv_mehlerKernel_le hv hu₁ 1 hu y w
    have hle : ‖F w‖ ≤ A * (f w * mehlerKernel v u y w) := by
      simp only [F, norm_smul, Real.norm_eq_abs]
      calc |Φ w| * ‖iteratedFDeriv ℝ 1 (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) (u, y)‖
          ≤ C * (2 ^ 1 * mehlerKernelBoundsCHat v (Module.finrank ℝ E) 1 *
              (κ * (1 + ‖y‖ + ‖w‖)) ^ (2 * 1) * mehlerKernel v u y w) :=
            mul_le_mul (hC w) hDK (norm_nonneg _) hC0
        _ ≤ C * (2 ^ 1 * c₁ * (κ * (1 + ‖y‖ + ‖w‖)) ^ (2 * 1) * mehlerKernel v u y w) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
                (by simp only [Nat.mul_one]; positivity))
              hK.le) hC0
        _ = A * (f w * mehlerKernel v u y w) := by
            simp only [hAdef, hfdef]
            ring
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal hle
  have hfm : Measurable fun w => ENNReal.ofReal (f w) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  -- `T_u f(y) ≤ 2 (1 + 2|y|)² + 2 d v`
  have hT : mehlerL v u (fun w => ENNReal.ofReal (f w)) y ≤
      ENNReal.ofReal (2 * (1 + 2 * ‖y‖) ^ 2 + 2 * (d * v)) := by
    have hint : Integrable (fun z : E => 2 * (1 + 2 * ‖y‖) ^ 2 + 2 * ‖z‖ ^ 2) (gaussE E v) :=
      (integrable_const _).add ((jointDensity_moments v 2).const_mul 2)
    have hval : ∫ z, (2 * (1 + 2 * ‖y‖) ^ 2 + 2 * ‖z‖ ^ 2) ∂gaussE E v =
        2 * (1 + 2 * ‖y‖) ^ 2 + 2 * (d * v) := by
      rw [integral_add (integrable_const _) ((jointDensity_moments v 2).const_mul 2),
        integral_const, integral_const_mul, integral_norm_sq_gaussE hv.le]
      simp [d]
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z => by positivity)]
    unfold mehlerL
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    have ha0 : 0 ≤ ouA u := (Real.exp_pos _).le
    have ha1 : ouA u ≤ 1 := by
      unfold ouA
      exact Real.exp_le_one_iff.2 (by linarith)
    have hs0 : 0 ≤ Real.sqrt (ouS u) := Real.sqrt_nonneg _
    have hs1 : Real.sqrt (ouS u) ≤ 1 := by
      rw [Real.sqrt_le_one]
      unfold ouS
      linarith [Real.exp_pos (-u)]
    have hn : ‖ouA u • y + Real.sqrt (ouS u) • z‖ ≤ ‖y‖ + ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha0, Real.norm_of_nonneg hs0]
      have := norm_nonneg y
      have := norm_nonneg z
      nlinarith
    simp only [hfdef]
    have hy := norm_nonneg y
    have hz := norm_nonneg z
    have hn0 := norm_nonneg (ouA u • y + Real.sqrt (ouS u) • z)
    nlinarith [sq_nonneg (1 + 2 * ‖y‖ - ‖z‖)]
  have hlin : ∫⁻ w, ‖F w‖ₑ ∂gaussE E v ≤
      ENNReal.ofReal (A * (2 * (1 + 2 * ‖y‖) ^ 2 + 2 * (d * v))) := by
    calc ∫⁻ w, ‖F w‖ₑ ∂gaussE E v
        ≤ ∫⁻ w, ENNReal.ofReal A *
            (ENNReal.ofReal (f w) * ENNReal.ofReal (mehlerKernel v u y w)) ∂gaussE E v :=
          lintegral_mono hpt
      _ = ENNReal.ofReal A * mehlerL v u (fun w => ENNReal.ofReal (f w)) y := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            mehlerL_eq_lintegral_kernel hv hu0 hfm y]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (2 * (1 + 2 * ‖y‖) ^ 2 + 2 * (d * v)) := by
          gcongr
      _ = _ := (ENNReal.ofReal_mul hA).symm
  calc ‖∫ w, F w ∂gaussE E v‖ ≤ ∫ w, ‖F w‖ ∂gaussE E v := norm_integral_le_integral_norm _
    _ = (∫⁻ w, ‖F w‖ₑ ∂gaussE E v).toReal := integral_norm_eq_lintegral_enorm hI.1
    _ ≤ A * (16 + 2 * d * v) * (1 + ‖y‖ ^ 2) := by
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hlin.trans ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        have hy := norm_nonneg y
        have hdv : 0 ≤ d * v := mul_nonneg hd hv.le
        have : 2 * (1 + 2 * ‖y‖) ^ 2 + 2 * (d * v) ≤ (16 + 2 * d * v) * (1 + ‖y‖ ^ 2) := by
          nlinarith [sq_nonneg (‖y‖ - 1), mul_nonneg hdv (sq_nonneg ‖y‖)]
        calc A * (2 * (1 + 2 * ‖y‖) ^ 2 + 2 * (d * v))
            ≤ A * ((16 + 2 * d * v) * (1 + ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left this hA
          _ = _ := by ring

/-- Lemma 14.3: smoothness of `T_u Φ` in `y` for `u > 0`, the `u`-derivative in terms of the joint
derivative, and the bound of the `y`-derivative by the joint derivative. -/
private theorem jointDensity_mehler_slice {v : ℝ} (hv : 0 < v) {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hb : ∃ C, ∀ y, |Φ y| ≤ C) {u : ℝ} (hu : 0 < u) (y : E) :
    ContDiff ℝ (⊤ : ℕ∞) (mehler v u Φ) ∧
      HasDerivAt (fun u' => mehler v u' Φ y)
        (fderiv ℝ (fun p : ℝ × E => mehler v p.1 Φ p.2) (u, y) (1, 0)) u ∧
      ouGen v (mehler v u Φ) y = fderiv ℝ (fun p : ℝ × E => mehler v p.1 Φ p.2) (u, y) (1, 0) ∧
      ‖fderiv ℝ (mehler v u Φ) y‖ ≤ ‖fderiv ℝ (fun p : ℝ × E => mehler v p.1 Φ p.2) (u, y)‖ := by
  set P : ℝ × E → ℝ := fun p => mehler v p.1 Φ p.2
  have hP := contDiffOn_mehler hv hΦ hb
  have hΩ : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := isOpen_Ioi.prod isOpen_univ
  have hx : (u, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E) := ⟨hu, trivial⟩
  have hPd : HasFDerivAt P (fderiv ℝ P (u, y)) (u, y) :=
    ((hP.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hsl : ContDiff ℝ (⊤ : ℕ∞) (mehler v u Φ) :=
    hP.comp_contDiff (f := fun H : E => (u, H)) (by fun_prop) fun H => ⟨hu, trivial⟩
  have hder : HasDerivAt (fun u' => mehler v u' Φ y) (fderiv ℝ P (u, y) (1, 0)) u :=
    hPd.comp_hasDerivAt (f := fun u' : ℝ => (u', y)) u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u y))
  refine ⟨hsl, hder, (hasDerivAt_mehler hv hΦ hb hu y).unique hder, ?_⟩
  have hsd : HasFDerivAt (mehler v u Φ) ((fderiv ℝ P (u, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y :=
    hPd.comp y (hasFDerivAt_prodMk_right u y)
  rw [hsd.fderiv]
  calc ‖(fderiv ℝ P (u, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)‖
      ≤ ‖fderiv ℝ P (u, y)‖ * ‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ P (u, y)‖ * 1 :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ ℝ E)
          (norm_nonneg (fderiv ℝ P (u, y)))
    _ = _ := mul_one _

end Mehler

/-! ### Lemma 15.1: `T_u` preserves bounded invariant functions -/

private theorem jointDensity_isInvariant_mehler {N : ℕ} {Φ : Herm 𝕜 N → ℝ}
    (hΦ : Herm.IsInvariant Φ) (hm : Measurable Φ) {C : ℝ} (hC : ∀ H, |Φ H| ≤ C) (u : ℝ) :
    Herm.IsInvariant (mehler (gaussVar 𝕜 N) u Φ) := by
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  set Φ' : Herm 𝕜 N → ℝ≥0∞ := fun H => ENNReal.ofReal (Φ H + C)
  have hΦ' : Herm.IsInvariant Φ' := fun U hU H => by simp only [Φ', hΦ U hU H]
  have hm' : Measurable Φ' := ENNReal.measurable_ofReal.comp (hm.add_const C)
  have key : ∀ H, mehler (gaussVar 𝕜 N) u Φ H =
      (mehlerL (gaussVar 𝕜 N) u Φ' H).toReal - C := by
    intro H
    have hmeas : AEStronglyMeasurable
        (fun z => Φ (ouA u • H + Real.sqrt (ouS u) • z)) (gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)) :=
      (hm.comp (by fun_prop)).aestronglyMeasurable
    have hint : Integrable (fun z => Φ (ouA u • H + Real.sqrt (ouS u) • z))
        (gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)) :=
      Integrable.of_bound hmeas C (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
    unfold mehler mehlerL
    have h2 : ∫ z, (Φ (ouA u • H + Real.sqrt (ouS u) • z) + C)
        ∂gaussE (Herm 𝕜 N) (gaussVar 𝕜 N) =
        (∫⁻ z, Φ' (ouA u • H + Real.sqrt (ouS u) • z)
          ∂gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun z => by
          have := hC (ouA u • H + Real.sqrt (ouS u) • z)
          simp only [Pi.zero_apply]
          linarith [neg_abs_le (Φ (ouA u • H + Real.sqrt (ouS u) • z))])
        (hmeas.add aestronglyMeasurable_const)
    rw [← h2, integral_add hint (integrable_const C)]
    simp
  intro U hU H
  rw [key, key, (hΦ'.mehlerL hm' u) U hU H]

/-! ### Theorem 16.3 -/

/-- Theorem 16.3, Steps 1–3: `∫ θ dμ = ∫ θ dμ*` for every bounded continuous `θ` on `ℝ^N`,
`N ≥ 1`. -/
private theorem jointDensity_integral_eq {N : ℕ} (hN : 0 < N)
    (θ : BoundedContinuousFunction (Fin N → ℝ) ℝ) :
    ∫ x, θ x ∂gbeLaw 𝕜 N = ∫ x, θ x ∂muStar (betaF 𝕜) N := by
  have := jointDensity_isProbabilityMeasure_muStar (𝕜 := 𝕜) (N := N)
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  set v := gaussVar 𝕜 N with hvdef
  have hv : 0 < v := by
    rw [hvdef]
    unfold gaussVar
    have := jointDensity_one_le_betaF (𝕜 := 𝕜)
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  set Φ : Herm 𝕜 N → ℝ := fun H => θ (eigVec H) with hΦdef
  have hΦc : Continuous Φ := θ.continuous.comp (continuous_eigVec N)
  have hΦm : Measurable Φ := hΦc.measurable
  have hC : ∀ H, |Φ H| ≤ ‖θ‖ := fun H => by
    rw [← Real.norm_eq_abs]
    exact θ.norm_coe_le_norm _
  have hb : ∃ C, ∀ H, |Φ H| ≤ C := ⟨_, hC⟩
  have hΦi : Herm.IsInvariant Φ := fun U hU H => by
    simp only [hΦdef]
    rw [eigVec_conj hU]
  set P : ℝ × Herm 𝕜 N → ℝ := fun p => mehler v p.1 Φ p.2 with hPdef
  set μs := muStar (betaF 𝕜) N
  set m : ℝ → ℝ := fun u => ∫ x, mehler v u Φ (Herm.diag x) ∂μs with hmdef
  have hdiag : Continuous (Herm.diag (𝕜 := 𝕜) (N := N)) :=
    (jointDensity_contDiff_diag (n := 0)).continuous
  have hcont : ∀ u > 0, Continuous fun x : Fin N → ℝ => mehler v u Φ (Herm.diag x) := fun u hu =>
    (jointDensity_mehler_slice hv hΦm hb hu 0).1.continuous.comp hdiag
  have hbd : ∀ u x, ‖mehler v u Φ (Herm.diag (𝕜 := 𝕜) x)‖ ≤ ‖θ‖ := fun u x => by
    rw [Real.norm_eq_abs]
    exact abs_mehler_le v u hC _
  -- Step 2: `m' = 0` on `(0, ∞)`
  have hderiv : ∀ u₀ > 0, HasDerivAt m 0 u₀ := by
    intro u₀ hu₀
    have hu₁ : 0 < u₀ / 2 := half_pos hu₀
    obtain ⟨A, hA⟩ := jointDensity_norm_fderiv_mehler_le hv hΦm hC hu₁
    set F' : ℝ → (Fin N → ℝ) → ℝ := fun u x => fderiv ℝ P (u, Herm.diag x) (1, 0) with hF'def
    have hs : Set.Ioi (u₀ / 2) ∈ 𝓝 u₀ := Ioi_mem_nhds (half_lt_self hu₀)
    have hΩ : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Herm 𝕜 N))) :=
      isOpen_Ioi.prod isOpen_univ
    have hF'c : Continuous (F' u₀) := by
      have hPc := (contDiffOn_mehler hv hΦm hb).continuousOn_fderiv_of_isOpen hΩ (by simp)
      have hin : Continuous fun x : Fin N → ℝ => (u₀, Herm.diag (𝕜 := 𝕜) x) :=
        continuous_const.prodMk hdiag
      exact ((hPc.comp_continuous hin fun x => ⟨hu₀, trivial⟩).clm_apply continuous_const)
    have hSint := jointDensity_integrable_sumSq (𝕜 := 𝕜) (N := N)
    have hbound_int : Integrable (fun x : Fin N → ℝ => A * (1 + ∑ i, x i ^ 2)) μs :=
      ((integrable_const 1).add hSint).const_mul A
    -- the bound of the type (16.7) on `Σ`
    have hP_le : ∀ u, u₀ / 2 ≤ u → ∀ x ∈ chamber N,
        ‖fderiv ℝ P (u, Herm.diag x)‖ ≤ A * (1 + ∑ i, x i ^ 2) := by
      intro u hu x hx
      have := hA u hu (Herm.diag x)
      rwa [jointDensity_norm_sq_diag hx.monotone] at this
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μs)
      (F := fun u x => mehler v u Φ (Herm.diag x)) (F' := F') (x₀ := u₀)
      (bound := fun x => A * (1 + ∑ i, x i ^ 2)) hs
      (by
        filter_upwards [Ioi_mem_nhds hu₀] with u hu
        exact (hcont u hu).aestronglyMeasurable)
      (Integrable.of_bound (hcont u₀ hu₀).aestronglyMeasurable ‖θ‖
        (ae_of_all _ fun x => hbd u₀ x))
      hF'c.aestronglyMeasurable
      (by
        filter_upwards [jointDensity_ae_muStar] with x hx u hu
        calc ‖F' u x‖ ≤ ‖fderiv ℝ P (u, Herm.diag x)‖ * ‖((1 : ℝ), (0 : Herm 𝕜 N))‖ :=
              (fderiv ℝ P (u, Herm.diag x)).le_opNorm _
          _ = ‖fderiv ℝ P (u, Herm.diag x)‖ := by simp [Prod.norm_def]
          _ ≤ _ := hP_le u (le_of_lt hu) x hx)
      hbound_int
      (ae_of_all _ fun x u hu =>
        (jointDensity_mehler_slice hv hΦm hb (hu₁.trans hu) (Herm.diag x)).2.1)
    obtain ⟨hint', hd⟩ := key
    -- `∫ F' u₀ dμ* = ∫ L φ_{u₀} dμ* = 0` by Corollary 16.2 with `k ≡ 1`
    set φ : (Fin N → ℝ) → ℝ := fun y => mehler v u₀ Φ (Herm.diag y) with hφdef
    obtain ⟨hsl, -, -, -⟩ := jointDensity_mehler_slice hv hΦm hb hu₀ (0 : Herm 𝕜 N)
    have hφ : ContDiff ℝ 2 φ :=
      (hsl.of_le (by simp)).comp jointDensity_contDiff_diag
    have hinv := jointDensity_isInvariant_mehler hΦi hΦm hC u₀
    have hF'eq : ∀ᵐ x ∂μs, F' u₀ x = 1 * dysonGen (betaF 𝕜) N φ x := by
      filter_upwards [jointDensity_ae_muStar] with x hx
      rw [one_mul, ← ouGen_diag_eq_dysonGen hinv (hsl.of_le (by simp))
        hx.injective, (jointDensity_mehler_slice hv hΦm hb hu₀ (Herm.diag x)).2.2.1]
    have hpk : ∀ (i : Fin N) (x : Fin N → ℝ), pderiv i (fun _ : Fin N → ℝ => (1 : ℝ)) x = 0 :=
      fun i x => by simp [pderiv]
    have h1 : Integrable (fun x => 1 * Real.sqrt (∑ i, pderiv i φ x ^ 2)) μs := by
      refine hbound_int.mono' ?_ ?_
      · have hφd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
        have : Continuous fun x => 1 * Real.sqrt (∑ i, pderiv i φ x ^ 2) := by
          unfold pderiv
          fun_prop
        exact this.aestronglyMeasurable
      · filter_upwards [jointDensity_ae_muStar] with x hx
        rw [one_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (∑ i, pderiv i φ x ^ 2)
            ≤ ‖fderiv ℝ (mehler v u₀ Φ) (Herm.diag x)‖ :=
              invariant_norm_gradient_comp_diag_le hsl (by exact_mod_cast le_top) x
          _ ≤ ‖fderiv ℝ P (u₀, Herm.diag x)‖ :=
              (jointDensity_mehler_slice hv hΦm hb hu₀ (Herm.diag x)).2.2.2
          _ ≤ _ := hP_le u₀ (half_le_self hu₀.le) x hx
    have h2 : Integrable (fun x => ∑ i, pderiv i (fun _ : Fin N → ℝ => (1 : ℝ)) x *
        pderiv i φ x) μs := by
      simp only [hpk, zero_mul, Finset.sum_const_zero]
      exact integrable_zero _ _ _
    have h3 : Integrable (fun x => 1 * dysonGen (betaF 𝕜) N φ x) μs := hint'.congr hF'eq
    have hibp := integral_mul_dysonGen_muStar jointDensity_one_le_betaF hφ contDiff_const h1 h2 h3
    simp only [hpk, zero_mul, Finset.sum_const_zero, integral_zero, mul_zero] at hibp
    rw [integral_congr_ae hF'eq, hibp] at hd
    exact hd
  -- `m` is constant on `(0, ∞)`
  have hstep : ∀ a b, 0 < a → a < b → m b = m a := by
    intro a b ha hab
    obtain ⟨c, -, hc'⟩ := exists_hasDerivAt_eq_slope m (fun _ => (0 : ℝ)) hab
      (fun t ht => (hderiv t (ha.trans_le ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => hderiv t (ha.trans ht.1))
    have h0 : (m b - m a) / (b - a) = 0 := hc'.symm
    rw [div_eq_zero_iff] at h0
    rcases h0 with h | h
    · linarith
    · linarith
  have hconst : ∀ u > 0, m u = m 1 := by
    intro u hu
    rcases lt_trichotomy u 1 with h | rfl | h
    · exact (hstep u 1 hu h).symm
    · rfl
    · exact hstep 1 u one_pos h
  -- Step 3: the two limits
  have hlim0 : Tendsto m (𝓝[>] 0) (𝓝 (∫ x, θ x ∂μs)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖θ‖) ?_
      (Eventually.of_forall fun u => ae_of_all _ fun x => hbd u x) (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact (hcont u hu).aestronglyMeasurable
    · filter_upwards [jointDensity_ae_muStar] with x hx
      have h := (tendsto_mehler hv hΦc hb (Herm.diag x)).1
      have e : Φ (Herm.diag x) = θ x := by
        simp only [hΦdef]
        rw [eigVec_diag hx.monotone]
      rwa [e] at h
  have hlimT : Tendsto m atTop (𝓝 (∫ x, θ x ∂gbeLaw 𝕜 N)) := by
    have e : ∫ x, θ x ∂gbeLaw 𝕜 N = ∫ H, Φ H ∂gaussE (Herm 𝕜 N) v := by
      unfold gbeLaw gaussH
      exact integral_map (continuous_eigVec N).measurable.aemeasurable
        θ.continuous.aestronglyMeasurable
    have hc : ∫ _x : Fin N → ℝ, (∫ H, Φ H ∂gaussE (Herm 𝕜 N) v) ∂μs =
        ∫ H, Φ H ∂gaussE (Herm 𝕜 N) v := by simp
    rw [e, ← hc]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖θ‖) ?_
      (Eventually.of_forall fun u => ae_of_all _ fun x => hbd u x) (integrable_const _) ?_
    · filter_upwards [eventually_gt_atTop 0] with u hu
      exact (hcont u hu).aestronglyMeasurable
    · exact ae_of_all _ fun x => (tendsto_mehler hv hΦc hb (Herm.diag x)).2
  have h0 : Tendsto m (𝓝[>] 0) (𝓝 (m 1)) := tendsto_const_nhds.congr' (by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hconst u hu).symm)
  have hT : Tendsto m atTop (𝓝 (m 1)) := tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop 0] with u hu
    exact (hconst u hu).symm)
  rw [tendsto_nhds_unique hlimT hT, tendsto_nhds_unique hlim0 h0]

/-- Theorem 16.3: `μ = λ_* 𝐆 = μ*`, and `ν_t ≪ μ`, `ν_t(∂Σ) = 0` for `t > 0`. -/
theorem gbeLaw_eq_muStar (N : ℕ) : gbeLaw 𝕜 N = muStar (betaF 𝕜) N := by
  have := jointDensity_isProbabilityMeasure_muStar (𝕜 := 𝕜) (N := N)
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  have : IsProbabilityMeasure (gbeLaw 𝕜 N) :=
    (Measure.isProbabilityMeasure_map_iff (continuous_eigVec N).measurable.aemeasurable).2
      inferInstance
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · ext s _
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [hne.eq_univ, measure_univ, measure_univ]
  · exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => jointDensity_integral_eq hN f

theorem eigFlow_ac {N : ℕ} (ρ : Measure (Herm 𝕜 N)) [IsProbabilityMeasure ρ] {t : ℝ}
    (ht : 0 < t) : eigFlow ρ t ≪ gbeLaw 𝕜 N ∧ eigFlow ρ t (closure (chamber N) \ chamber N) = 0 := by
  have hac : eigFlow ρ t ≪ gbeLaw 𝕜 N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · intro s hs
      have := jointDensity_isProbabilityMeasure_muStar (𝕜 := 𝕜) (N := 0)
      rw [gbeLaw_eq_muStar] at hs
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · rw [hne.eq_univ, measure_univ] at hs
        exact absurd hs one_ne_zero
    · have hv : 0 < gaussVar 𝕜 N := by
        unfold gaussVar
        have := jointDensity_one_le_betaF (𝕜 := 𝕜)
        have : (0 : ℝ) < N := by exact_mod_cast hN
        positivity
      unfold eigFlow gbeLaw gaussH
      rw [(ouLaw_eq_withDensity hv ht ρ).1]
      exact (withDensity_absolutelyContinuous _ _).map (continuous_eigVec N).measurable
  refine ⟨hac, hac ?_⟩
  rw [gbeLaw_eq_muStar]
  exact jointDensity_muStar_boundary

end Rigidity
