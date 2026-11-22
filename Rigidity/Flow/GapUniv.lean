module

public import Rigidity.Ensemble.Basic
public import Rigidity.Flow.Chamber
public import Rigidity.Flow.Ensembles
public import Rigidity.Flow.Entropy
public import Rigidity.Flow.EntropyBound
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.GoodSet
public import Rigidity.Flow.Herm
public import Rigidity.Flow.JointDensity
public import Rigidity.LogGas.GapConc
public import Rigidity.LogGas.TwoPoint

@[expose] public section

/-!
# Gap universality along the flow (Proposition 19.1)

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `ν ∈ 𝓔_N(ϑ, δ₋, δ₊, C₀)`, `ν_t = M.eigLaw t` the law of `λ(H_t)` and `μ = gbeLaw` the law of
`λ(V)`, `gapUniversality` is Proposition 19.1: for every `t > 0` with `N t ≥ (log N)²` and every
gap observable `F` of (17.4) (extended by `0` off the chamber `Σ_N`),
`|𝔼 F(λ(H_t)) - 𝔼 F(λ(V))| ≤ (4/N) √(C⋆ (n-1) |J|) (1/N + 32 β D² log N / t)^{1/2}` (19.1).

The proof follows the proof of Proposition 19.1.  With `R = R_t` (18.4) and `ω = ω_R` the local
relaxation measure (Definition 16.5), a convex log-gas (Definition 17.2, Comment (3)), the entropy
bound of Theorem 18.4 gives `S(ν_t|ω) ≤ 1/N + 32 β D² log N / t` and
`S(μ|ω) ≤ 28 β D² log N / t`.  In particular both measures are absolutely continuous with respect
to `ω`.  Corollary 17.9 is applied with `ν = ν_t` and with `ν = μ`, and the triangle inequality
gives (19.1).  Here `r = n - 1` and indices are 0-based.  Both `ν_t` and `μ` are absolutely
continuous with respect to `ω`, which is carried by the open chamber `Σ_N`; hence the integral of
`F` extended by `0` equals the integral of `F`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

private lemma GapUniv_one_le_betaF : 1 ≤ betaF 𝕜 := by
  unfold betaF
  exact_mod_cast Module.finrank_pos

private lemma GapUniv_isProbabilityMeasure_gbeLaw (N : ℕ) : IsProbabilityMeasure (gbeLaw 𝕜 N) := by
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  exact (Measure.isProbabilityMeasure_map_iff (continuous_eigVec N).measurable.aemeasurable).2
    inferInstance

private lemma GapUniv_isProbabilityMeasure_eigLaw {N : ℕ} (M : Ensemble 𝕜 N) (t : ℝ) :
    IsProbabilityMeasure (M.eigLaw t) := by
  have hρ : IsProbabilityMeasure M.hermLaw := by
    unfold Ensemble.hermLaw
    exact (Measure.isProbabilityMeasure_map_iff
      (Herm.measurable_ofPair (𝕜 := 𝕜) N).aemeasurable).2 inferInstance
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  unfold Ensemble.eigLaw eigFlow ouLaw
  infer_instance

/-- A measure absolutely continuous with respect to a log-gas is carried by the chamber. -/
private lemma GapUniv_ae_chamber {N : ℕ} {β : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    {ν : Measure (Fin N → ℝ)} (hνω : ν ≪ logGasMeasure β V₀) : ∀ᵐ x ∂ν, x ∈ chamber N := by
  have hac : logGasMeasure β V₀ ≪ volume.restrict (chamber N) :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  exact (hνω.trans hac).ae_le (ae_restrict_mem (isOpen_chamber N).measurableSet)

/-- Corollary 17.9 for a measure `ν` of entropy at most `b` relative to the log-gas, with the
observable extended by `0` off the chamber. -/
private lemma GapUniv_bound {N r : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) (hr : 1 ≤ r) {m : Fin r → ℕ} (hm : StrictMono m)
    (hm1 : ∀ k, 1 ≤ m k) {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N)
    {A A' ρ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ) {G : (Fin r → ℝ) → ℝ}
    (hG : GapHyp r A A' ρ G) (ν : Measure (Fin N → ℝ)) [IsProbabilityMeasure ν] {b : ℝ}
    (hb : 0 ≤ b) (hν : InformationTheory.klDiv ν (logGasMeasure β V₀) ≤ ENNReal.ofReal b) :
    |∫ x, (chamber N).indicator (gapObs J m G) x ∂ν -
        ∫ x, gapObs J m G x ∂logGasMeasure β V₀| ≤
      2 / N * (Real.sqrt (cStar A A' ρ * r * J.card) * Real.sqrt b) := by
  have hfin : InformationTheory.klDiv ν (logGasMeasure β V₀) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hν
  have hνω : ν ≪ logGasMeasure β V₀ := by
    by_contra h
    exact hfin (InformationTheory.klDiv_of_not_ac h)
  rw [integral_indicator (isOpen_chamber N).measurableSet,
    Measure.restrict_eq_self_of_ae_mem (GapUniv_ae_chamber hνω)]
  have h := abs_integral_gapObs_sub_le hω hr hm hm1 hJ hA hA' hρ hG ν hνω hfin
  have hstar : 0 ≤ cStar A A' ρ :=
    le_trans (div_nonneg (sq_nonneg A) (mul_pos two_pos cZero_pos).le) (le_max_left _ _)
  have hS : (InformationTheory.klDiv ν (logGasMeasure β V₀)).toReal ≤ b :=
    ENNReal.toReal_le_of_le_ofReal hb hν
  refine h.trans ?_
  rw [← Real.sqrt_mul (by positivity)]
  gcongr

/-- Proposition 19.1 (universality of gap observables); `F := 0` off `Σ_N`. -/
theorem gapUniversality {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 0 < C₀) {A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀)
      A₀ CR cR φ N₀) :
    ∃ N₄ : ℕ, ∀ N : ℕ, N₄ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ t : ℝ, 0 < t → Real.log N ^ 2 ≤ N * t →
      ∀ r : ℕ, 1 ≤ r → ∀ m : Fin r → ℕ, StrictMono m → (∀ k, 1 ≤ m k) →
      ∀ J : Finset ℕ, (∀ i ∈ J, ∀ k, i + m k < N) →
      ∀ A A' ρ : ℝ, 0 ≤ A → 0 ≤ A' → 0 < ρ → ∀ G : (Fin r → ℝ) → ℝ, GapHyp r A A' ρ G →
        |∫ x, (chamber N).indicator (gapObs J m G) x ∂M.eigLaw t -
            ∫ x, (chamber N).indicator (gapObs J m G) x ∂gbeLaw 𝕜 N| ≤
          4 / N * Real.sqrt (cStar A A' ρ * r * J.card) *
            Real.sqrt (1 / N + 32 * betaF 𝕜 * Dpar A₀ N ^ 2 * Real.log N / t) := by
  obtain ⟨N₄, hN₄⟩ := entropy_bound hϑ hδm hδp hC₀ hR
  refine ⟨max N₄ 16, fun N hN M hM t ht hNt r hr m hm hm1 J hJ A A' ρ hA hA' hρ G hG => ?_⟩
  obtain ⟨h1, h2⟩ := hN₄ N ((le_max_left _ _).trans hN) M hM t ht hNt
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0 : (0 : ℝ) < N := by linarith
  have hβ : 1 ≤ betaF 𝕜 := GapUniv_one_le_betaF
  have hβ0 : 0 < betaF 𝕜 := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hRpos : 0 < relaxScale 𝕜 N t := Real.sqrt_pos.2 (by positivity)
  have hωeq := relaxMeasure_eq_logGasMeasure (𝕜 := 𝕜) N hRpos
  have hconv := isConvexLogGas_relaxV₀ hβ N hRpos
  rw [hωeq] at h1 h2
  set D := Dpar A₀ N with hD
  set b : ℝ := 1 / N + 32 * betaF 𝕜 * D ^ 2 * Real.log N / t with hb
  have hb0 : 0 ≤ b := by positivity
  have hbμ0 : 0 ≤ 28 * betaF 𝕜 * D ^ 2 * Real.log N / t := by positivity
  have hle : 28 * betaF 𝕜 * D ^ 2 * Real.log N / t ≤ b := by
    have h28 : 28 * betaF 𝕜 * D ^ 2 * Real.log N / t ≤ 32 * betaF 𝕜 * D ^ 2 * Real.log N / t := by
      gcongr
      norm_num
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith
  have := GapUniv_isProbabilityMeasure_eigLaw M t
  have := GapUniv_isProbabilityMeasure_gbeLaw (𝕜 := 𝕜) N
  have hνt := GapUniv_bound hconv hr hm hm1 hJ hA hA' hρ hG (M.eigLaw t) hb0 h1
  have hμ := GapUniv_bound hconv hr hm hm1 hJ hA hA' hρ hG (gbeLaw 𝕜 N) hbμ0 h2
  have hsq : Real.sqrt (28 * betaF 𝕜 * D ^ 2 * Real.log N / t) ≤ Real.sqrt b :=
    Real.sqrt_le_sqrt hle
  have hsK : 0 ≤ Real.sqrt (cStar A A' ρ * r * J.card) := Real.sqrt_nonneg _
  have hμ' : |∫ x, gapObs J m G x ∂logGasMeasure (betaF 𝕜)
        (relaxV₀ (betaF 𝕜) N (relaxScale 𝕜 N t)) -
      ∫ x, (chamber N).indicator (gapObs J m G) x ∂gbeLaw 𝕜 N| ≤
        2 / N * (Real.sqrt (cStar A A' ρ * r * J.card) * Real.sqrt b) := by
    rw [abs_sub_comm]
    refine hμ.trans ?_
    gcongr
  calc _ ≤ _ := abs_sub_le _ (∫ x, gapObs J m G x ∂logGasMeasure (betaF 𝕜)
          (relaxV₀ (betaF 𝕜) N (relaxScale 𝕜 N t))) _
    _ ≤ 2 / N * (Real.sqrt (cStar A A' ρ * r * J.card) * Real.sqrt b) +
        2 / N * (Real.sqrt (cStar A A' ρ * r * J.card) * Real.sqrt b) := add_le_add hνt hμ'
    _ = _ := by ring

end Rigidity
