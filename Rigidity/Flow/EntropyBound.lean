import Rigidity.Ensemble.Basic
import Rigidity.Flow.Chamber
import Rigidity.Flow.EigDensity
import Rigidity.Flow.Ensembles
import Rigidity.Flow.Entropy
import Rigidity.Flow.GaussEnsemble
import Rigidity.Flow.GoodEvent
import Rigidity.Flow.GoodSet
import Rigidity.Flow.Herm
import Rigidity.Flow.IBP
import Rigidity.Flow.Invariant
import Rigidity.LogGas.LSI
import Rigidity.Semicircle.Density

/-!
# Entropy production along the flow (Proposition 18.3)

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Let `ν_t = λ_* ρ_t` be the law of the ordered eigenvalues along the flow, `μ = gbeLaw` and, for
`R > 0`, `ω = ω_R = ψ μ` the local relaxation measure (Definition 16.5), with
`ψ = e^{-NW}/Z_W`, `W = |x - γ|²/(2R²)`, `Z_W = ∫ e^{-NW} dμ`.  The file proves Proposition 18.3
(`entropy_production`): for a smooth density `f_t` of `ν_t` (Proposition 15.4),
`t ↦ S(ν_t|ω)` is finite and `C¹` on `(s, ∞)` and
`S'(t) ≤ -(2βN)⁻¹ I_t + N/(2βR⁴) E|λ(H_t) - γ|²` (18.3), where `I_t` (`relaxFisher`) is the
relative Fisher information.

The proof follows Steps 0–4 of the proof of Proposition 18.3.  With `q_t = f_t Z_W e^{NW}`, a
version of `dν_t/dω`, `S(ν_t|ω) = ∫ f_t (log f_t + NW + log Z_W) dμ` (Step 0); the integrand is
differentiated in `t` under the integral with the `t`-uniform dominating function
`(K + 1) 𝔪 (1 + |x|²)` built from the bounds of Proposition 15.4 (iv) (Step 1); on the chamber
`∂_t f_t = L f_t` (Step 2), and Corollary 16.2 integrates by parts (Step 3); completing the square
gives (18.3) (Step 4).  The constant `log Z_W` in the integrand does not change `∇k_t`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The relative Fisher information `I_t = ∫ |∇ log(f_t/ψ)|² f_t dμ` (Proposition 18.3), with
`∇ log ψ = -N ∇W = -N (x - γ)/R²`. -/
noncomputable def relaxFisher (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((∑ i, (pderiv i f x / f x + N * (x i - gamma N i) / R ^ 2) ^ 2) * f x)
    ∂gbeLaw 𝕜 N

/-! ### 1. The density of `ω_R` with respect to `μ` -/

section Density

variable {N : ℕ}

private lemma EntropyBound_one_le_betaF : 1 ≤ betaF 𝕜 := by
  unfold betaF
  exact_mod_cast Module.finrank_pos

private instance EntropyBound_isProbabilityMeasure_gbeLaw : IsProbabilityMeasure (gbeLaw 𝕜 N) := by
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  exact (Measure.isProbabilityMeasure_map_iff (continuous_eigVec N).measurable.aemeasurable).2
    inferInstance

private lemma EntropyBound_isProbabilityMeasure_eigFlow (ρ : Measure (Herm 𝕜 N))
    [IsProbabilityMeasure ρ] (t : ℝ) : IsProbabilityMeasure (eigFlow ρ t) := by
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  unfold eigFlow ouLaw
  infer_instance

private lemma EntropyBound_relaxW_nonneg (R : ℝ) (x : Fin N → ℝ) : 0 ≤ relaxW N R x := by
  unfold relaxW
  positivity

private lemma EntropyBound_continuous_relaxW (R : ℝ) : Continuous (relaxW N R) := by
  unfold relaxW
  fun_prop

/-- `Z_W = ∫ e^{-NW} dμ`. -/
private noncomputable def EntropyBound_Z (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (R : ℝ) : ℝ :=
  ∫ x, Real.exp (-(N * relaxW N R x)) ∂gbeLaw 𝕜 N

private lemma EntropyBound_integrable_exp (R : ℝ) :
    Integrable (fun x => Real.exp (-(N * relaxW N R x))) (gbeLaw 𝕜 N) := by
  refine (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.comp (continuous_const.mul (EntropyBound_continuous_relaxW R)).neg
      ).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have := EntropyBound_relaxW_nonneg R x
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

private lemma EntropyBound_Z_pos (R : ℝ) : 0 < EntropyBound_Z 𝕜 N R :=
  integral_exp_pos (EntropyBound_integrable_exp R)

/-- `ψ = e^{-NW}/Z_W = dω/dμ`. -/
private noncomputable def EntropyBound_psi (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (R : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  Real.exp (-(N * relaxW N R x)) / EntropyBound_Z 𝕜 N R

private lemma EntropyBound_psi_pos (R : ℝ) (x : Fin N → ℝ) : 0 < EntropyBound_psi 𝕜 N R x :=
  div_pos (Real.exp_pos _) (EntropyBound_Z_pos R)

private lemma EntropyBound_measurable_psi (R : ℝ) :
    Measurable fun x => ENNReal.ofReal (EntropyBound_psi 𝕜 N R x) := by
  unfold EntropyBound_psi
  exact ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
    (continuous_const.mul (EntropyBound_continuous_relaxW R)).neg).div_const _).measurable

/-- `ω_R = ψ μ` (Definition 16.5). -/
private lemma EntropyBound_relaxMeasure_eq (R : ℝ) :
    relaxMeasure 𝕜 N R =
      (gbeLaw 𝕜 N).withDensity fun x => ENNReal.ofReal (EntropyBound_psi 𝕜 N R x) := by
  have hint := EntropyBound_integrable_exp (𝕜 := 𝕜) (N := N) R
  have hZpos := EntropyBound_Z_pos (𝕜 := 𝕜) (N := N) R
  have hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (-(N * relaxW N R x))) ∂gbeLaw 𝕜 N =
      ENNReal.ofReal (EntropyBound_Z 𝕜 N R) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  have hmeas : Measurable fun x : Fin N → ℝ => ENNReal.ofReal (Real.exp (-(N * relaxW N R x))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (EntropyBound_continuous_relaxW R)).neg).measurable
  unfold relaxMeasure
  rw [hZ, ← ENNReal.ofReal_inv_of_pos hZpos, ← withDensity_smul _ hmeas]
  congr 1
  ext x
  simp only [Pi.smul_apply, smul_eq_mul, EntropyBound_psi]
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le), div_eq_inv_mul]

private lemma EntropyBound_isProbabilityMeasure_relax (R : ℝ) :
    IsProbabilityMeasure (relaxMeasure 𝕜 N R) := by
  constructor
  rw [EntropyBound_relaxMeasure_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable (EntropyBound_psi 𝕜 N R) (gbeLaw 𝕜 N) :=
    (EntropyBound_integrable_exp R).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => (EntropyBound_psi_pos R x).le)]
  unfold EntropyBound_psi
  rw [integral_div]
  change ENNReal.ofReal (EntropyBound_Z 𝕜 N R / EntropyBound_Z 𝕜 N R) = 1
  rw [div_self (EntropyBound_Z_pos R).ne', ENNReal.ofReal_one]

/-- `q = g Z_W e^{NW} = g/ψ`, a version of `d(gμ)/dω`. -/
private noncomputable def EntropyBound_q (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (R : ℝ)
    (g : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  g x * (EntropyBound_Z 𝕜 N R * Real.exp (N * relaxW N R x))

private lemma EntropyBound_psi_mul_q (R : ℝ) (g : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    EntropyBound_psi 𝕜 N R x * EntropyBound_q 𝕜 N R g x = g x := by
  have hZ := (EntropyBound_Z_pos (𝕜 := 𝕜) (N := N) R).ne'
  unfold EntropyBound_psi EntropyBound_q
  field_simp
  rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

private lemma EntropyBound_log_q (R : ℝ) {g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hg : 0 < g x) :
    Real.log (EntropyBound_q 𝕜 N R g x) =
      Real.log (g x) + (N * relaxW N R x + Real.log (EntropyBound_Z 𝕜 N R)) := by
  unfold EntropyBound_q
  rw [Real.log_mul hg.ne' (mul_pos (EntropyBound_Z_pos R) (Real.exp_pos _)).ne',
    Real.log_mul (EntropyBound_Z_pos R).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `g μ = q ω`. -/
private lemma EntropyBound_withDensity_eq (R : ℝ) {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) :
    (gbeLaw 𝕜 N).withDensity (fun x => ENNReal.ofReal (g x)) =
      (relaxMeasure 𝕜 N R).withDensity fun x => ENNReal.ofReal (EntropyBound_q 𝕜 N R g x) := by
  have hq : Measurable fun x => ENNReal.ofReal (EntropyBound_q 𝕜 N R g x) := by
    unfold EntropyBound_q
    exact ENNReal.measurable_ofReal.comp (hg.mul (measurable_const.mul
      (Real.continuous_exp.comp (continuous_const.mul
        (EntropyBound_continuous_relaxW R))).measurable))
  rw [EntropyBound_relaxMeasure_eq, ← withDensity_mul _ (EntropyBound_measurable_psi R) hq]
  congr 1
  ext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (EntropyBound_psi_pos R x).le, EntropyBound_psi_mul_q]

end Density

/-! ### 2. `S(gμ|ω)` through the version `q` of the density -/

section KL

variable {N : ℕ}

private lemma EntropyBound_measurable_q (R : ℝ) {g : (Fin N → ℝ) → ℝ} (hg : Measurable g) :
    Measurable (EntropyBound_q 𝕜 N R g) := by
  unfold EntropyBound_q
  exact hg.mul (measurable_const.mul (Real.continuous_exp.comp (continuous_const.mul
    (EntropyBound_continuous_relaxW R))).measurable)

private lemma EntropyBound_q_pos (R : ℝ) {g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hg : 0 < g x) :
    0 < EntropyBound_q 𝕜 N R g x :=
  mul_pos hg (mul_pos (EntropyBound_Z_pos R) (Real.exp_pos _))

/-- Lemma 18.2 for `ν' = gμ` with `g > 0`: `ν' = qω`, `S(ν'|ω) = ∫ (q log q - q + 1) dω`, and,
when `g log q ∈ L¹(μ)`, `S(ν'|ω) < ∞` with `S(ν'|ω) = ∫ g log q dμ`. -/
private lemma EntropyBound_klDiv (R : ℝ) {g : (Fin N → ℝ) → ℝ} (hg : Measurable g)
    (hgpos : ∀ x, 0 < g x) (ν : Measure (Fin N → ℝ)) [IsProbabilityMeasure ν]
    (hν : ν = (gbeLaw 𝕜 N).withDensity fun x => ENNReal.ofReal (g x)) :
    ν = (relaxMeasure 𝕜 N R).withDensity (fun x => ENNReal.ofReal (EntropyBound_q 𝕜 N R g x)) ∧
    InformationTheory.klDiv ν (relaxMeasure 𝕜 N R) =
      ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (EntropyBound_q 𝕜 N R g x))
        ∂relaxMeasure 𝕜 N R ∧
    (Integrable (fun x => g x * Real.log (EntropyBound_q 𝕜 N R g x)) (gbeLaw 𝕜 N) →
      InformationTheory.klDiv ν (relaxMeasure 𝕜 N R) ≠ ∞ ∧
        (InformationTheory.klDiv ν (relaxMeasure 𝕜 N R)).toReal =
          ∫ x, g x * Real.log (EntropyBound_q 𝕜 N R g x) ∂gbeLaw 𝕜 N) := by
  have := EntropyBound_isProbabilityMeasure_relax (𝕜 := 𝕜) (N := N) R
  have hν' := hν.trans (EntropyBound_withDensity_eq R hg)
  have hqm : Measurable fun x => ENNReal.ofReal (EntropyBound_q 𝕜 N R g x) :=
    ENNReal.measurable_ofReal.comp (EntropyBound_measurable_q R hg)
  have hq0 : ∀ x, 0 ≤ EntropyBound_q 𝕜 N R g x := fun x => (EntropyBound_q_pos R (hgpos x)).le
  have hac : ν ≪ relaxMeasure 𝕜 N R := by
    rw [hν']
    exact withDensity_absolutelyContinuous _ _
  have hrn : ν.rnDeriv (relaxMeasure 𝕜 N R) =ᵐ[relaxMeasure 𝕜 N R]
      fun x => ENNReal.ofReal (EntropyBound_q 𝕜 N R g x) := by
    rw [hν']
    exact Measure.rnDeriv_withDensity _ hqm
  have hllr : llr ν (relaxMeasure 𝕜 N R) =ᵐ[ν] fun x => Real.log (EntropyBound_q 𝕜 N R g x) := by
    filter_upwards [hac.ae_le hrn] with x hx
    simp only [llr, hx, ENNReal.toReal_ofReal (hq0 x)]
  refine ⟨hν', ?_, fun hint => ?_⟩
  · rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
    refine lintegral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (hq0 x)]
  · have hgm : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hg
    have hlt : ∀ᵐ x ∂gbeLaw 𝕜 N, ENNReal.ofReal (g x) < ∞ :=
      ae_of_all _ fun _ => ENNReal.ofReal_lt_top
    have hsm : (fun x => (ENNReal.ofReal (g x)).toReal • Real.log (EntropyBound_q 𝕜 N R g x)) =
        fun x => g x * Real.log (EntropyBound_q 𝕜 N R g x) := by
      funext x
      rw [ENNReal.toReal_ofReal (hgpos x).le, smul_eq_mul]
    have hint' : Integrable (llr ν (relaxMeasure 𝕜 N R)) ν := by
      refine (integrable_congr hllr).2 ?_
      rw [hν, integrable_withDensity_iff_integrable_smul' hgm hlt, hsm]
      exact hint
    refine ⟨InformationTheory.klDiv_ne_top hac hint', ?_⟩
    rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp [measure_univ]),
      integral_congr_ae hllr, hν, integral_withDensity_eq_integral_toReal_smul hgm hlt, hsm]

end KL

/-! ### 3. Partial derivatives -/

section Pderiv

variable {N : ℕ}

private lemma EntropyBound_contDiff_relaxW (R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (relaxW N R) := by
  unfold relaxW
  fun_prop

private lemma EntropyBound_pderiv_relaxW (R : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    pderiv i (relaxW N R) x = (x i - gamma N i) / R ^ 2 := by
  have h : HasFDerivAt (relaxW N R)
      ((2 * R ^ 2)⁻¹ • ∑ k, (2 * (x k - gamma N k)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) k) x := by
    unfold relaxW
    refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun k _ => ?_) _
    have := ((hasFDerivAt_apply (𝕜 := ℝ) k x).sub_const (gamma N k)).pow 2
    convert this using 1
    simp
  unfold pderiv
  rw [h.fderiv]
  simp [Pi.single_apply]
  field_simp

private lemma EntropyBound_abs_pderiv_le {g : (Fin N → ℝ) → ℝ} (x : Fin N → ℝ) (i : Fin N) :
    |pderiv i g x| ≤ ‖fderiv ℝ g x‖ := by
  unfold pderiv
  have := (fderiv ℝ g x).le_opNorm (Pi.single i 1)
  rwa [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] at this

private lemma EntropyBound_continuous_pderiv {g : (Fin N → ℝ) → ℝ} (hg : ContDiff ℝ 1 g)
    (i : Fin N) : Continuous (pderiv i g) := by
  unfold pderiv
  exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- `∑ (x_k - c_k)² ≤ (2 + 2|c|²)(1 + |x|²)`. -/
private lemma EntropyBound_sum_sq_sub_le (c x : Fin N → ℝ) :
    ∑ k, (x k - c k) ^ 2 ≤ (2 + 2 * ∑ k, c k ^ 2) * (1 + ∑ k, x k ^ 2) := by
  have h1 : ∑ k, (x k - c k) ^ 2 ≤ 2 * ∑ k, x k ^ 2 + 2 * ∑ k, c k ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (x k + c k)]
  have h2 : 0 ≤ ∑ k, x k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h3 : 0 ≤ ∑ k, c k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith [mul_nonneg h2 h3]

end Pderiv

/-! ### 4. The smooth family `f` -/

section Family

variable {N : ℕ} {ρ : Measure (Herm 𝕜 N)} {s : ℝ} {f : ℝ → (Fin N → ℝ) → ℝ}

private lemma EntropyBound_isOpen : IsOpen (Set.Ioi s ×ˢ (Set.univ : Set (Fin N → ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

private lemma EntropyBound_mem_nhds {t : ℝ} (ht : s < t) (x : Fin N → ℝ) :
    Set.Ioi s ×ˢ (Set.univ : Set (Fin N → ℝ)) ∈ 𝓝 (t, x) :=
  EntropyBound_isOpen.mem_nhds ⟨ht, Set.mem_univ _⟩

/-- `∂_t f_t(x)`, from the joint derivative. -/
private lemma EntropyBound_hasDerivAt (hf : IsSmoothDensity ρ s f) {t : ℝ} (ht : s < t)
    (x : Fin N → ℝ) :
    HasDerivAt (fun t' => f t' x) (fderiv ℝ (fun p : ℝ × (Fin N → ℝ) => f p.1 p.2) (t, x) (1, 0))
      t := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × (Fin N → ℝ) => f p.1 p.2) (t, x) :=
    ((hf.smooth.differentiableOn (by simp)) (t, x) ⟨ht, Set.mem_univ _⟩).differentiableAt
      (EntropyBound_mem_nhds ht x)
  exact hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

private lemma EntropyBound_contDiff (hf : IsSmoothDensity ρ s f) {t : ℝ} (ht : s < t)
    {n : ℕ} : ContDiff ℝ n (f t) := by
  have h := hf.smooth.comp_contDiff (f := fun x : Fin N → ℝ => (t, x))
    (contDiff_const.prodMk contDiff_id) fun x => ⟨ht, Set.mem_univ _⟩
  exact h.of_le (WithTop.coe_le_coe.2 le_top)

/-- `NW + log Z_W`, so that `log q = log g + NW + log Z_W`. -/
private noncomputable def EntropyBound_c (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (R : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  N * relaxW N R x + Real.log (EntropyBound_Z 𝕜 N R)

private lemma EntropyBound_continuous_c (R : ℝ) : Continuous (EntropyBound_c 𝕜 N R) :=
  (continuous_const.mul (EntropyBound_continuous_relaxW R)).add continuous_const

private lemma EntropyBound_continuousOn_G (hf : IsSmoothDensity ρ s f) :
    ContinuousOn (fun p : ℝ × (Fin N → ℝ) =>
      fderiv ℝ (fun p : ℝ × (Fin N → ℝ) => f p.1 p.2) p (1, 0))
      (Set.Ioi s ×ˢ Set.univ) :=
  (hf.smooth.continuousOn_fderiv_of_isOpen EntropyBound_isOpen (by simp)).clm_apply
    continuousOn_const

private lemma EntropyBound_continuous_dt (hf : IsSmoothDensity ρ s f) {t : ℝ} (ht : s < t) :
    Continuous fun x => deriv (fun t' => f t' x) t := by
  have h := (EntropyBound_continuousOn_G hf).comp_continuous
    (continuous_const.prodMk continuous_id) fun x => (⟨ht, Set.mem_univ x⟩ :
      ((t, x) : ℝ × (Fin N → ℝ)) ∈ Set.Ioi s ×ˢ Set.univ)
  exact h.congr fun x => (EntropyBound_hasDerivAt hf ht x).deriv.symm

private lemma EntropyBound_continuousAt_dt (hf : IsSmoothDensity ρ s f) {t : ℝ} (ht : s < t)
    (x : Fin N → ℝ) : ContinuousAt (fun t' => deriv (fun t'' => f t'' x) t') t := by
  have hev : (fun t' => fderiv ℝ (fun p : ℝ × (Fin N → ℝ) => f p.1 p.2) (t', x) (1, 0)) =ᶠ[𝓝 t]
      fun t' => deriv (fun t'' => f t'' x) t' := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with t' ht'
    exact (EntropyBound_hasDerivAt hf ht' x).deriv.symm
  refine ContinuousAt.congr ?_ hev
  have hG := (EntropyBound_continuousOn_G hf).continuousAt (EntropyBound_mem_nhds ht x)
  exact hG.comp (f := fun t' : ℝ => (t', x)) (x := t) (by fun_prop)

/-- The bounds of Proposition 15.4 (iv) on `[t₁, t₂]` in the form used in Steps 0–3. -/
private lemma EntropyBound_bounds (hf : IsSmoothDensity ρ s f) (R : ℝ) {t₁ t₂ : ℝ}
    (h₁ : s < t₁) (h₁₂ : t₁ < t₂) :
    ∃ 𝔪 : (Fin N → ℝ) → ℝ, ∃ K : ℝ, 0 ≤ K ∧
      Integrable (fun x => 𝔪 x * (1 + ∑ i, x i ^ 2)) (gbeLaw 𝕜 N) ∧ (∀ x, 0 ≤ 𝔪 x) ∧
      ∀ t ∈ Set.Icc t₁ t₂, ∀ x, f t x ≤ 𝔪 x ∧ ‖fderiv ℝ (f t) x‖ ≤ 𝔪 x ∧
        |deriv (fun t' => f t' x) t| ≤ 𝔪 x ∧
        |Real.log (f t x) + EntropyBound_c 𝕜 N R x| ≤ K * (1 + ∑ i, x i ^ 2) := by
  obtain ⟨C, hC⟩ := hf.logBound t₁ t₂ h₁ h₁₂
  obtain ⟨𝔪, h𝔪i, h𝔪⟩ := hf.dom t₁ t₂ h₁ h₁₂
  set Γ : ℝ := ∑ k, gamma N k ^ 2 with hΓ
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg fun k _ => sq_nonneg _
  refine ⟨𝔪, |C| + N * (2 * R ^ 2)⁻¹ * (2 + 2 * Γ) + |Real.log (EntropyBound_Z 𝕜 N R)|,
    by positivity, by simpa using h𝔪i 1, fun x => ?_, fun t ht x => ?_⟩
  · have := h𝔪 t₁ ⟨le_rfl, h₁₂.le⟩ x
    linarith [abs_nonneg (f t₁ x), norm_nonneg (fderiv ℝ (f t₁) x),
      norm_nonneg (iteratedFDeriv ℝ 2 (f t₁) x), abs_nonneg (deriv (fun t' => f t' x) t₁),
      norm_nonneg (fderiv ℝ (fun y => deriv (fun t' => f t' y) t₁) x)]
  have h := h𝔪 t ht x
  have hn := norm_nonneg (fderiv ℝ (f t) x)
  have hn2 := norm_nonneg (iteratedFDeriv ℝ 2 (f t) x)
  have hn3 := norm_nonneg (fderiv ℝ (fun y => deriv (fun t' => f t' y) t) x)
  have ha := abs_nonneg (f t x)
  have hd := abs_nonneg (deriv (fun t' => f t' x) t)
  refine ⟨(le_abs_self _).trans (by linarith), by linarith, by linarith, ?_⟩
  set P : ℝ := 1 + ∑ i, x i ^ 2 with hP
  have hP1 : 1 ≤ P := by
    have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hlog := hC t ht x
  have hW : (N : ℝ) * relaxW N R x ≤ N * (2 * R ^ 2)⁻¹ * (2 + 2 * Γ) * P := by
    unfold relaxW
    have := mul_le_mul_of_nonneg_left (EntropyBound_sum_sq_sub_le (gamma N) x)
      (by positivity : (0 : ℝ) ≤ N * (2 * R ^ 2)⁻¹)
    rw [hP]
    linarith
  have hW0 : 0 ≤ (N : ℝ) * relaxW N R x :=
    mul_nonneg (Nat.cast_nonneg N) (EntropyBound_relaxW_nonneg R x)
  have hc : |EntropyBound_c 𝕜 N R x| ≤
      N * (2 * R ^ 2)⁻¹ * (2 + 2 * Γ) * P + |Real.log (EntropyBound_Z 𝕜 N R)| * P := by
    unfold EntropyBound_c
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hW0]
    have := abs_nonneg (Real.log (EntropyBound_Z 𝕜 N R))
    nlinarith
  have hCP : C * P ≤ |C| * P := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  calc |Real.log (f t x) + EntropyBound_c 𝕜 N R x|
      ≤ |Real.log (f t x)| + |EntropyBound_c 𝕜 N R x| := abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- Steps 0 and 1 of the proof of Proposition 18.3: with `j_t = f_t (log f_t + NW + log Z_W)`,
`t ↦ ∫ j_t dμ` is differentiable with derivative `∫ ∂_t f_t (log f_t + NW + log Z_W + 1) dμ`,
which is continuous; the domination is `(K + 1) 𝔪 (1 + |x|²)`, uniform on a ball around `t₀`. -/
private lemma EntropyBound_step1 (hf : IsSmoothDensity ρ s f) (R : ℝ) {t₀ : ℝ} (ht₀ : s < t₀) :
    Integrable (fun x => f t₀ x * (Real.log (f t₀ x) + EntropyBound_c 𝕜 N R x)) (gbeLaw 𝕜 N) ∧
    Integrable (fun x => deriv (fun t' => f t' x) t₀ *
      (Real.log (f t₀ x) + EntropyBound_c 𝕜 N R x + 1)) (gbeLaw 𝕜 N) ∧
    HasDerivAt (fun t => ∫ x, f t x * (Real.log (f t x) + EntropyBound_c 𝕜 N R x) ∂gbeLaw 𝕜 N)
      (∫ x, deriv (fun t' => f t' x) t₀ *
        (Real.log (f t₀ x) + EntropyBound_c 𝕜 N R x + 1) ∂gbeLaw 𝕜 N) t₀ ∧
    ContinuousAt (fun t => ∫ x, deriv (fun t' => f t' x) t *
      (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1) ∂gbeLaw 𝕜 N) t₀ := by
  set ε : ℝ := (t₀ - s) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h₁ : s < t₀ - ε := by rw [hε]; linarith
  obtain ⟨𝔪, K, hK, h𝔪i, h𝔪0, hb⟩ :=
    EntropyBound_bounds (𝕜 := 𝕜) hf R h₁ (by linarith : t₀ - ε < t₀ + ε)
  have hIoo : Set.Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hsub : ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), t ∈ Set.Icc (t₀ - ε) (t₀ + ε) ∧ s < t :=
    fun t ht => ⟨Set.Ioo_subset_Icc_self ht, by linarith [ht.1]⟩
  have ht₀' : t₀ ∈ Set.Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hjc : ∀ t, s < t →
      Continuous fun x => f t x * (Real.log (f t x) + EntropyBound_c 𝕜 N R x) := fun t ht =>
    have hc := (EntropyBound_contDiff (n := 0) hf ht).continuous
    hc.mul ((hc.log fun x => (hf.pos t ht x).ne').add (EntropyBound_continuous_c R))
  have hj'c : ∀ t, s < t → Continuous fun x => deriv (fun t' => f t' x) t *
      (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1) := fun t ht =>
    have hc := (EntropyBound_contDiff (n := 0) hf ht).continuous
    (EntropyBound_continuous_dt hf ht).mul
      (((hc.log fun x => (hf.pos t ht x).ne').add (EntropyBound_continuous_c R)).add
        continuous_const)
  have hbound : ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ x,
      ‖deriv (fun t' => f t' x) t * (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1)‖ ≤
        (K + 1) * (𝔪 x * (1 + ∑ i, x i ^ 2)) := by
    intro t ht x
    obtain ⟨-, -, h3, h4⟩ := hb t (hsub t ht).1 x
    have hP : 1 ≤ 1 + ∑ i, x i ^ 2 := by
      have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith
    have h5 : |Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1| ≤ (K + 1) * (1 + ∑ i, x i ^ 2) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      nlinarith
    rw [Real.norm_eq_abs, abs_mul]
    calc |deriv (fun t' => f t' x) t| * |Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1|
        ≤ 𝔪 x * ((K + 1) * (1 + ∑ i, x i ^ 2)) :=
          mul_le_mul h3 h5 (abs_nonneg _) (h𝔪0 x)
      _ = (K + 1) * (𝔪 x * (1 + ∑ i, x i ^ 2)) := by ring
  have hdiff : ∀ x, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun t => f t x * (Real.log (f t x) + EntropyBound_c 𝕜 N R x))
        (deriv (fun t' => f t' x) t * (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1)) t := by
    intro x t ht
    have hts := (hsub t ht).2
    have hd : HasDerivAt (fun t' => f t' x) (deriv (fun t' => f t' x) t) t :=
      (EntropyBound_hasDerivAt hf hts x).differentiableAt.hasDerivAt
    have hpos := hf.pos t hts x
    have := hd.mul ((hd.log hpos.ne').add_const (EntropyBound_c 𝕜 N R x))
    convert this using 1
    field_simp
  have hint_j : Integrable (fun x => f t₀ x * (Real.log (f t₀ x) + EntropyBound_c 𝕜 N R x))
      (gbeLaw 𝕜 N) := by
    refine (h𝔪i.const_mul K).mono' (hjc t₀ ht₀).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    obtain ⟨h1, -, -, h4⟩ := hb t₀ ht₀' x
    have hpos := hf.pos t₀ ht₀ x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    calc f t₀ x * |Real.log (f t₀ x) + EntropyBound_c 𝕜 N R x|
        ≤ 𝔪 x * (K * (1 + ∑ i, x i ^ 2)) := mul_le_mul h1 h4 (abs_nonneg _) (h𝔪0 x)
      _ = K * (𝔪 x * (1 + ∑ i, x i ^ 2)) := by ring
  obtain ⟨hint', hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hIoo
    (Filter.eventually_of_mem hIoo fun t ht => (hjc t (hsub t ht).2).aestronglyMeasurable)
    hint_j (hj'c t₀ ht₀).aestronglyMeasurable (ae_of_all _ fun x t ht => hbound t ht x)
    (h𝔪i.const_mul (K + 1)) (ae_of_all _ fun x t ht => hdiff x t ht)
  refine ⟨hint_j, hint', hder, ?_⟩
  refine continuousAt_of_dominated
    (Filter.eventually_of_mem hIoo fun t ht => (hj'c t (hsub t ht).2).aestronglyMeasurable)
    (Filter.eventually_of_mem hIoo fun t ht => ae_of_all _ fun x => hbound t ht x)
    (h𝔪i.const_mul (K + 1)) (ae_of_all _ fun x => ?_)
  have hfc : ContinuousAt (fun t => f t x) t₀ := (EntropyBound_hasDerivAt hf ht₀ x).continuousAt
  exact (EntropyBound_continuousAt_dt hf ht₀ x).mul
    (((hfc.log (hf.pos t₀ ht₀ x).ne').add continuousAt_const).add continuousAt_const)

/-- Pointwise algebra of Step 4, with `a = p/φ + b` and `φ > 0`, so that `p = φ(a - b)`. -/
private lemma EntropyBound_sq_le {φ p b : ℝ} (hφ : 0 < φ) :
    (p / φ + b) ^ 2 * φ ≤ 2 * (p ^ 2 / φ) + 2 * (φ * b ^ 2) ∧
      (p / φ + b) ^ 2 * φ / 2 - φ * b ^ 2 / 2 ≤ (p / φ + b) * p ∧
      |(p / φ + b) * p| ≤ 3 / 2 * ((p / φ + b) ^ 2 * φ) + 1 / 2 * (φ * b ^ 2) := by
  set a := p / φ + b with ha
  have hp : p = φ * (a - b) := by
    rw [ha]
    field_simp
    ring
  have h2 : p ^ 2 / φ = φ * (a - b) ^ 2 := by
    rw [hp]
    field_simp
  rw [h2, hp]
  refine ⟨by nlinarith [mul_nonneg hφ.le (sq_nonneg (a - 2 * b))],
    by nlinarith [mul_nonneg hφ.le (sq_nonneg (a - b))], ?_⟩
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hφ.le (sq_nonneg (a + b)),
    mul_nonneg hφ.le (sq_nonneg (a - b)), mul_nonneg hφ.le (sq_nonneg a)]

/-- Steps 2–4 of the proof of Proposition 18.3: the equation on the chamber, integration by parts
(Corollary 16.2), and completing the square. -/
private lemma EntropyBound_step234 (hf : IsSmoothDensity ρ s f) {R : ℝ} (hR : 0 < R) {t : ℝ}
    (ht : s < t)
    (hint : Integrable (fun x => deriv (fun t' => f t' x) t *
      (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1)) (gbeLaw 𝕜 N)) :
    relaxFisher 𝕜 N R (f t) ≠ ∞ ∧
    ∫ x, deriv (fun t' => f t' x) t * (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1)
        ∂gbeLaw 𝕜 N ≤
      -(2 * betaF 𝕜 * N)⁻¹ * (relaxFisher 𝕜 N R (f t)).toReal +
        N / (2 * betaF 𝕜 * R ^ 4) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂eigFlow ρ t := by
  have hβ : 1 ≤ betaF 𝕜 := EntropyBound_one_le_betaF
  have hμ : gbeLaw 𝕜 N = muStar (betaF 𝕜) N := gbeLaw_eq_muStar N
  obtain ⟨𝔪, K, hK, h𝔪i, h𝔪0, hb⟩ := EntropyBound_bounds (𝕜 := 𝕜) hf R
    (by linarith : s < (s + t) / 2) (by linarith : (s + t) / 2 < t + 1)
  have htI : t ∈ Set.Icc ((s + t) / 2) (t + 1) := ⟨by linarith, by linarith⟩
  set φ := f t with hφdef
  have hφ2 : ContDiff ℝ 2 φ := EntropyBound_contDiff (n := 2) hf ht
  have hφ1 : ContDiff ℝ 1 φ := EntropyBound_contDiff (n := 1) hf ht
  have hpos : ∀ x, 0 < φ x := hf.pos t ht
  have hcφ : Continuous φ := hφ1.continuous
  have hcp : ∀ i, Continuous (pderiv i φ) := EntropyBound_continuous_pderiv hφ1
  set Γ : ℝ := ∑ k, gamma N k ^ 2 with hΓ
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg fun k _ => sq_nonneg _
  set k : (Fin N → ℝ) → ℝ := fun x => Real.log (φ x) + EntropyBound_c 𝕜 N R x + 1 with hkdef
  have hcc : ContDiff ℝ 1 (EntropyBound_c 𝕜 N R) := by
    unfold EntropyBound_c
    exact (contDiff_const.mul (EntropyBound_contDiff_relaxW R)).add contDiff_const
  have hk : ContDiff ℝ 1 k := ((hφ1.log fun x => (hpos x).ne').add hcc).add contDiff_const
  set a : Fin N → (Fin N → ℝ) → ℝ := fun i x => pderiv i φ x / φ x + N * (x i - gamma N i) / R ^ 2
    with hadef
  set b : Fin N → (Fin N → ℝ) → ℝ := fun i x => N * (x i - gamma N i) / R ^ 2 with hbdef
  have hpk : ∀ x i, pderiv i k x = a i x := by
    intro x i
    have hφd : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ1.differentiable one_ne_zero x).hasFDerivAt
    have hWd : HasFDerivAt (relaxW N R) (fderiv ℝ (relaxW N R) x) x :=
      ((EntropyBound_contDiff_relaxW (n := 1) R).differentiable one_ne_zero x).hasFDerivAt
    have h := ((hφd.log (hpos x).ne').add ((hWd.const_mul (N : ℝ)).add_const
      (Real.log (EntropyBound_Z 𝕜 N R)))).add_const 1
    have hW := EntropyBound_pderiv_relaxW R x i
    unfold pderiv at hW ⊢
    have h' : HasFDerivAt k ((φ x)⁻¹ • fderiv ℝ φ x + (N : ℝ) • fderiv ℝ (relaxW N R) x) x := h
    rw [h'.fderiv]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hW, hadef]
    unfold pderiv
    field_simp
  -- the functions of Step 4
  have hA : ∀ x, (∑ i, (pderiv i φ x / φ x + N * (x i - gamma N i) / R ^ 2) ^ 2) * φ x =
      ∑ i, a i x ^ 2 * φ x := fun x => Finset.sum_mul _ _ _
  have hB : ∀ x, φ x * ((N : ℝ) ^ 2 / R ^ 4 * ∑ k, (x k - gamma N k) ^ 2) =
      ∑ i, φ x * b i x ^ 2 := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hbdef]
    field_simp
  have hE : ∀ x, (∑ i, pderiv i φ x ^ 2) / φ x = ∑ i, pderiv i φ x ^ 2 / φ x :=
    fun x => Finset.sum_div _ _ _
  have hab : ∀ x i, a i x = pderiv i φ x / φ x + b i x := fun x i => rfl
  have hca : ∀ i, Continuous (a i) := fun i =>
    ((hcp i).div hcφ fun x => (hpos x).ne').add (by fun_prop)
  set A : (Fin N → ℝ) → ℝ :=
    fun x => (∑ i, (pderiv i φ x / φ x + N * (x i - gamma N i) / R ^ 2) ^ 2) * φ x with hAdef
  set B : (Fin N → ℝ) → ℝ :=
    fun x => φ x * ((N : ℝ) ^ 2 / R ^ 4 * ∑ k, (x k - gamma N k) ^ 2) with hBdef
  set E1 : (Fin N → ℝ) → ℝ := fun x => (∑ i, pderiv i φ x ^ 2) / φ x with hE1def
  set X : (Fin N → ℝ) → ℝ := fun x => ∑ i, pderiv i k x * pderiv i φ x with hXdef
  have hcA : Continuous A := (continuous_finsetSum _ fun i _ => (hca i).pow 2).mul hcφ
  have hcB : Continuous B :=
    hcφ.mul (continuous_const.mul (continuous_finsetSum _ fun k _ => by fun_prop))
  have hcE1 : Continuous E1 :=
    (continuous_finsetSum _ fun i _ => (hcp i).pow 2).div hcφ fun x => (hpos x).ne'
  have hXa : X = fun x => ∑ i, a i x * pderiv i φ x := funext fun x =>
    Finset.sum_congr rfl fun i _ => by rw [hpk]
  have hcX : Continuous X := by
    rw [hXa]
    exact continuous_finsetSum _ fun i _ => (hca i).mul (hcp i)
  have hA0 : ∀ x, 0 ≤ A x := fun x =>
    mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hpos x).le
  have hB0 : ∀ x, 0 ≤ B x := fun x => mul_nonneg (hpos x).le
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => sq_nonneg _))
  -- integrability
  have hiE1 : Integrable E1 (gbeLaw 𝕜 N) :=
    (lintegral_ofReal_ne_top_iff_integrable hcE1.aestronglyMeasurable (ae_of_all _ fun x =>
      div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (hpos x).le)).1
      (hf.fisher t ht).ne
  have hiB : Integrable B (gbeLaw 𝕜 N) := by
    refine (h𝔪i.const_mul ((N : ℝ) ^ 2 / R ^ 4 * (2 + 2 * Γ))).mono' hcB.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hB0 x)]
    obtain ⟨h1, -, -, -⟩ := hb t htI x
    have h2 := EntropyBound_sum_sq_sub_le (gamma N) x
    have h3 : 0 ≤ ∑ k, (x k - gamma N k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 2 / R ^ 4 := by positivity
    calc B x ≤ 𝔪 x * ((N : ℝ) ^ 2 / R ^ 4 * ((2 + 2 * Γ) * (1 + ∑ i, x i ^ 2))) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 h4) (mul_nonneg h4 h3) (h𝔪0 x)
      _ = _ := by ring
  have hiA : Integrable A (gbeLaw 𝕜 N) := by
    refine ((hiE1.const_mul 2).add (hiB.const_mul 2)).mono' hcA.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hA0 x)]
    simp only [hAdef, hBdef, hE1def, Pi.add_apply]
    rw [hA, hB, hE, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      rw [hab]
      exact (EntropyBound_sq_le (hpos x)).1
  have hiX : Integrable X (gbeLaw 𝕜 N) := by
    refine ((hiA.const_mul (3 / 2)).add (hiB.const_mul (1 / 2))).mono' hcX.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, hXa]
    simp only [hAdef, hBdef, Pi.add_apply]
    rw [hA, hB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hab]
    exact (EntropyBound_sq_le (hpos x)).2.2
  -- integration by parts
  have hi1 : Integrable (fun x => k x * Real.sqrt (∑ i, pderiv i φ x ^ 2)) (gbeLaw 𝕜 N) := by
    refine (h𝔪i.const_mul ((K + 1) * N)).mono'
      ((hk.continuous.mul (continuous_finsetSum _ fun i _ => (hcp i).pow 2).sqrt
        ).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    obtain ⟨-, h2, -, h4⟩ := hb t htI x
    have hP : 1 ≤ 1 + ∑ i, x i ^ 2 := by
      have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith
    have hk1 : |k x| ≤ (K + 1) * (1 + ∑ i, x i ^ 2) := by
      simp only [hkdef]
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      nlinarith
    have hsq : Real.sqrt (∑ i, pderiv i φ x ^ 2) ≤ N * 𝔪 x := by
      have hs : ∑ i, pderiv i φ x ^ 2 ≤ (N * 𝔪 x) ^ 2 := by
        calc ∑ i, pderiv i φ x ^ 2 ≤ ∑ _i : Fin N, 𝔪 x ^ 2 := Finset.sum_le_sum fun i _ => by
              have := (EntropyBound_abs_pderiv_le (g := φ) x i).trans h2
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = N * 𝔪 x ^ 2 := by simp
          _ ≤ (N * 𝔪 x) ^ 2 := by
            have : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
              rcases Nat.eq_zero_or_pos N with h | h
              · simp [h]
              · have : (1 : ℝ) ≤ N := by exact_mod_cast h
                nlinarith
            nlinarith [sq_nonneg (𝔪 x)]
      calc Real.sqrt (∑ i, pderiv i φ x ^ 2) ≤ Real.sqrt ((N * 𝔪 x) ^ 2) := Real.sqrt_le_sqrt hs
        _ = N * 𝔪 x := Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg N) (h𝔪0 x))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |k x| * Real.sqrt (∑ i, pderiv i φ x ^ 2)
        ≤ (K + 1) * (1 + ∑ i, x i ^ 2) * (N * 𝔪 x) :=
          mul_le_mul hk1 hsq (Real.sqrt_nonneg _) (by positivity)
      _ = (K + 1) * N * (𝔪 x * (1 + ∑ i, x i ^ 2)) := by ring
  have hch : ∀ᵐ x ∂gbeLaw 𝕜 N, x ∈ chamber N := by
    rw [hμ]
    unfold muStar
    refine Measure.ae_smul_measure ?_ _
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (isOpen_chamber N).measurableSet)
  have hL : (fun x => deriv (fun t' => f t' x) t *
      (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1)) =ᵐ[gbeLaw 𝕜 N]
      fun x => k x * dysonGen (betaF 𝕜) N φ x := by
    filter_upwards [hch] with x hx
    rw [(hf.eqn t ht x (StrictMono.injective hx)).deriv, mul_comm]
  have hi3 : Integrable (fun x => k x * dysonGen (betaF 𝕜) N φ x) (gbeLaw 𝕜 N) :=
    (integrable_congr hL).1 hint
  have hibp := integral_mul_dysonGen_muStar hβ hφ2 hk (hμ ▸ hi1) (hμ ▸ hiX) (hμ ▸ hi3)
  rw [← hμ] at hibp
  have hXge : (1 / 2) * ∫ x, A x ∂gbeLaw 𝕜 N - (1 / 2) * ∫ x, B x ∂gbeLaw 𝕜 N ≤
      ∫ x, X x ∂gbeLaw 𝕜 N := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hiA.const_mul _)
      (hiB.const_mul _)]
    refine integral_mono ((hiA.const_mul _).sub (hiB.const_mul _)) hiX fun x => ?_
    simp only [hAdef, hBdef]
    rw [hXa, hA, hB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hab]
    have := (EntropyBound_sq_le (b := b i x) (p := pderiv i φ x) (hpos x)).2.1
    linarith
  -- `I_t` and `E|λ(H_t) - γ|²`
  have hIfin : relaxFisher 𝕜 N R φ ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hcA.aestronglyMeasurable
      (ae_of_all _ hA0)).2 hiA
  have hI : (relaxFisher 𝕜 N R φ).toReal = ∫ x, A x ∂gbeLaw 𝕜 N :=
    (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hA0) hcA.aestronglyMeasurable).symm
  have hY : ∫ x, B x ∂gbeLaw 𝕜 N =
      (N : ℝ) ^ 2 / R ^ 4 * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂eigFlow ρ t := by
    rw [hf.density t ht, integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (f t x)) (ENNReal.measurable_ofReal.comp hcφ.measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hBdef, smul_eq_mul, ENNReal.toReal_ofReal (hf.pos t ht x).le, hφdef]
    ring
  refine ⟨hIfin, ?_⟩
  have hj : ∫ x, deriv (fun t' => f t' x) t * (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1)
      ∂gbeLaw 𝕜 N = -(betaF 𝕜 * N)⁻¹ * ∫ x, X x ∂gbeLaw 𝕜 N := by
    rw [integral_congr_ae hL, hibp]
  rw [hj, hI]
  rw [hY] at hXge
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hβ0 : 0 < betaF 𝕜 := by linarith
    have hc : 0 < (betaF 𝕜 * N)⁻¹ := by positivity
    have key := mul_le_mul_of_nonneg_left hXge hc.le
    set IA := ∫ x, A x ∂gbeLaw 𝕜 N
    set Y := ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂eigFlow ρ t
    have e : (betaF 𝕜 * N)⁻¹ * ((1 / 2) * IA - (1 / 2) * ((N : ℝ) ^ 2 / R ^ 4 * Y)) =
        (2 * betaF 𝕜 * N)⁻¹ * IA - N / (2 * betaF 𝕜 * R ^ 4) * Y := by
      field_simp
    linarith [key, e]

end Family

/-! ### 5. Proposition 18.3 -/

/-- Proposition 18.3 (entropy production). -/
theorem entropy_production {N : ℕ} (ρ : Measure (Herm 𝕜 N)) [IsProbabilityMeasure ρ]
    (hρ : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ) {s : ℝ} (hs : 0 < s)
    {f : ℝ → (Fin N → ℝ) → ℝ} (hf : IsSmoothDensity ρ s f) {R : ℝ} (hR : 0 < R) :
    (∀ t > s, InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R) ≠ ∞) ∧
    ContDiffOn ℝ 1 (fun t => (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal)
      (Set.Ioi s) ∧
    ∀ t > s, relaxFisher 𝕜 N R (f t) ≠ ∞ ∧
      deriv (fun t => (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal) t ≤
        -(2 * betaF 𝕜 * N)⁻¹ * (relaxFisher 𝕜 N R (f t)).toReal +
          N / (2 * betaF 𝕜 * R ^ 4) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂eigFlow ρ t := by
  have _ := hρ
  have _ := hs
  -- Step 0: `S(ν_t|ω) = ∫ f_t (log f_t + NW + log Z_W) dμ < ∞`
  have hS : ∀ t > s, InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R) ≠ ∞ ∧
      (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal =
        ∫ x, f t x * (Real.log (f t x) + EntropyBound_c 𝕜 N R x) ∂gbeLaw 𝕜 N := by
    intro t ht
    have := EntropyBound_isProbabilityMeasure_eigFlow ρ t
    have hcont := (EntropyBound_contDiff (n := 0) hf ht).continuous
    have hj : (fun x => f t x * Real.log (EntropyBound_q 𝕜 N R (f t) x)) =
        fun x => f t x * (Real.log (f t x) + EntropyBound_c 𝕜 N R x) :=
      funext fun x => by rw [EntropyBound_log_q R (hf.pos t ht x)]; rfl
    obtain ⟨-, -, h⟩ :=
      EntropyBound_klDiv R hcont.measurable (hf.pos t ht) (eigFlow ρ t) (hf.density t ht)
    rw [hj] at h
    exact h (EntropyBound_step1 hf R ht).1
  -- Step 1: `S` is differentiable on `(s, ∞)`
  have hD : ∀ t > s, HasDerivAt
      (fun t => (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal)
      (∫ x, deriv (fun t' => f t' x) t *
        (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1) ∂gbeLaw 𝕜 N) t := by
    intro t ht
    have hev : (fun t => ∫ x, f t x * (Real.log (f t x) + EntropyBound_c 𝕜 N R x) ∂gbeLaw 𝕜 N)
        =ᶠ[𝓝 t] fun t => (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with t' ht'
      exact (hS t' ht').2.symm
    exact (EntropyBound_step1 hf R ht).2.2.1.congr_of_eventuallyEq hev.symm
  refine ⟨fun t ht => (hS t ht).1, ?_, fun t ht => ?_⟩
  · have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0) isOpen_Ioi
      (f := fun t => (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal)).2
      ⟨fun t ht => (hD t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    · simpa using h
    rw [contDiffOn_zero]
    intro t ht
    have hev : (fun t => ∫ x, deriv (fun t' => f t' x) t *
        (Real.log (f t x) + EntropyBound_c 𝕜 N R x + 1) ∂gbeLaw 𝕜 N) =ᶠ[𝓝 t]
        deriv fun t => (InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R)).toReal := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with t' ht'
      exact (hD t' ht').deriv.symm
    exact ((EntropyBound_step1 hf R ht).2.2.2.congr_of_eventuallyEq hev.symm).continuousWithinAt
  · obtain ⟨h1, h2⟩ := EntropyBound_step234 hf hR ht (EntropyBound_step1 hf R ht).2.1
    exact ⟨h1, (hD t ht).deriv ▸ h2⟩

/-! ### 7. Theorem 18.4

With `R = R_t` (18.4) and `ω = ω_{R_t}`, Theorem 18.4 (`entropy_bound`) bounds `S(ν_t|ω)` and
`S(μ|ω)`.  The proof is the one of Theorem 18.4: Proposition 15.4 at `s = t/4` and Proposition 18.3
with this `s` and `R`; the LSI (Theorem 17.4) for `q_r = f_r Z_W e^{NW}`, whose Fisher information
`∫ |∇q_r|²/q_r dω` is `I_r` (`relaxFisher`); the bound `Q = 7D²/N` of Lemma 13.3; Grönwall on
`[t/2, t]`; and Lemmas 18.1 and 18.2 at `t/2`. -/

/-- `R_t = (t/(8β log N))^{1/2}` (18.4). -/
noncomputable def relaxScale (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (t / (8 * betaF 𝕜 * Real.log N))

section Bound

variable {N : ℕ}

private lemma EntropyBound_isProbabilityMeasure_hermLaw (M : Ensemble 𝕜 N) :
    IsProbabilityMeasure M.hermLaw := by
  unfold Ensemble.hermLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (Herm.measurable_ofPair (𝕜 := 𝕜) N).aemeasurable).2 inferInstance

/-- `∂_i q = q (∂_i g/g + N(x_i - γ_i)/R²)` for `q = g Z_W e^{NW}`. -/
private lemma EntropyBound_pderiv_q (R : ℝ) {g : (Fin N → ℝ) → ℝ} (hg : Differentiable ℝ g)
    {x : Fin N → ℝ} (hgx : g x ≠ 0) (i : Fin N) :
    pderiv i (EntropyBound_q 𝕜 N R g) x =
      EntropyBound_q 𝕜 N R g x * (pderiv i g x / g x + N * (x i - gamma N i) / R ^ 2) := by
  have hW : HasFDerivAt (relaxW N R) (fderiv ℝ (relaxW N R) x) x :=
    ((EntropyBound_contDiff_relaxW (n := 1) R).differentiable one_ne_zero x).hasFDerivAt
  have hh := ((hW.const_mul (N : ℝ)).exp).const_mul (EntropyBound_Z 𝕜 N R)
  have h := (hg x).hasFDerivAt.mul hh
  have hpW := EntropyBound_pderiv_relaxW R x i
  unfold pderiv at hpW ⊢
  have h' : HasFDerivAt (EntropyBound_q 𝕜 N R g) (g x • (EntropyBound_Z 𝕜 N R •
      (Real.exp (N * relaxW N R x) • ((N : ℝ) • fderiv ℝ (relaxW N R) x))) +
      (EntropyBound_Z 𝕜 N R * Real.exp (N * relaxW N R x)) • fderiv ℝ g x) x := h
  rw [h'.fderiv]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpW]
  unfold EntropyBound_q
  field_simp
  ring

/-- `∫ |∇q|²/q dω = ∫ |∇ log g + N(x - γ)/R²|² g dμ` for `q = g Z_W e^{NW}` (proof of
Proposition 18.3, the two forms of `I_t`). -/
private lemma EntropyBound_fisher_eq (R : ℝ) {g : (Fin N → ℝ) → ℝ} (hg : Differentiable ℝ g)
    (hgpos : ∀ x, 0 < g x) :
    ∫⁻ x, ENNReal.ofReal ((∑ i, pderiv i (EntropyBound_q 𝕜 N R g) x ^ 2) /
      EntropyBound_q 𝕜 N R g x) ∂relaxMeasure 𝕜 N R = relaxFisher 𝕜 N R g := by
  rw [EntropyBound_relaxMeasure_eq, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (EntropyBound_measurable_psi R) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  unfold relaxFisher
  refine lintegral_congr fun x => ?_
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (EntropyBound_psi_pos R x).le]
  congr 1
  have hq := EntropyBound_q_pos (𝕜 := 𝕜) R (hgpos x)
  have hψq := EntropyBound_psi_mul_q (𝕜 := 𝕜) R g x
  set q := EntropyBound_q 𝕜 N R g x with hqdef
  set ψ := EntropyBound_psi 𝕜 N R x with hψdef
  have e : ∀ i, pderiv i (EntropyBound_q 𝕜 N R g) x ^ 2 =
      q ^ 2 * (pderiv i g x / g x + N * (x i - gamma N i) / R ^ 2) ^ 2 := fun i => by
    rw [EntropyBound_pderiv_q R hg (hgpos x).ne', mul_pow]
  rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum]
  set T := ∑ i, (pderiv i g x / g x + N * (x i - gamma N i) / R ^ 2) ^ 2
  rw [show ψ * (q ^ 2 * T / q) = (ψ * q) * T by field_simp, hψq, mul_comm]

/-- `∑ x_k² ≤ 2 ∑ (x_k - γ_k)² + 2 ∑ γ_k²`, and the consequences of a bound
`E|x - γ|² ≤ Q`. -/
private lemma EntropyBound_integrable_sq {ν : Measure (Fin N → ℝ)} [IsFiniteMeasure ν] {Q : ℝ}
    (hQ : 0 ≤ Q)
    (h : ∫⁻ x, ENNReal.ofReal (∑ k, (x k - gamma N k) ^ 2) ∂ν ≤ ENNReal.ofReal Q) :
    Integrable (fun x => ∑ k, (x k - gamma N k) ^ 2) ν ∧ Integrable (fun x => ∑ k, x k ^ 2) ν ∧
      ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂ν ≤ Q := by
  have hc : Continuous fun x : Fin N → ℝ => ∑ k, (x k - gamma N k) ^ 2 := by fun_prop
  have h0 : ∀ x : Fin N → ℝ, 0 ≤ ∑ k, (x k - gamma N k) ^ 2 := fun x =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hi : Integrable (fun x => ∑ k, (x k - gamma N k) ^ 2) ν :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable (ae_of_all _ h0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  refine ⟨hi, ?_, ?_⟩
  · refine ((hi.const_mul 2).add (integrable_const (2 * ∑ k, gamma N k ^ 2))).mono'
      (by fun_prop : Continuous fun x : Fin N → ℝ => ∑ k, x k ^ 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    change ∑ k, x k ^ 2 ≤ 2 * ∑ k, (x k - gamma N k) ^ 2 + 2 * ∑ k, gamma N k ^ 2
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (x k - 2 * gamma N k)]
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hc.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hQ h

/-- Step (1) of the proof of Theorem 18.4: for `ν' = gμ` with `g > 0` of class `C²`,
`S(ν'|ω) ≤ (2κ)⁻¹ I ≤ R²/(2N) I` by the LSI (Theorem 17.4), `κ = N(β/2 + R⁻²)`. -/
private lemma EntropyBound_lsi {R : ℝ} (hR : 0 < R) (hN : 0 < N) {g : (Fin N → ℝ) → ℝ}
    (hg : ContDiff ℝ 2 g) (hgpos : ∀ x, 0 < g x) (ν : Measure (Fin N → ℝ))
    [IsProbabilityMeasure ν] (hν : ν = (gbeLaw 𝕜 N).withDensity fun x => ENNReal.ofReal (g x)) :
    InformationTheory.klDiv ν (relaxMeasure 𝕜 N R) ≤
      ENNReal.ofReal (R ^ 2 / (2 * N)) * relaxFisher 𝕜 N R g := by
  have hgm : Measurable g := hg.continuous.measurable
  obtain ⟨hνq, hkl, -⟩ := EntropyBound_klDiv R hgm hgpos ν hν
  have hβ := EntropyBound_one_le_betaF (𝕜 := 𝕜)
  have hω := isConvexLogGas_relaxV₀ hβ N hR
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hκ : 0 < (N : ℝ) * (betaF 𝕜 / 2 + 1 / R ^ 2) := by positivity
  have hqc : ContDiff ℝ 2 (EntropyBound_q 𝕜 N R g) := by
    unfold EntropyBound_q
    exact hg.mul (contDiff_const.mul (Real.contDiff_exp.comp
      (contDiff_const.mul (EntropyBound_contDiff_relaxW R))))
  have := EntropyBound_isProbabilityMeasure_relax (𝕜 := 𝕜) (N := N) R
  have hnorm : ∫ x, EntropyBound_q 𝕜 N R g x
      ∂logGasMeasure (betaF 𝕜) (relaxV₀ (betaF 𝕜) N R) = 1 := by
    rw [← relaxMeasure_eq_logGasMeasure N hR]
    have h1 : ∫⁻ x, ENNReal.ofReal (EntropyBound_q 𝕜 N R g x) ∂relaxMeasure 𝕜 N R = 1 := by
      have h := congrArg (fun m : Measure (Fin N → ℝ) => m Set.univ) hνq
      simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
      exact h.symm
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => (EntropyBound_q_pos R (hgpos x)).le)
      (EntropyBound_measurable_q R hgm).aestronglyMeasurable, h1, ENNReal.toReal_one]
  have hL := logSobolev hω hκ hqc (fun x => EntropyBound_q_pos R (hgpos x)) hnorm
  rw [← relaxMeasure_eq_logGasMeasure N hR, ← hkl,
    EntropyBound_fisher_eq R (hg.differentiable (by norm_num)) hgpos] at hL
  refine hL.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : R ^ 2 * (2 * ((N : ℝ) * (betaF 𝕜 / 2 + 1 / R ^ 2))) =
      N * R ^ 2 * betaF 𝕜 + 2 * N := by
    field_simp
  rw [e]
  have : 0 ≤ (N : ℝ) * R ^ 2 * betaF 𝕜 := by positivity
  linarith

end Bound

/-- Theorem 18.4 (entropy bound). -/
theorem entropy_bound {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 0 < C₀) {A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀)
      A₀ CR cR φ N₀) :
    ∃ N₄ : ℕ, ∀ N : ℕ, N₄ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ t : ℝ, 0 < t → Real.log N ^ 2 ≤ N * t →
        InformationTheory.klDiv (M.eigLaw t) (relaxMeasure 𝕜 N (relaxScale 𝕜 N t)) ≤
            ENNReal.ofReal (1 / N + 32 * betaF 𝕜 * Dpar A₀ N ^ 2 * Real.log N / t) ∧
          InformationTheory.klDiv (gbeLaw 𝕜 N) (relaxMeasure 𝕜 N (relaxScale 𝕜 N t)) ≤
            ENNReal.ofReal (28 * betaF 𝕜 * Dpar A₀ N ^ 2 * Real.log N / t) := by
  obtain ⟨N₃, hN₃⟩ := lintegral_dist_gamma_le hϑ hδm hδp hC₀ hR
  refine ⟨max N₃ 16, fun N hN M hM t ht hNt => ?_⟩
  obtain ⟨hQt, hQμ⟩ := hN₃ N ((le_max_left _ _).trans hN) M hM
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hN0 : (0 : ℝ) < N := by linarith
  have hβ := EntropyBound_one_le_betaF (𝕜 := 𝕜)
  have hβ0 : 0 < betaF 𝕜 := by linarith
  have hlog : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  set D := Dpar A₀ N with hD
  set Q : ℝ := 7 * D ^ 2 / N with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set R := relaxScale 𝕜 N t with hRdef
  have hR2 : R ^ 2 = t / (8 * betaF 𝕜 * Real.log N) := Real.sq_sqrt (by positivity)
  have hRpos : 0 < R := Real.sqrt_pos.2 (by positivity)
  set B : ℝ := N * Q / (2 * R ^ 2) with hB
  have hBval : B = 28 * betaF 𝕜 * D ^ 2 * Real.log N / t := by
    rw [hB, hQ, hR2]
    field_simp
    ring
  -- `S(μ|ω) ≤ NQ/(2R²)` (Lemma 18.2 at `ν' = μ`)
  have hμ := EntropyBound_integrable_sq hQ0 hQμ
  have h2 : InformationTheory.klDiv (gbeLaw 𝕜 N) (relaxMeasure 𝕜 N R) ≤ ENNReal.ofReal B := by
    refine (klDiv_relaxMeasure_le hRpos (gbeLaw 𝕜 N) (Measure.AbsolutelyContinuous.refl _)
      hμ.2.1).trans ?_
    rw [InformationTheory.klDiv_self, zero_add]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (N : ℝ) / (2 * R ^ 2) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂gbeLaw 𝕜 N
        ≤ N / (2 * R ^ 2) * Q := mul_le_mul_of_nonneg_left hμ.2.2 (by positivity)
      _ = B := by rw [hB]; ring
  refine ⟨?_, hBval ▸ h2⟩
  -- the flow from `s = t/4`
  set ρ := M.hermLaw with hρ
  have := EntropyBound_isProbabilityMeasure_hermLaw M
  have hmom : ∀ m : ℕ, Integrable (fun H => ‖H‖ ^ m) ρ := fun m => by
    simpa [Real.rpow_natCast] using
      Ensemble.integrable_norm_pow_hermLaw hϑ hM (q := m) (Nat.cast_nonneg m)
  have ht4 : 0 < t / 4 := by positivity
  obtain ⟨-, f, hf⟩ := exists_isSmoothDensity ρ hmom ht4
  obtain ⟨hfin, hC1, hder⟩ := entropy_production ρ hmom ht4 hf hRpos
  set S : ℝ → ℝ := fun r => (InformationTheory.klDiv (eigFlow ρ r) (relaxMeasure 𝕜 N R)).toReal
    with hS
  -- (1) LSI
  have hlsi : ∀ r > t / 4, S r ≤ R ^ 2 / (2 * N) * (relaxFisher 𝕜 N R (f r)).toReal := by
    intro r hr
    have := EntropyBound_isProbabilityMeasure_eigFlow ρ r
    have h := EntropyBound_lsi hRpos (by omega) (EntropyBound_contDiff (n := 2) hf hr)
      (hf.pos r hr) (eigFlow ρ r) (hf.density r hr)
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hder r hr).1) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
  -- (2) the differential inequality
  set a : ℝ := 1 / (betaF 𝕜 * R ^ 2) with ha
  have ha0 : 0 < a := by positivity
  have hdi : ∀ r > t / 4, deriv S r ≤ -a * S r + a * B := by
    intro r hr
    obtain ⟨-, hd⟩ := hder r hr
    have := EntropyBound_isProbabilityMeasure_eigFlow ρ r
    have hY := (EntropyBound_integrable_sq (ν := eigFlow ρ r) hQ0 (hQt r (by linarith))).2.2
    have hI := hlsi r hr
    set I := (relaxFisher 𝕜 N R (f r)).toReal
    set Y := ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂eigFlow ρ r
    have e1 : (2 * betaF 𝕜 * N)⁻¹ * I = (R ^ 2 / (2 * N) * I) / (betaF 𝕜 * R ^ 2) := by
      field_simp
    have h1 : S r / (betaF 𝕜 * R ^ 2) ≤ (2 * betaF 𝕜 * N)⁻¹ * I := by
      rw [e1]
      exact div_le_div_of_nonneg_right hI (by positivity)
    have h3 : (N : ℝ) / (2 * betaF 𝕜 * R ^ 4) * Y ≤ N / (2 * betaF 𝕜 * R ^ 4) * Q :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    have e3 : (N : ℝ) / (2 * betaF 𝕜 * R ^ 4) * Q = a * B := by
      rw [ha, hB]
      field_simp
    have e4 : -a * S r = -(S r / (betaF 𝕜 * R ^ 2)) := by
      rw [ha]
      ring
    have hd' : deriv S r ≤ -(2 * betaF 𝕜 * N)⁻¹ * I + N / (2 * betaF 𝕜 * R ^ 4) * Y := hd
    linarith
  -- (3) Grönwall on `[t/2, t]`
  have hSd : ∀ r > t / 4, HasDerivAt S (deriv S r) r := fun r hr =>
    ((hC1.differentiableOn one_ne_zero r hr).differentiableAt (isOpen_Ioi.mem_nhds hr)).hasDerivAt
  set h : ℝ → ℝ := fun r => Real.exp (a * r) * (S r - B) with hh
  have hhd : ∀ r > t / 4, HasDerivAt h (Real.exp (a * r) * (deriv S r + a * S r - a * B)) r := by
    intro r hr
    have := (((hasDerivAt_id r).const_mul a).exp).mul ((hSd r hr).sub_const B)
    exact this.congr_deriv (by simp only [id]; ring)
  have hanti : AntitoneOn h (Set.Icc (t / 2) t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact fun r hr => (hhd r (by linarith [hr.1])).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun r hr => (hhd r (by linarith [hr.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro r hr
      rw [(hhd r (by linarith [hr.1])).deriv]
      have := hdi r (by linarith [hr.1])
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hht := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : t / 2 ≤ t)
  -- (4) the initial value
  have hinit : S (t / 2) ≤ N ^ 3 + B := by
    have := EntropyBound_isProbabilityMeasure_eigFlow ρ (t / 2)
    have hi := EntropyBound_integrable_sq (ν := eigFlow ρ (t / 2)) hQ0 (hQt (t / 2) (by positivity))
    have hac := (eigFlow_ac ρ (by positivity : 0 < t / 2)).1
    have h18_2 := klDiv_relaxMeasure_le hRpos (eigFlow ρ (t / 2)) hac hi.2.1
    have hNt1 : 1 ≤ N * t := le_trans (by nlinarith) hNt
    have hs : (N : ℝ)⁻¹ ^ 2 ≤ t / 2 := by
      rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    have h18_1 := klDiv_eigLaw_le_cube (by omega) hϑ hM hs
    have hle : InformationTheory.klDiv (eigFlow ρ (t / 2)) (relaxMeasure 𝕜 N R) ≤
        ENNReal.ofReal (N ^ 3 + B) := by
      refine h18_2.trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      refine add_le_add h18_1 (ENNReal.ofReal_le_ofReal ?_)
      calc (N : ℝ) / (2 * R ^ 2) * ∫ x, ∑ k, (x k - gamma N k) ^ 2 ∂eigFlow ρ (t / 2)
          ≤ N / (2 * R ^ 2) * Q := mul_le_mul_of_nonneg_left hi.2.2 (by positivity)
        _ = B := by rw [hB]; ring
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  -- (5) arithmetic: `e^{at/2} = N⁴`
  have hat : a * (t / 2) = Real.log ((N : ℝ) ^ 4) := by
    rw [Real.log_pow, ha, hR2]
    field_simp
    ring
  have hE : Real.exp (a * (t / 2)) = (N : ℝ) ^ 4 := by
    rw [hat, Real.exp_log (by positivity)]
  have hE2 : Real.exp (a * t) = (N : ℝ) ^ 4 * (N : ℝ) ^ 4 := by
    rw [show a * t = a * (t / 2) + a * (t / 2) by ring, Real.exp_add, hE]
  have hfinal : S t ≤ 1 / N + B := by
    simp only [hh, hE, hE2] at hht
    have hN4 : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
    have h1 : (N : ℝ) ^ 4 * (S t - B) ≤ S (t / 2) - B := by
      have := hht
      nlinarith
    have h2 : (N : ℝ) ^ 4 * (S t - B) ≤ (N : ℝ) ^ 4 * (1 / N) := by
      have e : (N : ℝ) ^ 4 * (1 / N) = N ^ 3 := by field_simp
      rw [e]
      linarith
    linarith [le_of_mul_le_mul_left h2 hN4]
  change InformationTheory.klDiv (eigFlow ρ t) (relaxMeasure 𝕜 N R) ≤ _
  rw [← ENNReal.ofReal_toReal (hfin t (by linarith))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h28 : 28 * betaF 𝕜 * D ^ 2 * Real.log N / t ≤ 32 * betaF 𝕜 * D ^ 2 * Real.log N / t := by
    gcongr
    norm_num
  change S t ≤ _
  linarith [hBval ▸ hfinal]

end Rigidity
