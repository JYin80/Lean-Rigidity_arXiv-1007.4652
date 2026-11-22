module

public import Mathlib

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

/-!
# The entropy inequality

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].
-/

namespace Rigidity

/-- Lemma 17.8 (entropy inequality): `λ ∫ F dν - log ∫ e^{λF} dω ≤ S(ν|ω)`. -/
theorem entropy_ineq {α : Type*} [MeasurableSpace α] {ν ω : Measure α} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ω] (hνω : ν ≪ ω) {F : α → ℝ} (hF : Measurable F)
    (hb : ∃ C, ∀ x, |F x| ≤ C) {lam : ℝ} (hlam : 0 < lam) :
    ENNReal.ofReal (lam * ∫ x, F x ∂ν - Real.log (∫ x, Real.exp (lam * F x) ∂ω)) ≤
      InformationTheory.klDiv ν ω := by
  obtain ⟨C, hC⟩ := hb
  by_cases hint : Integrable (llr ν ω) ν
  swap
  · rw [InformationTheory.klDiv_of_not_integrable hint]
    exact le_top
  have hFν : Integrable F ν :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  have hexp : Integrable (fun x => Real.exp (lam * F x)) ω := by
    refine Integrable.of_bound ?_ (Real.exp (lam * C)) (Filter.Eventually.of_forall fun x => ?_)
    · exact (Real.measurable_exp.comp (hF.const_mul lam)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hC x)) hlam.le)
  have hlamF : Integrable (fun x => lam * F x) ν := hFν.const_mul lam
  have : IsProbabilityMeasure (ω.tilted fun x => lam * F x) := isProbabilityMeasure_tilted hexp
  have hac : ν ≪ ω.tilted fun x => lam * F x := hνω.trans (absolutelyContinuous_tilted hexp)
  have hint' : Integrable (llr ν (ω.tilted fun x => lam * F x)) ν :=
    integrable_llr_tilted_right hνω hlamF hint hexp
  have hgibbs := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint'
  have hcalc := integral_llr_tilted_right hνω hlamF hexp hint
  rw [InformationTheory.klDiv_of_ac_of_integrable hνω hint]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [probReal_univ] at hgibbs ⊢
  rw [hcalc, integral_const_mul] at hgibbs
  linarith

end Rigidity
