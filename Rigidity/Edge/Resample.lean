import Rigidity.Ensemble.Basic

/-!
# Resampling identities on product laws

Numbers refer to NP v1.1; the original is cited as [EYY, …].

Identities for the product law of an ensemble, obtained from Fubini's theorem on `Measure.pi`:
integrating out one coordinate (Lemma 11.4 (ii), (11.B2step)), invariance of a function that
does not depend on one coordinate under replacing the law of that coordinate (Lemma 11.4 (ii),
last statement), and the form of the conditional centring of Lemma 11.18 in which the partial
integral `P_J f` of Lemma 4.7 is expressed by resampling the coordinates in `J`
(Lemma 4.7 (b)–(d)).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


namespace Ensemble

variable {N : ℕ}

/-- Replacing the coordinates in `J` of `x` by those of `y` carries the product of two product
laws to the product law with the laws of `y` on `J` and the laws of `x` off `J`. -/
private lemma resample_measurePreserving {ι : Type*} [Fintype ι] (J : Set ι)
    [DecidablePred (· ∈ J)] (μ ν : ι → Measure 𝕜) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving (fun z : (ι → 𝕜) × (ι → 𝕜) => J.piecewise z.2 z.1)
      ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi fun i => if i ∈ J then ν i else μ i) := by
  have hT : Measurable (fun z : (ι → 𝕜) × (ι → 𝕜) => J.piecewise z.2 z.1) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i ∈ J
    · simp only [Set.piecewise_eq_of_mem _ _ _ h]
      exact (measurable_pi_apply i).comp measurable_snd
    · simp only [Set.piecewise_eq_of_notMem _ _ _ h]
      exact (measurable_pi_apply i).comp measurable_fst
  have : ∀ i, IsProbabilityMeasure (if i ∈ J then ν i else μ i) := fun i => by
    split_ifs <;> infer_instance
  refine ⟨hT, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
  have hpre : (fun z : (ι → 𝕜) × (ι → 𝕜) => J.piecewise z.2 z.1) ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun i => if i ∈ J then Set.univ else s i) ×ˢ
        (Set.univ.pi fun i => if i ∈ J then s i else Set.univ) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i ∈ J
        · simp [hi]
        · have := h i
          simpa [Set.piecewise_eq_of_notMem _ _ _ hi, hi] using this
      · by_cases hi : i ∈ J
        · have := h i
          simpa [Set.piecewise_eq_of_mem _ _ _ hi, hi] using this
        · simp [hi]
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ J
      · have := h2 i
        simpa [Set.piecewise_eq_of_mem _ _ _ hi, hi] using this
      · have := h1 i
        simpa [Set.piecewise_eq_of_notMem _ _ _ hi, hi] using this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ J <;> simp [hi]

/-- Replacing the coordinate `p` of `x` by an independent copy `v` carries the product of the
product law and the law at `p` to the product law. -/
private lemma resample_update_measurePreserving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure 𝕜) [∀ i, IsProbabilityMeasure (μ i)] (p : ι) :
    MeasurePreserving (fun z : (ι → 𝕜) × 𝕜 => Function.update z.1 p z.2)
      ((Measure.pi μ).prod (μ p)) (Measure.pi μ) := by
  have hu : Measurable (fun z : (ι → 𝕜) × 𝕜 => Function.update z.1 p z.2) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i = p
    · subst h
      simpa using measurable_snd
    · simp only [Function.update_of_ne h]
      exact (measurable_pi_apply i).comp measurable_fst
  have hT := resample_measurePreserving (𝕜 := 𝕜) ({p} : Set ι) μ fun _ => μ p
  have hh : MeasurePreserving (Prod.map id (Function.eval p) : (ι → 𝕜) × (ι → 𝕜) → (ι → 𝕜) × 𝕜)
      ((Measure.pi μ).prod (Measure.pi fun _ : ι => μ p)) ((Measure.pi μ).prod (μ p)) :=
    (MeasurePreserving.id _).prod (measurePreserving_eval (fun _ : ι => μ p) p)
  have hcomp : (fun z : (ι → 𝕜) × (ι → 𝕜) => ({p} : Set ι).piecewise z.2 z.1) =
      (fun z : (ι → 𝕜) × 𝕜 => Function.update z.1 p z.2) ∘
        (Prod.map id (Function.eval p) : (ι → 𝕜) × (ι → 𝕜) → (ι → 𝕜) × 𝕜) := by
    funext z
    simp [Set.piecewise_singleton]
  have hpi : (fun i => if i ∈ ({p} : Set ι) then μ p else μ i) = μ := by
    funext i
    by_cases hi : i = p
    · simp [hi]
    · simp [hi]
  refine ⟨hu, ?_⟩
  rw [← hh.map_eq, Measure.map_map hu hh.measurable, ← hcomp, hT.map_eq, hpi]

/-- Integration against the image measure of a measure preserving map, for a function that is
only a.e. strongly measurable. -/
private lemma resample_integral_comp {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m : Measure α} {n : Measure β} {T : α → β}
    (hT : MeasurePreserving T m n) (f : β → E) (hf : AEStronglyMeasurable f n) :
    ∫ x, f (T x) ∂m = ∫ y, f y ∂n := by
  have h := integral_map (f := f) hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hf)
  rw [hT.map_eq] at h
  exact h.symm

/-- Lemma 11.4 (ii), (11.B2step): integrating out the coordinate `p`. -/
theorem integral_eq_integral_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (M : Ensemble 𝕜 N) (p : Pair N) (f : (Pair N → 𝕜) → E)
    (hf : Integrable f M.prodLaw) :
    ∫ x, f x ∂M.prodLaw = ∫ x, (∫ v, f (Function.update x p v) ∂M.law p) ∂M.prodLaw := by
  have hmp : MeasurePreserving (fun z : (Pair N → 𝕜) × 𝕜 => Function.update z.1 p z.2)
      (M.prodLaw.prod (M.law p)) M.prodLaw := resample_update_measurePreserving M.law p
  have hint : Integrable (fun z : (Pair N → 𝕜) × 𝕜 => f (Function.update z.1 p z.2))
      (M.prodLaw.prod (M.law p)) :=
    (hmp.integrable_comp hf.aestronglyMeasurable).2 hf
  rw [← resample_integral_comp hmp f hf.aestronglyMeasurable, integral_prod _ hint]

/-- Lemma 11.4 (ii), last statement: a function that does not depend on `x_p` has the same
integral after the law at `p` is replaced. -/
theorem integral_hybrid_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (M U : Ensemble 𝕜 N) (p : Pair N) (f : (Pair N → 𝕜) → E)
    (hf : StronglyMeasurable f) (hfp : ∀ x v, f (Function.update x p v) = f x) :
    ∫ x, f x ∂(M.hybrid U {p}).prodLaw = ∫ x, f x ∂M.prodLaw := by
  have hmp : MeasurePreserving
      (fun z : (Pair N → 𝕜) × (Pair N → 𝕜) => ({p} : Set (Pair N)).piecewise z.2 z.1)
      (M.prodLaw.prod U.prodLaw) (M.hybrid U {p}).prodLaw :=
    resample_measurePreserving ({p} : Set (Pair N)) M.law U.law
  have hfun : (fun z : (Pair N → 𝕜) × (Pair N → 𝕜) =>
      f (({p} : Set (Pair N)).piecewise z.2 z.1)) = fun z => f z.1 := by
    funext z
    rw [Set.piecewise_singleton]
    exact hfp _ _
  rw [← resample_integral_comp hmp f hf.aestronglyMeasurable, hfun]
  exact resample_integral_comp (measurePreserving_fst (μ := M.prodLaw) (ν := U.prodLaw)) f
    hf.aestronglyMeasurable

/-- Lemma 4.7 (b)–(d), resampling form: for `g` bounded and independent of the coordinates in
`J`, `𝔼[g f] = 𝔼[g · P_J f]`. -/
theorem integral_mul_resample (M : Ensemble 𝕜 N) (J : Set (Pair N)) [DecidablePred (· ∈ J)]
    (f g : (Pair N → 𝕜) → ℂ) (hg : StronglyMeasurable g) (C : ℝ) (hgb : ∀ x, ‖g x‖ ≤ C)
    (hgJ : ∀ x y, (∀ q, q ∉ J → x q = y q) → g x = g y) (hf : Integrable f M.prodLaw) :
    ∫ x, g x * f x ∂M.prodLaw =
      ∫ x, g x * ∫ y, f (J.piecewise y x) ∂M.prodLaw ∂M.prodLaw := by
  have hmp : MeasurePreserving
      (fun z : (Pair N → 𝕜) × (Pair N → 𝕜) => J.piecewise z.2 z.1)
      (M.prodLaw.prod M.prodLaw) M.prodLaw := by
    have h := resample_measurePreserving J M.law M.law
    have e : (fun i => if i ∈ J then M.law i else M.law i) = M.law := funext fun i => ite_self _
    rw [e] at h
    exact h
  have hgf : Integrable (fun x => g x * f x) M.prodLaw :=
    hf.bdd_mul hg.aestronglyMeasurable (ae_of_all _ hgb)
  have hF : Integrable (fun z : (Pair N → 𝕜) × (Pair N → 𝕜) =>
      g (J.piecewise z.2 z.1) * f (J.piecewise z.2 z.1)) (M.prodLaw.prod M.prodLaw) :=
    (hmp.integrable_comp hgf.aestronglyMeasurable).2 hgf
  rw [← resample_integral_comp hmp (fun x => g x * f x) hgf.aestronglyMeasurable,
    integral_prod _ hF]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hgT : ∀ y : Pair N → 𝕜, g (J.piecewise y x) = g x := fun y =>
    hgJ _ _ fun q hq => Set.piecewise_eq_of_notMem _ _ _ hq
  simp only [hgT]
  exact integral_const_mul _ _

end Ensemble

end Rigidity
