import Mathlib

open MeasureTheory Real
open scoped ENNReal

namespace Rigidity

/-!
# Splitting of the product law

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].
-/

/-! ### §4.6: splitting of the product law (Lemma 4.7) -/

section Split

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- The point with coordinates in `J` from `y` and the other coordinates from `x`. -/
def piMerge (J : Set ι) [DecidablePred (· ∈ J)] (x : ∀ i, α i) (y : ∀ i : J, α i) : ∀ i, α i :=
  fun i => if h : i ∈ J then y ⟨i, h⟩ else x i

/-- The partial integral `P_J f` of a `[0, ∞]`-valued function (Lemma 4.7 (b)). -/
noncomputable def partialLInt (ν : ∀ i, Measure (α i)) (J : Set ι) [DecidablePred (· ∈ J)]
    (f : (∀ i, α i) → ℝ≥0∞) (x : ∀ i, α i) : ℝ≥0∞ :=
  ∫⁻ y, f (piMerge J x y) ∂Measure.pi (fun i : J => ν i)

/-- The partial integral `P_J f` of a complex function (Lemma 4.7 (c)); its value is `0` where
the slice is not integrable. -/
noncomputable def partialInt (ν : ∀ i, Measure (α i)) (J : Set ι) [DecidablePred (· ∈ J)]
    (f : (∀ i, α i) → ℂ) (x : ∀ i, α i) : ℂ :=
  ∫ y, f (piMerge J x y) ∂Measure.pi (fun i : J => ν i)

variable (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)] (J : Set ι)
  [DecidablePred (· ∈ J)]

omit [Fintype ι] [∀ i, MeasurableSpace (α i)] in
/-- The coordinates of `piMerge J x y` outside `J` are those of `x`. -/
private lemma piMerge_of_notMem (x : ∀ i, α i) (y : ∀ i : J, α i) {i : ι} (h : i ∉ J) :
    piMerge J x y i = x i := by
  simp [piMerge, h]

omit [Fintype ι] [∀ i, MeasurableSpace (α i)] in
/-- The coordinates of `piMerge J x y` in `J` are those of `y`. -/
private lemma piMerge_of_mem (x : ∀ i, α i) (y : ∀ i : J, α i) {i : ι} (h : i ∈ J) :
    piMerge J x y i = y ⟨i, h⟩ := by
  simp [piMerge, h]

omit [Fintype ι] in
/-- `piMerge` is jointly measurable in `(x, y)`. -/
private lemma measurable_piMerge :
    Measurable (fun p : (∀ i, α i) × (∀ i : J, α i) => piMerge J p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ J
  · have : (fun p : (∀ i, α i) × (∀ i : J, α i) => piMerge J p.1 p.2 i) =
        fun p => p.2 ⟨i, h⟩ := by
      funext p
      exact piMerge_of_mem J p.1 p.2 h
    rw [this]
    exact (measurable_pi_apply _).comp measurable_snd
  · have : (fun p : (∀ i, α i) × (∀ i : J, α i) => piMerge J p.1 p.2 i) =
        fun p => p.1 i := by
      funext p
      exact piMerge_of_notMem J p.1 p.2 h
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst

omit [Fintype ι] in
/-- For fixed `x`, `y ↦ piMerge J x y` is measurable. -/
private lemma measurable_piMerge_right (x : ∀ i, α i) : Measurable (piMerge J x) :=
  (measurable_piMerge J).comp (measurable_const.prodMk measurable_id)

/-- The splitting of `∀ i, α i` into the coordinates in `J` and those outside `J`
(Lemma 4.7 (a)). -/
private abbrev splitEquiv : (∀ i, α i) ≃ᵐ (∀ i : J, α i) × (∀ i : {i // i ∉ J}, α i) :=
  MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ J)

/-- The splitting equivalence carries `Measure.pi ν` to the product of the two partial product
laws (Lemma 4.7 (a)). -/
private lemma measurePreserving_splitEquiv :
    MeasurePreserving (splitEquiv (α := α) J) (Measure.pi ν)
      ((Measure.pi fun i : J => ν i).prod (Measure.pi fun i : {i // i ∉ J} => ν i)) :=
  measurePreserving_piEquivPiSubtypeProd ν (· ∈ J)

/-- The restriction to the coordinates outside `J` is measure preserving. -/
private lemma measurePreserving_restrict_compl :
    MeasurePreserving (fun x : ∀ i, α i => (splitEquiv J x).2) (Measure.pi ν)
      (Measure.pi fun i : {i // i ∉ J} => ν i) :=
  measurePreserving_snd.comp (measurePreserving_splitEquiv ν J)

/-- The restriction to the coordinates in `J` is measure preserving. -/
private lemma measurePreserving_restrict :
    MeasurePreserving (fun (x : ∀ i, α i) (i : J) => x i) (Measure.pi ν)
      (Measure.pi fun i : J => ν i) :=
  measurePreserving_fst.comp (measurePreserving_splitEquiv ν J)

/-- Lemma 4.7 (b): Tonelli. -/
theorem lintegral_partialLInt {f : (∀ i, α i) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (partialLInt ν J f) ∧
      ∫⁻ x, partialLInt ν J f x ∂Measure.pi ν = ∫⁻ x, f x ∂Measure.pi ν := by
  have hF : Measurable (fun p => f ((splitEquiv J).symm p)) :=
    hf.comp (splitEquiv J).symm.measurable
  have hG : Measurable fun z : (∀ i : {i // i ∉ J}, α i) =>
      ∫⁻ y, f ((splitEquiv J).symm (y, z)) ∂Measure.pi (fun i : J => ν i) :=
    hF.lintegral_prod_left'
  have hcomp : partialLInt ν J f = fun x => ∫⁻ y, f ((splitEquiv J).symm (y, (splitEquiv J x).2))
      ∂Measure.pi (fun i : J => ν i) := rfl
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hG.comp ((splitEquiv J).measurable.snd)
  · rw [hcomp]
    calc ∫⁻ x, ∫⁻ y, f ((splitEquiv J).symm (y, (splitEquiv J x).2))
          ∂Measure.pi (fun i : J => ν i) ∂Measure.pi ν
        = ∫⁻ z, ∫⁻ y, f ((splitEquiv J).symm (y, z)) ∂Measure.pi (fun i : J => ν i)
          ∂Measure.pi (fun i : {i // i ∉ J} => ν i) :=
          (measurePreserving_restrict_compl ν J).lintegral_comp hG
      _ = ∫⁻ p, f ((splitEquiv J).symm p)
          ∂(Measure.pi fun i : J => ν i).prod (Measure.pi fun i : {i // i ∉ J} => ν i) :=
          (lintegral_prod_symm' _ hF).symm
      _ = ∫⁻ x, f x ∂Measure.pi ν := by
          rw [← (measurePreserving_splitEquiv ν J).lintegral_comp hF]
          simp

/-- Lemma 4.7 (b): the conditional bound on an event. -/
theorem measure_le_of_slices {B : Set (∀ i, α i)} (hB : MeasurableSet B) {p : ℝ≥0∞}
    (h : ∀ x, Measure.pi (fun i : J => ν i) {y | piMerge J x y ∈ B} ≤ p) :
    Measure.pi ν B ≤ p := by
  have hf : Measurable (B.indicator (1 : (∀ i, α i) → ℝ≥0∞)) := measurable_one.indicator hB
  have hslice : ∀ x, partialLInt ν J (B.indicator 1) x =
      Measure.pi (fun i : J => ν i) {y | piMerge J x y ∈ B} := by
    intro x
    have hm : MeasurableSet {y | piMerge J x y ∈ B} := measurable_piMerge_right J x hB
    rw [← lintegral_indicator_one hm]
    unfold partialLInt
    refine lintegral_congr fun y => ?_
    by_cases hy : piMerge J x y ∈ B <;> simp [Set.indicator, hy]
  calc Measure.pi ν B = ∫⁻ x, B.indicator 1 x ∂Measure.pi ν := (lintegral_indicator_one hB).symm
    _ = ∫⁻ x, partialLInt ν J (B.indicator 1) x ∂Measure.pi ν :=
        (lintegral_partialLInt ν J hf).2.symm
    _ ≤ ∫⁻ _, p ∂Measure.pi ν := lintegral_mono fun x => by rw [hslice x]; exact h x
    _ = p := by simp

/-- Lemma 4.7 (c): Fubini. -/
theorem integral_partialInt {f : (∀ i, α i) → ℂ} (hf : Integrable f (Measure.pi ν)) :
    (∀ᵐ x ∂Measure.pi ν, Integrable (fun y => f (piMerge J x y)) (Measure.pi fun i : J => ν i)) ∧
      Integrable (partialInt ν J f) (Measure.pi ν) ∧
      ∫ x, partialInt ν J f x ∂Measure.pi ν = ∫ x, f x ∂Measure.pi ν := by
  have hmp := measurePreserving_splitEquiv (α := α) ν J
  have hF : Integrable (fun p => f ((splitEquiv J).symm p))
      ((Measure.pi fun i : J => ν i).prod (Measure.pi fun i : {i // i ∉ J} => ν i)) :=
    ((hmp.symm (splitEquiv J)).integrable_comp_emb
      (splitEquiv J).symm.measurableEmbedding).2 hf
  have hres := measurePreserving_restrict_compl ν J
  have hφ := hF.integral_prod_right
  have hcomp : partialInt ν J f = fun x => (fun z : (∀ i : {i // i ∉ J}, α i) =>
      ∫ y, f ((splitEquiv J).symm (y, z)) ∂Measure.pi (fun i : J => ν i)) (splitEquiv J x).2 :=
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hres.quasiMeasurePreserving.ae hF.prod_left_ae
  · rw [hcomp]
    exact (hres.integrable_comp hφ.aestronglyMeasurable).2 hφ
  · rw [hcomp]
    calc ∫ x, (fun z : (∀ i : {i // i ∉ J}, α i) =>
          ∫ y, f ((splitEquiv J).symm (y, z)) ∂Measure.pi (fun i : J => ν i))
          (splitEquiv J x).2 ∂Measure.pi ν
        = ∫ z, ∫ y, f ((splitEquiv J).symm (y, z)) ∂Measure.pi (fun i : J => ν i)
          ∂Measure.pi (fun i : {i // i ∉ J} => ν i) := by
          rw [← hres.map_eq]
          exact (integral_map hres.measurable.aemeasurable
            (by rw [hres.map_eq]; exact hφ.aestronglyMeasurable)).symm
      _ = ∫ p, f ((splitEquiv J).symm p)
          ∂(Measure.pi fun i : J => ν i).prod (Measure.pi fun i : {i // i ∉ J} => ν i) :=
          (integral_prod_symm _ hF).symm
      _ = ∫ x, f x ∂Measure.pi ν := by
          rw [← hmp.integral_comp' (fun p => f ((splitEquiv J).symm p))]
          simp

/-- Lemma 4.7 (d): a factor independent of the coordinates in `J`. -/
theorem integral_mul_partialInt {f g : (∀ i, α i) → ℂ} (hf : Integrable f (Measure.pi ν))
    (hgm : Measurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C)
    (hg : ∀ x x', (∀ i, i ∉ J → x i = x' i) → g x = g x') :
    (∀ x, partialInt ν J (fun w => g w * f w) x = g x * partialInt ν J f x) ∧
      ∫ x, g x * f x ∂Measure.pi ν = ∫ x, g x * partialInt ν J f x ∂Measure.pi ν := by
  have h1 : ∀ x, partialInt ν J (fun w => g w * f w) x = g x * partialInt ν J f x := by
    intro x
    unfold partialInt
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have : g (piMerge J x y) = g x :=
      hg _ _ fun i hi => piMerge_of_notMem J x y hi
    simp only [this]
  refine ⟨h1, ?_⟩
  have hgf : Integrable (fun w => g w * f w) (Measure.pi ν) :=
    hf.bdd_mul hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgC)
  calc ∫ x, g x * f x ∂Measure.pi ν
      = ∫ x, partialInt ν J (fun w => g w * f w) x ∂Measure.pi ν :=
        (integral_partialInt ν J hgf).2.2.symm
    _ = ∫ x, g x * partialInt ν J f x ∂Measure.pi ν := by simp only [h1]

/-- Lemma 4.7 (f): the tower property. -/
theorem partialLInt_tower {J₁ : Set ι} [DecidablePred (· ∈ J₁)] (hJ : J₁ ⊆ J)
    {f : (∀ i, α i) → ℝ≥0∞} (hf : Measurable f) :
    partialLInt ν J (partialLInt ν J₁ f) = partialLInt ν J f := by
  funext x
  have hr := measurePreserving_restrict (α := α) ν J
  have hrm : Measurable (fun (u : ∀ i, α i) (i : J) => u i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hmerge : Measurable (fun y : (∀ i : J, α i) => piMerge J x y) :=
    measurable_piMerge_right J x
  set h : (∀ i, α i) → ℝ≥0∞ := fun u => f (piMerge J x (fun i : J => u i)) with hh_def
  have hh : Measurable h := hf.comp (hmerge.comp hrm)
  have key : ∀ u : ∀ i, α i, partialLInt ν J₁ h u =
      partialLInt ν J₁ f (piMerge J x (fun i : J => u i)) := by
    intro u
    unfold partialLInt
    congr 1
    funext w
    simp only [hh_def]
    congr 1
    funext i
    by_cases hi₁ : i ∈ J₁
    · have hi : i ∈ J := hJ hi₁
      simp [piMerge, hi₁, hi]
    · by_cases hi : i ∈ J
      · simp [piMerge, hi₁, hi]
      · simp [piMerge, hi₁, hi]
  have hGm : Measurable fun y : (∀ i : J, α i) => partialLInt ν J₁ f (piMerge J x y) :=
    (lintegral_partialLInt ν J₁ hf).1.comp hmerge
  calc partialLInt ν J (partialLInt ν J₁ f) x
      = ∫⁻ y, partialLInt ν J₁ f (piMerge J x y) ∂Measure.pi (fun i : J => ν i) := rfl
    _ = ∫⁻ u, partialLInt ν J₁ f (piMerge J x (fun i : J => u i)) ∂Measure.pi ν :=
        (hr.lintegral_comp hGm).symm
    _ = ∫⁻ u, partialLInt ν J₁ h u ∂Measure.pi ν := by simp only [key]
    _ = ∫⁻ u, h u ∂Measure.pi ν := (lintegral_partialLInt ν J₁ hh).2
    _ = ∫⁻ y, f (piMerge J x y) ∂Measure.pi (fun i : J => ν i) :=
        hr.lintegral_comp (hf.comp hmerge)
    _ = partialLInt ν J f x := rfl

end Split

end Rigidity

namespace Rigidity

end Rigidity
