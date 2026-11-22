module

public import Mathlib

@[expose] public section

/-!
# The Prékopa–Leindler inequality

Numbers refer to the blueprint NP v1.1; results of the original paper are cited as [EYY, …].

Theorem 17.1 (§17): for `τ ∈ (0, 1)` and measurable `u v w : ℝ^N → [0, ∞]` with
`u x ^ τ * v y ^ (1 - τ) ≤ w (τ x + (1 - τ) y)` for all `x, y`, one has
`(∫ u) ^ τ * (∫ v) ^ (1 - τ) ≤ ∫ w`.

The proof follows Steps 0–4 of the proof of Theorem 17.1:
* Step 1 and Step 2: the one-dimensional level-set inequality
  `|C| ≥ τ |A| + (1 - τ) |B|`, through inner regularity of Lebesgue measure on `ℝ`
  (no measurability of sumsets is needed);
* Step 3: the case `N = 1` for functions bounded by `1` with supremum `1`, by the layer-cake
  formula and the weighted arithmetic–geometric mean inequality;
* Step 0: reduction to bounded functions by normalisation and truncation;
* Step 4: induction on the dimension through the marginals in the first coordinate.

The statement also holds for `N = 0`, where `ℝ^0` is a point carrying the unit Dirac mass.
-/

open MeasureTheory Real
open scoped ENNReal NNReal

namespace Rigidity

/-- The statement of Theorem 17.1 in dimension `N` ([0, ∞]-valued functions). -/
def PLStatement (N : ℕ) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ < 1 → ∀ u v w : (Fin N → ℝ) → ℝ≥0∞,
    Measurable u → Measurable v → Measurable w →
    (∀ x y, u x ^ τ * v y ^ (1 - τ) ≤ w (τ • x + (1 - τ) • y)) →
    (∫⁻ x, u x) ^ τ * (∫⁻ x, v x) ^ (1 - τ) ≤ ∫⁻ x, w x

open scoped Pointwise in
/-- The image of `S ⊆ ℝ` under `x ↦ c x + d`, `c > 0`, has Lebesgue measure `c |S|`. -/
private lemma volume_image_affine {c : ℝ} (hc : 0 < c) (d : ℝ) (S : Set ℝ) :
    volume ((fun x => c * x + d) '' S) = ENNReal.ofReal c * volume S := by
  have h1 : (fun x => c * x + d) '' S = (fun x => x + d) '' (c • S) := by
    rw [← Set.image_smul, Set.image_image]; rfl
  rw [h1, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_smul,
    Module.finrank_self, pow_one, abs_of_pos hc]

/-- Step 1 of the proof of Theorem 17.1 in the form used by Step 2: if `τ a + (1 - τ) b ∈ C`
for all `a ∈ A`, `b ∈ B`, then for `α ∈ A`, `β ∈ B`,
`|C| ≥ τ |A ∩ (-∞, α]| + (1 - τ) |B ∩ [β, ∞)|`. -/
private lemma level_bound {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {A B C : Set ℝ}
    (hC : ∀ a ∈ A, ∀ b ∈ B, τ * a + (1 - τ) * b ∈ C) {α β : ℝ} (hα : α ∈ A) (hβ : β ∈ B) :
    ENNReal.ofReal τ * volume (A ∩ Set.Iic α) + ENNReal.ofReal (1 - τ) * volume (B ∩ Set.Ici β)
      ≤ volume C := by
  have h1' : 0 < 1 - τ := sub_pos.2 h1
  set p := τ * α + (1 - τ) * β with hp
  have hp' : p = (1 - τ) * β + τ * α := by rw [hp]; ring
  rw [← volume_image_affine h0 ((1 - τ) * β), ← volume_image_affine h1' (τ * α),
    ← measure_inter_add_sdiff C (measurableSet_Iic : MeasurableSet (Set.Iic p))]
  refine add_le_add (measure_mono ?_) ?_
  · rintro _ ⟨x, ⟨hxA, hxα⟩, rfl⟩
    refine ⟨hC x hxA β hβ, ?_⟩
    have : τ * x ≤ τ * α := mul_le_mul_of_nonneg_left hxα h0.le
    simp only [Set.mem_Iic, hp]
    linarith
  · rw [← measure_sdiff_null (s := (fun y => (1 - τ) * y + τ * α) '' (B ∩ Set.Ici β))
      (measure_singleton p)]
    apply measure_mono
    rintro _ ⟨⟨y, ⟨hyB, hyβ⟩, rfl⟩, hne⟩
    refine ⟨by change (1 - τ) * y + τ * α ∈ C; rw [add_comm]; exact hC α hα y hyB, ?_⟩
    have : (1 - τ) * β ≤ (1 - τ) * y := mul_le_mul_of_nonneg_left hyβ h1'.le
    simp only [Set.mem_singleton_iff] at hne
    simp only [Set.mem_Iic, not_le]
    exact lt_of_le_of_ne (by rw [hp]; linarith) (Ne.symm hne)

/-- Inner regularity on `ℝ`, restricted to sets of the form `A ∩ (-∞, α]` with `α ∈ A`. -/
private lemma volume_eq_iSup_Iic {A : Set ℝ} (hA : MeasurableSet A) :
    volume A = ⨆ α : A, volume (A ∩ Set.Iic (α : ℝ)) := by
  refine le_antisymm ?_ (iSup_le fun α => measure_mono Set.inter_subset_left)
  rw [hA.measure_eq_iSup_isCompact]
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · refine le_iSup_of_le ⟨sSup K, hKA (hK.sSup_mem hne)⟩ (measure_mono ?_)
    exact fun x hx => ⟨hKA hx, le_csSup hK.bddAbove hx⟩

/-- Inner regularity on `ℝ`, restricted to sets of the form `B ∩ [β, ∞)` with `β ∈ B`. -/
private lemma volume_eq_iSup_Ici {B : Set ℝ} (hB : MeasurableSet B) :
    volume B = ⨆ β : B, volume (B ∩ Set.Ici (β : ℝ)) := by
  refine le_antisymm ?_ (iSup_le fun β => measure_mono Set.inter_subset_left)
  rw [hB.measure_eq_iSup_isCompact]
  refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hK => ?_
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · refine le_iSup_of_le ⟨sInf K, hKB (hK.sInf_mem hne)⟩ (measure_mono ?_)
    exact fun x hx => ⟨hKB hx, csInf_le hK.bddBelow hx⟩

/-- Step 2 of the proof of Theorem 17.1: for nonempty Borel `A, B ⊆ ℝ` and any `C ⊆ ℝ` with
`τ a + (1 - τ) b ∈ C` for all `a ∈ A`, `b ∈ B`, `|C| ≥ τ |A| + (1 - τ) |B|`. -/
private lemma level_sets {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hC : ∀ a ∈ A, ∀ b ∈ B, τ * a + (1 - τ) * b ∈ C) :
    ENNReal.ofReal τ * volume A + ENNReal.ofReal (1 - τ) * volume B ≤ volume C := by
  have := hAn.to_subtype
  have := hBn.to_subtype
  rw [volume_eq_iSup_Iic hA, volume_eq_iSup_Ici hB, ENNReal.mul_iSup, ENNReal.mul_iSup]
  exact ENNReal.iSup_add_iSup_le fun α β => level_bound h0 h1 hC α.2 β.2

/-- The layer-cake formula `∫ f = ∫_0^∞ |{f > t}| dt` for finite-valued measurable
`f : ℝ → [0, ∞]`. -/
private lemma lintegral_eq_meas_lt {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hfin : ∀ x, f x ≠ ⊤) :
    ∫⁻ x, f x = ∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t < f x} := by
  have h := lintegral_eq_lintegral_meas_lt volume (f := fun x => (f x).toReal)
    (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg) hf.ennreal_toReal.aemeasurable
  simp only [ENNReal.ofReal_toReal (hfin _)] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  congr 1
  ext x
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hfin x)).symm

/-- Step 3 of the proof of Theorem 17.1 (the case `N = 1`) for `u, v ≤ 1` with
`sup u = sup v = 1`, before the arithmetic–geometric mean step:
`∫ w ≥ τ ∫ u + (1 - τ) ∫ v`. -/
private lemma pl1_normalized {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {u v w : ℝ → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (hu1 : ∀ x, u x ≤ 1) (hv1 : ∀ x, v x ≤ 1)
    (husup : ∀ r < 1, ∃ x, r < u x) (hvsup : ∀ r < 1, ∃ x, r < v x)
    (h : ∀ x y, u x ^ τ * v y ^ (1 - τ) ≤ w (τ * x + (1 - τ) * y)) :
    ENNReal.ofReal τ * (∫⁻ x, u x) + ENNReal.ofReal (1 - τ) * (∫⁻ x, v x) ≤ ∫⁻ x, w x := by
  have h1' : 0 < 1 - τ := sub_pos.2 h1
  have fin1 : ∀ {a : ℝ≥0∞}, a ≤ 1 → a ≠ ⊤ := fun ha => ne_top_of_le_ne_top ENNReal.one_ne_top ha
  calc ENNReal.ofReal τ * (∫⁻ x, u x) + ENNReal.ofReal (1 - τ) * (∫⁻ x, v x)
      = ENNReal.ofReal τ * (∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t < u x})
        + ENNReal.ofReal (1 - τ) * (∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t < v x}) := by
        rw [lintegral_eq_meas_lt hu fun x => fin1 (hu1 x),
          lintegral_eq_meas_lt hv fun x => fin1 (hv1 x)]
    _ ≤ ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal τ * volume {x | ENNReal.ofReal t < u x}
        + ENNReal.ofReal (1 - τ) * volume {x | ENNReal.ofReal t < v x}) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact le_lintegral_add _ _
    _ ≤ ∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t < min (w x) 1} := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        rcases lt_or_ge t 1 with ht1 | ht1
        · have hr : ENNReal.ofReal t < 1 := ENNReal.ofReal_lt_one.2 ht1
          refine level_sets h0 h1 (measurableSet_lt measurable_const hu)
            (measurableSet_lt measurable_const hv) (husup _ hr) (hvsup _ hr) ?_
          intro a ha b hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          refine lt_min ?_ hr
          calc ENNReal.ofReal t = ENNReal.ofReal t ^ τ * ENNReal.ofReal t ^ (1 - τ) := by
                rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top]
                simp
            _ < u a ^ τ * v b ^ (1 - τ) :=
                ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow ha h0) (ENNReal.rpow_lt_rpow hb h1')
            _ ≤ w (τ * a + (1 - τ) * b) := h a b
        · have hr : 1 ≤ ENNReal.ofReal t := ENNReal.one_le_ofReal.2 ht1
          have hA : {x | ENNReal.ofReal t < u x} = ∅ :=
            Set.eq_empty_of_forall_notMem fun x hx => absurd ((hu1 x).trans hr) (not_le.2 hx)
          have hB : {x | ENNReal.ofReal t < v x} = ∅ :=
            Set.eq_empty_of_forall_notMem fun x hx => absurd ((hv1 x).trans hr) (not_le.2 hx)
          simp [hA, hB]
    _ = ∫⁻ x, min (w x) 1 :=
        (lintegral_eq_meas_lt (hw.min measurable_const) fun x => fin1 (min_le_right _ _)).symm
    _ ≤ ∫⁻ x, w x := lintegral_mono fun x => min_le_left _ _

/-- The weighted arithmetic–geometric mean inequality `a ^ τ b ^ (1 - τ) ≤ τ a + (1 - τ) b`
on `[0, ∞]`. -/
private lemma amgm {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (a b : ℝ≥0∞) :
    a ^ τ * b ^ (1 - τ) ≤ ENNReal.ofReal τ * a + ENNReal.ofReal (1 - τ) * b := by
  have h := ENNReal.geom_mean_le_arith_mean2_weighted τ.toNNReal (1 - τ).toNNReal a b
    (by rw [← Real.toNNReal_add h0 (sub_nonneg.2 h1)]; simp)
  rwa [Real.coe_toNNReal _ h0, Real.coe_toNNReal _ (sub_nonneg.2 h1)] at h

/-- Normalisation identity for `a, b ∈ (0, ∞)`:
`(p a⁻¹) ^ τ (q b⁻¹) ^ (1 - τ) = p ^ τ q ^ (1 - τ) (a ^ τ b ^ (1 - τ))⁻¹`. -/
private lemma normalize_eq {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {a b : ℝ≥0∞}
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (p q : ℝ≥0∞) :
    (p * a⁻¹) ^ τ * (q * b⁻¹) ^ (1 - τ)
      = p ^ τ * q ^ (1 - τ) * (a ^ τ * b ^ (1 - τ))⁻¹ := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0.le, ENNReal.mul_rpow_of_nonneg _ _ (sub_pos.2 h1).le,
    ENNReal.inv_rpow, ENNReal.inv_rpow,
    ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hat).ne')
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg h0.le hat)),
    mul_mul_mul_comm]

/-- Step 3 together with the normalisation of Step 0 in the proof of Theorem 17.1: the case
`N = 1` for `u, v` with finite suprema. -/
private lemma pl1_bounded {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {u v w : ℝ → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (hub : ⨆ x, u x ≠ ⊤) (hvb : ⨆ x, v x ≠ ⊤)
    (h : ∀ x y, u x ^ τ * v y ^ (1 - τ) ≤ w (τ * x + (1 - τ) * y)) :
    (∫⁻ x, u x) ^ τ * (∫⁻ x, v x) ^ (1 - τ) ≤ ∫⁻ x, w x := by
  have h1' : 0 < 1 - τ := sub_pos.2 h1
  rcases eq_or_ne (∫⁻ x, u x) 0 with hu0 | hu0
  · rw [hu0, ENNReal.zero_rpow_of_pos h0, zero_mul]; exact zero_le
  rcases eq_or_ne (∫⁻ x, v x) 0 with hv0 | hv0
  · rw [hv0, ENNReal.zero_rpow_of_pos h1', mul_zero]; exact zero_le
  set a := ⨆ x, u x with ha
  set b := ⨆ x, v x with hb
  have ha0 : a ≠ 0 := by
    intro ha'
    apply hu0
    have : ∀ x, u x = 0 := fun x => le_antisymm (ha' ▸ le_iSup u x) zero_le
    simp [this]
  have hb0 : b ≠ 0 := by
    intro hb'
    apply hv0
    have : ∀ x, v x = 0 := fun x => le_antisymm (hb' ▸ le_iSup v x) zero_le
    simp [this]
  set c := a ^ τ * b ^ (1 - τ) with hc
  have hc0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h0.le hub)
      (ENNReal.rpow_ne_top_of_nonneg h1'.le hvb))
  have hct : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2
    (mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hub).ne'
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hvb).ne')
  -- the normalised functions
  have le1 : ∀ {f : ℝ → ℝ≥0∞} {s : ℝ≥0∞}, s = ⨆ x, f x → s ≠ 0 → s ≠ ⊤ →
      ∀ x, f x * s⁻¹ ≤ 1 := by
    intro f s hs hs0 hst x
    calc f x * s⁻¹ ≤ s * s⁻¹ := mul_le_mul' (hs ▸ le_iSup f x) le_rfl
      _ = 1 := ENNReal.mul_inv_cancel hs0 hst
  have sup1 : ∀ {f : ℝ → ℝ≥0∞} {s : ℝ≥0∞}, s = ⨆ x, f x → s ≠ 0 → s ≠ ⊤ →
      ∀ r < 1, ∃ x, r < f x * s⁻¹ := by
    intro f s hs hs0 hst r hr
    have hrs : r * s < s := by
      simpa using ENNReal.mul_lt_mul_left hs0 hst hr
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 (lt_of_lt_of_eq hrs hs)
    refine ⟨x, ?_⟩
    calc r = r * s * s⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hs0 hst, mul_one]
      _ < f x * s⁻¹ :=
        ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hst) (ENNReal.inv_ne_top.2 hs0) hx
  have key := pl1_normalized h0 h1 (hu.mul_const a⁻¹) (hv.mul_const b⁻¹) (hw.mul_const c⁻¹)
    (le1 ha ha0 hub) (le1 hb hb0 hvb) (sup1 ha ha0 hub) (sup1 hb hb0 hvb)
    (fun x y => by
      rw [normalize_eq h0 h1 ha0 hub]
      exact mul_le_mul' (h x y) le_rfl)
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 ha0),
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hb0), lintegral_mul_const' _ _ hct] at key
  have := (amgm h0.le h1.le _ _).trans key
  rw [normalize_eq h0 h1 ha0 hub] at this
  exact (ENNReal.mul_le_mul_iff_left hc0 hct).1 this

/-- Theorem 17.1 for `N = 1`, stated on `ℝ` (Step 0 truncation applied to the bounded case). -/
private lemma pl1 {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {u v w : ℝ → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
    (h : ∀ x y, u x ^ τ * v y ^ (1 - τ) ≤ w (τ * x + (1 - τ) * y)) :
    (∫⁻ x, u x) ^ τ * (∫⁻ x, v x) ^ (1 - τ) ≤ ∫⁻ x, w x := by
  have h1' : 0 < 1 - τ := sub_pos.2 h1
  have trunc : ∀ {f : ℝ → ℝ≥0∞}, Measurable f →
      ∫⁻ x, f x = ⨆ k : ℕ, ∫⁻ x, min (f x) (k : ℝ≥0∞) := by
    intro f hf
    rw [← lintegral_iSup (fun k => hf.min measurable_const)
      (fun k l hkl x => min_le_min_left _ (Nat.cast_le.2 hkl))]
    congr 1
    ext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]
    exact (inf_top_eq _).symm
  have mono : ∀ (f : ℝ → ℝ≥0∞), Monotone fun k : ℕ => ∫⁻ x, min (f x) (k : ℝ≥0∞) :=
    fun f k l hkl => lintegral_mono fun x => min_le_min_left _ (Nat.cast_le.2 hkl)
  have hk : ∀ k : ℕ, (∫⁻ x, min (u x) (k : ℝ≥0∞)) ^ τ * (∫⁻ x, min (v x) (k : ℝ≥0∞)) ^ (1 - τ)
      ≤ ∫⁻ x, w x := fun k =>
    pl1_bounded h0 h1 (hu.min measurable_const) (hv.min measurable_const) hw
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) (iSup_le fun x => min_le_right _ _))
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) (iSup_le fun x => min_le_right _ _))
      (fun x y => (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) h0.le)
        (ENNReal.rpow_le_rpow (min_le_left _ _) h1'.le)).trans (h x y))
  have rpow_iSup : ∀ {s : ℝ} (hs : 0 < s) (g : ℕ → ℝ≥0∞), (⨆ k, g k) ^ s = ⨆ k, g k ^ s := by
    intro s hs g
    exact (ENNReal.orderIsoRpow s hs).map_iSup g
  rw [trunc hu, trunc hv, rpow_iSup h0, rpow_iSup h1', ENNReal.iSup_mul]
  refine iSup_le fun k => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun l => ?_
  calc (∫⁻ x, min (u x) (k : ℝ≥0∞)) ^ τ * (∫⁻ x, min (v x) (l : ℝ≥0∞)) ^ (1 - τ)
      ≤ (∫⁻ x, min (u x) ((max k l : ℕ) : ℝ≥0∞)) ^ τ
        * (∫⁻ x, min (v x) ((max k l : ℕ) : ℝ≥0∞)) ^ (1 - τ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (mono u (le_max_left k l)) h0.le)
          (ENNReal.rpow_le_rpow (mono v (le_max_right k l)) h1'.le)
    _ ≤ ∫⁻ x, w x := hk _

/-- Theorem 17.1 in dimension `0`: `ℝ^0` is a point with the unit Dirac mass. -/
private lemma pl_zero : PLStatement 0 := by
  intro τ _ _ u v w _ _ _ h
  rw [volume_pi, Measure.pi_of_empty, lintegral_dirac, lintegral_dirac, lintegral_dirac]
  set p : Fin 0 → ℝ := fun a => isEmptyElim a
  exact (h p p).trans_eq (congrArg w (Subsingleton.elim _ _))

/-- Step 4 of the proof of Theorem 17.1: the statement in dimension `N` implies the statement
in dimension `N + 1`, through the marginals in the first coordinate. -/
private lemma pl_succ {N : ℕ} (ih : PLStatement N) : PLStatement (N + 1) := by
  intro τ h0 h1 u v w hu hv hw h
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0
  have he : MeasurePreserving e.symm volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0).symm
  have split : ∀ f : (Fin (N + 1) → ℝ) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x = ∫⁻ a, ∫⁻ x', f (e.symm (a, x')) := by
    intro f hf
    rw [← he.lintegral_comp_emb e.symm.measurableEmbedding]
    exact lintegral_prod _ (hf.comp e.symm.measurable).aemeasurable
  have hlin : ∀ (a b : ℝ) (x y : Fin N → ℝ),
      τ • e.symm (a, x) + (1 - τ) • e.symm (b, y)
        = e.symm (τ * a + (1 - τ) * b, τ • x + (1 - τ) • y) := by
    intro a b x y
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
      Fin.insertNth_zero']
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  rw [split u hu, split v hv, split w hw]
  refine pl1 h0 h1 (hu.comp e.symm.measurable).lintegral_prod_right'
    (hv.comp e.symm.measurable).lintegral_prod_right'
    (hw.comp e.symm.measurable).lintegral_prod_right' fun a b => ?_
  exact ih τ h0 h1 (fun x => u (e.symm (a, x))) (fun y => v (e.symm (b, y)))
    (fun z => w (e.symm (τ * a + (1 - τ) * b, z)))
    (hu.comp (e.symm.measurable.comp measurable_prodMk_left))
    (hv.comp (e.symm.measurable.comp measurable_prodMk_left))
    (hw.comp (e.symm.measurable.comp measurable_prodMk_left))
    (fun x y => by rw [← hlin]; exact h _ _)

/-- Theorem 17.1 (Prékopa–Leindler). -/
theorem prekopaLeindler (N : ℕ) : PLStatement N := by
  induction N with
  | zero => exact pl_zero
  | succ N ih => exact pl_succ ih

end Rigidity
