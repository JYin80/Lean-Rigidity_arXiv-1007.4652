import Rigidity.Fluctuation.Size

/-!
# One index tuple; counting tuples (NP v1.1, §6.6: Lemmas 6.12, 6.13)

Numbers in this file refer to the blueprint NP v1.1; [EYY, …] refers to the original paper
(Erdős–Yau–Yin, arXiv:1007.4652).
-/

/-! Both lemmas are steps in the proof of [EYY, Lemma 4.1]. An index tuple is
`𝐤 : Fin p → Fin N`; its position `s` is `s.val + 1` in the numbering of §6.6. -/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The number `ℓ(𝐤)` of lone positions of an index tuple `𝐤` (§6.6). -/
def loneCount {N p : ℕ} (k : Fin p → Fin N) : ℕ :=
  (Finset.univ.filter fun s => ∀ u, u ≠ s → k u ≠ k s).card

/-! ### Lemma 6.13 -/

section Count

variable {N p : ℕ}

/-- The smallest position `u` with `k u = k s`; it determines the block of `s` in the partition
of the positions into the level sets of `𝐤`. -/
private def tuple_rep (k : Fin p → Fin N) (s : Fin p) : Fin p :=
  (Finset.univ.filter fun u => k u = k s).min' ⟨s, by simp⟩

private lemma tuple_k_rep (k : Fin p → Fin N) (s : Fin p) : k (tuple_rep k s) = k s := by
  unfold tuple_rep
  exact (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter fun u => k u = k s) _)).2

private lemma tuple_rep_congr (k : Fin p → Fin N) {s s' : Fin p} (h : k s = k s') :
    tuple_rep k s = tuple_rep k s' := by
  have e : (Finset.univ.filter fun u => k u = k s) = Finset.univ.filter fun u => k u = k s' := by
    rw [h]
  unfold tuple_rep
  congr 1

/-- `2 r(𝐤) ≤ p + ℓ(𝐤)`: the blocks of size one are the lone positions, the others have size
at least two. -/
private lemma tuple_two_card_le (k : Fin p → Fin N) :
    2 * (Finset.univ.image k).card ≤ p + loneCount k := by
  classical
  set I := Finset.univ.image k with hI
  have hp : p = ∑ v ∈ I, (Finset.univ.filter fun s => k s = v).card := by
    simpa using Finset.card_eq_sum_card_image k (Finset.univ : Finset (Fin p))
  have hc1 : ∀ v ∈ I, 1 ≤ (Finset.univ.filter fun s => k s = v).card := by
    intro v hv
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.card_pos.2 ⟨s, by simp⟩
  have hsub : (I.filter fun v => (Finset.univ.filter fun s => k s = v).card = 1) ⊆
      (Finset.univ.filter fun s => ∀ u, u ≠ s → k u ≠ k s).image k := by
    intro v hv
    obtain ⟨-, hv1⟩ := Finset.mem_filter.1 hv
    obtain ⟨s, hs⟩ := Finset.card_eq_one.1 hv1
    have hks : k s = v := by
      have : s ∈ Finset.univ.filter fun s => k s = v := by
        rw [hs]; exact Finset.mem_singleton_self s
      exact (Finset.mem_filter.1 this).2
    refine Finset.mem_image.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun u hu huk => hu ?_⟩,
      hks⟩
    have : u ∈ Finset.univ.filter fun s => k s = v :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, huk.trans hks⟩
    rw [hs] at this
    exact Finset.mem_singleton.1 this
  have hl : (I.filter fun v => (Finset.univ.filter fun s => k s = v).card = 1).card ≤
      loneCount k :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 : ∑ _v ∈ I, 2 ≤ ∑ v ∈ I, ((Finset.univ.filter fun s => k s = v).card +
      if (Finset.univ.filter fun s => k s = v).card = 1 then 1 else 0) :=
    Finset.sum_le_sum fun v hv => by
      have := hc1 v hv
      split_ifs with h <;> omega
  rw [Finset.sum_add_distrib, Finset.sum_boole, ← hp, Finset.sum_const, smul_eq_mul] at h2
  simp only [Nat.cast_id] at h2
  omega

/-- The number of blocks is at most `r(𝐤)`. -/
private lemma tuple_card_rep_image_le (k : Fin p → Fin N) :
    (Finset.univ.image (tuple_rep k)).card ≤ (Finset.univ.image k).card := by
  classical
  refine Finset.card_le_card_of_injOn k (fun u _ => by simp) (fun u hu u' hu' h => ?_)
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hu)
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hu')
  rw [tuple_k_rep k s, tuple_k_rep k s'] at h
  exact tuple_rep_congr k h

/-- The tuples with a given block map `b` are determined by their values on the image of `b`. -/
private lemma tuple_card_fiber_le (ℓ : ℕ) (b : Fin p → Fin p) :
    ((Finset.univ.filter fun k : Fin p → Fin N => loneCount k = ℓ).filter
      fun k => tuple_rep k = b).card ≤ N ^ (Finset.univ.image b).card := by
  classical
  calc _ ≤ (Finset.univ : Finset (↥(Finset.univ.image b) → Fin N)).card :=
        Finset.card_le_card_of_injOn (fun k (u : ↥(Finset.univ.image b)) => k u.1)
          (fun _ _ => by simp) ?_
    _ = N ^ (Finset.univ.image b).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  intro k hk k' hk' h
  have hk2 : tuple_rep k = b := (Finset.mem_filter.1 (Finset.mem_coe.1 hk)).2
  have hk2' : tuple_rep k' = b := (Finset.mem_filter.1 (Finset.mem_coe.1 hk')).2
  funext s
  have hm : b s ∈ Finset.univ.image b := Finset.mem_image_of_mem b (Finset.mem_univ s)
  have := congrFun h ⟨b s, hm⟩
  simp only at this
  rw [← tuple_k_rep k s, ← tuple_k_rep k' s, hk2, hk2']
  exact this

/-- Lemma 6.13: `#{𝐤 : ℓ(𝐤) = ℓ} ≤ p^p N^{(p+ℓ)/2}` and `r(𝐤) ≤ ℓ(𝐤) + (p - ℓ(𝐤))/2`. -/
theorem card_tuples_le (N p ℓ : ℕ) (hℓ : ℓ ≤ p) :
    ((Finset.univ.filter fun k : Fin p → Fin N => loneCount k = ℓ).card : ℝ) ≤
        (p : ℝ) ^ p * (N : ℝ) ^ (((p : ℝ) + ℓ) / 2) ∧
      ∀ k : Fin p → Fin N,
        ((Finset.univ.image k).card : ℝ) ≤ loneCount k + ((p : ℝ) - loneCount k) / 2 := by
  classical
  refine ⟨?_, fun k => ?_⟩
  · set A := Finset.univ.filter fun k : Fin p → Fin N => loneCount k = ℓ with hAdef
    have hA : A.card = ∑ b : Fin p → Fin p, (A.filter fun k => tuple_rep k = b).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [hA, Nat.cast_sum]
    have hcard : (((Finset.univ : Finset (Fin p → Fin p)).card : ℕ) : ℝ) = (p : ℝ) ^ p := by
      simp [Finset.card_univ]
    rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun b _ => ?_
    rcases (A.filter fun k => tuple_rep k = b).eq_empty_or_nonempty with h | ⟨k, hk⟩
    · rw [h, Finset.card_empty, Nat.cast_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · obtain ⟨hkA, rfl⟩ := Finset.mem_filter.1 hk
      have hℓk : loneCount k = ℓ := (Finset.mem_filter.1 hkA).2
      have h1 := tuple_card_fiber_le (N := N) ℓ (tuple_rep k)
      have h2 := tuple_card_rep_image_le k
      have h3 := tuple_two_card_le k
      have hexp : ((Finset.univ.image (tuple_rep k)).card : ℝ) ≤ ((p : ℝ) + ℓ) / 2 := by
        rw [le_div_iff₀ (by norm_num)]
        have : (Finset.univ.image (tuple_rep k)).card * 2 ≤ p + ℓ := by omega
        exact_mod_cast this
      calc ((A.filter fun k' => tuple_rep k' = tuple_rep k).card : ℝ)
          ≤ (N : ℝ) ^ (Finset.univ.image (tuple_rep k)).card := by exact_mod_cast h1
        _ ≤ (N : ℝ) ^ (((p : ℝ) + ℓ) / 2) := by
          rcases Nat.eq_zero_or_pos N with hN | hN
          · subst hN
            have hp0 : p = 0 := by
              rcases Nat.eq_zero_or_pos p with h | h
              · exact h
              · exact (k ⟨0, h⟩).elim0
            subst hp0
            have hℓ0 : ℓ = 0 := by omega
            subst hℓ0
            simp
          · rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp
  · have h := tuple_two_card_le k
    have h' : (2 : ℝ) * (Finset.univ.image k).card ≤ p + loneCount k := by exact_mod_cast h
    linarith

end Count

/-! ### Integrable slices and linearity of `P_T` (Lemma 6.3 (F0)) -/

section Slices

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `1 + ∑ aᵢ ≤ ∏ (1 + aᵢ)` for nonnegative `aᵢ`. -/
private lemma tuple_one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
    have h2 := ha i
    nlinarith [mul_nonneg h2 h1, mul_nonneg h2 (sub_nonneg.2 ih)]

/-- `(1 + a)^m ≤ 2^m (1 + a^m)` for `a ≥ 0`. -/
private lemma tuple_one_add_pow_le {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (1 + a) ^ m ≤ 2 ^ m * (1 + a ^ m) := by
  have hp : 0 ≤ a ^ m := pow_nonneg ha m
  by_cases h : a ≤ 1
  · calc (1 + a) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + a ^ m) := le_mul_of_one_le_right (by positivity) (by linarith)
  · replace h := not_le.1 h
    calc (1 + a) ^ m ≤ (2 * a) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * a ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + a ^ m) := by gcongr; linarith

/-- Every power of `1 + |y|` is integrable against an entry law. -/
private lemma tuple_integrable_one_add_norm_pow {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (q : Pair N) (m : ℕ) :
    Integrable (fun y : 𝕜 => (1 + ‖y‖) ^ m) (M.law q) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hϑ' : 0 < min ϑ 1 := lt_min hϑ one_pos
  have hM' := Ensemble.Assumptions.mono M hM hϑ' (min_le_left _ _) le_rfl le_rfl le_rfl
  have hmom := (moments_bound hϑ' (min_le_right _ _) (μ := M.law q)
    (s := Real.sqrt (M.varPair q)) (Real.sqrt_nonneg _) (hM'.subexp q)
    (q := (m : ℝ)) (by exact_mod_cast hm)).1
  simp only [Real.rpow_natCast] at hmom
  have hdom : Integrable (fun y : 𝕜 => (2 : ℝ) ^ m * (1 + ‖y‖ ^ m)) (M.law q) :=
    ((integrable_const (1 : ℝ)).add hmom).const_mul _
  refine hdom.mono' ((measurable_const.add measurable_norm).pow_const m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact tuple_one_add_pow_le (norm_nonneg y) m

variable (J : Set (Pair N)) [DecidablePred (· ∈ J)]

/-- For fixed `x`, `y ↦ piMerge J x y` is measurable. -/
private lemma tuple_measurable_merge_right (x : Pair N → 𝕜) :
    Measurable (fun y : J → 𝕜 => piMerge J x y) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ J
  · simp only [piMerge, h]
    exact measurable_pi_apply _
  · simp only [piMerge, h]
    exact measurable_const

/-- The coordinates of `piMerge J x y` are bounded by those of `x` and `y`. -/
private lemma tuple_sum_norm_merge_le (x : Pair N → 𝕜) (y : J → 𝕜) :
    ∑ p, ‖piMerge J x y p‖ ≤ ∑ p, ‖x p‖ + ∑ q : J, ‖y q‖ := by
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun p => ‖piMerge J x y p‖)]
  have h1 : ∑ i : {p // p ∈ J}, ‖piMerge J x y i‖ = ∑ q : J, ‖y q‖ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [piMerge, i.2]
  have h2 : ∑ i : {p // ¬ p ∈ J}, ‖piMerge J x y i‖ ≤ ∑ p, ‖x p‖ := by
    have h3 : ∑ i : {p // ¬ p ∈ J}, ‖piMerge J x y i‖ = ∑ i : {p // ¬ p ∈ J}, ‖x i‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [piMerge, i.2]
    have h4 := Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun p => ‖x p‖)
    have h5 : 0 ≤ ∑ i : {p // p ∈ J}, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  linarith

/-- The polynomial bound along a slice `y ↦ f (piMerge J x y)`. -/
private lemma tuple_norm_merge_le {f : (Pair N → 𝕜) → ℂ} {c : ℝ} (hc : 0 ≤ c) {m : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m) (x : Pair N → 𝕜) (y : J → 𝕜) :
    ‖f (piMerge J x y)‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m := by
  have ha : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb : 0 ≤ ∑ q : J, ‖y q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : 1 + ∑ p, ‖piMerge J x y p‖ ≤ (1 + ∑ p, ‖x p‖) * (1 + ∑ q : J, ‖y q‖) := by
    nlinarith [tuple_sum_norm_merge_le J x y, mul_nonneg ha hb]
  have h2 : 1 + ∑ q : J, ‖y q‖ ≤ ∏ q : J, (1 + ‖y q‖) := by
    simpa using tuple_one_add_sum_le_prod_one_add Finset.univ (fun q : J => ‖y q‖)
      (fun _ => norm_nonneg _)
  have hs : 0 ≤ ∑ p, ‖piMerge J x y p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖f (piMerge J x y)‖ ≤ c * (1 + ∑ p, ‖piMerge J x y p‖) ^ m := hf _
    _ ≤ c * ((1 + ∑ p, ‖x p‖) * (∏ q : J, (1 + ‖y q‖))) ^ m := by
        gcongr
        exact h1.trans (by gcongr)
    _ = c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m := by
        rw [mul_pow, Finset.prod_pow]; ring

/-- Every slice of a function of `𝒜` is integrable (Lemma 6.3 (F0)). -/
private lemma tuple_integrable_slice {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (x : Pair N → 𝕜) :
    Integrable (fun y : J → 𝕜 => f (piMerge J x y)) (Measure.pi fun p : J => M.law p) := by
  obtain ⟨hfm, c₀, m, hb₀⟩ := hf
  have hc : 0 ≤ |c₀| := abs_nonneg _
  have hb : ∀ x, ‖f x‖ ≤ |c₀| * (1 + ∑ p, ‖x p‖) ^ m := fun x =>
    (hb₀ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hdom : Integrable
      (fun y : J → 𝕜 => |c₀| * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m)
      (Measure.pi fun p : J => M.law p) :=
    (Integrable.fintype_prod (f := fun (_ : J) (z : 𝕜) => (1 + ‖z‖) ^ m)
      (μ := fun q : J => M.law q) fun q =>
        tuple_integrable_one_add_norm_pow M hM hϑ q m).const_mul _
  exact hdom.mono' (hfm.comp (tuple_measurable_merge_right J x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => tuple_norm_merge_le J hc hb x y)

omit J in
/-- `P_T` commutes with finite sums on `𝒜`. -/
private lemma tuple_rowInt_sum {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (T : Finset (Fin N)) {α : Type*} (s : Finset α) {F : α → (Pair N → 𝕜) → ℂ}
    (hF : ∀ a ∈ s, PolyGrowth (F a)) (x : Pair N → 𝕜) :
    rowInt M T (fun w => ∑ a ∈ s, F a w) x = ∑ a ∈ s, rowInt M T (F a) x := by
  unfold rowInt partialInt
  exact integral_finsetSum s fun a ha => tuple_integrable_slice M (rowsQ T) hM hϑ (hF a ha) x

omit J in
/-- `|P_T f| ≤ ‖f‖_{1,T}`. -/
private lemma tuple_norm_rowInt_le (T : Finset (Fin N)) (f : (Pair N → 𝕜) → ℂ)
    (x : Pair N → 𝕜) : ‖rowInt M T f x‖ ≤ rowNorm M T 1 f x := by
  unfold rowInt partialInt rowNorm partialLInt
  simp only [ENNReal.rpow_one, div_one, Real.rpow_one]
  refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
  simp only [ofReal_norm]

omit J in
/-- `‖f‖_{q,T}` depends only on `|f|`. -/
private lemma tuple_rowNorm_congr_norm (T : Finset (Fin N)) (q : ℝ) {f g : (Pair N → 𝕜) → ℂ}
    (h : ∀ w, ‖f w‖ = ‖g w‖) (x : Pair N → 𝕜) : rowNorm M T q f x = rowNorm M T q g x := by
  have h' : ∀ w, ‖f w‖ₑ = ‖g w‖ₑ := fun w => by rw [← ofReal_norm, ← ofReal_norm, h w]
  simp only [rowNorm, h']

end Slices

/-! ### The class `𝒜` -/

section Classes

variable {N : ℕ}

private lemma tuple_pg_const (c : ℂ) : PolyGrowth (fun _ : Pair N → 𝕜 => c) :=
  ⟨measurable_const, ‖c‖, 0, fun x => by simp⟩

private lemma tuple_pg_sub {f g : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun w => f w - g w) := by
  have h := hf.add ((tuple_pg_const (-1)).mul hg)
  simpa [sub_eq_add_neg] using h

private lemma tuple_pg_prod {α : Type*} (s : Finset α) {F : α → (Pair N → 𝕜) → ℂ}
    (hF : ∀ a ∈ s, PolyGrowth (F a)) : PolyGrowth (fun w => ∏ a ∈ s, F a w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tuple_pg_const (N := N) (𝕜 := 𝕜) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).mul
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end Classes

/-! ### Lemma 6.12 -/

section Tuple

variable {N : ℕ}

/-- The map `f ↦ f^{#_s}` of §6.6: complex conjugation at the positions `s.val + 1 > p/2`. -/
private def tuple_conj (p : ℕ) (s : Fin p) : ℂ →+* ℂ :=
  if p / 2 ≤ s.val then starRingEnd ℂ else RingHom.id ℂ

private lemma tuple_norm_conj (p : ℕ) (s : Fin p) (a : ℂ) : ‖tuple_conj p s a‖ = ‖a‖ := by
  unfold tuple_conj
  split_ifs
  · exact Complex.norm_conj a
  · rfl

private lemma tuple_pg_conj (p : ℕ) (s : Fin p) {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) :
    PolyGrowth (fun w => tuple_conj p s (f w)) := by
  unfold tuple_conj
  split_ifs
  · exact hf.conj
  · exact hf

/-- The position `s` of an index tuple `𝐤` as an element of `L(𝐤)`. -/
private def tuple_idx {p : ℕ} (k : Fin p → Fin N) (s : Fin p) :
    (Finset.univ.image k : Finset (Fin N)) :=
  ⟨k s, Finset.mem_image_of_mem k (Finset.mem_univ s)⟩

/-- The terms `Y_k(ξ)` in the proof of Lemma 6.12: `ε(γ) Q_k W_k(γ)` for a path `ξ = γ`, and
`-Q_k R_k` for the remainder symbol `ξ = 𝔯` (written `none`). -/
private noncomputable def tuple_Y (M : Ensemble 𝕜 N) (L : Finset (Fin N)) (z : ℂ) (n₀ : ℕ)
    (c : L) : Option (List L) → (Pair N → 𝕜) → ℂ
  | some γ, w => (-1) ^ γ.length * (faW L z c γ w - rowInt M {c.1} (faW L z c γ) w)
  | none, w => -(faR L z c n₀ w - rowInt M {c.1} (faR L z c n₀) w)

/-- The weight `c^{-|γ|}` of a path `γ`, and `1` for the remainder symbol. -/
private noncomputable def tuple_u {L : Type*} (c : ℝ) : Option (List L) → ℝ
  | some γ => c⁻¹ ^ γ.length
  | none => 1

/-- The order `|γ| = o(γ) - 1` of a path `γ`, and `p` for the remainder symbol. -/
private def tuple_e {L : Type*} (p : ℕ) : Option (List L) → ℕ
  | some γ => γ.length
  | none => p

private lemma tuple_rowNorm_nonneg (M : Ensemble 𝕜 N) (T : Finset (Fin N)) (q : ℝ)
    (f : (Pair N → 𝕜) → ℂ) (x : Pair N → 𝕜) : 0 ≤ rowNorm M T q f x :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- The values at the lone positions are distinct: if every lone position `s` has its value
`k s` among the vertices of some `γ u`, `u ≠ s`, then `ℓ(𝐤) ≤ ∑_u |γ u|` (6.33). -/
private lemma tuple_lone_le_sum {p : ℕ} (k : Fin p → Fin N)
    (γ : Fin p → List (Finset.univ.image k : Finset (Fin N)))
    (h : ∀ s, (∀ u, u ≠ s → k u ≠ k s) → ∃ u, u ≠ s ∧ tuple_idx k s ∈ γ u) :
    loneCount k ≤ ∑ u, (γ u).length := by
  classical
  set Λ := Finset.univ.filter fun s => ∀ u, u ≠ s → k u ≠ k s
  have hinj : Set.InjOn k Λ := by
    intro s hs s' _ hss'
    by_contra hne
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hs)).2 s' (Ne.symm hne) hss'.symm
  have hsub : Λ.image k ⊆ Finset.univ.biUnion fun u => (γ u).toFinset.image Subtype.val := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨u, -, hu⟩ := h s (Finset.mem_filter.1 hs).2
    exact Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _,
      Finset.mem_image.2 ⟨tuple_idx k s, List.mem_toFinset.2 hu, rfl⟩⟩
  calc loneCount k = (Λ.image k).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ u, ((γ u).toFinset.image Subtype.val).card := Finset.card_biUnion_le
    _ ≤ ∑ u, (γ u).length := Finset.sum_le_sum fun u _ =>
        Finset.card_image_le.trans (List.toFinset_card_le _)

private lemma tuple_loneCount_le {p : ℕ} (k : Fin p → Fin N) : loneCount k ≤ p :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- Lemma 6.12: the bound for one index tuple `𝐤`, `L = L(𝐤)`, `ℓ = ℓ(𝐤)`, at a point of `Ξ_L`;
the factor of position `s` is conjugated when `s > p/2` (positions are `s.val + 1`). -/
theorem faTuple {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {p : ℕ} (hp : 2 ≤ p)
    (hpe : Even p) (hN : 8 ≤ N) (hlog : Real.log N ≤ p) (hpN : p < N) {z : ℂ}
    (hη : 1 / N ≤ z.im) (k : Fin p → Fin N) {x : Pair N → 𝕜}
    (hx : x ∈ faXiL M C₀ ϑ⁻¹ p (Finset.univ.image k) z) :
    ‖rowInt M (Finset.univ.image k) (fun w => ∏ s : Fin p,
        (if p / 2 ≤ s.val then starRingEnd ℂ else RingHom.id ℂ)
          (selfX (toMatrix w) M.varMatrix z (k s))) x‖ ≤
      (8 * p * faRho C₀ ϑ⁻¹ p (Finset.univ.image k) z x) ^ (p + loneCount k) := by
  classical
  set L := Finset.univ.image k with hLdef
  set n₀ := faN0 p N with hn₀
  set ρ := faRho C₀ ϑ⁻¹ p L z x with hρdef
  set ℓ := loneCount k with hℓdef
  set κ := tuple_idx k with hκ
  change ‖rowInt M L (fun w => ∏ s : Fin p, tuple_conj p s
      (selfX (toMatrix w) M.varMatrix z (κ s).1)) x‖ ≤ (8 * p * ρ) ^ (p + ℓ)
  have hNpos : 0 < N := by omega
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hp0 : 0 < p := by omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hpR2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hL1 : 1 ≤ L.card :=
    Finset.card_pos.2 ⟨k ⟨0, hp0⟩, Finset.mem_image_of_mem k (Finset.mem_univ _)⟩
  have hLp : L.card ≤ p := Finset.card_image_le.trans (by simp)
  have hLN : L.card < N := hLp.trans_lt hpN
  have hS := fun c : L => faSize M hM hϑ hϑ1 hp hpe hN hlog hη hL1 hLp hLN c hx
  have hE := fun c : L => inv_green_expansion M hM hϑ hz L c n₀
  have hnil : ∀ c : L, ([] : List L) ∈ faPath c n₀ := fun c =>
    expansion_mem_faPath.2 ⟨by simp, by simp, List.IsChain.nil⟩
  have hpρ : (p : ℝ) * ρ ≤ 1 / 8 := (hS (κ ⟨0, hp0⟩)).1
  have hρ0 : 0 ≤ ρ := by
    have h := (hS (κ ⟨0, hp0⟩)).2.1 [] (hnil _)
    rw [List.length_nil, zero_add, pow_one] at h
    linarith [tuple_rowNorm_nonneg M L p (fun w => faW L z (κ ⟨0, hp0⟩) [] w -
      rowInt M {(κ ⟨0, hp0⟩).1} (faW L z (κ ⟨0, hp0⟩) []) w) x]
  set c : ℝ := 8 * p with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcρ0 : 0 ≤ c * ρ := mul_nonneg hc0.le hρ0
  have hcρ1 : c * ρ ≤ 1 := by rw [hc]; linarith
  have hu0 : ∀ ξ : Option (List L), 0 ≤ tuple_u c ξ := fun ξ => by
    cases ξ with
    | none => simp [tuple_u]
    | some γ => exact pow_nonneg (inv_nonneg.2 hc0.le) _
  -- the terms are in the class `𝒜`
  have hYpg : ∀ (c' : L) (ξ : Option (List L)), PolyGrowth (tuple_Y M L z n₀ c' ξ) := by
    intro c' ξ
    cases ξ with
    | none =>
      have h := tuple_pg_sub (hE c').2.2.1 (rowInt_polyGrowth M hM hϑ {c'.1} (hE c').2.2.1)
      have h' := (tuple_pg_const (-1)).mul h
      simp only [neg_one_mul] at h'
      exact h'
    | some γ =>
      exact (tuple_pg_const _).mul
        (tuple_pg_sub ((hE c').2.1 γ) (rowInt_polyGrowth M hM hϑ {c'.1} ((hE c').2.1 γ)))
  set F : (Fin p → Option (List L)) → (Pair N → 𝕜) → ℂ :=
    fun ξ w => ∏ s, tuple_conj p s (tuple_Y M L z n₀ (κ s) (ξ s) w) with hF
  have hFpg : ∀ ξ, PolyGrowth (F ξ) := fun ξ =>
    tuple_pg_prod _ fun s _ => tuple_pg_conj p s (hYpg (κ s) (ξ s))
  -- (6.22) and the expansion (6.32)
  have hX : ∀ s w, selfX (toMatrix w) M.varMatrix z (κ s).1 =
      ∑ ξ ∈ Finset.insertNone (faPath (κ s) n₀), tuple_Y M L z n₀ (κ s) ξ w := by
    intro s w
    rw [Finset.sum_insertNone, (hE (κ s)).2.2.2.1 w]
    simp only [tuple_Y]
    ring
  have hint : (fun w => ∏ s : Fin p, tuple_conj p s (selfX (toMatrix w) M.varMatrix z (κ s).1)) =
      fun w => ∑ ξ ∈ Fintype.piFinset (fun s => Finset.insertNone (faPath (κ s) n₀)), F ξ w := by
    funext w
    simp only [hX, map_sum, hF]
    exact Finset.prod_univ_sum (fun s => Finset.insertNone (faPath (κ s) n₀))
      fun s ξ => tuple_conj p s (tuple_Y M L z n₀ (κ s) ξ w)
  rw [hint, tuple_rowInt_sum M hM hϑ L _ (fun ξ _ => hFpg ξ) x]
  -- Lemma 6.11 (b), (c) for one factor
  have hB : ∀ s, ∀ ξ ∈ Finset.insertNone (faPath (κ s) n₀),
      rowNorm M L p (fun w => tuple_conj p s (tuple_Y M L z n₀ (κ s) ξ w)) x ≤
        2 * ρ * (c * ρ) ^ tuple_e p ξ * tuple_u c ξ := by
    intro s ξ hξ
    rw [tuple_rowNorm_congr_norm M L p (fun w => tuple_norm_conj p s _) x]
    cases ξ with
    | none =>
      change rowNorm M L p (fun w => -(faR L z (κ s) n₀ w - rowInt M {(κ s).1}
        (faR L z (κ s) n₀) w)) x ≤ 2 * ρ * (c * ρ) ^ p * 1
      rw [tuple_rowNorm_congr_norm M L p (fun w => norm_neg _) x]
      refine ((hS (κ s)).2.2).trans ?_
      have hpρ0 : 0 ≤ (p : ℝ) * ρ := mul_nonneg (by positivity) hρ0
      have hLρ : (L.card : ℝ) * ρ ≤ p * ρ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hLp) hρ0
      have h8 : (p : ℝ) ≤ 8 ^ p := by
        have : p < 8 ^ p := Nat.lt_pow_self (by norm_num)
        exact_mod_cast this.le
      have h1 : ((p : ℝ) * ρ) ^ (p + 1) ≤ 1 := pow_le_one₀ hpρ0 (by linarith)
      have hA : 0 ≤ ((p : ℝ) * ρ) ^ p := pow_nonneg hpρ0 _
      have hABC : ((p : ℝ) * ρ) ^ p * ((p : ℝ) * ρ) ^ (p + 1) * ((p : ℝ) * ρ) ≤
          ((p : ℝ) * ρ) ^ p * 1 * (8 ^ p * ρ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_right h8 hρ0) hpρ0
          (by rw [mul_one]; exact hA)
      calc 2 * ((L.card : ℝ) * ρ) ^ (2 * p + 2) ≤ 2 * ((p : ℝ) * ρ) ^ (2 * p + 2) := by
            have := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hρ0) hLρ (2 * p + 2)
            linarith
        _ = 2 * (((p : ℝ) * ρ) ^ p * ((p : ℝ) * ρ) ^ (p + 1) * ((p : ℝ) * ρ)) := by ring
        _ ≤ 2 * (((p : ℝ) * ρ) ^ p * 1 * (8 ^ p * ρ)) := by linarith
        _ = 2 * ρ * (c * ρ) ^ p * 1 := by rw [hc]; ring
    | some γ =>
      have hγ : γ ∈ faPath (κ s) n₀ := Finset.mem_insertNone.1 hξ γ rfl
      change rowNorm M L p (fun w => (-1) ^ γ.length * (faW L z (κ s) γ w - rowInt M {(κ s).1}
        (faW L z (κ s) γ) w)) x ≤ 2 * ρ * (c * ρ) ^ γ.length * c⁻¹ ^ γ.length
      rw [tuple_rowNorm_congr_norm M L p
        (g := fun w => faW L z (κ s) γ w - rowInt M {(κ s).1} (faW L z (κ s) γ) w)
        (fun w => by simp) x]
      refine ((hS (κ s)).2.1 γ hγ).trans (le_of_eq ?_)
      have e1 : (c * ρ) ^ γ.length * c⁻¹ ^ γ.length = ρ ^ γ.length := by
        rw [← mul_pow, mul_comm c ρ, mul_assoc, mul_inv_cancel₀ hc0.ne', mul_one]
      rw [mul_assoc (2 * ρ), e1, pow_succ]
      ring
  -- the bound for one `𝛏`
  have hterm : ∀ ξ ∈ Fintype.piFinset (fun s => Finset.insertNone (faPath (κ s) n₀)),
      ‖rowInt M L (F ξ) x‖ ≤ (2 * ρ) ^ p * (c * ρ) ^ ℓ * ∏ s, tuple_u c (ξ s) := by
    intro ξ hξ
    have hξs := Fintype.mem_piFinset.1 hξ
    have hP : 0 ≤ ∏ s, tuple_u c (ξ s) := Finset.prod_nonneg fun s _ => hu0 _
    have hnn : 0 ≤ (2 * ρ) ^ p * (c * ρ) ^ ℓ * ∏ s, tuple_u c (ξ s) :=
      mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hcρ0 _)) hP
    have hsum1 : ∑ _i : Fin p, 1 / (p : ℝ) = 1 / 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hgen : ℓ ≤ ∑ s, tuple_e p (ξ s) →
        ‖rowInt M L (F ξ) x‖ ≤ (2 * ρ) ^ p * (c * ρ) ^ ℓ * ∏ s, tuple_u c (ξ s) := by
      intro hsum
      calc ‖rowInt M L (F ξ) x‖ ≤ rowNorm M L 1 (F ξ) x := tuple_norm_rowInt_le M L _ x
        _ ≤ ∏ s, rowNorm M L p (fun w => tuple_conj p s (tuple_Y M L z n₀ (κ s) (ξ s) w)) x :=
            rowNorm_prod_le M hM hϑ L Finset.univ
              (fun s w => tuple_conj p s (tuple_Y M L z n₀ (κ s) (ξ s) w)) (fun _ => (p : ℝ))
              le_rfl (fun _ _ => hpR) hsum1 (fun s _ => tuple_pg_conj p s (hYpg _ _)) x
        _ ≤ ∏ s, (2 * ρ * (c * ρ) ^ tuple_e p (ξ s) * tuple_u c (ξ s)) :=
            Finset.prod_le_prod₀ (fun s _ => tuple_rowNorm_nonneg M L _ _ x)
              (fun s _ => hB s (ξ s) (hξs s))
        _ = (2 * ρ) ^ p * (c * ρ) ^ (∑ s, tuple_e p (ξ s)) * ∏ s, tuple_u c (ξ s) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
              Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
        _ ≤ (2 * ρ) ^ p * (c * ρ) ^ ℓ * ∏ s, tuple_u c (ξ s) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hcρ0 hcρ1 hsum) (pow_nonneg (by linarith) _)) hP
    by_cases hnone : ∃ s, ξ s = none
    · obtain ⟨s₀, hs₀⟩ := hnone
      refine hgen ?_
      calc ℓ ≤ p := tuple_loneCount_le k
        _ = tuple_e p (ξ s₀) := by rw [hs₀]; rfl
        _ ≤ ∑ s, tuple_e p (ξ s) :=
            Finset.single_le_sum (f := fun s => tuple_e p (ξ s)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ s₀)
    · push Not at hnone
      set γ : Fin p → List L := fun s => (ξ s).getD [] with hγ
      have hξγ : ∀ s, ξ s = some (γ s) := fun s => by
        rcases h : ξ s with _ | g
        · exact absurd h (hnone s)
        · simp [hγ, h]
      by_cases hvan : ∃ s, (∀ u, u ≠ s → k u ≠ k s) ∧ ∀ u, u ≠ s → κ s ∉ γ u
      · -- the terms of `𝒳₀` vanish (Lemma 6.10 (b))
        obtain ⟨s, hlone, hnot⟩ := hvan
        have hFeq : F ξ = fun w => (∏ s, tuple_conj p s ((-1) ^ (γ s).length)) *
            ∏ s, tuple_conj p s (faW L z (κ s) (γ s) w -
              rowInt M {(κ s).1} (faW L z (κ s) (γ s)) w) := by
          funext w
          simp only [hF, hξγ, tuple_Y, map_mul, Finset.prod_mul_distrib]
        have hl := (rowInt_lone_eq_zero M hM hϑ hz L).2 p κ γ (fun s => decide (p / 2 ≤ s.val))
          ⟨s, fun u hu => ⟨fun h => hlone u hu (congrArg Subtype.val h).symm, hnot u hu⟩⟩ x
        have h0 : rowInt M L (fun w => ∏ s, tuple_conj p s (faW L z (κ s) (γ s) w -
            rowInt M {(κ s).1} (faW L z (κ s) (γ s)) w)) x = 0 := by
          simpa [tuple_conj] using hl
        rw [hFeq, rowInt_mul_left M L (g := fun _ => ∏ s, tuple_conj p s ((-1) ^ (γ s).length))
          (fun _ _ _ => rfl), h0, mul_zero, norm_zero]
        exact hnn
      · -- the terms of `𝒳₁` have total order at least `p + ℓ` (6.33)
        push Not at hvan
        refine hgen ?_
        calc ℓ ≤ ∑ s, (γ s).length := tuple_lone_le_sum k γ hvan
          _ = ∑ s, tuple_e p (ξ s) := Finset.sum_congr rfl fun s _ => by rw [hξγ s]; rfl
  -- summation over `𝛏`
  have hLc : (L.card : ℝ) * c⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hc0, hc]
    have : (L.card : ℝ) ≤ p := by exact_mod_cast hLp
    linarith
  have hsumu : ∀ s, ∑ ξ ∈ Finset.insertNone (faPath (κ s) n₀), tuple_u c ξ ≤ 3 := by
    intro s
    rw [Finset.sum_insertNone]
    simp only [tuple_u]
    have hgeo : ∑ γ ∈ faPath (κ s) n₀, c⁻¹ ^ γ.length ≤ 2 := by
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (n₀ + 1)) (g := List.length)
        (fun γ hγ => Finset.mem_range.2 (Nat.lt_succ_of_le (expansion_mem_faPath.1 hγ).1))]
      calc ∑ n ∈ Finset.range (n₀ + 1),
            ∑ γ ∈ (faPath (κ s) n₀).filter (fun γ => γ.length = n), c⁻¹ ^ γ.length
          = ∑ n ∈ Finset.range (n₀ + 1),
              (((faPath (κ s) n₀).filter (fun γ => γ.length = n)).card : ℝ) * c⁻¹ ^ n := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.sum_congr rfl fun γ hγ => by rw [(Finset.mem_filter.1 hγ).2],
              Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ n ∈ Finset.range (n₀ + 1), (1 / 2 : ℝ) ^ n := by
            refine Finset.sum_le_sum fun n _ => ?_
            have hcount := (hE (κ s)).2.2.2.2.2.1 (n + 1)
            have hfil : (faPath (κ s) n₀).filter (fun γ => γ.length + 1 = n + 1) =
                (faPath (κ s) n₀).filter (fun γ => γ.length = n) :=
              Finset.filter_congr fun γ _ => by omega
            rw [hfil, Nat.add_sub_cancel] at hcount
            calc (((faPath (κ s) n₀).filter (fun γ => γ.length = n)).card : ℝ) * c⁻¹ ^ n
                ≤ (L.card : ℝ) ^ n * c⁻¹ ^ n :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
                    (pow_nonneg (inv_nonneg.2 hc0.le) _)
              _ = ((L.card : ℝ) * c⁻¹) ^ n := (mul_pow _ _ _).symm
              _ ≤ (1 / 2) ^ n :=
                  pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hc0.le)) hLc n
        _ ≤ 2 := sum_geometric_two_le _
    linarith
  have hprod : ∏ s : Fin p, ∑ ξ ∈ Finset.insertNone (faPath (κ s) n₀), tuple_u c ξ ≤ 3 ^ p := by
    calc _ ≤ ∏ _s : Fin p, (3 : ℝ) :=
          Finset.prod_le_prod₀ (fun s _ => Finset.sum_nonneg fun ξ _ => hu0 ξ)
            (fun s _ => hsumu s)
      _ = 3 ^ p := by simp
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun s => Finset.insertNone (faPath (κ s) n₀))
    (fun _ ξ => tuple_u c ξ)]
  have h6 : 2 * ρ * 3 ≤ c * ρ := by rw [hc]; nlinarith
  calc (2 * ρ) ^ p * (c * ρ) ^ ℓ *
        ∏ s : Fin p, ∑ ξ ∈ Finset.insertNone (faPath (κ s) n₀), tuple_u c ξ
      ≤ (2 * ρ) ^ p * (c * ρ) ^ ℓ * 3 ^ p :=
        mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hcρ0 _))
    _ = (2 * ρ * 3) ^ p * (c * ρ) ^ ℓ := by rw [mul_pow (2 * ρ) 3 p]; ring
    _ ≤ (c * ρ) ^ p * (c * ρ) ^ ℓ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) h6 p) (pow_nonneg hcρ0 _)
    _ = (8 * p * ρ) ^ (p + ℓ) := by rw [← pow_add, hc]

end Tuple

end Rigidity
