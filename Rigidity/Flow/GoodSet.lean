module

public import Rigidity.Ensemble.Basic
public import Rigidity.LocalLaw.Defs
public import Rigidity.Semicircle.Density
public import Rigidity.Semicircle.Locations
public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# The good set of eigenvalue vectors and its deterministic consequences

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file contains:
* the rigidity bound of Theorem 2.2 for one tuple of constants, as a predicate (`RigidityBound`);
* the empirical counting function `𝔫_x` of §12.1, the parameter `D` of (13.2), `ϱ*` of §12.1, and
  the good set `Ξ` of (13.3) (`flowGoodSet`);
* the existence of the threshold `N_*` of (13.2) (`exists_Nstar`);
* Lemma 13.C: the measurability of `x ↦ sup_{|e| ≤ a} |𝔫_x(e) - n_sc(e)|` and of `Ξ`;
* Lemma 13.4: on `Ξ`, the local density bound (a), the bulk localisation of eigenvalues (b), and
  the bounds on the index sets `J` and `𝓑` (c).

Indices of eigenvalues and classical locations are `0`-based: the paper's `x_j` and `γ_j` are
`x (j - 1)` and `gamma N (j - 1)`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- (RA1) for one tuple `(A₀, C, c, φ, N₀)`: both events of Theorem 2.2. -/
def RigidityBound (𝕜 : Type*) [RCLike 𝕜] (ϑ δm δp C₀ A₀ C c φ : ℝ) (N₀ : ℕ) : Prop :=
  1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
  ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ → ∀ L : ℝ, LRange A₀ N L →
    M.prodLaw {x | ∃ k : Fin N, Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) *
        (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |eig x k - gamma N k|} ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
    M.prodLaw {x | Real.log N ^ L / N ≤ ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L)))

/-- `𝔫_x(e) = N⁻¹ #{j : x_j ≤ e}` (§12.1). -/
noncomputable def empCount {N : ℕ} (x : Fin N → ℝ) (e : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ((Finset.univ.filter fun k => x k ≤ e).card : ℝ)

/-- `D = (log N)^L + 2` with `L = A₀ log log N` (13.2). -/
noncomputable def Dpar (A₀ : ℝ) (N : ℕ) : ℝ := Real.log N ^ (A₀ * Real.log (Real.log N)) + 2

/-- The good set `Ξ` (13.3), with the closed chamber written as `Monotone x`. -/
def flowGoodSet (N : ℕ) (D : ℝ) : Set (Fin N → ℝ) :=
  {x | Monotone x ∧ (⨆ e : Set.Icc (-4 : ℝ) 4, |empCount x e - nsc e|) ≤ D / N ∧
    ∀ k, |x k - gamma N k| ≤ D * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))}

/-- `ϱ*(c) = (2π)⁻¹ √(c - c²/16)` (§12.1). -/
noncomputable def rhoStar (c : ℝ) : ℝ := (2 * π)⁻¹ * Real.sqrt (c - c ^ 2 / 16)



/-! ### Elementary facts on `empCount` and `n_sc` -/

private lemma goodSet_empCount_eq_sum {N : ℕ} (x : Fin N → ℝ) (e : ℝ) :
    empCount x e = (N : ℝ)⁻¹ * ∑ k, if x k ≤ e then (1 : ℝ) else 0 := by
  unfold empCount
  rw [Finset.natCast_card_filter]

private lemma goodSet_empCount_nonneg {N : ℕ} (x : Fin N → ℝ) (e : ℝ) : 0 ≤ empCount x e := by
  unfold empCount
  positivity

private lemma goodSet_empCount_le_one {N : ℕ} (x : Fin N → ℝ) (e : ℝ) : empCount x e ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp [empCount]
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    unfold empCount
    rw [← div_eq_inv_mul, div_le_one hN]
    have := Finset.card_le_univ (Finset.univ.filter fun k : Fin N => x k ≤ e)
    rw [Fintype.card_fin] at this
    exact_mod_cast this

/-- `n_sc` takes values in `[0, 1]`. -/
private lemma goodSet_nsc_mem (E : ℝ) : 0 ≤ nsc E ∧ nsc E ≤ 1 := by
  obtain ⟨-, hmono, -, hlow, hhigh, -, -, -⟩ := nsc_props
  constructor
  · rcases le_total E (-2) with h | h
    · rw [hlow E h]
    · calc (0 : ℝ) = nsc (-2) := (hlow _ le_rfl).symm
        _ ≤ nsc E := hmono h
  · rcases le_total 2 E with h | h
    · rw [hhigh E h]
    · calc nsc E ≤ nsc 2 := hmono h
        _ = 1 := hhigh 2 le_rfl

private lemma goodSet_continuous_nsc : Continuous nsc :=
  continuous_iff_continuousAt.2 fun E => (nsc_props.1 E).continuousAt

private lemma goodSet_abs_le_one {N : ℕ} (x : Fin N → ℝ) (e : ℝ) :
    |empCount x e - nsc e| ≤ 1 := by
  have h1 := goodSet_empCount_nonneg x e
  have h2 := goodSet_empCount_le_one x e
  have h3 := goodSet_nsc_mem e
  rw [abs_le]
  constructor <;> linarith [h3.1, h3.2]

private lemma goodSet_bddAbove {N : ℕ} (x : Fin N → ℝ) (a : ℝ) :
    BddAbove (Set.range fun e : Set.Icc (-a) a => |empCount x e - nsc e|) :=
  ⟨1, by rintro _ ⟨e, rfl⟩; exact goodSet_abs_le_one x e⟩

/-- `e ↦ 𝔫_x(e)` is right-continuous. -/
private lemma goodSet_empCount_tendsto {N : ℕ} (x : Fin N → ℝ) (e : ℝ) :
    Tendsto (fun e' => empCount x e') (𝓝[>] e) (𝓝 (empCount x e)) := by
  have hk : ∀ k : Fin N, ∀ᶠ e' in 𝓝[>] e, (x k ≤ e' ↔ x k ≤ e) := by
    intro k
    by_cases h : x k ≤ e
    · filter_upwards [self_mem_nhdsWithin] with e' he'
      exact ⟨fun _ => h, fun _ => h.trans (le_of_lt he')⟩
    · rw [not_le] at h
      have : Set.Iio (x k) ∈ 𝓝[>] e := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)
      filter_upwards [this] with e' he'
      exact ⟨fun hh => absurd hh (not_le.mpr he'), fun hh => absurd hh (not_le.mpr h)⟩
  have hev : ∀ᶠ e' in 𝓝[>] e, empCount x e' = empCount x e := by
    filter_upwards [Filter.eventually_all.mpr hk] with e' he'
    unfold empCount
    congr 3
    ext k
    simp [he' k]
  exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)

private lemma goodSet_abs_tendsto {N : ℕ} (x : Fin N → ℝ) (e : ℝ) :
    Tendsto (fun e' => |empCount x e' - nsc e'|) (𝓝[>] e) (𝓝 |empCount x e - nsc e|) :=
  ((goodSet_empCount_tendsto x e).sub
    ((goodSet_continuous_nsc.tendsto e).mono_left nhdsWithin_le_nhds)).abs

private lemma goodSet_measurable_abs (N : ℕ) (e : ℝ) :
    Measurable fun x : Fin N → ℝ => |empCount x e - nsc e| := by
  have : Measurable fun x : Fin N → ℝ => ∑ k, if x k ≤ e then (1 : ℝ) else 0 :=
    Finset.measurable_sum _ fun k _ =>
      Measurable.ite (measurableSet_le (measurable_pi_apply k) measurable_const)
        measurable_const measurable_const
  have h2 : Measurable fun x : Fin N → ℝ => empCount x e := by
    simp_rw [goodSet_empCount_eq_sum]
    exact measurable_const.mul this
  exact (h2.sub measurable_const).abs

/-- Lemma 13.C. -/
theorem measurable_iSup_empCount (N : ℕ) (a : ℝ) :
    Measurable fun x : Fin N → ℝ => ⨆ e : Set.Icc (-a) a, |empCount x e - nsc e| := by
  rcases lt_or_ge a 0 with ha | ha
  · have : IsEmpty (Set.Icc (-a) a) := by
      rw [Set.isEmpty_coe_sort]
      exact Set.Icc_eq_empty (by linarith)
    simp
  · -- the supremum over `[-a, a]` equals the supremum over the countable set `S`
    set S : Set ℝ := {e | e ∈ Set.Icc (-a) a ∧ (e = a ∨ ∃ q : ℚ, (q : ℝ) = e)} with hS
    have hSc : S.Countable := by
      refine (Set.countable_singleton a |>.union (Set.countable_range ((↑) : ℚ → ℝ))).mono ?_
      rintro e ⟨-, h | ⟨q, hq⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, hq⟩
    have : Countable S := hSc.to_subtype
    have : Nonempty S := ⟨⟨a, ⟨by linarith, le_rfl⟩, Or.inl rfl⟩⟩
    have : Nonempty (Set.Icc (-a) a) := ⟨⟨a, by linarith, le_rfl⟩⟩
    have heq : ∀ x : Fin N → ℝ, (⨆ e : Set.Icc (-a) a, |empCount x e - nsc e|) =
        ⨆ s : S, |empCount x s - nsc s| := by
      intro x
      have hbddS : BddAbove (Set.range fun s : S => |empCount x s - nsc s|) :=
        ⟨1, by rintro _ ⟨s, rfl⟩; exact goodSet_abs_le_one x s⟩
      apply le_antisymm
      · refine ciSup_le fun e => ?_
        rcases e.2.2.eq_or_lt with he | he
        · exact le_ciSup hbddS ⟨e.1, e.2, Or.inl he⟩
        · refine le_of_forall_pos_le_add fun ε hε => ?_
          have h1 := (goodSet_abs_tendsto x e.1).eventually_const_lt
            (sub_lt_self |empCount x e.1 - nsc e.1| hε)
          have h2 : Set.Ioo e.1 a ∈ 𝓝[>] e.1 := Ioo_mem_nhdsGT he
          obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (Filter.inter_mem h1 h2)
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show e.1 < u from hu)
          obtain ⟨hqa, hqb⟩ := hsub ⟨hq1, hq2⟩
          have hqa' : |empCount x e.1 - nsc e.1| - ε < |empCount x (q : ℝ) - nsc (q : ℝ)| := hqa
          have hqmem : (q : ℝ) ∈ S :=
            ⟨⟨by linarith [e.2.1], hqb.2.le⟩, Or.inr ⟨q, rfl⟩⟩
          have := le_ciSup hbddS ⟨(q : ℝ), hqmem⟩
          simp only at this
          linarith
      · refine ciSup_le fun s => ?_
        exact le_ciSup (goodSet_bddAbove x a) ⟨s.1, s.2.1⟩
    simp_rw [heq]
    exact Measurable.iSup fun s => goodSet_measurable_abs N s

theorem measurableSet_flowGoodSet (N : ℕ) (D : ℝ) : MeasurableSet (flowGoodSet N D) := by
  have h1 : MeasurableSet {x : Fin N → ℝ | Monotone x} := by
    have : {x : Fin N → ℝ | Monotone x} = ⋂ a : Fin N, ⋂ b : Fin N, ⋂ (_ : a ≤ b),
        {x | x a ≤ x b} := by
      ext x; simp [Monotone]
    rw [this]
    exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b)
  have h2 : MeasurableSet {x : Fin N → ℝ | (⨆ e : Set.Icc (-4 : ℝ) 4, |empCount x e - nsc e|) ≤
      D / N} :=
    measurableSet_le (measurable_iSup_empCount N 4) measurable_const
  have h3 : MeasurableSet {x : Fin N → ℝ | ∀ k, |x k - gamma N k| ≤
      D * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))} := by
    have : {x : Fin N → ℝ | ∀ k, |x k - gamma N k| ≤
        D * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))} =
        ⋂ k : Fin N, {x | |x k - gamma N k| ≤
          D * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))} := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le (((measurable_pi_apply k).sub measurable_const).abs) measurable_const
  exact h1.inter (h2.inter h3)

/-! ### Lemma 13.4 -/

private lemma goodSet_rhoStar_pos {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) : 0 < rhoStar c := by
  unfold rhoStar
  have : 0 < c - c ^ 2 / 16 := by nlinarith
  positivity

/-- `ϱ*(c) ≤ 1 / π` for `c ≤ 2`. -/
private lemma goodSet_rhoStar_le {c : ℝ} (hc2 : c ≤ 2) : rhoStar c ≤ 1 / π := by
  unfold rhoStar
  have h : Real.sqrt (c - c ^ 2 / 16) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  calc (2 * π)⁻¹ * Real.sqrt (c - c ^ 2 / 16) ≤ (2 * π)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / π := by field_simp

/-- On `[-(2 - c/4), 2 - c/4]` the density `ϱ_sc` is at least `ϱ*(c)` (Lemma 3.4 (d)), so
`n_sc` grows at least linearly with slope `ϱ*(c)` there. -/
private lemma goodSet_nsc_sub_ge {c p q : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) (hpq : p ≤ q)
    (hp : -(2 - c / 4) ≤ p) (hq : q ≤ 2 - c / 4) : rhoStar c * (q - p) ≤ nsc q - nsc p := by
  rcases hpq.eq_or_lt with h | h
  · subst h; simp
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope nsc rhoSc h
    goodSet_continuous_nsc.continuousOn (fun x _ => nsc_props.1 x)
  have hb : rhoStar c ≤ rhoSc ξ := by
    have := rhoSc_bulk hc hc2 (x := ξ)
      (abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩)
    simpa [rhoStar, one_div] using this
  rw [hξeq, le_div_iff₀ (sub_pos.2 h)] at hb
  linarith

/-- `x ∈ Ξ` gives the counting bound `|#{j : x_j ≤ e} - N n_sc(e)| ≤ D` for `|e| ≤ 4`. -/
private lemma goodSet_abs_cnt_le {N : ℕ} (hN : 0 < N) {D : ℝ} {x : Fin N → ℝ}
    (hx : x ∈ flowGoodSet N D) {e : ℝ} (he : e ∈ Set.Icc (-4 : ℝ) 4) :
    |((Finset.univ.filter fun j => x j ≤ e).card : ℝ) - N * nsc e| ≤ D := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := le_trans (le_ciSup (goodSet_bddAbove x 4) ⟨e, he⟩) hx.2.1
  simp only at h
  have h2 : ((Finset.univ.filter fun j => x j ≤ e).card : ℝ) - N * nsc e =
      N * (empCount x e - nsc e) := by
    unfold empCount
    field_simp
  rw [h2, abs_mul, abs_of_pos hNR]
  calc (N : ℝ) * |empCount x e - nsc e| ≤ N * (D / N) := mul_le_mul_of_nonneg_left h hNR.le
    _ = D := by field_simp

/-- The number of `x_i` in `(u, w]` is `N (𝔫_x(w) - 𝔫_x(u))`. -/
private lemma goodSet_card_Ioc {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) {u w : ℝ} (huw : u ≤ w) :
    (N : ℝ) * (empCount x w - empCount x u) =
      ((Finset.univ.filter fun i => u < x i ∧ x i ≤ w).card : ℝ) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have key : (∑ k, if x k ≤ w then (1 : ℝ) else 0) =
      (∑ k, if x k ≤ u then (1 : ℝ) else 0) +
        ∑ k, if u < x k ∧ x k ≤ w then (1 : ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : x k ≤ u
    · have h2 : x k ≤ w := h1.trans huw
      simp [h1, h2, not_lt.mpr h1]
    · by_cases h2 : x k ≤ w
      · simp [h1, h2, not_le.mp h1]
      · simp [h1, h2]
  rw [goodSet_empCount_eq_sum, goodSet_empCount_eq_sum, key, Finset.natCast_card_filter]
  field_simp
  ring

/-- Lemma 13.4 (a): local density on `Ξ`. -/
theorem card_near_le_of_mem_flowGoodSet {N : ℕ} (hN : 3 ≤ N) {D c ℓ : ℝ} (hD : 0 ≤ D) (hc : 0 < c)
    (hc2 : c ≤ 2) (hℓ : 0 < ℓ) (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) {x : Fin N → ℝ}
    (hx : x ∈ flowGoodSet N D) {e : ℝ} (he : e ∈ Set.Icc (-3 : ℝ) 3) :
    ((Finset.univ.filter fun i => |x i - e| ≤ ℓ / N).card : ℝ) ≤ 2 * ℓ / π + 2 * D := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hρ := goodSet_rhoStar_pos hc hc2
  have hρ1 := goodSet_rhoStar_le hc2
  have hH' : D + ℓ ≤ N * rhoStar c * (c / 8) := by
    have := (div_le_iff₀ (by positivity : 0 < (N : ℝ) * rhoStar c)).mp hH
    linarith
  have hπ := Real.pi_gt_three
  have hρ2 : rhoStar c < 1 := lt_of_le_of_lt hρ1 ((div_lt_one Real.pi_pos).mpr (by linarith))
  have hℓN : ℓ / N < 1 := by
    rw [div_lt_one hNR]
    have : rhoStar c * (c / 8) < 1 := by nlinarith
    nlinarith
  have hℓN0 : 0 < ℓ / N := div_pos hℓ hNR
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η : ℝ := min (ε * π / N) ((1 - ℓ / N) / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  have hη1 : η < 1 - ℓ / N := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hη2 : (N : ℝ) * η / π ≤ ε := by
    have : η ≤ ε * π / N := min_le_left _ _
    rw [div_le_iff₀ Real.pi_pos]
    calc (N : ℝ) * η ≤ N * (ε * π / N) := mul_le_mul_of_nonneg_left this hNR.le
      _ = ε * π := by field_simp
  set u : ℝ := e - ℓ / N - η with hu
  set w : ℝ := e + ℓ / N with hw
  have huw : u ≤ w := by linarith
  have hu4 : u ∈ Set.Icc (-4 : ℝ) 4 := ⟨by linarith [he.1], by linarith [he.2]⟩
  have hw4 : w ∈ Set.Icc (-4 : ℝ) 4 := ⟨by linarith [he.1], by linarith [he.2]⟩
  have hsub : (Finset.univ.filter fun i => |x i - e| ≤ ℓ / N) ⊆
      Finset.univ.filter fun i => u < x i ∧ x i ≤ w := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨h1, h2⟩ := abs_le.mp hi
    exact ⟨by linarith, by linarith⟩
  have hcard := Finset.card_le_card hsub
  have hcardR : ((Finset.univ.filter fun i => |x i - e| ≤ ℓ / N).card : ℝ) ≤
      ((Finset.univ.filter fun i => u < x i ∧ x i ≤ w).card : ℝ) := by exact_mod_cast hcard
  rw [← goodSet_card_Ioc hNpos x huw] at hcardR
  have hbu := abs_le.mp (goodSet_abs_cnt_le hNpos hx hu4)
  have hbw := abs_le.mp (goodSet_abs_cnt_le hNpos hx hw4)
  have hlip : nsc w - nsc u ≤ (w - u) / π := by
    have := nsc_props.2.2.1 w u
    rw [abs_of_nonneg (by linarith : 0 ≤ w - u)] at this
    exact le_trans (le_abs_self _) this
  have hmul : (N : ℝ) * (empCount x w - empCount x u) ≤ N * (nsc w - nsc u) + 2 * D := by
    have e1 : (N : ℝ) * empCount x w = ((Finset.univ.filter fun j => x j ≤ w).card : ℝ) := by
      unfold empCount; field_simp
    have e2 : (N : ℝ) * empCount x u = ((Finset.univ.filter fun j => x j ≤ u).card : ℝ) := by
      unfold empCount; field_simp
    rw [mul_sub, e1, e2]
    linarith [hbu.1, hbu.2, hbw.1, hbw.2]
  have hNlip : (N : ℝ) * (nsc w - nsc u) ≤ (2 * ℓ + N * η) / π := by
    calc (N : ℝ) * (nsc w - nsc u) ≤ N * ((w - u) / π) := mul_le_mul_of_nonneg_left hlip hNR.le
      _ = (2 * ℓ + N * η) / π := by rw [hw, hu]; field_simp; ring
  have : (2 * ℓ + N * η) / π = 2 * ℓ / π + N * η / π := by ring
  linarith

/-- The bulk step of Lemma 13.4 (b): if `p ∈ [-2 + 3c/8, 2 - 3c/8]` and `|n_sc(q) - n_sc(p)| ≤ δ`
with `δ < ϱ*(c) c / 8`, then `|q - p| ≤ δ / ϱ*(c)`. -/
private lemma goodSet_bulk_step {c δ p q : ℝ} (hc : 0 < c) (hc2 : c ≤ 2)
    (hp : p ∈ Set.Icc (-2 + 3 / 8 * c) (2 - 3 / 8 * c)) (hδ : δ < rhoStar c * (c / 8))
    (hpq : |nsc q - nsc p| ≤ δ) : |q - p| ≤ δ / rhoStar c := by
  have hρ := goodSet_rhoStar_pos hc hc2
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨h1, h2⟩ := abs_le.mp hpq
  have hmono := nsc_props.2.1
  have hup : q ≤ p + c / 8 := by
    by_contra h
    rw [not_le] at h
    have h3 := goodSet_nsc_sub_ge (c := c) (p := p) (q := p + c / 8) hc hc2 (by linarith)
      (by linarith) (by linarith)
    have h4 := hmono h.le
    nlinarith
  have hdn : p - c / 8 ≤ q := by
    by_contra h
    rw [not_le] at h
    have h3 := goodSet_nsc_sub_ge (c := c) (p := p - c / 8) (q := p) hc hc2 (by linarith)
      (by linarith) (by linarith)
    have h4 := hmono h.le
    nlinarith
  rw [le_div_iff₀ hρ]
  rcases le_total q p with hqp | hpq'
  · have h3 := goodSet_nsc_sub_ge (c := c) (p := q) (q := p) hc hc2 hqp (by linarith)
      (by linarith)
    rw [abs_of_nonpos (by linarith : q - p ≤ 0)]
    nlinarith
  · have h3 := goodSet_nsc_sub_ge (c := c) (p := p) (q := q) hc hc2 hpq' (by linarith)
      (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ q - p)]
    nlinarith

/-- If `y ∈ [-2 + 3c/8, 2 - 3c/8]`, then `ϱ*(c) c / 8 ≤ n_sc(y) ≤ 1 - ϱ*(c) c / 8`. -/
private lemma goodSet_nsc_bulk {c y : ℝ} (hc : 0 < c) (hc2 : c ≤ 2)
    (hy : y ∈ Set.Icc (-2 + 3 / 8 * c) (2 - 3 / 8 * c)) :
    rhoStar c * (c / 8) ≤ nsc y ∧ nsc y ≤ 1 - rhoStar c * (c / 8) := by
  obtain ⟨-, hmono, -, -, -, -, hneg, -⟩ := nsc_props
  have h0 := (goodSet_nsc_mem (-2 + c / 4)).1
  have h1 := goodSet_nsc_sub_ge (c := c) (p := -2 + c / 4) (q := -2 + 3 / 8 * c) hc hc2
    (by linarith) (by linarith) (by linarith)
  have h2 : nsc (-2 + 3 / 8 * c) ≤ nsc y := hmono hy.1
  have h3 : nsc y ≤ nsc (2 - 3 / 8 * c) := hmono hy.2
  have h4 : nsc (2 - 3 / 8 * c) = 1 - nsc (-2 + 3 / 8 * c) := by
    have := hneg (2 - 3 / 8 * c)
    rw [show -(2 - 3 / 8 * c) = -2 + 3 / 8 * c by ring] at this
    linarith
  have h5 : (-2 + 3 / 8 * c) - (-2 + c / 4) = c / 8 := by ring
  rw [h5] at h1
  constructor <;> linarith

/-- The number of `j` with `x_j ≤ e` is at most `i` when `x_i > e` and `x` is monotone. -/
private lemma goodSet_cnt_lt {N : ℕ} {x : Fin N → ℝ} (hx : Monotone x) (i : Fin N) {e : ℝ}
    (he : e < x i) : (Finset.univ.filter fun j => x j ≤ e).card ≤ i.val := by
  calc (Finset.univ.filter fun j => x j ≤ e).card ≤ (Finset.Iio i).card := by
        refine Finset.card_le_card fun j hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at hj ⊢
        by_contra h
        rw [not_lt] at h
        exact absurd (hx h) (not_le.mpr (lt_of_le_of_lt hj he))
    _ = i.val := Fin.card_Iio i

/-- The number of `j` with `x_j ≤ e` is at least `i + 1` when `x_i ≤ e` and `x` is monotone. -/
private lemma goodSet_cnt_ge {N : ℕ} {x : Fin N → ℝ} (hx : Monotone x) (i : Fin N) {e : ℝ}
    (he : x i ≤ e) : i.val + 1 ≤ (Finset.univ.filter fun j => x j ≤ e).card := by
  calc i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
    _ ≤ (Finset.univ.filter fun j => x j ≤ e).card := by
        refine Finset.card_le_card fun j hj => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at hj ⊢
        exact (hx hj).trans he

/-- Lemma 13.4 (b): bulk localisation on `Ξ`. -/
theorem abs_sub_gamma_le_of_mem_flowGoodSet {N : ℕ} (hN : 3 ≤ N) {D c ℓ : ℝ} (hD : 0 ≤ D)
    (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ) (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8)
    {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) (i : Fin N)
    (hi : x i ∈ Set.Icc (-2 + 3 / 8 * c) (2 - 3 / 8 * c) ∨
      gamma N i ∈ Set.Icc (-2 + 3 / 8 * c) (2 - 3 / 8 * c)) :
    |x i - gamma N i| ≤ D / (N * rhoStar c) := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hρ := goodSet_rhoStar_pos hc hc2
  have hH' : D + ℓ ≤ N * rhoStar c * (c / 8) := by
    have := (div_le_iff₀ (by positivity : 0 < (N : ℝ) * rhoStar c)).mp hH
    linarith
  -- `D < N ϱ* c / 8`, i.e. `D / N < ϱ* c / 8`
  have hDlt : D < N * (rhoStar c * (c / 8)) := by nlinarith
  have hδ : D / N < rhoStar c * (c / 8) := by rwa [div_lt_iff₀ hNR, mul_comm]
  have hmono := hx.1
  have hgam := nsc_gamma i
  set y := x i with hy
  -- `|y| ≤ 4`
  have hy4 : y ∈ Set.Icc (-4 : ℝ) 4 := by
    rcases hi with hb | hb
    · exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    · obtain ⟨hn1, hn2⟩ := goodSet_nsc_bulk hc hc2 hb
      have hn1' : D < N * nsc (gamma N i) := by nlinarith
      have hn2' : D < N - N * nsc (gamma N i) := by nlinarith
      constructor
      · by_contra h
        rw [not_le] at h
        have hc1 := goodSet_cnt_ge hmono i (e := -4) h.le
        have hb4 := abs_le.mp (goodSet_abs_cnt_le hNpos hx (e := -4) ⟨le_rfl, by norm_num⟩)
        rw [(nsc_props.2.2.2.1 (-4) (by norm_num) : nsc (-4) = 0)] at hb4
        have : (i.val + 1 : ℝ) ≤ ((Finset.univ.filter fun j => x j ≤ -4).card : ℝ) := by
          exact_mod_cast hc1
        linarith [hb4.2]
      · by_contra h
        rw [not_le] at h
        have hc1 := goodSet_cnt_lt hmono i (e := 4) h
        have hb4 := abs_le.mp (goodSet_abs_cnt_le hNpos hx (e := 4) ⟨by norm_num, le_rfl⟩)
        rw [(nsc_props.2.2.2.2.1 4 (by norm_num) : nsc 4 = 1)] at hb4
        have : ((Finset.univ.filter fun j => x j ≤ 4).card : ℝ) ≤ i.val := by
          exact_mod_cast hc1
        linarith [hb4.1]
  -- `|N n_sc(y) - (i + 1)| ≤ D`
  have hlow : (i.val + 1 : ℝ) - D ≤ N * nsc y := by
    have hc1 := goodSet_cnt_ge hmono i (e := y) le_rfl
    have hb := abs_le.mp (goodSet_abs_cnt_le hNpos hx hy4)
    have : (i.val + 1 : ℝ) ≤ ((Finset.univ.filter fun j => x j ≤ y).card : ℝ) := by
      exact_mod_cast hc1
    linarith [hb.2]
  have hup : N * nsc y ≤ i.val + D := by
    rcases hy4.1.eq_or_lt with h | h
    · rw [← h, (nsc_props.2.2.2.1 (-4) (by norm_num) : nsc (-4) = 0)]
      have : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      linarith
    · have hev : ∀ᶠ e in 𝓝[<] y, N * nsc e ≤ i.val + D := by
        filter_upwards [Ioo_mem_nhdsLT h] with e he
        have hc1 := goodSet_cnt_lt hmono i (e := e) he.2
        have hb := abs_le.mp (goodSet_abs_cnt_le hNpos hx (e := e)
          ⟨he.1.le, he.2.le.trans hy4.2⟩)
        have : ((Finset.univ.filter fun j => x j ≤ e).card : ℝ) ≤ i.val := by
          exact_mod_cast hc1
        linarith [hb.1]
      exact le_of_tendsto
        (((goodSet_continuous_nsc.tendsto y).const_mul (N : ℝ)).mono_left nhdsWithin_le_nhds) hev
  have hny : |nsc y - nsc (gamma N i)| ≤ D / N := by
    rw [abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hNR]
      nlinarith
    · rw [le_div_iff₀ hNR]
      nlinarith
  have hfin : |x i - gamma N i| ≤ (D / N) / rhoStar c := by
    rcases hi with hb | hb
    · have := goodSet_bulk_step (q := gamma N i) hc hc2 hb hδ (by rwa [abs_sub_comm] at hny)
      rwa [abs_sub_comm] at this
    · exact goodSet_bulk_step (q := y) hc hc2 hb hδ hny
  rwa [div_div] at hfin

/-- The number of classical locations in `[t - r, t + r]` is at most `N (2 r) / π + 1`
(Lemma 3.4 (e)). -/
private lemma goodSet_card_gamma_near {N : ℕ} (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((Finset.univ.filter fun i : Fin N => |gamma N i - t| ≤ r).card : ℝ) ≤
      N * (2 * r) / π + 1 := by
  have h := card_gamma_mem_le (N := N) (a := t - r) (b := t + r) (I := {y | |y - t| ≤ r})
    (by linarith) (fun y (hy : |y - t| ≤ r) => by
      obtain ⟨h1, h2⟩ := abs_le.mp hy
      exact ⟨by linarith, by linarith⟩)
  have e : (Finset.univ.filter fun i : Fin N => |gamma N i - t| ≤ r).card =
      {k : Fin N | gamma N k ∈ {y | |y - t| ≤ r}}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext k
    simp
  rw [e]
  have e2 : (N : ℝ) * (t + r - (t - r)) / π = N * (2 * r) / π := by ring
  rwa [e2] at h

/-- Lemma 13.4 (c): the index sets `J` and `𝓑`. -/
theorem card_indexSets_le {N : ℕ} (hN : 3 ≤ N) {D c ℓ : ℝ} (hD : 0 ≤ D) (hc : 0 < c)
    (hc2 : c ≤ 2) (hℓ : 0 < ℓ) (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) {E b : ℝ}
    (hE : E ∈ Set.Icc (-2 + c) (2 - c)) (hb : 0 < b) (hb2 : b < c / 2) :
    ((Finset.univ.filter fun i => gamma N i ∈ Set.Icc (E - b) (E + b)).card : ℝ) ≤
        2 * N * b / π + 1 ∧
      ((Finset.univ.filter fun i => min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤
          D / (N * rhoStar c) + ℓ / N).card : ℝ) ≤ 4 * (D / rhoStar c + ℓ) / π + 2 := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hρ := goodSet_rhoStar_pos hc hc2
  constructor
  · have h := goodSet_card_gamma_near (N := N) E hb.le
    have e : (Finset.univ.filter fun i : Fin N => gamma N i ∈ Set.Icc (E - b) (E + b)) =
        Finset.univ.filter fun i : Fin N => |gamma N i - E| ≤ b := by
      refine Finset.filter_congr fun i _ => ?_
      rw [Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [e]
    have e2 : (N : ℝ) * (2 * b) / π = 2 * N * b / π := by ring
    rwa [e2] at h
  · set r : ℝ := D / (N * rhoStar c) + ℓ / N with hr
    have hr0 : 0 ≤ r := by positivity
    have hsub : (Finset.univ.filter fun i : Fin N =>
          min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ r) ⊆
        (Finset.univ.filter fun i : Fin N => |gamma N i - (E - b)| ≤ r) ∪
          (Finset.univ.filter fun i : Fin N => |gamma N i - (E + b)| ≤ r) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, min_le_iff] at hi ⊢
      exact hi
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcardR : ((Finset.univ.filter fun i : Fin N =>
          min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ r).card : ℝ) ≤
        ((Finset.univ.filter fun i : Fin N => |gamma N i - (E - b)| ≤ r).card : ℝ) +
          ((Finset.univ.filter fun i : Fin N => |gamma N i - (E + b)| ≤ r).card : ℝ) := by
      exact_mod_cast hcard
    have h1 := goodSet_card_gamma_near (N := N) (E - b) hr0
    have h2 := goodSet_card_gamma_near (N := N) (E + b) hr0
    have hNr : (N : ℝ) * r = D / rhoStar c + ℓ := by
      rw [hr]
      field_simp
    have : (N : ℝ) * (2 * r) / π + 1 + (N * (2 * r) / π + 1) =
        4 * (D / rhoStar c + ℓ) / π + 2 := by
      rw [← hNr]
      ring
    linarith

/-- (N*): for `A₀, φ > 0` and all large `N`, `10 A₀ (log log N)² ≤ log (10 N)` and
`2 ≤ φ A₀ log log N` (13.2). -/
theorem exists_Nstar (A₀ φ : ℝ) (hA₀ : 0 < A₀) (hφ : 0 < φ) :
    ∃ Nstar : ℕ, ∀ N : ℕ, Nstar ≤ N →
      10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N) ∧
        2 ≤ φ * A₀ * Real.log (Real.log N) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have h1 : ∀ᶠ N : ℕ in atTop,
      10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N) := by
    have h := Real.isLittleO_pow_log_id_atTop (n := 2) |>.def
      (show 0 < 1 / (10 * A₀) by positivity)
    filter_upwards [hlog.eventually h, hlog.eventually (eventually_ge_atTop 0),
      eventually_gt_atTop 0] with N hN hN0 hNpos
    simp only [id, Real.norm_eq_abs, abs_of_nonneg hN0,
      abs_of_nonneg (sq_nonneg (Real.log (Real.log N)))] at hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
    rw [Real.log_mul (by norm_num) hNR.ne']
    have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have : 10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log N := by
      have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 10 * A₀)
      calc 10 * A₀ * Real.log (Real.log N) ^ 2
          ≤ 10 * A₀ * (1 / (10 * A₀) * Real.log N) := this
        _ = Real.log N := by field_simp
    linarith
  have h2 : ∀ᶠ N : ℕ in atTop, 2 ≤ φ * A₀ * Real.log (Real.log N) := by
    filter_upwards [hloglog.eventually_ge_atTop (2 / (φ * A₀))] with N hN
    have := (div_le_iff₀ (mul_pos hφ hA₀)).mp hN
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h1.and h2)
  exact ⟨N₀, hN₀⟩

end Rigidity
