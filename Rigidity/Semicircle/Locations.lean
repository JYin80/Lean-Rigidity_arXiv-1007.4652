import Rigidity.Semicircle.Density
import Rigidity.Semicircle.Stieltjes

/-!
# Edge and bulk behaviour of `ϱ_sc`, `n_sc` and the classical locations

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file proves the remaining statements of Lemma 3.4: the edge behaviour of `ϱ_sc` and `n_sc`
(b), the reflection `γ_{N-j} = -γ_j` and the edge bounds with the constants `2.8` and `3.6` for
the classical locations (c), the bulk lower bound on `ϱ_sc` (d), the bound on the number of
classical locations in an interval (e), and the comparison of `ϱ_sc` with
`min (n_sc, 1 - n_sc)^{1/3}` together with its integrated form (f).

The bounds on `n_sc` near the edge come from comparing `n_sc(-2 + u)` with the explicit
primitive `u ↦ c u^{3/2}` through their derivatives.  The edge bounds on `γ_j` then follow by
cubing, and the counting bound from the Lipschitz constant `1/π` of `n_sc`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Comparison of two functions on `[a, b]` through their derivatives. -/
private lemma locations_le_of_deriv_le {F G f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) (hG : ∀ x ∈ Set.Icc a b, HasDerivAt G (g x) x)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) (ha : F a ≤ G a) : F b ≤ G b := by
  have hmono : MonotoneOn (fun x => G x - F x) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact ((hG x hx).sub (hF x hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hG x (Set.Ioo_subset_Icc_self hx)).sub
        (hF x (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
      have hd : HasDerivAt (fun x => G x - F x) (g x - f x) x := (hG x hx').sub (hF x hx')
      rw [hd.deriv]
      linarith [hfg x hx']
  have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only at this
  linarith

/-- `0 ≤ n_sc`. -/
private lemma locations_nsc_nonneg (E : ℝ) : 0 ≤ nsc E := by
  obtain ⟨-, hmono, -, hlow, -⟩ := nsc_props
  rcases le_total E (-2) with h | h
  · rw [hlow E h]
  · have := hmono h
    rw [hlow (-2) le_rfl] at this
    exact this

/-- `n_sc ≤ 1`. -/
private lemma locations_nsc_le_one (E : ℝ) : nsc E ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, hneg, -⟩ := nsc_props
  have := locations_nsc_nonneg (-E)
  rw [hneg] at this
  linarith

/-- `u ^ (3/2) = (√u) ^ 3`. -/
private lemma locations_rpow_three_halves {u : ℝ} (hu : 0 ≤ u) :
    u ^ (3 / 2 : ℝ) = Real.sqrt u ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

/-- The derivative of `u ↦ c u^{3/2}` is `(3 c / 2) √u`. -/
private lemma locations_hasDerivAt_rpow (c u : ℝ) :
    HasDerivAt (fun u : ℝ => c * u ^ (3 / 2 : ℝ)) (c * (3 / 2) * Real.sqrt u) u := by
  have h := (Real.hasDerivAt_rpow_const (x := u) (p := 3 / 2) (Or.inr (by norm_num))).const_mul c
  convert h using 1
  rw [Real.sqrt_eq_rpow]
  norm_num
  ring

/-- The derivative of `u ↦ n_sc(-2 + u)` is `ϱ_sc(-2 + u)`. -/
private lemma locations_hasDerivAt_nsc (u : ℝ) :
    HasDerivAt (fun u : ℝ => nsc (-2 + u)) (rhoSc (-2 + u)) u :=
  HasDerivAt.comp_const_add (-2) u (nsc_props.1 (-2 + u))

/-- For `u ≥ 0`, `ϱ_sc(-2 + u) ≤ √u / π`. -/
private lemma locations_rhoSc_edge_le {u : ℝ} (hu : 0 ≤ u) :
    rhoSc (-2 + u) ≤ Real.sqrt u / π := by
  unfold rhoSc
  have h1 : Real.sqrt (max (4 - (-2 + u) ^ 2) 0) ≤ 2 * Real.sqrt u := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hu]
    refine max_le ?_ (by positivity)
    nlinarith [sq_nonneg u]
  calc (2 * π)⁻¹ * Real.sqrt (max (4 - (-2 + u) ^ 2) 0) ≤ (2 * π)⁻¹ * (2 * Real.sqrt u) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.sqrt u / π := by field_simp

/-- For `0 ≤ u ≤ 2`, `√u / (√2 π) ≤ ϱ_sc(-2 + u)`. -/
private lemma locations_rhoSc_edge_ge {u : ℝ} (hu : 0 ≤ u) (hu2 : u ≤ 2) :
    Real.sqrt u / (Real.sqrt 2 * π) ≤ rhoSc (-2 + u) := by
  unfold rhoSc
  have h1 : Real.sqrt 2 * Real.sqrt u ≤ Real.sqrt (max (4 - (-2 + u) ^ 2) 0) := by
    rw [← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt (le_max_of_le_left ?_)
    nlinarith
  have h2 : Real.sqrt u / (Real.sqrt 2 * π) = (2 * π)⁻¹ * (Real.sqrt 2 * Real.sqrt u) := by
    have h2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [h2']
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Lemma 3.4 (b): edge behaviour. -/
theorem rhoSc_nsc_edge {u : ℝ} (hu : 0 ≤ u) :
    rhoSc (-2 + u) ≤ Real.sqrt u / π ∧ nsc (-2 + u) ≤ 2 / (3 * π) * u ^ (3 / 2 : ℝ) ∧
      (u ≤ 2 → Real.sqrt u / (Real.sqrt 2 * π) ≤ rhoSc (-2 + u) ∧
        Real.sqrt 2 / (3 * π) * u ^ (3 / 2 : ℝ) ≤ nsc (-2 + u)) := by
  have hnsc0 : nsc (-2) = 0 := nsc_props.2.2.2.1 _ le_rfl
  have hpi : 0 < π := Real.pi_pos
  refine ⟨locations_rhoSc_edge_le hu, ?_, fun hu2 => ⟨locations_rhoSc_edge_ge hu hu2, ?_⟩⟩
  · refine locations_le_of_deriv_le (F := fun u => nsc (-2 + u))
      (G := fun u => 2 / (3 * π) * u ^ (3 / 2 : ℝ)) (f := fun u => rhoSc (-2 + u))
      (g := fun u => 2 / (3 * π) * (3 / 2) * Real.sqrt u) hu
      (fun x _ => locations_hasDerivAt_nsc x) (fun x _ => locations_hasDerivAt_rpow _ x)
      (fun x hx => ?_) (by simp [hnsc0])
    have := locations_rhoSc_edge_le hx.1
    have e : 2 / (3 * π) * (3 / 2) * Real.sqrt x = Real.sqrt x / π := by field_simp
    rw [e]
    exact this
  · refine locations_le_of_deriv_le (F := fun u => Real.sqrt 2 / (3 * π) * u ^ (3 / 2 : ℝ))
      (G := fun u => nsc (-2 + u))
      (f := fun u => Real.sqrt 2 / (3 * π) * (3 / 2) * Real.sqrt u)
      (g := fun u => rhoSc (-2 + u)) hu
      (fun x _ => locations_hasDerivAt_rpow _ x) (fun x _ => locations_hasDerivAt_nsc x)
      (fun x hx => ?_) (by simp [hnsc0])
    have := locations_rhoSc_edge_ge hx.1 (hx.2.trans hu2)
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have e : Real.sqrt 2 / (3 * π) * (3 / 2) * Real.sqrt x = Real.sqrt x / (Real.sqrt 2 * π) := by
      have h2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      rw [h2']
    rw [e]
    exact this

/-- Lemma 3.4 (c): reflection of the classical locations, `γ_{N-j} = -γ_j`. -/
theorem gamma_reflect {N : ℕ} (k : Fin N) (hk : k.val + 1 < N) :
    gamma N ⟨N - 2 - k.val, by omega⟩ = -gamma N k := by
  obtain ⟨-, -, -, -, -, hstrict, hneg, -⟩ := nsc_props
  set k' : Fin N := ⟨N - 2 - k.val, by omega⟩ with hk'
  have hkv : k'.val = N - 2 - k.val := rfl
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
  have h1 := nsc_gamma k
  have h2 := nsc_gamma k'
  have hsum : ((k'.val : ℝ) + 1) + (k.val + 1) = N := by
    have : (N - 2 - k.val) + 1 + (k.val + 1) = N := by omega
    rw [hkv]
    exact_mod_cast this
  have hnsc : nsc (gamma N k') = nsc (-gamma N k) := by
    rw [hneg]
    apply mul_left_cancel₀ hNpos.ne'
    rw [h2, mul_sub, h1, mul_one]
    linarith
  have hm := gamma_mem k
  have hm' := gamma_mem k'
  exact hstrict.injOn ⟨hm'.1.le, hm'.2⟩ ⟨by linarith [hm.2], by linarith [hm.1]⟩ hnsc

/-- The constants of Lemma 3.4 (c): if `√2 / (3 π) · u^{3/2} ≤ t ≤ 2 / (3 π) · u^{3/2}` with
`u > 0`, then `2.8 t^{2/3} ≤ u ≤ 3.6 t^{2/3}`. -/
private lemma locations_edge_core {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (h1 : Real.sqrt 2 / (3 * π) * u ^ (3 / 2 : ℝ) ≤ t)
    (h2 : t ≤ 2 / (3 * π) * u ^ (3 / 2 : ℝ)) :
    2.8 * t ^ (2 / 3 : ℝ) ≤ u ∧ u ≤ 3.6 * t ^ (2 / 3 : ℝ) := by
  have hπ0 : 0 < π := Real.pi_pos
  have hπ1 : 3.14 < π := Real.pi_gt_d2
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hw0 : 0 ≤ t ^ (2 / 3 : ℝ) := Real.rpow_nonneg ht _
  have hw3 : (t ^ (2 / 3 : ℝ)) ^ 3 = t ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, ← Real.rpow_natCast t 2]
    norm_num
  have hu32 : (u ^ (3 / 2 : ℝ)) ^ 2 = u ^ 3 := by
    rw [locations_rpow_three_halves hu.le, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hu.le]
  have hu3 : 0 ≤ u ^ 3 := by positivity
  have hsq2 : t ^ 2 ≤ (2 / (3 * π)) ^ 2 * u ^ 3 := by
    calc t ^ 2 ≤ (2 / (3 * π) * u ^ (3 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ ht h2 2
      _ = (2 / (3 * π)) ^ 2 * u ^ 3 := by rw [mul_pow, hu32]
  have hsq1 : (Real.sqrt 2 / (3 * π)) ^ 2 * u ^ 3 ≤ t ^ 2 := by
    calc (Real.sqrt 2 / (3 * π)) ^ 2 * u ^ 3
        = (Real.sqrt 2 / (3 * π) * u ^ (3 / 2 : ℝ)) ^ 2 := by rw [mul_pow, hu32]
      _ ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have e2 : (2 / (3 * π)) ^ 2 = 4 / (9 * π ^ 2) := by field_simp; ring
  have e1 : (Real.sqrt 2 / (3 * π)) ^ 2 = 2 / (9 * π ^ 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hπsq : 9.8596 < π ^ 2 := by nlinarith
  have hπsq' : π ^ 2 < 9.9225 := by nlinarith
  constructor
  · refine (pow_le_pow_iff_left₀ (by positivity) hu.le (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    have c1 : (2.8 : ℝ) ^ 3 * (4 / (9 * π ^ 2)) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one (by positivity)]
      nlinarith
    calc (2.8 * t ^ (2 / 3 : ℝ)) ^ 3 = (2.8 : ℝ) ^ 3 * t ^ 2 := by rw [mul_pow, hw3]
      _ ≤ (2.8 : ℝ) ^ 3 * ((2 / (3 * π)) ^ 2 * u ^ 3) := by gcongr
      _ = ((2.8 : ℝ) ^ 3 * (4 / (9 * π ^ 2))) * u ^ 3 := by rw [e2]; ring
      _ ≤ 1 * u ^ 3 := by gcongr
      _ = u ^ 3 := one_mul _
  · refine (pow_le_pow_iff_left₀ hu.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    have c2 : 1 ≤ (3.6 : ℝ) ^ 3 * (2 / (9 * π ^ 2)) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      nlinarith
    calc u ^ 3 = 1 * u ^ 3 := (one_mul _).symm
      _ ≤ ((3.6 : ℝ) ^ 3 * (2 / (9 * π ^ 2))) * u ^ 3 := by gcongr
      _ = (3.6 : ℝ) ^ 3 * ((Real.sqrt 2 / (3 * π)) ^ 2 * u ^ 3) := by rw [e1]; ring
      _ ≤ (3.6 : ℝ) ^ 3 * t ^ 2 := by gcongr
      _ = (3.6 * t ^ (2 / 3 : ℝ)) ^ 3 := by rw [mul_pow, hw3]

/-- Lemma 3.4 (c), the case `j ≤ N / 2` of the edge bounds. -/
private lemma locations_edge_lower_half {N : ℕ} (k : Fin N) (h : 2 * (k.val + 1) ≤ N) :
    2.8 * (((k.val + 1 : ℝ)) / N) ^ (2 / 3 : ℝ) ≤ gamma N k + 2 ∧
      gamma N k + 2 ≤ 3.6 * (((k.val + 1 : ℝ)) / N) ^ (2 / 3 : ℝ) := by
  obtain ⟨-, -, -, -, -, hstrict, -, hhalf⟩ := nsc_props
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
  have hγ := nsc_gamma k
  have htval : nsc (gamma N k) = (k.val + 1 : ℝ) / N := by
    rw [eq_div_iff hNpos.ne']
    linarith
  have hle : (k.val + 1 : ℝ) / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]
    have : (2 * (k.val + 1) : ℝ) ≤ N := by exact_mod_cast h
    linarith
  have hm := gamma_mem k
  have hγ0 : gamma N k ≤ 0 := by
    by_contra hpos
    replace hpos := not_le.mp hpos
    have := hstrict ⟨by norm_num, by norm_num⟩ ⟨by linarith [hm.1], hm.2⟩ hpos
    rw [hhalf, htval] at this
    linarith
  have hu : 0 < gamma N k + 2 := by linarith [hm.1]
  have e : -2 + (gamma N k + 2) = gamma N k := by ring
  have hedge := rhoSc_nsc_edge (u := gamma N k + 2) hu.le
  rw [e] at hedge
  obtain ⟨-, hup, hlow⟩ := hedge
  obtain ⟨-, hlo⟩ := hlow (by linarith)
  rw [htval] at hup hlo
  exact locations_edge_core hu (by positivity) hlo hup

/-- Lemma 3.4 (c): the edge bounds on the classical locations (`j = k + 1`). -/
theorem gamma_edge_bounds {N : ℕ} (k : Fin N) :
    (2 * (k.val + 1) ≤ N → 2.8 * (((k.val + 1 : ℝ)) / N) ^ (2 / 3 : ℝ) ≤ gamma N k + 2 ∧
        gamma N k + 2 ≤ 3.6 * (((k.val + 1 : ℝ)) / N) ^ (2 / 3 : ℝ)) ∧
      (N ≤ 2 * (k.val + 1) → 2.8 * (((N - (k.val + 1) : ℝ)) / N) ^ (2 / 3 : ℝ) ≤ 2 - gamma N k ∧
        2 - gamma N k ≤ 3.6 * (((N - (k.val + 1) : ℝ)) / N) ^ (2 / 3 : ℝ)) := by
  refine ⟨locations_edge_lower_half k, fun h => ?_⟩
  have hN : 0 < N := Fin.pos k
  have hklt := k.isLt
  by_cases hlast : k.val + 1 = N
  · have hk : k = ⟨N - 1, by omega⟩ := Fin.ext (by simp; omega)
    have hg : gamma N k = 2 := by rw [hk]; exact gamma_last hN
    have h0 : ((N : ℝ) - (k.val + 1 : ℝ)) = 0 := by
      have : (k.val + 1 : ℝ) = N := by exact_mod_cast hlast
      linarith
    rw [hg, h0]
    simp
  · have hk : k.val + 1 < N := by omega
    set k' : Fin N := ⟨N - 2 - k.val, by omega⟩ with hk'
    have hkv : k'.val = N - 2 - k.val := rfl
    have hr := gamma_reflect k hk
    have hk2 : 2 * (k'.val + 1) ≤ N := by rw [hkv]; omega
    have key := locations_edge_lower_half k' hk2
    have e : ((k'.val : ℝ) + 1) = N - (k.val + 1 : ℝ) := by
      have : (N - 2 - k.val) + 1 + (k.val + 1) = N := by omega
      have h' : ((N - 2 - k.val : ℕ) : ℝ) + 1 + (k.val + 1) = N := by exact_mod_cast this
      rw [hkv]
      linarith
    rw [e, hr] at key
    constructor <;> linarith [key.1, key.2]

/-- Lemma 3.4 (d): bulk lower bound on `ρ_sc`. -/
theorem rhoSc_bulk {c x : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) (hx : |x| ≤ 2 - c / 4) :
    1 / (2 * π) * Real.sqrt (c - c ^ 2 / 16) ≤ rhoSc x := by
  -- `c - c ^ 2 / 16 ≤ 4 - x ^ 2` follows from `|x| ≤ 2 - c / 4` alone.
  have _ := hc
  have _ := hc2
  unfold rhoSc
  have hx2 : x ^ 2 ≤ (2 - c / 4) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [one_div]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_of_le_left ?_)) (by positivity)
  nlinarith [hx2]

/-- Lemma 3.4 (e): counting classical locations in an interval of length `b - a`. -/
theorem card_gamma_mem_le {N : ℕ} {a b : ℝ} {I : Set ℝ} (hab : a ≤ b) (hI : I ⊆ Set.Icc a b) :
    ({k : Fin N | gamma N k ∈ I}.ncard : ℝ) ≤ N * (b - a) / π + 1 := by
  obtain ⟨-, -, hlip, -⟩ := nsc_props
  set S : Set (Fin N) := {k : Fin N | gamma N k ∈ I} with hS
  have hπ : 0 < π := Real.pi_pos
  have hfin : S.Finite := Set.toFinite S
  have hbase : (0 : ℝ) ≤ N * (b - a) / π := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : 0 ≤ b - a := by linarith
    positivity
  rcases S.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Set.ncard_empty]
    simp only [Nat.cast_zero]
    linarith
  · obtain ⟨j₁, hj₁, hmin⟩ := Set.exists_min_image S id hfin hne
    obtain ⟨j₂, hj₂, hmax⟩ := Set.exists_max_image S id hfin hne
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Fin.pos j₁
    have hsub : S ⊆ Set.Icc j₁ j₂ := fun k hk => ⟨hmin k hk, hmax k hk⟩
    have hcard : S.ncard ≤ j₂.val + 1 - j₁.val := by
      calc S.ncard ≤ (Set.Icc j₁ j₂).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = (Finset.Icc j₁ j₂).card := Set.ncard_Icc _ _
        _ = j₂.val + 1 - j₁.val := Fin.card_Icc _ _
    have h12 : j₁.val ≤ j₂.val := hmin j₂ hj₂
    have hcardR : (S.ncard : ℝ) ≤ (j₂.val : ℝ) - j₁.val + 1 := by
      have : ((j₂.val + 1 - j₁.val : ℕ) : ℝ) = (j₂.val : ℝ) + 1 - j₁.val := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      calc (S.ncard : ℝ) ≤ ((j₂.val + 1 - j₁.val : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (j₂.val : ℝ) - j₁.val + 1 := by rw [this]; ring
    have hg1 := hI hj₁
    have hg2 := hI hj₂
    have hl := hlip (gamma N j₂) (gamma N j₁)
    have habs : |gamma N j₂ - gamma N j₁| ≤ b - a :=
      abs_le.mpr ⟨by linarith [hg1.1, hg1.2, hg2.1, hg2.2],
        by linarith [hg1.1, hg1.2, hg2.1, hg2.2]⟩
    have hdiff : (j₂.val : ℝ) - j₁.val = N * (nsc (gamma N j₂) - nsc (gamma N j₁)) := by
      have e1 := nsc_gamma j₁
      have e2 := nsc_gamma j₂
      rw [mul_sub, e1, e2]
      ring
    have hle : nsc (gamma N j₂) - nsc (gamma N j₁) ≤ (b - a) / π :=
      (le_abs_self _).trans (hl.trans (div_le_div_of_nonneg_right habs hπ.le))
    calc (S.ncard : ℝ) ≤ (j₂.val : ℝ) - j₁.val + 1 := hcardR
      _ = N * (nsc (gamma N j₂) - nsc (gamma N j₁)) + 1 := by rw [hdiff]
      _ ≤ N * ((b - a) / π) + 1 := by gcongr
      _ = N * (b - a) / π + 1 := by ring

/-- `(t ^ (1/3)) ^ 3 = t` for `t ≥ 0`. -/
private lemma locations_rpow_third_cube {t : ℝ} (ht : 0 ≤ t) : (t ^ (1 / 3 : ℝ)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- Lemma 3.4 (f) for `x ≤ 0`. -/
private lemma locations_ge_min_nsc_nonpos {x : ℝ} (hx : x ≤ 0) :
    1 / 3 * (min (nsc x) (1 - nsc x)) ^ (1 / 3 : ℝ) ≤ rhoSc x := by
  obtain ⟨-, hmono, -, hlow, -, -, -, hhalf⟩ := nsc_props
  have hρ0 : 0 ≤ rhoSc x := (rhoSc_props.2.2.1 x).1
  rcases le_or_gt x (-2) with hx2 | hx2
  · rw [hlow x hx2, sub_zero, min_eq_left zero_le_one, Real.zero_rpow (by norm_num), mul_zero]
    exact hρ0
  · have hu : 0 < x + 2 := by linarith
    have hu2 : x + 2 ≤ 2 := by linarith
    have hle : nsc x ≤ 1 / 2 := by rw [← hhalf]; exact hmono hx
    rw [min_eq_left (by linarith)]
    have ht0 : 0 ≤ nsc x := locations_nsc_nonneg x
    have e : -2 + (x + 2) = x := by ring
    have hedge := rhoSc_nsc_edge (u := x + 2) hu.le
    rw [e] at hedge
    obtain ⟨-, hup, hlow'⟩ := hedge
    obtain ⟨hρ, -⟩ := hlow' hu2
    rw [locations_rpow_three_halves hu.le] at hup
    have hπ : 0 < π := Real.pi_pos
    have hπ2 : π < 3.15 := Real.pi_lt_d2
    have hq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hq0 : 0 < Real.sqrt 2 := by positivity
    have hq15 : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    have hq3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, hq2]
    have hπsq : π ^ 2 < 9.9225 := by nlinarith
    have h4 : 4 * Real.sqrt 2 * π ^ 2 ≤ 81 := by
      have : Real.sqrt 2 * π ^ 2 ≤ 3 / 2 * 9.9225 :=
        mul_le_mul hq15 hπsq.le (by positivity) (by norm_num)
      linarith
    have key : 2 / (3 * π) ≤ 27 / (Real.sqrt 2 ^ 3 * π ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e2 : 2 * (Real.sqrt 2 ^ 3 * π ^ 3) = π * (4 * Real.sqrt 2 * π ^ 2) := by
        rw [hq3]; ring
      rw [e2]
      nlinarith
    have hv0 : 0 ≤ nsc x ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht0 _
    have hs0 : 0 ≤ Real.sqrt (x + 2) := Real.sqrt_nonneg _
    have hcube : nsc x ^ (1 / 3 : ℝ) ≤ 3 * (Real.sqrt (x + 2) / (Real.sqrt 2 * π)) := by
      refine (pow_le_pow_iff_left₀ hv0 (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
      rw [locations_rpow_third_cube ht0]
      calc nsc x ≤ 2 / (3 * π) * Real.sqrt (x + 2) ^ 3 := hup
        _ ≤ 27 / (Real.sqrt 2 ^ 3 * π ^ 3) * Real.sqrt (x + 2) ^ 3 := by gcongr
        _ = (3 * (Real.sqrt (x + 2) / (Real.sqrt 2 * π))) ^ 3 := by
          rw [mul_pow, div_pow, mul_pow]
          field_simp
          norm_num
    linarith

/-- Lemma 3.4 (f): density versus distribution function. -/
theorem rhoSc_ge_min_nsc (x : ℝ) : 1 / 3 * (min (nsc x) (1 - nsc x)) ^ (1 / 3 : ℝ) ≤ rhoSc x := by
  rcases le_total x 0 with hx | hx
  · exact locations_ge_min_nsc_nonpos hx
  · have h := locations_ge_min_nsc_nonpos (x := -x) (by linarith)
    rw [nsc_props.2.2.2.2.2.2.1 x, rhoSc_props.2.1 x, sub_sub_cancel, min_comm] at h
    exact h

/-- Lemma 3.4 (f), integrated form. -/
theorem sub_mul_min_nsc_le {a b : ℝ} (hab : a ≤ b) :
    (b - a) * (min (nsc a) (1 - nsc b)) ^ (1 / 3 : ℝ) ≤ 3 * (nsc b - nsc a) := by
  obtain ⟨hder, hmono, -⟩ := nsc_props
  set τ₀ := min (nsc a) (1 - nsc b) with hτ
  have hτ0 : 0 ≤ τ₀ := le_min (locations_nsc_nonneg a) (by linarith [locations_nsc_le_one b])
  have hρ : ∀ x ∈ Set.Icc a b, 1 / 3 * τ₀ ^ (1 / 3 : ℝ) ≤ rhoSc x := by
    intro x hx
    refine le_trans ?_ (rhoSc_ge_min_nsc x)
    have h1 : τ₀ ≤ nsc x := (min_le_left _ _).trans (hmono hx.1)
    have h2 : τ₀ ≤ 1 - nsc x := by
      have := hmono hx.2
      have := min_le_right (nsc a) (1 - nsc b)
      linarith
    have := Real.rpow_le_rpow hτ0 (le_min h1 h2) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    linarith
  have hmain := locations_le_of_deriv_le
    (F := fun x => nsc a + (x - a) * (1 / 3 * τ₀ ^ (1 / 3 : ℝ))) (G := nsc)
    (f := fun _ => 1 / 3 * τ₀ ^ (1 / 3 : ℝ)) (g := rhoSc) hab
    (fun x _ => by
      simpa using (((hasDerivAt_id x).sub_const a).mul_const
        (1 / 3 * τ₀ ^ (1 / 3 : ℝ))).const_add (nsc a))
    (fun x _ => hder x) hρ (by simp)
  linarith

end Rigidity
