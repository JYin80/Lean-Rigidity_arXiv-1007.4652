module

public import Rigidity.Counting.Count
public import Rigidity.Semicircle.Locations
public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# From the counting function to rigidity (NP v1.1, §9: Lemma 9.1)

Numbers in this file refer to the blueprint NP v1.1; the original argument is in the proof of
[EYY, Theorem 2.2] (Erdős–Yau–Yin, arXiv:1007.4652), which treats only `j ≤ N / 2` and reflects.

`rigidity_of_counting` is Lemma 9.1: if the counting function of an ordered family `λ₁ ≤ … ≤ λ_N`
differs from `n_sc` by at most `Δ / N` everywhere and the family lies in `[-2 - ω, 2 + ω]`, then
`λ_j` is within `9 Δ ĵ^{-1/3} N^{-2/3}` of the classical location `γ_j`, plus
`ω + 9 Δ^{2/3} N^{-2/3}` when `ĵ = min (j, N + 1 - j) ≤ 3 Δ`.

The proof counts: the counting function at `λ_j` pins `N n_sc(λ_j)` to `[j - Δ, j - 1 + Δ]`
(Step 1). In the bulk `ĵ > 3 Δ` the integrated density comparison of Lemma 3.4 (f) turns this
into a bound on `|λ_j - γ_j|` (Step 2). At an edge `ĵ ≤ 3 Δ` the edge behaviour of `n_sc`
(Lemma 3.4 (b)) bounds `λ_j + 2` (respectively `2 - λ_j`) from above, the hypothesis `λ ≥ -2 - ω`
(respectively `λ ≤ 2 + ω`) from below, and the edge bound of Lemma 3.4 (c) bounds `γ_j`
(Steps 3 and 4).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Real-power identities -/

/-- `(x ^ (1/3)) ^ 3 = x` for `x ≥ 0`. -/
private lemma conv_rpow_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `(x ^ 3) ^ (1/3) = x` for `x ≥ 0`. -/
private lemma conv_cube_rpow {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ (1 / 3 : ℝ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `x ^ (2/3) = (x ^ (1/3)) ^ 2` for `x ≥ 0`. -/
private lemma conv_rpow_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 / 3 : ℝ) = (x ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `(Δ / N) ^ (1/3)` is positive and its cube is `Δ / N`. -/
private lemma conv_w_props {Δ N : ℝ} (hΔ : 0 < Δ) (hN : 0 < N) :
    0 < (Δ / N) ^ (1 / 3 : ℝ) ∧ ((Δ / N) ^ (1 / 3 : ℝ)) ^ 3 = Δ / N :=
  ⟨Real.rpow_pos_of_pos (div_pos hΔ hN) _, conv_rpow_cube (div_pos hΔ hN).le⟩

/-- `Δ ^ (2/3) * N ^ (-(2/3)) = ((Δ / N) ^ (1/3)) ^ 2`. -/
private lemma conv_theta {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N) :
    Δ ^ (2 / 3 : ℝ) * N ^ (-(2 / 3 : ℝ)) = ((Δ / N) ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [← conv_rpow_two_thirds (div_nonneg hΔ hN), Real.div_rpow hΔ hN, Real.rpow_neg hN,
    div_eq_mul_inv (Δ ^ (2 / 3 : ℝ))]

/-- `ĵ = min (k + 1) (N - k)` as a real number. -/
private lemma conv_rigWeight_cast {N : ℕ} (k : Fin N) :
    (rigWeight N k : ℝ) = min ((k.val : ℝ) + 1) ((N : ℝ) - k.val) := by
  unfold rigWeight
  rw [Nat.cast_min, Nat.cast_sub k.isLt.le]
  push_cast
  rfl

/-! ### Step 1: the counting function at `λ_j` -/

private lemma conv_nsc_continuous : Continuous nsc :=
  continuous_iff_continuousAt.2 fun E => (nsc_props.1 E).continuousAt

/-- `{k' ≤ k} ⊆ {λ_{k'} ≤ λ_k}`: the counting function at `λ_k` is at least `(k + 1) / N`. -/
private lemma conv_count_ge {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) (k : Fin N) :
    ((k.val : ℝ) + 1) / N ≤ countOf lam (lam k) := by
  have hsub : Finset.Iic k ⊆ Finset.univ.filter fun k' => lam k' ≤ lam k := by
    intro k' hk'
    rw [Finset.mem_Iic] at hk'
    simp [hmono hk']
  have h := Finset.card_le_card hsub
  rw [Fin.card_Iic] at h
  unfold countOf
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

/-- For `E < λ_k`, `{λ_{k'} ≤ E} ⊆ {k' < k}`: the counting function at `E` is at most `k / N`. -/
private lemma conv_count_lt {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) (k : Fin N)
    {E : ℝ} (hE : E < lam k) : countOf lam E ≤ (k.val : ℝ) / N := by
  have hsub : (Finset.univ.filter fun k' => lam k' ≤ E) ⊆ Finset.Iio k := by
    intro k' hk'
    rw [Finset.mem_filter] at hk'
    rw [Finset.mem_Iio]
    by_contra h
    exact absurd (hmono (not_lt.1 h)) (not_le.2 (lt_of_le_of_lt hk'.2 hE))
  have h := Finset.card_le_card hsub
  rw [Fin.card_Iio] at h
  unfold countOf
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

/-- Step 1: `N n_sc(λ_k) ∈ [k + 1 - Δ, k + Δ]`. -/
private lemma conv_count_nsc {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) {Δ : ℝ}
    (hcount : ∀ E, |countOf lam E - nsc E| ≤ Δ / N) (k : Fin N) :
    ((k.val : ℝ) + 1 - Δ) / N ≤ nsc (lam k) ∧ nsc (lam k) ≤ ((k.val : ℝ) + Δ) / N := by
  constructor
  · have h1 := conv_count_ge lam hmono k
    have h2 := (abs_le.1 (hcount (lam k))).2
    rw [sub_div]
    linarith
  · have hlim : Tendsto nsc (𝓝[<] (lam k)) (𝓝 (nsc (lam k))) :=
      (conv_nsc_continuous.tendsto _).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with E hE
    have h1 := conv_count_lt lam hmono k hE
    have h2 := (abs_le.1 (hcount E)).1
    rw [add_div]
    linarith

/-! ### Step 2: the bulk -/

/-- Step 2: for `a ≤ b` with `n_sc a` and `1 - n_sc b` at least `(J - Δ) / N`, `J > 3 Δ`, and
`n_sc b - n_sc a ≤ Δ / N`, one has `b - a ≤ 9 Δ J^{-1/3} N^{-2/3}`. -/
private lemma conv_bulk {N : ℕ} {a b Δ J : ℝ} (hN : 0 < (N : ℝ)) (hΔ : 0 < Δ) (hJ : 3 * Δ < J)
    (hab : a ≤ b) (ha : (J - Δ) / N ≤ nsc a) (hb : (J - Δ) / N ≤ 1 - nsc b)
    (hd : nsc b - nsc a ≤ Δ / N) :
    b - a ≤ 9 * Δ * J ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hmain := sub_mul_min_nsc_le hab
  have hJ0 : 0 < J := by linarith
  have hp : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hN _
  have hr : 0 < J ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hJ0 _
  have hp3 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = N := conv_rpow_cube hN.le
  have hr3 : (J ^ (1 / 3 : ℝ)) ^ 3 = J := conv_rpow_cube hJ0.le
  set p := (N : ℝ) ^ (1 / 3 : ℝ) with hpdef
  set r := J ^ (1 / 3 : ℝ) with hrdef
  have hlow : J / (2 ^ 3 * N) ≤ (J - Δ) / N := by
    rw [div_le_div_iff₀ (by positivity) hN]
    nlinarith
  have hτ : (r / (2 * p)) ^ 3 ≤ min (nsc a) (1 - nsc b) := by
    rw [div_pow, mul_pow, hp3, hr3]
    exact le_min (hlow.trans ha) (hlow.trans hb)
  have hτ' : r / (2 * p) ≤ (min (nsc a) (1 - nsc b)) ^ (1 / 3 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hτ (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [conv_cube_rpow (by positivity)] at this
  have hba : 0 ≤ b - a := by linarith
  have h1 : (b - a) * (r / (2 * p)) ≤ 3 * (Δ / p ^ 3) := by
    calc (b - a) * (r / (2 * p)) ≤ (b - a) * (min (nsc a) (1 - nsc b)) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hτ' hba
      _ ≤ 3 * (nsc b - nsc a) := hmain
      _ ≤ 3 * (Δ / p ^ 3) := by rw [hp3]; linarith
  have h2 : (b - a) * r * p ^ 2 ≤ 6 * Δ := by
    have h3 : (b - a) * (r / (2 * p)) * (2 * p ^ 3) ≤ 3 * (Δ / p ^ 3) * (2 * p ^ 3) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have e1 : (b - a) * (r / (2 * p)) * (2 * p ^ 3) = (b - a) * r * p ^ 2 := by
      field_simp
    have e2 : 3 * (Δ / p ^ 3) * (2 * p ^ 3) = 6 * Δ := by
      field_simp
      norm_num
    rw [e1, e2] at h3
    exact h3
  have e3 : 9 * Δ * J ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) = 9 * Δ / (r * p ^ 2) := by
    rw [Real.rpow_neg hJ0.le, Real.rpow_neg hN.le, conv_rpow_two_thirds hN.le]
    field_simp
    rfl
  rw [e3, le_div_iff₀ (by positivity)]
  nlinarith

/-! ### Steps 3 and 4: the edges -/

/-- If `0 ≤ m ≤ 3 Δ` then `3.6 (m / N)^{2/3} ≤ 9 (Δ / N)^{2/3}`. -/
private lemma conv_edge_gamma {m Δ N : ℝ} (hΔ : 0 < Δ) (hN : 0 < N) (hm0 : 0 ≤ m)
    (hm : m ≤ 3 * Δ) :
    3.6 * (m / N) ^ (2 / 3 : ℝ) ≤ 9 * ((Δ / N) ^ (1 / 3 : ℝ)) ^ 2 := by
  obtain ⟨hw, hw3⟩ := conv_w_props hΔ hN
  set w := (Δ / N) ^ (1 / 3 : ℝ)
  have hT0 : 0 ≤ (m / N) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (div_nonneg hm0 hN.le) _
  have hT3 : ((m / N) ^ (1 / 3 : ℝ)) ^ 3 = m / N := conv_rpow_cube (div_nonneg hm0 hN.le)
  have hle : (m / N) ^ (1 / 3 : ℝ) ≤ 1.5 * w := by
    refine (pow_le_pow_iff_left₀ hT0 (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    rw [hT3, mul_pow]
    have : m / N ≤ 3 * (Δ / N) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hm hN.le
    rw [hw3]
    nlinarith [div_pos hΔ hN]
  rw [conv_rpow_two_thirds (div_nonneg hm0 hN.le)]
  have := pow_le_pow_left₀ hT0 hle 2
  nlinarith [sq_nonneg w]

/-- Edge case of Step 3 and 4: `0 < u`, `n_sc(-2 + u) ≤ 4 w³` with `4 w³ < 1/2` gives
`u ≤ 9 w²`. -/
private lemma conv_edge_u {u w : ℝ} (hu : 0 < u) (hw : 0 < w) (hn : nsc (-2 + u) ≤ 4 * w ^ 3)
    (hlt : 4 * w ^ 3 < 1 / 2) : u ≤ 9 * w ^ 2 := by
  have hu2 : u ≤ 2 := by
    by_contra h
    have h0 := nsc_props.2.1 (show (0 : ℝ) ≤ -2 + u by linarith)
    rw [nsc_props.2.2.2.2.2.2.2] at h0
    linarith
  have hlow := ((rhoSc_nsc_edge hu.le).2.2 hu2).2
  have hs0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hs2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have h32 : u ^ (3 / 2 : ℝ) = Real.sqrt u ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
  rw [h32] at hlow
  have hπ0 : 0 < π := Real.pi_pos
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hsq2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  have hc : Real.sqrt 2 * Real.sqrt u ^ 3 ≤ 12 * π * w ^ 3 := by
    have h1 : Real.sqrt 2 / (3 * π) * Real.sqrt u ^ 3 ≤ 4 * w ^ 3 := hlow.trans hn
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have hcube : Real.sqrt u ^ 3 ≤ (3 * w) ^ 3 := by
    have h1 : 1.4 * Real.sqrt u ^ 3 ≤ Real.sqrt 2 * Real.sqrt u ^ 3 :=
      mul_le_mul_of_nonneg_right hsq2 (by positivity)
    have h2 : 12 * π * w ^ 3 ≤ 37.8 * w ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [mul_pow]
    nlinarith
  have hs : Real.sqrt u ≤ 3 * w :=
    (pow_le_pow_iff_left₀ hs0 (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  calc u = Real.sqrt u ^ 2 := hs2.symm
    _ ≤ (3 * w) ^ 2 := pow_le_pow_left₀ hs0 hs 2
    _ = 9 * w ^ 2 := by ring

/-- Step 3: the lower edge, `ĵ = j = k + 1 ≤ 3 Δ`. -/
private lemma conv_left_edge {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) {Δ ω : ℝ}
    (hΔ : 1 ≤ Δ) (hω0 : 0 ≤ ω) (hN : 100 * Δ ≤ N)
    (hcount : ∀ E, |countOf lam E - nsc E| ≤ Δ / N) (hlo : ∀ k, -2 - ω ≤ lam k) (k : Fin N)
    (hk : (k.val : ℝ) + 1 ≤ 3 * Δ) :
    |lam k - gamma N k| ≤ ω + 9 * ((Δ / N) ^ (1 / 3 : ℝ)) ^ 2 := by
  have hΔ0 : 0 < Δ := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hw, hw3⟩ := conv_w_props hΔ0 hN0
  set w := (Δ / N) ^ (1 / 3 : ℝ)
  have hw2 : 0 ≤ 9 * w ^ 2 := by positivity
  have hgm := gamma_mem k
  have hk0 : (0 : ℝ) ≤ (k.val : ℝ) + 1 := by positivity
  have hγ : gamma N k + 2 ≤ 9 * w ^ 2 := by
    have hk2 : 2 * (k.val + 1) ≤ N := by
      have : (2 * ((k.val : ℝ) + 1)) ≤ N := by linarith
      exact_mod_cast this
    exact ((gamma_edge_bounds k).1 hk2).2.trans (conv_edge_gamma hΔ0 hN0 hk0 hk)
  have hR1 := (conv_count_nsc lam hmono hcount k).2
  have h4 : nsc (lam k) ≤ 4 * w ^ 3 := by
    rw [hw3]
    refine hR1.trans ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hN0.le
  have hlt : 4 * w ^ 3 < 1 / 2 := by
    rw [hw3, ← mul_div_assoc, div_lt_iff₀ hN0]
    linarith
  have hl : lam k + 2 ≤ 9 * w ^ 2 := by
    by_cases h : lam k ≤ -2
    · linarith
    · have h := not_le.1 h
      refine conv_edge_u (u := lam k + 2) (by linarith) hw ?_ hlt
      rw [show -2 + (lam k + 2) = lam k by ring]
      exact h4
  rw [abs_le]
  constructor <;> linarith [hlo k, hgm.1]

/-- Step 4: the upper edge, `ĵ = N + 1 - j = N - k ≤ 3 Δ`. -/
private lemma conv_right_edge {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) {Δ ω : ℝ}
    (hΔ : 1 ≤ Δ) (hω0 : 0 ≤ ω) (hN : 100 * Δ ≤ N)
    (hcount : ∀ E, |countOf lam E - nsc E| ≤ Δ / N) (hhi : ∀ k, lam k ≤ 2 + ω) (k : Fin N)
    (hk : (N : ℝ) - k.val ≤ 3 * Δ) :
    |lam k - gamma N k| ≤ ω + 9 * ((Δ / N) ^ (1 / 3 : ℝ)) ^ 2 := by
  have hΔ0 : 0 < Δ := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hw, hw3⟩ := conv_w_props hΔ0 hN0
  set w := (Δ / N) ^ (1 / 3 : ℝ)
  have hw2 : 0 ≤ 9 * w ^ 2 := by positivity
  have hgm := gamma_mem k
  have hk1 : (k.val : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
  have hγ : 2 - gamma N k ≤ 9 * w ^ 2 := by
    have hk2 : N ≤ 2 * (k.val + 1) := by
      have : (N : ℝ) ≤ 2 * ((k.val : ℝ) + 1) := by linarith
      exact_mod_cast this
    exact ((gamma_edge_bounds k).2 hk2).2.trans
      (conv_edge_gamma hΔ0 hN0 (by linarith) (by linarith))
  have hR1 := (conv_count_nsc lam hmono hcount k).1
  have h4 : nsc (-lam k) ≤ 4 * w ^ 3 := by
    rw [nsc_props.2.2.2.2.2.2.1, hw3]
    have : 1 - ((k.val : ℝ) + 1 - Δ) / N = ((N : ℝ) - k.val - 1 + Δ) / N := by
      field_simp
      ring
    have h5 : 1 - nsc (lam k) ≤ 1 - ((k.val : ℝ) + 1 - Δ) / N := by linarith
    rw [this] at h5
    refine h5.trans ?_
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hN0.le
  have hlt : 4 * w ^ 3 < 1 / 2 := by
    rw [hw3, ← mul_div_assoc, div_lt_iff₀ hN0]
    linarith
  have hl : 2 - lam k ≤ 9 * w ^ 2 := by
    by_cases h : 2 ≤ lam k
    · linarith
    · have h := not_le.1 h
      refine conv_edge_u (u := 2 - lam k) (by linarith) hw ?_ hlt
      rw [show -2 + (2 - lam k) = -lam k by ring]
      exact h4
  rw [abs_le]
  constructor <;> linarith [hhi k, hgm.2]

/-! ### Lemma 9.1 -/

/-- Lemma 9.1: from the counting function to rigidity (deterministic). -/
theorem rigidity_of_counting {N : ℕ} (lam : Fin N → ℝ) (hmono : Monotone lam) {Δ ω : ℝ}
    (hΔ : 1 ≤ Δ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hN : 100 * Δ ≤ N)
    (hcount : ∀ E, |countOf lam E - nsc E| ≤ Δ / N) (hlo : ∀ k, -2 - ω ≤ lam k)
    (hhi : ∀ k, lam k ≤ 2 + ω) (k : Fin N) :
    |lam k - gamma N k| ≤ 9 * Δ * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) +
      (if (rigWeight N k : ℝ) ≤ 3 * Δ then ω + 9 * Δ ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))
        else 0) := by
  have _ := hω1
  have hΔ0 : 0 < Δ := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hA : 0 ≤ 9 * Δ * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    positivity
  have hθ : 9 * Δ ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) =
      9 * ((Δ / N) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [mul_assoc, conv_theta hΔ0.le hN0.le]
  have hkN : (k.val : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
  by_cases hj : (rigWeight N k : ℝ) ≤ 3 * Δ
  · simp only [hj, ↓reduceIte]
    rw [hθ]
    rw [conv_rigWeight_cast, min_le_iff] at hj
    have hedge : |lam k - gamma N k| ≤ ω + 9 * ((Δ / N) ^ (1 / 3 : ℝ)) ^ 2 := by
      rcases hj with hj | hj
      · exact conv_left_edge lam hmono hΔ hω0 hN hcount hlo k hj
      · exact conv_right_edge lam hmono hΔ hω0 hN hcount hhi k hj
    linarith
  · simp only [hj, ↓reduceIte, add_zero]
    have hj' : 3 * Δ < (rigWeight N k : ℝ) := not_le.1 hj
    have hJ1 : (rigWeight N k : ℝ) ≤ (k.val : ℝ) + 1 := by
      rw [conv_rigWeight_cast]; exact min_le_left _ _
    have hJ2 : (rigWeight N k : ℝ) ≤ (N : ℝ) - k.val := by
      rw [conv_rigWeight_cast]; exact min_le_right _ _
    set J : ℝ := (rigWeight N k : ℝ) with hJ
    obtain ⟨hR1, hR2⟩ := conv_count_nsc lam hmono hcount k
    have hg : nsc (gamma N k) = ((k.val : ℝ) + 1) / N := by
      rw [eq_div_iff hN0.ne', mul_comm]
      exact nsc_gamma k
    have hx1 : (J - Δ) / N ≤ nsc (lam k) :=
      (div_le_div_of_nonneg_right (by linarith) hN0.le).trans hR1
    have hx2 : (J - Δ) / N ≤ 1 - nsc (lam k) := by
      have : (J - Δ) / N + ((k.val : ℝ) + Δ) / N ≤ 1 := by
        rw [← add_div, div_le_one hN0]
        linarith
      linarith
    have hg1 : (J - Δ) / N ≤ nsc (gamma N k) := by
      rw [hg]
      exact div_le_div_of_nonneg_right (by linarith) hN0.le
    have hg2 : (J - Δ) / N ≤ 1 - nsc (gamma N k) := by
      have : (J - Δ) / N + ((k.val : ℝ) + 1) / N ≤ 1 := by
        rw [← add_div, div_le_one hN0]
        linarith
      linarith
    have hd1 : nsc (gamma N k) - nsc (lam k) ≤ Δ / N := by
      rw [hg]
      have : ((k.val : ℝ) + 1) / N - ((k.val : ℝ) + 1 - Δ) / N = Δ / N := by
        rw [← sub_div]; ring_nf
      linarith
    have hd2 : nsc (lam k) - nsc (gamma N k) ≤ Δ / N := by
      rw [hg]
      have : ((k.val : ℝ) + Δ) / N - ((k.val : ℝ) + 1) / N ≤ Δ / N := by
        rw [← sub_div]
        exact div_le_div_of_nonneg_right (by linarith) hN0.le
      linarith
    rw [abs_le]
    rcases le_total (lam k) (gamma N k) with h | h
    · have := conv_bulk (N := N) hN0 hΔ0 hj' h hx1 hg2 hd1
      constructor <;> linarith
    · have := conv_bulk (N := N) hN0 hΔ0 hj' h hg1 hx2 hd2
      constructor <;> linarith

end Rigidity
