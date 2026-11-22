module

public import Rigidity.LocalLaw.CrudeNorm
public import Rigidity.Spectrum.Eigenvalues
public import Rigidity.Strong.FarPass
public import Rigidity.Strong.SecondPass

@[expose] public section

/-!
# No eigenvalues outside `2 + K^{C₃} N^{-2/3}` (NP v1.1, §8.1: Proposition 8.1)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The lattice height `η_e = 10 - N^{-4} ⌊(10 - N^{-2/3}) N⁴⌋` of Proposition 8.1. -/
noncomputable def etaE (N : ℕ) : ℝ :=
  10 - (⌊(10 - (N : ℝ) ^ (-(2 / 3 : ℝ))) * (N : ℝ) ^ 4⌋ : ℝ) / (N : ℝ) ^ 4

/-- The lattice height `η_f = 10 - N^{-4} ⌊(10 - N^{-1/2}/2) N⁴⌋` of Proposition 8.1. -/
noncomputable def etaF (N : ℕ) : ℝ :=
  10 - (⌊(10 - 1 / (2 * Real.sqrt N)) * (N : ℝ) ^ 4⌋ : ℝ) / (N : ℝ) ^ 4

/-- The energies `𝔼_e = {E ∈ N^{-4} ℤ : 2 + K^{C₃} N^{-2/3}/2 ≤ |E| ≤ 5}` of Proposition 8.1. -/
def energiesE (a K : ℝ) (N : ℕ) : Set ℝ :=
  {E | ∃ m : ℤ, E = m / (N : ℝ) ^ 4 ∧
    2 + K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) / 2 ≤ |E| ∧ |E| ≤ 5}

/-- The energies `𝔼_f = {E ∈ N^{-4} ℤ : 4.5 ≤ |E| ≤ E_max + 1}` of Proposition 8.1. -/
def energiesF (a C₀ K : ℝ) (N : ℕ) : Set ℝ :=
  {E | ∃ m : ℤ, E = m / (N : ℝ) ^ 4 ∧ 9 / 2 ≤ |E| ∧ |E| ≤ levelEmax a C₀ K N + 1}

/-- `Ξ_K^{(2)} = {‖H‖ ≤ E_max} ∩ ⋂_{E ∈ 𝔼_f} 𝒢^f(E + iη_f) ∩ ⋂_{E ∈ 𝔼_e} 𝒢³(E + iη_e)` of
Proposition 8.1. -/
noncomputable def strongXi2 {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) : Set (Pair N → 𝕜) :=
  {x | ‖toMatrix x‖ ≤ levelEmax a C₀ K N} ∩
    (⋂ E ∈ energiesF a C₀ K N, strongGf M a C₀ K (E + etaF N * Complex.I)) ∩
    ⋂ E ∈ energiesE a K N, strongG3 M a C₀ K (E + etaE N * Complex.I)

/-! ### 1. Elementary facts

The proof of Proposition 8.1 uses (8.a) (from Lemma 3.5 (e)), `Im m ≤ Im m_sc + Λ`, the bound
`|λ_k| ≤ ‖H‖` of Lemma 3.13 (a), rounding to `N^{-4} ℤ`, and the two heights `η_e`, `η_f`. -/

/-- `|λ_k| ≤ ‖H‖` (Lemma 3.13 (a)). -/
private lemma norm_abs_eig_le {N : ℕ} (x : Pair N → 𝕜) (k : Fin N) :
    |eig x k| ≤ ‖toMatrix x‖ := by
  have hN : 0 < N := Fin.pos k
  have hA := toMatrix_isHermitian x
  rw [norm_eq_max_eigAsc hA hN]
  have h1 : eigAsc hA k ≤ eigAsc hA ⟨N - 1, by omega⟩ :=
    eigAsc_monotone hA (by simp [Fin.le_def]; omega)
  have h2 : eigAsc hA ⟨0, hN⟩ ≤ eigAsc hA k := eigAsc_monotone hA (by simp [Fin.le_def])
  change |eigAsc hA k| ≤ _
  exact abs_le.2 ⟨by linarith [le_max_right (eigAsc hA ⟨N - 1, by omega⟩) (-eigAsc hA ⟨0, hN⟩)],
    le_trans h1 (le_max_left _ _)⟩

/-- `{‖H‖ ≤ E}` is closed (Lemma 3.13 (d)). -/
private lemma norm_isClosed_norm_le {N : ℕ} (E : ℝ) :
    IsClosed {x : Pair N → 𝕜 | ‖toMatrix x‖ ≤ E} := by
  have hc : Continuous fun x : Pair N → 𝕜 => ‖toMatrix x‖ := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hc : Continuous fun x : Pair N → 𝕜 =>
        Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by fun_prop
    refine squeeze_zero (fun _ => dist_nonneg) (fun x => ?_) (by simpa using hc.tendsto y)
    rw [Real.dist_eq]
    exact (abs_norm_sub_norm_le _ _).trans (norm_toMatrix_sub_le x y)
  exact isClosed_le hc continuous_const

/-- (8.a), from Lemma 3.5 (e): if `N η Im m(E + iη) < 1/2`, there is no eigenvalue in
`[E - η, E + η]`. -/
private lemma norm_exclude {N : ℕ} (x : Pair N → 𝕜) {E η : ℝ} (hη : 0 < η)
    (h : (N : ℝ) * η * (stieltjesEmp (toMatrix x) (E + η * Complex.I)).im < 1 / 2) (k : Fin N) :
    η < |eig x k - E| := by
  by_contra hk
  replace hk := not_lt.1 hk
  have hc := card_eig_near_le (toMatrix_isHermitian x) E hη
  have hpos : 0 < ({j : Fin N | |eigAsc (toMatrix_isHermitian x) j - E| ≤ η}).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨k, hk⟩
  have h1 : (1 : ℝ) ≤ ({j : Fin N | |eigAsc (toMatrix_isHermitian x) j - E| ≤ η}).ncard := by
    exact_mod_cast hpos
  linarith

/-- `Im m ≤ Im m_sc + Λ`. -/
private lemma norm_im_le {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) :
    (stieltjesEmp (toMatrix x) z).im ≤ (msc z).im + Lam x z := by
  have h := Complex.im_le_norm (stieltjesEmp (toMatrix x) z - msc z)
  rw [Complex.sub_im] at h
  unfold Lam
  linarith

/-- A point `n / D ≥ 0` of `D⁻¹ ℤ` close to `|y|` gives a point `m / D` close to `y`, with
`|m / D| = n / D`. -/
private lemma norm_signed (y D : ℝ) (n : ℤ) (hn : 0 ≤ (n : ℝ) / D) :
    ∃ m : ℤ, |(m : ℝ) / D| = n / D ∧ |y - m / D| = abs ((n : ℝ) / D - |y|) := by
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨n, abs_of_nonneg hn, ?_⟩
    rw [abs_of_nonneg hy, abs_sub_comm]
  · refine ⟨-n, ?_, ?_⟩
    · push_cast
      rw [neg_div, abs_neg, abs_of_nonneg hn]
    · push_cast
      rw [abs_of_neg hy, neg_div, sub_neg_eq_add, sub_neg_eq_add, add_comm]

/-- Rounding up to `D⁻¹ ℤ` (Step 2 of the proof of Proposition 8.1). -/
private lemma norm_round_up (y : ℝ) {D : ℝ} (hD : 0 < D) :
    ∃ m : ℤ, |y| ≤ |(m : ℝ) / D| ∧ |(m : ℝ) / D| ≤ |y| + 1 / D ∧ |y - m / D| ≤ 1 / D := by
  set n := ⌈|y| * D⌉ with hn
  have h1 := Int.le_ceil (|y| * D)
  have h2 := Int.ceil_lt_add_one (|y| * D)
  rw [← hn] at h1 h2
  have e1 : |y| ≤ (n : ℝ) / D := by rw [le_div_iff₀ hD]; exact h1
  have e2 : (n : ℝ) / D ≤ |y| + 1 / D := by
    rw [div_le_iff₀ hD, add_mul, one_div_mul_cancel hD.ne']; linarith
  obtain ⟨m, hm1, hm2⟩ := norm_signed y D n (le_trans (abs_nonneg y) e1)
  refine ⟨m, by rw [hm1]; exact e1, by rw [hm1]; exact e2, ?_⟩
  rw [hm2, abs_le]
  constructor <;> linarith [one_div_pos.2 hD]

/-- Rounding down to `D⁻¹ ℤ` (Step 3 of the proof of Proposition 8.1). -/
private lemma norm_round_down (y : ℝ) {D : ℝ} (hD : 0 < D) :
    ∃ m : ℤ, |y| - 1 / D ≤ |(m : ℝ) / D| ∧ |(m : ℝ) / D| ≤ |y| ∧ |y - m / D| ≤ 1 / D := by
  set n := ⌊|y| * D⌋ with hn
  have h1 := Int.floor_le (|y| * D)
  have h2 := Int.lt_floor_add_one (|y| * D)
  rw [← hn] at h1 h2
  have e1 : (n : ℝ) / D ≤ |y| := by rw [div_le_iff₀ hD]; exact h1
  have e2 : |y| - 1 / D ≤ (n : ℝ) / D := by
    rw [le_div_iff₀ hD, sub_mul, one_div_mul_cancel hD.ne']; linarith
  have hn0 : 0 ≤ (n : ℝ) / D := by
    have : (0 : ℝ) ≤ n := by
      exact_mod_cast Int.floor_nonneg.2 (mul_nonneg (abs_nonneg y) hD.le)
    positivity
  obtain ⟨m, hm1, hm2⟩ := norm_signed y D n hn0
  refine ⟨m, by rw [hm1]; exact e2, by rw [hm1]; exact e1, ?_⟩
  rw [hm2, abs_le]
  constructor <;> linarith [one_div_pos.2 hD]

/-- The lattice heights: `h ≤ 10 - D⁻¹ ⌊(10 - h) D⌋ ≤ h + D⁻¹`. -/
private lemma norm_height (h : ℝ) {D : ℝ} (hD : 0 < D) :
    h ≤ 10 - (⌊(10 - h) * D⌋ : ℝ) / D ∧ 10 - (⌊(10 - h) * D⌋ : ℝ) / D ≤ h + 1 / D := by
  have h1 := Int.floor_le ((10 - h) * D)
  have h2 := Int.lt_floor_add_one ((10 - h) * D)
  constructor
  · have : (⌊(10 - h) * D⌋ : ℝ) / D ≤ 10 - h := by rw [div_le_iff₀ hD]; exact h1
    linarith
  · have : 10 - h - 1 / D ≤ (⌊(10 - h) * D⌋ : ℝ) / D := by
      rw [le_div_iff₀ hD, sub_mul, one_div_mul_cancel hD.ne']; linarith
    linarith

/-- Points `m N⁻⁴ + i (10 - N⁻⁴ ⌊(10 - h) N⁴⌋)` with `h ≤ 10` lie on the grid. -/
private lemma norm_mem_grid {N : ℕ} (m : ℤ) {h : ℝ} (hh : h ≤ 10) :
    (((m : ℝ) / (N : ℝ) ^ 4 : ℝ) : ℂ) +
      ((10 - (⌊(10 - h) * (N : ℝ) ^ 4⌋ : ℝ) / (N : ℝ) ^ 4 : ℝ) : ℂ) * Complex.I ∈ gridPts N := by
  have h0 : 0 ≤ ⌊(10 - h) * (N : ℝ) ^ 4⌋ :=
    Int.floor_nonneg.2 (mul_nonneg (by linarith) (by positivity))
  refine ⟨m, ⌊(10 - h) * (N : ℝ) ^ 4⌋.toNat, ?_⟩
  have hk : ((⌊(10 - h) * (N : ℝ) ^ 4⌋.toNat : ℕ) : ℝ) = (⌊(10 - h) * (N : ℝ) ^ 4⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h0
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [hk]
    ring

/-- A set of points of `D⁻¹ ℤ` in `[-R, R]` is finite with at most `2 R D + 1` elements. -/
private lemma norm_card_le (S : Set ℝ) {R D : ℝ} (hR : 0 ≤ R) (hD : 0 < D)
    (hS : ∀ E ∈ S, ∃ m : ℤ, E = m / D ∧ |E| ≤ R) : S.Finite ∧ (S.ncard : ℝ) ≤ 2 * R * D + 1 := by
  classical
  set n := ⌊R * D⌋ with hn
  set T : Finset ℝ := (Finset.Icc (-n) n).image fun m : ℤ => (m : ℝ) / D with hT
  have hsub : S ⊆ (T : Set ℝ) := by
    intro E hE
    obtain ⟨m, rfl, hm⟩ := hS E hE
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD] at hm
    have hm' : |(m : ℝ)| ≤ R * D := hm
    rw [abs_le] at hm'
    have e1 : m ≤ n := Int.le_floor.2 hm'.2
    have e2 : -m ≤ n := Int.le_floor.2 (by push_cast; linarith)
    simp only [hT, Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc]
    exact ⟨m, ⟨by omega, e1⟩, rfl⟩
  have hfin : (T : Set ℝ).Finite := T.finite_toSet
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : S.ncard ≤ T.card := by
    rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub hfin
  have h2 : T.card ≤ (Finset.Icc (-n) n).card := Finset.card_image_le
  have hn0 : 0 ≤ n := Int.floor_nonneg.2 (mul_nonneg hR hD.le)
  have h3 : ((Finset.Icc (-n) n).card : ℤ) = 2 * n + 1 := by
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]; ring
  have h4 : ((Finset.Icc (-n) n).card : ℝ) = 2 * n + 1 := by exact_mod_cast h3
  have h5 : (n : ℝ) ≤ R * D := Int.floor_le _
  have : (S.ncard : ℝ) ≤ (Finset.Icc (-n) n).card := by exact_mod_cast h1.trans h2
  linarith


/-- `t = N^{-1/3}`: `0 < t ≤ 1`, `N t³ = 1`, `N^{-2/3} = t²`, `N^{1/3} t = 1`, `N⁻⁴ ≤ t²`. -/
private lemma norm_t_facts {N : ℕ} (hN : 1 ≤ N) :
    0 < (N : ℝ) ^ (-(1 / 3 : ℝ)) ∧ (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 ∧
      (N : ℝ) * ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 3 = 1 ∧
      (N : ℝ) ^ (-(2 / 3 : ℝ)) = ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 ∧
      (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) = 1 ∧
      1 / (N : ℝ) ^ 4 ≤ ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set t := (N : ℝ) ^ (-(1 / 3 : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have h3 : t ^ 3 = (N : ℝ)⁻¹ := by
    rw [ht, ← Real.rpow_mul_natCast hN0.le, ← Real.rpow_neg_one]
    norm_num
  have hNt : (N : ℝ) * t ^ 3 = 1 := by rw [h3]; field_simp
  refine ⟨ht0, ht1, hNt, ?_, ?_, ?_⟩
  · rw [ht, ← Real.rpow_mul_natCast hN0.le]
    norm_num
  · rw [ht, ← Real.rpow_add hN0]
    norm_num
  · have e : 1 / (N : ℝ) ^ 4 = t ^ 12 := by
      rw [show t ^ 12 = (t ^ 3) ^ 4 by ring, h3, inv_pow, one_div]
    rw [e]
    exact pow_le_pow_of_le_one ht0.le ht1 (by norm_num)

/-- `v = N^{1/32}` with `1000 v ≤ N^{1/8}` (from (S4)): `10 ≤ v`, `v³² = N`, `√N = v¹⁶`,
`N^{3/32} = v³`. -/
private lemma norm_v_facts {N : ℕ} (hN : 1 ≤ N)
    (hv : 1000 * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ)) :
    10 ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧ ((N : ℝ) ^ (1 / 32 : ℝ)) ^ 32 = N ∧
      Real.sqrt N = ((N : ℝ) ^ (1 / 32 : ℝ)) ^ 16 ∧
      (N : ℝ) ^ (3 / 32 : ℝ) = ((N : ℝ) ^ (1 / 32 : ℝ)) ^ 3 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set v := (N : ℝ) ^ (1 / 32 : ℝ) with hvdef
  have hv0 : 0 < v := Real.rpow_pos_of_pos hN0 _
  have hpow : ∀ n : ℕ, v ^ n = (N : ℝ) ^ ((1 / 32 : ℝ) * n) := fun n => by
    rw [hvdef, Real.rpow_mul_natCast hN0.le]
  have h4 : (N : ℝ) ^ (1 / 8 : ℝ) = v ^ 4 := by rw [hpow]; norm_num
  rw [h4] at hv
  have h10 : 10 ≤ v := by
    have h1 : 1000 ≤ v ^ 3 := by nlinarith [pow_pos hv0 3]
    by_contra hc
    push Not at hc
    have : v ^ 3 < 10 ^ 3 := pow_lt_pow_left₀ hc hv0.le (by norm_num)
    linarith
  refine ⟨h10, ?_, ?_, ?_⟩
  · rw [hpow]; norm_num
  · rw [hpow, Real.sqrt_eq_rpow]; norm_num
  · rw [hpow]; norm_num

/-! ### 2. The arithmetic of Steps 2 and 3 -/

/-- The arithmetic of Step 3. -/
private lemma norm_edge_ineq {u t η ϰ y Λ m P Q K : ℝ}
    (ht : 0 < t) (hut : u * t ^ 3 = 1) (hη1 : t ^ 2 ≤ η) (hη2 : η ≤ 2 * t ^ 2)
    (hK : 1000 ≤ K) (hP : 1 ≤ P) (hPQ : P * K ^ 4 = Q) (hϰ : Q * t / 2 ≤ ϰ)
    (hκ : Q ^ 2 * t ^ 2 / 2 ≤ ϰ ^ 2) (hy0 : 0 ≤ y) (hy : y ≤ 4 * (η / ϰ))
    (hΛ : Λ ≤ P * (y / (ϰ * (u * η)) + 1 / (ϰ * (u * η) ^ 2))) (hm : m ≤ y + Λ) :
    u * η * m < 1 / 2 := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hu : 0 < u := by nlinarith [pow_pos ht 3]
  have hη0 : 0 < η := lt_of_lt_of_le ht2 hη1
  have hK4 : (10 : ℝ) ^ 12 ≤ K ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000) hK 4
    norm_num at this ⊢; linarith
  have hQK : K ^ 4 ≤ Q := by rw [← hPQ]; nlinarith
  have hPQ' : P ≤ Q := by rw [← hPQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hϰ0 : 0 < ϰ := lt_of_lt_of_le (by positivity) hϰ
  set w := u * η with hw
  have hw0 : 0 < w := by positivity
  have htw : 1 ≤ t * w := by
    have : t * (u * t ^ 2) ≤ t * w := by rw [hw]; gcongr
    nlinarith
  -- `w m ≤ w y + P y / ϰ + P / (ϰ w)`
  have hA : w * m ≤ w * y + P * y / ϰ + P / (ϰ * w) := by
    have e : w * (P * (y / (ϰ * w) + 1 / (ϰ * w ^ 2))) = P * y / ϰ + P / (ϰ * w) := by
      field_simp
    have h1 : m ≤ y + P * (y / (ϰ * w) + 1 / (ϰ * w ^ 2)) := by linarith
    have := mul_le_mul_of_nonneg_left h1 hw0.le
    rw [mul_add, e] at this
    linarith
  -- the three terms
  have hT1 : w * y ≤ 32 / Q := by
    have h1 : y * ϰ ≤ 4 * η := by
      have := mul_le_mul_of_nonneg_right hy hϰ0.le
      rwa [show 4 * (η / ϰ) * ϰ = 4 * η by field_simp] at this
    have h2 : u * η ^ 2 ≤ 4 * t := by
      have : η ^ 2 ≤ 4 * t ^ 4 := by nlinarith
      nlinarith
    rw [le_div_iff₀ hQ0]
    have h3 : w * y * ϰ ≤ 16 * t := by rw [hw]; nlinarith
    nlinarith
  have hT2 : P * y / ϰ ≤ 16 / Q := by
    have h1 : y * ϰ ≤ 4 * η := by
      have := mul_le_mul_of_nonneg_right hy hϰ0.le
      rwa [show 4 * (η / ϰ) * ϰ = 4 * η by field_simp] at this
    rw [div_le_div_iff₀ hϰ0 hQ0]
    -- `P y Q ≤ 16 ϰ`: from `y ϰ² ≤ 4 η ϰ ≤ 8 t² ϰ` and `Q² t² ≤ 2 ϰ²`
    have h2 : y * ϰ * ϰ ≤ 8 * t ^ 2 * ϰ :=
      mul_le_mul_of_nonneg_right (by linarith) hϰ0.le
    have h3 : y * (Q ^ 2 * t ^ 2) ≤ y * (2 * ϰ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hy0
    have h4 : y * Q ^ 2 * t ^ 2 ≤ 16 * ϰ * t ^ 2 := by nlinarith
    have h5 : y * Q ^ 2 ≤ 16 * ϰ := le_of_mul_le_mul_right h4 ht2
    have h6 : P * y * Q ≤ Q * y * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPQ' hy0) hQ0.le
    nlinarith
  have hT3 : P / (ϰ * w) ≤ 2 / K ^ 4 := by
    have h0 : Q * t / 2 * w ≤ ϰ * w := mul_le_mul_of_nonneg_right hϰ hw0.le
    have h1 : Q / 2 ≤ Q / 2 * (t * w) := le_mul_of_one_le_right (by positivity) htw
    have h2 : Q * t / 2 * w = Q / 2 * (t * w) := by ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hfin : 32 / Q + 16 / Q + 2 / K ^ 4 < 1 / 2 := by
    have e1 : 32 / Q ≤ 32 / K ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hQK
    have e2 : 16 / Q ≤ 16 / K ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hQK
    have e3 : 50 / K ^ 4 < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have : 32 / K ^ 4 + 16 / K ^ 4 + 2 / K ^ 4 = 50 / K ^ 4 := by ring
    linarith
  linarith

/-- The arithmetic of Step 2. -/
private lemma norm_far_ineq {u s η y Λ m P : ℝ} (hs : 0 < s) (hus : s ^ 2 = u)
    (hη1 : 1 / (2 * s) ≤ η) (hη2 : η ≤ 1 / s) (hP : 0 ≤ P) (hPs : 100 * P ≤ s) (hy0 : 0 ≤ y)
    (hy : y ≤ η / 8) (hΛ : Λ ≤ P * (y / (u * η) + 1 / (u * η) ^ 2 + 1 / u)) (hm : m ≤ y + Λ) :
    u * η * m < 1 / 2 := by
  have hu : 0 < u := by rw [← hus]; positivity
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  set w := u * η with hw
  have hw0 : 0 < w := by positivity
  have hA : w * m ≤ w * y + P * (y + 1 / w + η) := by
    have e : w * (P * (y / w + 1 / w ^ 2 + 1 / u)) = P * (y + 1 / w + η) := by
      rw [hw]; field_simp
    have h1 : m ≤ y + P * (y / w + 1 / w ^ 2 + 1 / u) := by linarith
    have := mul_le_mul_of_nonneg_left h1 hw0.le
    rw [mul_add, e] at this
    linarith
  have hsη : s * η ≤ 1 := by rwa [le_div_iff₀ hs, mul_comm] at hη2
  have hsη' : 1 ≤ 2 * s * η := by rwa [div_le_iff₀ (by positivity), mul_comm] at hη1
  have hT1 : w * y ≤ 1 / 8 := by
    have : w * η ≤ 1 := by rw [hw, ← hus]; nlinarith
    nlinarith
  have hw2 : s ≤ 2 * w := by rw [hw, ← hus]; nlinarith
  have h1w : 1 / w ≤ 2 / s := by
    rw [div_le_div_iff₀ hw0 hs]; linarith
  have hηs : η ≤ 1 / s := hη2
  have hys : y ≤ 1 / (8 * s) := by
    calc y ≤ η / 8 := hy
      _ ≤ (1 / s) / 8 := by gcongr
      _ = 1 / (8 * s) := by field_simp
  have hT2 : P * (y + 1 / w + η) ≤ P * (25 / (8 * s)) := by
    apply mul_le_mul_of_nonneg_left _ hP
    have : 1 / (8 * s) + 2 / s + 1 / s = 25 / (8 * s) := by field_simp; ring
    linarith
  have hT3 : P * (25 / (8 * s)) ≤ 1 / 32 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-! ### 3. The lattice points of Steps 2 and 3 -/

/-- `N^{-2/3} ≤ η_e ≤ 2 N^{-2/3}`, written with `t = N^{-1/3}`. -/
private lemma norm_etaE_bounds {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 ≤ etaE N ∧ etaE N ≤ 2 * ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := by
  obtain ⟨-, -, -, ht2, -, ht4⟩ := norm_t_facts hN
  have hD : (0 : ℝ) < (N : ℝ) ^ 4 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  obtain ⟨h1, h2⟩ := norm_height ((N : ℝ) ^ (-(2 / 3 : ℝ))) hD
  change _ ≤ etaE N at h1
  change etaE N ≤ _ at h2
  rw [ht2] at h1 h2
  exact ⟨h1, by linarith⟩

/-- `N^{-1/2}/2 ≤ η_f ≤ N^{-1/2}`, and `N^{-4} ≤ N^{-1/2}/2`. -/
private lemma norm_etaF_bounds {N : ℕ} (hN : 2 ≤ N) :
    1 / (2 * Real.sqrt N) ≤ etaF N ∧ etaF N ≤ 1 / Real.sqrt N ∧
      1 / (N : ℝ) ^ 4 ≤ 1 / (2 * Real.sqrt N) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hD : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsN : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left hN0.le]; nlinarith
  have h4 : 1 / (N : ℝ) ^ 4 ≤ 1 / (2 * Real.sqrt N) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN2 3]
  obtain ⟨h1, h2⟩ := norm_height (1 / (2 * Real.sqrt N)) hD
  change _ ≤ etaF N at h1
  change etaF N ≤ _ at h2
  refine ⟨h1, ?_, h4⟩
  have : 1 / (2 * Real.sqrt N) + 1 / (2 * Real.sqrt N) = 1 / Real.sqrt N := by
    field_simp; ring
  linarith

/-- Step 3, covering: every `y` with `2 + K^{C₃} N^{-2/3} < |y| ≤ 5` lies within `η_e` of a point
of `𝔼_e`. -/
private lemma norm_edge_cover {N : ℕ} (hN : 1 ≤ N) {a K : ℝ} (ha : 1 ≤ a) (hK : 2 ≤ K) :
    0 < etaE N ∧ ∀ y : ℝ, 2 + K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) < |y| → |y| ≤ 5 →
      ∃ E ∈ energiesE a K N, |y - E| ≤ etaE N := by
  obtain ⟨ht0, -, -, ht2, -, ht4⟩ := norm_t_facts hN
  obtain ⟨hη1, -⟩ := norm_etaE_bounds hN
  have hD : (0 : ℝ) < (N : ℝ) ^ 4 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hKC : 2 ≤ K ^ ledgerC3 a := by
    refine le_trans hK ?_
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ K)
      (show (1 : ℝ) ≤ ledgerC3 a by unfold ledgerC3; linarith)
    rwa [Real.rpow_one] at this
  rw [ht2]
  set t := (N : ℝ) ^ (-(1 / 3 : ℝ))
  refine ⟨lt_of_lt_of_le (by positivity) hη1, fun y hy1 hy2 => ?_⟩
  obtain ⟨m, hm1, hm2, hm3⟩ := norm_round_down y hD
  have hs : t ^ 2 ≤ K ^ ledgerC3 a * t ^ 2 / 2 := by nlinarith [sq_nonneg t]
  refine ⟨m / (N : ℝ) ^ 4, ⟨m, rfl, by rw [ht2]; linarith, by linarith⟩, by linarith⟩

/-- Step 2, covering: every `y` with `5 < |y| ≤ E_max` lies within `η_f` of a point of `𝔼_f`. -/
private lemma norm_far_cover {N : ℕ} (hN : 2 ≤ N) {a C₀ K : ℝ} :
    0 < etaF N ∧ ∀ y : ℝ, 5 < |y| → |y| ≤ levelEmax a C₀ K N →
      ∃ E ∈ energiesF a C₀ K N, |y - E| ≤ etaF N := by
  obtain ⟨hη1, -, h4⟩ := norm_etaF_bounds hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hD : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have h1 : 1 / (N : ℝ) ^ 4 ≤ 1 := by
    rw [div_le_one hD]; exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ N by omega))
  refine ⟨lt_of_lt_of_le (by positivity) hη1, fun y hy1 hy2 => ?_⟩
  obtain ⟨m, hm1, hm2, hm3⟩ := norm_round_up y hD
  exact ⟨m / (N : ℝ) ^ 4, ⟨m, rfl, by linarith, by linarith⟩, by linarith⟩

/-- The powers of `K` in Step 3, with `P = K^{b+2}`, `Q = K^{b+6}`: `1 ≤ P`, `P K⁴ = Q`,
`K^{C₃} = Q²` (as `C₃ = 2b + 12`), `K^{b+3} ≤ Q/2`, and `1000 ≤ K⁴ ≤ Q`. -/
private lemma norm_K_powers {a K : ℝ} (ha : 1 ≤ a) (hK : 1000 ≤ K) :
    1 ≤ K ^ (ledgerB a + 2) ∧ K ^ (ledgerB a + 2) * K ^ 4 = K ^ (ledgerB a + 6) ∧
      K ^ ledgerC3 a = (K ^ (ledgerB a + 6)) ^ 2 ∧
      K ^ (ledgerB a + 3) ≤ K ^ (ledgerB a + 6) / 2 ∧ 1000 ≤ K ^ 4 ∧
      K ^ 4 ≤ K ^ (ledgerB a + 6) := by
  have hK1 : 1 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hPQ : K ^ (ledgerB a + 2) * K ^ 4 = K ^ (ledgerB a + 6) := by
    rw [show ledgerB a + 6 = ledgerB a + 2 + ((4 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hKpos (ledgerB a + 2), Real.rpow_natCast]
  have hP1 : 1 ≤ K ^ (ledgerB a + 2) := Real.one_le_rpow hK1 (by unfold ledgerB; linarith)
  have hC3 : K ^ ledgerC3 a = (K ^ (ledgerB a + 6)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hKpos.le]
    congr 1
    unfold ledgerC3 ledgerB
    push_cast
    ring
  have hB3 : K ^ (ledgerB a + 3) * K ^ 3 = K ^ (ledgerB a + 6) := by
    rw [show ledgerB a + 6 = ledgerB a + 3 + ((3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hKpos (ledgerB a + 3), Real.rpow_natCast]
  have hK3 : 2 ≤ K ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1000) hK 3]
  have hK4 : 1000 ≤ K ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hK1 3]
  have hB0 : 0 ≤ K ^ (ledgerB a + 3) := Real.rpow_nonneg hKpos.le _
  refine ⟨hP1, hPQ, hC3, ?_, hK4, ?_⟩
  · rw [← hB3]; nlinarith
  · rw [← hPQ]; nlinarith

/-- Step 3 at `E ∈ 𝔼_e` and `z = E + iη_e`: `z ∈ 𝕃 ∩ 𝐃^near`, `z` is of type (a)
(`ϰ N η_e ≥ K^{b+3}`), and on `𝒢³(z)`, `N η_e Im m(z) < 1/2`. -/
private lemma norm_edge_point {N : ℕ} (M : Ensemble 𝕜 N) {a C₀ K : ℝ} (ha : 1 ≤ a) (hN : 1 ≤ N)
    (hK : 1000 ≤ K) (hKN : K ≤ (N : ℝ) ^ ledgerc0 a) {E : ℝ} (hE : E ∈ energiesE a K N) :
    ((E : ℂ) + (etaE N : ℂ) * Complex.I) ∈ lattice a C₀ K N ∩ Dnear a K N ∧
      K ^ (ledgerB a + 3) ≤ varkappa ((E : ℂ) + (etaE N : ℂ) * Complex.I) *
        (N * ((E : ℂ) + (etaE N : ℂ) * Complex.I).im) ∧
      ∀ x ∈ strongG3 M a C₀ K ((E : ℂ) + (etaE N : ℂ) * Complex.I),
        (N : ℝ) * etaE N *
          (stieltjesEmp (toMatrix x) ((E : ℂ) + (etaE N : ℂ) * Complex.I)).im < 1 / 2 := by
  obtain ⟨m, rfl, hE1, hE2⟩ := hE
  obtain ⟨ht0, ht1, hNt, ht2, ht13, -⟩ := norm_t_facts hN
  obtain ⟨hη1, hη2⟩ := norm_etaE_bounds hN
  obtain ⟨hP1, hPQ, hC3, hB3, hK4, hQK⟩ := norm_K_powers ha hK
  obtain ⟨-, -, hT5⟩ := strong_T5 ha hN (by linarith) hKN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid := norm_mem_grid (N := N) m (h := (N : ℝ) ^ (-(2 / 3 : ℝ)))
    (by rw [ht2]; nlinarith [pow_le_one₀ ht0.le ht1 (n := 2)])
  rw [ht2] at hE1
  rw [hC3] at hE1
  have e1 : (N : ℝ) ^ (1 / 3 : ℝ) / N = ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [div_eq_iff hN0.ne']
    linear_combination (-((N : ℝ) ^ (1 / 3 : ℝ))) * hNt +
      (((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 * N) * ht13
  have hT5' : K ^ (ledgerC1 a - 1) / N ≤ ((N : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [← e1]; exact div_le_div_of_nonneg_right hT5 hN0.le
  change ((m / (N : ℝ) ^ 4 : ℝ) : ℂ) + (etaE N : ℂ) * Complex.I ∈ gridPts N at hgrid
  generalize (N : ℝ) ^ (-(1 / 3 : ℝ)) = t at *
  generalize etaE N = η at *
  generalize (m : ℝ) / (N : ℝ) ^ 4 = E at *
  generalize K ^ (ledgerB a + 6) = Q at *
  generalize K ^ (ledgerB a + 3) = B at *
  set z : ℂ := (E : ℂ) + (η : ℂ) * Complex.I with hz
  have hzre : z.re = E := by simp [hz]
  have hzim : z.im = η := by simp [hz]
  clear_value z
  have ht21 : t ^ 2 ≤ 1 := pow_le_one₀ ht0.le ht1
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hQ0 : 0 < Q := by linarith
  have hκpos : 0 < Q ^ 2 * t ^ 2 / 2 := by positivity
  have hκ : kappaE E = |E| - 2 := by
    unfold kappaE; rw [abs_of_nonneg (by linarith)]
  have hϰsq : varkappa z ^ 2 = kappaE E + η := by
    unfold varkappa; rw [hzre, hzim]; exact Real.sq_sqrt (by rw [hκ]; linarith)
  have hκsq : Q ^ 2 * t ^ 2 / 2 ≤ varkappa z ^ 2 := by rw [hϰsq, hκ]; linarith
  have hϰ : Q * t / 2 ≤ varkappa z := by
    unfold varkappa; rw [hzre, hzim]
    rw [Real.le_sqrt (by positivity) (by rw [hκ]; linarith), hκ]
    have : (Q * t / 2) ^ 2 = Q ^ 2 * t ^ 2 / 4 := by ring
    linarith
  have hηκ : η ≤ kappaE E := by
    have hQ4 : 4 ≤ Q ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_right hQ4 (sq_nonneg t)
    rw [hκ]; linarith only [hE1, hη2, h4]
  have hnear : z ∈ Dnear a K N := by
    refine ⟨by rw [hzre]; exact hE2, ?_, by rw [hzim]; linarith⟩
    rw [hzim]; linarith
  have hNη : 1 ≤ t * (N * η) := by
    have : t * (N * t ^ 2) ≤ t * (N * η) := by gcongr
    have e : t * (N * t ^ 2) = N * t ^ 3 := by ring
    linarith
  have hϰNη : Q / 2 ≤ varkappa z * (N * η) := by
    have h0 : Q * t / 2 * (N * η) ≤ varkappa z * (N * η) :=
      mul_le_mul_of_nonneg_right hϰ (by positivity)
    have h1 : Q / 2 ≤ Q / 2 * (t * (N * η)) := le_mul_of_one_le_right (by positivity) hNη
    have e : Q * t / 2 * (N * η) = Q / 2 * (t * (N * η)) := by ring
    linarith
  refine ⟨⟨⟨Or.inl hnear, hgrid⟩, hnear⟩, by rw [hzim]; linarith, fun x hx => ?_⟩
  have hΛ := hx.2
  simp only [Set.mem_ofPred_eq] at hΛ
  rw [hzim] at hΛ
  have hmsc := (msc_im_size_edge (z := z) (by rw [hzre]; exact hE2) (by rw [hzim]; exact hη0)
    (by rw [hzim]; linarith) (by rw [hzre]; linarith) (by rw [hzre, hzim]; exact hηκ)).2
  rw [hzim] at hmsc
  exact norm_edge_ineq ht0 hNt hη1 hη2 hK hP1 hPQ hϰ hκsq
    (msc_im_pos (by rw [hzim]; exact hη0)).le hmsc hΛ (norm_im_le x z)

/-- Step 2 at `E ∈ 𝔼_f` and `z = E + iη_f`: `z ∈ 𝕃 ∩ 𝐃^far`, and on `𝒢^f(z)`,
`N η_f Im m(z) < 1/2`. -/
private lemma norm_far_point {N : ℕ} (M : Ensemble 𝕜 N) {a C₀ K : ℝ} (ha : 1 ≤ a) (hN : 2 ≤ N)
    (hK : 1 ≤ K) (hKN : K ≤ (N : ℝ) ^ ledgerc0 a)
    (hv : 1000 * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ)) {E : ℝ}
    (hE : E ∈ energiesF a C₀ K N) :
    ((E : ℂ) + (etaF N : ℂ) * Complex.I) ∈ lattice a C₀ K N ∩ Dfar a C₀ K N ∧
      ∀ x ∈ strongGf M a C₀ K ((E : ℂ) + (etaF N : ℂ) * Complex.I),
        (N : ℝ) * etaF N *
          (stieltjesEmp (toMatrix x) ((E : ℂ) + (etaF N : ℂ) * Complex.I)).im < 1 / 2 := by
  obtain ⟨m, rfl, hE1, hE2⟩ := hE
  obtain ⟨hη1, hη2, -⟩ := norm_etaF_bounds hN
  obtain ⟨hv10, -, hvs, hv3⟩ := norm_v_facts (by omega) hv
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  set η := etaF N with hη
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  set E := (m : ℝ) / (N : ℝ) ^ 4 with hEdef
  set z : ℂ := (E : ℂ) + (η : ℂ) * Complex.I with hz
  have hzre : z.re = E := by simp [hz]
  have hzim : z.im = η := by simp [hz]
  obtain ⟨-, hT5, -⟩ := strong_T5 ha (by omega) hK hKN
  set P := K ^ (ledgerB a + 2) with hP
  set v := (N : ℝ) ^ (1 / 32 : ℝ) with hvdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  have hPs : 100 * P ≤ Real.sqrt N := by
    rw [hvs]
    rw [hv3] at hT5
    have h13 : (100 : ℝ) ≤ v ^ 13 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hv10 13]
    have : v ^ 16 = v ^ 13 * v ^ 3 := by ring
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ v by linarith) 3]
  have hη10 : η ≤ 10 := by
    have : 1 / Real.sqrt N ≤ 1 := by
      rw [div_le_one hs0, hvs]; nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ v by linarith) (n := 16)]
    linarith
  have hfar : z ∈ Dfar a C₀ K N := by
    refine ⟨by rw [hzre]; linarith, by rw [hzre]; exact hE2, by rw [hzim]; exact hη1,
      by rw [hzim]; exact hη10⟩
  have hgrid : z ∈ gridPts N := by
    refine norm_mem_grid m (h := 1 / (2 * Real.sqrt N)) ?_
    have : 0 < 1 / (2 * Real.sqrt N) := by positivity
    have : 1 / (2 * Real.sqrt N) ≤ η := hη1
    linarith
  refine ⟨⟨⟨Or.inr hfar, hgrid⟩, hfar⟩, fun x hx => ?_⟩
  have hΛ := hx.2
  simp only [Set.mem_ofPred_eq] at hΛ
  rw [hzim] at hΛ
  have hmsc := (msc_far (z := z) (by rw [hzim]; exact hη0) (by rw [hzre]; linarith)).2.1
  rw [hzim] at hmsc
  exact norm_far_ineq hs0 (Real.sq_sqrt hN0.le) hη1 hη2 hP0 hPs
    (msc_im_pos (by rw [hzim]; exact hη0)).le hmsc hΛ (norm_im_le x z)

/-! ### 4. Counting and the union bound -/

/-- `|𝔼_e| ≤ 10 N⁴ + 1 ≤ N⁵`. -/
private lemma norm_card_energiesE {N : ℕ} (hN : 11 ≤ N) (a K : ℝ) :
    (energiesE a K N).Finite ∧ ((energiesE a K N).ncard : ℝ) ≤ (N : ℝ) ^ 5 := by
  have hN11 : (11 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  obtain ⟨hfin, hcard⟩ := norm_card_le (energiesE a K N) (R := 5) (by norm_num) hD
    fun E hE => by obtain ⟨m, hm, -, h5⟩ := hE; exact ⟨m, hm, h5⟩
  refine ⟨hfin, hcard.trans ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by linarith)
  have : (N : ℝ) ^ 5 = N * (N : ℝ) ^ 4 := by ring
  nlinarith

/-- `|𝔼_f| ≤ 2 (E_max + 1) N⁴ + 1 ≤ N⁵`, for `1 ≤ E_max ≤ N^{1/32}` and
`1000 N^{1/32} ≤ N^{1/8}`. -/
private lemma norm_card_energiesF {N : ℕ} (hN : 1 ≤ N) {a C₀ K : ℝ}
    (hE1 : 1 ≤ levelEmax a C₀ K N) (hE2 : levelEmax a C₀ K N ≤ (N : ℝ) ^ (1 / 32 : ℝ))
    (hv : 1000 * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ)) :
    (energiesF a C₀ K N).Finite ∧ ((energiesF a C₀ K N).ncard : ℝ) ≤ (N : ℝ) ^ 5 := by
  obtain ⟨hv10, hv32, -, -⟩ := norm_v_facts hN hv
  set v := (N : ℝ) ^ (1 / 32 : ℝ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  obtain ⟨hfin, hcard⟩ := norm_card_le (energiesF a C₀ K N) (R := levelEmax a C₀ K N + 1)
    (by linarith) hD fun E hE => by obtain ⟨m, hm, -, h5⟩ := hE; exact ⟨m, hm, h5⟩
  refine ⟨hfin, hcard.trans ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
  have hvN : 2 * v + 3 ≤ N := by
    rw [← hv32]
    have : v ^ 2 ≤ v ^ 32 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have : (N : ℝ) ^ 5 = N * (N : ℝ) ^ 4 := by ring
  nlinarith

/-- The union bound over a finite set of energies. -/
private lemma norm_measure_biUnion_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {S : Set ℝ} (hS : S.Finite) (f : ℝ → Set α) {c : ℝ}
    (hf : ∀ E ∈ S, μ (f E) ≤ ENNReal.ofReal c) :
    μ (⋃ E ∈ S, f E) ≤ ENNReal.ofReal ((S.ncard : ℝ) * c) := by
  have hU : (⋃ E ∈ S, f E) = ⋃ E ∈ hS.toFinset, f E := by simp
  calc μ (⋃ E ∈ S, f E) = μ (⋃ E ∈ hS.toFinset, f E) := by rw [hU]
    _ ≤ ∑ E ∈ hS.toFinset, μ (f E) := measure_biUnion_finset_le _ _
    _ ≤ hS.toFinset.card • ENNReal.ofReal c :=
        Finset.sum_le_card_nsmul _ _ _ fun E hE => hf E (hS.mem_toFinset.1 hE)
    _ = ENNReal.ofReal ((S.ncard : ℝ) * c) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          Set.ncard_eq_toFinset_card _ hS]

/-- `μ(Sᶜ) ≤ μ(Tᶜ) + μ(T ∖ S)`. -/
private lemma norm_measure_compl_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S T : Set α) : μ Sᶜ ≤ μ Tᶜ + μ (T \ S) := by
  have hsub : Sᶜ ⊆ Tᶜ ∪ (T \ S) := by
    intro x hx
    by_cases h : x ∈ T
    · exact Or.inr ⟨h, hx⟩
    · exact Or.inl h
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- The final count of the probability bound:
`(N² a + 1 + 460 a N¹³ + N¹⁵) e^{-p₁} + 2 N⁵ e^{-p₂} ≤ N²¹ e^{-p₁} + N⁶ e^{-p₂}` for `a ≤ N`,
`N ≥ 13`, with `Z = e^{-K²} ≤ e^{-p₁}` and `W = e^{-N log N} ≤ e^{-p₁}`. -/
private lemma norm_prob_arith {N ϑ Z W X1 X2 nF nE : ℝ} (hN13 : 13 ≤ N) (hϑ : 0 < ϑ)
    (hϑN : 1 / ϑ ≤ N) (hZ0 : 0 ≤ Z) (hZ : Z ≤ X1) (hW : W ≤ X1) (hX2 : 0 ≤ X2)
    (hnF : nF ≤ N ^ 5) (hnE : nE ≤ N ^ 5) :
    N ^ 2 / ϑ * Z + 2 * W + nF * (460 / ϑ * N ^ 8 * Z + X2) + nE * (N ^ 10 * X1 + X2) ≤
      N ^ 21 * X1 + N ^ 6 * X2 := by
  have hNpos : 0 < N := by linarith
  have hX1 : 0 ≤ X1 := hZ0.trans hZ
  have hcF : 0 ≤ 460 / ϑ * N ^ 8 * Z + X2 := by positivity
  have hcE : 0 ≤ N ^ 10 * X1 + X2 := by positivity
  have e1 : N ^ 2 / ϑ * Z ≤ N ^ 3 * X1 := by
    have : N ^ 2 / ϑ = N ^ 2 * (1 / ϑ) := by ring
    rw [this, show N ^ 3 = N ^ 2 * N by ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hϑN (by positivity)) hZ hZ0 (by positivity)
  have e2 : 460 / ϑ * N ^ 8 * Z + X2 ≤ 460 * N ^ 9 * X1 + X2 := by
    have : 460 / ϑ * N ^ 8 = 460 * N ^ 8 * (1 / ϑ) := by ring
    rw [this, show 460 * N ^ 9 = 460 * N ^ 8 * N by ring]
    have := mul_le_mul (mul_le_mul_of_nonneg_left hϑN (by positivity : (0 : ℝ) ≤ 460 * N ^ 8))
      hZ hZ0 (by positivity)
    linarith
  have e3 : nF * (460 / ϑ * N ^ 8 * Z + X2) ≤ N ^ 5 * (460 * N ^ 9 * X1 + X2) :=
    mul_le_mul hnF e2 hcF (by positivity)
  have e4 : nE * (N ^ 10 * X1 + X2) ≤ N ^ 5 * (N ^ 10 * X1 + X2) :=
    mul_le_mul_of_nonneg_right hnE hcE
  have e5 : N ^ 3 + 2 + 460 * N ^ 14 + N ^ 15 ≤ N ^ 21 := by
    have h1 : (1 : ℝ) ≤ N := by linarith
    have a1 : N ^ 3 ≤ N ^ 15 := pow_le_pow_right₀ h1 (by norm_num)
    have a2 : (1 : ℝ) ≤ N ^ 15 := one_le_pow₀ h1
    have a3 : N ^ 14 ≤ N ^ 15 := pow_le_pow_right₀ h1 (by norm_num)
    have a4 : (13 : ℝ) ^ 6 ≤ N ^ 6 := pow_le_pow_left₀ (by norm_num) hN13 6
    have a5 : N ^ 21 = N ^ 6 * N ^ 15 := by ring
    have a6 : (13 : ℝ) ^ 6 * N ^ 15 ≤ N ^ 6 * N ^ 15 := mul_le_mul_of_nonneg_right a4 (by linarith)
    norm_num at a6
    linarith
  have e6 : 2 * N ^ 5 ≤ N ^ 6 := by
    have : N ^ 6 = N * N ^ 5 := by ring
    have h5 : 0 < N ^ 5 := pow_pos hNpos 5
    nlinarith
  have e7 : N ^ 3 * X1 + 2 * X1 + N ^ 5 * (460 * N ^ 9 * X1 + X2) + N ^ 5 * (N ^ 10 * X1 + X2) =
      (N ^ 3 + 2 + 460 * N ^ 14 + N ^ 15) * X1 + 2 * N ^ 5 * X2 := by ring
  have e8 := mul_le_mul_of_nonneg_right e5 hX1
  have e9 := mul_le_mul_of_nonneg_right e6 hX2
  linarith

/-- The probability bound of Proposition 8.1, from Step 1 (Lemma 4.5), the counts of `𝔼_f`, `𝔼_e`,
and the bounds at the points of `𝔼_f`, `𝔼_e`. -/
private lemma norm_prob {N : ℕ} (M : Ensemble 𝕜 N) {ϑ C₀ K : ℝ} (hϑ : 0 < ϑ) (hN13 : 13 ≤ N)
    (hNa : ϑ⁻¹ ≤ N) (hp1 : (levelP1 K : ℝ) ≤ K ^ 2) (hK2N : K ^ 2 ≤ N * Real.log N)
    (hA : M.prodLaw {x | levelEmax ϑ⁻¹ C₀ K N < ‖toMatrix x‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-K ^ 2) + 2 * Real.exp (-(N * Real.log N))))
    (hFfin : (energiesF ϑ⁻¹ C₀ K N).Finite)
    (hFcard : ((energiesF ϑ⁻¹ C₀ K N).ncard : ℝ) ≤ (N : ℝ) ^ 5)
    (hEfin : (energiesE ϑ⁻¹ K N).Finite) (hEcard : ((energiesE ϑ⁻¹ K N).ncard : ℝ) ≤ (N : ℝ) ^ 5)
    (hBf : ∀ E ∈ energiesF ϑ⁻¹ C₀ K N,
      M.prodLaw (strongGf M ϑ⁻¹ C₀ K ((E : ℂ) + (etaF N : ℂ) * Complex.I))ᶜ ≤
        ENNReal.ofReal (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2) + Real.exp (-(levelP2 K : ℝ))))
    (hBe : ∀ E ∈ energiesE ϑ⁻¹ K N,
      M.prodLaw (strongG3 M ϑ⁻¹ C₀ K ((E : ℂ) + (etaE N : ℂ) * Complex.I))ᶜ ≤
        ENNReal.ofReal ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)) +
          Real.exp (-(levelP2 K : ℝ)))) :
    M.prodLaw (strongXi2 M ϑ⁻¹ C₀ K)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ 21 *
      Real.exp (-(levelP1 K : ℝ)) + (N : ℝ) ^ 6 * Real.exp (-(levelP2 K : ℝ))) := by
  have hcompl : (strongXi2 M ϑ⁻¹ C₀ K)ᶜ ⊆ {x | levelEmax ϑ⁻¹ C₀ K N < ‖toMatrix x‖} ∪
      (⋃ E ∈ energiesF ϑ⁻¹ C₀ K N,
        (strongGf M ϑ⁻¹ C₀ K ((E : ℂ) + (etaF N : ℂ) * Complex.I))ᶜ) ∪
      ⋃ E ∈ energiesE ϑ⁻¹ K N,
        (strongG3 M ϑ⁻¹ C₀ K ((E : ℂ) + (etaE N : ℂ) * Complex.I))ᶜ := by
    intro x hx
    by_contra hc
    apply hx
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or,
      not_exists, not_not, not_lt] at hc
    obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
    exact ⟨⟨hc1, Set.mem_iInter₂.2 hc2⟩, Set.mem_iInter₂.2 hc3⟩
  have hN13' : (13 : ℝ) ≤ N := by exact_mod_cast hN13
  have hZ : Real.exp (-K ^ 2) ≤ Real.exp (-(levelP1 K : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have hW : Real.exp (-(N * Real.log N)) ≤ Real.exp (-(levelP1 K : ℝ)) :=
    Real.exp_le_exp.2 (by linarith)
  have hfin := norm_prob_arith (ϑ := ϑ) hN13' hϑ (by rw [one_div]; exact hNa)
    (Real.exp_pos _).le hZ hW (Real.exp_pos (-(levelP2 K : ℝ))).le hFcard hEcard
  calc M.prodLaw (strongXi2 M ϑ⁻¹ C₀ K)ᶜ
      ≤ M.prodLaw ({x | levelEmax ϑ⁻¹ C₀ K N < ‖toMatrix x‖} ∪
          (⋃ E ∈ energiesF ϑ⁻¹ C₀ K N,
            (strongGf M ϑ⁻¹ C₀ K ((E : ℂ) + (etaF N : ℂ) * Complex.I))ᶜ) ∪
          ⋃ E ∈ energiesE ϑ⁻¹ K N,
            (strongG3 M ϑ⁻¹ C₀ K ((E : ℂ) + (etaE N : ℂ) * Complex.I))ᶜ) := measure_mono hcompl
    _ ≤ M.prodLaw {x | levelEmax ϑ⁻¹ C₀ K N < ‖toMatrix x‖} +
          M.prodLaw (⋃ E ∈ energiesF ϑ⁻¹ C₀ K N,
            (strongGf M ϑ⁻¹ C₀ K ((E : ℂ) + (etaF N : ℂ) * Complex.I))ᶜ) +
          M.prodLaw (⋃ E ∈ energiesE ϑ⁻¹ K N,
            (strongG3 M ϑ⁻¹ C₀ K ((E : ℂ) + (etaE N : ℂ) * Complex.I))ᶜ) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-K ^ 2) +
            2 * Real.exp (-(N * Real.log N))) +
          ENNReal.ofReal ((energiesF ϑ⁻¹ C₀ K N).ncard *
            (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2) + Real.exp (-(levelP2 K : ℝ)))) +
          ENNReal.ofReal ((energiesE ϑ⁻¹ K N).ncard * ((N : ℝ) ^ 10 *
            Real.exp (-(levelP1 K : ℝ)) + Real.exp (-(levelP2 K : ℝ)))) :=
        add_le_add (add_le_add hA (norm_measure_biUnion_le _ hFfin _ hBf))
          (norm_measure_biUnion_le _ hEfin _ hBe)
    _ = ENNReal.ofReal ((N : ℝ) ^ 2 / ϑ * Real.exp (-K ^ 2) +
            2 * Real.exp (-(N * Real.log N)) +
          (energiesF ϑ⁻¹ C₀ K N).ncard *
            (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2) + Real.exp (-(levelP2 K : ℝ))) +
          (energiesE ϑ⁻¹ K N).ncard * ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)) +
            Real.exp (-(levelP2 K : ℝ)))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

/-! ### 5. Proposition 8.1

Step 1 is Lemma 4.5 at `κ = K²`; Steps 2 and 3 are `norm_far_point` and `norm_edge_point`, with
the coverings `norm_far_cover` and `norm_edge_cover`. The probability bound is the union bound
over `𝔼_f` and `𝔼_e` (at most `N⁵` points each), with
`ℙ(𝒢^f(z)ᶜ) ≤ ℙ(𝒢_col(z)ᶜ) + ℙ(𝒢_col(z) ∖ 𝒢^f(z))` and
`ℙ(𝒢³(z)ᶜ) ≤ ℙ(𝒢²(z)ᶜ) + ℙ(𝒢²(z) ∖ 𝒢³(z))`. -/

/-- Proposition 8.1 for the explicit event `Ξ_K^{(2)}`. -/
theorem norm_bound_strongXi2 {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
        IsClosed (strongXi2 M ϑ⁻¹ C₀ K) ∧
        M.prodLaw (strongXi2 M ϑ⁻¹ C₀ K)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ 21 *
          Real.exp (-(levelP1 K : ℝ)) + (N : ℝ) ^ 6 * Real.exp (-(levelP2 K : ℝ))) ∧
        ∀ x ∈ strongXi2 M ϑ⁻¹ C₀ K, ∀ k,
          |eig x k| ≤ 2 + K ^ ledgerC3 ϑ⁻¹ * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨N₁, h1⟩ := strong_improved (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := strong_far (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₃, h3⟩ := strong_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₄, h4⟩ := lattice_card (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₅, h5⟩ := standing_ineq hϑ hϑ1 hC₀ 1000
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ ⌈ϑ⁻¹⌉₊), ?_⟩
  intro N hN M hM K hK1 hK2
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : N₅ ≤ N := by omega
  have hNa : ϑ⁻¹ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈ϑ⁻¹⌉₊ ≤ N by omega))
  obtain ⟨⟨hK0, h13, hC0N, hκ⟩, ⟨-, -, hE1, hE2⟩, ⟨hP1, -, -, -, -⟩, hS4a, hS4b⟩ :=
    h5 N hN5 K hK1 hK2
  have hN13 : (13 : ℝ) ≤ N := by exact_mod_cast h13
  have hNpos : (0 : ℝ) < N := by linarith
  have hKpos : 0 < K := by linarith
  have hNn1 : 1 ≤ N := by omega
  have hNn2 : 2 ≤ N := by omega
  have hNn11 : 11 ≤ N := by omega
  have hv1 : (N : ℝ) ^ (1 / 32 : ℝ) ≤ N := Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hK6 : K ^ 2 ≤ K ^ (6 * ϑ⁻¹ + 6) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hEv : levelEmax ϑ⁻¹ C₀ K N ≤ (N : ℝ) ^ (1 / 32 : ℝ) :=
    hE2.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hS4a)
  obtain ⟨hFfin, hFcard⟩ := norm_card_energiesF hNn1 hE1 hEv hS4b
  obtain ⟨hEfin, hEcard⟩ := norm_card_energiesE hNn11 ϑ⁻¹ K
  have hedge := fun E (hE : E ∈ energiesE ϑ⁻¹ K N) =>
    norm_edge_point M (C₀ := C₀) ha hNn1 hK0 hK2 hE
  have hfar := fun E (hE : E ∈ energiesF ϑ⁻¹ C₀ K N) =>
    norm_far_point M ha hNn2 (by linarith) hK2 hS4b hE
  refine ⟨?_, ?_, ?_⟩
  -- closedness
  · refine IsClosed.inter (IsClosed.inter (norm_isClosed_norm_le _) ?_) ?_
    · exact isClosed_biInter fun E hE => (h2 N hN2 M hM K hK1 hK2 _ (hfar E hE).1).1
    · exact isClosed_biInter fun E hE =>
        (h1 N hN1 M hM K hK1 hK2 _ (hedge E hE).1 (hedge E hE).2.1).1
  -- the probability bound
  · have hsq : Real.sqrt C₀ ≤ N := by
      rw [Real.sqrt_le_left (by positivity)]
      exact hC0N
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le hNpos]
      have := Real.exp_one_lt_d9
      linarith
    have hp1 : (levelP1 K : ℝ) ≤ K ^ 2 := by
      have h0 : (0 : ℝ) ≤ levelP1 K := Nat.cast_nonneg _
      have : (levelP1 K : ℝ) * 1 ≤ levelP1 K * Real.log N := mul_le_mul_of_nonneg_left hlog h0
      linarith
    have hK2N : K ^ 2 ≤ N * Real.log N := by
      have : (N : ℝ) * 1 ≤ N * Real.log N := mul_le_mul_of_nonneg_left hlog hNpos.le
      linarith
    refine norm_prob M hϑ h13 hNa hp1 hK2N (prodLaw_norm_gt M hM hϑ hϑ1 hC₀ h13 hsq hκ)
      hFfin hFcard hEfin hEcard (fun E hE => ?_) (fun E hE => ?_)
    · have hz := (hfar E hE).1
      exact (norm_measure_compl_le _ _ (goodCol M ϑ⁻¹ C₀ K _)).trans
        ((add_le_add ((h4 N hN4 K hK1 hK2).2.2 M hM _ hz.1) (h2 N hN2 M hM K hK1 hK2 _ hz).2).trans
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm.le)
    · obtain ⟨hz, hza, -⟩ := hedge E hE
      exact (norm_measure_compl_le _ _ (strongG2 M ϑ⁻¹ C₀ K _)).trans
        ((add_le_add (h3 N hN3 M hM K hK1 hK2 _ hz).2.1
          (h1 N hN1 M hM K hK1 hK2 _ hz hza).2).trans
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm.le)
  -- the eigenvalues
  · intro x hx k
    obtain ⟨⟨hxn, hxf⟩, hxe⟩ := hx
    by_contra hlt
    rw [not_le] at hlt
    have hlam : |eig x k| ≤ levelEmax ϑ⁻¹ C₀ K N := (norm_abs_eig_le x k).trans hxn
    rcases le_or_gt |eig x k| 5 with h5 | h5
    · obtain ⟨hη0, hcov⟩ := norm_edge_cover hNn1 ha (by linarith : (2 : ℝ) ≤ K)
      obtain ⟨E, hE, hyE⟩ := hcov _ hlt h5
      have := norm_exclude x hη0 ((hedge E hE).2.2 x (Set.mem_iInter₂.1 hxe E hE)) k
      linarith
    · obtain ⟨hη0, hcov⟩ := norm_far_cover (a := ϑ⁻¹) (C₀ := C₀) (K := K) hNn2
      obtain ⟨E, hE, hyE⟩ := hcov _ h5 hlam
      have := norm_exclude x hη0 ((hfar E hE).2 x (Set.mem_iInter₂.1 hxf E hE)) k
      linarith

end Rigidity
