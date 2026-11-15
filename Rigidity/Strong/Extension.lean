import Rigidity.Rigidity.Reduction
import Rigidity.Strong.Lattice

/-!
# From the lattice to the domain (NP v1.1, §7.4: Lemma 7.5 and Theorem 2.6 (i), (ii))

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! The proofs follow NP v1.1, §7.4. Where the original paper (Erdős–Yau–Yin, arXiv:1007.4652) has
a counterpart, it is cited as [EYY, …].

* Lemma 7.5: for `z = E + iη ∈ D_K` the lattice point is
  `w = ⌊E N⁴⌋ N⁻⁴ + i (10 - ⌊(10 - η) N⁴⌋ N⁻⁴)`. It lies in `𝕃 ∩ 𝐃^near`, and
  `0 ≤ E - Re w < N⁻⁴`, `0 ≤ Im w - η < N⁻⁴`. The three Lipschitz bounds come from Lemma 3.5 (c),
  and the bound for `Im m_sc` from Lemma 3.1 (f), at `η₀ = N⁻¹`, which is a lower bound for
  `Im z` and `Im w` since `K ≥ 1`.
* Theorem 2.6 (i), (ii) on `Ξ_K^{(1)}`: the point `w` of Lemma 7.5 lies in `𝕃 ∩ 𝐃^near`, so the
  bounds (b), (c) of Proposition 7.2 hold at `w`, and the Lipschitz bounds carry them to `z`.
  The final comparison uses `N ≥ 400` (which gives `2 N^{-3/2} ≤ 1/(10 N)`) and `K ≥ 3`.
  The complement of `Ξ_K^{(1)}` is the union of the complements of `𝒢²(z)` over
  `z ∈ 𝕃 ∩ 𝐃^near`, and `|𝕃| ≤ N¹⁰` (Definition 5.1). -/

/-! ### 1. Lemma 7.5 -/

/-- The grid point below and to the left of `z`: for `|Re z| ≤ 5` and `Im z ≤ 10` there is
`w ∈ N⁻⁴ ℤ + i (10 - N⁻⁴ ℤ_{≥0})` with `|Re w| ≤ 5`, `Im w ≤ 10`, `0 ≤ Re z - Re w < N⁻⁴`
and `0 ≤ Im w - Im z < N⁻⁴`. -/
private lemma extension_point {N : ℕ} (hN : 0 < N) {z : ℂ} (hre : |z.re| ≤ 5) (him : z.im ≤ 10) :
    ∃ w : ℂ, w ∈ gridPts N ∧ |w.re| ≤ 5 ∧ w.im ≤ 10 ∧ 0 ≤ z.re - w.re ∧
      z.re - w.re < 1 / (N : ℝ) ^ 4 ∧ 0 ≤ w.im - z.im ∧ w.im - z.im < 1 / (N : ℝ) ^ 4 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  have h10 : 0 ≤ (10 - z.im) * (N : ℝ) ^ 4 := mul_nonneg (by linarith) hP.le
  have hm1 := Int.floor_le (z.re * (N : ℝ) ^ 4)
  have hm2 := Int.lt_floor_add_one (z.re * (N : ℝ) ^ 4)
  have hk1 := Nat.floor_le h10
  have hk2 := Nat.lt_floor_add_one ((10 - z.im) * (N : ℝ) ^ 4)
  have hm3 : ((-5 * (N : ℤ) ^ 4 : ℤ) : ℝ) ≤ ⌊z.re * (N : ℝ) ^ 4⌋ := by
    have : (-5 * (N : ℤ) ^ 4 : ℤ) ≤ ⌊z.re * (N : ℝ) ^ 4⌋ := by
      rw [Int.le_floor]
      push_cast
      nlinarith [(abs_le.1 hre).1]
    exact_mod_cast this
  push_cast at hm3
  refine ⟨⟨⌊z.re * (N : ℝ) ^ 4⌋ / (N : ℝ) ^ 4, 10 - (⌊(10 - z.im) * (N : ℝ) ^ 4⌋₊ : ℝ) /
    (N : ℝ) ^ 4⟩, ⟨_, _, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hP]
      linarith
    · rw [div_le_iff₀ hP]
      nlinarith [(abs_le.1 hre).2]
  · simp only
    have : 0 ≤ (⌊(10 - z.im) * (N : ℝ) ^ 4⌋₊ : ℝ) / (N : ℝ) ^ 4 := by positivity
    linarith
  · simp only
    rw [sub_nonneg, div_le_iff₀ hP]
    exact hm1
  · simp only
    have : z.re - ⌊z.re * (N : ℝ) ^ 4⌋ / (N : ℝ) ^ 4 =
        (z.re * (N : ℝ) ^ 4 - ⌊z.re * (N : ℝ) ^ 4⌋) / (N : ℝ) ^ 4 := by field_simp
    rw [this]
    exact div_lt_div_of_pos_right (by linarith) hP
  · simp only
    have : 10 - (⌊(10 - z.im) * (N : ℝ) ^ 4⌋₊ : ℝ) / (N : ℝ) ^ 4 - z.im =
        ((10 - z.im) * (N : ℝ) ^ 4 - ⌊(10 - z.im) * (N : ℝ) ^ 4⌋₊) / (N : ℝ) ^ 4 := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (by linarith) hP.le
  · simp only
    have : 10 - (⌊(10 - z.im) * (N : ℝ) ^ 4⌋₊ : ℝ) / (N : ℝ) ^ 4 - z.im =
        ((10 - z.im) * (N : ℝ) ^ 4 - ⌊(10 - z.im) * (N : ℝ) ^ 4⌋₊) / (N : ℝ) ^ 4 := by
      field_simp
      ring
    rw [this]
    exact div_lt_div_of_pos_right (by linarith) hP

/-- Lemma 7.5: Lipschitz extension from the lattice to `D_K`. -/
theorem lattice_extension {a C₀ K : ℝ} (ha : 1 ≤ a) (hK : 1 ≤ K) {N : ℕ} (hN : 13 ≤ N) {z : ℂ}
    (hz : z ∈ DK a N K) :
    ∃ w ∈ lattice a C₀ K N ∩ Dnear a K N, ‖z - w‖ ≤ 2 / (N : ℝ) ^ 4 ∧ z.im ≤ w.im ∧
      ∀ {A : Matrix (Fin N) (Fin N) 𝕜}, A.IsHermitian →
        |LamM A z - LamM A w| + |LamDM A z - LamDM A w| + |LamOM A z - LamOM A w| ≤
            8 / (N : ℝ) ^ 2 ∧
          |(msc z).im - (msc w).im| ≤ 4 / (N : ℝ) ^ 3 ∧
          |1 / (N * z.im) - 1 / (N * w.im)| ≤ 1 / (N : ℝ) ^ 3 := by
  have hNr : (13 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hP : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  obtain ⟨hre5, hη, hη10⟩ := hz
  obtain ⟨w, hwg, hw5, hw10, hre0, hre1, him0, him1⟩ :=
    extension_point (N := N) (by omega) hre5 hη10
  have hK0 : 0 ≤ K := by linarith
  have hC1 : 1 ≤ ledgerC1 a := by unfold ledgerC1; linarith
  have hKC : 1 ≤ K ^ ledgerC1 a := Real.one_le_rpow hK (by linarith)
  have hη1 : 1 / (N : ℝ) ≤ z.im :=
    le_trans (div_le_div_of_nonneg_right hKC hNpos.le) hη
  have hηw : z.im ≤ w.im := by linarith
  have hηw1 : 1 / (N : ℝ) ≤ w.im := le_trans hη1 hηw
  have hD : w ∈ Dnear a K N := by
    refine ⟨hw5, le_trans ?_ hηw, hw10⟩
    refine le_trans (div_le_div_of_nonneg_right ?_ hNpos.le) hη
    exact Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have hdist : ‖z - w‖ ≤ 2 / (N : ℝ) ^ 4 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, abs_of_nonneg hre0, abs_of_nonpos (by linarith)]
    have : 2 / (N : ℝ) ^ 4 = 1 / (N : ℝ) ^ 4 + 1 / (N : ℝ) ^ 4 := by ring
    rw [this]
    linarith
  refine ⟨w, ⟨⟨Or.inl hD, hwg⟩, hD⟩, hdist, hηw, fun {A} hA => ?_⟩
  have hη0 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  obtain ⟨hL1, hL2, hL3⟩ := abs_LamM_sub_le hA hη0 hη1 hηw1
  have hinv : (1 / (N : ℝ))⁻¹ = N := by rw [one_div, inv_inv]
  rw [hinv] at hL1 hL2 hL3
  have hconst : 3 * (((N : ℝ) ^ 2 + N + 1) * (2 / (N : ℝ) ^ 4)) ≤ 8 / (N : ℝ) ^ 2 := by
    have : 3 * (((N : ℝ) ^ 2 + N + 1) * (2 / (N : ℝ) ^ 4)) =
        6 * ((N : ℝ) ^ 2 + N + 1) / (N : ℝ) ^ 4 := by ring
    rw [this, div_le_div_iff₀ hP (by positivity)]
    nlinarith [sq_nonneg (N : ℝ), mul_pos hNpos hNpos]
  have hmul : ((N : ℝ) ^ 2 + N + 1) * ‖z - w‖ ≤ ((N : ℝ) ^ 2 + N + 1) * (2 / (N : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left hdist (by positivity)
  refine ⟨by linarith, ?_, ?_⟩
  · have hm := norm_msc_sub_le hη0 hη1 hηw1
    have hc : (1 / (N : ℝ) + 1) / (1 / (N : ℝ)) = 1 + N := by
      field_simp
    rw [hc] at hm
    have h1 : |(msc z).im - (msc w).im| ≤ ‖msc z - msc w‖ := by
      have := Complex.abs_im_le_norm (msc z - msc w)
      rwa [Complex.sub_im] at this
    refine h1.trans (hm.trans ?_)
    calc (1 + (N : ℝ)) * ‖z - w‖ ≤ (1 + N) * (2 / (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left hdist (by positivity)
      _ ≤ 4 / (N : ℝ) ^ 3 := by
          have : (1 + (N : ℝ)) * (2 / (N : ℝ) ^ 4) = 2 * (1 + N) / (N : ℝ) ^ 4 := by ring
          rw [this, div_le_div_iff₀ hP (by positivity)]
          nlinarith [pow_pos hNpos 3]
  · have hNη : 0 < (N : ℝ) * z.im := mul_pos hNpos (lt_of_lt_of_le hη0 hη1)
    have hNηw : 0 < (N : ℝ) * w.im := mul_pos hNpos (lt_of_lt_of_le hη0 hηw1)
    have hle : 1 / ((N : ℝ) * w.im) ≤ 1 / ((N : ℝ) * z.im) :=
      one_div_le_one_div_of_le hNη (mul_le_mul_of_nonneg_left hηw hNpos.le)
    rw [abs_of_nonneg (by linarith)]
    have hz0 : z.im ≠ 0 := (lt_of_lt_of_le hη0 hη1).ne'
    have hw0 : w.im ≠ 0 := (lt_of_lt_of_le hη0 hηw1).ne'
    have heq : 1 / ((N : ℝ) * z.im) - 1 / ((N : ℝ) * w.im) =
        (w.im - z.im) / ((N : ℝ) * z.im * w.im) := by
      field_simp
    rw [heq, div_le_iff₀ (mul_pos hNη (lt_of_lt_of_le hη0 hηw1))]
    have h1 : (1 : ℝ) / N ≤ (N : ℝ) * z.im * w.im := by
      have : (N : ℝ) * (1 / N) * (1 / N) = 1 / N := by field_simp
      calc (1 : ℝ) / N = (N : ℝ) * (1 / N) * (1 / N) := this.symm
        _ ≤ (N : ℝ) * z.im * w.im := by gcongr
    calc w.im - z.im ≤ 1 / (N : ℝ) ^ 4 := him1.le
      _ = 1 / (N : ℝ) ^ 3 * (1 / N) := by field_simp
      _ ≤ 1 / (N : ℝ) ^ 3 * ((N : ℝ) * z.im * w.im) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### 2. The comparison at the end of §7 -/

/-- The numerical step of Theorem 2.6 (i), (ii): bounds `Lw ≤ T/(Nη')` and
`Dw ≤ T K (√(μw/(Nη')) + 1/(Nη'))` at a point `w` with `η ≤ η'`, `μw ≤ μz + 4N⁻³`, and Lipschitz
differences at most `8N⁻²`, give the bounds at `z` with the extra factor `K`, for `N ≥ 400`,
`K ≥ 3`, `T ≥ 1`. -/
private lemma extension_compare {Nr K T η η' μz μw Lz Lw Dz Dw : ℝ}
    (hN : 400 ≤ Nr) (hK : 3 ≤ K) (hT : 1 ≤ T) (hη1 : 1 / Nr ≤ η) (hηη : η ≤ η')
    (hη10 : η ≤ 10) (hμz : 0 ≤ μz) (hμw : 0 ≤ μw) (hμ : μw ≤ μz + 4 / Nr ^ 3)
    (hLz : |Lz - Lw| ≤ 8 / Nr ^ 2) (hDz : |Dz - Dw| ≤ 8 / Nr ^ 2)
    (hb : Lw ≤ T / (Nr * η')) (hc : Dw ≤ T * K * (Real.sqrt (μw / (Nr * η')) + 1 / (Nr * η'))) :
    Lz ≤ T * K / (Nr * η) ∧
      Dz ≤ T * K * K * (Real.sqrt (μz / (Nr * η)) + 1 / (Nr * η)) := by
  have hNpos : 0 < Nr := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη1
  have hη'0 : 0 < η' := lt_of_lt_of_le hη0 hηη
  have hu : 0 < Nr * η := mul_pos hNpos hη0
  have hu' : 0 < Nr * η' := mul_pos hNpos hη'0
  have hu1 : 1 ≤ Nr * η := by
    have := mul_le_mul_of_nonneg_left hη1 hNpos.le
    rwa [mul_one_div_cancel hNpos.ne'] at this
  have hut : Nr * η ≤ Nr * η' := mul_le_mul_of_nonneg_left hηη hNpos.le
  -- `t = 1 / (N η)`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (Nr * η) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht' : 1 / (Nr * η') ≤ t := by rw [ht]; exact one_div_le_one_div_of_le hu hut
  have hsmall : 8 / Nr ^ 2 ≤ t / 5 := by
    rw [ht, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 0 ≤ Nr / 5 - 8 * η := by linarith
    nlinarith [mul_nonneg hNpos.le h1]
  have hTK : T * K ≥ T + 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hT) (sub_nonneg.2 hK)]
  have hT0 : 0 ≤ T := by linarith
  have hS0 : 0 ≤ T * K := by positivity
  have hdiv : ∀ y : ℝ, y / (Nr * η) = y * t := fun y => by rw [ht, div_eq_mul_one_div]
  have hdiv' : T / (Nr * η') ≤ T * t := by
    rw [← hdiv]
    exact div_le_div_of_nonneg_left hT0 hu hut
  rw [← ht]
  refine ⟨?_, ?_⟩
  · rw [hdiv]
    have h1 := (abs_le.1 hLz).2
    nlinarith [mul_le_mul_of_nonneg_right hTK ht0.le]
  · -- the square root
    have hα : 0 ≤ μz / (Nr * η) := by positivity
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (μz / (Nr * η)) := ⟨_, rfl⟩
    rw [← hσ]
    have hσ0 : 0 ≤ σ := by rw [hσ]; exact Real.sqrt_nonneg _
    have hσ2 : σ ^ 2 = μz / (Nr * η) := by rw [hσ]; exact Real.sq_sqrt hα
    have hc0 : 0 ≤ 1 / (10 * Nr) := by positivity
    have hβ : 4 / Nr ^ 3 ≤ (1 / (10 * Nr)) ^ 2 := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (10 * Nr) ^ 2 = 100 * Nr ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg Nr, mul_pos hNpos hNpos]
    have hsq : Real.sqrt (μw / (Nr * η')) ≤ σ + 1 / (10 * Nr) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have h1 : μw / (Nr * η') ≤ μw / (Nr * η) := div_le_div_of_nonneg_left hμw hu hut
      have h2 : μw / (Nr * η) ≤ (μz + 4 / Nr ^ 3) / (Nr * η) :=
        div_le_div_of_nonneg_right hμ hu.le
      have h3 : (μz + 4 / Nr ^ 3) / (Nr * η) = μz / (Nr * η) + 4 / Nr ^ 3 / (Nr * η) := by
        rw [add_div]
      have h4 : 4 / Nr ^ 3 / (Nr * η) ≤ 4 / Nr ^ 3 := by
        rw [div_le_iff₀ hu]
        have : 0 ≤ 4 / Nr ^ 3 := by positivity
        nlinarith
      nlinarith [mul_nonneg hσ0 hc0]
    have hc1 : 1 / (10 * Nr) ≤ t := by
      rw [ht]
      exact one_div_le_one_div_of_le hu (by nlinarith)
    have hsum : Real.sqrt (μw / (Nr * η')) + 1 / (Nr * η') ≤ σ + 2 * t := by linarith
    have hS1 : 1 ≤ T * K := by linarith
    have h1 : Dz ≤ Dw + t / 5 := by linarith [(abs_le.1 hDz).2]
    have h2 : Dw ≤ T * K * (σ + 2 * t) := hc.trans (mul_le_mul_of_nonneg_left hsum hS0)
    have h3 : T * K * K * (σ + t) ≥ 3 * (T * K) * (σ + t) := by
      have : 0 ≤ T * K * (σ + t) := by positivity
      have e : T * K * K * (σ + t) - 3 * (T * K) * (σ + t) = (K - 3) * (T * K * (σ + t)) := by
        ring
      have := mul_nonneg (sub_nonneg.2 hK) this
      linarith
    linarith [mul_nonneg hS0 hσ0, mul_le_mul_of_nonneg_right hS1 ht0.le]

/-- `Ξ_K^{(1)} = ⋂_{z ∈ 𝕃 ∩ 𝐃^near} 𝒢²(z)` (end of §7). -/
def strongXi1 {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) : Set (Pair N → 𝕜) :=
  ⋂ z ∈ lattice a C₀ K N ∩ Dnear a K N, strongG2 M a C₀ K z

/-- Theorem 2.6 (i), (ii) on `Ξ_K^{(1)}` (end of §7): `Ξ_K^{(1)}` is closed,
`ℙ((Ξ_K^{(1)})ᶜ) ≤ N^{20} e^{-p₁}`, and on it the bounds hold for all `z ∈ D_K` with the exponents
`b + 5`, `b + 6`. -/
theorem localLaw_i_ii {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
        IsClosed (strongXi1 M ϑ⁻¹ C₀ K) ∧
        M.prodLaw (strongXi1 M ϑ⁻¹ C₀ K)ᶜ ≤
          ENNReal.ofReal ((N : ℝ) ^ 20 * Real.exp (-(levelP1 K : ℝ))) ∧
        ∀ x ∈ strongXi1 M ϑ⁻¹ C₀ K, ∀ z ∈ DK ϑ⁻¹ N K,
          Lam x z ≤ K ^ (ledgerB ϑ⁻¹ + 5) / (N * z.im) ∧
          LamD x z + LamO x z ≤
            K ^ (ledgerB ϑ⁻¹ + 6) * (Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im)) := by
  obtain ⟨N₁, h1⟩ := strong_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := lattice_card (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₃, h3⟩ := standing_ineq hϑ hϑ1 hC₀ 3
  refine ⟨max (max (max N₁ N₂) N₃) 400, ?_⟩
  intro N hN M hM K hK1 hK2
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN400 : (400 : ℝ) ≤ N := by exact_mod_cast (by omega : 400 ≤ N)
  obtain ⟨⟨hK3, h13, -, -⟩, -, -, -⟩ := h3 N hN3 K hK1 hK2
  have ha : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hKpos : 0 < K := by linarith
  obtain ⟨hfin, hcard, -⟩ := h2 N hN2 K hK1 hK2
  have hfinS : (lattice ϑ⁻¹ C₀ K N ∩ Dnear ϑ⁻¹ K N).Finite := hfin.subset Set.inter_subset_left
  refine ⟨isClosed_biInter fun w hw => (h1 N hN1 M hM K hK1 hK2 w hw).1, ?_, ?_⟩
  · have hcompl : (strongXi1 M ϑ⁻¹ C₀ K)ᶜ =
        ⋃ w ∈ hfinS.toFinset, (strongG2 M ϑ⁻¹ C₀ K w)ᶜ := by
      ext x
      simp [strongXi1]
    have hb : 0 ≤ (N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)) := by positivity
    have hcard' : (hfinS.toFinset.card : ℝ) ≤ (N : ℝ) ^ 10 := by
      rw [← Set.ncard_eq_toFinset_card _ hfinS]
      exact le_trans (Nat.cast_le.2 (Set.ncard_le_ncard Set.inter_subset_left hfin)) hcard
    calc M.prodLaw (strongXi1 M ϑ⁻¹ C₀ K)ᶜ
        = M.prodLaw (⋃ w ∈ hfinS.toFinset, (strongG2 M ϑ⁻¹ C₀ K w)ᶜ) := by rw [hcompl]
      _ ≤ ∑ w ∈ hfinS.toFinset, M.prodLaw (strongG2 M ϑ⁻¹ C₀ K w)ᶜ :=
          measure_biUnion_finset_le _ _
      _ ≤ hfinS.toFinset.card • ENNReal.ofReal ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ))) :=
          Finset.sum_le_card_nsmul _ _ _ fun w hw =>
            (h1 N hN1 M hM K hK1 hK2 w (hfinS.mem_toFinset.1 hw)).2.1
      _ = ENNReal.ofReal ((hfinS.toFinset.card : ℝ) *
            ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)))) := by
          rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ 20 * Real.exp (-(levelP1 K : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          calc (hfinS.toFinset.card : ℝ) * ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)))
              ≤ (N : ℝ) ^ 10 * ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ))) :=
                mul_le_mul_of_nonneg_right hcard' hb
            _ = (N : ℝ) ^ 20 * Real.exp (-(levelP1 K : ℝ)) := by ring
  · intro x hx z hz
    obtain ⟨w, hw, -, hzw, hlip⟩ := lattice_extension (𝕜 := 𝕜) (C₀ := C₀) ha (by linarith) h13 hz
    obtain ⟨-, hb, hc⟩ := (h1 N hN1 M hM K hK1 hK2 w hw).2.2 x (Set.mem_iInter₂.1 hx w hw)
    obtain ⟨hL, hm, -⟩ := hlip (toMatrix_isHermitian x)
    obtain ⟨hre, hη, hη10⟩ := hz
    have hNpos : (0 : ℝ) < N := by linarith
    have hC1 : 0 ≤ ledgerC1 ϑ⁻¹ := by unfold ledgerC1; linarith
    have hη1 : 1 / (N : ℝ) ≤ z.im :=
      le_trans (div_le_div_of_nonneg_right (Real.one_le_rpow (by linarith) hC1) hNpos.le) hη
    have hη0 : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
    have hLzw : |Lam x z - Lam x w| + |LamD x z - LamD x w| + |LamO x z - LamO x w| ≤
        8 / (N : ℝ) ^ 2 := hL
    have hB : 0 ≤ ledgerB ϑ⁻¹ + 4 := by unfold ledgerB; linarith
    have e5 : K ^ (ledgerB ϑ⁻¹ + 5) = K ^ (ledgerB ϑ⁻¹ + 4) * K := by
      rw [show ledgerB ϑ⁻¹ + 5 = (ledgerB ϑ⁻¹ + 4) + 1 by ring, Real.rpow_add hKpos,
        Real.rpow_one]
    have e6 : K ^ (ledgerB ϑ⁻¹ + 6) = K ^ (ledgerB ϑ⁻¹ + 4) * K * K := by
      rw [show ledgerB ϑ⁻¹ + 6 = (ledgerB ϑ⁻¹ + 5) + 1 by ring, Real.rpow_add hKpos,
        Real.rpow_one, e5]
    rw [e5] at hc ⊢
    rw [e6]
    refine extension_compare hN400 hK3 (Real.one_le_rpow (by linarith) hB) hη1 hzw hη10
      (msc_im_pos hη0).le (msc_im_pos (lt_of_lt_of_le hη0 hzw)).le ?_ ?_ ?_ hb hc
    · have := (abs_le.1 hm).1
      linarith
    · have := abs_nonneg (LamD x z - LamD x w)
      have := abs_nonneg (LamO x z - LamO x w)
      linarith
    · have h0 := abs_nonneg (Lam x z - Lam x w)
      have : LamD x z + LamO x z - (LamD x w + LamO x w) =
          (LamD x z - LamD x w) + (LamO x z - LamO x w) := by ring
      rw [this]
      linarith [abs_add_le (LamD x z - LamD x w) (LamO x z - LamO x w)]

end Rigidity
