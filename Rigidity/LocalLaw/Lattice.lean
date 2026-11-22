module

public import Rigidity.Ensemble.Basic
public import Rigidity.LocalLaw.GoodEvent
public import Rigidity.LocalLaw.Ledger
public import Rigidity.LocalLaw.Levels

@[expose] public section

/-!
# The lattice of spectral parameters, the columns, and the a priori event

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file defines the spectral domains `𝐃^near`, `𝐃^far`, the grid `N⁻⁴ ℤ + i (10 - N⁻⁴ ℤ_{≥0})`,
the lattice `𝕃`, the column `col(z)` above a lattice point, the column event `𝒢_col(z)`
(Definition 5.1), the control quantity `Ψ` of (5.1) and the a priori event `Ξ_p(z)` of (5.7) and
Theorem 6.1.  It proves:

* `latticeCol_eq`: the column structure of Definition 5.1.  For `z = E + iη ∈ 𝕃` with
  `η = 10 - k N⁻⁴`, the column is `{E + i (10 - j N⁻⁴) : 0 ≤ j ≤ k}`, it has `k + 1` points, at
  most `10 N⁴` of them when `η > 0`, and it lies in each of the domains `𝐃^near`, `𝐃^far`
  that contains `z`;
* `lattice_card` (Definition 5.1): for `N` large and `(log N)³ ≤ K ≤ N^{c₀}`, with `c₀` of the
  exponent ledger (A.1), the lattice is finite with `|𝕃| ≤ N^{10}`, and under `M.Assumptions`
  every column event satisfies `ℙ(𝒢_col(z)ᶜ) ≤ 460 ϑ⁻¹ N⁸ e^{-K²}`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory


/-- `𝐃^near` of Definition 5.1. -/
def Dnear (a K : ℝ) (N : ℕ) : Set ℂ :=
  {z | |z.re| ≤ 5 ∧ K ^ (ledgerC1 a - 1) / N ≤ z.im ∧ z.im ≤ 10}

/-- `𝐃^far` of Definition 5.1. -/
def Dfar (a C₀ K : ℝ) (N : ℕ) : Set ℂ :=
  {z | 4 ≤ |z.re| ∧ |z.re| ≤ levelEmax a C₀ K N + 1 ∧ 1 / (2 * Real.sqrt N) ≤ z.im ∧ z.im ≤ 10}

/-- The grid `N^{-4} ℤ + i (10 - N^{-4} ℤ_{≥0})`. -/
def gridPts (N : ℕ) : Set ℂ :=
  {z | ∃ m : ℤ, ∃ k : ℕ, z = ⟨m / (N : ℝ) ^ 4, 10 - k / (N : ℝ) ^ 4⟩}

/-- The lattice `𝕃` of Definition 5.1. -/
def lattice (a C₀ K : ℝ) (N : ℕ) : Set ℂ := (Dnear a K N ∪ Dfar a C₀ K N) ∩ gridPts N

/-- The column above a lattice point (Definition 5.1). -/
def latticeCol (a C₀ K : ℝ) (N : ℕ) (z : ℂ) : Set ℂ :=
  {w ∈ lattice a C₀ K N | w.re = z.re ∧ z.im ≤ w.im}

/-- `𝒢_col(z)` of Definition 5.1, at level `K_w = K²`. -/
def goodCol {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  ⋂ w ∈ latticeCol a C₀ K N z, goodEvent M a (K ^ 2) w

/-- `Ψ = √((Im m_sc + Λ)/(Nη)) + 1/(Nη)` of (5.1). -/
noncomputable def ctrlPsi {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  Real.sqrt (((msc z).im + Lam x z) / (N * z.im)) + 1 / (N * z.im)

/-- The a priori event `Ξ_p(z) = {Λ_d ≤ |m_sc|/2, Λ_o ≤ |m_sc|/(16p)}` of (5.7) and
Theorem 6.1. -/
def aprioriEvent (N : ℕ) (p : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  {x | LamD x z ≤ ‖msc z‖ / 2 ∧ LamO x z ≤ ‖msc z‖ / (16 * p)}

/-! ### 1. The column structure -/

/-- A point of `𝐃^near` stays in `𝐃^near` when its imaginary part is raised up to `10`. -/
private lemma lattice_near_of_le {a K : ℝ} {N : ℕ} {z w : ℂ} (hz : z ∈ Dnear a K N)
    (hre : w.re = z.re) (him : z.im ≤ w.im) (h10 : w.im ≤ 10) : w ∈ Dnear a K N := by
  obtain ⟨h1, h2, -⟩ := hz
  exact ⟨by rw [hre]; exact h1, h2.trans him, h10⟩

/-- A point of `𝐃^far` stays in `𝐃^far` when its imaginary part is raised up to `10`. -/
private lemma lattice_far_of_le {a C₀ K : ℝ} {N : ℕ} {z w : ℂ} (hz : z ∈ Dfar a C₀ K N)
    (hre : w.re = z.re) (him : z.im ≤ w.im) (h10 : w.im ≤ 10) : w ∈ Dfar a C₀ K N := by
  obtain ⟨h1, h2, h3, -⟩ := hz
  exact ⟨by rw [hre]; exact h1, by rw [hre]; exact h2, h3.trans him, h10⟩

/-- The column structure of Definition 5.1.  For `z = E + iη` in the lattice with
`η = 10 - k N⁻⁴`, the column of `z` is `{E + i (10 - j N⁻⁴) : 0 ≤ j ≤ k}`; it is finite with
`k + 1` points, at most `10 N⁴` of them if `η > 0`, and it lies in each of the domains `𝐃^near`,
`𝐃^far` that contains `z`. -/
theorem latticeCol_eq {a C₀ K : ℝ} {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : z ∈ lattice a C₀ K N)
    {k : ℕ} (hk : z.im = 10 - k / (N : ℝ) ^ 4) :
    latticeCol a C₀ K N z =
        (fun j : ℕ => (⟨z.re, 10 - j / (N : ℝ) ^ 4⟩ : ℂ)) '' Set.Iic k ∧
      (latticeCol a C₀ K N z).Finite ∧ (latticeCol a C₀ K N z).ncard = k + 1 ∧
      (0 < z.im → k + 1 ≤ 10 * N ^ 4) ∧
      (z ∈ Dnear a K N → latticeCol a C₀ K N z ⊆ Dnear a K N) ∧
      (z ∈ Dfar a C₀ K N → latticeCol a C₀ K N z ⊆ Dfar a C₀ K N) := by
  have hP : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  set P : ℝ := (N : ℝ) ^ 4 with hPdef
  set f : ℕ → ℂ := fun j => ⟨z.re, 10 - j / P⟩ with hf
  have hfinj : Function.Injective f := by
    intro i j hij
    have h := congrArg Complex.im hij
    simp only [hf] at h
    have h2 : (i : ℝ) / P = j / P := by linarith
    have h3 : (i : ℝ) = j := by
      rwa [div_left_inj' hP.ne'] at h2
    exact_mod_cast h3
  obtain ⟨hz1, m, k', hzg⟩ : z ∈ (Dnear a K N ∪ Dfar a C₀ K N) ∩ gridPts N := hz
  have hzre : z.re = m / P := congrArg Complex.re hzg
  have hfk : ∀ j : ℕ, j ≤ k → z.im ≤ (f j).im ∧ (f j).im ≤ 10 := by
    intro j hj
    have h1 : (j : ℝ) / P ≤ k / P :=
      div_le_div_of_nonneg_right (by exact_mod_cast hj) hP.le
    have h2 : (0 : ℝ) ≤ j / P := by positivity
    simp only [hf]
    constructor <;> linarith
  have hcol : latticeCol a C₀ K N z = f '' Set.Iic k := by
    ext w
    constructor
    · rintro ⟨⟨-, m', j, hwg⟩, hre, him⟩
      have hwim : w.im = 10 - j / P := congrArg Complex.im hwg
      refine ⟨j, ?_, ?_⟩
      · have h1 : (j : ℝ) / P ≤ k / P := by linarith
        have h2 : (j : ℝ) ≤ k := (div_le_div_iff_of_pos_right hP).1 h1
        exact_mod_cast h2
      · apply Complex.ext
        · simp [hf, hre]
        · simp [hf, hwim]
    · rintro ⟨j, hj, rfl⟩
      have hj' : j ≤ k := hj
      obtain ⟨hlo, hhi⟩ := hfk j hj'
      refine ⟨⟨?_, m, j, ?_⟩, rfl, hlo⟩
      · rcases hz1 with h | h
        · exact Or.inl (lattice_near_of_le h rfl hlo hhi)
        · exact Or.inr (lattice_far_of_le h rfl hlo hhi)
      · apply Complex.ext
        · simp [hf, hzre, hPdef]
        · simp [hf, hPdef]
  have hsub : ∀ S : Set ℂ, (∀ w, w.re = z.re → z.im ≤ w.im → w.im ≤ 10 → w ∈ S) →
      latticeCol a C₀ K N z ⊆ S := by
    intro S hS w hw
    rw [hcol] at hw
    obtain ⟨j, hj, rfl⟩ := hw
    obtain ⟨hlo, hhi⟩ := hfk j hj
    exact hS _ rfl hlo hhi
  refine ⟨hcol, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcol]; exact (Set.finite_Iic k).image f
  · rw [hcol, Set.ncard_image_of_injective _ hfinj, Set.ncard_Iic, Nat.card_Iic]
  · intro hpos
    have h1 : (k : ℝ) / P < 10 := by linarith
    have h2 : (k : ℝ) < 10 * (N : ℝ) ^ 4 := by rwa [div_lt_iff₀ hP] at h1
    have h3 : k < 10 * N ^ 4 := by exact_mod_cast h2
    omega
  · exact fun h => hsub _ fun w hre hlo hhi => lattice_near_of_le h hre hlo hhi
  · exact fun h => hsub _ fun w hre hlo hhi => lattice_far_of_le h hre hlo hhi

/-! ### 2. The cardinality of the lattice and the column event -/

/-- Lattice points have positive imaginary part when `K > 0`. -/
private lemma lattice_im_pos {a C₀ K : ℝ} {N : ℕ} (hN : 0 < N) (hK : 0 < K) {z : ℂ}
    (hz : z ∈ lattice a C₀ K N) : 0 < z.im := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases hz.1 with h | h
  · exact lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hK _) hNr) h.2.1
  · exact lt_of_lt_of_le (by have := Real.sqrt_pos.2 hNr; positivity) h.2.2.1

/-- A lattice point lies on the grid, in the box `|Re| ≤ 5 E_max`, `0 < Im ≤ 10`; counting the
grid points of the box gives `|𝕃| ≤ 110 E_max N⁸` when `E_max ≥ 1`. -/
private lemma lattice_ncard_le {a C₀ K : ℝ} {N : ℕ} (hN : 0 < N) (hK : 0 < K)
    (hE : 1 ≤ levelEmax a C₀ K N) :
    (lattice a C₀ K N).Finite ∧
      ((lattice a C₀ K N).ncard : ℝ) ≤ 110 * levelEmax a C₀ K N * (N : ℝ) ^ 8 := by
  set E := levelEmax a C₀ K N with hEdef
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (N : ℝ) ^ 4 := by positivity
  set P : ℝ := (N : ℝ) ^ 4 with hPdef
  have hP1 : 1 ≤ P := one_le_pow₀ hNr
  have hEP : 1 ≤ E * P := one_le_mul_of_one_le_of_one_le hE hP1
  have hB : 0 ≤ 5 * E * P := by nlinarith
  set B : ℤ := ⌊5 * E * P⌋ with hBdef
  have hB0 : 0 ≤ B := Int.floor_nonneg.2 hB
  set S : Finset (ℤ × ℕ) := Finset.Icc (-B) B ×ˢ Finset.range (10 * N ^ 4) with hS
  set g : ℤ × ℕ → ℂ := fun p => ⟨p.1 / P, 10 - p.2 / P⟩ with hg
  have hsub : lattice a C₀ K N ⊆ g '' (S : Set (ℤ × ℕ)) := by
    intro z hz
    have hpos := lattice_im_pos hN hK hz
    obtain ⟨hz1, m, k, rfl⟩ : z ∈ (Dnear a K N ∪ Dfar a C₀ K N) ∩ gridPts N := hz
    have hre : |(m : ℝ) / P| ≤ 5 * E := by
      rcases hz1 with h | h
      · have h5 : |(m : ℝ) / P| ≤ 5 := h.1
        nlinarith
      · have h5 : |(m : ℝ) / P| ≤ E + 1 := h.2.1
        nlinarith
    have hm : |(m : ℝ)| ≤ 5 * E * P := by
      rw [abs_div, abs_of_pos hP, div_le_iff₀ hP] at hre
      exact hre
    obtain ⟨hm1, hm2⟩ := abs_le.1 hm
    have hk : (k : ℝ) < 10 * (N : ℝ) ^ 4 := by
      have h1 : 0 < 10 - (k : ℝ) / P := hpos
      have h2 : (k : ℝ) / P < 10 := by linarith
      rwa [div_lt_iff₀ hP] at h2
    refine ⟨(m, k), ?_, rfl⟩
    rw [Finset.mem_coe, hS, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨?_, Int.le_floor.2 hm2⟩, by exact_mod_cast hk⟩
    have h3 : -m ≤ B := Int.le_floor.2 (by push_cast; linarith)
    omega
  have hfin : (g '' (S : Set (ℤ × ℕ))).Finite := S.finite_toSet.image g
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : (lattice a C₀ K N).ncard ≤ S.card :=
    calc (lattice a C₀ K N).ncard ≤ (g '' (S : Set (ℤ × ℕ))).ncard :=
          Set.ncard_le_ncard hsub hfin
      _ ≤ (S : Set (ℤ × ℕ)).ncard := Set.ncard_image_le S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S
  have h2 : S.card = (B + 1 - -B).toNat * (10 * N ^ 4) := by
    rw [hS, Finset.card_product, Int.card_Icc, Finset.card_range]
  have h3 : (((B + 1 - -B).toNat : ℕ) : ℝ) = 2 * (B : ℝ) + 1 := by
    have h4 : (((B + 1 - -B).toNat : ℕ) : ℤ) = B + 1 - -B := Int.toNat_of_nonneg (by omega)
    have h5 := congrArg (Int.cast : ℤ → ℝ) h4
    push_cast at h5
    linarith
  have h6 : (B : ℝ) ≤ 5 * E * P := Int.floor_le _
  have h7 : ((lattice a C₀ K N).ncard : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h1
  rw [h2] at h7
  push_cast at h7
  rw [h3] at h7
  calc ((lattice a C₀ K N).ncard : ℝ) ≤ (2 * (B : ℝ) + 1) * (10 * (N : ℝ) ^ 4) := h7
    _ ≤ (11 * (E * P)) * (10 * P) := by
        apply mul_le_mul _ (by rw [hPdef]) (by positivity) (by nlinarith)
        linarith
    _ = 110 * E * (N : ℝ) ^ 8 := by rw [hPdef]; ring

/-- The union bound over a column: if every good event of the column fails with probability at
most `b`, then `𝒢_col(z)` fails with probability at most `10 N⁴ b`. -/
private lemma lattice_col_prob {N : ℕ} (M : Ensemble 𝕜 N) {a C₀ K : ℝ} {b : ℝ} (hN : 0 < N)
    (hK : 0 < K) (hb : 0 ≤ b) {z : ℂ} (hz : z ∈ lattice a C₀ K N)
    (hbound : ∀ w ∈ latticeCol a C₀ K N z,
      M.prodLaw (goodEvent M a (K ^ 2) w)ᶜ ≤ ENNReal.ofReal b) :
    M.prodLaw (goodCol M a C₀ K z)ᶜ ≤ ENNReal.ofReal (10 * (N : ℝ) ^ 4 * b) := by
  have hpos := lattice_im_pos hN hK hz
  have hz' : z ∈ (Dnear a K N ∪ Dfar a C₀ K N) ∩ gridPts N := hz
  obtain ⟨-, m, k, hzg⟩ := hz'
  obtain ⟨-, hfin, hcard, hle, -, -⟩ := latticeCol_eq hN hz (k := k) (congrArg Complex.im hzg)
  have hle' : (k : ℝ) + 1 ≤ 10 * (N : ℝ) ^ 4 := by exact_mod_cast hle hpos
  have hcompl : (goodCol M a C₀ K z)ᶜ = ⋃ w ∈ hfin.toFinset, (goodEvent M a (K ^ 2) w)ᶜ := by
    ext x
    simp [goodCol]
  have hcnt : (hfin.toFinset.card : ℝ) = k + 1 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, hcard]
    push_cast
    ring
  calc M.prodLaw (goodCol M a C₀ K z)ᶜ
      = M.prodLaw (⋃ w ∈ hfin.toFinset, (goodEvent M a (K ^ 2) w)ᶜ) := by rw [hcompl]
    _ ≤ ∑ w ∈ hfin.toFinset, M.prodLaw (goodEvent M a (K ^ 2) w)ᶜ := measure_biUnion_finset_le _ _
    _ ≤ hfin.toFinset.card • ENNReal.ofReal b :=
        Finset.sum_le_card_nsmul _ _ _ fun w hw => hbound w (hfin.mem_toFinset.1 hw)
    _ = ENNReal.ofReal ((hfin.toFinset.card : ℝ) * b) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (10 * (N : ℝ) ^ 4 * b) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hcnt]
        exact mul_le_mul_of_nonneg_right hle' hb

/-- Definition 5.1: `|𝕃| ≤ N^{10}` and the probability of `𝒢_col(z)^c`. -/
theorem lattice_card {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      (lattice ϑ⁻¹ C₀ K N).Finite ∧ ((lattice ϑ⁻¹ C₀ K N).ncard : ℝ) ≤ (N : ℝ) ^ 10 ∧
      ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ → ∀ z ∈ lattice ϑ⁻¹ C₀ K N,
        M.prodLaw (goodCol M ϑ⁻¹ C₀ K z)ᶜ ≤ ENNReal.ofReal (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2)) := by
  -- `δm` and `δp` enter only through `M.Assumptions`; the counting does not use them
  have _ : 0 < δm ∧ 0 < δp := ⟨hδm, hδp⟩
  obtain ⟨N₁, hN₁⟩ := standing_ineq hϑ hϑ1 hC₀ 1
  refine ⟨max N₁ 110, fun N hN K hK1 hK2 => ?_⟩
  obtain ⟨⟨hK1', hN13, -, hκ⟩, ⟨-, -, hE1, hE2⟩, -, hKN, -⟩ :=
    hN₁ N (le_trans (le_max_left _ _) hN) K hK1 hK2
  have hN110 : 110 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := by omega
  have hKpos : 0 < K := by linarith
  have hNr : (110 : ℝ) ≤ N := by exact_mod_cast hN110
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hEN : levelEmax ϑ⁻¹ C₀ K N ≤ N :=
    calc levelEmax ϑ⁻¹ C₀ K N ≤ K ^ (2 * ϑ⁻¹ + 1) := hE2
      _ ≤ K ^ (6 * ϑ⁻¹ + 6) := Real.rpow_le_rpow_of_exponent_le hK1' (by linarith)
      _ ≤ (N : ℝ) ^ (1 / 32 : ℝ) := hKN
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  obtain ⟨hfin, hcard⟩ := lattice_ncard_le (a := ϑ⁻¹) (C₀ := C₀) hNpos hKpos hE1
  refine ⟨hfin, ?_, ?_⟩
  · have h8 : (0 : ℝ) ≤ (N : ℝ) ^ 8 := by positivity
    calc ((lattice ϑ⁻¹ C₀ K N).ncard : ℝ) ≤ 110 * levelEmax ϑ⁻¹ C₀ K N * (N : ℝ) ^ 8 := hcard
      _ ≤ 110 * (N : ℝ) * (N : ℝ) ^ 8 := by gcongr
      _ = 110 * (N : ℝ) ^ 9 := by ring
      _ ≤ (N : ℝ) * (N : ℝ) ^ 9 := by gcongr
      _ = (N : ℝ) ^ 10 := by ring
  · intro M hM z hz
    have hb : 0 ≤ 46 / ϑ * (N : ℝ) ^ 4 * Real.exp (-K ^ 2) := by positivity
    refine (lattice_col_prob M hNpos hKpos hb hz fun w hw => ?_).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
    exact (goodEvent_level M hM hϑ hϑ1 hC₀ hN13 (lattice_im_pos hNpos hKpos hw.1) hκ).2.1

end Rigidity
