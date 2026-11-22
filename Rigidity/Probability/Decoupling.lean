module

public import Rigidity.Probability.LargeDeviation
public import Rigidity.Probability.Moments

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-!
# Off-diagonal quadratic forms by binary decoupling

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Under hypothesis (4.1) (`LDHyp`), for `0 < ϑ ≤ 1`, `n ≥ 1` and `κ ≥ κ_ϑ + log n`, Lemma 4.2, (4.5)
bounds the off-diagonal form `∑_{i ≠ j} X̄ i B i j X j` by
`½ ℓ₂(κ, n) (∑_{i ≠ j} s i² ‖B i j‖² s j²)^{1/2}` outside an event of probability at most
`20 n² ⌈log₂ 2n⌉ ϑ⁻¹ e^{-κ}`.

The proof is Step 5 of the proof of Lemma 4.2. Each pair `i ≠ j` of indices in `{0, …, n-1}` is
assigned a binary digit `d < ⌈log₂ n⌉` in which `i` and `j` differ (any such rule works,
Remark 4.2 (ii); here the least significant one). For each digit `d` and bit `β` the pairs
with digit `d` and `bit_d(i) = β` form a block whose rows and columns lie in the disjoint index
sets `{bit_d = β}` and `{bit_d = 1 - β}`; the bilinear bound (4.6) applies to each block, and a
union bound and the Cauchy–Schwarz inequality over the `2 ⌈log₂ n⌉` blocks give (4.5).

Remark 4.2 (iii): `ℓ(κ)² ≤ (2√2)⁻¹ ℓ₂(κ, n)` (`lossL_sq_le_lossL2`).
-/

/-- Remark 4.2 (iii): `ℓ(κ)² ≤ (2√2)⁻¹ ℓ₂(κ, n)`, for all real `a`, `κ` and all `n`. -/
theorem lossL_sq_le_lossL2 (a κ : ℝ) (n : ℕ) :
    lossL a κ ^ 2 ≤ (2 * Real.sqrt 2)⁻¹ * lossL2 a κ n := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hD : Real.sqrt 2 ≤ Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2) :=
    Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _; linarith)
  calc lossL a κ ^ 2 = (2 * Real.sqrt 2)⁻¹ * (2 * lossL a κ ^ 2 * Real.sqrt 2) := by
        field_simp
    _ ≤ (2 * Real.sqrt 2)⁻¹ * (2 * lossL a κ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2)) := by
        gcongr
    _ = (2 * Real.sqrt 2)⁻¹ * lossL2 a κ n := rfl

section LD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ϑ : ℝ}
  {n : ℕ} {X : Fin n → Ω → ℂ} {s : Fin n → ℝ}

omit [IsProbabilityMeasure μ] in
/-- (4.1) passes to an injective reindexing `a ↦ X (e a)` of the family, with scales
`s (e a)`. -/
private lemma decoupling_ldhyp_comp {m : ℕ} (hX : LDHyp μ ϑ X s) {e : Fin m → Fin n}
    (he : Function.Injective e) : LDHyp μ ϑ (fun a => X (e a)) (fun a => s (e a)) :=
  ⟨hX.indep.precomp he, fun a => hX.meas (e a), fun a => hX.mean (e a),
    fun a => hX.nonneg (e a), fun a => hX.var (e a), fun a => hX.tail (e a)⟩

/-- (4.6) for two independent families of sizes `p, q ≤ n` in either order and possibly empty,
with the bound `10 n² ϑ⁻¹ e^{-κ}` for `κ ≥ κ_ϑ + log n`. -/
private lemma decoupling_bilin (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {p q : ℕ} (hpn : p ≤ n) (hqn : q ≤ n)
    {X₁ : Fin p → Ω → ℂ} {s₁ : Fin p → ℝ} {Y₁ : Fin q → Ω → ℂ} {t₁ : Fin q → ℝ}
    (hX₁ : LDHyp μ ϑ X₁ s₁) (hY₁ : LDHyp μ ϑ Y₁ t₁) (hXY : iIndepFun (Sum.elim X₁ Y₁) μ)
    (B : Matrix (Fin p) (Fin q) ℂ) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ i, ∑ j, s₁ i ^ 2 * ‖B i j‖ ^ 2 * t₁ j ^ 2) <
        ‖∑ i, ∑ j, X₁ i ω * B i j * Y₁ j ω‖} ≤
      ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := by
  have hempty : (∀ ω, ∑ i, ∑ j, X₁ i ω * B i j * Y₁ j ω = 0) →
      μ {ω | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ i, ∑ j, s₁ i ^ 2 * ‖B i j‖ ^ 2 * t₁ j ^ 2) <
        ‖∑ i, ∑ j, X₁ i ω * B i j * Y₁ j ω‖} ≤
      ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := by
    intro h0
    have : {ω | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ i, ∑ j, s₁ i ^ 2 * ‖B i j‖ ^ 2 * t₁ j ^ 2) <
        ‖∑ i, ∑ j, X₁ i ω * B i j * Y₁ j ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, h0 ω, norm_zero, Set.mem_empty_iff_false, iff_false, not_lt]
      positivity
    rw [this, measure_empty]
    exact bot_le
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact hempty fun ω => by simp
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact hempty fun ω => by simp
  have hlog : ∀ m : ℕ, 1 ≤ m → m ≤ n → kappaTheta ϑ⁻¹ + Real.log m ≤ κ := fun m hm hmn => by
    have : Real.log (m : ℝ) ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)
    linarith
  have hbd : ∀ m : ℕ, m ≤ n → ENNReal.ofReal (10 * m ^ 2 / ϑ * Real.exp (-κ)) ≤
      ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := fun m hmn => by
    apply ENNReal.ofReal_le_ofReal
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hϑ.le) (Real.exp_pos _).le
    gcongr
  rcases le_total q p with hqp | hpq
  · exact (ld_bilinear hX₁ hϑ hϑ1 hp hq hqp hY₁ hXY B (hlog p hp hpn)).trans (hbd p hpn)
  · have hYX : iIndepFun (Sum.elim Y₁ X₁) μ := by
      have h := hXY.precomp Sum.swap_leftInverse.injective
      convert h using 1
      funext k
      cases k <;> rfl
    have h := ld_bilinear hY₁ hϑ hϑ1 hq hp hpq hX₁ hYX (Matrix.of fun j i => B i j) (hlog q hq hqn)
    simp only [Matrix.of_apply] at h
    have e1 : ∑ i, ∑ j, s₁ i ^ 2 * ‖B i j‖ ^ 2 * t₁ j ^ 2 =
        ∑ j, ∑ i, t₁ j ^ 2 * ‖B i j‖ ^ 2 * s₁ i ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∀ ω, ∑ i, ∑ j, X₁ i ω * B i j * Y₁ j ω = ∑ j, ∑ i, Y₁ j ω * B i j * X₁ i ω := by
      intro ω
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    simp only [e1, e2]
    exact h.trans (hbd q hqn)

/-- A double sum over `Fin n` of terms vanishing outside `I × J` is the double sum over the
increasing enumerations of `I` and `J`. -/
private lemma decoupling_sum_reindex {M : Type*} [AddCommMonoid M] (I J : Finset (Fin n))
    (g : Fin n → Fin n → M) (hg : ∀ i j, ¬ (i ∈ I ∧ j ∈ J) → g i j = 0) :
    ∑ i, ∑ j, g i j = ∑ a, ∑ b, g (I.orderEmbOfFin rfl a) (J.orderEmbOfFin rfl b) := by
  have hI : ∀ f : Fin n → M, ∑ i ∈ I, f i = ∑ a, f (I.orderEmbOfFin rfl a) := fun f => by
    conv_lhs => rw [← I.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]
    rfl
  have hJ : ∀ f : Fin n → M, ∑ j ∈ J, f j = ∑ b, f (J.orderEmbOfFin rfl b) := fun f => by
    conv_lhs => rw [← J.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]
    rfl
  have h1 : ∑ i ∈ I, ∑ j ∈ J, g i j = ∑ i, ∑ j, g i j := by
    rw [Finset.sum_subset (Finset.subset_univ I)
      (fun i _ hi => Finset.sum_eq_zero fun j _ => hg i j fun h => hi h.1)]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_subset (Finset.subset_univ J) fun j _ hj => hg i j fun h => hj h.2
  rw [← h1, hI]
  exact Finset.sum_congr rfl fun a _ => hJ _

/-- The bound (4.6) for one block: a matrix `M` supported in `I × J` with `I`, `J` disjoint,
for the form `∑ X̄ i M i j X j` of a single family. -/
private lemma decoupling_block (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    {I J : Finset (Fin n)} (hIJ : Disjoint I J) (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ¬ (i ∈ I ∧ j ∈ J) → M i j = 0) {κ : ℝ}
    (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | lossL ϑ⁻¹ κ ^ 2 * Real.sqrt (∑ i, ∑ j, s i ^ 2 * ‖M i j‖ ^ 2 * s j ^ 2) <
        ‖∑ i, ∑ j, starRingEnd ℂ (X i ω) * M i j * X j ω‖} ≤
      ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := by
  set eI := I.orderEmbOfFin rfl with heI
  set eJ := J.orderEmbOfFin rfl with heJ
  have hne : ∀ a b, eI a ≠ eJ b := fun a b h =>
    Finset.disjoint_left.1 hIJ (I.orderEmbOfFin_mem rfl a) (h ▸ J.orderEmbOfFin_mem rfl b)
  have he : Function.Injective (Sum.elim eI eJ) := eI.injective.sumElim eJ.injective hne
  have hX₁ := decoupling_ldhyp_comp hX.conj eI.injective
  have hY₁ := decoupling_ldhyp_comp hX eJ.injective
  have hXY : iIndepFun (Sum.elim (fun a ω => starRingEnd ℂ (X (eI a) ω))
      (fun b => X (eJ b))) μ := by
    have h := (hX.indep.precomp he).comp
      (fun k => Sum.elim (fun _ => (starRingEnd ℂ : ℂ → ℂ)) (fun _ => id) k)
      (fun k => by
        cases k
        · exact Complex.continuous_conj.measurable
        · exact measurable_id)
    convert h using 1
    funext k
    cases k <;> rfl
  have hpn : I.card ≤ n := (Finset.card_le_univ I).trans_eq (Fintype.card_fin n)
  have hqn : J.card ≤ n := (Finset.card_le_univ J).trans_eq (Fintype.card_fin n)
  have h := decoupling_bilin hϑ hϑ1 hpn hqn hX₁ hY₁ hXY
    (Matrix.of fun a b => M (eI a) (eJ b)) hκ
  simp only [Matrix.of_apply] at h
  have e1 : ∑ i, ∑ j, s i ^ 2 * ‖M i j‖ ^ 2 * s j ^ 2 =
      ∑ a, ∑ b, s (eI a) ^ 2 * ‖M (eI a) (eJ b)‖ ^ 2 * s (eJ b) ^ 2 :=
    decoupling_sum_reindex I J (fun i j => s i ^ 2 * ‖M i j‖ ^ 2 * s j ^ 2)
      fun i j hij => by simp [hM i j hij]
  have e2 : ∀ ω, ∑ i, ∑ j, starRingEnd ℂ (X i ω) * M i j * X j ω =
      ∑ a, ∑ b, starRingEnd ℂ (X (eI a) ω) * M (eI a) (eJ b) * X (eJ b) ω := fun ω =>
    decoupling_sum_reindex I J (fun i j => starRingEnd ℂ (X i ω) * M i j * X j ω)
      fun i j hij => by simp [hM i j hij]
  simp only [e1, e2]
  exact h

open Classical in
/-- A binary digit in which two distinct indices differ: the least such digit (Step 5 of the
proof of Lemma 4.2 and Remark 4.2 (ii)). -/
private noncomputable def decouplingDigit {n : ℕ} (i j : Fin n) : ℕ :=
  if h : ∃ d, Nat.testBit (i : ℕ) d ≠ Nat.testBit (j : ℕ) d then Nat.find h else 0

/-- For `i ≠ j` in `Fin n`, the digit `decouplingDigit i j` is below `⌈log₂ n⌉` and the binary
digits of `i` and `j` at that position differ. -/
private lemma decoupling_digit_spec {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    decouplingDigit i j < Nat.clog 2 n ∧
      Nat.testBit (i : ℕ) (decouplingDigit i j) ≠ Nat.testBit (j : ℕ) (decouplingDigit i j) := by
  have hex : ∃ d, Nat.testBit (i : ℕ) d ≠ Nat.testBit (j : ℕ) d := by
    by_contra h
    push Not at h
    exact hij (Fin.ext (Nat.eq_of_testBit_eq h))
  have hspec : Nat.testBit (i : ℕ) (decouplingDigit i j) ≠
      Nat.testBit (j : ℕ) (decouplingDigit i j) := by
    rw [decouplingDigit, dite_eq_left hex]
    exact Nat.find_spec hex
  refine ⟨?_, hspec⟩
  by_contra hD
  push Not at hD
  have hpow : n ≤ 2 ^ decouplingDigit i j :=
    (Nat.le_pow_clog one_lt_two n).trans (Nat.pow_le_pow_right two_pos hD)
  exact hspec ((Nat.testBit_eq_false_of_lt (i.2.trans_le hpow)).trans
    (Nat.testBit_eq_false_of_lt (j.2.trans_le hpow)).symm)

/-- The block `B^{(d, β)}` of Step 5: the entries `B i j` with `i ≠ j`, digit
`decouplingDigit i j = d` and `bit_d(i) = β`, the other entries set to `0`. -/
private noncomputable def decouplingBlock (B : Matrix (Fin n) (Fin n) ℂ)
    (k : Fin (Nat.clog 2 n) × Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j =>
    if i ≠ j ∧ decouplingDigit i j = k.1 ∧ Nat.testBit (i : ℕ) k.1 = k.2 then B i j else 0

/-- The partition property (i) of Step 5: for every pair `(i, j)` exactly one block contains it
if `i ≠ j`, and none if `i = j`. -/
private lemma decoupling_sum_blocks {M : Type*} [AddCommMonoid M] (i j : Fin n) (f : M) :
    ∑ k : Fin (Nat.clog 2 n) × Bool,
      (if i ≠ j ∧ decouplingDigit i j = k.1 ∧ Nat.testBit (i : ℕ) k.1 = k.2 then f else 0) =
      if i = j then 0 else f := by
  by_cases hij : i = j
  · simp [hij]
  obtain ⟨hlt, -⟩ := decoupling_digit_spec hij
  rw [ite_eq_right hij, Finset.sum_eq_single
    ((⟨decouplingDigit i j, hlt⟩ : Fin (Nat.clog 2 n)), Nat.testBit (i : ℕ) (decouplingDigit i j))]
  · simp [hij]
  · rintro ⟨d, β⟩ - hk
    rw [ite_eq_right]
    rintro ⟨-, hd, hβ⟩
    apply hk
    have hd' : d = ⟨decouplingDigit i j, hlt⟩ := Fin.ext hd.symm
    subst hd'
    exact Prod.ext rfl hβ.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Properties (ii), (iii) of Step 5: the block `B^{(d, β)}` is supported in
`{bit_d = β} × {bit_d = 1 - β}`. -/
private lemma decoupling_block_support (B : Matrix (Fin n) (Fin n) ℂ)
    (k : Fin (Nat.clog 2 n) × Bool) (i j : Fin n)
    (h : ¬ (i ∈ Finset.univ.filter (fun i : Fin n => Nat.testBit (i : ℕ) k.1 = k.2) ∧
      j ∈ Finset.univ.filter (fun j : Fin n => Nat.testBit (j : ℕ) k.1 = !k.2))) :
    decouplingBlock B k i j = 0 := by
  simp only [decouplingBlock, Matrix.of_apply]
  rw [ite_eq_right]
  rintro ⟨hij, hd, hβ⟩
  apply h
  refine ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hβ⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
  have hne := (decoupling_digit_spec hij).2
  rw [hd, hβ] at hne
  revert hne
  generalize Nat.testBit (j : ℕ) k.1 = b
  cases b <;> cases k.2 <;> simp

/-- Lemma 4.2, (4.5): off-diagonal quadratic forms. -/
theorem ld_offdiag (hX : LDHyp μ ϑ X s) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℂ) {κ : ℝ} (hκ : kappaTheta ϑ⁻¹ + Real.log n ≤ κ) :
    μ {ω | lossL2 ϑ⁻¹ κ n / 2 * Real.sqrt (∑ i, ∑ j, if i = j then 0 else
          s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) <
        ‖∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω‖} ≤
      ENNReal.ofReal (20 * n ^ 2 * Nat.clog 2 (2 * n) / ϑ * Real.exp (-κ)) := by
  set ℓ := lossL ϑ⁻¹ κ with hℓ
  have hQoff : (∑ i, ∑ j, if i = j then 0 else s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) =
      ∑ k : Fin (Nat.clog 2 n) × Bool,
        ∑ i, ∑ j, s i ^ 2 * ‖decouplingBlock B k i j‖ ^ 2 * s j ^ 2 := by
    have hpt : ∀ i j, (if i = j then (0 : ℝ) else s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) =
        ∑ k : Fin (Nat.clog 2 n) × Bool, s i ^ 2 * ‖decouplingBlock B k i j‖ ^ 2 * s j ^ 2 := by
      intro i j
      rw [← decoupling_sum_blocks i j]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [decouplingBlock, Matrix.of_apply]
      split_ifs <;> simp
    calc _ = ∑ i, ∑ j, ∑ k : Fin (Nat.clog 2 n) × Bool,
          s i ^ 2 * ‖decouplingBlock B k i j‖ ^ 2 * s j ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
      _ = ∑ i, ∑ k : Fin (Nat.clog 2 n) × Bool, ∑ j,
          s i ^ 2 * ‖decouplingBlock B k i j‖ ^ 2 * s j ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hF : ∀ ω, (∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω) =
      ∑ k : Fin (Nat.clog 2 n) × Bool,
        ∑ i, ∑ j, starRingEnd ℂ (X i ω) * decouplingBlock B k i j * X j ω := by
    intro ω
    have hpt : ∀ i j,
        (if i = j then (0 : ℂ) else starRingEnd ℂ (X i ω) * B i j * X j ω) =
        ∑ k : Fin (Nat.clog 2 n) × Bool,
          starRingEnd ℂ (X i ω) * decouplingBlock B k i j * X j ω := by
      intro i j
      rw [← decoupling_sum_blocks i j]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [decouplingBlock, Matrix.of_apply]
      split_ifs <;> simp
    calc _ = ∑ i, ∑ j, ∑ k : Fin (Nat.clog 2 n) × Bool,
          starRingEnd ℂ (X i ω) * decouplingBlock B k i j * X j ω :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
      _ = ∑ i, ∑ k : Fin (Nat.clog 2 n) × Bool, ∑ j,
          starRingEnd ℂ (X i ω) * decouplingBlock B k i j * X j ω :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  set Q : Fin (Nat.clog 2 n) × Bool → ℝ :=
    fun k => ∑ i, ∑ j, s i ^ 2 * ‖decouplingBlock B k i j‖ ^ 2 * s j ^ 2 with hQ
  set F : Fin (Nat.clog 2 n) × Bool → Ω → ℂ :=
    fun k ω => ∑ i, ∑ j, starRingEnd ℂ (X i ω) * decouplingBlock B k i j * X j ω with hFdef
  set E : Fin (Nat.clog 2 n) × Bool → Set Ω :=
    fun k => {ω | ℓ ^ 2 * Real.sqrt (Q k) < ‖F k ω‖} with hE
  have hEk : ∀ k, μ (E k) ≤ ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) := fun k =>
    decoupling_block hX hϑ hϑ1
      (I := Finset.univ.filter (fun i : Fin n => Nat.testBit (i : ℕ) k.1 = k.2))
      (J := Finset.univ.filter (fun j : Fin n => Nat.testBit (j : ℕ) k.1 = !k.2))
      (Finset.disjoint_filter.2 fun i _ h1 h2 => by
        rw [h1] at h2
        revert h2
        cases k.2 <;> simp)
      (decouplingBlock B k) (decoupling_block_support B k) hκ
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => by
    simp only [hQ]
    positivity
  have hcard : (Fintype.card (Fin (Nat.clog 2 n) × Bool) : ℝ) = 2 * (Nat.clog 2 n : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  have hsub : {ω | lossL2 ϑ⁻¹ κ n / 2 * Real.sqrt (∑ i, ∑ j, if i = j then 0 else
          s i ^ 2 * ‖B i j‖ ^ 2 * s j ^ 2) <
        ‖∑ i, ∑ j, if i = j then 0 else starRingEnd ℂ (X i ω) * B i j * X j ω‖} ⊆
      ⋃ k, E k := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    simp only [Set.mem_ofPred_eq] at hω
    rw [hQoff, hF ω] at hω
    have hle : ‖∑ k, F k ω‖ ≤
        ℓ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ)) * Real.sqrt (∑ k, Q k) :=
      calc ‖∑ k, F k ω‖ ≤ ∑ k, ‖F k ω‖ := norm_sum_le _ _
        _ ≤ ∑ k, ℓ ^ 2 * Real.sqrt (Q k) :=
          Finset.sum_le_sum fun k _ => not_lt.1 (hnot k)
        _ = ℓ ^ 2 * ∑ k, Real.sqrt 1 * Real.sqrt (Q k) := by
          rw [Finset.mul_sum]
          simp
        _ ≤ ℓ ^ 2 * (Real.sqrt (∑ _k : Fin (Nat.clog 2 n) × Bool, (1 : ℝ)) *
            Real.sqrt (∑ k, Q k)) :=
          mul_le_mul_of_nonneg_left
            (Real.sum_sqrt_mul_sqrt_le _ (fun _ => zero_le_one) hQ0) (sq_nonneg _)
        _ = ℓ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ)) * Real.sqrt (∑ k, Q k) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
          ring
    have hℓ2 : ℓ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ)) ≤ lossL2 ϑ⁻¹ κ n / 2 := by
      have : lossL2 ϑ⁻¹ κ n / 2 = ℓ ^ 2 * Real.sqrt (2 * (Nat.clog 2 n : ℝ) + 2) := by
        rw [lossL2, hℓ]
        ring
      rw [this]
      gcongr
      linarith
    have hfin : ‖∑ k, F k ω‖ ≤ lossL2 ϑ⁻¹ κ n / 2 * Real.sqrt (∑ k, Q k) :=
      hle.trans (mul_le_mul_of_nonneg_right hℓ2 (Real.sqrt_nonneg _))
    exact absurd hω (not_lt.2 hfin)
  have hD : (Nat.clog 2 n : ℝ) ≤ Nat.clog 2 (2 * n) := by
    exact_mod_cast Nat.clog_mono_right 2 (by omega : n ≤ 2 * n)
  calc μ _ ≤ μ (⋃ k, E k) := measure_mono hsub
    _ ≤ ∑ k, μ (E k) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _k : Fin (Nat.clog 2 n) × Bool, ENNReal.ofReal (10 * n ^ 2 / ϑ * Real.exp (-κ)) :=
        Finset.sum_le_sum fun k _ => hEk k
    _ = ENNReal.ofReal (2 * (Nat.clog 2 n : ℝ) * (10 * n ^ 2 / ϑ * Real.exp (-κ))) := by
        rw [Finset.sum_const, Finset.card_univ, ← ENNReal.ofReal_nsmul, nsmul_eq_mul, hcard]
    _ ≤ ENNReal.ofReal (20 * n ^ 2 * Nat.clog 2 (2 * n) / ϑ * Real.exp (-κ)) := by
        apply ENNReal.ofReal_le_ofReal
        have : 2 * (Nat.clog 2 n : ℝ) * (10 * n ^ 2 / ϑ * Real.exp (-κ)) =
            20 * n ^ 2 * (Nat.clog 2 n : ℝ) / ϑ * Real.exp (-κ) := by ring
        rw [this]
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hϑ.le)
          (Real.exp_pos _).le
        gcongr

end LD

end Rigidity
