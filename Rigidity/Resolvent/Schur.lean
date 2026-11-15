import Rigidity.Resolvent.Ward

/-!
# Minors, the Schur complement and the resolvent expansion formulas

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `H` over `ℝ` or `ℂ` (a field `𝕜` with `RCLike 𝕜`), `η = Im z > 0` and a set
of indices `T`, this file introduces the Green function `G^{(T)}` of the minor `H^{(T)}` extended
by `0` to the indices in `T` (Definition 3.1), its normalised trace `m^{(T)}`, and the Schur
complement `M^S` of (3.5).  It proves the items of Lemma 3.6:
* the block identity `(G_ab)_{a,b ∈ S} = (M^S)⁻¹`;
* (I1): `1 / G_ii = h_ii - z - ∑_{k,l} h_ik G^{(i)}_kl h_li`;
* (I2): the three expansions of `G_ij` and `G_ji` for `i ≠ j`;
* (I3) for one removed index: `G^{(k)}_ij = G_ij - G_ik G_kj / G_kk`;
* (I5): `|m^{(T)} - m| ≤ |T| / (N η)`.

The proofs use the block inverse formula (BI) of Lemma 3.6 in the following form.  With
`B = H - z`, `P_S` the diagonal projection onto the coordinates in `S`, `Q_S = 1 - P_S` and
`G^{(S)}` extended by `0`, one has `Q_S B G^{(S)} = Q_S`, `G^{(S)} B Q_S = Q_S`; from these and
`G B = B G = 1` follow `Q_S G = G^{(S)} - G^{(S)} B P_S G`, `G Q_S = G^{(S)} - G P_S B G^{(S)}`,
and, for `t ∉ S`, `Q_{S ∪ t} G^{(S)} = G^{(S ∪ t)} - G^{(S ∪ t)} B E_tt G^{(S)}`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `G^{(T)}_{kl}` (Definition before Lemma 3.5), extended by `0` to indices in `T`. -/
noncomputable def greenT {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (T : Finset (Fin N)) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun k l => if h : k ∉ T ∧ l ∉ T then greenMinor A T z ⟨k, h.1⟩ ⟨l, h.2⟩ else 0

/-- `m^{(T)} = N⁻¹ ∑_{k ∉ T} G^{(T)}_{kk}` (normalised by `N`). -/
noncomputable def stieltjesT {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (T : Finset (Fin N))
    (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k, greenT A T z k k

/-- The `S × S` matrix `M^S` of Lemma 3.6, (3.5). -/
noncomputable def schurM {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (S : Finset (Fin N)) (z : ℂ) :
    Matrix S S ℂ :=
  Matrix.of fun a b => toC (A a b) - (if a = b then z else 0) -
    ∑ k, ∑ l, toC (A a k) * greenT A S z k l * toC (A l b)

/-! ### Block identities in a ring -/

/-- The left block identity: from `Q₁ B T₁ = Q₁`, `T₂ B Q₂ = Q₂`, `Q₁ T₁ = T₁` and `T₂ Q₁ = T₂`,
`Q₂ T₁ = T₂ - T₂ B (Q₁ - Q₂) T₁`. -/
private theorem schur_rel_left {R : Type*} [Ring R] {B Q₁ Q₂ T₁ T₂ : R}
    (h1 : Q₁ * B * T₁ = Q₁) (h2 : T₂ * B * Q₂ = Q₂) (h3 : Q₁ * T₁ = T₁) (h4 : T₂ * Q₁ = T₂) :
    Q₂ * T₁ = T₂ - T₂ * B * (Q₁ - Q₂) * T₁ := by
  have e : T₂ * B * T₁ = T₂ := by
    calc T₂ * B * T₁ = T₂ * Q₁ * B * T₁ := by rw [h4]
      _ = T₂ * (Q₁ * B * T₁) := by noncomm_ring
      _ = T₂ := by rw [h1, h4]
  calc Q₂ * T₁ = T₂ * B * Q₂ * T₁ := by rw [h2]
    _ = T₂ * B * (Q₁ * T₁) - T₂ * B * (Q₁ - Q₂) * T₁ := by noncomm_ring
    _ = T₂ - T₂ * B * (Q₁ - Q₂) * T₁ := by rw [h3, e]

/-- The right block identity: from `T₁ B Q₁ = Q₁`, `Q₂ B T₂ = Q₂`, `T₁ Q₁ = T₁` and `Q₁ T₂ = T₂`,
`T₁ Q₂ = T₂ - T₁ (Q₁ - Q₂) B T₂`. -/
private theorem schur_rel_right {R : Type*} [Ring R] {B Q₁ Q₂ T₁ T₂ : R}
    (h1 : T₁ * B * Q₁ = Q₁) (h2 : Q₂ * B * T₂ = Q₂) (h3 : T₁ * Q₁ = T₁) (h4 : Q₁ * T₂ = T₂) :
    T₁ * Q₂ = T₂ - T₁ * (Q₁ - Q₂) * B * T₂ := by
  have e : T₁ * B * T₂ = T₂ := by
    calc T₁ * B * T₂ = T₁ * B * (Q₁ * T₂) := by rw [h4]
      _ = T₁ * B * Q₁ * T₂ := by noncomm_ring
      _ = T₂ := by rw [h1, h4]
  calc T₁ * Q₂ = T₁ * (Q₂ * B * T₂) := by rw [h2]
    _ = T₁ * Q₁ * B * T₂ - T₁ * (Q₁ - Q₂) * B * T₂ := by noncomm_ring
    _ = T₂ - T₁ * (Q₁ - Q₂) * B * T₂ := by rw [h3, e]

/-! ### The matrices `H - z`, `P_S`, `Q_S` -/

section Helpers

variable {N : ℕ}

/-- `H - z` as a complex matrix. -/
private noncomputable def schurB (A : Matrix (Fin N) (Fin N) 𝕜) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  A.map toC - z • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- The diagonal projection `P_S` onto the coordinates in `S`. -/
private noncomputable def schurP (S : Finset (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if i ∈ S then 1 else 0

/-- The diagonal projection `Q_S = 1 - P_S` onto the coordinates outside `S`. -/
private noncomputable def schurQ (S : Finset (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => if i ∈ S then 0 else 1

private theorem schurB_apply (A : Matrix (Fin N) (Fin N) 𝕜) (z : ℂ) (a b : Fin N) :
    schurB A z a b = toC (A a b) - if a = b then z else 0 := by
  by_cases h : a = b
  · subst h; simp [schurB]
  · simp [schurB, Matrix.one_apply_ne h, h]

private theorem schur_one_sub_Q (S : Finset (Fin N)) : 1 - schurQ S = schurP S := by
  rw [sub_eq_iff_eq_add, schurP, schurQ, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

private theorem schurQ_sub_insert {S : Finset (Fin N)} {t : Fin N} (ht : t ∉ S) :
    schurQ S - schurQ (insert t S) = Matrix.diagonal fun i => if i = t then 1 else 0 := by
  rw [schurQ, schurQ, Matrix.diagonal_sub]
  congr 1
  funext i
  by_cases h : i = t
  · subst h; simp [ht]
  · by_cases hi : i ∈ S <;> simp [h, hi]

/-- The sum over `Fin N` of a function vanishing on `S` is the sum over the complement. -/
private theorem schur_sum_dite {M : Type*} [AddCommMonoid M] (S : Finset (Fin N))
    (f : (i : Fin N) → i ∉ S → M) :
    ∑ i, (if h : i ∉ S then f i h else 0) = ∑ i : {i // i ∉ S}, f i.1 i.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∉ S)]
  have h0 : ∑ i : {x // ¬x ∉ S}, (if h : (i : Fin N) ∉ S then f i h else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => dite_eq_right_of_eq_false (eq_false i.2)
  rw [h0, add_zero]
  exact Finset.sum_congr rfl fun i _ => dite_eq_left_of_eq_true (eq_true i.2)

variable {A : Matrix (Fin N) (Fin N) 𝕜} {z : ℂ}

private theorem greenT_of_mem_left {S : Finset (Fin N)} {k : Fin N} (hk : k ∈ S) (l : Fin N) :
    greenT A S z k l = 0 := by
  simp [greenT, hk]

private theorem greenT_of_mem_right {S : Finset (Fin N)} {l : Fin N} (hl : l ∈ S) (k : Fin N) :
    greenT A S z k l = 0 := by
  simp [greenT, hl]

private theorem greenT_of_not_mem {S : Finset (Fin N)} {k l : Fin N} (hk : k ∉ S) (hl : l ∉ S) :
    greenT A S z k l = greenMinor A S z ⟨k, hk⟩ ⟨l, hl⟩ := by
  simp [greenT, hk, hl]

private theorem schurQ_mul_greenT {S S' : Finset (Fin N)} (h : S ⊆ S') :
    schurQ S * greenT A S' z = greenT A S' z := by
  ext k l
  rw [schurQ, Matrix.diagonal_mul]
  by_cases hk : k ∈ S
  · simp [hk, greenT_of_mem_left (h hk)]
  · simp [hk]

private theorem greenT_mul_schurQ {S S' : Finset (Fin N)} (h : S ⊆ S') :
    greenT A S' z * schurQ S = greenT A S' z := by
  ext k l
  rw [schurQ, Matrix.mul_diagonal]
  by_cases hl : l ∈ S
  · simp [hl, greenT_of_mem_right (h hl)]
  · simp [hl]

private theorem schur_minor_sub (A : Matrix (Fin N) (Fin N) 𝕜) (S : Finset (Fin N)) (z : ℂ) :
    (minor A S).map toC - z • (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℂ) =
      (schurB A z).submatrix Subtype.val Subtype.val := by
  ext i j
  rw [Matrix.submatrix_apply, schurB_apply]
  by_cases h : i = j
  · subst h; simp [minor]
  · have h' : (i : Fin N) ≠ j := fun e => h (Subtype.ext e)
    simp [minor, Matrix.one_apply_ne h, h']

private theorem schurQ_B_greenT (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    schurQ S * schurB A z * greenT A S z = schurQ S := by
  have hmul : ((minor A S).map toC - z • (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℂ)) *
      greenMinor A S z = 1 := green_mul (hA.submatrix _) hz.ne'
  rw [schur_minor_sub] at hmul
  ext k l
  rw [Matrix.mul_assoc, schurQ, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hk : k ∈ S
  · simp [hk]
  by_cases hl : l ∈ S
  · have hkl : k ≠ l := fun h => hk (h ▸ hl)
    simp [hk, hkl, Matrix.mul_apply, greenT_of_mem_right hl]
  have h1 := congrFun (congrFun hmul ⟨k, hk⟩) ⟨l, hl⟩
  rw [Matrix.mul_apply] at h1
  have h2 : ∑ m, schurB A z k m * greenT A S z m l =
      ∑ m, (if h : m ∉ S then schurB A z k m * greenMinor A S z ⟨m, h⟩ ⟨l, hl⟩ else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m ∈ S
    · simp [hm, greenT_of_mem_left hm]
    · simp [hm, greenT_of_not_mem hm hl]
  rw [ite_eq_right hk, one_mul, Matrix.mul_apply, h2, schur_sum_dite]
  simp only [Matrix.submatrix_apply] at h1
  rw [h1, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl; simp
  · have : (⟨k, hk⟩ : {i // i ∉ S}) ≠ ⟨l, hl⟩ := fun e => hkl (congrArg Subtype.val e)
    simp [hkl, this]

private theorem greenT_B_schurQ (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    greenT A S z * schurB A z * schurQ S = schurQ S := by
  have hmul : greenMinor A S z *
      ((minor A S).map toC - z • (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (det_sub_smul_ne_zero (isHermitian_map_toC (hA.submatrix _)) hz.ne'))
  rw [schur_minor_sub] at hmul
  ext k l
  rw [schurQ, Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases hl : l ∈ S
  · by_cases hkl : k = l
    · subst hkl; simp [hl]
    · simp [hl, hkl]
  by_cases hk : k ∈ S
  · have hkl : k ≠ l := fun h => hl (h ▸ hk)
    simp [hl, hkl, Matrix.mul_apply, greenT_of_mem_left hk]
  have h1 := congrFun (congrFun hmul ⟨k, hk⟩) ⟨l, hl⟩
  rw [Matrix.mul_apply] at h1
  have h2 : ∑ m, greenT A S z k m * schurB A z m l =
      ∑ m, (if h : m ∉ S then greenMinor A S z ⟨k, hk⟩ ⟨m, h⟩ * schurB A z m l else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m ∈ S
    · simp [hm, greenT_of_mem_right hm]
    · simp [hm, greenT_of_not_mem hk hm]
  rw [ite_eq_right hl, mul_one, Matrix.mul_apply, h2, schur_sum_dite]
  simp only [Matrix.submatrix_apply] at h1
  rw [h1, Matrix.one_apply]
  by_cases hkl : k = l
  · subst hkl; simp [hk]
  · have : (⟨k, hk⟩ : {i // i ∉ S}) ≠ ⟨l, hl⟩ := fun e => hkl (congrArg Subtype.val e)
    simp [hkl, this]

private theorem schur_green_B (hA : A.IsHermitian) (hz : 0 < z.im) :
    green A z * schurB A z = 1 :=
  Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero (isHermitian_map_toC hA) hz.ne'))

private theorem schur_B_green (hA : A.IsHermitian) (hz : 0 < z.im) :
    schurB A z * green A z = 1 :=
  green_mul hA hz.ne'

/-! ### The block inverse formula (BI) -/

/-- `Q_S G = G^{(S)} - G^{(S)} B P_S G`. -/
private theorem schur_left (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    schurQ S * green A z =
      greenT A S z - greenT A S z * schurB A z * schurP S * green A z := by
  have h := schur_rel_left (B := schurB A z) (Q₁ := 1) (Q₂ := schurQ S) (T₁ := green A z)
    (T₂ := greenT A S z) (by rw [one_mul, schur_B_green hA hz]) (greenT_B_schurQ hA hz S)
    (one_mul _) (mul_one _)
  rwa [schur_one_sub_Q] at h

/-- `G Q_S = G^{(S)} - G P_S B G^{(S)}`. -/
private theorem schur_right (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    green A z * schurQ S =
      greenT A S z - green A z * schurP S * schurB A z * greenT A S z := by
  have h := schur_rel_right (B := schurB A z) (Q₁ := 1) (Q₂ := schurQ S) (T₁ := green A z)
    (T₂ := greenT A S z) (by rw [mul_one, schur_green_B hA hz]) (schurQ_B_greenT hA hz S)
    (mul_one _) (one_mul _)
  rwa [schur_one_sub_Q] at h

/-- `Q_{S ∪ t} G^{(S)} = G^{(S ∪ t)} - G^{(S ∪ t)} B E_tt G^{(S)}` for `t ∉ S`. -/
private theorem schur_insert (hA : A.IsHermitian) (hz : 0 < z.im) {S : Finset (Fin N)}
    {t : Fin N} (ht : t ∉ S) :
    schurQ (insert t S) * greenT A S z = greenT A (insert t S) z -
      greenT A (insert t S) z * schurB A z * (Matrix.diagonal fun i => if i = t then 1 else 0) *
        greenT A S z := by
  have h := schur_rel_left (B := schurB A z) (Q₁ := schurQ S) (Q₂ := schurQ (insert t S))
    (T₁ := greenT A S z) (T₂ := greenT A (insert t S) z) (schurQ_B_greenT hA hz S)
    (greenT_B_schurQ hA hz _) (schurQ_mul_greenT (Finset.Subset.refl S))
    (greenT_mul_schurQ (Finset.subset_insert t S))
  rwa [schurQ_sub_insert ht] at h

/-- `G^{(∅)} = G`. -/
private theorem greenT_empty (hA : A.IsHermitian) (hz : 0 < z.im) : greenT A ∅ z = green A z := by
  have h := schur_left hA hz ∅
  have hQ : schurQ (∅ : Finset (Fin N)) = 1 := by simp [schurQ]
  have hP : schurP (∅ : Finset (Fin N)) = 0 := by simp [schurP]
  rw [hQ, hP, one_mul, mul_zero, zero_mul, sub_zero] at h
  exact h.symm

/-- `P_S G P_S (B - B G^{(S)} B) = P_S`: the identity `G_{SS} M^S = 1`. -/
private theorem schur_XI (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    schurP S * green A z * schurP S *
      (schurB A z - schurB A z * greenT A S z * schurB A z) = schurP S := by
  have hGQ := schur_right hA hz S
  have hPQ : schurP S + schurQ S = 1 := by rw [← schur_one_sub_Q]; abel
  have hPT : schurP S * greenT A S z = 0 := by
    ext k l
    rw [schurP, Matrix.diagonal_mul]
    by_cases hk : k ∈ S
    · simp [hk, greenT_of_mem_left hk]
    · simp [hk]
  set P := schurP S
  set Q := schurQ S
  set G := green A z
  set B := schurB A z
  set T := greenT A S z
  calc P * G * P * (B - B * T * B) = P * G * P * B + P * (T - G * P * B * T) * B - P * T * B := by
        noncomm_ring
    _ = P * G * P * B + P * (G * Q) * B - P * T * B := by rw [hGQ]
    _ = P * G * (P + Q) * B - P * T * B := by noncomm_ring
    _ = P := by rw [hPQ, mul_one, mul_assoc, schur_green_B hA hz, mul_one, hPT, zero_mul, sub_zero]

/-! ### Entries -/

private theorem schur_B_greenT_apply {S : Finset (Fin N)} {a : Fin N} (ha : a ∈ S) (l : Fin N) :
    (schurB A z * greenT A S z) a l = ∑ k, toC (A a k) * greenT A S z k l := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : a = k
  · subst hk; simp [greenT_of_mem_left ha]
  · rw [schurB_apply, ite_eq_right hk, sub_zero]

private theorem schur_greenT_B_apply {S : Finset (Fin N)} {b : Fin N} (hb : b ∈ S) (k : Fin N) :
    (greenT A S z * schurB A z) k b = ∑ m, greenT A S z k m * toC (A m b) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m = b
  · subst hm; simp [greenT_of_mem_right hb]
  · rw [schurB_apply, ite_eq_right hm, sub_zero]

private theorem schur_BTB_apply {S : Finset (Fin N)} {a b : Fin N} (ha : a ∈ S) (hb : b ∈ S) :
    (schurB A z * greenT A S z * schurB A z) a b =
      ∑ k, ∑ l, toC (A a k) * greenT A S z k l * toC (A l b) := by
  calc (schurB A z * greenT A S z * schurB A z) a b
        = ∑ l, (schurB A z * greenT A S z) a l * schurB A z l b := Matrix.mul_apply
    _ = ∑ l, ∑ k, toC (A a k) * greenT A S z k l * toC (A l b) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [schur_B_greenT_apply ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hl : l = b
        · subst hl; simp [greenT_of_mem_right hb]
        · rw [schurB_apply, ite_eq_right hl, sub_zero]
    _ = ∑ k, ∑ l, toC (A a k) * greenT A S z k l * toC (A l b) := Finset.sum_comm

private theorem schurM_apply {S : Finset (Fin N)} (c b : S) :
    schurM A S z c b = (schurB A z - schurB A z * greenT A S z * schurB A z) c b := by
  rw [Matrix.sub_apply, schur_BTB_apply c.2 b.2, schurB_apply]
  by_cases h : c = b
  · subst h; simp [schurM]
  · have h' : (c : Fin N) ≠ b := fun e => h (Subtype.ext e)
    simp [schurM, h, h']

/-- The entry `(a, b)` of `G_{SS} M^S = 1`, for `a ∈ S`. -/
private theorem schur_XI_apply (hA : A.IsHermitian) (hz : 0 < z.im) {S : Finset (Fin N)}
    {a b : Fin N} (ha : a ∈ S) :
    ∑ m ∈ S, green A z a m * (schurB A z - schurB A z * greenT A S z * schurB A z) m b =
      if a = b then 1 else 0 := by
  have h := congrFun (congrFun (schur_XI hA hz S) a) b
  rw [Matrix.mul_apply] at h
  simp only [schurP, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply,
    ite_eq_left ha, one_mul] at h
  rw [← h, ← Finset.sum_subset (Finset.subset_univ S)]
  · exact Finset.sum_congr rfl fun m hm => by simp [hm]
  · intro m _ hm
    simp [hm]

/-- (BI) for `S = {t}`, row `k ≠ t`: `G_kl = G^{(t)}_kl - (G^{(t)} B)_kt G_tl`. -/
private theorem schur_left_single (hA : A.IsHermitian) (hz : 0 < z.im) {t k : Fin N}
    (hk : k ≠ t) (l : Fin N) :
    green A z k l = greenT A {t} z k l - (greenT A {t} z * schurB A z) k t * green A z t l := by
  have h := congrFun (congrFun (schur_left hA hz {t}) k) l
  have hk' : k ∉ ({t} : Finset (Fin N)) := by simpa using hk
  rw [schurQ, Matrix.diagonal_mul, ite_eq_right hk', one_mul, Matrix.sub_apply] at h
  rw [h]
  congr 1
  rw [Matrix.mul_apply]
  simp [schurP, Matrix.mul_diagonal]

/-- (BI) for `S = {t}`, column `l ≠ t`: `G_kl = G^{(t)}_kl - G_kt (B G^{(t)})_tl`. -/
private theorem schur_right_single (hA : A.IsHermitian) (hz : 0 < z.im) {t l : Fin N}
    (hl : l ≠ t) (k : Fin N) :
    green A z k l = greenT A {t} z k l - green A z k t * (schurB A z * greenT A {t} z) t l := by
  have h := congrFun (congrFun (schur_right hA hz {t}) k) l
  have hl' : l ∉ ({t} : Finset (Fin N)) := by simpa using hl
  rw [schurQ, Matrix.mul_diagonal, ite_eq_right hl', mul_one, Matrix.sub_apply] at h
  rw [h]
  congr 1
  rw [Matrix.mul_assoc (green A z * schurP {t}), Matrix.mul_apply]
  simp [schurP, Matrix.mul_diagonal]

/-- (BI) relative to a minor, row `k ∉ S ∪ t`:
`G^{(S)}_kl = G^{(S ∪ t)}_kl - (G^{(S ∪ t)} B)_kt G^{(S)}_tl`. -/
private theorem schur_insert_apply (hA : A.IsHermitian) (hz : 0 < z.im) {S : Finset (Fin N)}
    {t k : Fin N} (ht : t ∉ S) (hk : k ∉ insert t S) (l : Fin N) :
    greenT A S z k l = greenT A (insert t S) z k l -
      (greenT A (insert t S) z * schurB A z) k t * greenT A S z t l := by
  have h := congrFun (congrFun (schur_insert hA hz ht) k) l
  rw [schurQ, Matrix.diagonal_mul, ite_eq_right hk, one_mul, Matrix.sub_apply] at h
  rw [h]
  congr 1
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

/-- Lemma 3.5 (a) for the minor: `Im G^{(S)}_tt > 0` for `t ∉ S`. -/
private theorem schur_greenT_im_pos (hA : A.IsHermitian) (hz : 0 < z.im) {S : Finset (Fin N)}
    {t : Fin N} (ht : t ∉ S) : 0 < (greenT A S z t t).im := by
  rw [greenT_of_not_mem ht ht]
  exact green_im_diag_pos (A := minor A S) (hA.submatrix _) hz ⟨t, ht⟩

/-- Lemma 3.5 (b) for the minor: the Ward identity for `G^{(S)}` in row and column `t ∉ S`. -/
private theorem schur_ward_greenT (hA : A.IsHermitian) (hz : 0 < z.im) {S : Finset (Fin N)}
    {t : Fin N} (ht : t ∉ S) :
    ∑ k, ‖greenT A S z t k‖ ^ 2 = (greenT A S z t t).im / z.im ∧
      ∑ k, ‖greenT A S z k t‖ ^ 2 = (greenT A S z t t).im / z.im := by
  have hw := ward (A := minor A S) (hA.submatrix _) hz ⟨t, ht⟩
  have e1 : ∑ k, ‖greenT A S z t k‖ ^ 2 =
      ∑ k : {i // i ∉ S}, ‖greenMinor A S z ⟨t, ht⟩ k‖ ^ 2 := by
    rw [← schur_sum_dite S (fun k hk => ‖greenMinor A S z ⟨t, ht⟩ ⟨k, hk⟩‖ ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ S
    · simp [hk, greenT_of_mem_right hk]
    · simp [hk, greenT_of_not_mem ht hk]
  have e2 : ∑ k, ‖greenT A S z k t‖ ^ 2 =
      ∑ k : {i // i ∉ S}, ‖greenMinor A S z k ⟨t, ht⟩‖ ^ 2 := by
    rw [← schur_sum_dite S (fun k hk => ‖greenMinor A S z ⟨k, hk⟩ ⟨t, ht⟩‖ ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∈ S
    · simp [hk, greenT_of_mem_left hk]
    · simp [hk, greenT_of_not_mem hk ht]
  rw [e1, e2, greenT_of_not_mem ht ht]
  exact hw

/-- One step of (I5): `|tr G^{(S)} - tr G^{(S ∪ t)}| ≤ η⁻¹` for `t ∉ S`. -/
private theorem schur_trace_step (hA : A.IsHermitian) (hz : 0 < z.im) {S : Finset (Fin N)}
    {t : Fin N} (ht : t ∉ S) :
    ‖∑ k, greenT A S z k k - ∑ k, greenT A (insert t S) z k k‖ ≤ 1 / z.im := by
  have htt : greenT A S z t t ≠ 0 := fun h => by
    have := schur_greenT_im_pos hA hz ht
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this
  have htS : t ∈ insert t S := Finset.mem_insert_self t S
  have hdiag : ∀ k, greenT A S z k k - greenT A (insert t S) z k k =
      greenT A S z t k * greenT A S z k t / greenT A S z t t := by
    intro k
    by_cases hkS : k ∈ S
    · rw [greenT_of_mem_left hkS, greenT_of_mem_left (Finset.mem_insert_of_mem hkS),
        greenT_of_mem_right hkS]
      simp
    by_cases hkt : k = t
    · subst hkt
      rw [greenT_of_mem_left htS, sub_zero, mul_div_assoc, div_self htt, mul_one]
    have hk : k ∉ insert t S := by simp [hkS, hkt]
    have h1 := schur_insert_apply hA hz ht hk k
    have h2 := schur_insert_apply hA hz ht hk t
    rw [greenT_of_mem_right htS] at h2
    rw [eq_div_iff htt]
    linear_combination greenT A S z t t * h1 - greenT A S z t k * h2
  have hw := schur_ward_greenT hA hz ht
  have hsum : ‖∑ k, greenT A S z t k * greenT A S z k t‖ ≤ (greenT A S z t t).im / z.im := by
    calc ‖∑ k, greenT A S z t k * greenT A S z k t‖
        ≤ ∑ k, ‖greenT A S z t k‖ * ‖greenT A S z k t‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp
      _ ≤ ∑ k, (‖greenT A S z t k‖ ^ 2 + ‖greenT A S z k t‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun k _ => by
            nlinarith [two_mul_le_add_sq ‖greenT A S z t k‖ ‖greenT A S z k t‖]
      _ = ((greenT A S z t t).im / z.im + (greenT A S z t t).im / z.im) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hw.1, hw.2]
      _ = (greenT A S z t t).im / z.im := by ring
  have him : (greenT A S z t t).im ≤ ‖greenT A S z t t‖ := Complex.im_le_norm _
  have hpos : 0 < ‖greenT A S z t t‖ := norm_pos_iff.mpr htt
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k _ => hdiag k, ← Finset.sum_div,
    norm_div, div_le_iff₀ hpos]
  calc ‖∑ k, greenT A S z t k * greenT A S z k t‖ ≤ (greenT A S z t t).im / z.im := hsum
    _ ≤ ‖greenT A S z t t‖ / z.im := div_le_div_of_nonneg_right him hz.le
    _ = 1 / z.im * ‖greenT A S z t t‖ := by ring

/-- (I5) for traces: `|tr G - tr G^{(S)}| ≤ |S| / η`. -/
private theorem schur_trace_le (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    ‖∑ k, green A z k k - ∑ k, greenT A S z k k‖ ≤ S.card / z.im := by
  induction S using Finset.induction_on with
  | empty => rw [greenT_empty hA hz]; simp
  | insert t S ht ih =>
    rw [Finset.card_insert_of_notMem ht]
    calc ‖∑ k, green A z k k - ∑ k, greenT A (insert t S) z k k‖
        ≤ ‖∑ k, green A z k k - ∑ k, greenT A S z k k‖ +
          ‖∑ k, greenT A S z k k - ∑ k, greenT A (insert t S) z k k‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ S.card / z.im + 1 / z.im := add_le_add ih (schur_trace_step hA hz ht)
      _ = ((S.card + 1 : ℕ) : ℝ) / z.im := by push_cast; ring

end Helpers

/-- Lemma 3.6: `(G_ab)_{a,b ∈ S} = (M^S)⁻¹`. -/
theorem schur_block {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (S : Finset (Fin N)) :
    IsUnit (schurM A S z) ∧ (Matrix.of fun a b : S => green A z a b) = (schurM A S z)⁻¹ := by
  have hXM : (Matrix.of fun a b : S => green A z a b) * schurM A S z = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    have h := schur_XI_apply hA hz (b := (b : Fin N)) a.2
    rw [← Finset.sum_coe_sort] at h
    simp only [Matrix.of_apply, schurM_apply]
    rw [h, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · have h' : (a : Fin N) ≠ b := fun e => hab (Subtype.ext e)
      simp [hab, h']
  exact ⟨⟨⟨schurM A S z, _, mul_eq_one_comm.mp hXM, hXM⟩, rfl⟩,
    (Matrix.inv_eq_left_inv hXM).symm⟩

/-- Lemma 3.6 (I1). -/
theorem inv_green_diag {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (i : Fin N) :
    1 / green A z i i =
      toC (A i i) - z - ∑ k, ∑ l, toC (A i k) * greenT A {i} z k l * toC (A l i) := by
  have hi : i ∈ ({i} : Finset (Fin N)) := Finset.mem_singleton_self i
  have h := schur_XI_apply hA hz (b := i) hi
  rw [Finset.sum_singleton, ite_eq_left rfl, Matrix.sub_apply, schur_BTB_apply hi hi, schurB_apply,
    ite_eq_left rfl] at h
  rw [one_div]
  exact inv_eq_of_mul_eq_one_right h

/-- Lemma 3.6 (I2). -/
theorem green_offdiag {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {i j : Fin N} (hij : i ≠ j) :
    green A z i j = -green A z i i * ∑ k, toC (A i k) * greenT A {i} z k j ∧
      green A z i j = -green A z i i * greenT A {i} z j j *
        (toC (A i j) - ∑ k, ∑ l, toC (A i k) * greenT A {i, j} z k l * toC (A l j)) ∧
      green A z j i = -green A z i i * ∑ k, greenT A {i} z j k * toC (A k i) := by
  have hi : i ∈ ({i} : Finset (Fin N)) := Finset.mem_singleton_self i
  have e1 : green A z i j = -green A z i i * ∑ k, toC (A i k) * greenT A {i} z k j := by
    rw [schur_right_single hA hz (Ne.symm hij) i, greenT_of_mem_left hi,
      schur_B_greenT_apply hi]
    ring
  have hji : j ∉ ({i} : Finset (Fin N)) := by simpa using Ne.symm hij
  have hjS : j ∈ insert j ({i} : Finset (Fin N)) := Finset.mem_insert_self j {i}
  have hkey : ∀ k, toC (A i k) * greenT A {i} z k j = greenT A {i} z j j *
      (toC (A i j) * (if k = j then 1 else 0) -
        ∑ l, toC (A i k) * greenT A (insert j {i}) z k l * toC (A l j)) := by
    intro k
    by_cases hki : k = i
    · subst hki
      rw [greenT_of_mem_left hi, ite_eq_right hij]
      simp [greenT_of_mem_left (Finset.mem_insert_of_mem hi)]
    by_cases hkj : k = j
    · subst hkj
      simp [greenT_of_mem_left hjS]
      ring
    have hk : k ∉ insert j ({i} : Finset (Fin N)) := by simp [hki, hkj]
    have h := schur_insert_apply hA hz hji hk j
    rw [greenT_of_mem_right hjS, zero_sub, schur_greenT_B_apply hjS] at h
    rw [h, ite_eq_right hkj, mul_zero, zero_sub]
    simp_rw [mul_assoc (toC (A i k))]
    rw [← Finset.mul_sum]
    ring
  have e2 : ∑ k, toC (A i k) * greenT A {i} z k j = greenT A {i} z j j *
      (toC (A i j) - ∑ k, ∑ l, toC (A i k) * greenT A {i, j} z k l * toC (A l j)) := by
    rw [Finset.sum_congr rfl fun k _ => hkey k, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.pair_comm]
    simp
  refine ⟨e1, ?_, ?_⟩
  · rw [e1, e2]
    ring
  · rw [schur_left_single hA hz (Ne.symm hij) i, greenT_of_mem_right hi,
      schur_greenT_B_apply hi]
    ring

/-- Lemma 3.6 (I3) for one removed index. -/
theorem greenT_single {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {k i j : Fin N} (hi : i ≠ k) (hj : j ≠ k) :
    greenT A {k} z i j = green A z i j - green A z i k * green A z k j / green A z k k := by
  have _ := hj
  have hk : k ∈ ({k} : Finset (Fin N)) := Finset.mem_singleton_self k
  have hkk : green A z k k ≠ 0 := fun h => by
    have := green_im_diag_pos hA hz k
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this
  have h1 := schur_left_single hA hz hi j
  have h2 := schur_left_single hA hz hi k
  rw [greenT_of_mem_right hk] at h2
  rw [h2, h1]
  field_simp
  ring

/-- Lemma 3.6 (I5). -/
theorem norm_stieltjesT_sub_le {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) :
    ‖stieltjesT A T z - stieltjesEmp A z‖ ≤ T.card / (N * z.im) := by
  have h := schur_trace_le hA hz T
  have e : stieltjesT A T z - stieltjesEmp A z =
      -((N : ℂ)⁻¹ * (∑ k, green A z k k - ∑ k, greenT A T z k k)) := by
    simp only [stieltjesT, stieltjesEmp, Fintype.card_fin, Matrix.trace, Matrix.diag]
    ring
  rw [e, norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ)⁻¹ * ‖∑ k, green A z k k - ∑ k, greenT A T z k k‖
        ≤ (N : ℝ)⁻¹ * (T.card / z.im) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = T.card / (N * z.im) := by field_simp

end Rigidity
