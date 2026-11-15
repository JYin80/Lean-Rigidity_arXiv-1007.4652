import Rigidity.Resolvent.Basic
import Rigidity.Resolvent.Schur

/-!
# Block Schur complement: the inverse of the `A`-block and the perturbation of minors

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `H` over `ℝ` or `ℂ` (a field `𝕜` with `RCLike 𝕜`), `η = Im z > 0`, the
Green function `G = (H - z)⁻¹`, its minors `G^{(T)}` (Definition 3.1) and the matrices `M^S` of
(3.5), this file proves the remaining items of Lemma 3.6 and Lemma 3.7:
* (I3): for `S ≠ {1, …, N}` the block `G_SS` is invertible and
  `G^{(S)}_ij = G_ij - ∑_{a,b ∈ S} G_ia (G_SS⁻¹)_ab G_bj` for `i, j ∉ S` (`greenT_eq_block`);
* (I4) and (3.5): for `k ∈ S` with `S' = S ∖ {k}` nonempty, `M^S_{S'S'}` is invertible with inverse
  `(G^{(k)}_ab)_{a,b ∈ S'}`, and `1 / G_kk = M^S_kk - ∑_{a,b ∈ S'} M^S_ka G^{(k)}_ab M^S_bk`
  (`inv_green_eq_schurM`);
* Remark 3.1 (ii): `M^S_aa = 1 / G^{(S ∖ {a})}_aa` for `a ∈ S` (`schurM_diag_eq`);
* Lemma 3.7: if `|G_aa| ≥ g` on `S` and the off-diagonal entries of `G_SS` are at most
  `g / (2 |S|)`, then `|G^{(S)}_ij - G_ij| ≤ (2 |S|² / g) max_a |G_ia| max_b |G_bj|`
  (`norm_greenT_sub_le`).

The proofs use the block inverse formula (BI) of Lemma 3.6 in the following form.  If an invertible
matrix `𝓜` with inverse `𝓝` is partitioned into blocks `[[P, Q], [R, S]]` and
`[[X, Y], [Z, W]]`, then `P` invertible gives `(S - R P⁻¹ Q) W = 1`, and `S` invertible gives
`(P - Q S⁻¹ R) X = 1`.  It is applied to `G` and `H - z` (partitioned into `S` and its
complement), and to `G_SS` and `M^S` (partitioned into `{k}` and `S ∖ {k}`).

-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-! ### The block inverse formula -/

section Blocks

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq α] [DecidableEq β]
  [DecidableEq ι]

/-- The four block equations of `𝓜 𝓝 = 1`. -/
private theorem minor_four_eqs {P X : Matrix α α ℂ} {Q Y : Matrix α β ℂ} {R Z : Matrix β α ℂ}
    {S W : Matrix β β ℂ} (h : Matrix.fromBlocks P Q R S * Matrix.fromBlocks X Y Z W = 1) :
    P * X + Q * Z = 1 ∧ P * Y + Q * W = 0 ∧ R * X + S * Z = 0 ∧ R * Y + S * W = 1 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h
  exact Matrix.fromBlocks_inj.mp h

/-- (BI) when the block `P` is invertible: `(S - R P⁻¹ Q) W = 1`. -/
private theorem minor_pivot_left {P X : Matrix α α ℂ} {Q Y : Matrix α β ℂ} {R Z : Matrix β α ℂ}
    {S W : Matrix β β ℂ} (h : Matrix.fromBlocks P Q R S * Matrix.fromBlocks X Y Z W = 1)
    (hP : IsUnit P) : (S - R * P⁻¹ * Q) * W = 1 := by
  obtain ⟨-, h2, -, h4⟩ := minor_four_eqs h
  have hdet := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hY : Y = -(P⁻¹ * (Q * W)) := by
    calc Y = P⁻¹ * (P * Y) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = -(P⁻¹ * (Q * W)) := by rw [eq_neg_of_add_eq_zero_left h2, Matrix.mul_neg]
  rw [hY] at h4
  rw [← h4]
  simp only [sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- (BI) when the block `S` is invertible: `(P - Q S⁻¹ R) X = 1`. -/
private theorem minor_pivot_right {P X : Matrix α α ℂ} {Q Y : Matrix α β ℂ} {R Z : Matrix β α ℂ}
    {S W : Matrix β β ℂ} (h : Matrix.fromBlocks P Q R S * Matrix.fromBlocks X Y Z W = 1)
    (hS : IsUnit S) : (P - Q * S⁻¹ * R) * X = 1 := by
  obtain ⟨h1, -, h3, -⟩ := minor_four_eqs h
  have hdet := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hZ : Z = -(S⁻¹ * (R * X)) := by
    calc Z = S⁻¹ * (S * Z) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = -(S⁻¹ * (R * X)) := by rw [eq_neg_of_add_eq_zero_right h3, Matrix.mul_neg]
  rw [hZ] at h1
  rw [← h1]
  simp only [sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- The block form of `M N = 1` for a partition of the index type `ι` into `α ⊕ β`. -/
private theorem minor_block_mul (e : α ⊕ β ≃ ι) {M N : Matrix ι ι ℂ} (h : M * N = 1) :
    Matrix.fromBlocks (M.submatrix e e).toBlocks₁₁ (M.submatrix e e).toBlocks₁₂
        (M.submatrix e e).toBlocks₂₁ (M.submatrix e e).toBlocks₂₂ *
      Matrix.fromBlocks (N.submatrix e e).toBlocks₁₁ (N.submatrix e e).toBlocks₁₂
        (N.submatrix e e).toBlocks₂₁ (N.submatrix e e).toBlocks₂₂ = 1 := by
  rw [Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks, Matrix.submatrix_mul_equiv, h,
    Matrix.submatrix_one_equiv]

end Blocks

/-! ### The partitions used below -/

section Split

variable {N : ℕ}

/-- The partition of the indices `Fin N` into `S` and its complement. -/
private abbrev minorSumCompl (S : Finset (Fin N)) : ↥S ⊕ {i // i ∉ S} ≃ Fin N :=
  Equiv.sumCompl (· ∈ S)

/-- The partition of the index set `S` into `{k}` and `S ∖ {k}`. -/
private def minorSplit (S : Finset (Fin N)) (k : Fin N) (hk : k ∈ S) :
    Unit ⊕ ↥(S.erase k) ≃ ↥S where
  toFun := Sum.elim (fun _ => ⟨k, hk⟩) (fun b => ⟨b.1, Finset.mem_of_mem_erase b.2⟩)
  invFun x := if h : x.1 = k then Sum.inl () else Sum.inr ⟨x.1, Finset.mem_erase.2 ⟨h, x.2⟩⟩
  left_inv := by
    rintro (u | b)
    · simp
    · have h : b.1 ≠ k := (Finset.mem_erase.1 b.2).1
      simp [h]
  right_inv x := by
    by_cases h : x.1 = k
    · have hx : x = ⟨k, hk⟩ := Subtype.ext h
      subst hx
      simp
    · simp [h]

private theorem minorSplit_inl (S : Finset (Fin N)) (k : Fin N) (hk : k ∈ S) (u : Unit) :
    minorSplit S k hk (Sum.inl u) = ⟨k, hk⟩ := rfl

private theorem minorSplit_inr (S : Finset (Fin N)) (k : Fin N) (hk : k ∈ S) (b : ↥(S.erase k)) :
    minorSplit S k hk (Sum.inr b) = ⟨b.1, Finset.mem_of_mem_erase b.2⟩ := rfl

/-- A `1 × 1` matrix with nonzero entry is invertible. -/
private theorem minor_isUnit_unit {P : Matrix Unit Unit ℂ} (h : P () () ≠ 0) : IsUnit P := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
  exact isUnit_iff_ne_zero.mpr h

/-- The inverse of a `1 × 1` matrix with nonzero entry. -/
private theorem minor_inv_unit {P : Matrix Unit Unit ℂ} (h : P () () ≠ 0) :
    P⁻¹ = Matrix.of fun _ _ => (P () ())⁻¹ := by
  apply Matrix.inv_eq_right_inv
  ext i j
  simp [Matrix.mul_apply, h]

end Split

/-! ### Lemma 3.6 (I3), (I4) and Remark 3.1 (ii) -/

section Main

variable {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} {z : ℂ}

/-- `G (H - z) = 1`. -/
private theorem minor_green_B (hA : A.IsHermitian) (hz : 0 < z.im) :
    green A z * (A.map toC - z • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero (isHermitian_map_toC hA) hz.ne'))

/-- The block of `H - z` on the complement of `S` is `H^{(S)} - z`. -/
private theorem minor_B_sub (A : Matrix (Fin N) (Fin N) 𝕜) (S : Finset (Fin N)) (z : ℂ) :
    ((A.map toC - z • (1 : Matrix (Fin N) (Fin N) ℂ)).submatrix (minorSumCompl S)
      (minorSumCompl S)).toBlocks₂₂ =
      (minor A S).map toC - z • (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.toBlocks₂₂, minor]
  · have h' : (i : Fin N) ≠ j := fun e => h (Subtype.ext e)
    simp [Matrix.toBlocks₂₂, minor, Matrix.one_apply_ne h, h']

/-- `G_SS M^S = 1` and `M^S G_SS = 1`. -/
private theorem minor_G_M (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N)) :
    (Matrix.of fun a b : S => green A z a b) * schurM A S z = 1 ∧
      schurM A S z * (Matrix.of fun a b : S => green A z a b) = 1 := by
  obtain ⟨hU, hG⟩ := schur_block hA hz S
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hU
  rw [hG]
  exact ⟨Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet⟩

/-- The diagonal entries of `G` are nonzero. -/
private theorem minor_green_diag_ne (hA : A.IsHermitian) (hz : 0 < z.im) (k : Fin N) :
    green A z k k ≠ 0 := fun h => by
  have := green_im_diag_pos hA hz k
  rw [h, Complex.zero_im] at this
  exact lt_irrefl _ this

/-- Lemma 3.6 (I3): for `S ≠ {1, …, N}` the block `G_SS` is invertible and, for `i, j ∉ S`,
`G^{(S)}_ij = G_ij - ∑_{a,b ∈ S} G_ia (G_SS⁻¹)_ab G_bj`.  The identity needs no assumption
`S ≠ ∅`: for `S = ∅` both sums are empty and `G^{(∅)} = G`. -/
theorem greenT_eq_block (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N))
    (hS : S ≠ Finset.univ) :
    IsUnit (Matrix.of fun a b : S => green A z a b) ∧
      ∀ i j : Fin N, i ∉ S → j ∉ S →
        greenT A S z i j = green A z i j -
          ∑ a : S, ∑ b : S, green A z i a * (Matrix.of fun a b : S => green A z a b)⁻¹ a b *
            green A z b j := by
  have _ := hS
  have hU : IsUnit (Matrix.of fun a b : S => green A z a b) := by
    rw [(schur_block hA hz S).2]
    exact Matrix.isUnit_nonsing_inv_iff.mpr (schur_block hA hz S).1
  refine ⟨hU, fun i j hi hj => ?_⟩
  have h := minor_block_mul (minorSumCompl S) (minor_green_B hA hz)
  have hP : IsUnit (((green A z).submatrix (minorSumCompl S) (minorSumCompl S)).toBlocks₁₁) := hU
  have key := minor_pivot_left h hP
  rw [minor_B_sub] at key
  have hinv : greenMinor A S z =
      ((green A z).submatrix (minorSumCompl S) (minorSumCompl S)).toBlocks₂₂ -
        ((green A z).submatrix (minorSumCompl S) (minorSumCompl S)).toBlocks₂₁ *
        ((green A z).submatrix (minorSumCompl S) (minorSumCompl S)).toBlocks₁₁⁻¹ *
        ((green A z).submatrix (minorSumCompl S) (minorSumCompl S)).toBlocks₁₂ :=
    Matrix.inv_eq_left_inv key
  have hij := congrFun (congrFun hinv ⟨i, hi⟩) ⟨j, hj⟩
  have hg : greenT A S z i j = greenMinor A S z ⟨i, hi⟩ ⟨j, hj⟩ := by simp [greenT, hi, hj]
  have hP11 : ((green A z).submatrix (minorSumCompl S) (minorSumCompl S)).toBlocks₁₁ =
      Matrix.of fun a b : S => green A z a b := rfl
  rw [hg, hij, hP11]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- Lemma 3.6 (I4), (3.5): for `k ∈ S` with `S' = S ∖ {k}` nonempty, the matrix
`M^S_{S'S'} = (M^S_ab)_{a,b ∈ S'}` is invertible with inverse `(G^{(k)}_ab)_{a,b ∈ S'}`, and
`1 / G_kk = M^S_kk - ∑_{a,b ∈ S'} M^S_ka G^{(k)}_ab M^S_bk`. -/
theorem inv_green_eq_schurM (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N))
    {k : Fin N} (hk : k ∈ S) (hS' : (S.erase k).Nonempty) :
    IsUnit (Matrix.of fun a b : S.erase k =>
        schurM A S z ⟨a, Finset.mem_of_mem_erase a.2⟩ ⟨b, Finset.mem_of_mem_erase b.2⟩) ∧
      (Matrix.of fun a b : S.erase k =>
        schurM A S z ⟨a, Finset.mem_of_mem_erase a.2⟩ ⟨b, Finset.mem_of_mem_erase b.2⟩)⁻¹ =
        (Matrix.of fun a b : S.erase k => greenT A {k} z a b) ∧
      1 / green A z k k = schurM A S z ⟨k, hk⟩ ⟨k, hk⟩ -
        ∑ a : S.erase k, ∑ b : S.erase k, schurM A S z ⟨k, hk⟩ ⟨a, Finset.mem_of_mem_erase a.2⟩ *
          greenT A {k} z a b * schurM A S z ⟨b, Finset.mem_of_mem_erase b.2⟩ ⟨k, hk⟩ := by
  have _ := hS'
  obtain ⟨hGM, hMG⟩ := minor_G_M hA hz S
  have hkk := minor_green_diag_ne hA hz k
  have h1 := minor_block_mul (minorSplit S k hk) hGM
  have hP : IsUnit (((Matrix.of fun a b : S => green A z a b).submatrix (minorSplit S k hk)
      (minorSplit S k hk)).toBlocks₁₁) := minor_isUnit_unit hkk
  have key1 := minor_pivot_left h1 hP
  have hC : ((Matrix.of fun a b : S => green A z a b).submatrix (minorSplit S k hk)
        (minorSplit S k hk)).toBlocks₂₂ -
      ((Matrix.of fun a b : S => green A z a b).submatrix (minorSplit S k hk)
        (minorSplit S k hk)).toBlocks₂₁ *
      ((Matrix.of fun a b : S => green A z a b).submatrix (minorSplit S k hk)
        (minorSplit S k hk)).toBlocks₁₁⁻¹ *
      ((Matrix.of fun a b : S => green A z a b).submatrix (minorSplit S k hk)
        (minorSplit S k hk)).toBlocks₁₂ =
      Matrix.of fun a b : S.erase k => greenT A {k} z a b := by
    rw [minor_inv_unit hkk]
    ext a b
    have ha : (a : Fin N) ≠ k := (Finset.mem_erase.1 a.2).1
    have hb : (b : Fin N) ≠ k := (Finset.mem_erase.1 b.2).1
    rw [Matrix.of_apply, greenT_single hA hz ha hb]
    simp [Matrix.mul_apply, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₁₁, minorSplit_inl, minorSplit_inr, div_eq_mul_inv]
    ring
  rw [hC] at key1
  have hM22 : ((schurM A S z).submatrix (minorSplit S k hk) (minorSplit S k hk)).toBlocks₂₂ =
      Matrix.of fun a b : S.erase k =>
        schurM A S z ⟨a, Finset.mem_of_mem_erase a.2⟩ ⟨b, Finset.mem_of_mem_erase b.2⟩ := rfl
  rw [hM22] at key1
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse key1)
  have hinv := Matrix.inv_eq_left_inv key1
  refine ⟨hunit, hinv, ?_⟩
  have h2 := minor_block_mul (minorSplit S k hk) hMG
  rw [← hM22] at hunit
  have key2 := minor_pivot_right h2 hunit
  rw [hM22, hinv] at key2
  have h3 := congrFun (congrFun key2 ()) ()
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq] at h3
  refine (eq_one_div_of_mul_eq_one_left h3).symm.trans ?_
  refine congrArg (schurM A S z ⟨k, hk⟩ ⟨k, hk⟩ - ·) ?_
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

/-- Remark 3.1 (ii), the last assertion of Lemma 3.6 (I4): `M^S_aa = 1 / G^{(S ∖ {a})}_aa` for
`a ∈ S`.  For `S = {a}` this is (I1), with the convention `G^{(∅)} = G`. -/
theorem schurM_diag_eq (hA : A.IsHermitian) (hz : 0 < z.im) (S : Finset (Fin N))
    {a : Fin N} (ha : a ∈ S) :
    schurM A S z ⟨a, ha⟩ ⟨a, ha⟩ = 1 / greenT A (S.erase a) z a a := by
  have hGM := (minor_G_M hA hz S).1
  have haT : a ∉ S.erase a := Finset.notMem_erase a S
  have hTu : S.erase a ≠ Finset.univ := fun h => haT (h ▸ Finset.mem_univ a)
  obtain ⟨hU, hform⟩ := greenT_eq_block hA hz (S.erase a) hTu
  have h1 := minor_block_mul (minorSplit S a ha) hGM
  have hP : IsUnit (((Matrix.of fun x y : S => green A z x y).submatrix (minorSplit S a ha)
      (minorSplit S a ha)).toBlocks₂₂) := hU
  have key := minor_pivot_right h1 hP
  have h3 := congrFun (congrFun key ()) ()
  have hform' := hform a a haT haT
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq] at h3
  rw [hform']
  refine eq_one_div_of_mul_eq_one_right ?_
  refine Eq.trans (congrArg₂ (· * ·) (congrArg (green A z a a - ·) ?_) rfl) h3
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

end Main

/-! ### Lemma 3.7 -/

/-- Lemma 3.7: perturbation of minors. -/
theorem norm_greenT_sub_le {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) {S : Finset (Fin N)} (hS : S.Nonempty) {g : ℝ} (hg : 0 < g)
    (hdiag : ∀ a ∈ S, g ≤ ‖green A z a a‖)
    (hoff : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ‖green A z a b‖ ≤ g / (2 * S.card)) {i j : Fin N}
    (hi : i ∉ S) (hj : j ∉ S) :
    ‖greenT A S z i j - green A z i j‖ ≤
      2 * S.card ^ 2 / g * (⨆ a : S, ‖green A z i a‖) * (⨆ b : S, ‖green A z b j‖) := by
  have hSu : S ≠ Finset.univ := fun h => hi (h ▸ Finset.mem_univ i)
  obtain ⟨hU, hform⟩ := greenT_eq_block hA hz S hSu
  have : Nonempty S := hS.to_subtype
  have hr : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hGX : (Matrix.of fun a b : S => green A z a b) * (Matrix.of fun a b : S => green A z a b)⁻¹ =
      1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  set X := (Matrix.of fun a b : S => green A z a b)⁻¹ with hX
  have hXb : ∀ a b : S, ‖X a b‖ ≤ 2 / g := by
    obtain ⟨⟨a, b⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (S × S))
      (fun p : S × S => ‖X p.1 p.2‖) Finset.univ_nonempty
    have hμ : ‖X a b‖ ≤ 2 / g := by
      have h := congrFun (congrFun hGX a) b
      rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), Matrix.of_apply] at h
      have hn : (((Finset.univ : Finset S).erase a).card : ℝ) + 1 = S.card := by
        have := Finset.card_erase_add_one (Finset.mem_univ a)
        rw [Finset.card_univ, Fintype.card_coe] at this
        exact_mod_cast this
      have hs : ‖∑ c ∈ (Finset.univ : Finset S).erase a, green A z a c * X c b‖ ≤
          ((Finset.univ : Finset S).erase a).card * (g / (2 * S.card) * ‖X a b‖) := by
        refine (norm_sum_le _ _).trans ?_
        rw [← nsmul_eq_mul]
        refine (Finset.sum_le_card_nsmul _ _ _ fun c hc => ?_)
        rw [norm_mul]
        have hca : (a : Fin N) ≠ c := fun e => (Finset.mem_erase.1 hc).1 (Subtype.ext e).symm
        exact mul_le_mul (hoff a a.2 c c.2 hca) (hmax (c, b) (Finset.mem_univ _)) (norm_nonneg _)
          (by positivity)
      have h1 : ‖green A z a a * X a b‖ ≤ 1 + ((Finset.univ : Finset S).erase a).card *
          (g / (2 * S.card) * ‖X a b‖) := by
        rw [eq_sub_of_add_eq h]
        refine (norm_sub_le _ _).trans (add_le_add ?_ hs)
        rw [Matrix.one_apply]
        split_ifs <;> simp
      have h2 : g * ‖X a b‖ ≤ ‖green A z a a * X a b‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hdiag a a.2) (norm_nonneg _)
      have h3 : (((Finset.univ : Finset S).erase a).card : ℝ) * (g / (2 * S.card)) ≤ g / 2 := by
        have : (((Finset.univ : Finset S).erase a).card : ℝ) * (g / (2 * S.card)) =
            g / 2 * ((((Finset.univ : Finset S).erase a).card : ℝ) / S.card) := by
          field_simp
        rw [this]
        have : ((((Finset.univ : Finset S).erase a).card : ℝ) / S.card) ≤ 1 :=
          (div_le_one hr).mpr (by linarith)
        have hg2 : 0 ≤ g / 2 := by positivity
        calc g / 2 * ((((Finset.univ : Finset S).erase a).card : ℝ) / S.card) ≤ g / 2 * 1 :=
              mul_le_mul_of_nonneg_left this hg2
          _ = g / 2 := mul_one _
      rw [le_div_iff₀ hg]
      have hμ0 : 0 ≤ ‖X a b‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right h3 hμ0]
    exact fun a' b' => (hmax (a', b') (Finset.mem_univ _)).trans hμ
  have hdiffeq : greenT A S z i j - green A z i j =
      -∑ a : S, ∑ b : S, green A z i a * X a b * green A z b j := by
    rw [hform i j hi hj]; ring
  have hs1 : ∀ a : S, ‖green A z i a‖ ≤ ⨆ a : S, ‖green A z i a‖ :=
    fun a => le_ciSup (Finite.bddAbove_range fun a : S => ‖green A z i a‖) a
  have hs2 : ∀ b : S, ‖green A z b j‖ ≤ ⨆ b : S, ‖green A z b j‖ :=
    fun b => le_ciSup (Finite.bddAbove_range fun b : S => ‖green A z b j‖) b
  obtain ⟨a₀⟩ := ‹Nonempty S›
  have hs10 : 0 ≤ ⨆ a : S, ‖green A z i a‖ := (norm_nonneg _).trans (hs1 a₀)
  have hs20 : 0 ≤ ⨆ b : S, ‖green A z b j‖ := (norm_nonneg _).trans (hs2 a₀)
  have hsum1 : ∑ a : S, ‖green A z i a‖ ≤ S.card * ⨆ a : S, ‖green A z i a‖ := by
    calc ∑ a : S, ‖green A z i a‖ ≤ ∑ _a : S, ⨆ a : S, ‖green A z i a‖ :=
          Finset.sum_le_sum fun a _ => hs1 a
      _ = S.card * ⨆ a : S, ‖green A z i a‖ := by simp
  have hsum2 : ∑ b : S, ‖green A z b j‖ ≤ S.card * ⨆ b : S, ‖green A z b j‖ := by
    calc ∑ b : S, ‖green A z b j‖ ≤ ∑ _b : S, ⨆ b : S, ‖green A z b j‖ :=
          Finset.sum_le_sum fun b _ => hs2 b
      _ = S.card * ⨆ b : S, ‖green A z b j‖ := by simp
  rw [hdiffeq, norm_neg]
  calc ‖∑ a : S, ∑ b : S, green A z i a * X a b * green A z b j‖
      ≤ ∑ a : S, ∑ b : S, ‖green A z i a * X a b * green A z b j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : S, ∑ b : S, 2 / g * (‖green A z i a‖ * ‖green A z b j‖) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul_of_nonneg_left (hXb a b)
          (mul_nonneg (norm_nonneg (green A z i a)) (norm_nonneg (green A z b j)))
        nlinarith [this]
    _ = 2 / g * ((∑ a : S, ‖green A z i a‖) * ∑ b : S, ‖green A z b j‖) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 2 / g * ((S.card * ⨆ a : S, ‖green A z i a‖) * (S.card * ⨆ b : S, ‖green A z b j‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hsum1 hsum2 (Finset.sum_nonneg fun b _ => norm_nonneg _)
            (mul_nonneg hr.le hs10)) (by positivity)
    _ = 2 * S.card ^ 2 / g * (⨆ a : S, ‖green A z i a‖) * (⨆ b : S, ‖green A z b j‖) := by
        ring

end Rigidity
