import Rigidity.Resolvent.Basic
import Rigidity.Edge.EntryDet

/-!
# Complexified hybrid matrices and the bridge to the Green function

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a family of entries `x : Pair N → 𝕜` over `ℝ` or `ℂ`, `toMatrixC x` is the hermitian matrix
`H(x)` of (2.1) viewed as a complex matrix.  The file proves:
* `green (toMatrix x) z` is the resolvent of `toMatrixC x`;
* `toMatrix` is additive and odd, so `H(-x) = -H(x)`;
* Lemma 11.4 (ii) and Definition 11.3: `H(x) = H(x)^{[p]} + V_p(x_p)`, where `H(x)^{[p]}` is
  `H(x)` with the entry `p` set to `0`, equivalently `H - V_p(h_ab)`;
* the entry bound `|H(x)_{ab}| ≤ |x_p|` for a pair `p = (a, b)`;
* Lemma 11.4 (iii): `λ₁(H(x)) = -λ_N(H(-x))`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem hybrid_toC_star (y : 𝕜) : toC (star y) = star (toC y) := by
  apply Complex.ext <;> simp [toC]

private theorem hybrid_toC_zero : toC (0 : 𝕜) = 0 := by
  apply Complex.ext <;> simp [toC]

private theorem hybrid_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

private theorem hybrid_mk'_lt {N : ℕ} {i j : Fin N} (h : i < j) :
    Pair.mk' i j = ⟨(i, j), h.le⟩ := by
  simp [Pair.mk', h.le]

private theorem hybrid_mk'_gt {N : ℕ} {i j : Fin N} (h : j < i) :
    Pair.mk' i j = ⟨(j, i), h.le⟩ := by
  simp [Pair.mk', not_le.mpr h]

private theorem hybrid_mk'_self {N : ℕ} (i : Fin N) : Pair.mk' i i = ⟨(i, i), le_rfl⟩ := by
  simp [Pair.mk']

private theorem hybrid_eigAsc_congr {N : ℕ} {A B : Matrix (Fin N) (Fin N) 𝕜} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin N) : eigAsc hA k = eigAsc hB k := by
  subst h; rfl

/-- `H(x)` as a complex matrix. -/
noncomputable def toMatrixC {N : ℕ} (x : Pair N → 𝕜) : Matrix (Fin N) (Fin N) ℂ :=
  (toMatrix x).map toC

theorem toMatrixC_isHermitian {N : ℕ} (x : Pair N → 𝕜) : (toMatrixC x).IsHermitian :=
  isHermitian_map_toC (toMatrix_isHermitian x)

private theorem hybrid_toMatrixC_apply {N : ℕ} (x : Pair N → 𝕜) (i j : Fin N) :
    toMatrixC x i j = toC (toMatrix x i j) := rfl

theorem toMatrix_neg {N : ℕ} (x : Pair N → 𝕜) : toMatrix (-x) = -toMatrix x := by
  ext i j
  simp only [toMatrix, Matrix.neg_apply, Matrix.of_apply, Pi.neg_apply]
  split_ifs
  · rfl
  · rw [star_neg]
  · rw [map_neg, RCLike.ofReal_neg]

/-- `H(x) = H(x)^{[p]} + V_p(x_p)` (Lemma 11.4 (ii)). -/
theorem toMatrixC_eq_update_add {N : ℕ} (x : Pair N → 𝕜) (p : Pair N) :
    toMatrixC x = toMatrixC (Function.update x p 0) + entryMat p.1.1 p.1.2 (toC (x p)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  ext i j
  simp only [Matrix.add_apply, hybrid_toMatrixC_apply, toMatrix, Matrix.of_apply, entryMat]
  rcases (lt_trichotomy i j).imp_right Or.symm with h | h | heq
  · simp only [h, ite_true, not_lt_of_gt h, ite_false, hybrid_mk'_lt h, Function.update_apply]
    by_cases hp : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hp
      simp [h.ne, hybrid_toC_zero]
    · have h1 : ¬ (⟨(i, j), h.le⟩ : Pair N) = ⟨(a, b), hab⟩ := by simpa using hp
      simp only [h1, ↓reduceIte]
      by_cases hb : a = b
      · subst hb
        simp only [ite_true]
        have : ¬ (a = i ∧ a = j) := fun hh => h.ne (hh.1.symm.trans hh.2)
        simp [this]
      · simp only [hb, ite_false, Matrix.add_apply, Matrix.single_apply]
        have h2 : ¬ (a = i ∧ b = j) := fun hh => hp ⟨hh.1.symm, hh.2.symm⟩
        have h3 : ¬ (b = i ∧ a = j) := fun hh => by
          have hh1 : (a : Fin N) < b := lt_of_le_of_ne hab hb
          exact absurd (hh.1 ▸ hh.2 ▸ h) (not_lt.mpr hh1.le)
        simp [h2, h3]
  · simp only [h, not_lt_of_gt h, ite_true, ite_false, hybrid_mk'_gt h, Function.update_apply]
    by_cases hp : j = a ∧ i = b
    · obtain ⟨rfl, rfl⟩ := hp
      simp [h.ne, h.ne', hybrid_toC_zero]
      exact hybrid_toC_star (x ⟨(j, i), hab⟩)
    · have h1 : ¬ (⟨(j, i), h.le⟩ : Pair N) = ⟨(a, b), hab⟩ := by simpa using hp
      simp only [h1, ↓reduceIte]
      by_cases hb : a = b
      · subst hb
        simp only [ite_true]
        have : ¬ (a = i ∧ a = j) := fun hh => h.ne (hh.2.symm.trans hh.1)
        simp [this]
      · simp only [hb, ite_false, Matrix.add_apply, Matrix.single_apply]
        have hh1 : (a : Fin N) < b := lt_of_le_of_ne hab hb
        have h2 : ¬ (a = i ∧ b = j) := fun hh => by
          exact absurd (hh.1 ▸ hh.2 ▸ h) (not_lt.mpr hh1.le)
        have h3 : ¬ (b = i ∧ a = j) := fun hh => hp ⟨hh.2.symm, hh.1.symm⟩
        simp [h2, h3]
  · subst heq
    simp only [lt_irrefl, ite_false, hybrid_mk'_self, Function.update_apply]
    by_cases hp : i = a ∧ i = b
    · obtain ⟨rfl, rfl⟩ := hp
      apply Complex.ext <;> simp [toC]
    · have h1 : ¬ (⟨(i, i), le_rfl⟩ : Pair N) = ⟨(a, b), hab⟩ := by simpa using hp
      simp only [h1, ↓reduceIte]
      by_cases hb : a = b
      · subst hb
        simp only [ite_true]
        have : a ≠ i := fun e => hp ⟨e.symm, e.symm⟩
        simp [this]
      · simp only [hb, ite_false, Matrix.add_apply, Matrix.single_apply]
        have h2 : ¬ (a = i ∧ b = i) := fun hh => hp ⟨hh.1.symm, hh.2.symm⟩
        have h3 : ¬ (b = i ∧ a = i) := fun hh => hp ⟨hh.2.symm, hh.1.symm⟩
        simp [h2, h3]

/-- `H(x)^{[p]} = H - V_p(h_ab)` (Definition 11.3). -/
theorem toMatrixC_update_zero {N : ℕ} (x : Pair N → 𝕜) (p : Pair N) :
    toMatrixC (Function.update x p 0) =
      toMatrixC x - entryMat p.1.1 p.1.2 (toMatrixC x p.1.1 p.1.2) := by
  have key : entryMat p.1.1 p.1.2 (toMatrixC x p.1.1 p.1.2) =
      entryMat p.1.1 p.1.2 (toC (x p)) := by
    obtain ⟨⟨a, b⟩, hab⟩ := p
    rcases (show a ≤ b from hab).lt_or_eq with h | h
    · simp [hybrid_toMatrixC_apply, toMatrix, h, hybrid_mk'_lt h]
    · subst h
      simp [entryMat, hybrid_toMatrixC_apply, toMatrix, toC, hybrid_mk'_self]
  rw [key]
  exact eq_sub_of_add_eq (toMatrixC_eq_update_add x p).symm

theorem norm_toMatrixC_pair_le {N : ℕ} (x : Pair N → 𝕜) (p : Pair N) :
    ‖toMatrixC x p.1.1 p.1.2‖ ≤ ‖x p‖ := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  rw [hybrid_toMatrixC_apply, hybrid_norm_toC]
  rcases (show a ≤ b from hab).lt_or_eq with h | h
  · simp [toMatrix, h, hybrid_mk'_lt h]
  · subst h
    simp only [toMatrix, lt_irrefl, Matrix.of_apply, ite_false, hybrid_mk'_self]
    rw [RCLike.norm_ofReal]
    exact RCLike.abs_re_le_norm _

/-- `λ₁(H(x)) = -λ_N(H(-x))` (Lemma 11.4 (iii)). -/
theorem lamMin_eq_neg_lamMax_neg {N : ℕ} (x : Pair N → 𝕜) : lamMin x = -lamMax (-x) := by
  by_cases hN : 0 < N
  · simp only [lamMin, lamMax, hN, dite_true, eig]
    rw [hybrid_eigAsc_congr (toMatrix_neg x) (toMatrix_isHermitian (-x))
      (toMatrix_isHermitian x).neg ⟨N - 1, by omega⟩, eigAsc_neg]
    have : Fin.rev (⟨N - 1, by omega⟩ : Fin N) = ⟨0, hN⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    rw [this, neg_neg]
  · simp [lamMin, lamMax, hN]

end Rigidity
