module

public import Rigidity.Spectrum.Eigenvalues
public import Rigidity.Edge.Resolvent
public import Rigidity.MainDefs

@[expose] public section

/-!
# The Green function, minors and basic resolvent bounds

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian matrix `H` over `ℝ` or `ℂ` (a field `𝕜` with `RCLike 𝕜`), this file introduces
the complexification `toC : 𝕜 → ℂ` (a ring homomorphism `toCHom`), the Green function
`G(z) = (H - z)⁻¹` (2.8), its normalised trace `m(z) = N⁻¹ tr G(z)` (2.9), and the minor `H^{(T)}`
with its Green function `G^{(T)}` (Definition 3.1).  It proves:
* the complexification of a hermitian matrix is hermitian and has the same ordered eigenvalues
  `eigAsc`;
* `(H - z) G(z) = 1` for `Im z ≠ 0`;
* Lemma 3.5 (a): `‖G(z)‖ ≤ 1 / Im z` for the `ℓ²` operator norm and `Im z > 0`;
* Lemma 3.5 (d): the spectral form `m(z) = N⁻¹ ∑ 1 / (λ_α - z)`;
* Lemma 3.5 (c): the entry bound `|G_ij(z) - G_ij(w)| ≤ |z - w| / (Im z · Im w)`, which follows
  from the resolvent identity `G(z) - G(w) = (z - w) G(z) G(w)`.

-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 4. Resolvent quantities -/

/-- `toC` as a ring homomorphism. -/
noncomputable def toCHom : 𝕜 →+* ℂ where
  toFun := toC
  map_one' := by apply Complex.ext <;> simp [toC]
  map_mul' a b := by apply Complex.ext <;> simp [toC, RCLike.mul_re, RCLike.mul_im]
  map_zero' := by apply Complex.ext <;> simp [toC]
  map_add' a b := by apply Complex.ext <;> simp [toC]

theorem isHermitian_map_toC {n : Type*} [Fintype n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A.map toC).IsHermitian := by
  ext i j
  have h : star (A j i) = A i j := congrFun (congrFun hA i) j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← h]
  apply Complex.ext <;> simp [toC]

private theorem toC_ofReal (r : ℝ) : toC (RCLike.ofReal r : 𝕜) = (r : ℂ) := by
  apply Complex.ext <;> simp [toC]

/-- The real parts of the roots of the characteristic polynomial of the complexification of a
hermitian matrix are the eigenvalues of the matrix. -/
private theorem map_re_roots_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (A.map toC).charpoly.roots.map (⇑(RCLike.re : ℂ →+ ℝ)) =
      Finset.univ.val.map hA.eigenvalues := by
  have h1 : (A.map toC).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((hA.eigenvalues i : ℝ) : ℂ)) := by
    have := Matrix.charpoly_map A (toCHom : 𝕜 →+* ℂ)
    have h2 : A.map (toCHom : 𝕜 →+* ℂ) = A.map toC := rfl
    rw [← h2, this, hA.charpoly_eq, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 2
    exact toC_ofReal _
  rw [h1]
  have h3 : (∏ i, (Polynomial.X - Polynomial.C ((hA.eigenvalues i : ℝ) : ℂ))) =
      ((Finset.univ.val.map fun i => ((hA.eigenvalues i : ℝ) : ℂ)).map
        fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [h3, Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_map]
  rfl

theorem eigAsc_map_toC {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    eigAsc (isHermitian_map_toC hA) = eigAsc hA := by
  have hB := isHermitian_map_toC hA
  have h1 := hB.sort_roots_charpoly_eq_eigenvalues₀
  have h2 := hA.sort_roots_charpoly_eq_eigenvalues₀
  have h3 : (A.charpoly.roots.map RCLike.re) = Finset.univ.val.map hA.eigenvalues := by
    rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    simp [Function.comp_def]
  rw [h3] at h2
  rw [map_re_roots_charpoly hA] at h1
  have h4 : hB.eigenvalues₀ = hA.eigenvalues₀ := by
    rw [← List.ofFn_inj, ← h1, ← h2]
  funext k
  unfold eigAsc
  rw [h4]

/-- The minor `H^{(T)}` (Definition 3.1). -/
def minor {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (T : Finset (Fin N)) :
    Matrix {i // i ∉ T} {i // i ∉ T} 𝕜 :=
  A.submatrix Subtype.val Subtype.val

/-- `G^{(T)}(z) = (H^{(T)} - z)⁻¹` (Definition 3.1). -/
noncomputable def greenMinor {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (T : Finset (Fin N))
    (z : ℂ) : Matrix {i // i ∉ T} {i // i ∉ T} ℂ :=
  green (minor A T) z

theorem green_mul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (A.map toC - z • (1 : Matrix n n ℂ)) * green A z = 1 :=
  Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero (isHermitian_map_toC hA) hz))

theorem norm_green_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) : ‖green A z‖ ≤ 1 / z.im :=
  norm_resolventMat_le (isHermitian_map_toC hA) hz

/-- The bijection of `Fin N` sending `k` to the index, in `hA.eigenvalues`, of the `(k+1)`-st
smallest eigenvalue. -/
private noncomputable def ascPermC (N : ℕ) : Equiv.Perm (Fin N) :=
  Fin.revPerm.trans ((finCongr (Fintype.card_fin N).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)))

private theorem eigenvalues_ascPermC {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (k : Fin N) : hA.eigenvalues (ascPermC N k) = eigAsc hA k := by
  simp [ascPermC, Matrix.IsHermitian.eigenvalues, eigAsc]

/-- The trace of the resolvent of a hermitian complex matrix `B` is `∑ 1 / (μ_i - z)`, where
`μ_i` are the eigenvalues of `B`: with the eigenvector unitary `U`, `(B - z)⁻¹ = U (μ - z)⁻¹ U*`. -/
private theorem trace_inv_sub_smul {N : ℕ} {B : Matrix (Fin N) (Fin N) ℂ} (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    (B - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace = ∑ i, 1 / ((hB.eigenvalues i : ℂ) - z) := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hB.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hU
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hden : ∀ i, (hB.eigenvalues i : ℂ) - z ≠ 0 := by
    intro i h
    apply hz
    have := congrArg Complex.im h
    simpa using this.symm
  set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun i => (hB.eigenvalues i : ℂ) - z with hD
  set E : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal fun i => 1 / ((hB.eigenvalues i : ℂ) - z)
    with hE
  have hDE : D * E = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp [hden i]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hBeq : B - z • (1 : Matrix (Fin N) (Fin N) ℂ) = U * D * star U := by
    have h1 : B = U * Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) * star U := by
      conv_lhs => rw [hB.spectral_theorem]
      simp [Function.comp_def]
      rfl
    have h2 : z • (1 : Matrix (Fin N) (Fin N) ℂ) = U * (z • 1) * star U := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    have h3 : D = Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) - z • 1 := by
      rw [hD]; ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rw [h3, Matrix.mul_sub, Matrix.sub_mul]
    rw [← h1, ← h2]
  have hinv : (B - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = U * E * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hBeq]
    calc U * D * star U * (U * E * star U) = U * (D * (star U * U) * E) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, hDE, Matrix.mul_one, hU2]
  rw [hinv, Matrix.trace_mul_cycle, hU1, Matrix.one_mul, hE, Matrix.trace_diagonal]

theorem stieltjesEmp_eq_sum {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    stieltjesEmp A z = (N : ℂ)⁻¹ * ∑ k, 1 / ((eigAsc hA k : ℂ) - z) := by
  have hB := isHermitian_map_toC hA
  unfold stieltjesEmp green
  rw [trace_inv_sub_smul hB hz.ne', Fintype.card_fin]
  congr 1
  rw [← Equiv.sum_comp (ascPermC N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eigenvalues_ascPermC hB k, eigAsc_map_toC hA]

/-- The `(i, j)` entry of a complex matrix is bounded by its `ℓ²` operator norm. -/
private theorem norm_apply_le_l2_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ n)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M *ᵥ (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ n))) i
  simpa [Matrix.mulVec_single_one] using this

theorem norm_green_sub_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (i j : n) :
    ‖green A z i j - green A w i j‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  have hB := isHermitian_map_toC hA
  have h1 : green A z * (A.map toC - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hB hz.ne'))
  have h2 := green_mul hA hw.ne'
  have hid : green A z - green A w = (z - w) • (green A z * green A w) := by
    have h3 : green A z *
        ((A.map toC - w • (1 : Matrix n n ℂ)) - (A.map toC - z • (1 : Matrix n n ℂ))) *
          green A w = (z - w) • (green A z * green A w) := by
      have : (A.map toC - w • (1 : Matrix n n ℂ)) - (A.map toC - z • (1 : Matrix n n ℂ)) =
          (z - w) • (1 : Matrix n n ℂ) := by
        rw [sub_smul]; abel
      rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [← h3, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul,
      Matrix.mul_assoc _ (A.map toC - w • (1 : Matrix n n ℂ)), h2, Matrix.mul_one]
  have h4 : green A z i j - green A w i j = ((z - w) • (green A z * green A w)) i j := by
    rw [← hid]; rfl
  rw [h4]
  refine (norm_apply_le_l2_opNorm _ i j).trans ?_
  rw [norm_smul]
  have h5 := Matrix.l2_opNorm_mul (green A z) (green A w)
  have h6 := norm_green_le hA hz
  have h7 := norm_green_le hA hw
  have h8 : ‖green A z * green A w‖ ≤ 1 / z.im * (1 / w.im) :=
    h5.trans (mul_le_mul h6 h7 (norm_nonneg _) (by positivity))
  calc ‖z - w‖ * ‖green A z * green A w‖ ≤ ‖z - w‖ * (1 / z.im * (1 / w.im)) :=
        mul_le_mul_of_nonneg_left h8 (norm_nonneg _)
    _ = ‖z - w‖ / (z.im * w.im) := by field_simp

end Rigidity
