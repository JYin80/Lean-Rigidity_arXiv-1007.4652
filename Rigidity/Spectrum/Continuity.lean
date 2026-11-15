import Rigidity.Spectrum.Eigenvalues

/-!
# Continuity of the ordered eigenvalues in the entries

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The space of entries is `Ω = Pair N → 𝕜`, with the Euclidean norm
`|x|² = ∑_{(i,j)} ‖x_ij‖²` of the first paragraph of §3.4.  This file proves the parts of
Lemma 3.13 that concern the map `x ↦ H(x)`:
(d) the Lipschitz bounds `‖H(x) - H(x')‖ ≤ √2 |x - x'|` and
`|λ_k(H(x)) - λ_k(H(x'))| ≤ √2 |x - x'|`, and hence continuity of `x ↦ λ_k(H(x))` on `Ω`.
The operator norm bound goes through the Hilbert–Schmidt norm, in which each off-diagonal entry
of `H(x) - H(x')` is counted twice.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. The map `x ↦ H(x)` is `ℝ`-linear -/

private theorem toMatrix_sub {N : ℕ} (x y : Pair N → 𝕜) :
    toMatrix x - toMatrix y = toMatrix (x - y) := by
  ext i j
  simp only [toMatrix, Matrix.sub_apply, Matrix.of_apply, Pi.sub_apply]
  split_ifs
  · rfl
  · rw [star_sub]
  · rw [map_sub, RCLike.ofReal_sub]

/-! ### 2. The operator norm is at most the Hilbert–Schmidt norm -/

/-- `‖M‖ ≤ (∑ᵢⱼ ‖Mᵢⱼ‖²)^{1/2}` for the `ℓ²` operator norm. -/
private theorem norm_le_sqrt_sum_sq {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜) :
    ‖M‖ ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun X => ?_
  change ‖Matrix.toEuclideanLin M X‖ ≤ _ * ‖X‖
  have hrow : ∀ i, ‖(M *ᵥ X.ofLp) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := fun i => by
    have h1 : ‖(M *ᵥ X.ofLp) i‖ ≤ ∑ j, ‖M i j‖ * ‖X.ofLp j‖ := by
      calc ‖(M *ᵥ X.ofLp) i‖ = ‖∑ j, M i j * X.ofLp j‖ := rfl
        _ ≤ ∑ j, ‖M i j * X.ofLp j‖ := norm_sum_le _ _
        _ = ∑ j, ‖M i j‖ * ‖X.ofLp j‖ := by simp only [norm_mul]
    calc ‖(M *ᵥ X.ofLp) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖X.ofLp j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖X.ofLp j‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖(Matrix.toEuclideanLin M X).ofLp i‖ ^ 2 = ∑ i, ‖(M *ᵥ X.ofLp) i‖ ^ 2 := by
        rfl
    _ ≤ ∑ i, (∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ j, ‖M i j‖ ^ 2) * ‖X‖ ^ 2 := by rw [Finset.sum_mul]
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]

/-! ### 3. Counting each off-diagonal entry twice -/

/-- A sum over `Pair N` as a sum over the pairs `(i, j)` with `i ≤ j`. -/
private theorem sum_pair {N : ℕ} (f : Pair N → ℝ) :
    ∑ p, f p = ∑ q : Fin N × Fin N, if q.1 ≤ q.2 then f (Pair.mk' q.1 q.2) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter fun q : Fin N × Fin N =>
    q.1 ≤ q.2) (p := fun q : Fin N × Fin N => q.1 ≤ q.2) (by simp)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pair.mk', p.2]

/-- The squared Hilbert–Schmidt norm of `H(d)` is at most `2 |d|²`: each pair `(i, j)` with
`i < j` fills the entries `(i, j)` and `(j, i)`, and the diagonal entry `(i, i)` is bounded by
`‖d_ii‖`. -/
private theorem sum_sq_toMatrix_le {N : ℕ} (d : Pair N → 𝕜) :
    ∑ i, ∑ j, ‖toMatrix d i j‖ ^ 2 ≤ 2 * ∑ p, ‖d p‖ ^ 2 := by
  have hent : ∀ i j : Fin N, ‖toMatrix d i j‖ ^ 2 ≤ ‖d (Pair.mk' i j)‖ ^ 2 := fun i j => by
    unfold toMatrix
    simp only [Matrix.of_apply]
    split_ifs
    · exact le_rfl
    · rw [norm_star]
    · exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using RCLike.abs_re_le_norm _) 2
  rw [← Fintype.sum_prod_type' (fun i j => ‖toMatrix d i j‖ ^ 2)]
  set w : Fin N × Fin N → ℝ := fun q => ‖d (Pair.mk' q.1 q.2)‖ ^ 2 with hw
  have h1 : ∑ q : Fin N × Fin N, (if q.1 ≤ q.2 then w q else 0) = ∑ p, ‖d p‖ ^ 2 :=
    (sum_pair fun p => ‖d p‖ ^ 2).symm
  have h2 : ∑ q : Fin N × Fin N, (if q.2 ≤ q.1 then w q else 0) = ∑ p, ‖d p‖ ^ 2 := by
    rw [← h1]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun q => ?_
    simp only [hw, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [Pair.mk'_comm]
  calc ∑ q : Fin N × Fin N, ‖toMatrix d q.1 q.2‖ ^ 2
      ≤ ∑ q : Fin N × Fin N, ((if q.1 ≤ q.2 then w q else 0) + (if q.2 ≤ q.1 then w q else 0)) :=
        Finset.sum_le_sum fun q _ => by
          have hq : 0 ≤ w q := by positivity
          rcases le_total q.1 q.2 with h | h
          · by_cases h' : q.2 ≤ q.1
            · simp only [h, h', ite_true]; linarith [hent q.1 q.2]
            · simp only [h, h', ite_true, ite_false]; linarith [hent q.1 q.2]
          · by_cases h' : q.1 ≤ q.2
            · simp only [h, h', ite_true]; linarith [hent q.1 q.2]
            · simp only [h, h', ite_true, ite_false]; linarith [hent q.1 q.2]
    _ = 2 * ∑ p, ‖d p‖ ^ 2 := by rw [Finset.sum_add_distrib, h1, h2]; ring

/-- Lemma 3.13 (d), first inequality: `‖H(x) - H(y)‖ ≤ √2 |x - y|`. -/
private theorem norm_toMatrix_sub_le_aux {N : ℕ} (x y : Pair N → 𝕜) :
    ‖toMatrix x - toMatrix y‖ ≤ Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
  rw [toMatrix_sub]
  calc ‖toMatrix (x - y)‖ ≤ Real.sqrt (∑ i, ∑ j, ‖toMatrix (x - y) i j‖ ^ 2) :=
        norm_le_sqrt_sum_sq _
    _ ≤ Real.sqrt (2 * ∑ p, ‖(x - y) p‖ ^ 2) := Real.sqrt_le_sqrt (sum_sq_toMatrix_le _)
    _ = Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
        rw [Real.sqrt_mul (by norm_num)]; rfl

theorem abs_eig_sub_le {N : ℕ} (x y : Pair N → 𝕜) (k : Fin N) :
    |eig x k - eig y k| ≤ Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
  exact (abs_eigAsc_sub_le (toMatrix_isHermitian x) (toMatrix_isHermitian y) k).trans
    (norm_toMatrix_sub_le_aux x y)

theorem continuous_eig {N : ℕ} (k : Fin N) : Continuous fun x : Pair N → 𝕜 => eig x k := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous fun x : Pair N → 𝕜 => Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
    fun_prop
  refine squeeze_zero (fun _ => dist_nonneg) (fun x => ?_) (by simpa using hc.tendsto y)
  rw [Real.dist_eq]
  exact abs_eig_sub_le x y k

/-- Lemma 3.13 (d): `‖H(x) - H(x')‖ ≤ √2 |x - x'|`. -/
theorem norm_toMatrix_sub_le {N : ℕ} (x y : Pair N → 𝕜) :
    ‖toMatrix x - toMatrix y‖ ≤ Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
  exact norm_toMatrix_sub_le_aux x y

end Rigidity
