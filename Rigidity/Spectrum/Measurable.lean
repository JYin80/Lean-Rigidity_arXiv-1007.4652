import Rigidity.Ensemble.Basic
import Rigidity.LocalLaw.Defs
import Rigidity.Resolvent.Schur
import Rigidity.Semicircle.Density
import Rigidity.Spectrum.Continuity
import Rigidity.Stability.Equations

/-!
# Lipschitz dependence of the minor resolvents on the entries; continuity

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The space of entries is `Ω = Pair N → 𝕜`, with the Euclidean norm
`|x|² = ∑_{(i,j)} ‖x_ij‖²` of the first paragraph of §3.4.  This file proves the parts of
Lemma 3.13 that concern the resolvent entries:
(e) the Lipschitz bound
`|G^{(T)}_{ij}(x, z) - G^{(T)}_{ij}(y, z)| ≤ √2 (Im z)⁻² |x - y|` for the entries of the resolvent
of the minor, and the joint continuity of `(x, z) ↦ G^{(T)}_{ij}(x, z)` on `Ω × {Im z > 0}`.
The Lipschitz bound goes through the resolvent identity for the minor and the Hilbert–Schmidt
norm, in which each off-diagonal entry of `H(x) - H(y)` is counted twice.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. The Hilbert–Schmidt estimate for the difference of two minors -/

/-- `‖toC y‖ = ‖y‖`. -/
private theorem measurable_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- `‖M‖ ≤ (∑ᵢⱼ ‖Mᵢⱼ‖²)^{1/2}` for the `ℓ²` operator norm on a finite index type. -/
private theorem measurable_norm_le_sqrt_sum_sq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : ‖M‖ ≤ Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2) := by
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

/-- The `(i, j)` entry of a complex matrix is bounded by its `ℓ²` operator norm. -/
private theorem measurable_norm_apply_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (i j : n) : ‖M i j‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ n)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (M *ᵥ (WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ n))) i
  simpa [Matrix.mulVec_single_one] using this

/-- The resolvent identity `G_A - G_B = G_A (B - A) G_B` for hermitian matrices. -/
private theorem measurable_green_sub {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    green A z - green B z = green A z * (B.map toC - A.map toC) * green B z := by
  have h1 : green A z * (A.map toC - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero (isHermitian_map_toC hA) hz.ne'))
  have h2 := green_mul hB hz.ne'
  have h3 : B.map toC - A.map toC =
      (B.map toC - z • (1 : Matrix n n ℂ)) - (A.map toC - z • (1 : Matrix n n ℂ)) := by abel
  rw [h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, h1, Matrix.one_mul]

private theorem measurable_toMatrix_sub {N : ℕ} (x y : Pair N → 𝕜) :
    toMatrix x - toMatrix y = toMatrix (x - y) := by
  ext i j
  simp only [toMatrix, Matrix.sub_apply, Matrix.of_apply, Pi.sub_apply]
  split_ifs
  · rfl
  · rw [star_sub]
  · rw [map_sub, RCLike.ofReal_sub]

/-- A sum over `Pair N` as a sum over the pairs `(i, j)` with `i ≤ j`. -/
private theorem measurable_sum_pair {N : ℕ} (f : Pair N → ℝ) :
    ∑ p, f p = ∑ q : Fin N × Fin N, if q.1 ≤ q.2 then f (Pair.mk' q.1 q.2) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter fun q : Fin N × Fin N =>
    q.1 ≤ q.2) (p := fun q : Fin N × Fin N => q.1 ≤ q.2) (by simp)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Pair.mk', p.2]

/-- The squared Hilbert–Schmidt norm of `H(d)` is at most `2 |d|²`. -/
private theorem measurable_sum_sq_toMatrix_le {N : ℕ} (d : Pair N → 𝕜) :
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
    (measurable_sum_pair fun p => ‖d p‖ ^ 2).symm
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

/-- A sum over the elements of a subtype of nonnegative terms is at most the sum over the whole
type. -/
private theorem measurable_sum_subtype_le {N : ℕ} (T : Finset (Fin N)) (f : Fin N → ℝ)
    (hf : ∀ k, 0 ≤ f k) : ∑ a : {i // i ∉ T}, f a.val ≤ ∑ k, f k := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => i ∉ T) (by simp) f]
  exact Finset.sum_le_univ_sum_of_nonneg hf

/-! ### 2. Lemma 3.13 (e): the Lipschitz bound -/

/-- Lemma 3.13 (e): Lipschitz bound for the resolvent entries in the entries of `H`. -/
theorem norm_greenT_toMatrix_sub_le {N : ℕ} (T : Finset (Fin N)) {z : ℂ} (hz : 0 < z.im)
    (i j : Fin N) (x y : Pair N → 𝕜) :
    ‖greenT (toMatrix x) T z i j - greenT (toMatrix y) T z i j‖ ≤
      Real.sqrt 2 / z.im ^ 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
  have hrhs : 0 ≤ Real.sqrt 2 / z.im ^ 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by positivity
  by_cases h : i ∉ T ∧ j ∉ T
  · have hP : (minor (toMatrix x) T).IsHermitian :=
      (toMatrix_isHermitian x).submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    have hP' : (minor (toMatrix y) T).IsHermitian :=
      (toMatrix_isHermitian y).submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    simp only [greenT, Matrix.of_apply, h.1, h.2, not_false_eq_true, and_self, ↓reduceDIte,
      greenMinor]
    set a : {i // i ∉ T} := ⟨i, h.1⟩
    set b : {i // i ∉ T} := ⟨j, h.2⟩
    have hid := measurable_green_sub (z := z) hP hP' hz
    have h1 : green (minor (toMatrix x) T) z a b - green (minor (toMatrix y) T) z a b =
        (green (minor (toMatrix x) T) z *
          ((minor (toMatrix y) T).map toC - (minor (toMatrix x) T).map toC) *
            green (minor (toMatrix y) T) z) a b := by
      rw [← hid]; rfl
    rw [h1]
    refine (measurable_norm_apply_le _ a b).trans ?_
    set D : Matrix {i // i ∉ T} {i // i ∉ T} ℂ :=
      (minor (toMatrix y) T).map toC - (minor (toMatrix x) T).map toC with hD
    have hG := norm_green_le (z := z) hP hz
    have hG' := norm_green_le (z := z) hP' hz
    have hDn : ‖D‖ ≤ Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2) := by
      refine (measurable_norm_le_sqrt_sum_sq D).trans ?_
      have hDe : ∀ a b : {i // i ∉ T}, ‖D a b‖ ^ 2 = ‖toMatrix (y - x) a.val b.val‖ ^ 2 := by
        intro a b
        have : D a b = toC (toMatrix (y - x) a.val b.val) := by
          rw [hD, ← measurable_toMatrix_sub]
          simp only [minor, Matrix.sub_apply, Matrix.map_apply, Matrix.submatrix_apply]
          apply Complex.ext <;> simp [toC]
        rw [this, measurable_norm_toC]
      have hsum : ∑ a, ∑ b, ‖D a b‖ ^ 2 ≤ 2 * ∑ p, ‖x p - y p‖ ^ 2 := by
        have hg : ∀ k l : Fin N, 0 ≤ ‖toMatrix (y - x) k l‖ ^ 2 := fun k l => by positivity
        calc ∑ a, ∑ b, ‖D a b‖ ^ 2
            = ∑ a : {i // i ∉ T}, ∑ b : {i // i ∉ T}, ‖toMatrix (y - x) a.val b.val‖ ^ 2 :=
              Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hDe a b
          _ ≤ ∑ a : {i // i ∉ T}, ∑ l, ‖toMatrix (y - x) a.val l‖ ^ 2 :=
              Finset.sum_le_sum fun a _ =>
                measurable_sum_subtype_le T (fun l => ‖toMatrix (y - x) a.val l‖ ^ 2)
                  fun l => by positivity
          _ ≤ ∑ k, ∑ l, ‖toMatrix (y - x) k l‖ ^ 2 :=
              measurable_sum_subtype_le T (fun k => ∑ l, ‖toMatrix (y - x) k l‖ ^ 2)
                fun k => Finset.sum_nonneg fun l _ => by positivity
          _ ≤ 2 * ∑ p, ‖(y - x) p‖ ^ 2 := measurable_sum_sq_toMatrix_le _
          _ = 2 * ∑ p, ‖x p - y p‖ ^ 2 := by
              congr 1
              exact Finset.sum_congr rfl fun p _ => by
                rw [Pi.sub_apply, norm_sub_rev]
      calc Real.sqrt (∑ a, ∑ b, ‖D a b‖ ^ 2) ≤ Real.sqrt (2 * ∑ p, ‖x p - y p‖ ^ 2) :=
            Real.sqrt_le_sqrt hsum
        _ = _ := Real.sqrt_mul (by norm_num) _
    calc ‖green (minor (toMatrix x) T) z * D * green (minor (toMatrix y) T) z‖
        ≤ ‖green (minor (toMatrix x) T) z * D‖ * ‖green (minor (toMatrix y) T) z‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ (‖green (minor (toMatrix x) T) z‖ * ‖D‖) * ‖green (minor (toMatrix y) T) z‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ ((1 / z.im) * (Real.sqrt 2 * Real.sqrt (∑ p, ‖x p - y p‖ ^ 2))) * (1 / z.im) := by
          refine mul_le_mul (mul_le_mul hG hDn (norm_nonneg _) (by positivity)) hG'
            (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  · have h0 : ∀ A : Matrix (Fin N) (Fin N) 𝕜, greenT A T z i j = 0 := fun A => by
      simp [greenT, h]
    rw [h0, h0, sub_zero, norm_zero]
    exact hrhs

/-! ### 3. Lemma 3.13 (e): joint continuity -/

/-- The entries of `G^{(T)}` of a fixed matrix are Lipschitz in the spectral parameter, with
constant `(Im z Im w)⁻¹`. -/
private theorem measurable_norm_greenT_sub_spectral_le {N : ℕ} (T : Finset (Fin N))
    (x : Pair N → 𝕜) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (i j : Fin N) :
    ‖greenT (toMatrix x) T z i j - greenT (toMatrix x) T w i j‖ ≤ ‖z - w‖ / (z.im * w.im) := by
  by_cases h : i ∉ T ∧ j ∉ T
  · have hP : (minor (toMatrix x) T).IsHermitian :=
      (toMatrix_isHermitian x).submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    simp only [greenT, Matrix.of_apply, h.1, h.2, not_false_eq_true, and_self, ↓reduceDIte,
      greenMinor]
    exact norm_green_sub_le hP hz hw _ _
  · have h0 : ∀ u : ℂ, greenT (toMatrix x) T u i j = 0 := fun u => by simp [greenT, h]
    rw [h0, h0, sub_zero, norm_zero]
    positivity

/-- Lemma 3.13 (e): joint continuity of resolvent entries. -/
theorem continuous_greenT {N : ℕ} (T : Finset (Fin N)) (i j : Fin N) :
    Continuous fun q : (Pair N → 𝕜) × {z : ℂ // 0 < z.im} => greenT (toMatrix q.1) T q.2 i j := by
  refine continuous_iff_continuousAt.2 fun q₀ => ?_
  obtain ⟨x₀, z₀, hz₀⟩ := q₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  set g : (Pair N → 𝕜) × {z : ℂ // 0 < z.im} → ℝ := fun q =>
    Real.sqrt 2 / (z₀.im / 2) ^ 2 * Real.sqrt (∑ p, ‖q.1 p - x₀ p‖ ^ 2) +
      ‖(q.2 : ℂ) - z₀‖ / (z₀.im / 2 * z₀.im) with hg
  have hgc : Continuous g := by fun_prop
  have hg0 : g (x₀, ⟨z₀, hz₀⟩) = 0 := by simp [hg]
  have hev : ∀ᶠ q in 𝓝 (x₀, (⟨z₀, hz₀⟩ : {z : ℂ // 0 < z.im})), z₀.im / 2 < (q.2 : ℂ).im := by
    have hc : Continuous fun q : (Pair N → 𝕜) × {z : ℂ // 0 < z.im} => (q.2 : ℂ).im := by
      fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (half_lt_self hz₀))
  have hT : Tendsto g (𝓝 (x₀, (⟨z₀, hz₀⟩ : {z : ℂ // 0 < z.im}))) (𝓝 0) := by
    have := hgc.tendsto (x₀, (⟨z₀, hz₀⟩ : {z : ℂ // 0 < z.im}))
    rwa [hg0] at this
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hT
  filter_upwards [hev] with q hq
  have hh : 0 < z₀.im / 2 := by positivity
  rw [dist_eq_norm]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (greenT (toMatrix x₀) T q.2 i j) _).trans ?_
  refine add_le_add ?_ ?_
  · refine (norm_greenT_toMatrix_sub_le T q.2.2 i j q.1 x₀).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
      (pow_le_pow_left₀ hh.le hq.le 2)
  · refine (measurable_norm_greenT_sub_spectral_le T x₀ q.2.2 hz₀ i j).trans ?_
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_right hq.le hz₀.le)

end Rigidity
