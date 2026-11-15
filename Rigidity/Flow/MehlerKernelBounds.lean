import Rigidity.Flow.Mehler

/-!
# Bounds on the derivatives of the Mehler kernel; smoothness of kernel integrals

This file proves Lemma 14.F (explicit bounds on the derivatives of the Mehler kernel
`K(u, y, w)` of (14.2) in `x = (u, y) ∈ (0, ∞) × E`) and Lemma 14.G (the domination (14.4) and
the smoothness of `Ψ_h(u, y) = ∫ K(u, y, w) h(w) ρ(dw)`, with all derivatives taken under the
integral sign, and the equation `∂_u Ψ_h = A Ψ_h`), with the constants `t_k`, `c_{j,k}`, `ĉ_n`,
`κ(u₁)` of §14.4. On `ℝ × E` the norm is `‖(h, e)‖ = max (|h|, |e|)`, as in §14.4.

Statement numbers refer to the blueprint NP v1.1; a result of Erdős–Yau–Yin (arXiv:1007.4652) is
cited as [EYY, …].
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-! ### The constants of §14.4 -/

/-- `t_0 = t_1 = 1`, `t_{k+1} = t_k + k t_{k-1}` (§14.4). -/
noncomputable def mehlerKernelBoundsT : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | k + 2 => mehlerKernelBoundsT (k + 1) + (k + 1 : ℕ) * mehlerKernelBoundsT k

/-- `c_{0,k} = t_k`, `c_{j,k} = (v d / 2) c_{j-1,k+2} + c_{j-1,k+1} / 2 + (k / 2) c_{j-1,k}`
(§14.4, with `v = σ²`). -/
noncomputable def mehlerKernelBoundsC (v : ℝ) (d : ℕ) : ℕ → ℕ → ℝ
  | 0, k => mehlerKernelBoundsT k
  | j + 1, k => v * d / 2 * mehlerKernelBoundsC v d j (k + 2) +
      1 / 2 * mehlerKernelBoundsC v d j (k + 1) + k / 2 * mehlerKernelBoundsC v d j k

/-- `ĉ_n = max_{0 ≤ j ≤ n} c_{j,n-j}` (§14.4). -/
noncomputable def mehlerKernelBoundsCHat (v : ℝ) (d n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun j => mehlerKernelBoundsC v d j (n - j)

/-- `κ(u₁) = 1 + 1 / (v s_{u₁}) + 1 / (v s_{u₁})^{1/2}` (§14.4, with `v = σ²`). -/
noncomputable def mehlerKernelBoundsKappa (v u₁ : ℝ) : ℝ :=
  1 + 1 / (v * ouS u₁) + 1 / Real.sqrt (v * ouS u₁)

private lemma mehlerKernelBoundsT_succ_succ (k : ℕ) :
    mehlerKernelBoundsT (k + 2) =
      mehlerKernelBoundsT (k + 1) + (k + 1 : ℕ) * mehlerKernelBoundsT k :=
  rfl

private lemma mehlerKernelBoundsT_nonneg : ∀ k, 0 ≤ mehlerKernelBoundsT k
  | 0 => zero_le_one
  | 1 => zero_le_one
  | k + 2 => by
    rw [mehlerKernelBoundsT_succ_succ]
    have := mehlerKernelBoundsT_nonneg (k + 1)
    have := mehlerKernelBoundsT_nonneg k
    positivity

private lemma mehlerKernelBoundsC_nonneg {v : ℝ} (hv : 0 ≤ v) (d : ℕ) :
    ∀ j k, 0 ≤ mehlerKernelBoundsC v d j k
  | 0, k => mehlerKernelBoundsT_nonneg k
  | j + 1, k => by
    simp only [mehlerKernelBoundsC]
    have := mehlerKernelBoundsC_nonneg hv d j (k + 2)
    have := mehlerKernelBoundsC_nonneg hv d j (k + 1)
    have := mehlerKernelBoundsC_nonneg hv d j k
    positivity

private lemma mehlerKernelBoundsC_le_cHat (v : ℝ) (d : ℕ) {n j : ℕ} (hj : j ≤ n) :
    mehlerKernelBoundsC v d j (n - j) ≤ mehlerKernelBoundsCHat v d n :=
  Finset.le_sup' (fun j => mehlerKernelBoundsC v d j (n - j)) (Finset.mem_range.2 (by omega))

/-! ### Derivative bounds on a slice -/

section Slice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A Leibniz sum whose second factor vanishes from order `2` on. -/
private lemma mehlerKernelBounds_sum_peel (k : ℕ) (a b : ℕ → ℝ) (ha : ∀ i, 2 ≤ i → a i = 0) :
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * b i * a (k - i) =
      b k * a 0 + k * b (k - 1) * a 1 := by
  rcases k with _ | k
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range k, ((k + 1).choose i : ℝ) * b i * a (k + 1 - i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [ha _ (by simp at hi; omega)]; ring
    rw [this, Nat.choose_self, Nat.choose_succ_self_right, Nat.sub_self,
      show k + 1 - k = 1 by omega, Nat.add_sub_cancel]
    push_cast
    ring

omit [FiniteDimensional ℝ E] in
/-- The iterated derivatives of order `≥ 2` of an affine map vanish. -/
private lemma mehlerKernelBounds_iteratedFDeriv_affine {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} {L : E →L[ℝ] F} (hg : ∀ y, HasFDerivAt g L y) {i : ℕ}
    (hi : 2 ≤ i) (y : E) : ‖iteratedFDeriv ℝ i g y‖ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv]
  have : fderiv ℝ g = fun _ => L := funext fun y => (hg y).fderiv
  rw [this, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]

omit [FiniteDimensional ℝ E] in
/-- A continuous linear map with `‖L X‖ ≤ C ‖X‖` multiplies the norms of iterated derivatives by
at most `C`. -/
private lemma mehlerKernelBounds_norm_iteratedFDeriv_comp_le {X F G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {C : ℝ}
    (hC : 0 ≤ C) (hL : ∀ X, ‖L X‖ ≤ C * ‖X‖) {f : X → F} {y : X} {k : ℕ}
    (hf : ContDiffAt ℝ k f y) :
    ‖iteratedFDeriv ℝ k (L ∘ f) y‖ ≤ C * ‖iteratedFDeriv ℝ k f y‖ := by
  rw [L.iteratedFDeriv_comp_left hf le_rfl]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, mul_assoc]
  exact (hL _).trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ _) hC)

/-- The trace `L ↦ Σ_i L b_i b_i` over an orthonormal basis `(b_i)`. -/
private noncomputable def mehlerKernelBounds_trace : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.apply ℝ ℝ (stdOrthonormalBasis ℝ E i)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (stdOrthonormalBasis ℝ E i))

private lemma mehlerKernelBounds_trace_apply (L : E →L[ℝ] E →L[ℝ] ℝ) :
    mehlerKernelBounds_trace L =
      ∑ i, L (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
  simp [mehlerKernelBounds_trace]

private lemma mehlerKernelBounds_norm_trace_apply_le (L : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖mehlerKernelBounds_trace L‖ ≤ Module.finrank ℝ E * ‖L‖ := by
  rw [mehlerKernelBounds_trace_apply]
  calc ‖∑ i, L (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖
      ≤ ∑ i, ‖L (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖L‖ := Finset.sum_le_sum fun i _ => by
        refine (L.le_opNorm₂ _ _).trans ?_
        rw [(stdOrthonormalBasis ℝ E).orthonormal.1 i]; simp
    _ = Module.finrank ℝ E * ‖L‖ := by simp

/-- The generator `A φ = (v/2) Δ φ - (1/2) ⟨y, ∇ φ⟩` of (14.1), written with `D² φ` and `D φ`. -/
private noncomputable def mehlerKernelBounds_gen (v : ℝ) (φ : E → ℝ) (y : E) : ℝ :=
  v / 2 * mehlerKernelBounds_trace (fderiv ℝ (fderiv ℝ φ) y) - 1 / 2 * fderiv ℝ φ y y

/-- The commutator bound of Step 3 of Lemma 14.F:
`N_k(A φ) ≤ (v d / 2) N_{k+2} φ + (|y| / 2) N_{k+1} φ + (k / 2) N_k φ`. -/
private lemma mehlerKernelBounds_norm_iteratedFDeriv_gen_le {v : ℝ} (hv : 0 ≤ v) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (k : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ k (mehlerKernelBounds_gen v φ) y‖ ≤
      v * Module.finrank ℝ E / 2 * ‖iteratedFDeriv ℝ (k + 2) φ y‖ +
        ‖y‖ / 2 * ‖iteratedFDeriv ℝ (k + 1) φ y‖ + k / 2 * ‖iteratedFDeriv ℝ k φ y‖ := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ φ)) := h1.fderiv_right (by simp)
  have hT : ContDiff ℝ (⊤ : ℕ∞) (mehlerKernelBounds_trace ∘ fderiv ℝ (fderiv ℝ φ)) :=
    mehlerKernelBounds_trace.contDiff.comp h2
  have hI : ContDiff ℝ (⊤ : ℕ∞) fun y : E => fderiv ℝ φ y (id y) := h1.clm_apply contDiff_id
  have heq : mehlerKernelBounds_gen v φ = (fun y => (v / 2) •
      (mehlerKernelBounds_trace ∘ fderiv ℝ (fderiv ℝ φ)) y) -
        fun y => (1 / 2 : ℝ) • fderiv ℝ φ y (id y) :=
    rfl
  rw [heq, iteratedFDeriv_sub_apply ((hT.const_smul _).contDiffAt.of_le (by simp))
    ((hI.const_smul _).contDiffAt.of_le (by simp))]
  refine (norm_sub_le _ _).trans ?_
  rw [iteratedFDeriv_const_smul_apply' (hT.contDiffAt.of_le (by simp)),
    iteratedFDeriv_const_smul_apply' (hI.contDiffAt.of_le (by simp)), norm_smul, norm_smul]
  have hTb : ‖iteratedFDeriv ℝ k (mehlerKernelBounds_trace ∘ fderiv ℝ (fderiv ℝ φ)) y‖ ≤
      Module.finrank ℝ E * ‖iteratedFDeriv ℝ (k + 2) φ y‖ := by
    refine (mehlerKernelBounds_norm_iteratedFDeriv_comp_le _ (by positivity)
      mehlerKernelBounds_norm_trace_apply_le (h2.contDiffAt.of_le (by simp))).trans ?_
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  have hIb : ‖iteratedFDeriv ℝ k (fun y : E => fderiv ℝ φ y (id y)) y‖ ≤
      ‖y‖ * ‖iteratedFDeriv ℝ (k + 1) φ y‖ + k * ‖iteratedFDeriv ℝ k φ y‖ := by
    refine (norm_iteratedFDeriv_clm_apply h1 contDiff_id y (by simp)).trans ?_
    rw [mehlerKernelBounds_sum_peel k (fun i => ‖iteratedFDeriv ℝ i (id : E → E) y‖)
      (fun i => ‖iteratedFDeriv ℝ i (fderiv ℝ φ) y‖)
      (fun i hi => mehlerKernelBounds_iteratedFDeriv_affine (fun y => hasFDerivAt_id y) hi y)]
    simp only [norm_iteratedFDeriv_zero, id, norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    have hid : ‖fderiv ℝ (id : E → E) y‖ ≤ 1 := by
      rw [fderiv_id]; exact ContinuousLinearMap.norm_id_le
    rcases k with _ | k
    · simp only [CharP.cast_eq_zero, zero_mul, add_zero]
      rw [mul_comm]
    · rw [Nat.add_sub_cancel]
      have h3 := norm_nonneg (iteratedFDeriv ℝ (k + 1) φ y)
      have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left hid (mul_nonneg hk h3)
      nlinarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hTb (by positivity : (0 : ℝ) ≤ v / 2)]

omit [FiniteDimensional ℝ E] in
/-- Step 1 of Lemma 14.F in abstract form: if `D f = f · ℓ` with `ℓ` affine, `‖ℓ(y)‖ ≤ L` and
`‖Dℓ‖ ≤ L²`, then `N_k f(y) ≤ t_k L^k |f(y)|`. -/
private lemma mehlerKernelBounds_norm_iteratedFDeriv_le_of_affine {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : E →L[ℝ] ℝ) (Lℓ : E →L[ℝ] E →L[ℝ] ℝ)
    (hfd : ∀ y, fderiv ℝ f y = f y • (c + Lℓ y)) (y : E) {L : ℝ} (hL1 : ‖c + Lℓ y‖ ≤ L)
    (hL2 : ‖Lℓ‖ ≤ L ^ 2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k f y‖ ≤ mehlerKernelBoundsT k * L ^ k * |f y| := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hL1
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) fun y => c + Lℓ y := contDiff_const.add Lℓ.contDiff
  have hfd' : fderiv ℝ f = fun y => f y • (c + Lℓ y) := funext hfd
  have hrec : ∀ k, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤
      ‖iteratedFDeriv ℝ k f y‖ * L + k * ‖iteratedFDeriv ℝ (k - 1) f y‖ * L ^ 2 := by
    intro k
    rw [← norm_iteratedFDeriv_fderiv, hfd']
    refine (norm_iteratedFDeriv_smul_le hf hℓ y (by simp)).trans ?_
    rw [mehlerKernelBounds_sum_peel k (fun i => ‖iteratedFDeriv ℝ i (fun y => c + Lℓ y) y‖)
      (fun i => ‖iteratedFDeriv ℝ i f y‖) (fun i hi =>
        mehlerKernelBounds_iteratedFDeriv_affine (L := Lℓ)
          (fun y => (Lℓ.hasFDerivAt).const_add c) hi y)]
    simp only [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
    rw [((Lℓ.hasFDerivAt (x := y)).const_add c).fderiv]
    gcongr
  have key : ∀ k, ‖iteratedFDeriv ℝ k f y‖ ≤ mehlerKernelBoundsT k * L ^ k * |f y| ∧
      ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤
        mehlerKernelBoundsT (k + 1) * L ^ (k + 1) * |f y| := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp [mehlerKernelBoundsT], ?_⟩
      refine (hrec 0).trans ?_
      simp [mehlerKernelBoundsT, mul_comm]
    | succ k ih =>
      refine ⟨ih.2, (hrec (k + 1)).trans ?_⟩
      rw [mehlerKernelBoundsT_succ_succ, Nat.add_sub_cancel]
      have h1 := mul_le_mul_of_nonneg_right ih.2 hL
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih.1
        (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))) (by positivity : (0 : ℝ) ≤ L ^ 2)
      calc _ ≤ mehlerKernelBoundsT (k + 1) * L ^ (k + 1) * |f y| * L +
            (k + 1 : ℕ) * (mehlerKernelBoundsT k * L ^ k * |f y|) * L ^ 2 := by
            push_cast at h1 h2 ⊢; linarith
        _ = _ := by push_cast; ring
  exact (key k).1

/-- Step 4 of Lemma 14.F: one application of the generator, from `c_{j,·}` to `c_{j+1,·}`. -/
private lemma mehlerKernelBounds_norm_iteratedFDeriv_gen_le_of {v : ℝ} (hv : 0 ≤ v) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : E) {Λ M : ℝ} (hΛ : 1 ≤ Λ) (hy : ‖y‖ ≤ Λ) (hM : 0 ≤ M)
    (j : ℕ) (hb : ∀ m, ‖iteratedFDeriv ℝ m φ y‖ ≤
      mehlerKernelBoundsC v (Module.finrank ℝ E) j m * Λ ^ (m + 2 * j) * M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (mehlerKernelBounds_gen v φ) y‖ ≤
      mehlerKernelBoundsC v (Module.finrank ℝ E) (j + 1) k * Λ ^ (k + 2 * (j + 1)) * M := by
  refine (mehlerKernelBounds_norm_iteratedFDeriv_gen_le hv hφ k y).trans ?_
  set d := Module.finrank ℝ E
  have c0 := mehlerKernelBoundsC_nonneg hv d j k
  have c1 := mehlerKernelBoundsC_nonneg hv d j (k + 1)
  have c2 := mehlerKernelBoundsC_nonneg hv d j (k + 2)
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have p1 : Λ ^ (k + 1 + 2 * j) * ‖y‖ ≤ Λ ^ (k + 2 * (j + 1)) := by
    calc Λ ^ (k + 1 + 2 * j) * ‖y‖ ≤ Λ ^ (k + 1 + 2 * j) * Λ :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = Λ ^ (k + 2 * (j + 1)) := by rw [← pow_succ]; congr 1; omega
  have p2 : Λ ^ (k + 2 * j) ≤ Λ ^ (k + 2 * (j + 1)) := pow_le_pow_right₀ hΛ (by omega)
  have p3 : Λ ^ (k + 2 + 2 * j) = Λ ^ (k + 2 * (j + 1)) := by congr 1; ring
  have b0 := hb k
  have b1 := hb (k + 1)
  have b2 := hb (k + 2)
  simp only [mehlerKernelBoundsC]
  rw [p3] at b2
  have hk : (0 : ℝ) ≤ k := by positivity
  have hd : (0 : ℝ) ≤ v * d / 2 := by positivity
  have e1 : ‖y‖ / 2 * ‖iteratedFDeriv ℝ (k + 1) φ y‖ ≤
      1 / 2 * mehlerKernelBoundsC v d j (k + 1) * Λ ^ (k + 2 * (j + 1)) * M := by
    calc ‖y‖ / 2 * ‖iteratedFDeriv ℝ (k + 1) φ y‖ ≤
          ‖y‖ / 2 * (mehlerKernelBoundsC v d j (k + 1) * Λ ^ (k + 1 + 2 * j) * M) :=
          mul_le_mul_of_nonneg_left b1 (by positivity)
      _ = 1 / 2 * mehlerKernelBoundsC v d j (k + 1) * (Λ ^ (k + 1 + 2 * j) * ‖y‖) * M := by ring
      _ ≤ _ := by gcongr
  have e2 : (k : ℝ) / 2 * ‖iteratedFDeriv ℝ k φ y‖ ≤
      k / 2 * mehlerKernelBoundsC v d j k * Λ ^ (k + 2 * (j + 1)) * M := by
    calc (k : ℝ) / 2 * ‖iteratedFDeriv ℝ k φ y‖ ≤
          k / 2 * (mehlerKernelBoundsC v d j k * Λ ^ (k + 2 * j) * M) :=
          mul_le_mul_of_nonneg_left b0 (by positivity)
      _ ≤ k / 2 * (mehlerKernelBoundsC v d j k * Λ ^ (k + 2 * (j + 1)) * M) := by gcongr
      _ = _ := by ring
  have e3 : v * d / 2 * ‖iteratedFDeriv ℝ (k + 2) φ y‖ ≤
      v * d / 2 * mehlerKernelBoundsC v d j (k + 2) * Λ ^ (k + 2 * (j + 1)) * M := by
    calc v * d / 2 * ‖iteratedFDeriv ℝ (k + 2) φ y‖ ≤
          v * d / 2 * (mehlerKernelBoundsC v d j (k + 2) * Λ ^ (k + 2 * (j + 1)) * M) :=
          mul_le_mul_of_nonneg_left b2 hd
      _ = _ := by ring
  calc _ ≤ v * d / 2 * mehlerKernelBoundsC v d j (k + 2) * Λ ^ (k + 2 * (j + 1)) * M +
        1 / 2 * mehlerKernelBoundsC v d j (k + 1) * Λ ^ (k + 2 * (j + 1)) * M +
        k / 2 * mehlerKernelBoundsC v d j k * Λ ^ (k + 2 * (j + 1)) * M := by linarith
    _ = _ := by ring

end Slice

/-! ### Joint derivatives in `(u, y)` -/

section Joint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option quotPrecheck false in
local notation "Ω" => Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)

omit [NormedSpace ℝ E] in
private lemma mehlerKernelBounds_isOpen : IsOpen (Ω : Set (ℝ × E)) := isOpen_Ioi.prod isOpen_univ

/-- `H_{j,k}(x) = ∂_u^j D_y^k G(x)`, the `k`-linear form in the `y`-directions obtained from the
joint derivatives of `G` by `j` derivatives in the direction `(1, 0)`. -/
private noncomputable def mehlerKernelBounds_H (G : ℝ × E → ℝ) :
    ℕ → (k : ℕ) → ℝ × E → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ
  | 0, k => fun x => (iteratedFDeriv ℝ k G x).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ ℝ E)
  | j + 1, k => fun x => fderiv ℝ (mehlerKernelBounds_H G j k) x (1, 0)

private lemma mehlerKernelBounds_H_contDiffOn {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) :
    ∀ j k, ContDiffOn ℝ (⊤ : ℕ∞) (mehlerKernelBounds_H G j k) Ω
  | 0, k => by
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ k G) Ω := fun x hx =>
      ((hG.contDiffAt (mehlerKernelBounds_isOpen.mem_nhds hx)).iteratedFDeriv_right
        (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).contDiffWithinAt
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => ContinuousLinearMap.inr ℝ ℝ E)).contDiff.comp_contDiffOn h
  | j + 1, k => by
    have := mehlerKernelBounds_H_contDiffOn hG j k
    exact (this.fderiv_of_isOpen mehlerKernelBounds_isOpen (by simp)).clm_apply contDiffOn_const

private lemma mehlerKernelBounds_H_contDiffAt {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) (j k : ℕ) {x : ℝ × E} (hx : x ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) (mehlerKernelBounds_H G j k) x :=
  (mehlerKernelBounds_H_contDiffOn hG j k).contDiffAt (mehlerKernelBounds_isOpen.mem_nhds hx)

private lemma mehlerKernelBounds_H_differentiableAt {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) (j k : ℕ) {x : ℝ × E} (hx : x ∈ Ω) :
    DifferentiableAt ℝ (mehlerKernelBounds_H G j k) x :=
  (mehlerKernelBounds_H_contDiffAt hG j k hx).differentiableAt (by simp)

/-- The derivative of a continuous linear image. -/
private lemma mehlerKernelBounds_fderiv_clm_comp {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (L : Y →L[ℝ] Z) {f : X → Y} {x : X} (hf : DifferentiableAt ℝ f x) (h : X) :
    fderiv ℝ (fun x => L (f x)) x h = L (fderiv ℝ f x h) := by
  show fderiv ℝ (L ∘ f) x h = _
  rw [(L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]; rfl

/-- The `y`-derivative of `H_{j,k}` is `H_{j,k+1}`. -/
private lemma mehlerKernelBounds_H_fderiv_inr {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) :
    ∀ j k, ∀ x ∈ Ω, ∀ (e : E) (m : Fin k → E),
      fderiv ℝ (mehlerKernelBounds_H G j k) x (0, e) m =
        mehlerKernelBounds_H G j (k + 1) x (Fin.cons e m)
  | 0, k => fun x hx e m => by
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k G) x :=
      (hG.contDiffAt (mehlerKernelBounds_isOpen.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top k))
    have := mehlerKernelBounds_fderiv_clm_comp (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) hd (0, e)
    show fderiv ℝ (fun x => (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inr ℝ ℝ E)) (iteratedFDeriv ℝ k G x)) x (0, e) m = _
    rw [this]
    simp only [mehlerKernelBounds_H, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_succ_apply_left]
    congr 1
  | j + 1, k => fun x hx e m => by
    set F := mehlerKernelBounds_H G j k
    have hF := mehlerKernelBounds_H_contDiffAt hG j k hx
    have hF1 := hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    have hF1d := hF1.differentiableAt (by simp)
    have hsymm := hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    -- left side
    have hL : fderiv ℝ (mehlerKernelBounds_H G (j + 1) k) x (0, e) =
        fderiv ℝ (fderiv ℝ F) x (0, e) (1, 0) := by
      show fderiv ℝ (fun x => fderiv ℝ F x (1, 0)) x (0, e) = _
      exact mehlerKernelBounds_fderiv_clm_comp
        (ContinuousLinearMap.apply ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
          ((1 : ℝ), (0 : E))) hF1d ((0 : ℝ), e)
    -- right side
    have hR : mehlerKernelBounds_H G (j + 1) (k + 1) x (Fin.cons e m) =
        fderiv ℝ (fderiv ℝ F) x (1, 0) (0, e) m := by
      show fderiv ℝ (mehlerKernelBounds_H G j (k + 1)) x (1, 0) (Fin.cons e m) = _
      have h1 := mehlerKernelBounds_fderiv_clm_comp (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin (k + 1) => E) ℝ (Fin.cons e m))
        (mehlerKernelBounds_H_differentiableAt hG j (k + 1) hx) ((1 : ℝ), (0 : E))
      have h2 := mehlerKernelBounds_fderiv_clm_comp (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin k => E) ℝ m) (f := fun x => fderiv ℝ F x (0, e))
        (hF1d.clm_apply (differentiableAt_const ((0 : ℝ), e)))
        ((1 : ℝ), (0 : E))
      have h3 := mehlerKernelBounds_fderiv_clm_comp
        (ContinuousLinearMap.apply ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
          ((0 : ℝ), e)) hF1d ((1 : ℝ), (0 : E))
      have hev : (fun x' => mehlerKernelBounds_H G j (k + 1) x' (Fin.cons e m)) =ᶠ[𝓝 x]
          fun x' => fderiv ℝ F x' (0, e) m := by
        filter_upwards [mehlerKernelBounds_isOpen.mem_nhds hx] with x' hx'
        exact (mehlerKernelBounds_H_fderiv_inr hG j k x' hx' e m).symm
      simp only [ContinuousMultilinearMap.apply_apply] at h1 h2
      simp only [ContinuousLinearMap.apply_apply] at h3
      rw [← h1, hev.fderiv_eq, h2, h3]
    rw [hL, hR, hsymm]

omit [NormedSpace ℝ E] in
private lemma mehlerKernelBounds_natCast_lt_top (k : ℕ) :
    (k : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_lt_coe.2 (ENat.natCast_lt_top k)

/-- `D H_{j,k}(x)[(h, e)] = h H_{j+1,k}(x) + H_{j,k+1}(x)[e, ·]`. -/
private lemma mehlerKernelBounds_H_fderiv_apply {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) (j k : ℕ) {x : ℝ × E} (hx : x ∈ Ω) (h : ℝ) (e : E)
    (m : Fin k → E) :
    fderiv ℝ (mehlerKernelBounds_H G j k) x (h, e) m =
      h * mehlerKernelBounds_H G (j + 1) k x m +
        mehlerKernelBounds_H G j (k + 1) x (Fin.cons e m) := by
  have : ((h, e) : ℝ × E) = h • ((1 : ℝ), (0 : E)) + ((0 : ℝ), e) := by ext <;> simp
  rw [this, map_add, map_smul, add_apply,
    smul_apply, mehlerKernelBounds_H_fderiv_inr hG j k x hx e m,
    smul_eq_mul]
  rfl

variable (E) in
/-- The map `X ↦ (h, e) ↦ h X`. -/
private noncomputable def mehlerKernelBounds_L1 (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ →L[ℝ]
      (ℝ × E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  ContinuousLinearMap.smulRightL ℝ (ℝ × E) _ (ContinuousLinearMap.fst ℝ ℝ E)

variable (E) in
/-- The map `X ↦ (h, e) ↦ X[e, ·]`. -/
private noncomputable def mehlerKernelBounds_L2 (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ →L[ℝ]
      (ℝ × E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  ((ContinuousLinearMap.compL ℝ (ℝ × E) E _).flip (ContinuousLinearMap.snd ℝ ℝ E)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ :
      ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ →L[ℝ]
        (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ))

private lemma mehlerKernelBounds_L1_apply (k : ℕ) (X : ContinuousMultilinearMap ℝ
    (fun _ : Fin k => E) ℝ) (h : ℝ) (e : E) (m : Fin k → E) :
    mehlerKernelBounds_L1 E k X (h, e) m = h * X m := by
  simp [mehlerKernelBounds_L1]

private lemma mehlerKernelBounds_L2_apply (k : ℕ) (X : ContinuousMultilinearMap ℝ
    (fun _ : Fin (k + 1) => E) ℝ) (h : ℝ) (e : E) (m : Fin k → E) :
    mehlerKernelBounds_L2 E k X (h, e) m = X (Fin.cons e m) := by
  simp [mehlerKernelBounds_L2]

private lemma mehlerKernelBounds_norm_L1_apply_le (k : ℕ)
    (X : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖mehlerKernelBounds_L1 E k X‖ ≤ 1 * ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  obtain ⟨h, e⟩ := p
  rw [mehlerKernelBounds_L1_apply, norm_mul, one_mul, mul_comm ‖X‖, mul_assoc]
  refine mul_le_mul (norm_fst_le (h, e)) (X.le_opNorm m) (norm_nonneg _) (norm_nonneg _)

private lemma mehlerKernelBounds_norm_L2_apply_le (k : ℕ)
    (X : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ) :
    ‖mehlerKernelBounds_L2 E k X‖ ≤ 1 * ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  obtain ⟨h, e⟩ := p
  rw [mehlerKernelBounds_L2_apply, one_mul]
  refine (X.le_opNorm _).trans ?_
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  have : ‖e‖ ≤ ‖((h, e) : ℝ × E)‖ := norm_snd_le (h, e)
  have hp : 0 ≤ ∏ i : Fin k, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg (m i)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hp) (norm_nonneg _)

/-- `D H_{j,k} = L₁ H_{j+1,k} + L₂ H_{j,k+1}` on `Ω`. -/
private lemma mehlerKernelBounds_H_hasFDerivAt {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) (j k : ℕ) {x : ℝ × E} (hx : x ∈ Ω) :
    HasFDerivAt (mehlerKernelBounds_H G j k)
      (mehlerKernelBounds_L1 E k (mehlerKernelBounds_H G (j + 1) k x) +
        mehlerKernelBounds_L2 E k (mehlerKernelBounds_H G j (k + 1) x)) x := by
  convert (mehlerKernelBounds_H_differentiableAt hG j k hx).hasFDerivAt using 1
  refine ContinuousLinearMap.ext fun p => ?_
  ext m
  obtain ⟨h, e⟩ := p
  rw [mehlerKernelBounds_H_fderiv_apply hG j k hx, add_apply,
    add_apply, mehlerKernelBounds_L1_apply, mehlerKernelBounds_L2_apply]

/-- Iterating `D H_{j,k} = L₁ H_{j+1,k} + L₂ H_{j,k+1}` (Step 5 of Lemma 14.F): if
`‖H_{j+i,k+n-i}(x)‖ ≤ B` for `i ≤ n`, then `‖D^n H_{j,k}(x)‖ ≤ 2^n B`. -/
private lemma mehlerKernelBounds_norm_iteratedFDeriv_H_le {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) {x : ℝ × E} (hx : x ∈ Ω) (B : ℝ) :
    ∀ n j k, (∀ i ≤ n, ‖mehlerKernelBounds_H G (j + i) (k + (n - i)) x‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (mehlerKernelBounds_H G j k) x‖ ≤ 2 ^ n * B := by
  intro n
  induction n with
  | zero =>
    intro j k hB
    simpa using hB 0 le_rfl
  | succ n ih =>
    intro j k hB
    rw [← norm_iteratedFDeriv_fderiv]
    have hev : fderiv ℝ (mehlerKernelBounds_H G j k) =ᶠ[𝓝 x]
        (fun x => mehlerKernelBounds_L1 E k (mehlerKernelBounds_H G (j + 1) k x)) +
          fun x => mehlerKernelBounds_L2 E k (mehlerKernelBounds_H G j (k + 1) x) := by
      filter_upwards [mehlerKernelBounds_isOpen.mem_nhds hx] with x' hx'
      exact (mehlerKernelBounds_H_hasFDerivAt hG j k hx').fderiv
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
    have hc1 := (mehlerKernelBounds_H_contDiffAt hG (j + 1) k hx).of_le
      (m := (n : WithTop ℕ∞)) (mehlerKernelBounds_natCast_lt_top n).le
    have hc2 := (mehlerKernelBounds_H_contDiffAt hG j (k + 1) hx).of_le
      (m := (n : WithTop ℕ∞)) (mehlerKernelBounds_natCast_lt_top n).le
    have hc1' : ContDiffAt ℝ n (fun x => mehlerKernelBounds_L1 E k
        (mehlerKernelBounds_H G (j + 1) k x)) x :=
      (ContinuousLinearMap.contDiff _).contDiffAt.comp x hc1
    have hc2' : ContDiffAt ℝ n (fun x => mehlerKernelBounds_L2 E k
        (mehlerKernelBounds_H G j (k + 1) x)) x :=
      (ContinuousLinearMap.contDiff _).contDiffAt.comp x hc2
    rw [iteratedFDeriv_add_apply hc1' hc2']
    refine (norm_add_le _ _).trans ?_
    have b1 : ‖iteratedFDeriv ℝ n (fun x => mehlerKernelBounds_L1 E k
        (mehlerKernelBounds_H G (j + 1) k x)) x‖ ≤
        1 * ‖iteratedFDeriv ℝ n (mehlerKernelBounds_H G (j + 1) k) x‖ :=
      mehlerKernelBounds_norm_iteratedFDeriv_comp_le _ zero_le_one
        (fun X => mehlerKernelBounds_norm_L1_apply_le k X) hc1
    have b2 : ‖iteratedFDeriv ℝ n (fun x => mehlerKernelBounds_L2 E k
        (mehlerKernelBounds_H G j (k + 1) x)) x‖ ≤
        1 * ‖iteratedFDeriv ℝ n (mehlerKernelBounds_H G j (k + 1)) x‖ :=
      mehlerKernelBounds_norm_iteratedFDeriv_comp_le _ zero_le_one
        (fun X => mehlerKernelBounds_norm_L2_apply_le k X) hc2
    have i1 := ih (j + 1) k fun i hi => by
      have := hB (i + 1) (by omega)
      rwa [show j + (i + 1) = j + 1 + i by omega, show k + (n + 1 - (i + 1)) = k + (n - i) by
        omega] at this
    have i2 := ih j (k + 1) fun i hi => by
      have := hB i (by omega)
      rwa [show k + (n + 1 - i) = k + 1 + (n - i) by omega] at this
    rw [pow_succ]
    linarith

/-- The derivative along the line `u' ↦ (u', y)`. -/
private lemma mehlerKernelBounds_hasDerivAt_line {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {F : ℝ × E → X} {u : ℝ} {y : E} (hF : DifferentiableAt ℝ F (u, y)) :
    HasDerivAt (fun u' => F (u', y)) (fderiv ℝ F (u, y) ((1 : ℝ), (0 : E))) u :=
  hF.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u y))

/-- `H_{j,k}(u, y) = D^k_y H_{j,0}(u, y)`. -/
private lemma mehlerKernelBounds_iteratedFDeriv_slice {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    ∀ k (y : E), iteratedFDeriv ℝ k (fun y' => mehlerKernelBounds_H G j 0 (u, y') 0) y =
      mehlerKernelBounds_H G j k (u, y)
  | 0, y => by
    ext m
    rw [iteratedFDeriv_zero_apply]
    congr 1
    exact Subsingleton.elim _ _
  | k + 1, y => by
    have ih : iteratedFDeriv ℝ k (fun y' => mehlerKernelBounds_H G j 0 (u, y') 0) =
        fun y' => mehlerKernelBounds_H G j k (u, y') :=
      funext (mehlerKernelBounds_iteratedFDeriv_slice hG j hu k)
    have hx : (u, y) ∈ (Ω : Set (ℝ × E)) := ⟨hu, trivial⟩
    have hd := (mehlerKernelBounds_H_differentiableAt hG j k hx).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) u y)
    ext m
    rw [iteratedFDeriv_succ_apply_left, ih]
    erw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [mehlerKernelBounds_H_fderiv_inr hG j k _ hx, Fin.cons_self_tail]

private lemma mehlerKernelBounds_H_zero_apply (G : ℝ × E → ℝ) (k : ℕ) (x : ℝ × E)
    (m : Fin k → E) :
    mehlerKernelBounds_H G 0 k x m = iteratedFDeriv ℝ k G x (fun i => ((0 : ℝ), m i)) :=
  rfl

private lemma mehlerKernelBounds_H_zero_zero (G : ℝ × E → ℝ) (x : ℝ × E) (m : Fin 0 → E) :
    mehlerKernelBounds_H G 0 0 x m = G x := by
  simp [mehlerKernelBounds_H]

end Joint

/-! ### The generator in terms of `H` -/

section Generator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option quotPrecheck false in
local notation "Ω" => Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)

omit [FiniteDimensional ℝ E] in
/-- `H_{1,0} = ∂_u G`. -/
private lemma mehlerKernelBounds_H_one_zero {G : ℝ × E → ℝ} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω)
    {x : ℝ × E} (hx : x ∈ (Ω : Set (ℝ × E))) :
    mehlerKernelBounds_H G 1 0 x 0 = fderiv ℝ G x ((1 : ℝ), (0 : E)) := by
  have := mehlerKernelBounds_fderiv_clm_comp (ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 0 => E) ℝ 0) (mehlerKernelBounds_H_differentiableAt hG 0 0 hx)
    ((1 : ℝ), (0 : E))
  simp only [ContinuousMultilinearMap.apply_apply, mehlerKernelBounds_H_zero_zero] at this
  exact this.symm

/-- `A_y G = (v/2) Σ_i H_{0,2}[b_i, b_i] - (1/2) H_{0,1}[y]`. -/
private lemma mehlerKernelBounds_gen_eq_H {G : ℝ × E → ℝ} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω)
    (v : ℝ) {u : ℝ} (hu : 0 < u) (y : E) :
    v / 2 * Laplacian.laplacian (fun y' => G (u, y')) y -
        1 / 2 * inner ℝ y (gradient (fun y' => G (u, y')) y) =
      v / 2 * ∑ i, mehlerKernelBounds_H G 0 2 (u, y)
          ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] -
        1 / 2 * mehlerKernelBounds_H G 0 1 (u, y) ![y] := by
  have hslice : (fun y' => G (u, y')) = fun y' => mehlerKernelBounds_H G 0 0 (u, y') 0 :=
    funext fun y' => (mehlerKernelBounds_H_zero_zero G _ _).symm
  rw [hslice,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  simp only [mehlerKernelBounds_iteratedFDeriv_slice hG 0 hu]
  congr 2
  rw [gradient, real_inner_comm, InnerProductSpace.toDual_symm_apply,
    ← mehlerKernelBounds_iteratedFDeriv_slice hG 0 hu 1 y, iteratedFDeriv_one_apply]
  rfl

/-- If `∂_u G = A_y G` on `Ω`, then `H_{j+1,0} = (v/2) Σ_i H_{j,2}[b_i, b_i] - (1/2) H_{j,1}[y]`
(Step 2 of Lemma 14.F). -/
private lemma mehlerKernelBounds_H_succ_eq {G : ℝ × E → ℝ} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω)
    (v : ℝ) (hPDE : ∀ u > 0, ∀ y : E, HasDerivAt (fun u' => G (u', y))
      (v / 2 * Laplacian.laplacian (fun y' => G (u, y')) y -
        1 / 2 * inner ℝ y (gradient (fun y' => G (u, y')) y)) u) :
    ∀ j, ∀ x ∈ (Ω : Set (ℝ × E)), mehlerKernelBounds_H G (j + 1) 0 x 0 =
      v / 2 * ∑ i, mehlerKernelBounds_H G j 2 x
          ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] -
        1 / 2 * mehlerKernelBounds_H G j 1 x ![x.2]
  | 0, x, hx => by
    obtain ⟨u, y⟩ := x
    have hGd : DifferentiableAt ℝ G (u, y) :=
      (hG.contDiffAt (mehlerKernelBounds_isOpen.mem_nhds hx)).differentiableAt (by simp)
    rw [mehlerKernelBounds_H_one_zero hG hx,
      (mehlerKernelBounds_hasDerivAt_line hGd).unique (hPDE u hx.1 y),
      mehlerKernelBounds_gen_eq_H hG v hx.1 y]
  | j + 1, x, hx => by
    obtain ⟨u, y⟩ := x
    have hu : 0 < u := hx.1
    set b := stdOrthonormalBasis ℝ E
    -- the left side is the `u`-derivative of `H_{j+1,0}`
    have hL : HasDerivAt (fun u' => mehlerKernelBounds_H G (j + 1) 0 (u', y) 0)
        (mehlerKernelBounds_H G (j + 2) 0 (u, y) 0) u := by
      have := mehlerKernelBounds_fderiv_clm_comp (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin 0 => E) ℝ 0) (mehlerKernelBounds_H_differentiableAt hG (j + 1) 0 hx)
        ((1 : ℝ), (0 : E))
      simp only [ContinuousMultilinearMap.apply_apply] at this
      have h := mehlerKernelBounds_hasDerivAt_line (F := fun x => mehlerKernelBounds_H G (j + 1) 0
        x 0) ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ 0).differentiableAt.comp
          (u, y) (mehlerKernelBounds_H_differentiableAt hG (j + 1) 0 hx))
      rw [this] at h
      exact h
    -- the `u`-derivative of an evaluation of `H_{j,k}` is the evaluation of `H_{j+1,k}`
    have hev : ∀ k (m : Fin k → E), HasDerivAt (fun u' => mehlerKernelBounds_H G j k (u', y) m)
        (mehlerKernelBounds_H G (j + 1) k (u, y) m) u := by
      intro k m
      have := mehlerKernelBounds_fderiv_clm_comp (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin k => E) ℝ m) (mehlerKernelBounds_H_differentiableAt hG j k hx)
        ((1 : ℝ), (0 : E))
      simp only [ContinuousMultilinearMap.apply_apply] at this
      have h := mehlerKernelBounds_hasDerivAt_line (F := fun x => mehlerKernelBounds_H G j k x m)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ m).differentiableAt.comp
          (u, y) (mehlerKernelBounds_H_differentiableAt hG j k hx))
      rw [this] at h
      exact h
    have hR : HasDerivAt (fun u' => v / 2 * ∑ i, mehlerKernelBounds_H G j 2 (u', y) ![b i, b i] -
        1 / 2 * mehlerKernelBounds_H G j 1 (u', y) ![y])
        (v / 2 * ∑ i, mehlerKernelBounds_H G (j + 1) 2 (u, y) ![b i, b i] -
          1 / 2 * mehlerKernelBounds_H G (j + 1) 1 (u, y) ![y]) u :=
      ((HasDerivAt.fun_sum fun i _ => hev 2 ![b i, b i]).const_mul _).sub
        ((hev 1 ![y]).const_mul _)
    have heq : (fun u' => mehlerKernelBounds_H G (j + 1) 0 (u', y) 0) =ᶠ[𝓝 u]
        fun u' => v / 2 * ∑ i, mehlerKernelBounds_H G j 2 (u', y) ![b i, b i] -
          1 / 2 * mehlerKernelBounds_H G j 1 (u', y) ![y] := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with u' hu'
      exact mehlerKernelBounds_H_succ_eq hG v hPDE j (u', y) ⟨hu', trivial⟩
    exact hL.unique (hR.congr_of_eventuallyEq heq)

end Generator

/-! ### Lemma 14.F -/

section KernelBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option quotPrecheck false in
local notation "Ω" => Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)

private lemma mehlerKernelBounds_ouA_pos (u : ℝ) : 0 < ouA u := Real.exp_pos _

private lemma mehlerKernelBounds_ouA_le_one {u : ℝ} (hu : 0 ≤ u) : ouA u ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

private lemma mehlerKernelBounds_ouS_pos {u : ℝ} (hu : 0 < u) : 0 < ouS u := by
  rw [ouS, sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)

private lemma mehlerKernelBounds_ouS_mono {u₁ u : ℝ} (hu : u₁ ≤ u) : ouS u₁ ≤ ouS u := by
  rw [ouS, ouS]; linarith [Real.exp_le_exp.2 (neg_le_neg hu)]

private lemma mehlerKernelBounds_one_le_kappa {v u₁ : ℝ} (hv : 0 < v) (hu₁ : 0 < u₁) :
    1 ≤ mehlerKernelBoundsKappa v u₁ := by
  have := mehlerKernelBounds_ouS_pos hu₁
  rw [mehlerKernelBoundsKappa]
  have : 0 ≤ 1 / (v * ouS u₁) := by positivity
  have : 0 ≤ 1 / Real.sqrt (v * ouS u₁) := by positivity
  linarith

omit [FiniteDimensional ℝ E] in
/-- The joint kernel `x = (u, y) ↦ K(u, y, w)` is smooth on `Ω`. -/
private lemma mehlerKernelBounds_contDiffOn {v : ℝ} (hv : 0 < v) (w : E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) Ω := by
  have h := mehlerKernel_contDiffOn (E := E) hv
  have hm : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ × E => (x.1, x.2, w) := by fun_prop
  exact h.comp hm.contDiffOn fun x hx => ⟨hx.1, trivial⟩

omit [FiniteDimensional ℝ E] in
/-- The `y`-slices of the kernel are smooth. -/
private lemma mehlerKernelBounds_contDiff_slice {v : ℝ} (hv : 0 < v) {u : ℝ} (hu : 0 < u)
    (w : E) : ContDiff ℝ (⊤ : ℕ∞) fun y => mehlerKernel v u y w :=
  (mehlerKernelBounds_contDiffOn hv w).comp_contDiff (f := fun y : E => (u, y)) (by fun_prop)
    fun _ => ⟨hu, trivial⟩

/-- Step 1 of Lemma 14.F: `N_k(K(u, ·, w))(y) ≤ t_k Λ^k K(u, y, w)` for `u ≥ u₁`. -/
private lemma mehlerKernelBounds_norm_iteratedFDeriv_slice_le {v : ℝ} (hv : 0 < v) {u₁ u : ℝ}
    (hu₁ : 0 < u₁) (hu : u₁ ≤ u) (y w : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y' => mehlerKernel v u y' w) y‖ ≤
      mehlerKernelBoundsT k * (mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)) ^ k *
        mehlerKernel v u y w := by
  have hu0 : 0 < u := hu₁.trans_le hu
  have hs := mehlerKernelBounds_ouS_pos hu0
  have hs₁ := mehlerKernelBounds_ouS_pos hu₁
  have hss := mehlerKernelBounds_ouS_mono hu
  have ha := mehlerKernelBounds_ouA_pos u
  have ha1 := mehlerKernelBounds_ouA_le_one hu0.le
  set a := ouA u
  set α := a / (v * ouS u)
  set c : E →L[ℝ] ℝ := innerSL ℝ (α • w)
  set Lℓ : E →L[ℝ] E →L[ℝ] ℝ := (-(α * a)) • innerSL ℝ
  have hℓ : ∀ y', c + Lℓ y' = innerSL ℝ (α • (w - a • y')) := fun y' => by
    ext z
    simp only [c, Lℓ, add_apply, smul_apply,
      innerSL_apply_apply, inner_sub_left, inner_smul_left, smul_eq_mul, RCLike.conj_to_real]
    have : (innerSL ℝ y') z = inner ℝ y' z := rfl
    rw [this]
    ring
  have hfd : ∀ y', fderiv ℝ (fun y'' => mehlerKernel v u y'' w) y' =
      mehlerKernel v u y' w • (c + Lℓ y') := fun y' => by
    rw [(mehlerKernel_hasGradientAt v u y' w).hasFDerivAt.fderiv, hℓ]
    ext z
    simp [InnerProductSpace.toDual_apply_apply, α, a]
  set Λ := mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)
  have hκ := mehlerKernelBounds_one_le_kappa hv hu₁
  have hvs : 1 / (v * ouS u) ≤ 1 / (v * ouS u₁) :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hα : α ≤ 1 / (v * ouS u₁) := by
    calc α = a * (1 / (v * ouS u)) := by rw [mul_one_div]
      _ ≤ 1 * (1 / (v * ouS u₁)) := by gcongr
      _ = _ := one_mul _
  have hα0 : 0 ≤ α := by positivity
  have hκ' : 1 / (v * ouS u₁) ≤ mehlerKernelBoundsKappa v u₁ := by
    rw [mehlerKernelBoundsKappa]
    have : 0 ≤ 1 / Real.sqrt (v * ouS u₁) := by positivity
    linarith
  have hL1 : ‖c + Lℓ y‖ ≤ Λ := by
    rw [hℓ, innerSL_apply_norm, norm_smul, Real.norm_of_nonneg hα0]
    have h1 : ‖w - a • y‖ ≤ ‖w‖ + ‖y‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) ha1
    calc α * ‖w - a • y‖ ≤ mehlerKernelBoundsKappa v u₁ * (‖w‖ + ‖y‖) :=
          mul_le_mul (hα.trans hκ') h1 (norm_nonneg _) (by positivity)
      _ ≤ Λ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  have hL2 : ‖Lℓ‖ ≤ Λ ^ 2 := by
    have h1 : ‖Lℓ‖ ≤ α * a := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
      rw [smul_apply, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg (by positivity)]
    have h2 : α * a ≤ mehlerKernelBoundsKappa v u₁ :=
      (mul_le_of_le_one_right hα0 ha1).trans (hα.trans hκ')
    have h3 : mehlerKernelBoundsKappa v u₁ ≤ Λ := by
      apply le_mul_of_one_le_right (by linarith)
      linarith [norm_nonneg y, norm_nonneg w]
    have h4 : 1 ≤ Λ := hκ.trans h3
    nlinarith
  have := mehlerKernelBounds_norm_iteratedFDeriv_le_of_affine
    (mehlerKernelBounds_contDiff_slice hv hu0 w) c Lℓ hfd y hL1 hL2 k
  rwa [abs_of_pos (mehlerKernel_pos v hu0 y w)] at this

/-- Step 4 of Lemma 14.F, i.e. Lemma 14.F(b) for `∂_u^j D_y^k K`:
`‖∂_u^j D_y^k K(u, y, w)‖ ≤ c_{j,k} Λ^{k+2j} K(u, y, w)` for `u ≥ u₁`. -/
private lemma mehlerKernelBounds_norm_H_le {v : ℝ} (hv : 0 < v) {u₁ u : ℝ} (hu₁ : 0 < u₁)
    (hu : u₁ ≤ u) (y w : E) :
    ∀ j k, ‖mehlerKernelBounds_H (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) j k (u, y)‖ ≤
      mehlerKernelBoundsC v (Module.finrank ℝ E) j k *
        (mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)) ^ (k + 2 * j) *
          mehlerKernel v u y w := by
  have hu0 : 0 < u := hu₁.trans_le hu
  set G := fun x : ℝ × E => mehlerKernel v x.1 x.2 w with hGdef
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω := mehlerKernelBounds_contDiffOn hv w
  have hPDE : ∀ u > 0, ∀ y : E, HasDerivAt (fun u' => G (u', y))
      (v / 2 * Laplacian.laplacian (fun y' => G (u, y')) y -
        1 / 2 * inner ℝ y (gradient (fun y' => G (u, y')) y)) u :=
    fun u hu y => hasDerivAt_mehlerKernel hv hu y w
  have hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun y' => mehlerKernelBounds_H G j 0 (u, y') 0 := fun j =>
    ((ContinuousLinearMap.contDiff _).comp_contDiffOn
      (mehlerKernelBounds_H_contDiffOn hG j 0)).comp_contDiff
      (g := fun x => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ 0
        (mehlerKernelBounds_H G j 0 x))
      (f := fun y' : E => (u, y')) (by fun_prop) fun _ => ⟨hu0, trivial⟩
  have hgen : ∀ j, (fun y' => mehlerKernelBounds_H G (j + 1) 0 (u, y') 0) =
      mehlerKernelBounds_gen v (fun y' => mehlerKernelBounds_H G j 0 (u, y') 0) := fun j => by
    funext y'
    rw [mehlerKernelBounds_H_succ_eq hG v hPDE j (u, y') ⟨hu0, trivial⟩, mehlerKernelBounds_gen,
      mehlerKernelBounds_trace_apply, ← mehlerKernelBounds_iteratedFDeriv_slice hG j hu0 2 y',
      ← mehlerKernelBounds_iteratedFDeriv_slice hG j hu0 1 y']
    simp only [iteratedFDeriv_two_apply, iteratedFDeriv_one_apply]
    rfl
  have hκ := mehlerKernelBounds_one_le_kappa hv hu₁
  have hΛ : 1 ≤ mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖) :=
    one_le_mul_of_one_le_of_one_le hκ (by linarith [norm_nonneg y, norm_nonneg w])
  have hy : ‖y‖ ≤ mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖) := by
    calc ‖y‖ ≤ 1 * (1 + ‖y‖ + ‖w‖) := by linarith [norm_nonneg w]
      _ ≤ _ := mul_le_mul_of_nonneg_right hκ (by positivity)
  have hK := (mehlerKernel_pos v hu0 y w).le
  intro j
  induction j with
  | zero =>
    intro k
    rw [← mehlerKernelBounds_iteratedFDeriv_slice hG 0 hu0 k y]
    have : (fun y' => mehlerKernelBounds_H G 0 0 (u, y') 0) = fun y' => mehlerKernel v u y' w :=
      funext fun y' => mehlerKernelBounds_H_zero_zero G _ _
    rw [this]
    simpa [mehlerKernelBoundsC] using
      mehlerKernelBounds_norm_iteratedFDeriv_slice_le hv hu₁ hu y w k
  | succ j ih =>
    intro k
    rw [← mehlerKernelBounds_iteratedFDeriv_slice hG (j + 1) hu0 k y, hgen j]
    exact mehlerKernelBounds_norm_iteratedFDeriv_gen_le_of hv.le (hφ j) y hΛ hy hK j
      (fun m => by rw [mehlerKernelBounds_iteratedFDeriv_slice hG j hu0 m y]; exact ih m) k

/-- **Lemma 14.F(c).** For `u ≥ u₁ > 0` and `y, w ∈ E`, the `n`-th Fréchet derivative of
`x = (u, y) ↦ K(u, y, w)` on `ℝ × E` (with the norm `‖(h, e)‖ = max (|h|, |e|)`) satisfies
`‖D^n_x K(u, y, w)‖ ≤ 2^n ĉ_n Λ(y, w)^{2n} K(u, y, w)`, where `Λ(y, w) = κ(u₁) (1 + |y| + |w|)`
and the constants `ĉ_n`, `κ(u₁)` are those of §14.4 (with `σ² = v`). -/
theorem norm_iteratedFDeriv_mehlerKernel_le {v : ℝ} (hv : 0 < v) {u₁ : ℝ} (hu₁ : 0 < u₁)
    (n : ℕ) {u : ℝ} (hu : u₁ ≤ u) (y w : E) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) (u, y)‖ ≤
      2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
        (mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)) ^ (2 * n) * mehlerKernel v u y w := by
  have hu0 : 0 < u := hu₁.trans_le hu
  set G := fun x : ℝ × E => mehlerKernel v x.1 x.2 w with hGdef
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G Ω := mehlerKernelBounds_contDiffOn hv w
  have hx : (u, y) ∈ (Ω : Set (ℝ × E)) := ⟨hu0, trivial⟩
  set Λ := mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)
  have hκ := mehlerKernelBounds_one_le_kappa hv hu₁
  have hΛ : 1 ≤ Λ :=
    one_le_mul_of_one_le_of_one_le hκ (by linarith [norm_nonneg y, norm_nonneg w])
  have hK := (mehlerKernel_pos v hu0 y w).le
  have hc := (mehlerKernelBounds_H_contDiffAt hG 0 0 hx).of_le
    (m := (n : WithTop ℕ∞)) (mehlerKernelBounds_natCast_lt_top n).le
  have h1 : ‖iteratedFDeriv ℝ n (fun x => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ
      0 (mehlerKernelBounds_H G 0 0 x)) (u, y)‖ ≤
      1 * ‖iteratedFDeriv ℝ n (mehlerKernelBounds_H G 0 0) (u, y)‖ :=
    mehlerKernelBounds_norm_iteratedFDeriv_comp_le _ zero_le_one (fun X => by
      rw [ContinuousMultilinearMap.apply_apply, one_mul]
      simp) hc
  have hGe : (fun x => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ 0
      (mehlerKernelBounds_H G 0 0 x)) = G :=
    funext fun x => mehlerKernelBounds_H_zero_zero G x 0
  rw [hGe, one_mul] at h1
  refine h1.trans ?_
  have h2 := mehlerKernelBounds_norm_iteratedFDeriv_H_le hG hx
    (mehlerKernelBoundsCHat v (Module.finrank ℝ E) n * Λ ^ (2 * n) * mehlerKernel v u y w) n 0 0
    (fun i hi => by
      rw [zero_add, zero_add]
      refine (mehlerKernelBounds_norm_H_le hv hu₁ hu y w i (n - i)).trans ?_
      have hc0 := mehlerKernelBoundsC_nonneg hv.le (Module.finrank ℝ E) i (n - i)
      have hle := mehlerKernelBoundsC_le_cHat v (Module.finrank ℝ E) hi
      have hp : Λ ^ (n - i + 2 * i) ≤ Λ ^ (2 * n) := pow_le_pow_right₀ hΛ (by omega)
      gcongr
      exact hc0.trans hle)
  calc _ ≤ _ := h2
    _ = _ := by ring

end KernelBounds

/-! ### Lemma 14.G -/

/-- The `x`-derivatives of a jointly smooth function of `(x, w)` are the joint derivatives
restricted to the `x`-directions. -/
private lemma mehlerKernelBounds_iteratedFDeriv_left {X Y F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {P : X × Y → F} {U : Set (X × Y)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) P U) :
    ∀ n (x : X) (w : Y), (x, w) ∈ U → iteratedFDeriv ℝ n (fun x' => P (x', w)) x =
      (iteratedFDeriv ℝ n P (x, w)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ X Y)
  | 0, x, w, _ => by ext m; simp
  | n + 1, x, w, hxw => by
    have hev : iteratedFDeriv ℝ n (fun x' => P (x', w)) =ᶠ[𝓝 x] fun x' =>
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin n => ContinuousLinearMap.inl ℝ X Y)) (iteratedFDeriv ℝ n P (x', w)) := by
      have : ∀ᶠ x' in 𝓝 x, (x', w) ∈ U :=
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hxw)
      filter_upwards [this] with x' hx'
      exact mehlerKernelBounds_iteratedFDeriv_left hU hP n x' w hx'
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n P) (x, w) :=
      (hP.contDiffAt (hU.mem_nhds hxw)).differentiableAt_iteratedFDeriv
        (mehlerKernelBounds_natCast_lt_top n)
    have hd' : DifferentiableAt ℝ (fun x' => iteratedFDeriv ℝ n P (x', w)) x :=
      hd.comp x (differentiableAt_id.prodMk (differentiableAt_const w))
    ext m
    rw [iteratedFDeriv_succ_apply_left, hev.fderiv_eq,
      mehlerKernelBounds_fderiv_clm_comp _ hd']
    have h2 : fderiv ℝ (fun x' => iteratedFDeriv ℝ n P (x', w)) x (m 0) =
        fderiv ℝ (iteratedFDeriv ℝ n P) (x, w) (m 0, 0) := by
      rw [fderiv_fun_comp x hd (differentiableAt_id.prodMk (differentiableAt_const w)),
        ((hasFDerivAt_prodMk_left (𝕜 := ℝ) x w).fderiv)]
      rfl
    rw [h2]
    simp only [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_succ_apply_left]
    rfl

section KernelIntegral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option quotPrecheck false in
local notation "Ω" => Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `x ∈ Ω`, `w ↦ D^n_x K(x, w)` is continuous. -/
private lemma mehlerKernelBounds_continuous_iteratedFDeriv {v : ℝ} (hv : 0 < v) (n : ℕ)
    {x : ℝ × E} (hx : x ∈ (Ω : Set (ℝ × E))) :
    Continuous fun w : E => iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x := by
  set P : (ℝ × E) × E → ℝ := fun p => mehlerKernel v p.1.1 p.1.2 p.2
  have hU : IsOpen ((Ω : Set (ℝ × E)) ×ˢ (Set.univ : Set E)) :=
    mehlerKernelBounds_isOpen.prod isOpen_univ
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) P ((Ω : Set (ℝ × E)) ×ˢ (Set.univ : Set E)) := by
    have h := mehlerKernel_contDiffOn (E := E) hv
    have hm : ContDiff ℝ (⊤ : ℕ∞) fun p : (ℝ × E) × E => (p.1.1, p.1.2, p.2) := by fun_prop
    exact h.comp hm.contDiffOn fun p hp => ⟨hp.1.1, trivial⟩
  have heq : (fun w : E => iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x) =
      fun w => (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin n => ContinuousLinearMap.inl ℝ (ℝ × E) E)) (iteratedFDeriv ℝ n P (x, w)) :=
    funext fun w => mehlerKernelBounds_iteratedFDeriv_left hU hP n x w ⟨hx, trivial⟩
  rw [heq]
  refine (ContinuousLinearMap.continuous _).comp (continuous_iff_continuousAt.2 fun w => ?_)
  have hxw : (x, w) ∈ (Ω : Set (ℝ × E)) ×ˢ (Set.univ : Set E) := ⟨hx, trivial⟩
  have hc := (hP.contDiffAt (hU.mem_nhds hxw)).continuousAt_iteratedFDeriv
    (k := n) (mehlerKernelBounds_natCast_lt_top n).le
  exact hc.comp (continuous_const.prodMk continuous_id).continuousAt

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Lemma 14.G(a), domination (14.4).** For `u ≥ u₁ > 0`, `|y| ≤ r`, `w ∈ E` and `|h| ≤ C`:
`‖D^n_x K(u, y, w) h(w)‖ ≤ G_{n,u₁,r}(w) =
C 2^n ĉ_n κ(u₁)^{2n} s_{u₁}^{-d/2} e^{r²/(2v)} (1 + r + |w|)^{2n}` (with `σ² = v`). -/
theorem mehlerKernelBounds_norm_smul_iteratedFDeriv_le {v : ℝ} (hv : 0 < v) {u₁ r : ℝ}
    (hu₁ : 0 < u₁) (n : ℕ) {h : E → ℝ} {C : ℝ} (hC : ∀ w, |h w| ≤ C) {u : ℝ} (hu : u₁ ≤ u)
    {y : E} (hy : ‖y‖ ≤ r) (w : E) :
    ‖h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) (u, y)‖ ≤
      C * 2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
        mehlerKernelBoundsKappa v u₁ ^ (2 * n) * ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (r ^ 2 / (2 * v)) * (1 + r + ‖w‖) ^ (2 * n) := by
  have hu0 : 0 < u := hu₁.trans_le hu
  have hr : 0 ≤ r := (norm_nonneg y).trans hy
  have hs₁ := mehlerKernelBounds_ouS_pos hu₁
  have hκ := mehlerKernelBounds_one_le_kappa hv hu₁
  have hc : 0 ≤ mehlerKernelBoundsCHat v (Module.finrank ℝ E) n :=
    (mehlerKernelBoundsC_nonneg hv.le _ 0 n).trans
      (by simpa using mehlerKernelBoundsC_le_cHat v (Module.finrank ℝ E) (Nat.zero_le n))
  have hK0 := (mehlerKernel_pos v hu0 y w).le
  have hK : mehlerKernel v u y w ≤ ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (r ^ 2 / (2 * v)) := by
    refine (mehlerKernel_le hv hu0 y w).trans ?_
    have h1 : ouS u ^ (-(Module.finrank ℝ E : ℝ) / 2) ≤
        ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hs₁ (mehlerKernelBounds_ouS_mono hu)
        (by have := (Module.finrank ℝ E).cast_nonneg (α := ℝ); linarith)
    have h2 : Real.exp (‖y‖ ^ 2 / (2 * v)) ≤ Real.exp (r ^ 2 / (2 * v)) := by
      gcongr
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  have hΛ : (mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)) ^ (2 * n) ≤
      mehlerKernelBoundsKappa v u₁ ^ (2 * n) * (1 + r + ‖w‖) ^ (2 * n) := by
    rw [mul_pow]
    gcongr
  rw [norm_smul, Real.norm_eq_abs]
  have hD := norm_iteratedFDeriv_mehlerKernel_le hv hu₁ n hu y w
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC w)
  calc |h w| * ‖iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) (u, y)‖
      ≤ C * (2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
          (mehlerKernelBoundsKappa v u₁ * (1 + ‖y‖ + ‖w‖)) ^ (2 * n) * mehlerKernel v u y w) :=
        mul_le_mul (hC w) hD (norm_nonneg _) hCn
    _ ≤ C * (2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
          (mehlerKernelBoundsKappa v u₁ ^ (2 * n) * (1 + r + ‖w‖) ^ (2 * n)) *
            (ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (r ^ 2 / (2 * v)))) := by
        gcongr
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `w ↦ (a + |w|)^N` is integrable if all moments `∫ |w|^m dρ` are finite. -/
private lemma mehlerKernelBounds_integrable_add_pow {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) (a : ℝ) (N : ℕ) :
    Integrable (fun w => (a + ‖w‖) ^ N) ρ := by
  simp_rw [add_pow]
  exact integrable_finsetSum _ fun m _ => ((hρ (N - m)).const_mul (a ^ m)).mul_const _

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Lemma 14.G(a), integrability of `G_{n,u₁,r}`.** If `ρ` has all moments
`∫ |w|^m dρ < ∞`, then `G_{n,u₁,r} ∈ L¹(ρ)` and
`∫ G_{n,u₁,r} dρ ≤ C 2^n ĉ_n κ(u₁)^{2n} s_{u₁}^{-d/2} e^{r²/(2v)} (1 + r)^{2n} M_{2n}(ρ)`, with
`M_p(ρ) = ∫ (1 + |w|)^p dρ`. -/
theorem mehlerKernelBounds_integrable_dom {v : ℝ} (hv : 0 < v) {u₁ : ℝ} (hu₁ : 0 < u₁)
    {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) (n : ℕ) {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 ≤ r) :
    Integrable (fun w => C * 2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
        mehlerKernelBoundsKappa v u₁ ^ (2 * n) * ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (r ^ 2 / (2 * v)) * (1 + r + ‖w‖) ^ (2 * n)) ρ ∧
      ∫ w, C * 2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
        mehlerKernelBoundsKappa v u₁ ^ (2 * n) * ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (r ^ 2 / (2 * v)) * (1 + r + ‖w‖) ^ (2 * n) ∂ρ ≤
        C * 2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
          mehlerKernelBoundsKappa v u₁ ^ (2 * n) * ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
            Real.exp (r ^ 2 / (2 * v)) * (1 + r) ^ (2 * n) *
              ∫ w, (1 + ‖w‖) ^ (2 * n) ∂ρ := by
  set A := C * 2 ^ n * mehlerKernelBoundsCHat v (Module.finrank ℝ E) n *
    mehlerKernelBoundsKappa v u₁ ^ (2 * n) * ouS u₁ ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (r ^ 2 / (2 * v))
  have hI : Integrable (fun w => A * (1 + r + ‖w‖) ^ (2 * n)) ρ :=
    (mehlerKernelBounds_integrable_add_pow hρ (1 + r) (2 * n)).const_mul A
  have hA : 0 ≤ A := by
    have hc : 0 ≤ mehlerKernelBoundsCHat v (Module.finrank ℝ E) n :=
      (mehlerKernelBoundsC_nonneg hv.le _ 0 n).trans
        (by simpa using mehlerKernelBoundsC_le_cHat v (Module.finrank ℝ E) (Nat.zero_le n))
    have := Real.rpow_nonneg (mehlerKernelBounds_ouS_pos hu₁).le
      (-(Module.finrank ℝ E : ℝ) / 2)
    have := (mehlerKernelBounds_one_le_kappa hv hu₁)
    have : 0 ≤ mehlerKernelBoundsKappa v u₁ ^ (2 * n) := by positivity
    simp only [A]
    positivity
  refine ⟨hI, ?_⟩
  rw [mul_assoc A, ← integral_const_mul, ← integral_const_mul]
  refine integral_mono hI
    (((mehlerKernelBounds_integrable_add_pow hρ 1 (2 * n)).const_mul _).const_mul _) fun w => ?_
  simp only
  rw [← mul_pow]
  gcongr
  nlinarith [norm_nonneg w]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `D(D^n f)(x)` is `D^{n+1} f(x)` with its first argument separated. -/
private lemma mehlerKernelBounds_fderiv_iteratedFDeriv {X F : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : X → F) (n : ℕ) (x : X) :
    fderiv ℝ (iteratedFDeriv ℝ n f) x =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) F
        (iteratedFDeriv ℝ (n + 1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]

private lemma mehlerKernelBounds_aestronglyMeasurable {v : ℝ} (hv : 0 < v) {h : E → ℝ}
    (hh : Measurable h) (ρ : Measure E) (n : ℕ) {x : ℝ × E} (hx : x ∈ (Ω : Set (ℝ × E))) :
    AEStronglyMeasurable
      (fun w => h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x) ρ :=
  hh.aestronglyMeasurable.smul
    (mehlerKernelBounds_continuous_iteratedFDeriv hv n hx).aestronglyMeasurable

private lemma mehlerKernelBounds_integrable_smul {v : ℝ} (hv : 0 < v) {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {h : E → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ w, |h w| ≤ C) (n : ℕ) {x : ℝ × E} (hx : x ∈ (Ω : Set (ℝ × E))) :
    Integrable (fun w => h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x)
      ρ := by
  obtain ⟨u, y⟩ := x
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  exact (mehlerKernelBounds_integrable_dom hv hx.1 hρ n hCn (norm_nonneg y)).1.mono'
    (mehlerKernelBounds_aestronglyMeasurable hv hh ρ n hx)
    (ae_of_all _ fun w => mehlerKernelBounds_norm_smul_iteratedFDeriv_le hv hx.1 n hC le_rfl
      le_rfl w)

/-- Differentiation under the integral sign in the proof of Lemma 14.G(b). -/
private lemma mehlerKernelBounds_hasFDerivAt_integral {v : ℝ} (hv : 0 < v) {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {h : E → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ w, |h w| ≤ C) (n : ℕ) {x₀ : ℝ × E} (hx₀ : x₀ ∈ (Ω : Set (ℝ × E))) :
    HasFDerivAt
      (fun x => ∫ w, h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x ∂ρ)
      (∫ w, h w • fderiv ℝ (iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w))
        x₀ ∂ρ) x₀ := by
  obtain ⟨u₀, y₀⟩ := x₀
  have hu₀ : 0 < u₀ := hx₀.1
  have hCn : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set ε := min (u₀ / 2) 1
  have hε : 0 < ε := lt_min (by linarith) one_pos
  have hball : ∀ x ∈ Metric.ball (u₀, y₀) ε, u₀ / 2 ≤ x.1 ∧ ‖x.2‖ ≤ ‖y₀‖ + 1 := by
    intro x hx
    rw [Metric.mem_ball, Prod.dist_eq] at hx
    have h1 : dist x.1 u₀ < u₀ / 2 := (le_max_left _ _).trans_lt (hx.trans_le (min_le_left _ _))
    have h2 : dist x.2 y₀ < 1 := (le_max_right _ _).trans_lt (hx.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at h1
    refine ⟨by linarith [(abs_lt.1 h1).1], ?_⟩
    rw [dist_eq_norm] at h2
    calc ‖x.2‖ = ‖y₀ + (x.2 - y₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y₀‖ + ‖x.2 - y₀‖ := norm_add_le _ _
      _ ≤ ‖y₀‖ + 1 := by linarith
  have hballΩ : ∀ x ∈ Metric.ball (u₀, y₀) ε, x ∈ (Ω : Set (ℝ × E)) := fun x hx =>
    ⟨show (0 : ℝ) < x.1 by linarith [(hball x hx).1], trivial⟩
  have hint := mehlerKernelBounds_integrable_dom hv (half_pos hu₀) hρ (n + 1) hCn
    (r := ‖y₀‖ + 1) (by positivity)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x w => h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x)
    (F' := fun x w => h w • fderiv ℝ (iteratedFDeriv ℝ n
      (fun x : ℝ × E => mehlerKernel v x.1 x.2 w)) x)
    (Metric.ball_mem_nhds _ hε) ?_
    (mehlerKernelBounds_integrable_smul hv hρ hh hC n hx₀) ?_ ?_ hint.1 ?_
  · filter_upwards [Metric.ball_mem_nhds _ hε] with x hx
    exact mehlerKernelBounds_aestronglyMeasurable hv hh ρ n (hballΩ x hx)
  · have h1 := mehlerKernelBounds_aestronglyMeasurable hv hh ρ (n + 1) hx₀
    have h2 := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => ℝ × E)
      ℝ).continuous.comp_aestronglyMeasurable h1
    refine h2.congr (ae_of_all _ fun w => ?_)
    simp only [map_smul, mehlerKernelBounds_fderiv_iteratedFDeriv]
  · refine ae_of_all _ fun w x hx => ?_
    obtain ⟨u, y⟩ := x
    rw [norm_smul, mehlerKernelBounds_fderiv_iteratedFDeriv, LinearIsometryEquiv.norm_map,
      ← norm_smul]
    exact mehlerKernelBounds_norm_smul_iteratedFDeriv_le hv (half_pos hu₀) (n + 1) hC
      (hball _ hx).1 (hball _ hx).2 w
  · refine ae_of_all _ fun w x hx => ?_
    have hc := (mehlerKernelBounds_contDiffOn hv w).contDiffAt
      (mehlerKernelBounds_isOpen.mem_nhds (hballΩ x hx))
    exact ((hc.differentiableAt_iteratedFDeriv
      (mehlerKernelBounds_natCast_lt_top n)).hasFDerivAt).const_smul (h w)

/-- The derivative formula of Lemma 14.G(b), for all orders. -/
private lemma mehlerKernelBounds_iteratedFDeriv_integral_eq {v : ℝ} (hv : 0 < v)
    {ρ : Measure E} (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {h : E → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ w, |h w| ≤ C) :
    ∀ n, ∀ x ∈ (Ω : Set (ℝ × E)),
      iteratedFDeriv ℝ n (fun x : ℝ × E => ∫ w, mehlerKernel v x.1 x.2 w * h w ∂ρ) x =
        ∫ w, h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x ∂ρ
  | 0, x, hx => by
    ext m
    rw [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.integral_apply
      (mehlerKernelBounds_integrable_smul hv hρ hh hC 0 hx)]
    simp only [smul_apply, iteratedFDeriv_zero_apply, smul_eq_mul]
    exact integral_congr_ae (ae_of_all _ fun w => mul_comm _ _)
  | n + 1, x, hx => by
    have hev : iteratedFDeriv ℝ n (fun x : ℝ × E => ∫ w, mehlerKernel v x.1 x.2 w * h w ∂ρ)
        =ᶠ[𝓝 x] fun x => ∫ w, h w • iteratedFDeriv ℝ n
          (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x ∂ρ := by
      filter_upwards [mehlerKernelBounds_isOpen.mem_nhds hx] with x' hx'
      exact mehlerKernelBounds_iteratedFDeriv_integral_eq hv hρ hh hC n x' hx'
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq,
      (mehlerKernelBounds_hasFDerivAt_integral hv hρ hh hC n hx).fderiv]
    have := ContinuousLinearEquiv.integral_comp_comm (μ := ρ) (𝕜 := ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => ℝ × E)
        ℝ).symm.toContinuousLinearEquiv
      (fun w => h w • fderiv ℝ (iteratedFDeriv ℝ n
        (fun x : ℝ × E => mehlerKernel v x.1 x.2 w)) x)
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at this
    rw [← this]
    congr 1

/-- **Lemma 14.G(b), derivative formula.** Let `ρ` be a Borel measure on `E` with
`∫ |w|^m dρ < ∞` for every `m ∈ ℕ` (so `ρ` is finite and `M_p(ρ) < ∞` for all `p ≥ 0`), and let `h`
be Borel with `|h| ≤ C`. For `x ∈ Ω = (0, ∞) × E` and every `n`, the Bochner integral of
`n`-linear forms `∫ h(w) D^n_x K(x, w) ρ(dw)` converges absolutely and equals
`D^n Ψ_h(x)`, where `Ψ_h(u, y) = ∫ K(u, y, w) h(w) ρ(dw)`. -/
theorem iteratedFDeriv_kernelIntegral {v : ℝ} (hv : 0 < v) {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {h : E → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ w, |h w| ≤ C) (n : ℕ) {x : ℝ × E} (hx : x ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) :
    Integrable (fun w => h w • iteratedFDeriv ℝ n
        (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x) ρ ∧
      iteratedFDeriv ℝ n (fun x : ℝ × E => ∫ w, mehlerKernel v x.1 x.2 w * h w ∂ρ) x =
        ∫ w, h w • iteratedFDeriv ℝ n (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x ∂ρ :=
  ⟨mehlerKernelBounds_integrable_smul hv hρ hh hC n hx,
    mehlerKernelBounds_iteratedFDeriv_integral_eq hv hρ hh hC n x hx⟩

/-- **Lemma 14.G(b), smoothness.** Under the hypotheses of `iteratedFDeriv_kernelIntegral`,
`Ψ_h(u, y) = ∫ K(u, y, w) h(w) ρ(dw)` is `C^∞` on `Ω = (0, ∞) × E`. -/
theorem contDiffOn_kernelIntegral {v : ℝ} (hv : 0 < v) {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {h : E → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ w, |h w| ≤ C) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × E => ∫ w, mehlerKernel v x.1 x.2 w * h w ∂ρ)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  set Ψ := fun x : ℝ × E => ∫ w, mehlerKernel v x.1 x.2 w * h w ∂ρ
  have hdiff : ∀ m : ℕ, DifferentiableOn ℝ (fun x => iteratedFDerivWithin ℝ m Ψ Ω x) Ω := by
    intro m x hx
    have hev : (fun x => iteratedFDerivWithin ℝ m Ψ Ω x) =ᶠ[𝓝 x] fun x => ∫ w, h w •
        iteratedFDeriv ℝ m (fun x : ℝ × E => mehlerKernel v x.1 x.2 w) x ∂ρ := by
      filter_upwards [mehlerKernelBounds_isOpen.mem_nhds hx] with x' hx'
      rw [iteratedFDerivWithin_of_isOpen m mehlerKernelBounds_isOpen hx']
      exact mehlerKernelBounds_iteratedFDeriv_integral_eq hv hρ hh hC m x' hx'
    exact ((mehlerKernelBounds_hasFDerivAt_integral hv hρ hh hC m
      hx).differentiableAt.congr_of_eventuallyEq hev).differentiableWithinAt
  exact contDiffOn_of_continuousOn_differentiableOn (fun m _ => (hdiff m).continuousOn)
    fun m _ => hdiff m

/-- **Lemma 14.G(b), the equation.** Under the hypotheses of `iteratedFDeriv_kernelIntegral`,
`∂_u Ψ_h = A Ψ_h` on `Ω`, with `A = (v/2) Δ - (1/2) ⟨y, ∇⟩` acting on the variable `y`. -/
theorem mehlerKernelBounds_hasDerivAt_kernelIntegral {v : ℝ} (hv : 0 < v) {ρ : Measure E}
    (hρ : ∀ m : ℕ, Integrable (fun w => ‖w‖ ^ m) ρ) {h : E → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ w, |h w| ≤ C) {u : ℝ} (hu : 0 < u) (y : E) :
    HasDerivAt (fun u' => ∫ w, mehlerKernel v u' y w * h w ∂ρ)
      (v / 2 * Laplacian.laplacian (fun y' => ∫ w, mehlerKernel v u y' w * h w ∂ρ) y -
        1 / 2 * inner ℝ y (gradient (fun y' => ∫ w, mehlerKernel v u y' w * h w ∂ρ) y)) u := by
  set Ψ := fun x : ℝ × E => ∫ w, mehlerKernel v x.1 x.2 w * h w ∂ρ
  set K := fun (w : E) (x : ℝ × E) => mehlerKernel v x.1 x.2 w
  have hx : (u, y) ∈ (Ω : Set (ℝ × E)) := ⟨hu, trivial⟩
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω := contDiffOn_kernelIntegral hv hρ hh hC
  have hΨd : DifferentiableAt ℝ Ψ (u, y) :=
    (hΨ.contDiffAt (mehlerKernelBounds_isOpen.mem_nhds hx)).differentiableAt (by simp)
  -- evaluations of `D^k Ψ` are integrals of evaluations of `D^k K`
  have hev : ∀ k (m : Fin k → ℝ × E), iteratedFDeriv ℝ k Ψ (u, y) m =
      ∫ w, h w * iteratedFDeriv ℝ k (K w) (u, y) m ∂ρ := by
    intro k m
    obtain ⟨hI, hD⟩ := iteratedFDeriv_kernelIntegral hv hρ hh hC k hx
    rw [hD, ContinuousMultilinearMap.integral_apply hI]
    rfl
  have hint : ∀ k (m : Fin k → ℝ × E),
      Integrable (fun w => h w * iteratedFDeriv ℝ k (K w) (u, y) m) ρ := fun k m =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) ℝ m).integrable_comp
      (iteratedFDeriv_kernelIntegral hv hρ hh hC k hx).1
  have hH : ∀ k (m : Fin k → E), mehlerKernelBounds_H Ψ 0 k (u, y) m =
      ∫ w, h w * mehlerKernelBounds_H (K w) 0 k (u, y) m ∂ρ := fun k m => by
    simp only [mehlerKernelBounds_H_zero_apply]
    exact hev k _
  -- the kernel identity `∂_u K = A_y K`, in terms of `H`
  set b := stdOrthonormalBasis ℝ E
  have hKeq : ∀ w, fderiv ℝ (K w) (u, y) ((1 : ℝ), (0 : E)) =
      v / 2 * ∑ i, mehlerKernelBounds_H (K w) 0 2 (u, y) ![b i, b i] -
        1 / 2 * mehlerKernelBounds_H (K w) 0 1 (u, y) ![y] := fun w => by
    have hG := mehlerKernelBounds_contDiffOn hv w
    rw [← mehlerKernelBounds_H_one_zero hG hx]
    exact mehlerKernelBounds_H_succ_eq hG v (fun u hu y => hasDerivAt_mehlerKernel hv hu y w) 0
      (u, y) hx
  have hd1 : fderiv ℝ Ψ (u, y) ((1 : ℝ), (0 : E)) =
      ∫ w, h w * fderiv ℝ (K w) (u, y) ((1 : ℝ), (0 : E)) ∂ρ := by
    have := hev 1 ![((1 : ℝ), (0 : E))]
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] at this
    exact this
  refine (mehlerKernelBounds_hasDerivAt_line hΨd).congr_deriv ?_
  rw [mehlerKernelBounds_gen_eq_H hΨ v hu y, hd1]
  have hi2 : ∀ i, Integrable (fun w => h w * mehlerKernelBounds_H (K w) 0 2 (u, y)
      ![b i, b i]) ρ := fun i => by
    simp only [mehlerKernelBounds_H_zero_apply]
    exact hint 2 _
  have hi1 : Integrable (fun w => h w * mehlerKernelBounds_H (K w) 0 1 (u, y) ![y]) ρ := by
    simp only [mehlerKernelBounds_H_zero_apply]
    exact hint 1 _
  calc ∫ w, h w * fderiv ℝ (K w) (u, y) ((1 : ℝ), (0 : E)) ∂ρ
      = ∫ w, (v / 2 * ∑ i, h w * mehlerKernelBounds_H (K w) 0 2 (u, y) ![b i, b i] -
          1 / 2 * (h w * mehlerKernelBounds_H (K w) 0 1 (u, y) ![y])) ∂ρ :=
        integral_congr_ae (ae_of_all _ fun w => by
          dsimp only
          rw [hKeq w, mul_sub, ← mul_assoc, mul_comm (h w) (v / 2), mul_assoc, Finset.mul_sum]
          ring)
    _ = v / 2 * ∑ i, ∫ w, h w * mehlerKernelBounds_H (K w) 0 2 (u, y) ![b i, b i] ∂ρ -
          1 / 2 * ∫ w, h w * mehlerKernelBounds_H (K w) 0 1 (u, y) ![y] ∂ρ := by
        rw [integral_sub ((integrable_finsetSum _ fun i _ => hi2 i).const_mul _)
          (hi1.const_mul _), integral_const_mul, integral_const_mul,
          integral_finsetSum _ fun i _ => hi2 i]
    _ = _ := by simp only [hH]; rfl

end KernelIntegral

end Rigidity
