import Rigidity.Edge.Decorrelation
import Rigidity.Edge.EdgeEvent
import Rigidity.Edge.EntryIntegral
import Rigidity.Edge.Hybrid
import Rigidity.Edge.HybridLaw
import Rigidity.Edge.Inputs
import Rigidity.Edge.Params
import Rigidity.Edge.Resample
import Rigidity.Edge.SmoothCount
import Rigidity.Ensemble.Basic
import Rigidity.Resolvent.Basic

/-!
# Green function comparison at the edge

Numbers refer to NP v1.1; the original is cited as [EYY, …].

This file proves Proposition 11.19 (one replacement step) and Theorem 11.20, the form (6.25) of
[EYY, Theorem 6.3]: for two ensembles `M^v`, `M^w` with the assumptions 𝔄 and matching moments
of order at most two, energies `E₁ ≤ E₂` in the edge window, `η = N^{-2/3-ε_g}` and `F ∈ C³` with
`|F^{(k)}| ≤ C_F` (`k ≤ 3`),
`|𝔼^v F(X(H)) - 𝔼^w F(X(H))| ≤ C₄ C_F N^{-1/6+4ε_g}`, where
`X(H) = (N/π) ∫_{E₁}^{E₂} Im m(y + iη) dy` (Definition 11.7).

Proposition 11.19 is stated for one step that replaces the law at a pair `p` in an ensemble `M`
whose entry laws are taken from `M^v` or `M^w`; the steps `M_{k-1} → M_k` of Definition 11.3 are
the case `M = M_{k-1}`, `p = p_k`.  Its proof follows Steps 1–5 of the proof of Proposition 11.19:
* Step 1 (Lemma 11.4 (ii)): the difference of the two expectations is the integral of
  `D^v - D^w` over the law of `Q = H^{[p]}`;
* Step 2 (Lemma 11.15 (b)): the complement of `𝒢_p` costs `O(C_F N^{-20})`;
* Steps 3–5 (Corollary 11.17, Lemma 11.18, Lemma 11.16 (a)): on `𝒢_p` the second order terms
  cancel by (2.40), and the third order term is bounded by decorrelation.

The constants `C₃`, `C₄` are existential and depend on `(ϑ, C₀)` only.  The hypotheses
`EdgeLarge` and `EdgeInputs` stand for the threshold `N ≥ N₁(Par, ε_g)` and for (BB1), (BB2);
the statements are conditional on them.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. Entries and continuity -/

private lemma comparison_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

private lemma comparison_continuous_toC : Continuous (toC : 𝕜 → ℂ) := by
  have : (toC : 𝕜 → ℂ) =
      fun y => ((RCLike.re y : ℝ) : ℂ) + ((RCLike.im y : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [toC]
  rw [this]
  fun_prop

/-- The Bochner integral commutes with `toC`. -/
private lemma comparison_integral_toC {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → 𝕜) : ∫ a, toC (f a) ∂μ = toC (∫ a, f a ∂μ) := by
  by_cases hf : Integrable f μ
  · have hf' : Integrable (fun a => toC (f a)) μ :=
      hf.norm.mono' (comparison_continuous_toC.comp_aestronglyMeasurable hf.1)
        (Eventually.of_forall fun a => by rw [comparison_norm_toC])
    apply Complex.ext
    · have h1 := integral_re hf'
      have h2 := integral_re hf
      simp only [RCLike.re_to_complex] at h1
      rw [← h1]
      change ∫ a, RCLike.re (f a) ∂μ = RCLike.re (∫ a, f a ∂μ)
      exact h2
    · have h1 := integral_im hf'
      have h2 := integral_im hf
      simp only [RCLike.im_to_complex] at h1
      rw [← h1]
      change ∫ a, RCLike.im (f a) ∂μ = RCLike.im (∫ a, f a ∂μ)
      exact h2
  · have hinv : Continuous fun w : ℂ => ((w.re : ℝ) : 𝕜) + ((w.im : ℝ) : 𝕜) * RCLike.I := by
      fun_prop
    have hf' : ¬ Integrable (fun a => toC (f a)) μ := by
      intro h
      refine hf (h.norm.mono' ?_ (Eventually.of_forall fun a => by rw [comparison_norm_toC]))
      have : f = fun a => (((toC (f a)).re : ℝ) : 𝕜) + (((toC (f a)).im : ℝ) : 𝕜) * RCLike.I := by
        funext a
        simp [toC, RCLike.re_add_im]
      rw [this]
      exact hinv.comp_aestronglyMeasurable h.1
    rw [integral_undef hf, integral_undef hf']
    apply Complex.ext <;> simp [toC]

private lemma comparison_continuous_toMatrixC {N : ℕ} :
    Continuous fun x : Pair N → 𝕜 => toMatrixC x := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · exact comparison_continuous_toC.comp (continuous_apply _)
  · exact comparison_continuous_toC.comp (continuous_star.comp (continuous_apply _))
  · exact comparison_continuous_toC.comp (RCLike.continuous_ofReal.comp
      (RCLike.continuous_re.comp (continuous_apply _)))

private lemma comparison_continuous_update {N : ℕ} (p : Pair N) :
    Continuous fun x : Pair N → 𝕜 => Function.update x p 0 :=
  continuous_id.update p continuous_const

private lemma comparison_mk'_self {N : ℕ} (p : Pair N) : Pair.mk' p.1.1 p.1.2 = p := by
  unfold Pair.mk'
  simp [p.2]

private lemma comparison_mk'_diag {N : ℕ} {p : Pair N} (h : p.1.1 = p.1.2) :
    Pair.mk' p.1.1 p.1.1 = p := by
  conv_lhs => arg 2; rw [h]
  exact comparison_mk'_self p

private lemma comparison_abs_le {S A B K : ℝ} (h : |S - A + B| ≤ K) : |S| ≤ K + |A| + |B| := by
  have := abs_le.1 h
  rw [abs_le]
  constructor <;> linarith [neg_abs_le A, le_abs_self A, neg_abs_le B, le_abs_self B]

/-! ### 2. Step 1: reduction to one entry -/

/-- `x ↦ ∫ f(x with x_p := v) dν(v)` is continuous and bounded by the bound of `f`. -/
private lemma comparison_integral_update {N : ℕ} (U : Ensemble 𝕜 N) (p : Pair N)
    (f : (Pair N → 𝕜) → ℝ) (hf : Continuous f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    Continuous (fun x => ∫ v, f (Function.update x p v) ∂U.law p) ∧
      ∀ x, |∫ v, f (Function.update x p v) ∂U.law p| ≤ C := by
  have hjoint : Continuous fun z : (Pair N → 𝕜) × 𝕜 => f (Function.update z.1 p z.2) :=
    hf.comp (continuous_fst.update p continuous_snd)
  refine ⟨?_, fun x => ?_⟩
  · refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_)
      (integrable_const C) (Eventually.of_forall fun v => ?_)
    · exact (hjoint.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hfC _
    · exact hjoint.comp (Continuous.prodMk continuous_id continuous_const)
  · rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C) (Eventually.of_forall fun v =>
      (by rw [Real.norm_eq_abs]; exact hfC _ : ‖f (Function.update x p v)‖ ≤ C))).trans ?_
    simp

/-- Lemma 11.4 (ii), last statement, combined with the resampling of the entry at `p`. -/
private lemma comparison_integral_hybrid {N : ℕ} (M U : Ensemble 𝕜 N) (p : Pair N)
    (f : (Pair N → 𝕜) → ℝ) (hf : Continuous f) (C : ℝ) (hfC : ∀ x, |f x| ≤ C) :
    ∫ x, f x ∂(M.hybrid U {p}).prodLaw =
      ∫ x, (∫ v, f (Function.update x p v) ∂U.law p) ∂M.prodLaw := by
  have hint : Integrable f (M.hybrid U {p}).prodLaw :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfC x)
  have hlaw : (M.hybrid U {p}).law p = U.law p := by
    change (if p ∈ ({p} : Set (Pair N)) then U.law p else M.law p) = U.law p
    simp
  rw [Ensemble.integral_eq_integral_update (M.hybrid U {p}) p f hint, hlaw]
  refine Ensemble.integral_hybrid_singleton M U p _
    (comparison_integral_update U p f hf C hfC).1.stronglyMeasurable fun x w => ?_
  simp only [Function.update_idem]

/-! ### 3. Steps 3–4: the third order term -/

section Third

variable {ϑ δm δp C₀ A₀ εg E₁ E₂ : ℝ} {N : ℕ}

/-- The quantity `𝔈_{cd,i}` of Step 4: on `𝒢_p`, `|𝔼[1_𝒢 F'(X(Q)) R_cd(z_i) g(z_i)]| ≤
(37/4) C_F Ψ²`. -/
private lemma comparison_E_le (hϑ : 0 < ϑ) (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) (hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N) (hE : E₁ ≤ E₂)
    (hE₁ : E₁ ∈ edgeWindow εg N) (hE₂ : E₂ ∈ edgeWindow εg N) (M : Ensemble 𝕜 N)
    (hM : M.Assumptions ϑ δm δp C₀) (p : Pair N) (hp : p.1.1 ≠ p.1.2) (F : ℝ → ℝ) (CF : ℝ)
    (hF : ContDiff ℝ 3 F) (hFb : ∀ k : ℕ, k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) {y : ℝ}
    (hy : y = E₁ ∨ y = E₂) {c d : Fin N}
    (hcd : (c = p.1.1 ∧ d = p.1.2) ∨ (c = p.1.2 ∧ d = p.1.1)) :
    IntegrableOn (fun x : Pair N → 𝕜 =>
        ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
            (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
          resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
          pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩) p.1.1 p.1.2)
      {x | toMatrixC (Function.update x p 0) ∈
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} M.prodLaw ∧
    ‖∫ x in {x | toMatrixC (Function.update x p 0) ∈
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2},
        ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
            (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
          resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
          pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩) p.1.1 p.1.2
        ∂M.prodLaw‖ ≤ 37 / 4 * CF * edgePsi εg N ^ 2 := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hη : 0 < edgeEta εg N := Real.rpow_pos_of_pos hNpos _
  have hΨ : 0 < edgePsi εg N := by unfold edgePsi; positivity
  have hΨ8 : edgePsi εg N ≤ 1 / 8 := hN.psi_le
  have hF1 : ∀ x, |iteratedDeriv 1 F x| ≤ CF := hFb 1 (by norm_num)
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF1 0)
  have hcd' : c ≠ d := by
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact fun h => hp h.symm
  have hcm : c ∈ ({p.1.1, p.1.2} : Set (Fin N)) := by
    rcases hcd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hdm : d ∈ ({p.1.1, p.1.2} : Set (Fin N)) := by
    rcases hcd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hyI : y ∈ Set.Icc E₁ E₂ := by
    rcases hy with rfl | rfl
    · exact ⟨le_rfl, hE⟩
    · exact ⟨hE, le_rfl⟩
  have hy' : y ∈ ({E₁, E₂} : Set ℝ) := by
    rcases hy with rfl | rfl <;> simp
  set G := {x : Pair N → 𝕜 | toMatrixC (Function.update x p 0) ∈
    goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} with hGdef
  have hQc : Continuous fun x : Pair N → 𝕜 => toMatrixC (Function.update x p 0) :=
    comparison_continuous_toMatrixC.comp (comparison_continuous_update p)
  have hG : MeasurableSet G :=
    ((isClosed_goodSet hη _ _ _ _ _).preimage hQc).measurableSet
  have hΦc : Continuous fun x : Pair N → 𝕜 => ((iteratedDeriv 1 F (smoothCount E₁ E₂
      (edgeEta εg N) (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hF.continuous_iteratedDeriv 1 (by norm_num)).comp
      ((continuous_smoothCount_toMatrixC hη hE).comp (comparison_continuous_update p)))
  have hRc : ∀ k l : Fin N, Continuous fun x : Pair N → 𝕜 =>
      resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ k l := fun k l =>
    (continuous_resolventMat_toMatrixC (z := ⟨y, edgeEta εg N⟩) hη k l).comp
      (comparison_continuous_update p)
  have hgc : Continuous fun x : Pair N → 𝕜 =>
      pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩) p.1.1 p.1.2 := by
    unfold pairG
    exact ((hRc _ _).mul (hRc _ _)).sub ((hRc _ _).mul (hRc _ _))
  -- bounds on `𝒢_p`
  have hRb : ∀ x ∈ G,
      ‖resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d‖ ≤
        edgePsi εg N := by
    intro x hx
    have h := hx.2 c hcm d hdm y hyI
    rwa [Matrix.add_apply, Matrix.one_apply_ne hcd', add_zero] at h
  have hgb : ∀ x ∈ G,
      ‖pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩)
          p.1.1 p.1.2 - 1‖ ≤ 9 / 4 * edgePsi εg N ∧
        ‖pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩)
          p.1.1 p.1.2‖ ≤ 4 / 3 := fun x hx =>
    norm_pairG_le hη hΨ hΨ8 hx.1 hp (endpointGood_of_mem_goodSet hE hx) hy'
  have hΦb : ∀ x : Pair N → 𝕜, ‖((iteratedDeriv 1 F (smoothCount E₁ E₂
      (edgeEta εg N) (toMatrixC (Function.update x p 0))) : ℝ) : ℂ)‖ ≤ CF := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hF1 _
  have hfin : M.prodLaw G < ⊤ := measure_lt_top _ _
  have hGle : M.prodLaw.real G ≤ 1 := measureReal_le_one
  -- the two pieces
  have hint1 : IntegrableOn (fun x : Pair N → 𝕜 =>
      ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d) G M.prodLaw := by
    refine IntegrableOn.of_bound hfin (hΦc.mul (hRc c d)).aestronglyMeasurable
      (CF * edgePsi εg N) ((ae_restrict_iff' hG).2 (Eventually.of_forall fun x hx => ?_))
    rw [norm_mul]
    exact mul_le_mul (hΦb x) (hRb x hx) (norm_nonneg _) hCF
  have hint2 : IntegrableOn (fun x : Pair N → 𝕜 =>
      ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
        (pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩)
          p.1.1 p.1.2 - 1)) G M.prodLaw := by
    refine IntegrableOn.of_bound hfin
      ((hΦc.mul (hRc c d)).mul (hgc.sub continuous_const)).aestronglyMeasurable
      (CF * edgePsi εg N * (9 / 4 * edgePsi εg N))
      ((ae_restrict_iff' hG).2 (Eventually.of_forall fun x hx => ?_))
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hΦb x) (hRb x hx) (norm_nonneg _) hCF) (hgb x hx).1
      (norm_nonneg _) (mul_nonneg hCF hΨ.le)
  have hsplit : ∀ x : Pair N → 𝕜,
      ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
        pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩) p.1.1 p.1.2 =
      ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d +
      ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
        (pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩)
          p.1.1 p.1.2 - 1) := fun x => by ring
  simp_rw [hsplit]
  refine ⟨hint1.add hint2, ?_⟩
  rw [integral_add hint1 hint2]
  -- Lemma 11.18 with `Φ = F'`
  have hΦ1 : ContDiff ℝ 1 (iteratedDeriv 1 F) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv' 1 1 (hF.of_le (by norm_num))
  have hΦd : ∀ x, |deriv (iteratedDeriv 1 F) x| ≤ CF := fun x => by
    rw [← iteratedDeriv_succ]; exact hFb 2 (by norm_num) x
  have hdec := norm_integral_decor_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hp
    (iteratedDeriv 1 F) CF hΦ1 hF1 hΦd hy hcd
  rw [integral_indicator hG] at hdec
  have hrem := norm_setIntegral_le_of_norm_le_const hfin (fun x hx => by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hΦb x) (hRb x hx) (norm_nonneg _) hCF) (hgb x hx).1
      (norm_nonneg _) (mul_nonneg hCF hΨ.le) :
    ∀ x ∈ G, ‖((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
        (pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩)
          p.1.1 p.1.2 - 1)‖ ≤ CF * edgePsi εg N * (9 / 4 * edgePsi εg N))
  have h0 : 0 ≤ CF * edgePsi εg N * (9 / 4 * edgePsi εg N) := by positivity
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 7 * CF * edgePsi εg N ^ 2 + CF * edgePsi εg N * (9 / 4 * edgePsi εg N) * 1 :=
        add_le_add hdec (hrem.trans (mul_le_mul_of_nonneg_left hGle h0))
    _ = 37 / 4 * CF * edgePsi εg N ^ 2 := by ring

/-- Step 4: `|𝔼[1_𝒢 F'(X(Q)) 𝔗₃(Q; ν)]| ≤ (37/π) |μ₃| C_F Ψ²` (11.b3:T3int), (11.b3:third). -/
private lemma comparison_third_le (hϑ : 0 < ϑ) (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) (hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N) (hE : E₁ ≤ E₂)
    (hE₁ : E₁ ∈ edgeWindow εg N) (hE₂ : E₂ ∈ edgeWindow εg N) (M : Ensemble 𝕜 N)
    (hM : M.Assumptions ϑ δm δp C₀) (p : Pair N) (hp : p.1.1 ≠ p.1.2) (F : ℝ → ℝ) (CF : ℝ)
    (hF : ContDiff ℝ 3 F) (hFb : ∀ k : ℕ, k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) (μ3 : ℂ) :
    IntegrableOn (fun x : Pair N → 𝕜 =>
        iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0))) *
          entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2 μ3)
      {x | toMatrixC (Function.update x p 0) ∈
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} M.prodLaw ∧
    |∫ x in {x | toMatrixC (Function.update x p 0) ∈
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2},
        iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0))) *
          entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2 μ3
        ∂M.prodLaw| ≤ 37 / π * ‖μ3‖ * CF * edgePsi εg N ^ 2 := by
  set G := {x : Pair N → 𝕜 | toMatrixC (Function.update x p 0) ∈
    goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} with hGdef
  set e : Fin N → Fin N → ℝ → (Pair N → 𝕜) → ℂ := fun c d y x =>
    ((iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) : ℝ) : ℂ) *
      resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d *
      pairG (resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩) p.1.1 p.1.2
    with he
  have hba : (p.1.2 = p.1.1 ∧ p.1.1 = p.1.2) ∨ (p.1.2 = p.1.2 ∧ p.1.1 = p.1.1) :=
    Or.inr ⟨rfl, rfl⟩
  have hab : (p.1.1 = p.1.1 ∧ p.1.2 = p.1.2) ∨ (p.1.1 = p.1.2 ∧ p.1.2 = p.1.1) :=
    Or.inl ⟨rfl, rfl⟩
  obtain ⟨i1, b1⟩ := comparison_E_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hp F CF hF hFb
    (Or.inr rfl) hba
  obtain ⟨i2, b2⟩ := comparison_E_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hp F CF hF hFb
    (Or.inr rfl) hab
  obtain ⟨i3, b3⟩ := comparison_E_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hp F CF hF hFb
    (Or.inl rfl) hba
  obtain ⟨i4, b4⟩ := comparison_E_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hp F CF hF hFb
    (Or.inl rfl) hab
  have hpt : (fun x : Pair N → 𝕜 =>
      iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0))) *
        entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2 μ3) =
      fun x => -π⁻¹ * (μ3 * e p.1.2 p.1.1 E₂ x + star μ3 * e p.1.1 p.1.2 E₂ x -
        (μ3 * e p.1.2 p.1.1 E₁ x + star μ3 * e p.1.1 p.1.2 E₁ x)).im := by
    funext x
    have key : ∀ (r : ℝ) (w : ℂ), r * (-π⁻¹ * w.im) = -π⁻¹ * ((r : ℂ) * w).im := by
      intro r w
      simp [Complex.mul_im]
      ring
    simp only [entryT3, he]
    rw [key]
    congr 2
    ring
  have j1 : Integrable (fun x => μ3 * e p.1.2 p.1.1 E₂ x) (M.prodLaw.restrict G) :=
    Integrable.const_mul i1 μ3
  have j2 : Integrable (fun x => star μ3 * e p.1.1 p.1.2 E₂ x) (M.prodLaw.restrict G) :=
    Integrable.const_mul i2 (star μ3)
  have j3 : Integrable (fun x => μ3 * e p.1.2 p.1.1 E₁ x) (M.prodLaw.restrict G) :=
    Integrable.const_mul i3 μ3
  have j4 : Integrable (fun x => star μ3 * e p.1.1 p.1.2 E₁ x) (M.prodLaw.restrict G) :=
    Integrable.const_mul i4 (star μ3)
  have j12 : Integrable (fun x => μ3 * e p.1.2 p.1.1 E₂ x + star μ3 * e p.1.1 p.1.2 E₂ x)
      (M.prodLaw.restrict G) := j1.add j2
  have j34 : Integrable (fun x => μ3 * e p.1.2 p.1.1 E₁ x + star μ3 * e p.1.1 p.1.2 E₁ x)
      (M.prodLaw.restrict G) := j3.add j4
  have hh : Integrable (fun x => μ3 * e p.1.2 p.1.1 E₂ x + star μ3 * e p.1.1 p.1.2 E₂ x -
      (μ3 * e p.1.2 p.1.1 E₁ x + star μ3 * e p.1.1 p.1.2 E₁ x)) (M.prodLaw.restrict G) :=
    j12.sub j34
  rw [hpt]
  refine ⟨Integrable.const_mul (hh.im) _, ?_⟩
  rw [integral_const_mul]
  have him := integral_im hh
  simp only [RCLike.im_to_complex] at him
  rw [him, integral_sub j12 j34, integral_add j1 j2, integral_add j3 j4,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hpi : 0 < π := Real.pi_pos
  set A := 37 / 4 * CF * edgePsi εg N ^ 2
  have hw : ‖μ3 * ∫ x in G, e p.1.2 p.1.1 E₂ x ∂M.prodLaw +
      star μ3 * ∫ x in G, e p.1.1 p.1.2 E₂ x ∂M.prodLaw -
      (μ3 * ∫ x in G, e p.1.2 p.1.1 E₁ x ∂M.prodLaw +
        star μ3 * ∫ x in G, e p.1.1 p.1.2 E₁ x ∂M.prodLaw)‖ ≤ 4 * (‖μ3‖ * A) := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_
    simp only [norm_mul, norm_star]
    have h0 := norm_nonneg μ3
    nlinarith [mul_le_mul_of_nonneg_left b1 h0, mul_le_mul_of_nonneg_left b2 h0,
      mul_le_mul_of_nonneg_left b3 h0, mul_le_mul_of_nonneg_left b4 h0]
  rw [abs_mul, abs_neg, abs_inv, abs_of_pos hpi]
  calc π⁻¹ * |(_ : ℂ).im| ≤ π⁻¹ * (4 * (‖μ3‖ * A)) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hw) (inv_nonneg.2 hpi.le)
    _ = 37 / π * ‖μ3‖ * CF * edgePsi εg N ^ 2 := by
        simp only [A]; field_simp

end Third

/-- Proposition 11.19, for the step that replaces the law at `p` in an ensemble `M` whose laws
are taken from `Mv` or `Mw`. -/
theorem hybrid_step_le (ϑ C₀ : ℝ) (hϑ : 0 < ϑ) (hC₀ : 0 < C₀) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (δm δp A₀ εg : ℝ), 0 < εg → εg ≤ 1 / 10 → ∀ N : ℕ,
      EdgeLarge ϑ C₀ A₀ εg N → EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N →
      ∀ E₁ E₂ : ℝ, E₁ ≤ E₂ → E₁ ∈ edgeWindow εg N → E₂ ∈ edgeWindow εg N →
      ∀ (F : ℝ → ℝ) (CF : ℝ), ContDiff ℝ 3 F →
      (∀ k : ℕ, k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) →
      ∀ Mv Mw : Ensemble 𝕜 N, Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ →
      Ensemble.MomentMatch2 Mv Mw →
      ∀ M : Ensemble 𝕜 N, (∀ q, M.law q = Mv.law q ∨ M.law q = Mw.law q) → ∀ p : Pair N,
      |∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) ∂(M.hybrid Mv {p}).prodLaw -
          ∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) ∂(M.hybrid Mw {p}).prodLaw| ≤
        C₃ * CF * (if p.1.1 = p.1.2 then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
          else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) := by
  obtain ⟨C₂, hC₂, hent⟩ := entry_integral_le (𝕜 := 𝕜) ϑ C₀ hϑ hC₀
  obtain ⟨m3, hm3, hmom⟩ := exists_moment_le (𝕜 := 𝕜) ϑ hϑ 3
  have hC₀3 : 0 ≤ C₀ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  refine ⟨2 * C₂ + 396 * m3 * C₀ ^ ((3 : ℝ) / 2) + 8, by positivity, ?_⟩
  intro δm δp A₀ εg hεg hεg' N hN hIn E₁ E₂ hE hE₁ hE₂ F CF hF hFb Mv Mw hv hw hvw M hMlaw p
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hη : 0 < edgeEta εg N := Real.rpow_pos_of_pos hNpos _
  have hF0 : ∀ x, |F x| ≤ CF := fun x => by simpa using hFb 0 (by norm_num) x
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF0 0)
  have hM : M.Assumptions ϑ δm δp C₀ := Ensemble.Assumptions.of_law_mem hv hw hvw M hMlaw
  have hfc : Continuous fun x : Pair N → 𝕜 =>
      F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) :=
    hF.continuous.comp (continuous_smoothCount_toMatrixC hη hE)
  have hfb : ∀ x : Pair N → 𝕜, |F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x))| ≤ CF :=
    fun x => hF0 _
  -- Step 1
  rw [comparison_integral_hybrid M Mv p _ hfc CF hfb,
    comparison_integral_hybrid M Mw p _ hfc CF hfb]
  obtain ⟨hgvc, hgvb⟩ := comparison_integral_update Mv p _ hfc CF hfb
  obtain ⟨hgwc, hgwb⟩ := comparison_integral_update Mw p _ hfc CF hfb
  have hgvi := Integrable.of_bound (μ := M.prodLaw) hgvc.aestronglyMeasurable CF
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgvb x)
  have hgwi := Integrable.of_bound (μ := M.prodLaw) hgwc.aestronglyMeasurable CF
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgwb x)
  rw [← integral_sub hgvi hgwi]
  set G := {x : Pair N → 𝕜 | toMatrixC (Function.update x p 0) ∈
    goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} with hGdef
  have hQc : Continuous fun x : Pair N → 𝕜 => toMatrixC (Function.update x p 0) :=
    comparison_continuous_toMatrixC.comp (comparison_continuous_update p)
  have hG : MeasurableSet G :=
    ((isClosed_goodSet hη _ _ _ _ _).preimage hQc).measurableSet
  have hGle : M.prodLaw.real G ≤ 1 := measureReal_le_one
  have hΔi : Integrable (fun x => (∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p) M.prodLaw := hgvi.sub hgwi
  rw [← integral_add_compl hG hΔi]
  -- Step 2: the bad set
  have hbadμ : M.prodLaw Gᶜ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ (-20 : ℝ)) :=
    prodLaw_not_goodSet_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p
  have hbad : |∫ x in Gᶜ, ((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p) ∂M.prodLaw| ≤
      2 * CF * (2 * (N : ℝ) ^ (-20 : ℝ)) := by
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := 2 * CF) (measure_lt_top _ _)
      fun x _ => ?_).trans ?_
    · rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by linarith [hgvb x, hgwb x])
    · exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_le_of_le_ofReal (by positivity) hbadμ) (by positivity)
  -- Step 3: one entry, on the good set
  have hD : ∀ U : Ensemble 𝕜 N, U.Assumptions ϑ δm δp C₀ → ∀ x ∈ G,
      |(∫ v, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p v))) ∂U.law p) -
          F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0))) -
          entryQ2 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2 F
            (∫ y, ‖y‖ ^ 2 ∂U.law p) (∫ y, toC y ^ 2 ∂U.law p) -
          (if p.1.1 = p.1.2 then 0 else
            iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
                (toMatrixC (Function.update x p 0))) *
              entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
                (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂U.law p))| ≤
        C₂ * CF * (if p.1.1 = p.1.2 then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
          else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) := by
    intro U hU x hx
    have hi0 : Integrable (fun v => F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p v)))) (U.law p) :=
      Integrable.of_bound (hfc.comp (continuous_const.update p continuous_id)).aestronglyMeasurable
        CF (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hfb _)
    have hcongr : (fun v => F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p v)))) = fun v => F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0) + entryMat p.1.1 p.1.2 (toC v))) := by
      funext v
      rw [toMatrixC_eq_update_add (Function.update x p v) p, Function.update_idem,
        Function.update_self]
    rw [hcongr] at hi0 ⊢
    have hsub : (∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0) + entryMat p.1.1 p.1.2 (toC v))) ∂U.law p) -
        F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0))) =
        ∫ v, (F (smoothCount E₁ E₂ (edgeEta εg N)
          (toMatrixC (Function.update x p 0) + entryMat p.1.1 p.1.2 (toC v))) -
          F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)))) ∂U.law p := by
      rw [integral_sub hi0 (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [hsub]
    have hreal : p.1.1 = p.1.2 → ∀ᵐ y ∂U.law p, RCLike.im y = 0 := fun h => by
      have := hU.diagReal p.1.1
      rwa [comparison_mk'_diag h] at this
    have hσ : ∫ y, ‖y‖ ^ 2 ∂U.law p ≤ C₀ / N := by
      have := hU.boundC p.1.1 p.1.2
      rwa [Ensemble.var, comparison_mk'_self] at this
    exact hent A₀ εg hεg hεg' N hN E₁ E₂ hE p _ hx F CF hF hFb (U.law p) hreal hσ
      (hU.subexp p) (hU.meanZero p)
  -- (2.40) with `(l, u) = (1, 1), (0, 2)`
  have h11 : ∫ y, ‖y‖ ^ 2 ∂Mv.law p = ∫ y, ‖y‖ ^ 2 ∂Mw.law p := hvw.varPair_eq p
  have h20 : ∫ y, toC y ^ 2 ∂Mv.law p = ∫ y, toC y ^ 2 ∂Mw.law p := by
    have h := hvw p 0 2 (by norm_num)
    simp only [pow_zero, one_mul] at h
    have e : ∀ U : Ensemble 𝕜 N, ∫ y, toC y ^ 2 ∂U.law p = toC (∫ y, y ^ 2 ∂U.law p) :=
      fun U => by
        rw [← comparison_integral_toC]
        congr 1
        funext y
        exact (map_pow (toCHom (𝕜 := 𝕜)) y 2).symm
    rw [e, e, h]
  have hNe : ∀ r : ℝ, -20 ≤ r → (N : ℝ) ^ (-20 : ℝ) ≤ (N : ℝ) ^ r := fun r hr =>
    Real.rpow_le_rpow_of_exponent_le hN1 hr
  refine (abs_add_le _ _).trans ?_
  by_cases hpd : p.1.1 = p.1.2
  · -- Step 3, case `a = b`
    rw [ite_eq_left_of_eq_true _ _ (eq_true hpd)]
    have hgood : ∀ x ∈ G, ‖((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p)‖ ≤
        2 * (C₂ * CF * (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)) := by
      intro x hx
      have hv' := hD Mv hv x hx
      have hw' := hD Mw hw x hx
      simp only [eq_true hpd, ↓reduceIte, sub_zero] at hv' hw'
      rw [h11, h20] at hv'
      rw [Real.norm_eq_abs]
      have := abs_le.1 hv'
      have := abs_le.1 hw'
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hb0 : 0 ≤ (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg) := by positivity
    have hGb := (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hgood).trans
      (mul_le_of_le_one_right (by positivity) hGle)
    rw [Real.norm_eq_abs] at hGb
    have h20' := hNe (-(11 / 6 : ℝ) + 2 * εg) (by linarith)
    have := mul_nonneg (mul_nonneg (mul_nonneg hm3.le hC₀3) hCF) hb0
    nlinarith [mul_le_mul_of_nonneg_left h20' hCF]
  · -- Steps 3–5, case `a ≠ b`
    rw [ite_eq_right_of_eq_false _ _ (eq_false hpd)]
    obtain ⟨iTv, bTv⟩ := comparison_third_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hpd F CF hF hFb
      (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mv.law p)
    obtain ⟨iTw, bTw⟩ := comparison_third_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p hpd F CF hF hFb
      (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mw.law p)
    have hgood : ∀ x ∈ G, ‖((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p) -
      (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mv.law p)) +
      (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mw.law p))‖ ≤
        2 * (C₂ * CF * (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) := by
      intro x hx
      have hv' := hD Mv hv x hx
      have hw' := hD Mw hw x hx
      simp only [hpd, ↓reduceIte] at hv' hw'
      rw [h11, h20] at hv'
      rw [Real.norm_eq_abs]
      have := abs_le.1 hv'
      have := abs_le.1 hw'
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hΔG : IntegrableOn (fun x => ((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p)) G M.prodLaw := hΔi.integrableOn
    have hi1 : IntegrableOn (fun x => ((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p) -
      (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mv.law p))) G M.prodLaw := hΔG.sub iTv
    have heq : ∫ x in G, (((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p) -
      (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mv.law p)) +
      (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mw.law p))) ∂M.prodLaw =
        ∫ x in G, ((∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mv.law p) - ∫ v, F (smoothCount E₁ E₂ (edgeEta εg N)
      (toMatrixC (Function.update x p v))) ∂Mw.law p) ∂M.prodLaw -
      ∫ x in G, (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mv.law p)) ∂M.prodLaw +
          ∫ x in G, (iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N)
        (toMatrixC (Function.update x p 0))) *
      entryT3 E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0)) p.1.1 p.1.2
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂Mw.law p)) ∂M.prodLaw := by
      rw [integral_add hi1 iTw, integral_sub hΔG iTv]
    have hb0 : 0 ≤ (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) := by positivity
    have hGb := (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hgood).trans
      (mul_le_of_le_one_right (by positivity) hGle)
    rw [Real.norm_eq_abs, heq] at hGb
    -- the moments `μ₃`
    have hμ : ∀ U : Ensemble 𝕜 N, U.Assumptions ϑ δm δp C₀ →
        ‖∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂U.law p‖ ≤ m3 * (C₀ / N) ^ ((3 : ℝ) / 2) := by
      intro U hU
      have hσ : ∫ y, ‖y‖ ^ 2 ∂U.law p ≤ C₀ / N := by
        have := hU.boundC p.1.1 p.1.2
        rwa [Ensemble.var, comparison_mk'_self] at this
      have hm := hmom C₀ N (U.law p) hσ (hU.subexp p)
      simp only [Nat.cast_ofNat] at hm
      refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ hm)
      congr 1
      funext y
      rw [norm_mul, Complex.norm_real, comparison_norm_toC, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      ring
    have hpow : (C₀ / N) ^ ((3 : ℝ) / 2) * edgePsi εg N ^ 2 =
        16 * C₀ ^ ((3 : ℝ) / 2) * (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) := by
      have h3 : (0 : ℝ) < (N : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hNpos _
      have hsplit : (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) * (N : ℝ) ^ ((3 : ℝ) / 2) =
          (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        congr 1
        ring
      unfold edgePsi
      rw [Real.div_rpow hC₀.le hNpos.le, mul_pow, sq ((N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg)),
        ← hsplit, div_mul_eq_mul_div, div_eq_iff h3.ne']
      ring
    have hpi : 37 / π ≤ 37 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
    have hT : ∀ μ : ℂ, ‖μ‖ ≤ m3 * (C₀ / N) ^ ((3 : ℝ) / 2) →
        37 / π * ‖μ‖ * CF * edgePsi εg N ^ 2 ≤
          198 * m3 * C₀ ^ ((3 : ℝ) / 2) * CF * (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) := by
      intro μ hμ'
      have hΨ2 : 0 ≤ edgePsi εg N ^ 2 := sq_nonneg _
      have h1 : 37 / π * ‖μ‖ * CF * edgePsi εg N ^ 2 ≤
          37 / 3 * (m3 * (C₀ / N) ^ ((3 : ℝ) / 2)) * CF * edgePsi εg N ^ 2 := by
        gcongr
      have h2 : 37 / 3 * (m3 * (C₀ / N) ^ ((3 : ℝ) / 2)) * CF * edgePsi εg N ^ 2 =
          37 / 3 * 16 * (m3 * C₀ ^ ((3 : ℝ) / 2) * CF * (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) := by
        linear_combination (37 / 3 * m3 * CF) * hpow
      have h0 : 0 ≤ m3 * C₀ ^ ((3 : ℝ) / 2) * CF * (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) := by
        positivity
      nlinarith
    have hv3 := (hT _ (hμ Mv hv)).trans' bTv
    have hw3 := (hT _ (hμ Mw hw)).trans' bTw
    have h20' := hNe (-(13 / 6 : ℝ) + 4 * εg) (by linarith)
    have hX := comparison_abs_le hGb
    nlinarith [mul_le_mul_of_nonneg_left h20' hCF]

/-- Counting the pairs: `N` diagonal pairs and at most `N²` pairs in total. -/
private lemma comparison_sum_le {N : ℕ} (hN : (1 : ℝ) ≤ N) {εg : ℝ} (hεg : 0 < εg) :
    ∑ p : Pair N, (if p.1.1 = p.1.2 then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
      else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) ≤ 2 * (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hd : ((Finset.univ.filter fun p : Pair N => p.1.1 = p.1.2).card : ℝ) ≤ N := by
    have h := Finset.card_le_card_of_injOn (fun p : Pair N => p.1.1)
      (s := Finset.univ.filter fun p : Pair N => p.1.1 = p.1.2) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by
        intro p hp q hq h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
        exact Subtype.ext (Prod.ext h (by rw [← hp, ← hq]; exact h)))
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have ho : ((Finset.univ.filter fun p : Pair N => ¬ p.1.1 = p.1.2).card : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h1 := Finset.card_filter_le (Finset.univ : Finset (Pair N)) fun p => ¬ p.1.1 = p.1.2
    have h2 : (Finset.univ : Finset (Pair N)).card ≤ N * N := by
      rw [Finset.card_univ]
      refine (Fintype.card_subtype_le _).trans ?_
      simp
    have h3 := h1.trans h2
    rw [sq]
    exact_mod_cast h3
  have he1 : 0 ≤ (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg) := by positivity
  have he2 : 0 ≤ (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) := by positivity
  have hdiag : (N : ℝ) * (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg) ≤
      (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg) := by
    calc (N : ℝ) * (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
        = (N : ℝ) ^ ((1 : ℝ) + (-(11 / 6 : ℝ) + 2 * εg)) := by
          rw [Real.rpow_add hNpos (1 : ℝ), Real.rpow_one]
      _ ≤ (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg) :=
          Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hoff : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) =
      (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg) := by
    rw [← Real.rpow_two, ← Real.rpow_add hNpos]
    congr 1
    ring
  nlinarith [mul_le_mul_of_nonneg_right hd he1, mul_le_mul_of_nonneg_right ho he2]

/-- Theorem 11.20 (the form (6.25) of Theorem 6.3, with `X = (N/π) ∫ Im m`). -/
theorem edgeComparison (ϑ C₀ : ℝ) (hϑ : 0 < ϑ) (hC₀ : 0 < C₀) :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∀ (δm δp A₀ εg : ℝ), 0 < εg → εg ≤ 1 / 10 → ∀ N : ℕ,
      EdgeLarge ϑ C₀ A₀ εg N → EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N →
      ∀ Mv Mw : Ensemble 𝕜 N, Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ →
      Ensemble.MomentMatch2 Mv Mw →
      ∀ E₁ E₂ : ℝ, E₁ ≤ E₂ → E₁ ∈ edgeWindow εg N → E₂ ∈ edgeWindow εg N →
      ∀ (F : ℝ → ℝ) (CF : ℝ), ContDiff ℝ 3 F →
      (∀ k : ℕ, k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) →
      |∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) ∂Mv.prodLaw -
          ∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) ∂Mw.prodLaw| ≤
        C₄ * CF * (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg) := by
  obtain ⟨C₃, hC₃, hstep⟩ := hybrid_step_le (𝕜 := 𝕜) ϑ C₀ hϑ hC₀
  refine ⟨2 * C₃, by positivity, ?_⟩
  intro δm δp A₀ εg hεg hεg' N hN hIn Mv Mw hv hw hvw E₁ E₂ hE hE₁ hE₂ F CF hF hFb
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hF0 : ∀ x, |F x| ≤ CF := fun x => by simpa using hFb 0 (by norm_num) x
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF0 0)
  set I : ℕ → ℝ := fun k => ∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x))
    ∂(Ensemble.hybridSeq Mv Mw k).prodLaw with hI
  set b : Pair N → ℝ := fun p => if p.1.1 = p.1.2 then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
    else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg) with hb
  set Γ := Fintype.card (Pair N)
  have h0 : I 0 = ∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) ∂Mv.prodLaw := by
    simp only [hI, Ensemble.hybridSeq_zero]
  have hΓ : I Γ = ∫ x, F (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC x)) ∂Mw.prodLaw := by
    simp only [hI, Γ, Ensemble.hybridSeq_card]
  rw [← h0, ← hΓ, ← Finset.sum_range_sub']
  -- Proposition 11.19 at each step
  have hk : ∀ k (hk : k < Γ), |I k - I (k + 1)| ≤
      C₃ * CF * b ((Fintype.equivFin (Pair N)).symm ⟨k, hk⟩) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Ensemble.hybridSeq_succ Mv Mw k hk
    have := hstep δm δp A₀ εg hεg hεg' N hN hIn E₁ E₂ hE hE₁ hE₂ F CF hF hFb Mv Mw hv hw hvw
      (Ensemble.hybridSeq Mv Mw k) (Ensemble.hybridSeq_law Mv Mw k)
      ((Fintype.equivFin (Pair N)).symm ⟨k, hk⟩)
    rw [← h2, ← h1] at this
    exact this
  have hb0 : ∀ p, 0 ≤ b p := fun p => by simp only [hb]; split_ifs <;> positivity
  calc |∑ k ∈ Finset.range Γ, (I k - I (k + 1))|
      ≤ ∑ k ∈ Finset.range Γ, |I k - I (k + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range Γ, C₃ * CF *
          (if h : k < Γ then b ((Fintype.equivFin (Pair N)).symm ⟨k, h⟩) else 0) := by
        refine Finset.sum_le_sum fun k hkΓ => ?_
        have hkΓ' : k < Γ := Finset.mem_range.1 hkΓ
        rw [dite_eq_left hkΓ']
        exact hk k hkΓ'
    _ = C₃ * CF * ∑ p : Pair N, b p := by
        rw [← Finset.mul_sum, Finset.sum_range (fun k =>
          if h : k < Γ then b ((Fintype.equivFin (Pair N)).symm ⟨k, h⟩) else 0)]
        congr 1
        rw [← Equiv.sum_comp (Fintype.equivFin (Pair N)).symm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dite_eq_left i.isLt]
    _ ≤ C₃ * CF * (2 * (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg)) :=
        mul_le_mul_of_nonneg_left (comparison_sum_le hN1 hεg) (by positivity)
    _ = 2 * C₃ * CF * (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * εg) := by ring

end Rigidity
