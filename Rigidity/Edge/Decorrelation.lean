module

public import Rigidity.Edge.Continuity
public import Rigidity.Edge.EdgeEvent
public import Rigidity.Edge.GoodSet
public import Rigidity.Edge.Hybrid
public import Rigidity.Edge.Inputs
public import Rigidity.Edge.Minor
public import Rigidity.Edge.Params
public import Rigidity.Edge.Resample
public import Rigidity.Edge.Resolvent
public import Rigidity.Edge.SmoothCount
public import Rigidity.Ensemble.Basic

@[expose] public section

/-!
# Decorrelation of one off-diagonal resolvent entry

Numbers refer to NP v1.1; the original is cited as [EYY, …].

This file proves Lemma 11.18.  Let `M` be an ensemble with the assumptions 𝔄, `p = (a, b)` an
off-diagonal pair, `Q = H^{[p]}` (the matrix `H(x)` with the entry `x_p` set to `0`), `Φ` a `C¹`
function with `|Φ|, |Φ'| ≤ C_Φ`, `z = y + iη` with `y ∈ {E₁, E₂}` and `(c, d) ∈ {(a, b), (b, a)}`.
Then `|𝔼[1(Q ∈ 𝒢_p) Φ(X(Q)) R_cd(z)]| ≤ 7 C_Φ Ψ²`.

The proof follows the four steps of the proof of Lemma 11.18:
* Step 1 (Lemma 3.6 (I2)): `R_cd = -R_cc Y` with `Y = ∑_{j ≠ c} Q_cj R^{(c)}_jd`, where `R^{(c)}`
  is the resolvent of the minor `Q^{(c)}`; the minor does not depend on the entries of the row `c`.
* Step 2: resampling the entries `h_cj`, `j ∉ {c, d}`, of the row `c` (Lemma 4.7, resampling
  form) and the centring condition (2.1) give `𝔼[Φ(X(Q^{(c)})) Y] = 0`.
* Step 3: on `𝒢_p`, Corollary 11.11 (ii) and `|R_cc| ≥ 1 - Ψ` give
  `|Φ(X(Q)) R_cd - Φ(X(Q^{(c)})) Y| ≤ (8/3) C_Φ Ψ²`.
* Step 4: off `𝒢_p`, Lemma 11.15 (b) and the second moments of the entries bound the remaining
  term by `C_Φ Ψ²`.  Here the bound `|Y| ≤ η⁻¹ ∑_j |h_cj|` and the elementary inequality
  `s ≤ s²/(2t) + t/2` with `t = N^{10}` are used for each entry in place of the Cauchy–Schwarz
  inequality.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. Entries of `H(x)` -/

/-- `‖toC y‖ = ‖y‖`. -/
private lemma decor_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

private lemma decor_toC_star (y : 𝕜) : toC (star y) = starRingEnd ℂ (toC y) := by
  apply Complex.ext <;> simp [toC]

private lemma decor_continuous_toC : Continuous (toC : 𝕜 → ℂ) := by
  have : (toC : 𝕜 → ℂ) =
      fun y => ((RCLike.re y : ℝ) : ℂ) + ((RCLike.im y : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [toC]
  rw [this]
  fun_prop

/-- The Bochner integral commutes with `toC`. -/
private lemma decor_integral_toC {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → 𝕜} (hf : Integrable f μ) : ∫ a, toC (f a) ∂μ = toC (∫ a, f a ∂μ) := by
  have hf' : Integrable (fun a => toC (f a)) μ :=
    hf.norm.mono' (decor_continuous_toC.comp_aestronglyMeasurable hf.1)
      (Eventually.of_forall fun a => by rw [decor_norm_toC])
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

/-- The entry `H(x)_{ij}` depends only on the coordinate `x_{(min(i,j), max(i,j))}`. -/
private lemma decor_toMatrixC_congr {N : ℕ} {x x' : Pair N → 𝕜} {i j : Fin N}
    (h : x (Pair.mk' i j) = x' (Pair.mk' i j)) : toMatrixC x i j = toMatrixC x' i j := by
  simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply, h]

private lemma decor_toMatrixC_eq_zero {N : ℕ} {x : Pair N → 𝕜} {i j : Fin N}
    (h : x (Pair.mk' i j) = 0) : toMatrixC x i j = 0 := by
  rw [decor_toMatrixC_congr (x' := 0) (by rw [h]; rfl)]
  simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
  split_ifs <;> apply Complex.ext <;> simp [toC]

/-- `|H(x)_{ij}| ≤ |x_{(min(i,j), max(i,j))}|`. -/
private lemma decor_norm_toMatrixC_le {N : ℕ} (x : Pair N → 𝕜) (i j : Fin N) :
    ‖toMatrixC x i j‖ ≤ ‖x (Pair.mk' i j)‖ := by
  simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · rw [decor_norm_toC]
  · rw [decor_norm_toC, norm_star]
  · rw [decor_norm_toC, RCLike.norm_ofReal]
    exact RCLike.abs_re_le_norm _

private lemma decor_continuous_toMatrixC {N : ℕ} (i j : Fin N) :
    Continuous fun x : Pair N → 𝕜 => toMatrixC x i j := by
  simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs
  · exact decor_continuous_toC.comp (continuous_apply _)
  · exact decor_continuous_toC.comp (continuous_star.comp (continuous_apply _))
  · exact decor_continuous_toC.comp (RCLike.continuous_ofReal.comp
      (RCLike.continuous_re.comp (continuous_apply _)))

private lemma decor_continuous_update {N : ℕ} (p : Pair N) :
    Continuous fun x : Pair N → 𝕜 => Function.update x p 0 :=
  continuous_pi fun q => by
    by_cases h : q = p
    · subst h; simp only [Function.update_self]; exact continuous_const
    · simp only [Function.update_of_ne h]; exact continuous_apply q

/-- An entry of a matrix is bounded by its `ℓ²` operator norm. -/
private lemma decor_norm_entry_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm
    (A *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp)) i
  refine le_trans (le_of_eq ?_) h2
  simp

/-! ### 2. Index pairs of the row `c` -/

private lemma decor_mk'_cases {N : ℕ} (i j : Fin N) :
    ((Pair.mk' i j).1.1 = i ∧ (Pair.mk' i j).1.2 = j) ∨
      ((Pair.mk' i j).1.1 = j ∧ (Pair.mk' i j).1.2 = i) := by
  unfold Pair.mk'
  split_ifs <;> simp

private lemma decor_mk'_eq {N : ℕ} {i k c j : Fin N} (h : Pair.mk' i k = Pair.mk' c j) :
    (i = c ∧ k = j) ∨ (i = j ∧ k = c) := by
  have e1 : (Pair.mk' i k).1.1 = (Pair.mk' c j).1.1 := by rw [h]
  have e2 : (Pair.mk' i k).1.2 = (Pair.mk' c j).1.2 := by rw [h]
  rcases decor_mk'_cases i k with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases decor_mk'_cases c j with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    · rw [a1, b1] at e1
      rw [a2, b2] at e2
      tauto

private lemma decor_mk'_self {N : ℕ} (p : Pair N) : Pair.mk' p.1.1 p.1.2 = p := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  simp [Pair.mk', h]

private lemma decor_mk'_cd {N : ℕ} {p : Pair N} {c d : Fin N}
    (hcd : (c = p.1.1 ∧ d = p.1.2) ∨ (c = p.1.2 ∧ d = p.1.1)) : Pair.mk' c d = p := by
  rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact decor_mk'_self p
  · rw [Pair.mk'_comm]
    exact decor_mk'_self p

/-- The set `𝒥` of the proof of Lemma 11.18: the pairs `(min(c,j), max(c,j))`, `j ∉ {c, d}`,
which carry the entries of the row `c` other than `h_cc` and `h_cd`. -/
private def decorRow {N : ℕ} (c d : Fin N) : Set (Pair N) :=
  {q | ∃ j, j ≠ c ∧ j ≠ d ∧ q = Pair.mk' c j}

private lemma decor_mk'_notMem_row {N : ℕ} {c d i k : Fin N} (hi : i ≠ c) (hk : k ≠ c) :
    Pair.mk' i k ∉ decorRow c d := by
  rintro ⟨j, -, -, h⟩
  rcases decor_mk'_eq h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hi h1
  · exact hk h2

private lemma decor_ne_of_minor {N : ℕ} {c : Fin N} (j : {i // i ∉ ({c} : Finset (Fin N))}) :
    (j : Fin N) ≠ c :=
  fun e => j.2 (Finset.mem_singleton.2 e)

/-! ### 3. The minor and the function `Y` -/

/-- The minor `Q^{(c)}` of `Q = H(x)^{[p]}`, with row and column `c` removed. -/
private noncomputable def decorMinor {N : ℕ} (p : Pair N) (c : Fin N) (x : Pair N → 𝕜) :
    Matrix {i // i ∉ ({c} : Finset (Fin N))} {i // i ∉ ({c} : Finset (Fin N))} ℂ :=
  (toMatrixC (Function.update x p 0)).submatrix Subtype.val Subtype.val

/-- Step 0 (i): the minor `Q^{(c)}` does not depend on the coordinates in `𝒥`. -/
private lemma decorMinor_congr {N : ℕ} {p : Pair N} {c d : Fin N} {x x' : Pair N → 𝕜}
    (h : ∀ q, q ∉ decorRow c d → x q = x' q) : decorMinor p c x = decorMinor p c x' := by
  ext i k
  simp only [decorMinor, Matrix.submatrix_apply]
  apply decor_toMatrixC_congr
  by_cases hq : Pair.mk' (i : Fin N) k = p
  · rw [hq, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]
    exact h _ (decor_mk'_notMem_row (decor_ne_of_minor i) (decor_ne_of_minor k))

/-- `Y = ∑_{j ≠ c} Q_cj R^{(c)}_jd` (Step 1 of the proof of Lemma 11.18). -/
private noncomputable def decorY {N : ℕ} (p : Pair N) {c d : Fin N} (hcd : c ≠ d) (z : ℂ)
    (x : Pair N → 𝕜) : ℂ :=
  ∑ j : {i // i ∉ ({c} : Finset (Fin N))}, toMatrixC (Function.update x p 0) c j *
    resolventMat (decorMinor p c x) z j ⟨d, by simpa using hcd.symm⟩

/-- Step 1 of the proof of Lemma 11.18: `R_cd = -R_cc Y` (Lemma 3.6 (I2)). -/
private lemma decor_schur {N : ℕ} (p : Pair N) {c d : Fin N} (hcd : c ≠ d) {z : ℂ}
    (hz : 0 < z.im) (x : Pair N → 𝕜) :
    resolventMat (toMatrixC (Function.update x p 0)) z c d =
      -resolventMat (toMatrixC (Function.update x p 0)) z c c * decorY p hcd z x := by
  unfold decorY decorMinor
  exact resolventMat_offDiag (toMatrixC_isHermitian _) hz hcd

/-- Step 0 (ii): after resampling the coordinates in `𝒥`, the row `c` of `Q` is `0` at `d` and
the row `c` of the resampled matrix `H(w)` elsewhere. -/
private lemma decor_row_piecewise {N : ℕ} {p : Pair N} {c d : Fin N} (hpcd : Pair.mk' c d = p)
    (hcd : c ≠ d) [DecidablePred (· ∈ decorRow c d)] (x w : Pair N → 𝕜) (j : Fin N)
    (hj : j ≠ c) :
    toMatrixC (Function.update ((decorRow c d).piecewise w x) p 0) c j =
      if j = d then 0 else toMatrixC w c j := by
  split_ifs with hjd
  · subst hjd
    apply decor_toMatrixC_eq_zero
    rw [hpcd, Function.update_self]
  · apply decor_toMatrixC_congr
    have hne : Pair.mk' c j ≠ p := by
      rw [← hpcd]
      intro h
      rcases decor_mk'_eq h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hjd h2
      · exact hcd h1
    rw [Function.update_of_ne hne, Set.piecewise_eq_of_mem _ _ _
      (show Pair.mk' c j ∈ decorRow c d from ⟨j, hj, hjd, rfl⟩)]

/-- `|Y| ≤ η⁻¹ ∑_{j ≠ c} |x_{(min(c,j), max(c,j))}|`, by `|R^{(c)}_jd| ≤ ‖R^{(c)}‖ ≤ η⁻¹`
(Lemma 3.5 (a)). -/
private lemma decor_norm_Y_le {N : ℕ} (p : Pair N) {c d : Fin N} (hcd : c ≠ d) {y η : ℝ}
    (hη : 0 < η) (x : Pair N → 𝕜) :
    ‖decorY p hcd ⟨y, η⟩ x‖ ≤
      η⁻¹ * ∑ j : {i // i ∉ ({c} : Finset (Fin N))}, ‖x (Pair.mk' c j)‖ := by
  unfold decorY
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  have h1 : ‖toMatrixC (Function.update x p 0) c j‖ ≤ ‖x (Pair.mk' c j)‖ := by
    refine (decor_norm_toMatrixC_le _ _ _).trans ?_
    by_cases hq : Pair.mk' c (j : Fin N) = p
    · rw [hq, Function.update_self, norm_zero]
      exact norm_nonneg _
    · rw [Function.update_of_ne hq]
  have hz : 0 < (⟨y, η⟩ : ℂ).im := hη
  have h2 : ‖resolventMat (decorMinor p c x) ⟨y, η⟩ j ⟨d, by simpa using hcd.symm⟩‖ ≤ η⁻¹ := by
    refine (decor_norm_entry_le _ _ _).trans ?_
    refine (norm_resolventMat_le ((toMatrixC_isHermitian _).submatrix _) hz).trans ?_
    rw [one_div]
  exact mul_le_mul h2 h1 (norm_nonneg _) (inv_nonneg.2 hη.le)

/-! ### 4. Moments of the entries -/

/-- Under (2.17), a vanishing variance forces the entry to vanish almost surely. -/
private lemma decor_law_eq_zero {N : ℕ} (M : Ensemble 𝕜 N) {ϑ : ℝ} (h : M.SubexpDecay ϑ)
    (hϑ : 0 < ϑ) (p : Pair N) (hp : M.varPair p = 0) : M.law p {y | y ≠ 0} = 0 := by
  have key : ∀ x : ℝ, 1 ≤ x →
      M.law p {y | y ≠ 0} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ))) := by
    intro x hx
    have := h p x hx
    simpa [hp] using this
  have ht : Tendsto (fun x : ℝ => ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => ϑ⁻¹ * Real.exp (-(x ^ ϑ))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_rpow_atTop hϑ)).const_mul ϑ⁻¹
      simpa using this
    simpa using (ENNReal.tendsto_ofReal h0)
  have := ge_of_tendsto ht (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx using key x hx)
  exact le_antisymm this zero_le

/-- Under (2.17) with `ϑ > 0`, every moment of an entry is finite (Lemma 2.5). -/
private lemma decor_integrable_norm_pow {N : ℕ} (M : Ensemble 𝕜 N) {ϑ : ℝ}
    (h : M.SubexpDecay ϑ) (hϑ : 0 < ϑ) (p : Pair N) (k : ℕ) :
    Integrable (fun y => ‖y‖ ^ k) (M.law p) := by
  have hmeas : AEStronglyMeasurable (fun y : 𝕜 => ‖y‖ ^ k) (M.law p) := by fun_prop
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hv0 : 0 ≤ M.varPair p := integral_nonneg fun y => by positivity
  rcases hv0.eq_or_lt with hv | hv
  · have h0 := decor_law_eq_zero M h hϑ p hv.symm
    refine (integrable_zero _ _ _).congr ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with y hy
    have : y = 0 := by simpa using hy
    simp [this, hk.ne']
  set σ := Real.sqrt (M.varPair p) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr hv
  set b : ℝ := (σ ^ ϑ)⁻¹ with hbdef
  have hb : 0 < b := inv_pos.mpr (Real.rpow_pos_of_pos hσ _)
  set C : ℝ := max ϑ⁻¹ (Real.exp 1) with hCdef
  have hC0 : 0 ≤ C := (Real.exp_pos 1).le.trans (le_max_right _ _)
  have tail : ∀ t : ℝ, 0 < t →
      M.law p {y | t < ‖y‖} ≤ ENNReal.ofReal (C * Real.exp (-b * t ^ ϑ)) := by
    intro t ht
    have hbt : b * t ^ ϑ = (t / σ) ^ ϑ := by
      rw [Real.div_rpow ht.le hσ.le, hbdef]
      ring
    rw [neg_mul, hbt]
    rcases le_or_gt 1 (t / σ) with hx | hx
    · have := h p (t / σ) hx
      rw [← hσdef, div_mul_cancel₀ _ hσ.ne'] at this
      refine this.trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (t / σ) ^ ϑ ≤ 1 :=
        Real.rpow_le_one (div_pos ht hσ).le hx.le hϑ.le
      calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
        _ ≤ C * Real.exp (-(t / σ) ^ ϑ) :=
          mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_pos _).le hC0
  refine ⟨hmeas, ?_⟩
  have hnn : 0 ≤ᵐ[M.law p] fun y : 𝕜 => ‖y‖ ^ k :=
    Filter.Eventually.of_forall fun y => by positivity
  rw [hasFiniteIntegral_iff_ofReal hnn]
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hint : IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - 1) * Real.exp (-b * t ^ ϑ))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hϑ hb
  have hlt := (hint.const_mul C).lintegral_lt_top
  have hlay := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := M.law p)
    (f := fun y : 𝕜 => ‖y‖) (Filter.Eventually.of_forall fun y => norm_nonneg y)
    measurable_norm.aemeasurable hk'
  have hconv : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ k) ∂M.law p =
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ (k : ℝ)) ∂M.law p := by
    simp only [Real.rpow_natCast]
  rw [hconv, hlay]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hlt)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have ht' : 0 < t := ht
  calc M.law p {a | t < ‖a‖} * ENNReal.ofReal (t ^ ((k : ℝ) - 1))
      ≤ ENNReal.ofReal (C * Real.exp (-b * t ^ ϑ)) * ENNReal.ofReal (t ^ ((k : ℝ) - 1)) :=
        mul_le_mul' (tail t ht') le_rfl
    _ = ENNReal.ofReal (C * Real.exp (-b * t ^ ϑ) * t ^ ((k : ℝ) - 1)) :=
        (ENNReal.ofReal_mul (mul_nonneg hC0 (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (C * (t ^ ((k : ℝ) - 1) * Real.exp (-b * t ^ ϑ))) := by
        congr 1; ring

/-- Step 2: an off-diagonal entry of `H` has mean zero, by (2.1). -/
private lemma decor_integral_entry {N : ℕ} (M : Ensemble 𝕜 N) (hM0 : M.MeanZero)
    (hint : ∀ q, Integrable (fun s : 𝕜 => s) (M.law q)) {i j : Fin N} (hij : i ≠ j) :
    ∫ w, toMatrixC w i j ∂M.prodLaw = 0 := by
  have hq : Integrable (fun w : Pair N → 𝕜 => w (Pair.mk' i j)) M.prodLaw :=
    by
      unfold Ensemble.prodLaw
      exact integrable_comp_eval (μ := M.law) (i := Pair.mk' i j) (f := fun s : 𝕜 => s) (hint _)
  have h0 : ∫ w, w (Pair.mk' i j) ∂M.prodLaw = 0 := by
    have := integral_comp_eval (μ := M.law) (i := Pair.mk' i j) (f := fun s : 𝕜 => s)
      aestronglyMeasurable_id
    rw [Ensemble.prodLaw, this]
    exact hM0 _
  rcases lt_or_gt_of_ne hij with h | h
  · have e : ∀ w : Pair N → 𝕜, toMatrixC w i j = toC (w (Pair.mk' i j)) := fun w => by
      simp [toMatrixC, toMatrix, h]
    simp_rw [e]
    rw [decor_integral_toC hq, h0]
    apply Complex.ext <;> simp [toC]
  · have e : ∀ w : Pair N → 𝕜, toMatrixC w i j = starRingEnd ℂ (toC (w (Pair.mk' i j))) :=
      fun w => by
        simp only [toMatrixC, toMatrix, Matrix.map_apply, Matrix.of_apply, not_lt_of_gt h, h,
          ite_false, ite_true]
        exact decor_toC_star _
    simp_rw [e]
    rw [integral_conj, decor_integral_toC hq, h0]
    apply Complex.ext <;> simp [toC]

/-! ### 5. Lemma 11.18 -/

/-- `Φ(X(Q^{(c)}))`, the function `T` of the proof of Lemma 11.18. -/
private noncomputable def decorT {N : ℕ} (Φ : ℝ → ℝ) (E₁ E₂ η : ℝ) (p : Pair N) (c : Fin N)
    (x : Pair N → 𝕜) : ℂ :=
  (Φ (smoothCount E₁ E₂ η (decorMinor p c x)) : ℂ)

/-- The mean value bound `|Φ(s) - Φ(t)| ≤ C_Φ |s - t|`. -/
private lemma decor_lipschitz {Φ : ℝ → ℝ} {CΦ : ℝ} (hΦ : ContDiff ℝ 1 Φ)
    (hΦ1 : ∀ x, |deriv Φ x| ≤ CΦ) (s t : ℝ) : |Φ s - Φ t| ≤ CΦ * |s - t| := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable one_ne_zero
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hd x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hΦ1 x) convex_univ (Set.mem_univ t)
    (Set.mem_univ s)
  simpa [Real.norm_eq_abs] using this

/-- Lemma 11.18. -/
theorem norm_integral_decor_le {ϑ δm δp C₀ A₀ εg E₁ E₂ : ℝ} {N : ℕ} (hϑ : 0 < ϑ)
    (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10) (hN : EdgeLarge ϑ C₀ A₀ εg N)
    (hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N) (hE : E₁ ≤ E₂) (hE₁ : E₁ ∈ edgeWindow εg N)
    (hE₂ : E₂ ∈ edgeWindow εg N) (M : Ensemble 𝕜 N) (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) (hp : p.1.1 ≠ p.1.2) (Φ : ℝ → ℝ) (CΦ : ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (hΦ0 : ∀ x, |Φ x| ≤ CΦ) (hΦ1 : ∀ x, |deriv Φ x| ≤ CΦ) {y : ℝ} (hy : y = E₁ ∨ y = E₂)
    {c d : Fin N} (hcd : (c = p.1.1 ∧ d = p.1.2) ∨ (c = p.1.2 ∧ d = p.1.1)) :
    ‖∫ x, Set.indicator {x | toMatrixC (Function.update x p 0) ∈
          goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2}
        (fun x => (Φ (smoothCount E₁ E₂ (edgeEta εg N) (toMatrixC (Function.update x p 0))) : ℂ) *
          resolventMat (toMatrixC (Function.update x p 0)) ⟨y, edgeEta εg N⟩ c d) x
        ∂M.prodLaw‖ ≤ 7 * CΦ * edgePsi εg N ^ 2 := by
  classical
  -- parameters
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hη : 0 < edgeEta εg N := Real.rpow_pos_of_pos hNpos _
  have hΨ : 0 < edgePsi εg N := by unfold edgePsi; positivity
  have hΨ8 : edgePsi εg N ≤ 1 / 8 := hN.psi_le
  have hCΦ : 0 ≤ CΦ := (abs_nonneg _).trans (hΦ0 0)
  have hcd' : c ≠ d := by
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact fun h => hp h.symm
  have hpcd : Pair.mk' c d = p := decor_mk'_cd hcd
  have hc : c ∈ ({p.1.1, p.1.2} : Set (Fin N)) := by
    rcases hcd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hd : d ∈ ({p.1.1, p.1.2} : Set (Fin N)) := by
    rcases hcd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hyI : y ∈ Set.Icc E₁ E₂ := by
    rcases hy with rfl | rfl
    · exact ⟨le_rfl, hE⟩
    · exact ⟨hE, le_rfl⟩
  set η := edgeEta εg N with hηdef
  set Ψ := edgePsi εg N with hΨdef
  have hz : 0 < (⟨y, η⟩ : ℂ).im := hη
  set G : Set (Pair N → 𝕜) :=
    {x | toMatrixC (Function.update x p 0) ∈ goodSet η Ψ E₁ E₂ p.1.1 p.1.2} with hGdef
  set J : Set (Pair N) := decorRow c d with hJdef
  -- continuity and measurability
  have hQc : Continuous fun x : Pair N → 𝕜 => toMatrixC (Function.update x p 0) :=
    continuous_pi fun i => continuous_pi fun j =>
      (decor_continuous_toMatrixC i j).comp (decor_continuous_update p)
  have hGm : MeasurableSet G :=
    ((isClosed_goodSet hη Ψ E₁ E₂ p.1.1 p.1.2).preimage hQc).measurableSet
  have hRc : ∀ k l : Fin N, Continuous fun x : Pair N → 𝕜 =>
      resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ k l := fun k l =>
    (continuous_resolventMat_toMatrixC hz k l).comp (decor_continuous_update p)
  have hXc : Continuous fun x : Pair N → 𝕜 =>
      smoothCount E₁ E₂ η (toMatrixC (Function.update x p 0)) :=
    (continuous_smoothCount_toMatrixC hη hE).comp (decor_continuous_update p)
  have hTc : Continuous (decorT (𝕜 := 𝕜) Φ E₁ E₂ η p c) :=
    Complex.continuous_ofReal.comp (hΦ.continuous.comp (continuous_smoothCount_minor hη hE p c))
  have hRcc0 : ∀ x : Pair N → 𝕜,
      resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ c c ≠ 0 := fun x h => by
    have := im_resolventMat_diag_pos (toMatrixC_isHermitian (Function.update x p 0)) hz c
    rw [h] at this
    simp at this
  have hYeq : ∀ x : Pair N → 𝕜, decorY p hcd' ⟨y, η⟩ x =
      -resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ c d /
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ c c := fun x => by
    rw [decor_schur p hcd' hz x]
    field_simp [hRcc0 x]
  have hYc : Continuous (decorY (𝕜 := 𝕜) p hcd' ⟨y, η⟩) :=
    (continuous_congr hYeq).2 (((hRc c d).neg).div (hRc c c) hRcc0)
  have hAc : Continuous fun x : Pair N → 𝕜 =>
      (Φ (smoothCount E₁ E₂ η (toMatrixC (Function.update x p 0))) : ℂ) *
        resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ c d :=
    (Complex.continuous_ofReal.comp (hΦ.continuous.comp hXc)).mul (hRc c d)
  -- bounds on `T`
  have hTb : ∀ x, ‖decorT (𝕜 := 𝕜) Φ E₁ E₂ η p c x‖ ≤ CΦ := fun x => by
    unfold decorT
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hΦ0 _
  have hTJ : ∀ x x' : Pair N → 𝕜, (∀ q, q ∉ J → x q = x' q) →
      decorT Φ E₁ E₂ η p c x = decorT Φ E₁ E₂ η p c x' := fun x x' h => by
    unfold decorT
    rw [decorMinor_congr h]
  -- moments
  have hmom : ∀ q k, Integrable (fun x : Pair N → 𝕜 => ‖x q‖ ^ k) M.prodLaw := fun q k => by
    unfold Ensemble.prodLaw
    exact integrable_comp_eval (μ := M.law) (i := q) (f := fun s : 𝕜 => ‖s‖ ^ k)
      (decor_integrable_norm_pow M hM.subexp hϑ q k)
  have hmom1 : ∀ q, Integrable (fun x : Pair N → 𝕜 => ‖x q‖) M.prodLaw := fun q => by
    simpa using hmom q 1
  have hint1 : ∀ q, Integrable (fun s : 𝕜 => s) (M.law q) := fun q =>
    (by simpa using decor_integrable_norm_pow M hM.subexp hϑ q 1 :
      Integrable (fun s : 𝕜 => ‖s‖) (M.law q)).mono' aestronglyMeasurable_id
      (ae_of_all _ fun s => le_rfl)
  have hvar : ∀ j : Fin N, ∫ x, ‖x (Pair.mk' c j)‖ ^ 2 ∂M.prodLaw ≤ 1 := fun j => by
    have e : ∫ x, ‖x (Pair.mk' c j)‖ ^ 2 ∂M.prodLaw = M.var c j := by
      unfold Ensemble.prodLaw
      rw [integral_comp_eval (μ := M.law) (i := Pair.mk' c j) (f := fun s : 𝕜 => ‖s‖ ^ 2)
        (by fun_prop)]
      rfl
    rw [e, ← hM.sumA j]
    exact Finset.single_le_sum (f := fun i => M.var i j)
      (fun i _ => integral_nonneg fun s => by positivity) (Finset.mem_univ c)
  -- integrability of `Y` and `T Y`
  have hYint : Integrable (decorY (𝕜 := 𝕜) p hcd' ⟨y, η⟩) M.prodLaw :=
    ((integrable_finsetSum (Finset.univ : Finset {i // i ∉ ({c} : Finset (Fin N))})
      fun j _ => hmom1 (Pair.mk' c j)).const_mul η⁻¹).mono'
      hYc.aestronglyMeasurable (ae_of_all _ fun x => decor_norm_Y_le p hcd' hη x)
  have hTYint : Integrable (fun x => decorT (𝕜 := 𝕜) Φ E₁ E₂ η p c x *
      decorY p hcd' ⟨y, η⟩ x) M.prodLaw :=
    hYint.bdd_mul hTc.aestronglyMeasurable (ae_of_all _ hTb)
  -- Step 2: `𝔼[T Y] = 0`
  have hentry : ∀ j : Fin N, Integrable (fun w : Pair N → 𝕜 => toMatrixC w c j) M.prodLaw :=
    fun j => (hmom1 (Pair.mk' c j)).mono' (decor_continuous_toMatrixC c j).aestronglyMeasurable
      (ae_of_all _ fun w => decor_norm_toMatrixC_le w c j)
  have hin : ∀ x : Pair N → 𝕜,
      ∫ w, decorY p hcd' ⟨y, η⟩ (J.piecewise w x) ∂M.prodLaw = 0 := by
    intro x
    have e : ∀ w : Pair N → 𝕜, decorY p hcd' ⟨y, η⟩ (J.piecewise w x) =
        ∑ j : {i // i ∉ ({c} : Finset (Fin N))},
          (if (j : Fin N) = d then 0 else toMatrixC w c j) *
            resolventMat (decorMinor p c x) ⟨y, η⟩ j ⟨d, by simpa using hcd'.symm⟩ := by
      intro w
      unfold decorY
      rw [decorMinor_congr (d := d) (x := J.piecewise w x) (x' := x)
        (fun q hq => Set.piecewise_eq_of_notMem _ _ _ hq)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [decor_row_piecewise hpcd hcd' x w j (decor_ne_of_minor j)]
    simp_rw [e]
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_mul_const]
      by_cases hjd : (j : Fin N) = d
      · simp [hjd]
      · simp only [hjd, ite_false]
        rw [decor_integral_entry M hM.meanZero hint1 (decor_ne_of_minor j).symm, zero_mul]
    · intro j _
      by_cases hjd : (j : Fin N) = d
      · simp [hjd]
      · simp only [hjd, ite_false]
        exact (hentry j).mul_const _
  have hTY0 : ∫ x, decorT (𝕜 := 𝕜) Φ E₁ E₂ η p c x * decorY p hcd' ⟨y, η⟩ x ∂M.prodLaw = 0 := by
    rw [Ensemble.integral_mul_resample M J _ _ hTc.stronglyMeasurable CΦ hTb hTJ hYint]
    simp [hin]
  -- Step 3: the bound on `𝒢_p`
  have hgood : ∀ x ∈ G,
      ‖(Φ (smoothCount E₁ E₂ η (toMatrixC (Function.update x p 0))) : ℂ) *
          resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ c d -
        decorT Φ E₁ E₂ η p c x * decorY p hcd' ⟨y, η⟩ x‖ ≤ 8 / 3 * CΦ * Ψ ^ 2 := by
    intro x hx
    have hQ := toMatrixC_isHermitian (Function.update x p 0)
    set Q := toMatrixC (Function.update x p 0) with hQdef
    have hdiag : ∀ w ∈ Set.Icc E₁ E₂, ‖resolventMat Q ⟨w, η⟩ c c + 1‖ ≤ Ψ := fun w hw => by
      have := hx.2 c hc c hc w hw
      rwa [Matrix.add_apply, Matrix.one_apply_eq] at this
    have hoff : ‖resolventMat Q ⟨y, η⟩ c d‖ ≤ Ψ := by
      have := hx.2 c hc d hd y hyI
      rwa [Matrix.add_apply, Matrix.one_apply_ne hcd', add_zero] at this
    have h₁ := hdiag E₁ ⟨le_rfl, hE⟩
    have h₂ := hdiag E₂ ⟨hE, le_rfl⟩
    have hy' := hdiag y hyI
    -- (3a)
    have hX := abs_smoothCount_sub_minor_le hQ hη hE c (by linarith) (by linarith)
    have hpi : 2 / π * (‖resolventMat Q ⟨E₁, η⟩ c c + 1‖ + ‖resolventMat Q ⟨E₂, η⟩ c c + 1‖) ≤
        4 / 3 * Ψ := by
      have hpi3 : 3 < π := Real.pi_gt_three
      rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
      nlinarith
    have hΦd : ‖(Φ (smoothCount E₁ E₂ η Q) : ℂ) - decorT Φ E₁ E₂ η p c x‖ ≤ CΦ * (4 / 3 * Ψ) := by
      unfold decorT decorMinor
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (decor_lipschitz hΦ hΦ1 _ _).trans
        (mul_le_mul_of_nonneg_left (hX.trans hpi) hCΦ)
    -- (3b)
    have hs := decor_schur p hcd' hz x
    rw [← hQdef] at hs
    have hcc : 7 / 8 ≤ ‖resolventMat Q ⟨y, η⟩ c c‖ := by
      have := norm_sub_le (resolventMat Q ⟨y, η⟩ c c) (resolventMat Q ⟨y, η⟩ c c + 1)
      rw [show resolventMat Q ⟨y, η⟩ c c - (resolventMat Q ⟨y, η⟩ c c + 1) = -1 by ring,
        norm_neg, norm_one] at this
      linarith
    have hYb : ‖decorY p hcd' ⟨y, η⟩ x‖ ≤ 8 / 7 * Ψ := by
      have h1 : ‖resolventMat Q ⟨y, η⟩ c c‖ * ‖decorY p hcd' ⟨y, η⟩ x‖ ≤ Ψ := by
        rw [← norm_mul, ← norm_neg, ← neg_mul, ← hs]
        exact hoff
      have h2 := norm_nonneg (decorY p hcd' ⟨y, η⟩ x)
      nlinarith
    -- (3c)
    have hΦQ : ‖(Φ (smoothCount E₁ E₂ η Q) : ℂ)‖ ≤ CΦ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hΦ0 _
    have hρ : ‖(Φ (smoothCount E₁ E₂ η Q) : ℂ) * (resolventMat Q ⟨y, η⟩ c c + 1) -
        ((Φ (smoothCount E₁ E₂ η Q) : ℂ) - decorT Φ E₁ E₂ η p c x)‖ ≤ 7 / 3 * CΦ * Ψ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul hΦQ hy' (norm_nonneg _) hCΦ
      nlinarith
    have heq : (Φ (smoothCount E₁ E₂ η Q) : ℂ) * resolventMat Q ⟨y, η⟩ c d -
        decorT Φ E₁ E₂ η p c x * decorY p hcd' ⟨y, η⟩ x =
        -(((Φ (smoothCount E₁ E₂ η Q) : ℂ) * (resolventMat Q ⟨y, η⟩ c c + 1) -
          ((Φ (smoothCount E₁ E₂ η Q) : ℂ) - decorT Φ E₁ E₂ η p c x)) *
            decorY p hcd' ⟨y, η⟩ x) := by
      rw [hs]
      ring
    rw [heq, norm_neg, norm_mul]
    calc _ ≤ 7 / 3 * CΦ * Ψ * (8 / 7 * Ψ) :=
          mul_le_mul hρ hYb (norm_nonneg _) (by positivity)
      _ = 8 / 3 * CΦ * Ψ ^ 2 := by ring
  -- Step 4: the complement of `𝒢_p`
  set s : ℝ := (N : ℝ) ^ 10 with hsdef
  have hs0 : 0 < s := by positivity
  have hamgm : ∀ t : ℝ, t ≤ t ^ 2 / (2 * s) + s / 2 := fun t => by
    have h1 : t ^ 2 / (2 * s) + s / 2 - t = (t - s) ^ 2 / (2 * s) := by field_simp; ring
    have h2 : 0 ≤ (t - s) ^ 2 / (2 * s) := by positivity
    linarith
  set D : (Pair N → 𝕜) → ℝ := fun x => CΦ * (η⁻¹ * ∑ j : {i // i ∉ ({c} : Finset (Fin N))},
      (‖x (Pair.mk' c j)‖ ^ 2 / (2 * s) + Gᶜ.indicator (fun _ => s / 2) x)) with hDdef
  have hterm_int : ∀ j : {i // i ∉ ({c} : Finset (Fin N))}, Integrable (fun x : Pair N → 𝕜 =>
      ‖x (Pair.mk' c j)‖ ^ 2 / (2 * s) + Gᶜ.indicator (fun _ => s / 2) x) M.prodLaw :=
    fun j => ((hmom _ 2).div_const _).add ((integrable_const (s / 2)).indicator hGm.compl)
  have hDint : Integrable D M.prodLaw :=
    ((integrable_finsetSum _ fun j _ => hterm_int j).const_mul _).const_mul _
  have hbadpt : ∀ x, ‖Gᶜ.indicator (fun x => decorT Φ E₁ E₂ η p c x *
      decorY p hcd' ⟨y, η⟩ x) x‖ ≤ D x := by
    intro x
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_notMem (by simpa using hx), norm_zero]
      refine mul_nonneg hCΦ (mul_nonneg (inv_nonneg.2 hη.le) (Finset.sum_nonneg fun j _ => ?_))
      exact add_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) _)
    · have hxc : x ∈ Gᶜ := hx
      rw [Set.indicator_of_mem hxc, norm_mul]
      simp only [hDdef, Set.indicator_of_mem hxc]
      refine mul_le_mul (hTb x) ((decor_norm_Y_le p hcd' hη x).trans ?_) (norm_nonneg _) hCΦ
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hamgm _)
        (inv_nonneg.2 hη.le)
  have hGc : M.prodLaw.real Gᶜ ≤ 2 * (N : ℝ) ^ (-20 : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      (prodLaw_not_goodSet_le hϑ hεg hεg' hN hIn hE hE₁ hE₂ M hM p)
  have hN20 : (N : ℝ) ^ (-20 : ℝ) = (s ^ 2)⁻¹ := by
    rw [Real.rpow_neg hNpos.le, show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      hsdef, ← pow_mul]
  have hterm : ∀ j : {i // i ∉ ({c} : Finset (Fin N))}, ∫ x, (‖x (Pair.mk' c j)‖ ^ 2 / (2 * s) +
      Gᶜ.indicator (fun _ => s / 2) x) ∂M.prodLaw ≤ 2 / s := by
    intro j
    rw [integral_add ((hmom _ 2).div_const _) ((integrable_const _).indicator hGm.compl),
      integral_div, integral_indicator_const _ hGm.compl, smul_eq_mul]
    have h1 := hvar j
    calc _ ≤ 1 / (2 * s) + 2 * (N : ℝ) ^ (-20 : ℝ) * (s / 2) :=
          add_le_add (div_le_div_of_nonneg_right h1 (by positivity))
            (mul_le_mul_of_nonneg_right hGc (by positivity))
      _ = 3 / 2 / s := by rw [hN20]; field_simp; ring
      _ ≤ 2 / s := div_le_div_of_nonneg_right (by norm_num) hs0.le
  have hcard : (Fintype.card {i // i ∉ ({c} : Finset (Fin N))} : ℝ) ≤ N := by
    have := Fintype.card_subtype_le (fun i : Fin N => i ∉ ({c} : Finset (Fin N)))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hηinv : η⁻¹ ≤ N := by
    have h1 : (N : ℝ)⁻¹ ≤ η := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have := inv_anti₀ (by positivity) h1
    rwa [inv_inv] at this
  have hΨN : 4 * (N : ℝ)⁻¹ ≤ Ψ := by
    rw [hΨdef]
    unfold edgePsi
    rw [← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
      (by norm_num)
  have hDle : ∫ x, D x ∂M.prodLaw ≤ CΦ * Ψ ^ 2 := by
    simp only [hDdef]
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ => hterm_int j]
    have hsum : ∑ j : {i // i ∉ ({c} : Finset (Fin N))}, ∫ x, (‖x (Pair.mk' c j)‖ ^ 2 / (2 * s) +
        Gᶜ.indicator (fun _ => s / 2) x) ∂M.prodLaw ≤ N * (2 / s) := by
      refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have hsum0 : 0 ≤ ∑ j : {i // i ∉ ({c} : Finset (Fin N))}, ∫ x, (‖x (Pair.mk' c j)‖ ^ 2 /
        (2 * s) + Gᶜ.indicator (fun _ => s / 2) x) ∂M.prodLaw :=
      Finset.sum_nonneg fun j _ => integral_nonneg fun x =>
        add_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) _)
    have hfin : (N : ℝ) * (N * (2 / s)) ≤ Ψ ^ 2 := by
      have h16 : 16 * ((N : ℝ) ^ 2)⁻¹ ≤ Ψ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hΨN 2
        rw [mul_pow, inv_pow] at this
        linarith
      refine le_trans ?_ h16
      rw [hsdef]
      have h8 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hN1 (by norm_num)
      rw [show (N : ℝ) * (N * (2 / (N : ℝ) ^ 10)) = 2 / (N : ℝ) ^ 8 by field_simp,
        ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc CΦ * (η⁻¹ * _) ≤ CΦ * (N * (N * (2 / s))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCΦ
          exact mul_le_mul hηinv hsum (by positivity) (by positivity)
      _ ≤ CΦ * Ψ ^ 2 := mul_le_mul_of_nonneg_left hfin hCΦ
  -- assembly: `1_𝒢 Φ(X(Q)) R_cd = 1_𝒢 (Φ(X(Q)) R_cd - T Y) + T Y - 1_{𝒢ᶜ} T Y`
  set A : (Pair N → 𝕜) → ℂ := fun x =>
    (Φ (smoothCount E₁ E₂ η (toMatrixC (Function.update x p 0))) : ℂ) *
      resolventMat (toMatrixC (Function.update x p 0)) ⟨y, η⟩ c d with hAdef
  set TY : (Pair N → 𝕜) → ℂ := fun x =>
    decorT Φ E₁ E₂ η p c x * decorY p hcd' ⟨y, η⟩ x with hTYdef
  have hsplit : ∀ x, G.indicator A x =
      G.indicator (fun x => A x - TY x) x + TY x - Gᶜ.indicator TY x := by
    intro x
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Set.indicator_of_notMem (show x ∉ Gᶜ from fun h => h hx)]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
        Set.indicator_of_mem (show x ∈ Gᶜ from hx)]
      ring
  have hI1pt : ∀ x, ‖G.indicator (fun x => A x - TY x) x‖ ≤ 8 / 3 * CΦ * Ψ ^ 2 := by
    intro x
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
      exact hgood x hx
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hI1int : Integrable (G.indicator fun x => A x - TY x) M.prodLaw :=
    Integrable.of_bound ((hAc.sub (hTc.mul hYc)).aestronglyMeasurable.indicator hGm)
      (8 / 3 * CΦ * Ψ ^ 2) (ae_of_all _ hI1pt)
  have hI3int : Integrable (Gᶜ.indicator TY) M.prodLaw := hTYint.indicator hGm.compl
  have h1 : ‖∫ x, G.indicator (fun x => A x - TY x) x ∂M.prodLaw‖ ≤ 8 / 3 * CΦ * Ψ ^ 2 := by
    refine (norm_integral_le_of_norm_le_const (ae_of_all _ hI1pt)).trans ?_
    rw [probReal_univ, mul_one]
  have h3 : ‖∫ x, Gᶜ.indicator TY x ∂M.prodLaw‖ ≤ CΦ * Ψ ^ 2 :=
    (norm_integral_le_of_norm_le hDint (ae_of_all _ hbadpt)).trans hDle
  rw [integral_congr_ae (ae_of_all _ hsplit),
    integral_sub (f := fun x => G.indicator (fun x => A x - TY x) x + TY x)
      (g := fun x => Gᶜ.indicator TY x) (hI1int.add hTYint) hI3int,
    integral_add hI1int hTYint, hTY0, add_zero]
  calc _ ≤ ‖∫ x, G.indicator (fun x => A x - TY x) x ∂M.prodLaw‖ +
        ‖∫ x, Gᶜ.indicator TY x ∂M.prodLaw‖ := norm_sub_le _ _
    _ ≤ 8 / 3 * CΦ * Ψ ^ 2 + CΦ * Ψ ^ 2 := add_le_add h1 h3
    _ ≤ 7 * CΦ * Ψ ^ 2 := by nlinarith [mul_nonneg hCΦ (sq_nonneg Ψ)]

end Rigidity
