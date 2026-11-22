module

public import Rigidity.LocalLaw.Lattice

@[expose] public section

/-!
# The initial estimate (NP v1.1, §5.2: Lemma 5.3)

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

At `η = 10` the Green function is bounded by `η⁻¹ = 1/10` entrywise, so on the good event `𝒢(z)`
the control parameter `Ψ_m` of (4.10) is of order `N^{-1/2}`; Lemma 4.6 (S5) bounds `X_i`, `A_i` and
`G_ij` by multiples of `𝔏 N^{-1/2}`, and the second identity of (3.6)
(Lemma 3.8) then gives `Λ_d ≤ Υ_max / 9`.  No a priori assumption and no stability analysis is
needed.

* `initial_estimate` (Lemma 5.3): for `N` large, `K ≥ (log N)³`, `Im z = 10` and `x ∈ 𝒢(z)`:
  `max_i |G_ii| ≤ 1/10` and `Λ_d + Λ_o ≤ 4 𝔏 N^{-1/2}`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### 1. The threshold -/

/-- If `N ≥ exp (max 2 κ_ϑ)` and `K ≥ (log N)³`, then `κ_ϑ + 3 log N ≤ K²`: with `L = log N ≥ 2`,
`K² ≥ L⁶ ≥ 4 L ≥ κ_ϑ + 3 L`. -/
private lemma weakInitial_kappa_le {ϑ : ℝ} {N : ℕ} {K : ℝ}
    (hN : Real.exp (max 2 (kappaTheta ϑ⁻¹)) ≤ N) (hK : Real.log N ^ 3 ≤ K) :
    kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ K ^ 2 := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN
  have hL : max 2 (kappaTheta ϑ⁻¹) ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 hN
  have hL2 : 2 ≤ Real.log N := (le_max_left _ _).trans hL
  have hLκ : kappaTheta ϑ⁻¹ ≤ Real.log N := (le_max_right _ _).trans hL
  have h3 : 0 ≤ Real.log N ^ 3 := by positivity
  have h6 : Real.log N ^ 6 ≤ K ^ 2 := by
    calc Real.log N ^ 6 = (Real.log N ^ 3) ^ 2 := by ring
      _ ≤ K ^ 2 := pow_le_pow_left₀ h3 hK 2
  have h5 : 32 ≤ Real.log N ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL2 5
  have h4 : 4 * Real.log N ≤ Real.log N ^ 6 := by
    have : Real.log N ^ 6 = Real.log N * Real.log N ^ 5 := by ring
    rw [this]
    nlinarith
  linarith

/-! ### 2. Entries of the Green function of a minor -/

/-- Lemma 3.5 (a) for the minors: `‖G^{(T)}_kl‖ ≤ η⁻¹`. -/
private lemma weakInitial_norm_greenT_le {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (k l : Fin N) :
    ‖greenT A T z k l‖ ≤ 1 / z.im := by
  by_cases h : k ∉ T ∧ l ∉ T
  · have hP : (minor A T).IsHermitian :=
      hA.submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    have : greenT A T z k l = green (minor A T) z ⟨k, h.1⟩ ⟨l, h.2⟩ := by
      simp [greenT, greenMinor, h.1, h.2]
    rw [this]
    exact norm_green_apply_le hP hz _ _
  · have : greenT A T z k l = 0 := by simp [greenT, h]
    rw [this, norm_zero]
    exact (one_div_pos.2 hz).le

/-- `‖m‖ ≤ c` if `‖G_kk‖ ≤ c` for all `k` (`N ≥ 1`). -/
private lemma weakInitial_norm_stieltjes_le {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (z : ℂ)
    {c : ℝ} (hc : ∀ k, ‖green A z k k‖ ≤ c) (hN : 0 < N) : ‖stieltjesEmp A z‖ ≤ c := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  unfold stieltjesEmp
  rw [Fintype.card_fin, norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
  have h1 : ‖∑ k, (green A z).diag k‖ ≤ N * c := by
    calc ‖∑ k, (green A z).diag k‖ ≤ ∑ k, ‖(green A z).diag k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin N, c := Finset.sum_le_sum fun k _ => hc k
      _ = N * c := by simp
  calc (N : ℝ)⁻¹ * ‖∑ k, (green A z).diag k‖ ≤ (N : ℝ)⁻¹ * (N * c) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c := by field_simp

/-! ### 3. The variance matrix -/

/-- The rows of the variance matrix sum to `1`: the columns do by (A), and `σ_ij² = σ_ji²`. -/
private lemma weakInitial_row_sum {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (i : Fin N) : ∑ j, M.varMatrix i j = 1 := by
  rw [← hM.sumA i]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Ensemble.varMatrix, Ensemble.var, Pair.mk'_comm i j]

/-- The variance matrix has nonnegative entries. -/
private lemma weakInitial_var_nonneg {N : ℕ} (M : Ensemble 𝕜 N) (i j : Fin N) :
    0 ≤ M.varMatrix i j :=
  integral_nonneg fun _ => by positivity

/-- A row of the variance matrix averages complex numbers of norm at most `c` to a complex number
of norm at most `c`. -/
private lemma weakInitial_norm_row_le {N : ℕ} {M : Ensemble 𝕜 N} {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (i : Fin N) {f : Fin N → ℂ} {c : ℝ}
    (hf : ∀ j, ‖f j‖ ≤ c) : ‖∑ j, (M.varMatrix i j : ℂ) * f j‖ ≤ c := by
  calc ‖∑ j, (M.varMatrix i j : ℂ) * f j‖ ≤ ∑ j, ‖(M.varMatrix i j : ℂ) * f j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j, M.varMatrix i j * c := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (weakInitial_var_nonneg M i j)]
        exact mul_le_mul_of_nonneg_left (hf j) (weakInitial_var_nonneg M i j)
    _ = c := by rw [← Finset.sum_mul, weakInitial_row_sum hM i, one_mul]

/-! ### 4. Lemma 5.3 -/

/-- Lemma 5.3: the initial estimate at `η = 10` (any `E`): on `𝒢(z)`, `maxᵢ |Gᵢᵢ| ≤ 1/10` and
`Λ_d + Λ_o ≤ 4 𝔏 N^{-1/2}`. -/
theorem initial_estimate {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z : ℂ, z.im = 10 → ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z,
        (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 10) ∧
        LamD x z + LamO x z ≤ 4 * levelFL ϑ⁻¹ C₀ K N / Real.sqrt N := by
  refine ⟨max 13 ⌈Real.exp (max 2 (kappaTheta ϑ⁻¹))⌉₊, ?_⟩
  intro N hN M hM K hK1 _ z hz x hx
  have hN13 : 13 ≤ N := (le_max_left _ _).trans hN
  have hNexp : Real.exp (max 2 (kappaTheta ϑ⁻¹)) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hzpos : 0 < z.im := by rw [hz]; norm_num
  have hA := toMatrix_isHermitian (𝕜 := 𝕜) x
  have hNpos : 0 < N := by omega
  have hNr : (13 : ℝ) ≤ N := by exact_mod_cast hN13
  obtain ⟨-, -, hcons, -⟩ := goodEvent_level M hM hϑ hϑ1 hC₀ hN13 hzpos
    (weakInitial_kappa_le hNexp hK1)
  -- entries of `G`, of the minors, and `m`
  have hG : ∀ i j, ‖green (toMatrix x) z i j‖ ≤ 1 / 10 := fun i j => by
    have := norm_green_apply_le hA hzpos i j
    rwa [hz] at this
  have hGT : ∀ i j, ‖greenT (toMatrix x) {i} z j j‖ ≤ 1 / 10 := fun i j => by
    have := weakInitial_norm_greenT_le hA hzpos {i} j j
    rwa [hz] at this
  refine ⟨fun i => hG i i, ?_⟩
  have hm : ‖stieltjesEmp (toMatrix x) z‖ ≤ 1 / 10 :=
    weakInitial_norm_stieltjes_le _ _ (fun k => hG k k) hNpos
  -- `t = N^{-1/2}`
  set t : ℝ := 1 / Real.sqrt N with ht
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by linarith)
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 = 1 / N := by rw [ht, div_pow, hsq]; ring
  have ht3 : t ≤ 1 / 3 := by
    by_contra h
    have h := not_le.1 h
    have h1 : t ^ 2 ≤ 1 / 13 := by
      rw [ht2]
      exact one_div_le_one_div_of_le (by norm_num) hNr
    nlinarith
  have htN : 1 / (N : ℝ) ≤ t := by
    rw [← ht2]; nlinarith
  -- `Ψ_m ≤ (6/5) t`
  have hΨ : ctrlPsiM x z ≤ 6 / 5 * t := by
    have hIm : (stieltjesEmp (toMatrix x) z).im ≤ 1 / 10 := (Complex.im_le_norm _).trans hm
    have e1 : Real.sqrt ((stieltjesEmp (toMatrix x) z).im / (N * z.im)) ≤ t / 10 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [hz, div_pow, ht2]
      have : (stieltjesEmp (toMatrix x) z).im / (N * 10) ≤ 1 / 10 / (N * 10) :=
        div_le_div_of_nonneg_right hIm (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    have e2 : 1 / ((N : ℝ) * z.im) ≤ t / 10 := by
      rw [hz]
      calc 1 / ((N : ℝ) * 10) = (1 / N) / 10 := by field_simp
        _ ≤ t / 10 := by gcongr
    unfold ctrlPsiM
    have : 1 / Real.sqrt (N : ℝ) = t := rfl
    rw [this]
    linarith
  have hΨ0 : 0 ≤ ctrlPsiM x z := by unfold ctrlPsiM; positivity
  -- `𝔏 ≥ 0`
  have hL0 : 0 ≤ levelFL ϑ⁻¹ C₀ K N := by
    unfold levelFL lossL2 lossL
    positivity
  set L := levelFL ϑ⁻¹ C₀ K N with hLdef
  have hLt : 0 ≤ L * t := by positivity
  -- another index for each `i`
  have hcard : 1 < Fintype.card (Fin N) := by rw [Fintype.card_fin]; omega
  -- bounds on `Υ_i` and `G_ij`
  have hUps : ∀ i, ‖selfUps (toMatrix x) M.varMatrix z i‖ ≤ 13 / 10 * (L * t) := by
    intro i
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    obtain ⟨h1, h2, -⟩ := hcons x hx i j hj.symm
    have hX : ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ 6 / 5 * (L * t) := by
      calc ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ L * ctrlPsiM x z := h1
        _ ≤ L * (6 / 5 * t) := mul_le_mul_of_nonneg_left hΨ hL0
        _ = 6 / 5 * (L * t) := by ring
    have hA' : ‖selfA (toMatrix x) M.varMatrix z i‖ ≤ 1 / 10 * (L * t) := by
      have hΨ2 : ctrlPsiM x z ^ 2 ≤ (6 / 5 * t) ^ 2 := pow_le_pow_left₀ hΨ0 hΨ 2
      have e : L * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 ≤
          L * (1 / 10) * (6 / 5 * t) ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (hG i i) hL0) hΨ2 (by positivity)
        positivity
      calc ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
            L * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 := h2
        _ ≤ L * (1 / 10) * (6 / 5 * t) ^ 2 := e
        _ = (L * t) * (36 / 250 * t) := by ring
        _ ≤ (L * t) * (1 / 10) := mul_le_mul_of_nonneg_left (by linarith) hLt
        _ = 1 / 10 * (L * t) := by ring
    calc ‖selfUps (toMatrix x) M.varMatrix z i‖
        = ‖selfA (toMatrix x) M.varMatrix z i + selfX (toMatrix x) M.varMatrix z i‖ := rfl
      _ ≤ ‖selfA (toMatrix x) M.varMatrix z i‖ + ‖selfX (toMatrix x) M.varMatrix z i‖ :=
          norm_add_le _ _
      _ ≤ 13 / 10 * (L * t) := by linarith
  have hLamO : LamO x z ≤ L * t := by
    refine Real.iSup_le (fun q => ?_) hLt
    obtain ⟨-, -, h3⟩ := hcons x hx q.1.1 q.1.2 q.2
    calc ‖green (toMatrix x) z q.1.1 q.1.2‖
        ≤ L * ‖green (toMatrix x) z q.1.1 q.1.1‖ * ‖greenT (toMatrix x) {q.1.1} z q.1.2 q.1.2‖ *
          ctrlPsiM x z := h3
      _ ≤ L * (1 / 10) * (1 / 10) * (6 / 5 * t) := by
          apply mul_le_mul _ hΨ hΨ0 (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hG _ _) hL0) (hGT _ _) (norm_nonneg _)
            (by positivity)
      _ ≤ L * t := by nlinarith
  -- the second identity of (3.6)
  have hLamD : LamD x z ≤ L * t := by
    have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    set U : ℝ := 13 / 10 * (L * t) with hU
    have hLD0 : 0 ≤ LamD x z :=
      Real.iSup_nonneg fun k => norm_nonneg _
    have hv : ∀ j, ‖green (toMatrix x) z j j - msc z‖ ≤ LamD x z := fun j =>
      le_ciSup (Finite.bddAbove_range fun k : Fin N => ‖green (toMatrix x) z k k - msc z‖) j
    have hbd : ∀ i, ‖green (toMatrix x) z i i - msc z‖ ≤ 1 / 10 * (LamD x z + U) := by
      intro i
      obtain ⟨-, e2, -⟩ := sce hA (weakInitial_row_sum hM) hzpos i
      rw [e2, norm_mul, norm_mul]
      have hs : ‖∑ j, (M.varMatrix i j : ℂ) * (green (toMatrix x) z j j - msc z)‖ ≤ LamD x z :=
        weakInitial_norm_row_le hM i hv
      have hdiff : ‖∑ j, (M.varMatrix i j : ℂ) * (green (toMatrix x) z j j - msc z) -
          selfUps (toMatrix x) M.varMatrix z i‖ ≤ LamD x z + U :=
        (norm_sub_le _ _).trans (add_le_add hs (hUps i))
      have hm1 : ‖msc z‖ ≤ 1 := (norm_msc_lt_one hzpos).le
      calc ‖msc z‖ * ‖green (toMatrix x) z i i‖ * ‖∑ j, (M.varMatrix i j : ℂ) *
            (green (toMatrix x) z j j - msc z) - selfUps (toMatrix x) M.varMatrix z i‖
          ≤ 1 * (1 / 10) * (LamD x z + U) := by
            apply mul_le_mul (mul_le_mul hm1 (hG i i) (norm_nonneg _) (by norm_num)) hdiff
              (norm_nonneg _) (by norm_num)
        _ = 1 / 10 * (LamD x z + U) := by ring
    have h1 : LamD x z ≤ 1 / 10 * (LamD x z + U) := ciSup_le hbd
    have h2 : LamD x z ≤ U / 9 := by linarith
    calc LamD x z ≤ U / 9 := h2
      _ ≤ L * t := by rw [hU]; linarith
  calc LamD x z + LamO x z ≤ L * t + L * t := add_le_add hLamD hLamO
    _ ≤ 4 * L / Real.sqrt N := by
        have : 4 * L / Real.sqrt N = 4 * (L * t) := by rw [ht]; ring
        rw [this]
        linarith

end Rigidity
