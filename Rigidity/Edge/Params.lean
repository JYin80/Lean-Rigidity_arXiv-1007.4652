import Mathlib

/-!
# Edge parameters and the largeness of `N`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The file defines the parameters `L₀`, `W`, `E_L` of (11.1) and `η`, `ℓ`, `Ψ`, `t` of (11.2) of
Section 11.  The structure `EdgeLarge` bundles the conditions on `N` of Lemma 11.2 that involve no
probabilistic input: `N ≥ e^27`, the upper bound in (N1) and the lower bound for `η`, (N2), the
second half of (N3), (N4) and (N5).  The theorem `exists_edgeLarge` shows that they hold for all
large `N`, and `exists_partI_bound_le` is the first half of (N3).  Both thresholds are existential.

The proofs write `u = log log N`, so that `log N = e^u`, `N^x = exp (x e^u)` and
`(log N)^{a L₀} = exp (a A₀ u²)`; every condition then reduces to an inequality
`α u² + β ≤ γ e^u` (the elementary inequality (E) in the proof of Lemma 11.2) or to an inequality
`u + β ≤ γ u²`.
-/

open Real

namespace Rigidity

/-- `L₀ = A₀ log log N` (11.1). -/
noncomputable def edgeL0 (A₀ : ℝ) (N : ℕ) : ℝ := A₀ * Real.log (Real.log N)

/-- `W = (log N)^{L₀} N^{-2/3}` (11.1). -/
noncomputable def edgeW (A₀ : ℝ) (N : ℕ) : ℝ :=
  Real.log N ^ edgeL0 A₀ N * (N : ℝ) ^ (-(2 / 3 : ℝ))

/-- `E_L = 2 + 2W` (11.1). -/
noncomputable def edgeEL (A₀ : ℝ) (N : ℕ) : ℝ := 2 + 2 * edgeW A₀ N

/-- `η = N^{-2/3-ε_g}` (11.2). -/
noncomputable def edgeEta (εg : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ) - εg)

/-- `ℓ = N^{-2/3-ε}/3` with `ε = ε_g/2` (11.2). -/
noncomputable def edgeEll (εg : ℝ) (N : ℕ) : ℝ := (1 / 3) * (N : ℝ) ^ (-(2 / 3 : ℝ) - εg / 2)

/-- `Ψ = 4 N^{-1/3+2ε_g}` (11.2). -/
noncomputable def edgePsi (εg : ℝ) (N : ℕ) : ℝ := 4 * (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg)

/-- `t = N^{-1/2+2ε_g}` (11.2). -/
noncomputable def edgeT (εg : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ) + 2 * εg)

/-- The deterministic conditions on `N` of Lemma 11.2: `N ≥ e^{27}`, (N1) without the
inputs (BB1), (BB2), (N2), the second half of (N3), (N4), (N5). -/
structure EdgeLarge (ϑ C₀ A₀ εg : ℝ) (N : ℕ) : Prop where
  exp_le : Real.exp 27 ≤ N
  L0_le : edgeL0 A₀ N ≤ Real.log (10 * N) / (10 * Real.log (Real.log N))
  eta_gt : (N : ℝ)⁻¹ * Real.log N ^ (10 * edgeL0 A₀ N) < edgeEta εg N
  logPow_le : 3 * Real.log N ^ (4 * edgeL0 A₀ N) ≤ (N : ℝ) ^ (εg / 2)
  logPow_le' : 2 * Real.log N ^ edgeL0 A₀ N + 1 ≤ (N : ℝ) ^ εg
  tail_le : ϑ⁻¹ * Real.exp (-((N : ℝ) ^ (εg * ϑ))) ≤ (N : ℝ) ^ (-20 : ℝ)
  sqrt_le : Real.sqrt C₀ ≤ (N : ℝ) ^ εg
  psi_le : edgePsi εg N ≤ 1 / 8
  t_le : 40 * edgeT εg N ≤ edgePsi εg N
  sandwich_le : 3 / π * (4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) + 1) * (N : ℝ) ^ (-(εg / 2)) +
      4 * (N : ℝ) ^ (-εg) * Real.log N ^ edgeL0 A₀ N ≤ 1 / 9
  sandwich_le' : 6 / π * (N : ℝ) ^ (-(εg / 2)) ≤ 1 / 9
  ell_le : 2 * edgeEll εg N ≤ edgeW A₀ N

/-- `a ^ x = exp (x log a)` for `a > 0`. -/
private lemma edgeParams_rpow (a x : ℝ) (ha : 0 < a) : a ^ x = Real.exp (x * Real.log a) := by
  rw [Real.rpow_def_of_pos ha, mul_comm]

/-- The elementary inequality (E) of Lemma 11.2: for `α, β ≥ 0` and `γ > 0`, the inequality
`α u² + β ≤ γ e^u` holds for all large `u`. -/
private lemma edgeParams_quad_le_exp (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → α * u ^ 2 + β ≤ γ * Real.exp u := by
  refine ⟨max 1 (Real.sqrt (24 * (α + β) / γ)), le_max_left _ _, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu2 : Real.sqrt (24 * (α + β) / γ) ≤ u := le_trans (le_max_right _ _) hu
  have h0 : 0 ≤ 24 * (α + β) / γ := by positivity
  have hsq : 24 * (α + β) / γ ≤ u ^ 2 := by
    calc 24 * (α + β) / γ = Real.sqrt (24 * (α + β) / γ) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ u ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hu2 2
  have h24 : 24 * (α + β) ≤ γ * u ^ 2 := by
    rw [div_le_iff₀ hγ] at hsq
    linarith
  have hexp : u ^ 4 / 24 ≤ Real.exp u := by
    have := Real.pow_div_factorial_le_exp u (by linarith) 4
    simpa [Nat.factorial] using this
  have hu2' : 1 ≤ u ^ 2 := by nlinarith
  have hu4 : 0 ≤ u ^ 2 := by positivity
  calc α * u ^ 2 + β ≤ (α + β) * u ^ 2 := by nlinarith
    _ ≤ γ * u ^ 2 * u ^ 2 / 24 := by nlinarith
    _ = γ * (u ^ 4 / 24) := by ring
    _ ≤ γ * Real.exp u := by gcongr

/-- For `γ > 0` and `β ≥ 0`, the inequality `u + β ≤ γ u²` holds for all large `u`. -/
private lemma edgeParams_lin_le_quad (β γ : ℝ) (hβ : 0 ≤ β) (hγ : 0 < γ) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ u : ℝ, U ≤ u → u + β ≤ γ * u ^ 2 := by
  refine ⟨max 1 ((1 + β) / γ), le_max_left _ _, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu2 : (1 + β) / γ ≤ u := le_trans (le_max_right _ _) hu
  have h3 : 1 + β ≤ γ * u := by
    rw [div_le_iff₀ hγ, mul_comm] at hu2
    exact hu2
  nlinarith [mul_nonneg (by linarith : 0 ≤ u) (by linarith : 0 ≤ γ * u - (1 + β)),
    mul_nonneg (by linarith : 0 ≤ u - 1) hβ]

/-- For every `U` there is `N₁` such that `N ≥ N₁` implies `N ≥ e^27` and `U ≤ log log N`. -/
private lemma edgeParams_bridge (U : ℝ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → Real.exp 27 ≤ (N : ℝ) ∧ U ≤ Real.log (Real.log N) := by
  refine ⟨⌈max (Real.exp (Real.exp U)) (Real.exp 27)⌉₊, fun N hN => ?_⟩
  have hN' : max (Real.exp (Real.exp U)) (Real.exp 27) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h1 : Real.exp (Real.exp U) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN'
  have h2 : Real.exp 27 ≤ (N : ℝ) := le_trans (le_max_right _ _) hN'
  refine ⟨h2, ?_⟩
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) h2
  have h3 : Real.exp U ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).2 h1
  exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h3)).2 h3

/-- The data shared by the field lemmas below: `T = log N`, `u = log T`, `N ≥ e^27`, `T ≥ 1000`,
and the inequality `4 A₀ u² + 81 ≤ (ε_g/2) T` (the form of (E) used throughout). -/
private structure EdgeCtx (A₀ εg : ℝ) (N : ℕ) (T u : ℝ) : Prop where
  hT : Real.log (N : ℝ) = T
  hu : Real.log T = u
  hN27 : Real.exp 27 ≤ (N : ℝ)
  hT1000 : 1000 ≤ T
  hA₀ : 0 < A₀
  hεg : 0 < εg
  hεg' : εg ≤ 1 / 10
  c1 : 4 * A₀ * u ^ 2 + 81 ≤ εg / 2 * T

private lemma edgeParams_Npos {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) h.hN27

private lemma edgeParams_N1 {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) h.hN27

private lemma edgeParams_Tpos {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    0 < T := by linarith [h.hT1000]

private lemma edgeParams_upos {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    0 < u := by
  rw [← h.hu]
  exact Real.log_pos (by linarith [h.hT1000])

private lemma edgeParams_Npow {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) (x : ℝ) :
    (N : ℝ) ^ x = Real.exp (x * T) := by
  rw [edgeParams_rpow _ _ (edgeParams_Npos h), h.hT]

private lemma edgeParams_Tpow {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) (y : ℝ) :
    T ^ y = Real.exp (y * u) := by
  rw [edgeParams_rpow _ _ (edgeParams_Tpos h), h.hu]

private lemma edgeParams_L0 {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    edgeL0 A₀ N = A₀ * u := by
  unfold edgeL0
  rw [h.hT, h.hu]

/-- `80 A₀ u² ≤ T`. -/
private lemma edgeParams_A {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    80 * (A₀ * u ^ 2) ≤ T := by
  have hT0 := edgeParams_Tpos h
  have h1 := h.c1
  have h2 := h.hεg'
  nlinarith [mul_nonneg (sub_nonneg.2 h2) hT0.le]

private lemma edgeParams_Xone {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) (a : ℝ)
    (ha : 0 ≤ a) : 1 ≤ T ^ (a * (A₀ * u)) := by
  have := edgeParams_upos h
  have := h.hA₀
  exact Real.one_le_rpow (by linarith [h.hT1000]) (by positivity)

private lemma edgeParams_L0_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    edgeL0 A₀ N ≤ Real.log (10 * N) / (10 * Real.log (Real.log N)) := by
  have hu0 := edgeParams_upos h
  have hNpos := edgeParams_Npos h
  rw [edgeParams_L0 h, h.hT, h.hu, le_div_iff₀ (by positivity)]
  have h1 : Real.log (N : ℝ) ≤ Real.log (10 * N) := Real.log_le_log hNpos (by linarith)
  rw [h.hT] at h1
  have hA₀ := h.hA₀
  have hA2 : 0 ≤ A₀ * u ^ 2 := by positivity
  nlinarith [edgeParams_A h]

private lemma edgeParams_eta_gt {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    (N : ℝ)⁻¹ * Real.log N ^ (10 * edgeL0 A₀ N) < edgeEta εg N := by
  have hNpos := edgeParams_Npos h
  have hT0 := edgeParams_Tpos h
  have hNeq : Real.exp T = N := by rw [← h.hT]; exact Real.exp_log hNpos
  unfold edgeEta
  rw [edgeParams_L0 h, h.hT, edgeParams_Npow h, edgeParams_Tpow h]
  have hNinv : (N : ℝ)⁻¹ = Real.exp (-T) := by rw [Real.exp_neg, hNeq]
  rw [hNinv, ← Real.exp_add, Real.exp_lt_exp]
  have := h.hεg'
  nlinarith [mul_pos hT0 (by linarith : (0 : ℝ) < 1 / 3 - εg - 1 / 8), edgeParams_A h]

private lemma edgeParams_logPow_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    3 * Real.log N ^ (4 * edgeL0 A₀ N) ≤ (N : ℝ) ^ (εg / 2) := by
  rw [edgeParams_L0 h, h.hT, edgeParams_Tpow h, edgeParams_Npow h]
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h1 := h.c1
  have hA2 : 0 ≤ A₀ * u ^ 2 := by have := h.hA₀; positivity
  calc 3 * Real.exp (4 * (A₀ * u) * u) ≤ Real.exp 3 * Real.exp (4 * (A₀ * u) * u) := by gcongr
    _ = Real.exp (3 + 4 * (A₀ * u) * u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (εg / 2 * T) := Real.exp_le_exp.2 (by nlinarith)

private lemma edgeParams_logPow_le' {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    2 * Real.log N ^ edgeL0 A₀ N + 1 ≤ (N : ℝ) ^ εg := by
  have hLP := edgeParams_logPow_le h
  have hX1 := edgeParams_Xone h 1 (by norm_num)
  rw [edgeParams_L0 h, h.hT] at hLP ⊢
  rw [one_mul] at hX1
  have hu0 := edgeParams_upos h
  have hA₀ := h.hA₀
  have h1 : T ^ (A₀ * u) ≤ T ^ (4 * (A₀ * u)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [h.hT1000]) (by nlinarith [mul_pos hA₀ hu0])
  have h2 : (N : ℝ) ^ (εg / 2) ≤ (N : ℝ) ^ εg :=
    Real.rpow_le_rpow_of_exponent_le (edgeParams_N1 h) (by linarith [h.hεg])
  linarith

private lemma edgeParams_sqrt_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u)
    (C₀ : ℝ) (c3 : Real.sqrt C₀ ≤ εg * T) : Real.sqrt C₀ ≤ (N : ℝ) ^ εg := by
  rw [edgeParams_Npow h]
  linarith [Real.add_one_le_exp (εg * T)]

private lemma edgeParams_psi_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    edgePsi εg N ≤ 1 / 8 := by
  unfold edgePsi
  rw [edgeParams_Npow h]
  have h32 : (32 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have hT0 := edgeParams_Tpos h
  have hc : (-(1 / 3 : ℝ) + 2 * εg) ≤ -(2 / 15) := by linarith [h.hεg']
  have hex : (-(1 / 3 : ℝ) + 2 * εg) * T ≤ -32 := by
    calc (-(1 / 3 : ℝ) + 2 * εg) * T ≤ -(2 / 15) * T := mul_le_mul_of_nonneg_right hc hT0.le
      _ ≤ -32 := by linarith [h.hT1000]
  have h1 : 32 * Real.exp ((-(1 / 3 : ℝ) + 2 * εg) * T) ≤ 1 := by
    calc 32 * Real.exp ((-(1 / 3 : ℝ) + 2 * εg) * T)
        ≤ Real.exp 32 * Real.exp ((-(1 / 3 : ℝ) + 2 * εg) * T) := by gcongr
      _ = Real.exp (32 + (-(1 / 3 : ℝ) + 2 * εg) * T) := (Real.exp_add _ _).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  linarith

private lemma edgeParams_t_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    40 * edgeT εg N ≤ edgePsi εg N := by
  unfold edgeT edgePsi
  rw [edgeParams_Npow h, edgeParams_Npow h]
  have h10 : (10 : ℝ) ≤ Real.exp (T / 6) := by
    linarith [Real.add_one_le_exp (T / 6), h.hT1000]
  have hE := Real.exp_pos ((-(1 / 2 : ℝ) + 2 * εg) * T)
  rw [show (-(1 / 3 : ℝ) + 2 * εg) * T = (-(1 / 2 : ℝ) + 2 * εg) * T + T / 6 by ring,
    Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left h10 hE.le]

/-- `81 · (log N)^{3 L₀/2} · N^{-ε_g/2} ≤ 1`. -/
private lemma edgeParams_key {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    81 * T ^ (3 / 2 * (A₀ * u)) * (N : ℝ) ^ (-(εg / 2)) ≤ 1 := by
  rw [edgeParams_Tpow h, edgeParams_Npow h]
  have h81 : (81 : ℝ) ≤ Real.exp 81 := by linarith [Real.add_one_le_exp (81 : ℝ)]
  have h1 := h.c1
  have hA2 : 0 ≤ A₀ * u ^ 2 := by have := h.hA₀; positivity
  calc 81 * Real.exp (3 / 2 * (A₀ * u) * u) * Real.exp (-(εg / 2) * T)
      ≤ Real.exp 81 * Real.exp (3 / 2 * (A₀ * u) * u) * Real.exp (-(εg / 2) * T) := by gcongr
    _ = Real.exp (81 + 3 / 2 * (A₀ * u) * u + -(εg / 2) * T) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by nlinarith)
    _ = 1 := Real.exp_zero

private lemma edgeParams_sandwich_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    3 / π * (4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) + 1) * (N : ℝ) ^ (-(εg / 2)) +
      4 * (N : ℝ) ^ (-εg) * Real.log N ^ edgeL0 A₀ N ≤ 1 / 9 := by
  have hkey := edgeParams_key h
  have hY1 := edgeParams_Xone h (3 / 2) (by norm_num)
  have hX1 := edgeParams_Xone h 1 (by norm_num)
  rw [one_mul] at hX1
  rw [edgeParams_L0 h, h.hT]
  have hu0 := edgeParams_upos h
  have hA₀ := h.hA₀
  have hNpos := edgeParams_Npos h
  have hqpos : 0 < (N : ℝ) ^ (-(εg / 2)) := Real.rpow_pos_of_pos hNpos _
  have hq'pos : 0 < (N : ℝ) ^ (-εg) := Real.rpow_pos_of_pos hNpos _
  have hqq' : (N : ℝ) ^ (-εg) ≤ (N : ℝ) ^ (-(εg / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (edgeParams_N1 h) (by linarith [h.hεg])
  have hXY : T ^ (A₀ * u) ≤ T ^ (3 / 2 * (A₀ * u)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [h.hT1000]) (by nlinarith [mul_pos hA₀ hu0])
  have hpi : 3 / π ≤ 1 := (div_le_one Real.pi_pos).2 Real.pi_gt_three.le
  have h1 : 3 / π * (4 * T ^ (3 / 2 * (A₀ * u)) + 1) ≤ 5 * T ^ (3 / 2 * (A₀ * u)) := by
    calc 3 / π * (4 * T ^ (3 / 2 * (A₀ * u)) + 1) ≤ 1 * (4 * T ^ (3 / 2 * (A₀ * u)) + 1) :=
          mul_le_mul_of_nonneg_right hpi (by linarith)
      _ ≤ 5 * T ^ (3 / 2 * (A₀ * u)) := by linarith
  have h2 : 3 / π * (4 * T ^ (3 / 2 * (A₀ * u)) + 1) * (N : ℝ) ^ (-(εg / 2)) ≤
      5 * T ^ (3 / 2 * (A₀ * u)) * (N : ℝ) ^ (-(εg / 2)) :=
    mul_le_mul_of_nonneg_right h1 hqpos.le
  have h3 : 4 * (N : ℝ) ^ (-εg) * T ^ (A₀ * u) ≤
      4 * (N : ℝ) ^ (-(εg / 2)) * T ^ (3 / 2 * (A₀ * u)) :=
    mul_le_mul (by linarith) hXY (by linarith) (by positivity)
  nlinarith

private lemma edgeParams_sandwich_le' {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    6 / π * (N : ℝ) ^ (-(εg / 2)) ≤ 1 / 9 := by
  have hkey := edgeParams_key h
  have hY1 := edgeParams_Xone h (3 / 2) (by norm_num)
  have hqpos : 0 < (N : ℝ) ^ (-(εg / 2)) := Real.rpow_pos_of_pos (edgeParams_Npos h) _
  have hpi6 : 6 / π ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  have h1 : 81 * (N : ℝ) ^ (-(εg / 2)) ≤ 81 * T ^ (3 / 2 * (A₀ * u)) * (N : ℝ) ^ (-(εg / 2)) := by
    nlinarith
  have h2 : 6 / π * (N : ℝ) ^ (-(εg / 2)) ≤ 2 * (N : ℝ) ^ (-(εg / 2)) :=
    mul_le_mul_of_nonneg_right hpi6 hqpos.le
  linarith

private lemma edgeParams_ell_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u) :
    2 * edgeEll εg N ≤ edgeW A₀ N := by
  have hX1 := edgeParams_Xone h 1 (by norm_num)
  rw [one_mul] at hX1
  unfold edgeEll edgeW
  rw [edgeParams_L0 h, h.hT]
  have h1 : (N : ℝ) ^ (-(2 / 3 : ℝ) - εg / 2) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (edgeParams_N1 h) (by linarith [h.hεg])
  have h2 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (edgeParams_Npos h) _
  nlinarith [mul_le_mul_of_nonneg_right hX1 h2.le]

private lemma edgeParams_tail_le {A₀ εg : ℝ} {N : ℕ} {T u : ℝ} (h : EdgeCtx A₀ εg N T u)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (c2 : u + Real.log (20 + |Real.log ϑ|) ≤ εg * ϑ * T) :
    ϑ⁻¹ * Real.exp (-((N : ℝ) ^ (εg * ϑ))) ≤ (N : ℝ) ^ (-20 : ℝ) := by
  have hT0 := edgeParams_Tpos h
  have hexpu : Real.exp u = T := by rw [← h.hu]; exact Real.exp_log hT0
  simp only [edgeParams_Npow h]
  have hK : 0 < 20 + |Real.log ϑ| := by positivity
  have hM : 20 * T + Real.log ϑ⁻¹ ≤ Real.exp (εg * ϑ * T) := by
    have h2 : Real.exp (u + Real.log (20 + |Real.log ϑ|)) ≤ Real.exp (εg * ϑ * T) :=
      Real.exp_le_exp.2 c2
    rw [Real.exp_add, Real.exp_log hK, hexpu] at h2
    have h3 : Real.log ϑ⁻¹ ≤ |Real.log ϑ| := by
      rw [Real.log_inv]
      exact neg_le_abs _
    nlinarith [mul_nonneg (abs_nonneg (Real.log ϑ)) (by linarith [h.hT1000] : (0 : ℝ) ≤ T - 1)]
  have hϑinv : 0 < ϑ⁻¹ := inv_pos.2 hϑ
  calc ϑ⁻¹ * Real.exp (-Real.exp (εg * ϑ * T))
      ≤ ϑ⁻¹ * Real.exp (-(20 * T + Real.log ϑ⁻¹)) := by gcongr
    _ = Real.exp (-20 * T) := by
        rw [neg_add, Real.exp_add, Real.exp_neg (Real.log ϑ⁻¹), Real.exp_log hϑinv, inv_inv,
          show -(20 * T) = -20 * T by ring]
        field_simp

/-- Lemma 11.2, deterministic part. -/
theorem exists_edgeLarge (ϑ C₀ A₀ εg : ℝ) (hϑ : 0 < ϑ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀)
    (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → EdgeLarge ϑ C₀ A₀ εg N := by
  have _ := hC₀
  obtain ⟨U₁, -, h₁⟩ := edgeParams_quad_le_exp (4 * A₀) 81 (εg / 2) (by positivity)
    (by norm_num) (by positivity)
  have hK : 1 ≤ 20 + |Real.log ϑ| := by linarith [abs_nonneg (Real.log ϑ)]
  obtain ⟨U₂, hU₂, h₂⟩ := edgeParams_quad_le_exp 1 (Real.log (20 + |Real.log ϑ|)) (εg * ϑ)
    (by norm_num) (Real.log_nonneg hK) (by positivity)
  obtain ⟨U₃, -, h₃⟩ := edgeParams_quad_le_exp 0 (Real.sqrt C₀) εg le_rfl (Real.sqrt_nonneg _) hεg
  obtain ⟨N₁, hN₁⟩ := edgeParams_bridge (max (max U₁ U₂) (max U₃ (Real.log 1000)))
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨hN27, hu⟩ := hN₁ N hN
  obtain ⟨T, hT⟩ : ∃ T : ℝ, Real.log (N : ℝ) = T := ⟨_, rfl⟩
  obtain ⟨u, hu'⟩ : ∃ u : ℝ, Real.log T = u := ⟨_, rfl⟩
  rw [hT, hu'] at hu
  have hu₁ : U₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hu₂ : U₂ ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hu₃ : U₃ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hu₄ : Real.log 1000 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hu
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN27
  have hT27 : 27 ≤ T := by rw [← hT]; exact (Real.le_log_iff_exp_le hNpos).2 hN27
  have hTpos : 0 < T := by linarith
  have hexpu : Real.exp u = T := by rw [← hu']; exact Real.exp_log hTpos
  have hT1000 : 1000 ≤ T := by
    have h := (Real.le_log_iff_exp_le hTpos).1 (hu' ▸ hu₄)
    rwa [Real.exp_log (by norm_num)] at h
  have c1 := h₁ u hu₁
  have c2 := h₂ u hu₂
  have c3 := h₃ u hu₃
  rw [hexpu] at c1 c2 c3
  have hu1 : 1 ≤ u := le_trans hU₂ hu₂
  have c2' : u + Real.log (20 + |Real.log ϑ|) ≤ εg * ϑ * T := by nlinarith
  have c3' : Real.sqrt C₀ ≤ εg * T := by linarith
  have h := EdgeCtx.mk (A₀ := A₀) (εg := εg) (N := N) (T := T) (u := u) hT hu' hN27 hT1000 hA₀ hεg
    hεg' c1
  exact ⟨hN27, edgeParams_L0_le h, edgeParams_eta_gt h, edgeParams_logPow_le h,
    edgeParams_logPow_le' h, edgeParams_tail_le h ϑ hϑ c2', edgeParams_sqrt_le h C₀ c3',
    edgeParams_psi_le h, edgeParams_t_le h, edgeParams_sandwich_le h, edgeParams_sandwich_le' h,
    edgeParams_ell_le h⟩

/-- Lemma 11.2, first half of (N3): the bound of (BB1), (BB2) at `L = L₀` is at most `N^{-20}`. -/
theorem exists_partI_bound_le (A₀ C c φ : ℝ) (hA₀ : 0 < A₀) (hc : 0 < c) (hφ : 0 < φ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      C * Real.exp (-c * Real.log N ^ (φ * edgeL0 A₀ N)) ≤ (N : ℝ) ^ (-20 : ℝ) := by
  have hK : 0 < (|C| + 20) / c := by positivity
  obtain ⟨U, hU1, hU⟩ := edgeParams_lin_le_quad |Real.log ((|C| + 20) / c)| (φ * A₀)
    (abs_nonneg _) (mul_pos hφ hA₀)
  obtain ⟨N₁, hN₁⟩ := edgeParams_bridge U
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨hN27, hu⟩ := hN₁ N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN27
  obtain ⟨T, hT⟩ : ∃ T : ℝ, Real.log (N : ℝ) = T := ⟨_, rfl⟩
  obtain ⟨u, hu'⟩ : ∃ u : ℝ, Real.log T = u := ⟨_, rfl⟩
  rw [hT, hu'] at hu
  have hT27 : 27 ≤ T := by rw [← hT]; exact (Real.le_log_iff_exp_le hNpos).2 hN27
  have hTpos : 0 < T := by linarith
  have hexpu : Real.exp u = T := by rw [← hu']; exact Real.exp_log hTpos
  have hNpow : ∀ x : ℝ, (N : ℝ) ^ x = Real.exp (x * T) := fun x => by
    rw [edgeParams_rpow _ _ hNpos, hT]
  have hTpow : ∀ y : ℝ, T ^ y = Real.exp (y * u) := fun y => by
    rw [edgeParams_rpow _ _ hTpos, hu']
  have hL0 : edgeL0 A₀ N = A₀ * u := by unfold edgeL0; rw [hT, hu']
  rw [hL0, hT, hTpow, hNpow]
  have h1 : Real.exp (u + |Real.log ((|C| + 20) / c)|) ≤ Real.exp (φ * (A₀ * u) * u) :=
    Real.exp_le_exp.2 (by nlinarith [hU u hu])
  have h2 : (|C| + 20) / c ≤ Real.exp |Real.log ((|C| + 20) / c)| := by
    calc (|C| + 20) / c = Real.exp (Real.log ((|C| + 20) / c)) := (Real.exp_log hK).symm
      _ ≤ Real.exp |Real.log ((|C| + 20) / c)| := Real.exp_le_exp.2 (le_abs_self _)
  rw [Real.exp_add, hexpu] at h1
  have hZ : (|C| + 20) / c * T ≤ Real.exp (φ * (A₀ * u) * u) :=
    le_trans (by nlinarith [mul_le_mul_of_nonneg_left h2 hTpos.le]) h1
  have hcZ : (|C| + 20) * T ≤ c * Real.exp (φ * (A₀ * u) * u) := by
    have := mul_le_mul_of_nonneg_left hZ hc.le
    calc (|C| + 20) * T = c * ((|C| + 20) / c * T) := by field_simp
      _ ≤ _ := this
  have hCle : C ≤ Real.exp (c * Real.exp (φ * (A₀ * u) * u) - 20 * T) := by
    calc C ≤ |C| := le_abs_self C
      _ ≤ |C| + 1 := by linarith
      _ ≤ Real.exp |C| := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.2 (by nlinarith [abs_nonneg C])
  calc C * Real.exp (-c * Real.exp (φ * (A₀ * u) * u))
      ≤ Real.exp (c * Real.exp (φ * (A₀ * u) * u) - 20 * T) *
          Real.exp (-c * Real.exp (φ * (A₀ * u) * u)) :=
        mul_le_mul_of_nonneg_right hCle (Real.exp_pos _).le
    _ = Real.exp (-20 * T) := by
        rw [← Real.exp_add]; congr 1; ring

end Rigidity
