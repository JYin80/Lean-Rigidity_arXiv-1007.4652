import Rigidity.LocalLaw.GoodEvent
import Rigidity.LocalLaw.Ledger
import Rigidity.Probability.Moments

/-!
# The levels `p₁`, `p₂`, `𝔏`, `E_max` and the standing inequalities

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For the level parameter `K` in the range `(log N)³ ≤ K ≤ N^{c₀}`, this file proves:
* Definition 4.4: the integers `p₁ = 2⌈K^{3/2}/2⌉`, `p₂ = 2⌈K/2⌉` and the constants
  `𝔏 = 3 C₀² ℓ₂(K², N)`, `E_max = 25 (K²)^{ϑ⁻¹} √(C₀ log N)`;
* Lemma 4.6 (S1)–(S4), `standing_ineq`: for `N` large and `(log N)³ ≤ K ≤ N^{c₀}`, with `c₀` of the
  exponent ledger (A.1), the inequalities `K ≥ K₀`, `N ≥ 13`, `C₀ ≤ N²`,
  `κ_ϑ + 3 log N ≤ K²`, `150 ≤ 𝔏 ≤ K^{4ϑ⁻¹+3}`, `1 ≤ E_max ≤ K^{2ϑ⁻¹+1}`, the level relations
  (4.14), `K^{3/2} ≤ p₁ ≤ 2 K^{3/2}`, and `K^{6ϑ⁻¹+6} ≤ N^{1/32}`, `K₀ N^{1/32} ≤ N^{1/8}`;
* Convention 1.2, `exp_le_of_level`: `N^C e^{-K} ≤ e^{-K/2}` for `K ≥ (log N)³` and
  `(log N)² ≥ 2C`;
* Lemma 4.6 (S5), `goodEvent_level`: the good event `𝒢(z) = 𝒢_{K²}(z)` (Definition 4.3, Lemma 4.4
  at `κ = K²`) is closed, has `ℙ(𝒢(z)ᶜ) ≤ 46 ϑ⁻¹ N⁴ e^{-K²}`, and on it `|X_i| ≤ 𝔏 Ψ_m`,
  `|A_i| ≤ 𝔏 |G_ii| Ψ_m²`, `|G_ij| ≤ 𝔏 |G_ii| |G^{(i)}_jj| Ψ_m`; under `46/ϑ ≤ N`,
  `(log N)² ≥ 10` and `K ≥ (log N)³` the bound is `ℙ(𝒢(z)ᶜ) ≤ e^{-K}`.

The ledger values of `c₀` enter through `ledger_closes` (Lemma A.1, relation (L2)).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory


/-- `p₁ = 2⌈K^{3/2}/2⌉` (Definition 4.4). -/
noncomputable def levelP1 (K : ℝ) : ℕ := 2 * ⌈K ^ (3 / 2 : ℝ) / 2⌉₊

/-- `p₂ = 2⌈K/2⌉` (Definition 4.4). -/
noncomputable def levelP2 (K : ℝ) : ℕ := 2 * ⌈K / 2⌉₊

/-- `𝔏 = 3 C₀² ℓ₂(K², N)` (Definition 4.4). -/
noncomputable def levelFL (a C₀ K : ℝ) (N : ℕ) : ℝ := 3 * C₀ ^ 2 * lossL2 a (K ^ 2) N

/-- `E_max = 25 (K²)^a √(C₀ log N)` (Definition 4.4). -/
noncomputable def levelEmax (a C₀ K : ℝ) (N : ℕ) : ℝ := 25 * (K ^ 2) ^ a * Real.sqrt (C₀ * Real.log N)

/-! ### 1. Elementary facts on the levels -/

/-- `(K²)^t = K^{2t}` for `K ≥ 0`. -/
private lemma levels_rpow_sq {K : ℝ} (hK : 0 ≤ K) (t : ℝ) : (K ^ 2) ^ t = K ^ (2 * t) := by
  rw [Real.rpow_mul hK, Real.rpow_two]

/-- `𝔏 = 150 C₀² K^{4a+2} √(2⌈log₂ N⌉ + 2)`, written with `Q = K^{2a+1}`. -/
private lemma levels_FL_eq {a C₀ K : ℝ} (hK : 0 < K) (N : ℕ) :
    levelFL a C₀ K N =
      150 * C₀ ^ 2 * (K ^ (2 * a + 1)) ^ 2 * Real.sqrt (2 * (Nat.clog 2 N : ℝ) + 2) := by
  unfold levelFL lossL2 lossL
  rw [levels_rpow_sq hK.le, show 2 * (a + 1 / 2) = 2 * a + 1 by ring]
  ring

/-- `K^{4a+3} = (K^{2a+1})² K`. -/
private lemma levels_rpow_four {a K : ℝ} (hK : 0 < K) :
    K ^ (4 * a + 3) = (K ^ (2 * a + 1)) ^ 2 * K := by
  rw [show 4 * a + 3 = (2 * a + 1) * 2 + 1 by ring, Real.rpow_add hK, Real.rpow_mul hK.le,
    Real.rpow_two, Real.rpow_one]

/-- `K^{2a+1} = K^{2a} K`. -/
private lemma levels_rpow_succ {a K : ℝ} (hK : 0 < K) : K ^ (2 * a + 1) = K ^ (2 * a) * K := by
  rw [Real.rpow_add hK, Real.rpow_one]

/-- `⌈log₂ N⌉ ≤ 2 log N + 1` for `N ≥ 1`. -/
private lemma levels_clog_le {N : ℕ} (hN : 1 ≤ N) : (Nat.clog 2 N : ℝ) ≤ 2 * Real.log N + 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : 1 / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  set k : ℕ := ⌈Real.log N / Real.log 2⌉₊ with hk
  have h1 : Real.log N / Real.log 2 ≤ k := Nat.le_ceil _
  have h2 : (k : ℝ) < Real.log N / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : Real.log N ≤ k * Real.log 2 := by
    rw [div_le_iff₀ hl2] at h1
    exact h1
  have h4 : (N : ℝ) ≤ 2 ^ k := by
    calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNr).symm
      _ ≤ Real.exp (k * Real.log 2) := Real.exp_le_exp.2 h3
      _ = 2 ^ k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h5 : Nat.clog 2 N ≤ k := Nat.clog_le_of_le_pow (by exact_mod_cast h4)
  have h6 : Real.log N / Real.log 2 ≤ 2 * Real.log N := by
    rw [div_le_iff₀ hl2]
    nlinarith
  have h7 : (Nat.clog 2 N : ℝ) ≤ k := by exact_mod_cast h5
  linarith

/-- `K^{3/2} ≤ p₁ ≤ K^{3/2} + 2` for `K ≥ 0`. -/
private lemma levels_P1_bounds {K : ℝ} (hK : 0 ≤ K) :
    K ^ (3 / 2 : ℝ) ≤ (levelP1 K : ℝ) ∧ (levelP1 K : ℝ) ≤ K ^ (3 / 2 : ℝ) + 2 := by
  have hu : 0 ≤ K ^ (3 / 2 : ℝ) / 2 := by positivity
  have h1 := Nat.le_ceil (K ^ (3 / 2 : ℝ) / 2)
  have h2 := Nat.ceil_lt_add_one hu
  unfold levelP1
  push_cast
  constructor <;> linarith

/-- `K ≤ p₂ ≤ K + 2` for `K ≥ 0`. -/
private lemma levels_P2_bounds {K : ℝ} (hK : 0 ≤ K) :
    K ≤ (levelP2 K : ℝ) ∧ (levelP2 K : ℝ) ≤ K + 2 := by
  have hu : 0 ≤ K / 2 := by positivity
  have h1 := Nat.le_ceil (K / 2)
  have h2 := Nat.ceil_lt_add_one hu
  unfold levelP2
  push_cast
  constructor <;> linarith

/-- Consequences of `1681 ≤ L` and `L³ ≤ K`. -/
private lemma levels_K_facts {L K : ℝ} (hL : 1681 ≤ L) (hK : L ^ 3 ≤ K) :
    0 < L ∧ 1681 * L ≤ L ^ 2 ∧ L ^ 2 ≤ K ∧ 1 ≤ K ∧ L ≤ K := by
  have hLpos : 0 < L := by linarith
  have h1 : 1681 * L ≤ L ^ 2 := by nlinarith
  have h2 : 1681 * L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L]
  have h3 : 0 ≤ L ^ 2 := sq_nonneg L
  refine ⟨hLpos, h1, by linarith, by linarith, by linarith⟩

/-- (S2) for `𝔏`: `150 ≤ 𝔏 ≤ K^{4a+3}` when `log N ≥ 1681`, `log N ≥ 13 C₀` and
`K ≥ (log N)³`. -/
private lemma levels_FL_bounds {a C₀ K : ℝ} {N : ℕ} (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hN : 1 ≤ N)
    (hL : 1681 ≤ Real.log N) (hLC : 13 * C₀ ≤ Real.log N) (hK : Real.log N ^ 3 ≤ K) :
    150 ≤ levelFL a C₀ K N ∧ levelFL a C₀ K N ≤ K ^ (4 * a + 3) := by
  obtain ⟨hLpos, h1, h2, hK1, hLK⟩ := levels_K_facts hL hK
  have hKpos : 0 < K := by linarith
  have hQ : 1 ≤ K ^ (2 * a + 1) := Real.one_le_rpow hK1 (by linarith)
  have hs1 : 1 ≤ Real.sqrt (2 * (Nat.clog 2 N : ℝ) + 2) := by
    rw [Real.one_le_sqrt]
    have : (0 : ℝ) ≤ Nat.clog 2 N := Nat.cast_nonneg _
    linarith
  have hsL : Real.sqrt (2 * (Nat.clog 2 N : ℝ) + 2) ≤ Real.log N := by
    rw [Real.sqrt_le_left hLpos.le]
    have := levels_clog_le hN
    linarith
  have hFL := levels_FL_eq (a := a) (C₀ := C₀) hKpos N
  refine ⟨?_, ?_⟩
  · rw [hFL]
    have e1 : 1 ≤ C₀ ^ 2 := one_le_pow₀ hC₀
    have e2 : 1 ≤ (K ^ (2 * a + 1)) ^ 2 := one_le_pow₀ hQ
    calc (150 : ℝ) = 150 * 1 * 1 * 1 := by norm_num
      _ ≤ 150 * C₀ ^ 2 * (K ^ (2 * a + 1)) ^ 2 * Real.sqrt (2 * (Nat.clog 2 N : ℝ) + 2) := by
        gcongr
  · rw [hFL, levels_rpow_four hKpos]
    have e1 : (13 * C₀) ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ (by positivity) hLC 2
    have e2 : 150 * C₀ ^ 2 ≤ Real.log N ^ 2 := by nlinarith [sq_nonneg C₀]
    have e3 : 150 * C₀ ^ 2 * Real.log N ≤ Real.log N ^ 2 * Real.log N :=
      mul_le_mul_of_nonneg_right e2 hLpos.le
    have e4 : 150 * C₀ ^ 2 * Real.log N ≤ K := by
      have : Real.log N ^ 2 * Real.log N = Real.log N ^ 3 := by ring
      linarith
    calc 150 * C₀ ^ 2 * (K ^ (2 * a + 1)) ^ 2 * Real.sqrt (2 * (Nat.clog 2 N : ℝ) + 2)
        ≤ 150 * C₀ ^ 2 * (K ^ (2 * a + 1)) ^ 2 * Real.log N := by gcongr
      _ = (K ^ (2 * a + 1)) ^ 2 * (150 * C₀ ^ 2 * Real.log N) := by ring
      _ ≤ (K ^ (2 * a + 1)) ^ 2 * K := by gcongr

/-- (S2) for `E_max`: `1 ≤ E_max ≤ K^{2a+1}` when `log N ≥ 1681`, `log N ≥ C₀` and
`K ≥ (log N)³`. -/
private lemma levels_Emax_bounds {a C₀ K : ℝ} {N : ℕ} (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀)
    (hL : 1681 ≤ Real.log N) (hLC : C₀ ≤ Real.log N) (hK : Real.log N ^ 3 ≤ K) :
    1 ≤ levelEmax a C₀ K N ∧ levelEmax a C₀ K N ≤ K ^ (2 * a + 1) := by
  obtain ⟨hLpos, h1, h2, hK1, hLK⟩ := levels_K_facts hL hK
  have hKpos : 0 < K := by linarith
  have hR : 1 ≤ K ^ (2 * a) := Real.one_le_rpow hK1 (by linarith)
  have hEm : levelEmax a C₀ K N = 25 * K ^ (2 * a) * Real.sqrt (C₀ * Real.log N) := by
    unfold levelEmax
    rw [levels_rpow_sq hKpos.le]
  have hCL : 1 ≤ C₀ * Real.log N := by nlinarith
  have hsCL : Real.sqrt (C₀ * Real.log N) ≤ Real.log N := by
    rw [Real.sqrt_le_left hLpos.le]
    nlinarith
  have hs1 : 1 ≤ Real.sqrt (C₀ * Real.log N) := Real.one_le_sqrt.2 hCL
  refine ⟨?_, ?_⟩
  · rw [hEm]
    nlinarith
  · rw [hEm, levels_rpow_succ hKpos]
    have e1 : 25 * Real.log N ≤ K := by linarith
    have e2 : 0 ≤ K ^ (2 * a) := by linarith
    calc 25 * K ^ (2 * a) * Real.sqrt (C₀ * Real.log N) ≤ 25 * K ^ (2 * a) * Real.log N := by
          gcongr
      _ = K ^ (2 * a) * (25 * Real.log N) := by ring
      _ ≤ K ^ (2 * a) * K := by gcongr

/-- (S3): the level relations (4.14) and `K^{3/2} ≤ p₁ ≤ 2 K^{3/2}` when `log N ≥ 1681` and
`K ≥ (log N)³`. -/
private lemma levels_P_bounds {K L : ℝ} (hL : 1681 ≤ L) (hK : L ^ 3 ≤ K) :
    40 * (levelP1 K : ℝ) * L ≤ K ^ 2 ∧ 40 * (levelP2 K : ℝ) * L ≤ levelP1 K ∧
      K ≤ levelP2 K ∧ K ^ (3 / 2 : ℝ) ≤ levelP1 K ∧ (levelP1 K : ℝ) ≤ 2 * K ^ (3 / 2 : ℝ) := by
  obtain ⟨hLpos, h1, h2, hK1, hLK⟩ := levels_K_facts hL hK
  have hKpos : 0 < K := by linarith
  set s : ℝ := Real.sqrt K with hs
  have hs2 : s ^ 2 = K := Real.sq_sqrt hKpos.le
  have hs41 : 41 * L ≤ s := by
    rw [hs, Real.le_sqrt (by positivity) hKpos.le]
    nlinarith
  have hspos : 0 < s := by linarith
  have hu : K ^ (3 / 2 : ℝ) = s ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hKpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow, ← hs, ← hs2]
    ring
  have hs80 : 80 ≤ s := by linarith
  have hs3 : 80 ≤ s ^ 3 := le_trans hs80 (le_self_pow₀ (by linarith) (by norm_num))
  have hs2' : 80 ≤ s ^ 2 := le_trans hs80 (le_self_pow₀ (by linarith) (by norm_num))
  obtain ⟨hP1a0, hP1b0⟩ := levels_P1_bounds hKpos.le
  obtain ⟨hP2a, hP2b⟩ := levels_P2_bounds hKpos.le
  have hP1a : s ^ 3 ≤ (levelP1 K : ℝ) := by rw [← hu]; exact hP1a0
  have hP1b : (levelP1 K : ℝ) ≤ s ^ 3 + 2 := by rw [← hu]; exact hP1b0
  refine ⟨?_, ?_, hP2a, hP1a0, ?_⟩
  · have e1 : 41 * L * s ^ 3 ≤ s * s ^ 3 :=
      mul_le_mul_of_nonneg_right hs41 (by positivity)
    have e2 : L * 80 ≤ L * s ^ 3 := mul_le_mul_of_nonneg_left hs3 hLpos.le
    have e3 : K ^ 2 = s * s ^ 3 := by rw [← hs2]; ring
    have e4 : 40 * (levelP1 K : ℝ) * L ≤ 40 * (s ^ 3 + 2) * L := by gcongr
    linarith
  · have e1 : 41 * L * s ^ 2 ≤ s * s ^ 2 :=
      mul_le_mul_of_nonneg_right hs41 (by positivity)
    have e2 : L * 80 ≤ L * s ^ 2 := mul_le_mul_of_nonneg_left hs2' hLpos.le
    have e4 : 40 * (levelP2 K : ℝ) * L ≤ 40 * (s ^ 2 + 2) * L := by
      have : (levelP2 K : ℝ) ≤ s ^ 2 + 2 := by rw [hs2]; exact hP2b
      gcongr
    have e5 : s * s ^ 2 = s ^ 3 := by ring
    linarith
  · rw [hu]
    linarith

/-! ### 2. Lemma 4.6, (S1)–(S4) -/

/-- Lemma 4.6: the standing inequalities (S1)–(S4) (the probabilistic (S5) is Lemma 4.4 at
`κ = K²`). -/
theorem standing_ineq {ϑ C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) (K₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      (K₀ ≤ K ∧ 13 ≤ N ∧ C₀ ≤ (N : ℝ) ^ 2 ∧ kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ K ^ 2) ∧
      (150 ≤ levelFL ϑ⁻¹ C₀ K N ∧ levelFL ϑ⁻¹ C₀ K N ≤ K ^ (4 * ϑ⁻¹ + 3) ∧
        1 ≤ levelEmax ϑ⁻¹ C₀ K N ∧ levelEmax ϑ⁻¹ C₀ K N ≤ K ^ (2 * ϑ⁻¹ + 1)) ∧
      (40 * levelP1 K * Real.log N ≤ K ^ 2 ∧ 40 * levelP2 K * Real.log N ≤ levelP1 K ∧
        K ≤ levelP2 K ∧ K ^ (3 / 2 : ℝ) ≤ levelP1 K ∧ (levelP1 K : ℝ) ≤ 2 * K ^ (3 / 2 : ℝ)) ∧
      (K ^ (6 * ϑ⁻¹ + 6) ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        K₀ * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ)) := by
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  generalize ϑ⁻¹ = a at ha ⊢
  obtain ⟨-, hL2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc0⟩ := ledger_closes ha
  -- the threshold on `log N`, and the thresholds on `N`
  set L₀ : ℝ := max (max 1681 (13 * C₀)) (max K₀ (max |kappaTheta a| 4)) with hL₀
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      13 ≤ N ∧ L₀ ≤ Real.log N ∧ K₀ ≤ (N : ℝ) ^ (3 / 32 : ℝ) := by
    refine ⟨max 13 ⌈max (Real.exp L₀) ((max K₀ 0) ^ (32 / 3 : ℝ))⌉₊, fun N hN => ?_⟩
    have h13 : 13 ≤ N := le_trans (le_max_left _ _) hN
    have hNr : (0 : ℝ) < N := by
      have : (0 : ℕ) < N := by omega
      exact_mod_cast this
    have hN' : max (Real.exp L₀) ((max K₀ 0) ^ (32 / 3 : ℝ)) ≤ N :=
      Nat.ceil_le.1 (le_trans (le_max_right _ _) hN)
    refine ⟨h13, ?_, ?_⟩
    · exact (Real.le_log_iff_exp_le hNr).2 (le_trans (le_max_left _ _) hN')
    · have h1 : (max K₀ 0) ^ (32 / 3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN'
      have h2 : ((max K₀ 0) ^ (32 / 3 : ℝ)) ^ (3 / 32 : ℝ) ≤ (N : ℝ) ^ (3 / 32 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (le_max_right _ _) _) h1 (by norm_num)
      rw [← Real.rpow_mul (le_max_right _ _), show (32 / 3 : ℝ) * (3 / 32) = 1 by norm_num,
        Real.rpow_one] at h2
      exact le_trans (le_max_left _ _) h2
  refine ⟨N₀, fun N hN K hK1 hK2 => ?_⟩
  obtain ⟨hN13, hLL₀, hK₀N⟩ := hN₀ N hN
  have hN1' : 1 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1681 : 1681 ≤ Real.log N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL₀
  have hLC : 13 * C₀ ≤ Real.log N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL₀
  have hLK₀ : K₀ ≤ Real.log N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL₀
  have hLκ : |kappaTheta a| ≤ Real.log N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLL₀
  have hLC' : C₀ ≤ Real.log N := by linarith
  obtain ⟨hLpos, h1, h2, hK1le, hLK⟩ := levels_K_facts hL1681 hK1
  have hKpos : 0 < K := by linarith
  -- (S1)
  have hS1b : C₀ ≤ (N : ℝ) ^ 2 := by
    have e1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos hNpos
    nlinarith
  have hS1c : kappaTheta a + 3 * Real.log N ≤ K ^ 2 := by
    have e1 : kappaTheta a ≤ Real.log N := le_trans (le_abs_self _) hLκ
    have e2 : K ≤ K ^ 2 := by nlinarith
    linarith
  -- (S2), (S3), (S4)
  obtain ⟨hS2a, hS2b⟩ := levels_FL_bounds ha hC₀ hN1' hL1681 hLC hK1
  obtain ⟨hS2c, hS2d⟩ := levels_Emax_bounds ha hC₀ hL1681 hLC' hK1
  have hS4a : K ^ (6 * a + 6) ≤ (N : ℝ) ^ (1 / 32 : ℝ) := by
    calc K ^ (6 * a + 6) ≤ ((N : ℝ) ^ ledgerc0 a) ^ (6 * a + 6) :=
          Real.rpow_le_rpow hKpos.le hK2 (by linarith)
      _ = (N : ℝ) ^ (ledgerc0 a * (6 * a + 6)) := (Real.rpow_mul hN0 _ _).symm
      _ ≤ (N : ℝ) ^ (1 / 32 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hL2
  have hS4b : K₀ * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
    rw [show (1 / 8 : ℝ) = 3 / 32 + 1 / 32 by norm_num, Real.rpow_add hNpos]
    exact mul_le_mul_of_nonneg_right hK₀N (Real.rpow_nonneg hN0 _)
  exact ⟨⟨le_trans hLK₀ hLK, hN13, hS1b, hS1c⟩, ⟨hS2a, hS2b, hS2c, hS2d⟩,
    levels_P_bounds hL1681 hK1, hS4a, hS4b⟩

/-! ### 3. Convention 1.2 -/

/-- Convention 1.2: `N^C e^{-K} ≤ e^{-K/2}` whenever `K ≥ (log N)³` and `(log N)² ≥ 2C`, because
then `C log N ≤ ½ (log N)³ ≤ K/2`; here `N ≥ 1`. -/
theorem exp_le_of_level {N C K : ℝ} (hN : 1 ≤ N) (hK : Real.log N ^ 3 ≤ K)
    (hC : 2 * C ≤ Real.log N ^ 2) : N ^ C * Real.exp (-K) ≤ Real.exp (-K / 2) := by
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN
  have h1 : 2 * C * Real.log N ≤ Real.log N ^ 2 * Real.log N :=
    mul_le_mul_of_nonneg_right hC hL
  have h2 : Real.log N * C ≤ K / 2 := by
    have : Real.log N ^ 2 * Real.log N = Real.log N ^ 3 := by ring
    linarith
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-! ### 4. Lemma 4.6 (S5) -/

/-- Lemma 4.6 (S5): the good event `𝒢(z) = 𝒢_{K²}(z)` of Definition 4.3 at `κ = K²` is closed, has
`ℙ(𝒢(z)ᶜ) ≤ 46 ϑ⁻¹ N⁴ e^{-K²}` and, on it, `|X_i| ≤ 𝔏 Ψ_m`, `|A_i| ≤ 𝔏 |G_ii| Ψ_m²` and
`|G_ij| ≤ 𝔏 |G_ii| |G^{(i)}_jj| Ψ_m` for `i ≠ j`, with `𝔏 = 3 C₀² ℓ₂(K², N)`.  If moreover
`46/ϑ ≤ N`, `(log N)² ≥ 10` and `K ≥ (log N)³`, then `ℙ(𝒢(z)ᶜ) ≤ e^{-K}`. -/
theorem goodEvent_level {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) (hN : 13 ≤ N)
    {z : ℂ} (hz : 0 < z.im) {K : ℝ} (hK : kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ K ^ 2) :
    IsClosed (goodEvent M ϑ⁻¹ (K ^ 2) z) ∧
      M.prodLaw (goodEvent M ϑ⁻¹ (K ^ 2) z)ᶜ ≤
        ENNReal.ofReal (46 / ϑ * N ^ 4 * Real.exp (-K ^ 2)) ∧
      (∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z, ∀ i j, i ≠ j →
        ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ∧
        ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
          levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 ∧
        ‖green (toMatrix x) z i j‖ ≤ levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ *
          ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z) ∧
      (46 / ϑ ≤ N → 10 ≤ Real.log N ^ 2 → Real.log N ^ 3 ≤ K →
        M.prodLaw (goodEvent M ϑ⁻¹ (K ^ 2) z)ᶜ ≤ ENNReal.ofReal (Real.exp (-K))) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hκ : kappaTheta ϑ⁻¹ + Real.log N ≤ K ^ 2 := by linarith
  obtain ⟨hcl, hpr, hcons⟩ := goodEvent_spec M hM hϑ hϑ1 hC₀ (by omega : 3 ≤ N) hz hκ
  refine ⟨hcl, hpr, ?_, ?_⟩
  · intro x hx i j hij
    obtain ⟨h1, h2, h3⟩ := hcons x hx i j hij
    set ℓ := lossL ϑ⁻¹ (K ^ 2) with hℓ
    set ℓ₂ := lossL2 ϑ⁻¹ (K ^ 2) N with hℓ₂
    have hℓ₂0 : 0 ≤ ℓ₂ := by rw [hℓ₂]; unfold lossL2; positivity
    have hℓsq : ℓ ^ 2 ≤ ℓ₂ / 2 := by
      have e1 := lossL_sq_le_lossL2 ϑ⁻¹ (K ^ 2) N
      have e2 : (2 * Real.sqrt 2)⁻¹ ≤ 2⁻¹ := by
        have : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
        apply inv_anti₀ (by norm_num)
        linarith
      calc ℓ ^ 2 ≤ (2 * Real.sqrt 2)⁻¹ * ℓ₂ := e1
        _ ≤ 2⁻¹ * ℓ₂ := mul_le_mul_of_nonneg_right e2 hℓ₂0
        _ = ℓ₂ / 2 := by ring
    have hFL : levelFL ϑ⁻¹ C₀ K N = 3 * C₀ ^ 2 * ℓ₂ := rfl
    have hΨ : 0 ≤ ctrlPsiM x z := by unfold ctrlPsiM; positivity
    have hC0 : 0 < C₀ := by linarith
    have hCC : C₀ ≤ C₀ ^ 2 := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · refine h1.trans ?_
      rw [hFL]
      have : 2 * C₀ * ℓ₂ ≤ 3 * C₀ ^ 2 * ℓ₂ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hΨ
    · refine h2.trans ?_
      rw [hFL]
      have e1 : 2 * C₀ ^ 2 * ℓ ^ 2 ≤ 3 * C₀ ^ 2 * ℓ₂ := by nlinarith [sq_nonneg C₀]
      have e2 : 0 ≤ ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 := by positivity
      calc 2 * C₀ ^ 2 * ℓ ^ 2 * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2
          = (2 * C₀ ^ 2 * ℓ ^ 2) * (‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2) := by ring
        _ ≤ (3 * C₀ ^ 2 * ℓ₂) * (‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2) :=
          mul_le_mul_of_nonneg_right e1 e2
        _ = 3 * C₀ ^ 2 * ℓ₂ * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 := by ring
    · refine h3.trans ?_
      rw [hFL]
      have e1 : 3 * C₀ * ℓ ^ 2 ≤ 3 * C₀ ^ 2 * ℓ₂ := by nlinarith [mul_nonneg hC0.le hℓ₂0]
      have e2 : 0 ≤ ‖green (toMatrix x) z i i‖ * ‖greenT (toMatrix x) {i} z j j‖ *
          ctrlPsiM x z := by positivity
      calc 3 * C₀ * ℓ ^ 2 * ‖green (toMatrix x) z i i‖ * ‖greenT (toMatrix x) {i} z j j‖ *
            ctrlPsiM x z
          = (3 * C₀ * ℓ ^ 2) * (‖green (toMatrix x) z i i‖ *
            ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z) := by ring
        _ ≤ (3 * C₀ ^ 2 * ℓ₂) * (‖green (toMatrix x) z i i‖ *
            ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z) :=
          mul_le_mul_of_nonneg_right e1 e2
        _ = 3 * C₀ ^ 2 * ℓ₂ * ‖green (toMatrix x) z i i‖ * ‖greenT (toMatrix x) {i} z j j‖ *
            ctrlPsiM x z := by ring
  · intro h46 h10 hKl
    refine hpr.trans (ENNReal.ofReal_le_ofReal ?_)
    have hK1 : 1 ≤ K := by
      have : 3 ≤ Real.log N := by nlinarith
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) this 3]
    have hK2 : 2 ≤ K := by
      have : 3 ≤ Real.log N := by nlinarith
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) this 3]
    have hKK : Real.log N ^ 3 ≤ K ^ 2 := by nlinarith
    have h5 := exp_le_of_level (N := (N : ℝ)) (C := 5) (K := K ^ 2) hN1 hKK (by linarith)
    have hN5 : (N : ℝ) ^ (5 : ℝ) = (N : ℝ) ^ 5 := Real.rpow_ofNat _ 5
    rw [hN5] at h5
    have h4 : 46 / ϑ * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 5 := by
      have : 0 ≤ (N : ℝ) ^ 4 := by positivity
      calc 46 / ϑ * (N : ℝ) ^ 4 ≤ N * (N : ℝ) ^ 4 := mul_le_mul_of_nonneg_right h46 this
        _ = (N : ℝ) ^ 5 := by ring
    have h6 : Real.exp (-K ^ 2 / 2) ≤ Real.exp (-K) := Real.exp_le_exp.2 (by nlinarith)
    calc 46 / ϑ * (N : ℝ) ^ 4 * Real.exp (-K ^ 2) ≤ (N : ℝ) ^ 5 * Real.exp (-K ^ 2) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ ≤ Real.exp (-K ^ 2 / 2) := h5
      _ ≤ Real.exp (-K) := h6

end Rigidity
