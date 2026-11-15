import Rigidity.LocalLaw.Defs
import Rigidity.LocalLaw.Ledger
import Rigidity.Semicircle.Density
import Rigidity.Spectrum.Eigenvalues

/-!
# The level form and the reduction (NP v1.1, §2: (2.27), Theorem 2.6 (i)–(v), Proposition 2.7)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The domain `D_K = {|E| ≤ 5, K^{C₁} N⁻¹ ≤ η ≤ 10}` of Theorem 2.6. -/
def DK (a : ℝ) (N : ℕ) (K : ℝ) : Set ℂ :=
  {z | |z.re| ≤ 5 ∧ K ^ ledgerC1 a / N ≤ z.im ∧ z.im ≤ 10}

/-- Conclusions (i)–(v) of Theorem 2.6 at the point `x` and level `K` (`a = 1/ϑ`). -/
def LevelGood {N : ℕ} (a K : ℝ) (x : Pair N → 𝕜) : Prop :=
  (∀ z ∈ DK a N K, Lam x z ≤ K ^ ledgerC2 a / (N * z.im)) ∧
  (∀ z ∈ DK a N K, LamD x z + LamO x z ≤
      K ^ ledgerC2 a * (Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im))) ∧
  (∀ k, |eig x k| ≤ 2 + K ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ))) ∧
  (∀ E : ℝ, |countFn x E - nsc E| ≤ K ^ ledgerC5 a / N) ∧
  (∀ k, |eig x k - gamma N k| ≤
      K ^ ledgerC4 a * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)))

/-- Comparison of the `C`-th power of the level `K = (log N)^{φL}` with a power of `log N`:
if `φ C ≤ s` then `K ^ C ≤ (log N)^{sL}` (Proposition 2.7, Step 2). -/
private lemma reduction_pow_le {lg φ C s L : ℝ} (hlg : 1 ≤ lg) (hL : 0 ≤ L) (h : φ * C ≤ s) :
    (lg ^ (φ * L)) ^ C ≤ lg ^ (s * L) := by
  rw [← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hlg ?_
  calc φ * L * C = (φ * C) * L := by ring
    _ ≤ s * L := mul_le_mul_of_nonneg_right h hL

/-- Strict form of `reduction_pow_le`: if `φ C < s` and `L > 0` then `K ^ C < (log N)^{sL}`. -/
private lemma reduction_pow_lt {lg φ C s L : ℝ} (hlg : 1 < lg) (hL : 0 < L) (h : φ * C < s) :
    (lg ^ (φ * L)) ^ C < lg ^ (s * L) := by
  rw [← Real.rpow_mul (by linarith)]
  refine Real.rpow_lt_rpow_of_exponent_lt hlg ?_
  calc φ * L * C = (φ * C) * L := by ring
    _ < s * L := mul_lt_mul_of_pos_right h hL

/-- For `N ≥ 16`, `log N > e`, so `log N > 1` and `log log N > 1`. -/
private lemma reduction_exp_one_lt_log {N : ℕ} (hN : 16 ≤ N) : Real.exp 1 < Real.log N := by
  have h16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) h16
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.log_two_gt_d9
  linarith

/-- Proposition 2.7, Steps 1–2: `K = (log N)^{φL}` lies in the range of Theorem 2.6,
`S_L ⊆ D_K`, and the powers of `K` are below the powers of `log N` in (2.19)–(2.26). -/
theorem reduction_level {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hN : 16 ≤ N) {L : ℝ}
    (hL : LRange (ledgerA0 a) N L) :
    Real.log N ^ 3 ≤ Real.log N ^ (ledgerPhi a * L) ∧
    Real.log N ^ (ledgerPhi a * L) ≤ (N : ℝ) ^ ledgerc0 a ∧
    SL N L ⊆ DK a N (Real.log N ^ (ledgerPhi a * L)) ∧
    (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC2 a < Real.log N ^ (4 * L) ∧
    (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC3 a < Real.log N ^ (9 * L) ∧
    (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC4 a < Real.log N ^ L ∧
    (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC5 a < Real.log N ^ L := by
  obtain ⟨hφ1, hφ2, hφ3, hφ4, hφ5, hφc0, hφpos, -, hA⟩ := ledgerPhi_mul ha
  obtain ⟨-, hA0⟩ := ledgerPhi_eq ha
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc0⟩ := ledger_closes ha
  have hφA : ledgerPhi a * ledgerA0 a = 3 := by
    rw [hA0]
    field_simp
  have hexp := reduction_exp_one_lt_log hN
  have hlg1 : 1 < Real.log N := lt_trans (Real.one_lt_exp_iff.2 one_pos) hexp
  have hℓ1 : 1 < Real.log (Real.log N) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact hexp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLpos : 0 < L :=
    lt_of_lt_of_le (mul_pos (by linarith) (by linarith)) hL.1
  have hφL : 3 ≤ ledgerPhi a * L :=
    calc (3 : ℝ) ≤ 3 * Real.log (Real.log N) := by linarith
      _ = ledgerPhi a * (ledgerA0 a * Real.log (Real.log N)) := by rw [← mul_assoc, hφA]
      _ ≤ ledgerPhi a * L := mul_le_mul_of_nonneg_left hL.1 hφpos.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h3 : Real.log N ^ (3 : ℝ) = Real.log N ^ 3 := by
      exact_mod_cast Real.rpow_natCast (Real.log N) 3
    rw [← h3]
    exact Real.rpow_le_rpow_of_exponent_le hlg1.le hφL
  · have hL2 : L * (10 * Real.log (Real.log N)) ≤ Real.log (10 * N) :=
      (le_div_iff₀ (by linarith)).1 hL.2
    have h10 : Real.log (10 * N) = Real.log 10 + Real.log N :=
      Real.log_mul (by norm_num) hNpos.ne'
    have h10N : Real.log 10 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 10 ≤ N))
    have hLl : L * Real.log (Real.log N) ≤ Real.log N / 5 := by linarith
    rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hNpos]
    refine Real.exp_le_exp.2 ?_
    calc Real.log (Real.log N) * (ledgerPhi a * L)
        = ledgerPhi a * (L * Real.log (Real.log N)) := by ring
      _ ≤ (5 * ledgerc0 a) * (L * Real.log (Real.log N)) :=
          mul_le_mul_of_nonneg_right hφc0 (by positivity)
      _ ≤ (5 * ledgerc0 a) * (Real.log N / 5) :=
          mul_le_mul_of_nonneg_left hLl (by linarith)
      _ = Real.log N * ledgerc0 a := by ring
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    refine ⟨h1, ?_, h3⟩
    have hK : (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC1 a ≤ Real.log N ^ (10 * L) :=
      reduction_pow_le hlg1.le hLpos.le (by linarith)
    calc (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC1 a / N
        = (N : ℝ)⁻¹ * (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC1 a := by
          rw [div_eq_inv_mul]
      _ ≤ (N : ℝ)⁻¹ * Real.log N ^ (10 * L) :=
          mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hNpos.le)
      _ ≤ z.im := h2.le
  · exact reduction_pow_lt hlg1 hLpos (by linarith)
  · exact reduction_pow_lt hlg1 hLpos (by linarith)
  · have := reduction_pow_lt (φ := ledgerPhi a) (C := ledgerC4 a) (s := 1) hlg1 hLpos (by linarith)
    rwa [one_mul] at this
  · have := reduction_pow_lt (φ := ledgerPhi a) (C := ledgerC5 a) (s := 1) hlg1 hLpos (by linarith)
    rwa [one_mul] at this

/-- The complements of the five events of (2.19), (2.21), (2.22), (2.25), (2.26) at `x`. -/
def MainGood {N : ℕ} (L : ℝ) (x : Pair N → 𝕜) : Prop :=
  (∀ z ∈ SL N L, Lam x z < Real.log N ^ (4 * L) / (N * z.im)) ∧
  (∀ z ∈ SL N L, LamD x z + LamO x z < Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
      Real.log N ^ (4 * L) / (N * z.im)) ∧
  (∀ k, |eig x k| < 2 + (N : ℝ) ^ (-(2 / 3 : ℝ)) * Real.log N ^ (9 * L)) ∧
  (∀ k, |eig x k - gamma N k| <
      Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ∧
  (⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|) < Real.log N ^ L / N

/-- Proposition 2.7, Step 3 (deterministic): at `K = (log N)^{φL}`, the conclusions of
Theorem 2.6 exclude the five events. -/
theorem LevelGood.mainGood {a : ℝ} (ha : 1 ≤ a) {N : ℕ} (hN : 16 ≤ N) {L : ℝ}
    (hL : LRange (ledgerA0 a) N L) {x : Pair N → 𝕜}
    (hx : LevelGood a (Real.log N ^ (ledgerPhi a * L)) x) : MainGood L x := by
  obtain ⟨-, -, hDK, h4, h5, h6, h7⟩ := reduction_level ha hN hL
  have hexp := reduction_exp_one_lt_log hN
  have hlg1 : 1 < Real.log N := lt_trans (Real.one_lt_exp_iff.2 one_pos) hexp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpos : ∀ z ∈ SL N L, 0 < (N : ℝ) * z.im := by
    intro z hz
    have h1 : 0 < (N : ℝ)⁻¹ * Real.log N ^ (10 * L) :=
      mul_pos (inv_pos.2 hNpos) (Real.rpow_pos_of_pos (by linarith) _)
    exact mul_pos hNpos (lt_trans h1 hz.2.1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzD := hDK hz
    calc Lam x z ≤ (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC2 a / (N * z.im) := hx.1 z hzD
      _ < Real.log N ^ (4 * L) / (N * z.im) := by gcongr; exact hpos z hz
  · intro z hz
    have hzD := hDK hz
    have hs : 0 ≤ Real.sqrt ((msc z).im / (N * z.im)) := Real.sqrt_nonneg _
    have ht : 0 < 1 / ((N : ℝ) * z.im) := one_div_pos.2 (hpos z hz)
    calc LamD x z + LamO x z
        ≤ (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC2 a *
          (Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im)) := hx.2.1 z hzD
      _ = (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC2 a * Real.sqrt ((msc z).im / (N * z.im)) +
          (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC2 a * (1 / (N * z.im)) := mul_add _ _ _
      _ < Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
          Real.log N ^ (4 * L) * (1 / (N * z.im)) :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right h4.le hs)
          (mul_lt_mul_of_pos_right h4 ht)
      _ = Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
          Real.log N ^ (4 * L) / (N * z.im) := by rw [mul_one_div]
  · intro k
    have hN23 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
    calc |eig x k|
        ≤ 2 + (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC3 a * (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
          hx.2.2.1 k
      _ < 2 + Real.log N ^ (9 * L) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
          gcongr
      _ = 2 + (N : ℝ) ^ (-(2 / 3 : ℝ)) * Real.log N ^ (9 * L) := by rw [mul_comm]
  · intro k
    have hN23 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
    have hw : 0 < (rigWeight N k : ℝ) := by
      have hk := k.isLt
      have : 0 < rigWeight N k := by unfold rigWeight; omega
      exact_mod_cast this
    have hw3 : 0 < (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hw _
    calc |eig x k - gamma N k|
        ≤ (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC4 a * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(2 / 3 : ℝ)) := hx.2.2.2.2 k
      _ < Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
          gcongr
  · have : Nonempty (Set.Icc (-5 : ℝ) 5) := ⟨⟨0, by norm_num, by norm_num⟩⟩
    calc (⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|)
        ≤ (Real.log N ^ (ledgerPhi a * L)) ^ ledgerC5 a / N :=
          ciSup_le fun E => hx.2.2.2.1 E
      _ < Real.log N ^ L / N := by gcongr

end Rigidity
