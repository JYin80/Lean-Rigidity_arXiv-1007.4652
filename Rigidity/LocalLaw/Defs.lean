import Rigidity.Ensemble.Basic
import Rigidity.Resolvent.Basic
import Rigidity.Resolvent.Spectral
import Rigidity.Semicircle.Basic
import Rigidity.Semicircle.Density
import Rigidity.Spectrum.Eigenvalues

/-!
# The counting function and the control quantities of the local law

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].  The equation
numbers inside the docstrings of the definitions below are the [EYY] numbers; the same objects
carry the numbers (2.6) (the quantities `Λ`, `Λ_d`, `Λ_o`), (2.7) (the spectral domain `S_L`) and
(2.8) (the range of `L`) in NP v1.1, and the counting function `𝔫` is the display after (2.5).

This file defines the normalised counting function `𝔫(E) = N⁻¹ #{j : λ_j ≤ E}` of the ordered
eigenvalues, the three control quantities
`Λ = |m - m_sc|`, `Λ_d = max_k |G_kk - m_sc|`, `Λ_o = max_{k ≠ l} |G_kl|`, the spectral domain
`S_L`, and the range of the exponent `L` (NP (2.8)).  It proves:

* `exists_LRange_nonempty` (NP Remark 2.3): for `N` large in terms of `A₀`, the range of `L`
  is nonempty, and `S_L` is nonempty for every `L` below the upper endpoint
  `log (10 N) / (10 log log N)`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The normalised counting function `𝔫(E)` (2.23). -/
noncomputable def countFn {N : ℕ} (x : Pair N → 𝕜) (E : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ((Finset.univ.filter fun k => eig x k ≤ E).card : ℝ)

/-- `Λ = |m - m_sc|` (2.16). -/
noncomputable def Lam {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  ‖stieltjesEmp (toMatrix x) z - msc z‖

/-- `Λ_d = max_k |G_kk - m_sc|` (2.16). -/
noncomputable def LamD {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  ⨆ k : Fin N, ‖green (toMatrix x) z k k - msc z‖

/-- `Λ_o = max_{k ≠ l} |G_kl|` (2.16). -/
noncomputable def LamO {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  ⨆ q : {q : Fin N × Fin N // q.1 ≠ q.2}, ‖green (toMatrix x) z q.1.1 q.1.2‖

/-- The spectral domain `S_L` (2.20). -/
def SL (N : ℕ) (L : ℝ) : Set ℂ :=
  {z | |z.re| ≤ 5 ∧ (N : ℝ)⁻¹ * Real.log N ^ (10 * L) < z.im ∧ z.im ≤ 10}

/-- The range (2.18) of `L`. -/
def LRange (A₀ : ℝ) (N : ℕ) (L : ℝ) : Prop :=
  A₀ * Real.log (Real.log N) ≤ L ∧ L ≤ Real.log (10 * N) / (10 * Real.log (Real.log N))

/-- For `A₀` fixed, eventually in `N`: `log N > 1` and `10 (|A₀| + 1) (log log N)² ≤ log N`. -/
private lemma eventually_loglog_le (A₀ : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      1 < Real.log N ∧ 10 * (|A₀| + 1) * Real.log (Real.log N) ^ 2 ≤ Real.log N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Filter.Eventually.and (hlog.eventually (eventually_gt_atTop 1)) ?_
  have hc : (0 : ℝ) < (10 * (|A₀| + 1))⁻¹ := by positivity
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).def hc
  have h' : ∀ᶠ t : ℝ in atTop, 10 * (|A₀| + 1) * Real.log t ^ 2 ≤ t := by
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have ht0 : (0 : ℝ) ≤ t := by linarith
    simp only [Real.norm_eq_abs, id, abs_of_nonneg ht0,
      abs_of_nonneg (sq_nonneg (Real.log t))] at ht
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity : (0 : ℝ) < 10 * (|A₀| + 1))] at ht
    linarith
  exact hlog.eventually h'

theorem exists_LRange_nonempty (A₀ : ℝ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (∃ L, LRange A₀ N L) ∧
        ∀ L : ℝ, L < Real.log (10 * N) / (10 * Real.log (Real.log N)) → (SL N L).Nonempty := by
  obtain ⟨N₁, hN₁⟩ := (eventually_loglog_le A₀).exists_forall_of_atTop
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := hN₁ N hN
  have hNpos : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg N)
    rw [this, Real.log_zero] at h1
    linarith
  have hℓ : 0 < Real.log (Real.log N) := Real.log_pos h1
  have h10 : Real.log N ≤ Real.log (10 * N) :=
    Real.log_le_log hNpos (by linarith)
  refine ⟨⟨A₀ * Real.log (Real.log N), le_rfl, ?_⟩, fun L hL => ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have : A₀ * Real.log (Real.log N) * (10 * Real.log (Real.log N)) ≤
        10 * (|A₀| + 1) * Real.log (Real.log N) ^ 2 := by
      have := le_abs_self A₀
      nlinarith [sq_nonneg (Real.log (Real.log N))]
    linarith
  · refine ⟨10 * Complex.I, ?_, ?_, ?_⟩ <;> simp only [Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat] <;> norm_num
    rw [lt_div_iff₀ (by positivity)] at hL
    rw [inv_mul_lt_iff₀ hNpos, Real.rpow_def_of_pos (by linarith)]
    calc Real.exp (Real.log (Real.log N) * (10 * L))
        = Real.exp (10 * L * Real.log (Real.log N)) := by ring_nf
      _ < Real.exp (Real.log (10 * N)) := Real.exp_lt_exp.mpr (by linarith)
      _ = 10 * N := Real.exp_log (by positivity)
      _ = N * 10 := by ring

end Rigidity
