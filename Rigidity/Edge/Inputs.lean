import Rigidity.Edge.Continuity
import Rigidity.Edge.GoodSet
import Rigidity.Edge.Hybrid
import Rigidity.Edge.Params
import Rigidity.Ensemble.Basic
import Rigidity.LocalLaw.Defs
import Rigidity.Resolvent.Basic
import Rigidity.Semicircle.Basic
import Rigidity.Semicircle.Density
import Rigidity.Spectrum.Eigenvalues

/-!
# The inputs (BB1), (BB2) and the semicircle law near the edge

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

`localLawEvent N L` is the event `U_L` of (BB1), the union over `z ∈ S_L` of the events
`Λ_d + Λ_o ≥ (log N)^{4L} √(Im m_sc / (N η)) + (log N)^{4L} / (N η)`, and `rigidityEvent N L` is
the event of (BB2).  The structure `EdgeInputs` states (BB1) and (BB2) at `L = L₀` with the bound
`N^{-20}` of (N3), for every ensemble of the class of Theorem 2.1 at size `N`; it is a hypothesis of
the edge argument.  The unions are not assumed to be measurable: a measure of an arbitrary set is
its outer measure, which is how (BB1) is used.

Lemma 11.5 (a) is the identity `(m_sc + 1)² = (2 - z) m_sc` for `Im z > 0` together with the
bounds `|m_sc + 1| ≤ |z - 2|^{1/2}` and `Im m_sc ≤ |z - 2|^{1/2}`; Lemma 11.5 (b) specialises these
to `z = y + i η` with `|y - 2| ≤ N^{-2/3+ε_g}` and `η = N^{-2/3-ε_g}`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The event of (BB1) at level `L`: the event of (2.21). -/
def localLawEvent (N : ℕ) (L : ℝ) : Set (Pair N → 𝕜) :=
  ⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
    Real.log N ^ (4 * L) / (N * z.im) ≤ LamD x z + LamO x z}

/-- The event of (BB2) at level `L`: the event of (2.25). -/
def rigidityEvent (N : ℕ) (L : ℝ) : Set (Pair N → 𝕜) :=
  {x | ∃ k : Fin N, Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) *
    (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |eig x k - gamma N k|}

/-- (BB1), (BB2) at `L = L₀`, with the bound `N^{-20}` of (N3), for every ensemble of the
class at size `N`. -/
structure EdgeInputs (𝕜 : Type*) [RCLike 𝕜] (ϑ δm δp C₀ A₀ : ℝ) (N : ℕ) : Prop where
  localLaw : ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    M.prodLaw (localLawEvent N (edgeL0 A₀ N)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ))
  rigidity : ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    M.prodLaw (rigidityEvent N (edgeL0 A₀ N)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ))

theorem EdgeLarge.lRange {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (h : EdgeLarge ϑ C₀ A₀ εg N) :
    LRange A₀ N (edgeL0 A₀ N) :=
  ⟨le_refl _, h.L0_le⟩

/-- Lemma 11.5 (a): `(m_sc + 1)² = (2 - z) m_sc`. -/
theorem msc_add_one_sq {z : ℂ} (hz : 0 < z.im) : (msc z + 1) ^ 2 = (2 - z) * msc z := by
  linear_combination msc_sq_add hz

/-- Lemma 11.5 (a), bounds. -/
theorem norm_msc_add_one_le {z : ℂ} (hz : 0 < z.im) :
    ‖msc z + 1‖ ≤ Real.sqrt ‖z - 2‖ ∧ (msc z).im ≤ Real.sqrt ‖z - 2‖ := by
  have h1 : ‖msc z + 1‖ ≤ Real.sqrt ‖z - 2‖ := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have h2 : ‖msc z + 1‖ ^ 2 = ‖z - 2‖ * ‖msc z‖ := by
      rw [← norm_pow, msc_add_one_sq hz, norm_mul, norm_sub_rev]
    rw [h2]
    have h3 := norm_msc_lt_one hz
    nlinarith [norm_nonneg (z - 2), norm_nonneg (msc z)]
  refine ⟨h1, le_trans ?_ h1⟩
  calc (msc z).im = (msc z + 1).im := by simp
    _ ≤ |(msc z + 1).im| := le_abs_self _
    _ ≤ ‖msc z + 1‖ := Complex.abs_im_le_norm _

/-- Lemma 11.5 (b). -/
theorem msc_edge_le {N : ℕ} (hN : 1 ≤ N) {εg y : ℝ} (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hy : |y - 2| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εg)) :
    ‖(⟨y, edgeEta εg N⟩ : ℂ) - 2‖ ≤ 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) + εg) ∧
      ‖msc ⟨y, edgeEta εg N⟩ + 1‖ ≤ Real.sqrt 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) ∧
      (msc ⟨y, edgeEta εg N⟩).im ≤ Real.sqrt 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) := by
  have _ := hεg'
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (by exact_mod_cast hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη : 0 < edgeEta εg N := Real.rpow_pos_of_pos hNpos _
  have hηle : edgeEta εg N ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εg) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hz : 0 < (⟨y, edgeEta εg N⟩ : ℂ).im := hη
  have hy' := abs_le.1 hy
  have hnorm : ‖(⟨y, edgeEta εg N⟩ : ℂ) - 2‖ ≤ 2 * (N : ℝ) ^ (-(2 / 3 : ℝ) + εg) := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    have hre : ((⟨y, edgeEta εg N⟩ : ℂ) - 2).re = y - 2 := by simp
    have him : ((⟨y, edgeEta εg N⟩ : ℂ) - 2).im = edgeEta εg N := by simp
    rw [hre, him, abs_of_pos hη]
    linarith
  have hsq : Real.sqrt ‖(⟨y, edgeEta εg N⟩ : ℂ) - 2‖ ≤
      Real.sqrt 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) := by
    refine le_trans (Real.sqrt_le_sqrt hnorm) ?_
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow ((N : ℝ) ^ (-(2 / 3 : ℝ) + εg)),
      ← Real.rpow_mul hNpos.le]
    refine le_of_eq ?_
    congr 2
    ring
  obtain ⟨h1, h2⟩ := norm_msc_add_one_le hz
  exact ⟨hnorm, h1.trans hsq, h2.trans hsq⟩

end Rigidity
