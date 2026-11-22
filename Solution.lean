module

public import Rigidity

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `Rigidity` named in its proof. The
definitions that occur in the statements are those of `Rigidity/MainDefs.lean`.
-/

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.1 (i), (2.19). -/
theorem thm2_1_avg :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) / (N * z.im) ≤ Lam x z}) ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) :=
  strongLocalLaw_avg

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.1 (ii), (2.21). -/
theorem thm2_1_entries :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
          Real.log N ^ (4 * L) / (N * z.im) ≤ LamD x z + LamO x z}) ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) :=
  strongLocalLaw_entries

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.1 (iii), (2.22). -/
theorem thm2_1_extreme :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | ∃ k : Fin N,
          2 + (N : ℝ) ^ (-(2 / 3 : ℝ)) * Real.log N ^ (9 * L) ≤ |eig x k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) :=
  extremeEigenvalues_le

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.2, (2.25). -/
theorem thm2_2_rigidity :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | ∃ k : Fin N, Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |eig x k - gamma N k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) :=
  rigidity

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.2, (2.26), with the supremum itself. -/
theorem thm2_2_counting :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | Real.log N ^ L / N ≤ ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) :=
  countingFunction_close

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
open scoped NNReal
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.3, (2.36) (strong local ergodicity of Dyson Brownian motion). -/
theorem thm2_3_localErgodicity :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO →
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, max n 3 ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + K) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ) ^ (-1 + ε') + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2)) :=
  dbm_localErgodicity

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.4, (2.41). -/
theorem thm2_4_max :
    ∀ ϑ : ℝ, 0 < ϑ → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ δm δp C₀ : ℝ, 0 < δm → 0 < δp → 0 < C₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Mv Mw : Ensemble 𝕜 N,
      Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ → Ensemble.MomentMatch2 Mv Mw →
      ∀ s : ℝ,
        Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-ε)} ≤
            Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) ∧
          Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} ≤
            Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s + (N : ℝ) ^ (-ε)} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) :=
  edgeUniversality_max

end Rigidity

end

section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace Rigidity
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.4, the smallest eigenvalue. -/
theorem thm2_4_min :
    ∀ ϑ : ℝ, 0 < ϑ → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ δm δp C₀ : ℝ, 0 < δm → 0 < δp → 0 < C₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Mv Mw : Ensemble 𝕜 N,
      Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ → Ensemble.MomentMatch2 Mv Mw →
      ∀ s : ℝ,
        Mv.prodLaw {x | s + (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} ≤
            Mw.prodLaw {x | s ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) ∧
          Mw.prodLaw {x | s ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} ≤
            Mv.prodLaw {x | s - (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) :=
  edgeUniversality_min

end Rigidity

end
