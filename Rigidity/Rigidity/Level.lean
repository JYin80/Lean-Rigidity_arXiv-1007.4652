import Rigidity.Rigidity.Deterministic
import Rigidity.Strong.Event

/-!
# Theorem 2.6: local law and rigidity at level K (NP v1.1, §2, §8.2)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorem 2.6 (local law and rigidity at level `K`), for normalised parameters. -/
theorem localLaw_level :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → ϑ ≤ 1 → 0 < δm → δm ≤ 1 → 0 < δp → δp ≤ 1 → 1 ≤ C₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
    ∃ Ξ : Set (Pair N → 𝕜), MeasurableSet Ξ ∧
      M.prodLaw Ξᶜ ≤ ENNReal.ofReal (Real.exp (-K / 2)) ∧ ∀ x ∈ Ξ, LevelGood ϑ⁻¹ K x := by
  intro ϑ δm δp C₀ hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₁, h1⟩ := prob_XiK (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := localLaw_i_iii (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  have ha : (1 : ℝ) ≤ ϑ⁻¹ := one_le_inv₀ hϑ |>.2 hϑ1
  refine ⟨max (max N₁ N₂) ⌈Real.exp 6⌉₊, fun N hN M hM K hK1 hK2 => ?_⟩
  have hN6 : Real.exp 6 ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
  obtain ⟨hcl, -, hprob⟩ := h1 N (by omega) M hM K hK1 hK2
  refine ⟨XiK M ϑ⁻¹ C₀ K, hcl.measurableSet, hprob, fun x hx => ?_⟩
  obtain ⟨hi, hii, hiii⟩ := h2 N (by omega) M hM K hK1 hK2 x hx
  have hrig := rigidity_of_localLaw ha hN6 hK1 hK2 (toMatrix_isHermitian x)
    (fun z hre him him' => hi z ⟨by linarith, him, by linarith⟩) hiii
  exact ⟨hi, hii, hiii, fun E => hrig.1 E, hrig.2⟩

end Rigidity
