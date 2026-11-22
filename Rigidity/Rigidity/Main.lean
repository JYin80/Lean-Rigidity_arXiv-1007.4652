module

public import Rigidity.Rigidity.Level

@[expose] public section

/-!
# Theorems 2.1 and 2.2 on one event (NP v1.1, §2: Proposition 2.7)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Theorems 2.1 and 2.2 with common constants and one measurable event
(Proposition 2.7 and the last sentence of Theorem 2.1). -/
theorem mainTheorems_event :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
    ∃ Ξ : Set (Pair N → 𝕜), MeasurableSet Ξ ∧
      M.prodLaw Ξᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
      ∀ x ∈ Ξ, MainGood L x := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  set ϑ' := min ϑ 1
  have hϑ' : 0 < ϑ' := lt_min hϑ one_pos
  have hϑ'1 : ϑ' ≤ 1 := min_le_right _ _
  have ha : (1 : ℝ) ≤ ϑ'⁻¹ := one_le_inv₀ hϑ' |>.2 hϑ'1
  obtain ⟨-, -, -, -, -, -, hφ0, hφ1, hA0⟩ := ledgerPhi_mul ha
  obtain ⟨N₁, h1⟩ := localLaw_level (𝕜 := 𝕜) ϑ' (min δm 1) (min δp 1) (max C₀ 1) hϑ' hϑ'1
    (lt_min hδm one_pos) (min_le_right _ _) (lt_min hδp one_pos) (min_le_right _ _)
    (le_max_right _ _)
  refine ⟨ledgerA0 ϑ'⁻¹, 1, 1 / 2, ledgerPhi ϑ'⁻¹, hA0, one_pos, by norm_num, hφ0, hφ1,
    max N₁ 16, fun N hN M hM L hL => ?_⟩
  have hN16 : 16 ≤ N := (le_max_right _ _).trans hN
  have hM' : M.Assumptions ϑ' (min δm 1) (min δp 1) (max C₀ 1) :=
    Ensemble.Assumptions.mono M hM hϑ' (min_le_left _ _) (min_le_left _ _) (min_le_left _ _)
      (le_max_left _ _)
  obtain ⟨hK1, hK2, -⟩ := reduction_level ha hN16 hL
  obtain ⟨Ξ, hΞ, hprob, hgood⟩ := h1 N ((le_max_left _ _).trans hN) M hM' _ hK1 hK2
  refine ⟨Ξ, hΞ, hprob.trans_eq ?_, fun x hx => LevelGood.mainGood ha hN16 hL (hgood x hx)⟩
  congr 1
  ring_nf

/-- Witness for `mainTheorems_event` at the Rademacher ensemble over `ℂ` with `ϑ = 1/2`,
`δ₋ = δ₊ = C₀ = 1`: a dimension `N` and an exponent `L` in the admissible range. -/
example : ∃ (A₀ C c φ : ℝ) (N : ℕ) (L : ℝ), 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    LRange A₀ N L ∧ ∃ Ξ : Set (Pair N → ℂ), MeasurableSet Ξ ∧
      (rademacher (𝕜 := ℂ) N).prodLaw Ξᶜ ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
      ∀ x ∈ Ξ, MainGood L x := by
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := ℂ) (1 / 2) 1 1 1 (by norm_num) one_pos one_pos one_pos
  obtain ⟨N₁, hL⟩ := exists_LRange_nonempty A₀
  set N := max (max N₀ N₁) 16
  obtain ⟨L, hLN⟩ := (hL N ((le_max_right _ _).trans (le_max_left _ _))).1
  exact ⟨A₀, C, c, φ, N, L, hA, hC, hc, hφ, hφ1, hLN,
    h N ((le_max_left _ _).trans (le_max_left _ _)) _
      (rademacher_assumptions N (by omega)) L hLN⟩

end Rigidity
