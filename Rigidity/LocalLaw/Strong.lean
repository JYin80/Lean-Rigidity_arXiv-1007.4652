module

public import Rigidity.Rigidity.Main

@[expose] public section

/-!
# Theorems 2.1 and 2.2: the endpoint statements (NP v1.1, §2: (2.19), (2.21), (2.22), (2.25),
(2.26))

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- Theorem 2.1 (i), (2.19). -/
theorem strongLocalLaw_avg :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) / (N * z.im) ≤ Lam x z}) ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  refine ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, fun N hN M hM L hL => ?_⟩
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N hN M hM L hL
  refine (measure_mono ?_).trans hprob
  intro x hx hxΞ
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  obtain ⟨z, hz, hle⟩ := hx
  exact absurd ((hgood x hxΞ).1 z hz) (not_lt.2 hle)

/-- Theorem 2.1 (ii), (2.21). -/
theorem strongLocalLaw_entries :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
          Real.log N ^ (4 * L) / (N * z.im) ≤ LamD x z + LamO x z}) ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  refine ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, fun N hN M hM L hL => ?_⟩
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N hN M hM L hL
  refine (measure_mono ?_).trans hprob
  intro x hx hxΞ
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
  obtain ⟨z, hz, hle⟩ := hx
  exact absurd ((hgood x hxΞ).2.1 z hz) (not_lt.2 hle)

/-- Theorem 2.1 (iii), (2.22). -/
theorem extremeEigenvalues_le :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | ∃ k : Fin N,
          2 + (N : ℝ) ^ (-(2 / 3 : ℝ)) * Real.log N ^ (9 * L) ≤ |eig x k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  refine ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, fun N hN M hM L hL => ?_⟩
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N hN M hM L hL
  refine (measure_mono ?_).trans hprob
  intro x hx hxΞ
  obtain ⟨k, hk⟩ := hx
  exact absurd ((hgood x hxΞ).2.2.1 k) (not_lt.2 hk)

/-- Theorem 2.2, (2.25). -/
theorem rigidity :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | ∃ k : Fin N, Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |eig x k - gamma N k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  refine ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, fun N hN M hM L hL => ?_⟩
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N hN M hM L hL
  refine (measure_mono ?_).trans hprob
  intro x hx hxΞ
  obtain ⟨k, hk⟩ := hx
  exact absurd ((hgood x hxΞ).2.2.2.1 k) (not_lt.2 hk)

/-- Theorem 2.2, (2.26), with the supremum itself. -/
theorem countingFunction_close :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | Real.log N ^ L / N ≤ ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  intro ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  refine ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, fun N hN M hM L hL => ?_⟩
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N hN M hM L hL
  refine (measure_mono ?_).trans hprob
  intro x hx hxΞ
  exact absurd (hgood x hxΞ).2.2.2.2 (not_lt.2 hx)

/-- Witness for the five endpoint statements at the Rademacher ensemble over `ℂ` with `ϑ = 1/2`,
`δ₋ = δ₊ = C₀ = 1`: the bounds hold at one admissible pair `(N, L)` with the common constants. -/
example : ∃ (A₀ C c φ : ℝ) (N : ℕ) (L : ℝ), 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    LRange A₀ N L ∧
    (rademacher (𝕜 := ℂ) N).prodLaw
        (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) / (N * z.im) ≤ Lam x z}) ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
    (rademacher (𝕜 := ℂ) N).prodLaw
        (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
          Real.log N ^ (4 * L) / (N * z.im) ≤ LamD x z + LamO x z}) ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
    (rademacher (𝕜 := ℂ) N).prodLaw {x | ∃ k : Fin N,
          2 + (N : ℝ) ^ (-(2 / 3 : ℝ)) * Real.log N ^ (9 * L) ≤ |eig x k|} ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
    (rademacher (𝕜 := ℂ) N).prodLaw {x | ∃ k : Fin N, Real.log N ^ L *
          (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          |eig x k - gamma N k|} ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
    (rademacher (𝕜 := ℂ) N).prodLaw
        {x | Real.log N ^ L / N ≤ ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} ≤
      ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) := by
  obtain ⟨A₀, C, c, φ, hA, hC, hc, hφ, hφ1, N₀, h⟩ :=
    mainTheorems_event (𝕜 := ℂ) (1 / 2) 1 1 1 (by norm_num) one_pos one_pos one_pos
  obtain ⟨N₁, hL⟩ := exists_LRange_nonempty A₀
  set N := max (max N₀ N₁) 16
  obtain ⟨L, hLN⟩ := (hL N ((le_max_right _ _).trans (le_max_left _ _))).1
  obtain ⟨Ξ, -, hprob, hgood⟩ := h N ((le_max_left _ _).trans (le_max_left _ _)) _
    (rademacher_assumptions N (by omega)) L hLN
  refine ⟨A₀, C, c, φ, N, L, hA, hC, hc, hφ, hφ1, hLN, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine (measure_mono ?_).trans hprob <;> intro x hx hxΞ
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    obtain ⟨z, hz, hle⟩ := hx
    exact absurd ((hgood x hxΞ).1 z hz) (not_lt.2 hle)
  · simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    obtain ⟨z, hz, hle⟩ := hx
    exact absurd ((hgood x hxΞ).2.1 z hz) (not_lt.2 hle)
  · obtain ⟨k, hk⟩ := hx
    exact absurd ((hgood x hxΞ).2.2.1 k) (not_lt.2 hk)
  · obtain ⟨k, hk⟩ := hx
    exact absurd ((hgood x hxΞ).2.2.2.1 k) (not_lt.2 hk)
  · exact absurd (hgood x hxΞ).2.2.2.2 (not_lt.2 hx)

end Rigidity
