module

public import Rigidity.Edge.Comparison
public import Rigidity.Edge.Continuity
public import Rigidity.Edge.Cutoff
public import Rigidity.Edge.Inputs
public import Rigidity.Edge.Params
public import Rigidity.Edge.Sandwich
public import Rigidity.Ensemble.Basic
public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# The one-sided comparison for the largest eigenvalue

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Proposition 11.21 is the one-sided comparison of the law of `N^{2/3}(λ_N - 2)` under two ensembles
`M^v`, `M^w` of the class of Theorem 2.1 with matching second moments: with `ε_g = 1/50`,
`ε = ε_g / 2 = 1/100` and `δ = 1/20`,
`P^v(N^{2/3}(λ_N - 2) ≤ s - N^{-ε}) ≤ P^w(N^{2/3}(λ_N - 2) ≤ s) + N^{-δ}`.

The proof splits according to the size of `s` against `(log N)^{L₀} = N^{2/3} W`.  Off the
rigidity event of (BB2), `|λ_N - 2| < W`, because `γ_N = 2` and the weight at `j = N` is `1`; this
settles the cases `s > (log N)^{L₀}` (Case A) and `s < -(log N)^{L₀}` (Case B) with the bound
`N^{-20}` of `EdgeInputs`.  In Case C, `|s| ≤ (log N)^{L₀}`, the point `E = 2 + s N^{-2/3}` lies in
`[2 - W, 2 + W]`, and the chain of Proposition 11.21 combines the upper bound of the sandwich
(Proposition 11.13) at `E' = E - 2ℓ` for `M^v`, the identity `X⁺_{E'} = X⁻_E` of the smoothed
counting functionals, the comparison Theorem 11.20 with the cut-off `q` of §11.8, and the lower
bound of the sandwich at `E` for `M^w`.  The threshold on `N` is existential: it collects the
threshold of `exists_edgeLarge` and the condition (N6),
`C₄ C_q N^{-1/6+4ε_g} + 2 N^{-20} ≤ N^{-δ}`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The condition (N6): `K N^{-1/6+4ε_g} + 2 N^{-20} ≤ N^{-1/20}` for all large `N`, at
`ε_g = 1/50`. -/
private lemma oneSided_N6 (K : ℝ) (hK : 0 < K) :
    ∃ N₆ : ℕ, ∀ N : ℕ, N₆ ≤ N →
      K * (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * (1 / 50 : ℝ)) + 2 * (N : ℝ) ^ (-20 : ℝ) ≤
        (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
  refine ⟨⌈max 2 ((2 * K) ^ (300 / 11 : ℝ))⌉₊, fun N hN => ?_⟩
  have hx : max 2 ((2 * K) ^ (300 / 11 : ℝ)) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hx2 : (2 : ℝ) ≤ N := le_trans (le_max_left _ _) hx
  have hxK : (2 * K) ^ (300 / 11 : ℝ) ≤ N := le_trans (le_max_right _ _) hx
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have h1 : 2 * K ≤ (N : ℝ) ^ (11 / 300 : ℝ) := by
    calc 2 * K = ((2 * K) ^ (300 / 11 : ℝ)) ^ (11 / 300 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]
          norm_num
      _ ≤ (N : ℝ) ^ (11 / 300 : ℝ) := Real.rpow_le_rpow (by positivity) hxK (by norm_num)
  have e1 : (N : ℝ) ^ (-(1 / 6 : ℝ) + 4 * (1 / 50 : ℝ)) =
      (N : ℝ) ^ (-(11 / 300 : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    norm_num
  have e2 : (N : ℝ) ^ (-(11 / 300 : ℝ)) * (N : ℝ) ^ (11 / 300 : ℝ) = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hp : 0 < (N : ℝ) ^ (-(1 / 20 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hq : 0 < (N : ℝ) ^ (-(11 / 300 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have h3 : K * (N : ℝ) ^ (-(11 / 300 : ℝ)) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h1 hq.le
    nlinarith
  have e3 : (N : ℝ) ^ (-20 : ℝ) =
      (N : ℝ) ^ (-(399 / 20 : ℝ)) * (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    norm_num
  have e4 : (N : ℝ) ^ (-(399 / 20 : ℝ)) * (N : ℝ) ^ (399 / 20 : ℝ) = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have h5 : (4 : ℝ) ≤ (N : ℝ) ^ (399 / 20 : ℝ) := by
    calc (4 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
          rw [Real.rpow_two]
          nlinarith
      _ ≤ (N : ℝ) ^ (399 / 20 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hq' : 0 < (N : ℝ) ^ (-(399 / 20 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have h4 : (N : ℝ) ^ (-(399 / 20 : ℝ)) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left h5 hq'.le
    nlinarith
  rw [e1, e3]
  nlinarith [mul_le_mul_of_nonneg_right h3 hp.le, mul_le_mul_of_nonneg_right h4 hp.le]

/-- Off the event of (BB2) at `L = L₀`, `|λ_N - 2| < W`: the classical location `γ_N` is `2` and
the weight `min(j, N - j + 1)` at `j = N` is `1`. -/
private lemma oneSided_lamMax_sub_two {A₀ : ℝ} {N : ℕ} (hN0 : 0 < N) {x : Pair N → 𝕜}
    (hx : x ∉ rigidityEvent N (edgeL0 A₀ N)) : |lamMax x - 2| < edgeW A₀ N := by
  simp only [rigidityEvent, Set.mem_ofPred_eq, not_exists, not_le] at hx
  have h := hx ⟨N - 1, by omega⟩
  have hw : rigWeight N ⟨N - 1, by omega⟩ = 1 := by
    unfold rigWeight
    simp only
    omega
  have hl : lamMax x = eig x ⟨N - 1, by omega⟩ := by
    unfold lamMax
    simp only [hN0, dite_true]
  rw [hw, gamma_last hN0] at h
  rw [hl]
  simpa [edgeW] using h

/-- Proposition 11.21, with `ε = 1/100`, `δ = 1/20`. -/
theorem edge_oneSided (ϑ δm δp C₀ A₀ : ℝ) (hϑ : 0 < ϑ) (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) :
    ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N → EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N →
      ∀ Mv Mw : Ensemble 𝕜 N, Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ →
      Ensemble.MomentMatch2 Mv Mw → ∀ s : ℝ,
        Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-(1 / 100 : ℝ))} ≤
          Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} +
            ENNReal.ofReal ((N : ℝ) ^ (-(1 / 20 : ℝ))) := by
  obtain ⟨N₁, hN₁⟩ := exists_edgeLarge ϑ C₀ A₀ (1 / 50) hϑ hC₀ hA₀ (by norm_num) (by norm_num)
  obtain ⟨C₄, hC₄, hcomp⟩ := edgeComparison (𝕜 := 𝕜) ϑ C₀ hϑ hC₀
  obtain ⟨Cq, hCq, hCqb⟩ := exists_iteratedDeriv_edgeCutoff_le
  obtain ⟨N₆, hN₆⟩ := oneSided_N6 (C₄ * Cq) (mul_pos hC₄ hCq)
  refine ⟨max N₁ N₆, fun N hN hIn Mv Mw hv hw hvw s => ?_⟩
  have hNL : EdgeLarge ϑ C₀ A₀ (1 / 50) N := hN₁ N (le_trans (le_max_left _ _) hN)
  have h6 := hN₆ N (le_trans (le_max_right _ _) hN)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hNL.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hNL.exp_le
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hT : 0 < Real.log N := by
    have h : (1 : ℝ) + 27 ≤ Real.exp 27 := by linarith [Real.add_one_le_exp (27 : ℝ)]
    exact Real.log_pos (by linarith [hNL.exp_le])
  have hW : 0 < edgeW A₀ N :=
    mul_pos (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hNpos _)
  have hℓ : 0 < edgeEll (1 / 50) N := mul_pos (by norm_num) (Real.rpow_pos_of_pos hNpos _)
  have hℓW : 2 * edgeEll (1 / 50) N ≤ edgeW A₀ N := hNL.ell_le
  have hc : 0 < (N : ℝ) ^ (-(1 / 100 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hsmall : ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(1 / 20 : ℝ))) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hBv : Mv.prodLaw (rigidityEvent N (edgeL0 A₀ N)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) :=
    hIn.rigidity Mv hv
  have hBw : Mw.prodLaw (rigidityEvent N (edgeL0 A₀ N)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) :=
    hIn.rigidity Mw hw
  have hab : (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hapos : 0 < (N : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hbpos : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  -- `N^{2/3} W = (log N)^{L₀}`
  have haW : (N : ℝ) ^ (2 / 3 : ℝ) * edgeW A₀ N = Real.log N ^ edgeL0 A₀ N := by
    unfold edgeW
    linear_combination (Real.log N ^ edgeL0 A₀ N) * hab
  -- off the event of (BB2), `|N^{2/3} (λ_N - 2)| < (log N)^{L₀}`
  have hoff : ∀ x : Pair N → 𝕜, x ∉ rigidityEvent N (edgeL0 A₀ N) →
      |(N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2)| < Real.log N ^ edgeL0 A₀ N := by
    intro x hx
    rw [abs_mul, abs_of_pos hapos, ← haW]
    exact mul_lt_mul_of_pos_left (oneSided_lamMax_sub_two hN0 hx) hapos
  by_cases hA : Real.log N ^ edgeL0 A₀ N < s
  · -- Case A
    have hcov : (Set.univ : Set (Pair N → 𝕜)) ⊆
        {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} ∪ rigidityEvent N (edgeL0 A₀ N) := by
      intro x _
      by_cases hxB : x ∈ rigidityEvent N (edgeL0 A₀ N)
      · exact Or.inr hxB
      · left
        have := (abs_lt.1 (hoff x hxB)).2
        change (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s
        linarith
    calc Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-(1 / 100 : ℝ))}
        ≤ 1 := prob_le_one
      _ = Mw.prodLaw Set.univ := measure_univ.symm
      _ ≤ Mw.prodLaw ({x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} ∪
            rigidityEvent N (edgeL0 A₀ N)) := measure_mono hcov
      _ ≤ Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} +
            Mw.prodLaw (rigidityEvent N (edgeL0 A₀ N)) := measure_union_le _ _
      _ ≤ Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} +
            ENNReal.ofReal ((N : ℝ) ^ (-(1 / 20 : ℝ))) := add_le_add le_rfl (hBw.trans hsmall)
  by_cases hB : s < -Real.log N ^ edgeL0 A₀ N
  · -- Case B
    have hsub : {x : Pair N → 𝕜 |
        (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-(1 / 100 : ℝ))} ⊆
        rigidityEvent N (edgeL0 A₀ N) := by
      intro x hx
      by_contra hxB
      have h1 := (abs_lt.1 (hoff x hxB)).1
      have h2 : (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-(1 / 100 : ℝ)) := hx
      linarith
    calc Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-(1 / 100 : ℝ))}
        ≤ Mv.prodLaw (rigidityEvent N (edgeL0 A₀ N)) := measure_mono hsub
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(1 / 20 : ℝ))) := hBv.trans hsmall
      _ ≤ _ := le_add_self
  -- Case C
  have hsR : s ≤ Real.log N ^ edgeL0 A₀ N := not_lt.1 hA
  have hRs : -Real.log N ^ edgeL0 A₀ N ≤ s := not_lt.1 hB
  set a : ℝ := (N : ℝ) ^ (2 / 3 : ℝ) with ha
  set b : ℝ := (N : ℝ) ^ (-(2 / 3 : ℝ)) with hb
  set c : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hc'
  set ℓ : ℝ := edgeEll (1 / 50) N with hℓdef
  set W : ℝ := edgeW A₀ N with hWdef
  set R : ℝ := Real.log N ^ edgeL0 A₀ N with hR
  have hWR : W = R * b := rfl
  -- the point `E = 2 + s N^{-2/3}` and `E' = E - 2 ℓ`
  have hsb1 : s * b ≤ W := by
    rw [hWR]
    exact mul_le_mul_of_nonneg_right hsR hbpos.le
  have hsb2 : -W ≤ s * b := by
    rw [hWR, neg_mul_eq_neg_mul]
    exact mul_le_mul_of_nonneg_right hRs hbpos.le
  have hE : 2 + s * b ∈ Set.Icc (2 - 2 * W) (2 + W) := ⟨by linarith, by linarith⟩
  have hE' : 2 + s * b - 2 * ℓ ∈ Set.Icc (2 - 2 * W) (2 + W) := ⟨by linarith, by linarith⟩
  -- `3 ℓ = N^{-2/3} N^{-ε}`
  have h3ℓ : 3 * ℓ = b * c := by
    rw [hℓdef, hb, hc']
    unfold edgeEll
    rw [← Real.rpow_add hNpos]
    rw [show (-(2 / 3 : ℝ) + -(1 / 100 : ℝ)) = -(2 / 3 : ℝ) - 1 / 50 / 2 by norm_num]
    ring
  -- inclusion of the events
  have hsub1 : {x : Pair N → 𝕜 | a * (lamMax x - 2) ≤ s - c} ⊆
      {x : Pair N → 𝕜 | lamMax x < 2 + s * b - 2 * ℓ} := by
    intro x hx
    have h1 : a * (lamMax x - 2) ≤ s - c := hx
    have h2 : lamMax x - 2 = a * (lamMax x - 2) * b := by
      linear_combination (-(lamMax x - 2)) * hab
    have h3 : a * (lamMax x - 2) * b ≤ (s - c) * b := mul_le_mul_of_nonneg_right h1 hbpos.le
    change lamMax x < 2 + s * b - 2 * ℓ
    nlinarith
  have hsub2 : {x : Pair N → 𝕜 | lamMax x < 2 + s * b} ⊆
      {x : Pair N → 𝕜 | a * (lamMax x - 2) ≤ s} := by
    intro x hx
    have h1 : lamMax x < 2 + s * b := hx
    have h2 : a * (lamMax x - 2) ≤ a * (s * b) := mul_le_mul_of_nonneg_left (by linarith) hapos.le
    change a * (lamMax x - 2) ≤ s
    have h3 : a * (s * b) = s := by linear_combination s * hab
    linarith
  -- the sandwich
  have hq : Measurable edgeCutoff := contDiff_edgeCutoff.continuous.measurable
  have hup := (sandwich (𝕜 := 𝕜) (by norm_num) (by norm_num) hNL hIn edgeCutoff hq
    edgeCutoff_mem_Icc (fun x hx => edgeCutoff_eq_one hx) (fun x hx => edgeCutoff_eq_zero hx)
    hE' Mv hv).2
  have hlow := (sandwich (𝕜 := 𝕜) (by norm_num) (by norm_num) hNL hIn edgeCutoff hq
    edgeCutoff_mem_Icc (fun x hx => edgeCutoff_eq_one hx) (fun x hx => edgeCutoff_eq_zero hx)
    hE Mw hw).1
  rw [show 2 + s * b - 2 * ℓ + ℓ = 2 + s * b - ℓ by ring] at hup
  -- the comparison
  have hTw : 2 * W ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + 1 / 50) := by
    have h1 := hNL.logPow_le'
    have h2 : (N : ℝ) ^ (-(2 / 3 : ℝ) + 1 / 50) = (N : ℝ) ^ (1 / 50 : ℝ) * b := by
      rw [Real.rpow_add hNpos, mul_comm]
    rw [h2, hWR]
    nlinarith [mul_le_mul_of_nonneg_right h1 hbpos.le]
  have hmem : ∀ y : ℝ, 2 - 2 * W ≤ y → y ≤ 2 + 2 * W → y ∈ edgeWindow (1 / 50) N :=
    fun y h1 h2 => by
      unfold edgeWindow
      exact ⟨by linarith, by linarith⟩
  have hE₂ : edgeEL A₀ N = 2 + 2 * W := rfl
  have hcmp := hcomp δm δp A₀ (1 / 50) (by norm_num) (by norm_num) N hNL hIn Mv Mw hv hw hvw
    (2 + s * b - ℓ) (edgeEL A₀ N) (by rw [hE₂]; linarith)
    (hmem _ (by linarith) (by linarith)) (hmem _ (by rw [hE₂]; linarith) (by rw [hE₂]))
    edgeCutoff Cq contDiff_edgeCutoff (fun k hk x => hCqb k hk x)
  have hreal : Mv.prodLaw.real {x : Pair N → 𝕜 | lamMax x < 2 + s * b - 2 * ℓ} ≤
      Mw.prodLaw.real {x : Pair N → 𝕜 | a * (lamMax x - 2) ≤ s} +
        (N : ℝ) ^ (-(1 / 20 : ℝ)) := by
    have hm := measureReal_mono (μ := Mw.prodLaw) hsub2
    have h1 := (abs_le.1 hcmp).2
    linarith
  calc Mv.prodLaw {x : Pair N → 𝕜 | a * (lamMax x - 2) ≤ s - c}
      ≤ Mv.prodLaw {x : Pair N → 𝕜 | lamMax x < 2 + s * b - 2 * ℓ} := measure_mono hsub1
    _ = ENNReal.ofReal (Mv.prodLaw.real {x : Pair N → 𝕜 | lamMax x < 2 + s * b - 2 * ℓ}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Mw.prodLaw.real {x : Pair N → 𝕜 | a * (lamMax x - 2) ≤ s} +
          (N : ℝ) ^ (-(1 / 20 : ℝ))) := ENNReal.ofReal_le_ofReal hreal
    _ = Mw.prodLaw {x : Pair N → 𝕜 | a * (lamMax x - 2) ≤ s} +
          ENNReal.ofReal ((N : ℝ) ^ (-(1 / 20 : ℝ))) := by
        rw [ENNReal.ofReal_add measureReal_nonneg (Real.rpow_nonneg hNpos.le _),
          ofReal_measureReal (measure_ne_top _ _)]

end Rigidity
