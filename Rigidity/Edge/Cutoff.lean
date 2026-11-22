module

public import Mathlib

@[expose] public section

/-!
# The smooth cutoff `q`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The file defines the cutoff `q(x) = 1 - S(9x - 1)` of Section 11.8, where `S` is Mathlib's smooth
transition function (the alternative to the polynomial step allowed in Section 11.8).  It proves
that `q` is `C³` (indeed smooth), takes values in `[0, 1]`, equals `1` on `x ≤ 1/9` and `0` on
`x ≥ 2/9`, and that the constant `C_q = max_{k ≤ 3} sup |q^{(k)}|` is finite, by compactness of
`[1/9, 2/9]` and because `q` is locally constant outside it.
-/

open Real

namespace Rigidity

/-- The cutoff `q(x) = 1 - S(9x - 1)` of §11.8, with the smooth transition function `S`. -/
noncomputable def edgeCutoff (x : ℝ) : ℝ := 1 - Real.smoothTransition (9 * x - 1)

theorem contDiff_edgeCutoff : ContDiff ℝ 3 edgeCutoff := by
  have hS : ContDiff ℝ 3 Real.smoothTransition := by
    exact_mod_cast (Real.smoothTransition.contDiff (n := 3))
  have h : ContDiff ℝ 3 (fun x : ℝ => 9 * x - 1) := by fun_prop
  exact contDiff_const.sub (hS.comp h)

theorem edgeCutoff_mem_Icc (x : ℝ) : edgeCutoff x ∈ Set.Icc 0 1 := by
  unfold edgeCutoff
  have h0 := Real.smoothTransition.nonneg (9 * x - 1)
  have h1 := Real.smoothTransition.le_one (9 * x - 1)
  constructor <;> linarith

theorem edgeCutoff_eq_one {x : ℝ} (hx : x ≤ 1 / 9) : edgeCutoff x = 1 := by
  unfold edgeCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

theorem edgeCutoff_eq_zero {x : ℝ} (hx : 2 / 9 ≤ x) : edgeCutoff x = 0 := by
  unfold edgeCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

/-- Away from `[1/9, 2/9]` the derivatives of `q` of positive order vanish. -/
private lemma edgeCutoff_iteratedDeriv_eq_zero {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : x ∉ Set.Icc (1 / 9 : ℝ) (2 / 9)) : iteratedDeriv k edgeCutoff x = 0 := by
  have hk' : k ≠ 0 := by omega
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have hev : edgeCutoff =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact edgeCutoff_eq_one (le_of_lt hy)
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
    simp [hk']
  · have hev : edgeCutoff =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact edgeCutoff_eq_zero (le_of_lt hy)
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
    simp [hk']

/-- `C_q = max_{k ≤ 3} sup |q^{(k)}| < ∞`. -/
theorem exists_iteratedDeriv_edgeCutoff_le :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ k : ℕ, k ≤ 3 → ∀ x : ℝ, |iteratedDeriv k edgeCutoff x| ≤ Cq := by
  have hcpt : IsCompact (Set.Icc (1 / 9 : ℝ) (2 / 9)) := isCompact_Icc
  have hM : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      (k ≤ 3 → ∀ x ∈ Set.Icc (1 / 9 : ℝ) (2 / 9), |iteratedDeriv k edgeCutoff x| ≤ M) := by
    intro k
    by_cases hk : k ≤ 3
    · have hc : Continuous (iteratedDeriv k edgeCutoff) :=
        contDiff_edgeCutoff.continuous_iteratedDeriv k (by exact_mod_cast hk)
      obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hc.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun _ x hx => ?_⟩
      exact (by simpa using hC x hx : |iteratedDeriv k edgeCutoff x| ≤ C).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose M hM0 hMb using hM
  refine ⟨1 + ∑ k ∈ Finset.range 4, M k, ?_, fun k hk x => ?_⟩
  · have : 0 ≤ ∑ k ∈ Finset.range 4, M k := Finset.sum_nonneg fun k _ => hM0 k
    linarith
  · have hsum : M k ≤ ∑ j ∈ Finset.range 4, M j :=
      Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.2 (by omega))
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range 4, M j := Finset.sum_nonneg fun j _ => hM0 j
    by_cases hx : x ∈ Set.Icc (1 / 9 : ℝ) (2 / 9)
    · have := hMb k hk x hx
      linarith
    · rcases Nat.eq_zero_or_pos k with rfl | hpos
      · have h := edgeCutoff_mem_Icc x
        have : |iteratedDeriv 0 edgeCutoff x| ≤ 1 := by
          rw [iteratedDeriv_zero, abs_le]
          constructor <;> linarith [h.1, h.2]
        linarith
      · rw [edgeCutoff_iteratedDeriv_eq_zero hpos hx]
        simp only [abs_zero]
        linarith

end Rigidity
