module

public import Rigidity.Edge.EdgeEvent
public import Rigidity.Edge.Hybrid
public import Rigidity.Edge.HybridLaw
public import Rigidity.Edge.Inputs
public import Rigidity.Edge.OneSided
public import Rigidity.Edge.Params
public import Rigidity.Ensemble.Basic
public import Rigidity.Ensemble.Moments
public import Rigidity.LocalLaw.Defs
public import Rigidity.LocalLaw.Strong
public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# Edge universality

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Theorem 2.4 (Theorem 11.1) states that the laws of the extreme eigenvalues `N^{2/3}(λ_N - 2)` and
`N^{2/3}(λ_1 + 2)` of two ensembles of the class of Theorem 2.1 with matching second moments
(2.40) agree up to a shift `N^{-ε}` of the threshold and an additive error `N^{-δ}`, with
`ε = 1/100` and `δ = 1/20`.

The inputs (BB1), (BB2) of the edge argument are the events of (2.21) and (2.25) at
`L = L₀ = A₀ log log N` with the bound `N^{-20}`.  `exists_edgeInputs` obtains them from
Theorems 2.1 (ii) and 2.2: the two statements come with their own constants, `A₀` is the larger of
the two, and `LRange` for the larger `A₀` implies `LRange` for each of them at large `N`.  The
bound `C exp(-c (log N)^{φ L₀}) ≤ N^{-20}` is the first half of (N3).  The largest eigenvalue is
treated by the one-sided comparison of Proposition 11.21 applied in both directions, using that the
second moments match symmetrically; the smallest eigenvalue follows from the reflection `H ↦ -H`,
which preserves the class of Theorem 2.1 (Lemma 2.5 (iv)) and the moment matching (Lemma 11.4
(iii)), and exchanges `λ_1` and `-λ_N`.  All thresholds on `N` are existential.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- (BB1), (BB2) from Theorems 2.1 (ii) and 2.2. -/
private lemma universality_edgeInputs (ϑ δm δp C₀ : ℝ) (hϑ : 0 < ϑ) (hδm : 0 < δm)
    (hδp : 0 < δp) (hC₀ : 0 < C₀) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → LRange A₀ N (edgeL0 A₀ N) →
      EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N := by
  obtain ⟨A₁, C₁, c₁, φ₁, hA₁, hC₁, hc₁, hφ₁, -, N₀₁, h₁⟩ :=
    strongLocalLaw_entries (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨A₂, C₂, c₂, φ₂, hA₂, hC₂, hc₂, hφ₂, -, N₀₂, h₂⟩ :=
    rigidity (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  have hA₀ : 0 < max A₁ A₂ := lt_of_lt_of_le zero_lt_one (le_trans hA₁.le (le_max_left _ _))
  obtain ⟨N₁₁, hN₁₁⟩ := exists_partI_bound_le (max A₁ A₂) C₁ c₁ φ₁ hA₀ hc₁ hφ₁
  obtain ⟨N₁₂, hN₁₂⟩ := exists_partI_bound_le (max A₁ A₂) C₂ c₂ φ₂ hA₀ hc₂ hφ₂
  refine ⟨max A₁ A₂, hA₀, max (max N₀₁ N₀₂) (max (max N₁₁ N₁₂) 3), fun N hN hL => ?_⟩
  have hN₀₁ : N₀₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₀₂ : N₀₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₁₁' : N₁₁ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN₁₂' : N₁₂ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  -- `log log N ≥ 0`
  have hlog : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    exact (Real.le_log_iff_exp_le (by linarith)).2 (he.trans h3)
  have hll : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlog
  have hR : ∀ A : ℝ, A ≤ max A₁ A₂ → LRange A N (edgeL0 (max A₁ A₂) N) := fun A hA =>
    ⟨le_trans (mul_le_mul_of_nonneg_right hA hll) hL.1, hL.2⟩
  have hb₁ := hN₁₁ N hN₁₁'
  have hb₂ := hN₁₂ N hN₁₂'
  exact ⟨fun M hM => (h₁ N hN₀₁ M hM _ (hR A₁ (le_max_left _ _))).trans
      (ENNReal.ofReal_le_ofReal hb₁),
    fun M hM => (h₂ N hN₀₂ M hM _ (hR A₂ (le_max_right _ _))).trans
      (ENNReal.ofReal_le_ofReal hb₂)⟩

/-- The law of the reflected ensemble: `N^{2/3}(λ_N - 2) ≤ r` under `H ↦ -H` is
`-r ≤ N^{2/3}(λ_1 + 2)` under the original ensemble. -/
private lemma universality_prodLaw_neg (N : ℕ) (M : Ensemble 𝕜 N) (r : ℝ) :
    (M.smul (-1)).prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ r} =
      M.prodLaw {x | -r ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} := by
  have hmeas : Measurable fun x : Pair N → 𝕜 => ((-1 : ℝ) : 𝕜) • x := measurable_const_smul _
  have hcl : IsClosed {x : Pair N → 𝕜 | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ r} :=
    isClosed_le (continuous_const.mul (continuous_lamMax.sub continuous_const)) continuous_const
  rw [Ensemble.prodLaw_smul, Measure.map_apply hmeas hcl.measurableSet]
  congr 1
  ext x
  have hneg : ((-1 : ℝ) : 𝕜) • x = -x := by
    rw [RCLike.ofReal_neg, RCLike.ofReal_one, neg_smul, one_smul]
  have hmin : lamMax (-x) = -lamMin x := by
    rw [lamMin_eq_neg_lamMax_neg, neg_neg]
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hneg, hmin]
  constructor <;> intro h <;> nlinarith

/-- Theorem 2.4, (2.41). -/
theorem edgeUniversality_max :
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
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) := by
  intro ϑ hϑ
  refine ⟨1 / 100, 1 / 20, by norm_num, by norm_num, ?_⟩
  intro δm δp C₀ hδm hδp hC₀
  obtain ⟨A₀, hA₀, N₂, hN₂⟩ := universality_edgeInputs (𝕜 := 𝕜) ϑ δm δp C₀ hϑ hδm hδp hC₀
  obtain ⟨N₁, hN₁⟩ := exists_edgeLarge ϑ C₀ A₀ (1 / 50) hϑ hC₀ hA₀ (by norm_num) (by norm_num)
  obtain ⟨N₃, hN₃⟩ := edge_oneSided (𝕜 := 𝕜) ϑ δm δp C₀ A₀ hϑ hC₀ hA₀
  refine ⟨max (max N₁ N₂) N₃, fun N hN Mv Mw hv hw hvw s => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃' : N₃ ≤ N := le_trans (le_max_right _ _) hN
  have hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N := hN₂ N hN₂' (hN₁ N hN₁').lRange
  refine ⟨hN₃ N hN₃' hIn Mv Mw hv hw hvw s, ?_⟩
  have h := hN₃ N hN₃' hIn Mw Mv hw hv hvw.symm (s + (N : ℝ) ^ (-(1 / 100 : ℝ)))
  rwa [add_sub_cancel_right] at h

/-- Theorem 2.4, the smallest eigenvalue. -/
theorem edgeUniversality_min :
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
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) := by
  intro ϑ hϑ
  obtain ⟨ε, δ, hε, hδ, h⟩ := edgeUniversality_max (𝕜 := 𝕜) ϑ hϑ
  refine ⟨ε, δ, hε, hδ, fun δm δp C₀ hδm hδp hC₀ => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h δm δp C₀ hδm hδp hC₀
  refine ⟨N₀, fun N hN Mv Mw hv hw hvw s => ?_⟩
  have key := hN₀ N hN (Mv.smul (-1)) (Mw.smul (-1)) hv.neg hw.neg hvw.smul_neg_one (-s)
  simp only [universality_prodLaw_neg] at key
  obtain ⟨k₁, k₂⟩ := key
  rw [show -(-s - (N : ℝ) ^ (-ε)) = s + (N : ℝ) ^ (-ε) by ring,
    show -(-s) = s by ring] at k₁
  rw [show -(-s) = s by ring, show -(-s + (N : ℝ) ^ (-ε)) = s - (N : ℝ) ^ (-ε) by ring] at k₂
  exact ⟨k₁, k₂⟩

/-- (BB1), (BB2) from Theorems 2.1 (ii) and 2.2. -/
theorem exists_edgeInputs (ϑ δm δp C₀ : ℝ) (hϑ : 0 < ϑ) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 0 < C₀) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → LRange A₀ N (edgeL0 A₀ N) →
      EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N :=
  universality_edgeInputs ϑ δm δp C₀ hϑ hδm hδp hC₀

/-! ### Instances

The inputs (BB1), (BB2) at `ϑ = 1/2`, `δ_- = δ_+ = C₀ = 1`: there is a size `N ≥ 2` at which
`LRange` holds for `A₀ = A₀(1/2, 1, 1, 1)` and `EdgeInputs` follows.  Theorem 2.4 (2.41) and the
statement for the smallest eigenvalue at the same parameters with the Rademacher ensemble (entries
`±N^{-1/2}`) for both `M^v` and `M^w`, over `ℂ` and over `ℝ`, at a size `N ≥ 2`; the second moments
match since the two ensembles coincide. -/

example : ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, 2 ≤ N ∧ LRange A₀ N (edgeL0 A₀ N) ∧
    EdgeInputs ℂ (1 / 2) 1 1 1 A₀ N := by
  obtain ⟨A₀, hA₀, N₂, h⟩ := exists_edgeInputs (𝕜 := ℂ) (1 / 2) 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := exists_edgeLarge (1 / 2) 1 A₀ (1 / 50) (by norm_num) (by norm_num) hA₀
    (by norm_num) (by norm_num)
  have hL : LRange A₀ (max (max N₁ N₂) 2) (edgeL0 A₀ (max (max N₁ N₂) 2)) :=
    (hN₁ _ (le_trans (le_max_left _ _) (le_max_left _ _))).lRange
  exact ⟨A₀, hA₀, max (max N₁ N₂) 2, le_max_right _ _, hL,
    h _ (le_trans (le_max_right _ _) (le_max_left _ _)) hL⟩

example : ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ s : ℝ,
    (rademacher (𝕜 := ℂ) N).prodLaw
        {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-ε)} ≤
      (rademacher (𝕜 := ℂ) N).prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} +
        ENNReal.ofReal ((N : ℝ) ^ (-δ)) ∧
    (rademacher (𝕜 := ℂ) N).prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} ≤
      (rademacher (𝕜 := ℂ) N).prodLaw
        {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s + (N : ℝ) ^ (-ε)} +
        ENNReal.ofReal ((N : ℝ) ^ (-δ)) := by
  obtain ⟨ε, δ, hε, hδ, h⟩ := edgeUniversality_max (𝕜 := ℂ) (1 / 2) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h 1 1 1 one_pos one_pos one_pos
  exact ⟨ε, δ, hε, hδ, N₀ + 2, by omega, fun s => hN₀ (N₀ + 2) (by omega) _ _
    (rademacher_assumptions _ (by omega)) (rademacher_assumptions _ (by omega))
    (fun _ _ _ _ => rfl) s⟩

example : ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ s : ℝ,
    (rademacher (𝕜 := ℝ) N).prodLaw
        {x | s + (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} ≤
      (rademacher (𝕜 := ℝ) N).prodLaw {x | s ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} +
        ENNReal.ofReal ((N : ℝ) ^ (-δ)) ∧
    (rademacher (𝕜 := ℝ) N).prodLaw {x | s ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} ≤
      (rademacher (𝕜 := ℝ) N).prodLaw
        {x | s - (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} +
        ENNReal.ofReal ((N : ℝ) ^ (-δ)) := by
  obtain ⟨ε, δ, hε, hδ, h⟩ := edgeUniversality_min (𝕜 := ℝ) (1 / 2) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := h 1 1 1 one_pos one_pos one_pos
  exact ⟨ε, δ, hε, hδ, N₀ + 2, by omega, fun s => hN₀ (N₀ + 2) (by omega) _ _
    (rademacher_assumptions _ (by omega)) (rademacher_assumptions _ (by omega))
    (fun _ _ _ _ => rfl) s⟩

end Rigidity
