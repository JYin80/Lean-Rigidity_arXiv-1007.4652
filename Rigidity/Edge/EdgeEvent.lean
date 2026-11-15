import Rigidity.Edge.Inputs
import Rigidity.Edge.GoodSet
import Rigidity.Edge.Continuity
import Rigidity.Edge.Params

/-!
# The edge event and its probability

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `ε_g > 0` the window is `I_edge = [2 - N^{-2/3+ε_g}, 2 + N^{-2/3+ε_g}]`, and `edgeBad εg N`
is the event `Ω_edge` of Lemma 11.6: for some `y ∈ I_edge` and some indices `k, l` the shifted
resolvent entry satisfies `|G_{kl}(y + i η) + δ_{kl}| > Ψ / 2`, with `η = N^{-2/3-ε_g}`.  It is
open (Step 0 of Lemma 11.6).  Its probability is at most `N^{-20}`: an element of `Ω_edge` lies in
the event of (BB1) at `L = L₀`, because `y + i η ∈ S_{L₀}` and the control parameter of (BB1) at
`y + i η` is at most `N^{-1/3+3ε_g/2}`, which together with Lemma 11.5 (b) is below `Ψ / 2`.

The tail of one entry beyond `t = N^{-1/2+2ε_g}` has probability at most `N^{-20}` ((11.b3:T)).
With Lemma 11.6 this bounds by `2 N^{-20}` the probability that the matrix `H^{[p]}` with the entry
`p` removed lies outside the good set `𝒢_p` (Lemma 11.15 (b)).
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `I_edge = [2 - N^{-2/3+ε_g}, 2 + N^{-2/3+ε_g}]` (Lemma 11.6). -/
noncomputable def edgeWindow (εg : ℝ) (N : ℕ) : Set ℝ :=
  Set.Icc (2 - (N : ℝ) ^ (-(2 / 3 : ℝ) + εg)) (2 + (N : ℝ) ^ (-(2 / 3 : ℝ) + εg))

/-- `Ω_edge` (Lemma 11.6). -/
def edgeBad (εg : ℝ) (N : ℕ) : Set (Pair N → 𝕜) :=
  {x | ∃ y ∈ edgeWindow εg N, ∃ k l : Fin N,
    edgePsi εg N / 2 < ‖(green (toMatrix x) ⟨y, edgeEta εg N⟩ + 1) k l‖}

/-- The control parameter of (BB1) at `y + i η` is at most `N^{-1/3+3ε_g/2}`. -/
private lemma edgeEvent_control_le {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) {y : ℝ} (hy : |y - 2| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εg)) :
    Real.log N ^ (4 * edgeL0 A₀ N) *
        Real.sqrt ((msc ⟨y, edgeEta εg N⟩).im / (N * (⟨y, edgeEta εg N⟩ : ℂ).im)) +
      Real.log N ^ (4 * edgeL0 A₀ N) / (N * (⟨y, edgeEta εg N⟩ : ℂ).im) ≤
    (N : ℝ) ^ (-(1 / 3 : ℝ) + 3 * εg / 2) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hN1' : 1 ≤ N := by exact_mod_cast hN1
  have hP0 : 0 ≤ Real.log (N : ℝ) ^ (4 * edgeL0 A₀ N) :=
    Real.rpow_nonneg (Real.log_nonneg hN1) _
  have hd0 : 0 < (N : ℝ) ^ (1 / 3 - εg) := Real.rpow_pos_of_pos hNpos _
  have hs0 : 0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) := Real.rpow_pos_of_pos hNpos _
  have hNη : (N : ℝ) * (⟨y, edgeEta εg N⟩ : ℂ).im = (N : ℝ) ^ (1 / 3 - εg) := by
    change (N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) - εg) = _
    calc (N : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) - εg)
        = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ) - εg) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-(2 / 3 : ℝ) - εg)) := (Real.rpow_add hNpos _ _).symm
      _ = _ := by congr 1; ring
  have hds : 1 / (N : ℝ) ^ (1 / 3 - εg) = (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) := by
    rw [one_div, ← Real.rpow_neg hNpos.le]
    congr 1
    ring
  obtain ⟨-, -, him⟩ := msc_edge_le hN1' hεg hεg' hy
  have hr : (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hr0 : 0 ≤ (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) := Real.rpow_nonneg hNpos.le _
  have hsqrt2 : Real.sqrt 2 ≤ 4 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hq : (msc ⟨y, edgeEta εg N⟩).im / (N : ℝ) ^ (1 / 3 - εg) ≤
      (2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg)) ^ 2 := by
    calc (msc ⟨y, edgeEta εg N⟩).im / (N : ℝ) ^ (1 / 3 - εg)
        ≤ Real.sqrt 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) / (N : ℝ) ^ (1 / 3 - εg) :=
          div_le_div_of_nonneg_right him hd0.le
      _ = Real.sqrt 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) *
            (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) := by rw [div_eq_mul_one_div, hds]
      _ ≤ 4 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hsqrt2 hr hr0 (by norm_num)) hs0.le
      _ = (2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg)) ^ 2 := by ring
  have hsq : Real.sqrt ((msc ⟨y, edgeEta εg N⟩).im / (N : ℝ) ^ (1 / 3 - εg)) ≤
      2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) := Real.sqrt_le_iff.2 ⟨by positivity, hq⟩
  rw [hNη]
  calc Real.log N ^ (4 * edgeL0 A₀ N) *
          Real.sqrt ((msc ⟨y, edgeEta εg N⟩).im / (N : ℝ) ^ (1 / 3 - εg)) +
        Real.log N ^ (4 * edgeL0 A₀ N) / (N : ℝ) ^ (1 / 3 - εg)
      ≤ Real.log N ^ (4 * edgeL0 A₀ N) * (2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg)) +
        Real.log N ^ (4 * edgeL0 A₀ N) * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hsq hP0) (le_of_eq ?_)
        rw [div_eq_mul_one_div, hds]
    _ = (3 * Real.log N ^ (4 * edgeL0 A₀ N)) * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) := by ring
    _ ≤ (N : ℝ) ^ (εg / 2) * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg) :=
        mul_le_mul_of_nonneg_right hN.logPow_le hs0.le
    _ = (N : ℝ) ^ (-(1 / 3 : ℝ) + 3 * εg / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring

/-- The sum of the control parameter bound and of the bound for `|m_sc + 1|` is at most `Ψ / 2`. -/
private lemma edgeEvent_final_le {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hεg : 0 < εg)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    (N : ℝ) ^ (-(1 / 3 : ℝ) + 3 * εg / 2) + Real.sqrt 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) ≤
      edgePsi εg N / 2 := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hs2 : 0 < (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) := Real.rpow_pos_of_pos hNpos _
  have hq0 : 0 < (N : ℝ) ^ (-(εg / 2)) := Real.rpow_pos_of_pos hNpos _
  have hq : (N : ℝ) ^ (-(εg / 2)) ≤ 1 / 10 := by
    have h := hN.sandwich_le'
    rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at h
    linarith [Real.pi_lt_four]
  have hu0 : 0 ≤ (N : ℝ) ^ (-(3 * εg / 2)) := Real.rpow_nonneg hNpos.le _
  have hu : (N : ℝ) ^ (-(3 * εg / 2)) ≤ (N : ℝ) ^ (-(εg / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have e1 : (N : ℝ) ^ (-(1 / 3 : ℝ) + 3 * εg / 2) =
      (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (N : ℝ) ^ (-(εg / 2)) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have e2 : (N : ℝ) ^ (-(1 / 3 : ℝ) + εg / 2) =
      (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (N : ℝ) ^ (-(3 * εg / 2)) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hsqrt2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hPsi : edgePsi εg N / 2 = 2 * (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) := by
    unfold edgePsi
    ring
  rw [hPsi, e1, e2]
  have h1 : (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (N : ℝ) ^ (-(εg / 2)) ≤
      (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (1 / 10) :=
    mul_le_mul_of_nonneg_left hq hs2.le
  have h2 : Real.sqrt 2 * ((N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (N : ℝ) ^ (-(3 * εg / 2))) ≤
      2 * ((N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) * (1 / 10)) :=
    mul_le_mul hsqrt2 (mul_le_mul_of_nonneg_left (hu.trans hq) hs2.le)
      (mul_nonneg hs2.le hu0) (by norm_num)
  linarith

/-- Entrywise, `|(G + 1)_{kl}| ≤ Λ_d + Λ_o + |m_sc + 1|`. -/
private lemma edgeEvent_entry_le {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) (k l : Fin N) :
    ‖(green (toMatrix x) z + 1) k l‖ ≤ LamD x z + LamO x z + ‖msc z + 1‖ := by
  have hD : 0 ≤ LamD x z := Real.iSup_nonneg fun _ => norm_nonneg _
  have hO : 0 ≤ LamO x z := Real.iSup_nonneg fun _ => norm_nonneg _
  by_cases hkl : k = l
  · subst hkl
    have h1 : ‖green (toMatrix x) z k k - msc z‖ ≤ LamD x z :=
      le_ciSup (f := fun k : Fin N => ‖green (toMatrix x) z k k - msc z‖)
        (Set.finite_range _).bddAbove k
    calc ‖(green (toMatrix x) z + 1) k k‖
        = ‖(green (toMatrix x) z k k - msc z) + (msc z + 1)‖ := by
          rw [Matrix.add_apply, Matrix.one_apply_eq]
          congr 1
          ring
      _ ≤ ‖green (toMatrix x) z k k - msc z‖ + ‖msc z + 1‖ := norm_add_le _ _
      _ ≤ LamD x z + LamO x z + ‖msc z + 1‖ := by linarith
  · have h1 : ‖green (toMatrix x) z k l‖ ≤ LamO x z :=
      le_ciSup (f := fun q : {q : Fin N × Fin N // q.1 ≠ q.2} =>
        ‖green (toMatrix x) z q.1.1 q.1.2‖) (Set.finite_range _).bddAbove ⟨(k, l), hkl⟩
    rw [Matrix.add_apply, Matrix.one_apply_ne hkl, add_zero]
    linarith [norm_nonneg (msc z + 1)]

/-- Step 3 of Lemma 11.6: `Ω_edge` is contained in the event of (BB1) at `L = L₀`. -/
private lemma edgeEvent_subset {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    edgeBad (𝕜 := 𝕜) εg N ⊆ localLawEvent N (edgeL0 A₀ N) := by
  rintro x ⟨y, hy, k, l, hkl⟩
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hN1' : 1 ≤ N := by exact_mod_cast hN1
  have hya : |y - 2| ≤ (N : ℝ) ^ (-(2 / 3 : ℝ) + εg) :=
    abs_le.2 ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
  have ha1 : (N : ℝ) ^ (-(2 / 3 : ℝ) + εg) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hη1 : edgeEta εg N ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hz : (⟨y, edgeEta εg N⟩ : ℂ) ∈ SL N (edgeL0 A₀ N) := by
    refine ⟨?_, hN.eta_gt, by change edgeEta εg N ≤ 10; linarith⟩
    change |y| ≤ 5
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  simp only [localLawEvent, Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨⟨y, edgeEta εg N⟩, hz, ?_⟩
  by_contra hcon
  have hlt := not_le.mp hcon
  have hctrl := edgeEvent_control_le hεg hεg' hN hya
  obtain ⟨-, hm, -⟩ := msc_edge_le hN1' hεg hεg' hya
  have hfin := edgeEvent_final_le hεg hN
  have hent := edgeEvent_entry_le x ⟨y, edgeEta εg N⟩ k l
  linarith

/-- Lemma 11.6. -/
theorem prodLaw_edgeBad_le {ϑ δm δp C₀ A₀ εg : ℝ} {N : ℕ} (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) (hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N) (M : Ensemble 𝕜 N)
    (hM : M.Assumptions ϑ δm δp C₀) :
    M.prodLaw (edgeBad εg N) ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) :=
  (measure_mono (edgeEvent_subset hεg hεg' hN)).trans (hIn.localLaw M hM)

/-- (11.b3:T): the tail of one entry beyond `t`. -/
theorem law_norm_gt_edgeT_le {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hϑ : 0 < ϑ) (hεg : 0 < εg)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) (ν : Measure 𝕜) [IsProbabilityMeasure ν]
    (hσ : ∫ y, ‖y‖ ^ 2 ∂ν ≤ C₀ / N)
    (htail : ∀ x : ℝ, 1 ≤ x → ν {y | x * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) < ‖y‖} ≤
      ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))) :
    ν {y | edgeT εg N < ‖y‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) := by
  have _ := hϑ
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hX : 1 ≤ (N : ℝ) ^ εg := Real.one_le_rpow hN1 hεg.le
  have hσle : Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) ≤ (N : ℝ) ^ εg * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) ≤ Real.sqrt (C₀ / N) := Real.sqrt_le_sqrt hσ
      _ = Real.sqrt C₀ / Real.sqrt N := Real.sqrt_div' _ hNpos.le
      _ ≤ (N : ℝ) ^ εg / Real.sqrt N :=
          div_le_div_of_nonneg_right hN.sqrt_le (Real.sqrt_nonneg _)
      _ = (N : ℝ) ^ εg * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_neg hNpos.le, div_eq_mul_inv]
  have hsub : {y : 𝕜 | edgeT εg N < ‖y‖} ⊆
      {y : 𝕜 | (N : ℝ) ^ εg * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) < ‖y‖} := by
    intro y hy
    have hy' : edgeT εg N < ‖y‖ := hy
    refine lt_of_le_of_lt ?_ hy'
    calc (N : ℝ) ^ εg * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν)
        ≤ (N : ℝ) ^ εg * ((N : ℝ) ^ εg * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hσle (Real.rpow_nonneg hNpos.le _)
      _ = edgeT εg N := by
          unfold edgeT
          rw [← mul_assoc, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          congr 1
          ring
  calc ν {y | edgeT εg N < ‖y‖}
      ≤ ν {y | (N : ℝ) ^ εg * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) < ‖y‖} := measure_mono hsub
    _ ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(((N : ℝ) ^ εg) ^ ϑ))) := htail _ hX
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_mul hNpos.le]
        exact hN.tail_le

/-- `(p₁, p₂)` is its own normal form. -/
private lemma edgeEvent_mk'_eq {N : ℕ} (p : Pair N) : Pair.mk' p.1.1 p.1.2 = p := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  simp [Pair.mk', h]

/-- The set of Lemma 11.15 (b) is contained in `Ω_edge ∪ {|x_p| > t}`. -/
private lemma edgeEvent_goodSet_subset {ϑ C₀ A₀ εg E₁ E₂ : ℝ} {N : ℕ}
    (hεg : 0 < εg) (hN : EdgeLarge ϑ C₀ A₀ εg N) (hE₁ : E₁ ∈ edgeWindow εg N)
    (hE₂ : E₂ ∈ edgeWindow εg N) (p : Pair N) :
    {x : Pair N → 𝕜 | toMatrixC (Function.update x p 0) ∉
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} ⊆
      edgeBad εg N ∪ {x : Pair N → 𝕜 | edgeT εg N < ‖x p‖} := by
  have _ := hεg
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hη : 0 < edgeEta εg N := Real.rpow_pos_of_pos hNpos _
  have hΨ : 0 < edgePsi εg N := by unfold edgePsi; positivity
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hnb, hnt⟩ := hcon
  have hnt' : ‖x p‖ ≤ edgeT εg N := not_lt.1 hnt
  refine hx ?_
  rw [toMatrixC_update_zero]
  refine mem_goodSet_entryRemoved (toMatrixC_isHermitian x) hη hΨ hN.psi_le
    (by linarith [hN.t_le]) ((norm_toMatrixC_pair_le x p).trans hnt') ?_
  intro y hy k _ l _
  by_contra hlt
  exact hnb ⟨y, ⟨le_trans hE₁.1 hy.1, le_trans hy.2 hE₂.2⟩, k, l, not_le.1 hlt⟩

/-- Lemma 11.15 (b). -/
theorem prodLaw_not_goodSet_le {ϑ δm δp C₀ A₀ εg E₁ E₂ : ℝ} {N : ℕ} (hϑ : 0 < ϑ)
    (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10) (hN : EdgeLarge ϑ C₀ A₀ εg N)
    (hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N) (hE : E₁ ≤ E₂) (hE₁ : E₁ ∈ edgeWindow εg N)
    (hE₂ : E₂ ∈ edgeWindow εg N) (M : Ensemble 𝕜 N) (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) :
    M.prodLaw {x | toMatrixC (Function.update x p 0) ∉
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2} ≤
      ENNReal.ofReal (2 * (N : ℝ) ^ (-20 : ℝ)) := by
  have _ := hE
  have hmeas : M.prodLaw {x : Pair N → 𝕜 | edgeT εg N < ‖x p‖} =
      M.law p {y : 𝕜 | edgeT εg N < ‖y‖} :=
    (measurePreserving_eval M.law p).measure_preimage
      (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet
  have h1 := prodLaw_edgeBad_le hεg hεg' hN hIn M hM
  have hσ : ∫ y, ‖y‖ ^ 2 ∂M.law p ≤ C₀ / N := by
    have h := hM.boundC p.1.1 p.1.2
    rwa [Ensemble.var, edgeEvent_mk'_eq] at h
  have h2 : M.law p {y : 𝕜 | edgeT εg N < ‖y‖} ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) :=
    law_norm_gt_edgeT_le hϑ hεg hN (M.law p) hσ (hM.subexp p)
  calc M.prodLaw {x | toMatrixC (Function.update x p 0) ∉
        goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2}
      ≤ M.prodLaw (edgeBad εg N ∪ {x : Pair N → 𝕜 | edgeT εg N < ‖x p‖}) :=
        measure_mono (edgeEvent_goodSet_subset hεg hN hE₁ hE₂ p)
    _ ≤ M.prodLaw (edgeBad εg N) + M.prodLaw {x : Pair N → 𝕜 | edgeT εg N < ‖x p‖} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) + ENNReal.ofReal ((N : ℝ) ^ (-20 : ℝ)) :=
        add_le_add h1 (hmeas ▸ h2)
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-20 : ℝ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Rigidity
