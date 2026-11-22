module

public import Rigidity.Ensemble.Basic
public import Rigidity.Flow.Ensembles
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.GoodSet
public import Rigidity.Semicircle.Density

@[expose] public section

/-!
# The good event along the flow and the second-moment bound

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

This file contains:
* Lemma 13.2: for `N` large and every ensemble `ν ∈ 𝓔_N(ϑ, δ₋, δ₊, C₀)`, the eigenvalue vector
  `λ(H_t)` lies outside the good set `Ξ` of (13.3) with probability at most `N^{-K}`, uniformly in
  `t ≥ 0`, and the same holds for `μ = λ_* 𝐆` (`t = ∞`); the rigidity bound of Theorem 2.2 for the
  rescaled ensemble `ν̃^t` is the hypothesis `RigidityBound`;
* Lemma 13.3: `𝔼|λ(H_t) - γ|² ≤ 7 D² / N` for every `t ≥ 0`, and the same for `μ`.

Indices of eigenvalues and classical locations are `0`-based: the paper's `x_j` and `γ_j` are
`x (j - 1)` and `gamma N (j - 1)`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The event of Theorem 2.2 for `L = A₀ log log N` -/

/-- The complement of the set `S` in the proof of Lemma 13.2, with `L = A₀ log log N`: some
`|y_j - γ_j|` is at least `(log N)^L m_j^{-1/3} N^{-2/3}`, or the counting function deviates from
`n_sc` by at least `(log N)^L / N` on `[-5, 5]`.  These are the two events of Theorem 2.2. -/
private def goodEvent_bad (A₀ : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  {y | ∃ k : Fin N, Real.log N ^ (A₀ * Real.log (Real.log N)) *
      (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |y k - gamma N k|} ∪
    {y | Real.log N ^ (A₀ * Real.log (Real.log N)) / N ≤
      ⨆ E : Set.Icc (-5 : ℝ) 5, |empCount y E - nsc E|}

private lemma goodEvent_measurableSet_bad (A₀ : ℝ) (N : ℕ) :
    MeasurableSet (goodEvent_bad A₀ N) := by
  refine MeasurableSet.union ?_ ?_
  · rw [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k =>
      measurableSet_le measurable_const (((measurable_pi_apply k).sub measurable_const).abs)
  · exact measurableSet_le measurable_const (measurable_iSup_empCount N 5)

/-! ### The deterministic transfer from `S` to `Ξ` -/

private lemma goodEvent_empCount_nonneg {N : ℕ} (x : Fin N → ℝ) (e : ℝ) : 0 ≤ empCount x e := by
  unfold empCount
  positivity

private lemma goodEvent_empCount_le_one {N : ℕ} (x : Fin N → ℝ) (e : ℝ) : empCount x e ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp [empCount]
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    unfold empCount
    rw [← div_eq_inv_mul, div_le_one hN]
    have := Finset.card_le_univ (Finset.univ.filter fun k : Fin N => x k ≤ e)
    rw [Fintype.card_fin] at this
    exact_mod_cast this

private lemma goodEvent_nsc_mem (E : ℝ) : 0 ≤ nsc E ∧ nsc E ≤ 1 := by
  obtain ⟨-, hmono, -, hlow, hhigh, -, -, -⟩ := nsc_props
  constructor
  · rcases le_total E (-2) with h | h
    · rw [hlow E h]
    · calc (0 : ℝ) = nsc (-2) := (hlow _ le_rfl).symm
        _ ≤ nsc E := hmono h
  · rcases le_total 2 E with h | h
    · rw [hhigh E h]
    · calc nsc E ≤ nsc 2 := hmono h
        _ = 1 := hhigh 2 le_rfl

private lemma goodEvent_abs_le_one {N : ℕ} (x : Fin N → ℝ) (e : ℝ) :
    |empCount x e - nsc e| ≤ 1 := by
  have h1 := goodEvent_empCount_nonneg x e
  have h2 := goodEvent_empCount_le_one x e
  have h3 := goodEvent_nsc_mem e
  rw [abs_le]
  constructor <;> linarith [h3.1, h3.2]

private lemma goodEvent_loglog_facts {N : ℕ} (hN : 16 ≤ N) {A₀ : ℝ}
    (hNs : 10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N)) :
    1 < Real.log N ∧ 0 < Real.log (Real.log N) ∧
      Real.log N ^ (A₀ * Real.log (Real.log N)) ≤ (N : ℝ) ^ (1 / 5 : ℝ) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : 1 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : 0 < Real.log (Real.log N) := Real.log_pos h1
  refine ⟨h1, h2, ?_⟩
  have h10 : Real.log 10 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
  rw [Real.log_mul (by norm_num) hNpos.ne'] at hNs
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  have e : Real.log (Real.log N) * (A₀ * Real.log (Real.log N)) =
      A₀ * Real.log (Real.log N) ^ 2 := by ring
  rw [e]
  nlinarith

/-- Lemma 13.2, deterministic transfer: if `κ x` avoids the event of Theorem 2.2 and
`κ⁻¹ - 1 ≤ 1/(2N)`, then `x ∈ Ξ`. -/
private lemma goodEvent_mem_of_not_bad {N : ℕ} (hN : 16 ≤ N) {A₀ : ℝ}
    (hNs : 10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N)) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hκ2 : κ⁻¹ - 1 ≤ 1 / (2 * N)) {x : Fin N → ℝ} (hx : Monotone x)
    (hy : κ • x ∉ goodEvent_bad A₀ N) : x ∈ flowGoodSet N (Dpar A₀ N) := by
  obtain ⟨hlog, -, hΛ⟩ := goodEvent_loglog_facts hN hNs
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set Λ : ℝ := Real.log N ^ (A₀ * Real.log (Real.log N)) with hΛdef
  have hΛ0 : 0 < Λ := Real.rpow_pos_of_pos (by linarith) _
  simp only [goodEvent_bad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_le] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hN23 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hΛ1 : Λ * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := by
    calc Λ * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
          gcongr
      _ = (N : ℝ) ^ (1 / 5 + -(2 / 3) : ℝ) := (Real.rpow_add hNpos _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hm1 : ∀ k : Fin N, (1 : ℝ) ≤ (rigWeight N k : ℝ) := fun k => by
    have : 1 ≤ rigWeight N k := le_min (by omega) (by have := k.2; omega)
    exact_mod_cast this
  have hmN : ∀ k : Fin N, (rigWeight N k : ℝ) ≤ N := fun k => by
    have : rigWeight N k ≤ N := (min_le_right _ _).trans (Nat.sub_le _ _)
    exact_mod_cast this
  have hmw : ∀ k : Fin N, (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos (hm1 k) (by norm_num)
  have hmw0 : ∀ k : Fin N, 0 < (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) := fun k =>
    Real.rpow_pos_of_pos (by linarith [hm1 k]) _
  -- `m^{-1/3} N^{-2/3} ≥ 1/N`
  have hP : ∀ k : Fin N, 1 / (N : ℝ) ≤
      (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := fun k => by
    have h1 : (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hm1 k]) (hmN k) (by norm_num)
    have h2 : (N : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) = 1 / (N : ℝ) := by
      rw [← Real.rpow_add hNpos, show -(1 / 3 : ℝ) + -(2 / 3) = -1 by norm_num,
        Real.rpow_neg_one, one_div]
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 hN23.le
  have hκinv0 : 0 ≤ κ⁻¹ - 1 := by
    rw [sub_nonneg]
    exact one_le_inv₀ hκ0 |>.mpr hκ1
  have hy1' : ∀ k, |κ * x k - gamma N k| <
      Λ * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := fun k => by
    simpa using hy1 k
  have hy3 : ∀ k, |κ * x k| ≤ 3 := fun k => by
    have h1 := hy1' k
    have h2 : Λ * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := by
      calc Λ * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))
          ≤ Λ * 1 * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by gcongr; exact hmw k
        _ ≤ 1 := by linarith
    have h3 := gamma_mem k
    have h4 : |gamma N k| ≤ 2 := abs_le.mpr ⟨by linarith [h3.1], h3.2⟩
    calc |κ * x k| = |(κ * x k - gamma N k) + gamma N k| := by ring_nf
      _ ≤ |κ * x k - gamma N k| + |gamma N k| := abs_add_le _ _
      _ ≤ 3 := by linarith
  refine ⟨hx, ?_, ?_⟩
  · -- the counting function
    have hne : Nonempty (Set.Icc (-4 : ℝ) 4) := ⟨⟨0, by norm_num, by norm_num⟩⟩
    refine ciSup_le fun e' => ?_
    obtain ⟨e, he⟩ := e'
    dsimp only
    have hκe : κ * e ∈ Set.Icc (-5 : ℝ) 5 := by
      constructor <;> nlinarith [he.1, he.2]
    have h1 : empCount x e = empCount (κ • x) (κ * e) := by
      rw [empCount_smul x hκ0, mul_div_cancel_left₀ _ hκ0.ne']
    have hbdd : BddAbove (Set.range fun E : Set.Icc (-5 : ℝ) 5 => |empCount (κ • x) E - nsc E|) :=
      ⟨1, by rintro _ ⟨E, rfl⟩; exact goodEvent_abs_le_one _ _⟩
    have h2 : |empCount (κ • x) (κ * e) - nsc (κ * e)| < Λ / N :=
      lt_of_le_of_lt (le_ciSup hbdd ⟨κ * e, hκe⟩) hy2
    have hκ3 : 1 - κ ≤ 1 / (2 * N) := by
      have : 1 - κ = κ * (κ⁻¹ - 1) := by field_simp
      rw [this]
      calc κ * (κ⁻¹ - 1) ≤ 1 * (κ⁻¹ - 1) := by gcongr
        _ ≤ 1 / (2 * N) := by linarith
    have h3 : |nsc (κ * e) - nsc e| ≤ 2 / N := by
      obtain ⟨-, -, hlip, -⟩ := nsc_props
      have h4 := hlip (κ * e) e
      have h5 : |κ * e - e| ≤ 4 * (1 / (2 * N)) := by
        have : κ * e - e = -((1 - κ) * e) := by ring
        rw [this, abs_neg, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - κ)]
        have : |e| ≤ 4 := abs_le.mpr he
        calc (1 - κ) * |e| ≤ (1 / (2 * N)) * 4 := by gcongr
          _ = 4 * (1 / (2 * N)) := by ring
      have h6 : |κ * e - e| / π ≤ 2 / N := by
        rw [div_le_iff₀ Real.pi_pos]
        have : 4 * (1 / (2 * (N : ℝ))) = 2 / N := by field_simp; ring
        have h7 : 2 / (N : ℝ) ≤ 2 / N * π := by
          have : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
          nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hNpos.le]
        linarith
      linarith
    have h4 : |empCount x e - nsc e| ≤
        |empCount (κ • x) (κ * e) - nsc (κ * e)| + |nsc (κ * e) - nsc e| := by
      rw [h1]
      calc |empCount (κ • x) (κ * e) - nsc e|
          = |(empCount (κ • x) (κ * e) - nsc (κ * e)) + (nsc (κ * e) - nsc e)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h5 : Dpar A₀ N / N = Λ / N + 2 / N := by
      rw [Dpar, add_div]
    rw [h5]
    linarith
  · intro k
    have h1 := hy1' k
    have hP' := hP k
    have h3 := gamma_mem k
    have h4 : |gamma N k| ≤ 2 := abs_le.mpr ⟨by linarith [h3.1], h3.2⟩
    have hx : x k - gamma N k = (κ * x k - gamma N k) + (κ⁻¹ - 1) * (κ * x k) := by
      field_simp
      ring
    have h5 : |x k - gamma N k| ≤ |κ * x k - gamma N k| + (κ⁻¹ - 1) * 3 := by
      rw [hx]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hκinv0]
      gcongr
      exact hy3 k
    have h6 : (κ⁻¹ - 1) * 3 ≤ 3 / (2 * N) := by
      calc (κ⁻¹ - 1) * 3 ≤ (1 / (2 * N)) * 3 := by gcongr
        _ = 3 / (2 * N) := by ring
    have h7 : 3 / (2 * (N : ℝ)) ≤ 2 * (1 / N) := by
      rw [div_le_iff₀ (by positivity)]
      field_simp
      linarith
    have e : Dpar A₀ N * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) =
        Λ * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) +
          2 * ((rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
      rw [Dpar]; ring
    rw [e]
    linarith

/-! ### The transfer in law -/

/-- `eig x` is the eigenvalue vector of `H(x)`. -/
private lemma goodEvent_eigVec_ofPair {N : ℕ} (x : Pair N → 𝕜) :
    eigVec (Herm.ofPair x) = eig x := by
  funext k
  have h : ∀ {A B : Matrix (Fin N) (Fin N) 𝕜} (hAB : A = B) (hA : A.IsHermitian)
      (hB : B.IsHermitian), eigAsc hA k = eigAsc hB k := by
    intro A B hAB hA hB
    subst hAB
    rfl
  exact h (Herm.toMatrix_ofPair x) _ _

/-- `H(c x) = c H(x)` for real `c`. -/
private lemma goodEvent_ofPair_smul {N : ℕ} (c : ℝ) (x : Pair N → 𝕜) :
    Herm.ofPair ((c : 𝕜) • x) = c • Herm.ofPair x := by
  apply Subtype.ext
  apply PiLp.ext
  intro q
  have h : Rigidity.toMatrix ((c : 𝕜) • x) q.1 q.2.1 = (c : 𝕜) * Rigidity.toMatrix x q.1 q.2.1 := by
    simp only [Rigidity.toMatrix, Matrix.of_apply]
    split_ifs
    · rfl
    · simp [star_mul', RCLike.star_def]
    · simp
  change _ = c * (Herm.ofPair x).coord q
  simp only [Herm.coord, Herm.ofPair, h]
  split_ifs <;> simp

private lemma goodEvent_hermLaw_smul {N : ℕ} (M : Ensemble 𝕜 N) (c : ℝ) :
    (M.smul c).hermLaw = M.hermLaw.map fun H => c • H := by
  have hm := Herm.measurable_ofPair (𝕜 := 𝕜) N
  have hs : Measurable fun x : Pair N → 𝕜 => (c : 𝕜) • x := measurable_const_smul _
  unfold Ensemble.hermLaw
  rw [Ensemble.prodLaw_smul, Measure.map_map hm hs, Measure.map_map (measurable_const_smul _) hm]
  congr 1
  funext x
  exact goodEvent_ofPair_smul c x

/-- The law of `c V` for `V ∼ 𝐆`. -/
private lemma goodEvent_gbe_hermLaw {N : ℕ} (c : ℝ) :
    ((gbeEnsemble 𝕜 N).smul c).hermLaw = (gaussH 𝕜 N).map fun H => c • H := by
  rw [goodEvent_hermLaw_smul, gbeEnsemble_hermLaw]

private lemma goodEvent_measurableSet_preimage_bad (A₀ : ℝ) (N : ℕ) :
    MeasurableSet (eigVec ⁻¹' goodEvent_bad A₀ N : Set (Herm 𝕜 N)) :=
  (continuous_eigVec N).measurable (goodEvent_measurableSet_bad A₀ N)

/-- If `κ H` avoids the event of Theorem 2.2 and `κ⁻¹ - 1 ≤ 1/(2N)`, then `λ(H) ∈ Ξ`, so the law
of `λ(H)` under `ρ` is bounded by the law of `H̃ = κ H` of the event. -/
private lemma goodEvent_law_le {N : ℕ} (hN : 16 ≤ N) {A₀ : ℝ}
    (hNs : 10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N)) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hκ2 : κ⁻¹ - 1 ≤ 1 / (2 * N)) {ρ : Measure (Herm 𝕜 N)} {M' : Ensemble 𝕜 N}
    (hρ : M'.hermLaw = ρ.map fun H => κ • H) :
    ρ (eigVec ⁻¹' (flowGoodSet N (Dpar A₀ N))ᶜ) ≤ M'.hermLaw (eigVec ⁻¹' goodEvent_bad A₀ N) := by
  have hsub : eigVec ⁻¹' (flowGoodSet N (Dpar A₀ N))ᶜ ⊆
      (fun H : Herm 𝕜 N => κ • H) ⁻¹' (eigVec ⁻¹' goodEvent_bad A₀ N) := by
    intro H hH
    by_contra hcon
    apply hH
    refine goodEvent_mem_of_not_bad hN hNs hκ0 hκ1 hκ2 (x := eigVec H)
      (eigAsc_monotone H.isHermitian) ?_
    rw [← eigVec_smul hκ0]
    exact hcon
  rw [hρ, Measure.map_apply (measurable_const_smul κ)
    (goodEvent_measurableSet_preimage_bad A₀ N)]
  exact measure_mono hsub

/-- The event of Theorem 2.2 for `L = A₀ log log N` has probability at most `N^{-K}`, for
every `N` beyond a threshold depending only on the constants of `RigidityBound`; the threshold
also makes `10 A₀ (log log N)² ≤ log (10 N)` and `16 ≤ N` hold. -/
private lemma goodEvent_exists_NK {ϑ' δm' δp' C₀' A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 ϑ' δm' δp' C₀' A₀ CR cR φ N₀) (K : ℝ) :
    ∃ NK : ℕ, 16 ≤ NK ∧
      (∀ N : ℕ, NK ≤ N → 10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N)) ∧
      ∀ N : ℕ, NK ≤ N → ∀ M' : Ensemble 𝕜 N, M'.Assumptions ϑ' δm' δp' C₀' →
        M'.hermLaw (eigVec ⁻¹' goodEvent_bad A₀ N) ≤ ENNReal.ofReal ((N : ℝ) ^ (-K)) := by
  obtain ⟨hA, hCR, hcR, hφ, -, hR'⟩ := hR
  have hA0 : 0 < A₀ := by linarith
  obtain ⟨Ns, hNs⟩ := exists_Nstar A₀ φ hA0 hφ
  have hev : ∀ᶠ N : ℕ in atTop, K + max 0 (Real.log (2 * CR)) ≤ cR * Real.log N := by
    have h : Tendsto (fun N : ℕ => cR * Real.log N) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hcR
    exact h.eventually_ge_atTop _
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp hev
  refine ⟨max (max N₀ 16) (max Ns Nc), le_trans (le_max_right _ _) (le_max_left _ _),
    fun N hN => (hNs N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)).1, ?_⟩
  intro N hN M' hM'
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN16 : 16 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNs' := hNs N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have hNc' := hNc N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hlog, hll, -⟩ := goodEvent_loglog_facts hN16 hNs'.1
  have hL : LRange A₀ N (A₀ * Real.log (Real.log N)) := by
    refine ⟨le_rfl, ?_⟩
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hNs'.1]
  obtain ⟨h1, h2⟩ := hR' N hN0 M' hM' _ hL
  rw [Ensemble.hermLaw, Measure.map_apply (Herm.measurable_ofPair N)
    (goodEvent_measurableSet_preimage_bad A₀ N)]
  have hset : (Herm.ofPair ⁻¹' (eigVec ⁻¹' goodEvent_bad A₀ N) : Set (Pair N → 𝕜)) =
      {x | ∃ k : Fin N, Real.log N ^ (A₀ * Real.log (Real.log N)) * (rigWeight N k : ℝ) ^
          (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |eig x k - gamma N k|} ∪
        {x | Real.log N ^ (A₀ * Real.log (Real.log N)) / N ≤
          ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} := by
    ext x
    simp only [Set.mem_preimage, goodEvent_bad, Set.mem_union, Set.mem_ofPred_eq,
      goodEvent_eigVec_ofPair]
    rfl
  rw [hset]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set ℓ := Real.log N with hℓ
  have hφL : ℓ ^ 2 ≤ ℓ ^ (φ * (A₀ * Real.log ℓ)) := by
    have : (2 : ℝ) ≤ φ * (A₀ * Real.log ℓ) := by
      have := hNs'.2
      linarith
    calc ℓ ^ 2 = ℓ ^ (2 : ℝ) := by norm_cast
      _ ≤ ℓ ^ (φ * (A₀ * Real.log ℓ)) := Real.rpow_le_rpow_of_exponent_le hlog.le this
  have hE : Real.exp (-cR * ℓ ^ (φ * (A₀ * Real.log ℓ))) ≤ Real.exp (-cR * ℓ ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2CR : 0 < 2 * CR := by positivity
  have hm : Real.log (2 * CR) - cR * ℓ ^ 2 ≤ -K * ℓ := by
    have h3 : (K + max 0 (Real.log (2 * CR))) * ℓ ≤ cR * ℓ ^ 2 := by nlinarith
    have h4 : max 0 (Real.log (2 * CR)) ≤ max 0 (Real.log (2 * CR)) * ℓ := by
      nlinarith [le_max_left 0 (Real.log (2 * CR))]
    have h5 := le_max_right 0 (Real.log (2 * CR))
    nlinarith
  calc CR * Real.exp (-cR * ℓ ^ (φ * (A₀ * Real.log ℓ))) +
        CR * Real.exp (-cR * ℓ ^ (φ * (A₀ * Real.log ℓ)))
      = 2 * CR * Real.exp (-cR * ℓ ^ (φ * (A₀ * Real.log ℓ))) := by ring
    _ ≤ 2 * CR * Real.exp (-cR * ℓ ^ 2) := by gcongr
    _ = Real.exp (Real.log (2 * CR) - cR * ℓ ^ 2) := by
        rw [Real.exp_sub, Real.exp_log h2CR, neg_mul, Real.exp_neg]
        field_simp
    _ ≤ Real.exp (-K * ℓ) := Real.exp_le_exp.mpr hm
    _ = (N : ℝ) ^ (-K) := by
        rw [Real.rpow_def_of_pos hNpos, hℓ]
        congr 1
        ring

/-- `κ = (1 + r)^{-1/2}` with `0 ≤ r ≤ 1/N`: `0 < κ ≤ 1` and `κ⁻¹ - 1 ≤ 1/(2N)`. -/
private lemma goodEvent_rpow_bounds {r : ℝ} {N : ℕ} (hN : 0 < N) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1 / N) :
    0 < (1 + r) ^ (-(1 / 2 : ℝ)) ∧ (1 + r) ^ (-(1 / 2 : ℝ)) ≤ 1 ∧
      ((1 + r) ^ (-(1 / 2 : ℝ)))⁻¹ - 1 ≤ 1 / (2 * N) := by
  have hpos : 0 < 1 + r := by linarith
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : ((1 + r) ^ (-(1 / 2 : ℝ)))⁻¹ = Real.sqrt (1 + r) := by
    rw [Real.rpow_neg hpos.le, inv_inv, Real.sqrt_eq_rpow]
  refine ⟨Real.rpow_pos_of_pos hpos _,
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num), ?_⟩
  rw [h1]
  have h3 : Real.sqrt (1 + r) ≤ 1 + r / 2 := by
    calc Real.sqrt (1 + r) ≤ Real.sqrt ((1 + r / 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg r])
      _ = 1 + r / 2 := Real.sqrt_sq (by linarith)
  have h2 : r / 2 ≤ 1 / (2 * N) := by
    have e : (1 : ℝ) / (2 * N) = 1 / N / 2 := by ring
    rw [e]
    linarith
  linarith

/-- `1 ≤ β ≤ 2`. -/
private lemma goodEvent_betaF_mem : 1 ≤ betaF 𝕜 ∧ betaF 𝕜 ≤ 2 := by
  refine ⟨?_, ?_⟩
  · unfold betaF
    exact_mod_cast Module.finrank_pos
  · unfold betaF
    exact_mod_cast RCLike.finrank_le_two 𝕜

/-- `0 ≤ (2 - β)/(βN) ≤ 1/N`. -/
private lemma goodEvent_rN_mem {N : ℕ} (hN : 0 < N) :
    0 ≤ (2 - betaF 𝕜) / (betaF 𝕜 * N) ∧ (2 - betaF 𝕜) / (betaF 𝕜 * N) ≤ 1 / N := by
  obtain ⟨h1, h2⟩ := goodEvent_betaF_mem (𝕜 := 𝕜)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨div_nonneg (by linarith) (mul_nonneg (by linarith) hN'.le), ?_⟩
  rw [div_le_div_iff₀ (by positivity) hN']
  nlinarith

/-- Lemma 13.2 (good event, uniformly in `t`). -/
theorem flowGoodSet_compl_le {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 0 < C₀) {A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀)
      A₀ CR cR φ N₀) (K : ℝ) (hK : 0 < K) :
    ∃ NK : ℕ, ∀ N : ℕ, NK ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      (∀ t : ℝ, 0 ≤ t → M.eigLaw t (flowGoodSet N (Dpar A₀ N))ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-K))) ∧
        gbeLaw 𝕜 N (flowGoodSet N (Dpar A₀ N))ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-K)) := by
  have _ := hK
  obtain ⟨NK, hNK16, hNs, hbad⟩ := goodEvent_exists_NK hR K
  refine ⟨NK, fun N hN M hM => ⟨fun t ht => ?_, ?_⟩⟩
  · have hN16 : 16 ≤ N := hNK16.trans hN
    obtain ⟨hk1, hk2, -, hk4⟩ := kappaT_bounds (𝕜 := 𝕜) (N := N) (by omega) ht
    have hk0 : 0 < Ensemble.kappaT 𝕜 N t :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) hk2
    have hM' := Ensemble.tildeFlow_assumptions (by omega) hϑ hδm hδp hC₀ hM ht
    have hlaw := goodEvent_law_le hN16 (hNs N hN) hk0 hk1 hk4 (Ensemble.tildeFlow_hermLaw M t)
    calc M.eigLaw t (flowGoodSet N (Dpar A₀ N))ᶜ
        = M.flowLaw t (eigVec ⁻¹' (flowGoodSet N (Dpar A₀ N))ᶜ) :=
          Measure.map_apply (continuous_eigVec N).measurable
            (measurableSet_flowGoodSet N _).compl
      _ ≤ _ := hlaw
      _ ≤ _ := hbad N hN _ hM'
  · have hN16 : 16 ≤ N := hNK16.trans hN
    obtain ⟨hr0, hr1⟩ := goodEvent_rN_mem (𝕜 := 𝕜) (N := N) (by omega)
    obtain ⟨hk0, hk1, hk2⟩ := goodEvent_rpow_bounds (by omega) hr0 hr1
    have hM' := gbeTilde_assumptions (𝕜 := 𝕜) (N := N) (by omega) hϑ hδm hδp hC₀
    have hlaw := goodEvent_law_le hN16 (hNs N hN) hk0 hk1 hk2
      (goodEvent_gbe_hermLaw (𝕜 := 𝕜) (N := N) _)
    calc gbeLaw 𝕜 N (flowGoodSet N (Dpar A₀ N))ᶜ
        = gaussH 𝕜 N (eigVec ⁻¹' (flowGoodSet N (Dpar A₀ N))ᶜ) :=
          Measure.map_apply (continuous_eigVec N).measurable
            (measurableSet_flowGoodSet N _).compl
      _ ≤ _ := hlaw
      _ ≤ _ := hbad N hN _ hM'

/-! ### The sum of `m_j^{-2/3}` -/

/-- `∑_{j=1}^n j^{-2/3} ≤ 3 n^{1/3}`. -/
private lemma goodEvent_sum_pow_le (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ (-(2 / 3 : ℝ)) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : ((n : ℝ) + 1) ^ (-(2 / 3 : ℝ)) ≤
        3 * (((n : ℝ) + 1) ^ (1 / 3 : ℝ) - (n : ℝ) ^ (1 / 3 : ℝ)) := by
      set a := ((n : ℝ) + 1) ^ (1 / 3 : ℝ) with ha
      set b := (n : ℝ) ^ (1 / 3 : ℝ) with hb
      have ha0 : 0 < a := Real.rpow_pos_of_pos (by linarith) _
      have hb0 : 0 ≤ b := Real.rpow_nonneg hn _
      have ha3 : a ^ 3 = (n : ℝ) + 1 := by
        rw [ha, ← Real.rpow_mul_natCast (by linarith)]
        norm_num
      have hb3 : b ^ 3 = n := by
        rw [hb, ← Real.rpow_mul_natCast hn]
        norm_num
      have hba : b ≤ a := Real.rpow_le_rpow hn (by linarith) (by norm_num)
      have e : ((n : ℝ) + 1) ^ (-(2 / 3 : ℝ)) = (a ^ 2)⁻¹ := by
        rw [ha, ← Real.rpow_mul_natCast (by linarith), ← Real.rpow_neg (by linarith)]
        norm_num
      rw [e, inv_eq_one_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg (a - b)) (by positivity : 0 ≤ 2 * a + b)]
    push_cast
    linarith

/-- `∑_k m_k^{-2/3} ≤ 6 N^{1/3}` for the weights `m_k = min(k+1, N-k)`. -/
private lemma goodEvent_sum_rigWeight_le (N : ℕ) :
    ∑ k : Fin N, (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 6 * (N : ℝ) ^ (1 / 3 : ℝ) := by
  have h1 : ∀ k : Fin N, (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) ≤
      ((k.val : ℝ) + 1) ^ (-(2 / 3 : ℝ)) + ((N - k.val : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := fun k => by
    have p1 : 0 ≤ ((k.val : ℝ) + 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have p2 : 0 ≤ ((N - k.val : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by positivity) _
    rcases min_choice (k.val + 1) (N - k.val) with h | h
    · have : (rigWeight N k : ℝ) = (k.val : ℝ) + 1 := by
        unfold rigWeight
        rw [h]
        push_cast
        ring
      rw [this]
      linarith
    · have : (rigWeight N k : ℝ) = ((N - k.val : ℕ) : ℝ) := by
        unfold rigWeight
        rw [h]
      rw [this]
      linarith
  have ha : ∑ k : Fin N, ((k.val : ℝ) + 1) ^ (-(2 / 3 : ℝ)) ≤ 3 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j : ℝ) + 1) ^ (-(2 / 3 : ℝ))) N]
    exact goodEvent_sum_pow_le N
  have hb : ∑ k : Fin N, ((N - k.val : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 3 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((N - j : ℕ) : ℝ) ^ (-(2 / 3 : ℝ))) N]
    have : ∑ j ∈ Finset.range N, ((N - j : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) =
        ∑ j ∈ Finset.range N, (((N - 1 - j : ℕ) : ℝ) + 1) ^ (-(2 / 3 : ℝ)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      congr 1
      rw [← Nat.cast_succ]
      congr 1
      omega
    rw [this, Finset.sum_range_reflect (fun j : ℕ => ((j : ℝ) + 1) ^ (-(2 / 3 : ℝ))) N]
    exact goodEvent_sum_pow_le N
  calc ∑ k : Fin N, (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ))
      ≤ ∑ k : Fin N, (((k.val : ℝ) + 1) ^ (-(2 / 3 : ℝ)) +
          ((N - k.val : ℕ) : ℝ) ^ (-(2 / 3 : ℝ))) := Finset.sum_le_sum fun k _ => h1 k
    _ = ∑ k : Fin N, ((k.val : ℝ) + 1) ^ (-(2 / 3 : ℝ)) +
          ∑ k : Fin N, ((N - k.val : ℕ) : ℝ) ^ (-(2 / 3 : ℝ)) := Finset.sum_add_distrib
    _ ≤ 3 * (N : ℝ) ^ (1 / 3 : ℝ) + 3 * (N : ℝ) ^ (1 / 3 : ℝ) := add_le_add ha hb
    _ = 6 * (N : ℝ) ^ (1 / 3 : ℝ) := by ring

/-- On `Ξ`: `|x - γ|² ≤ 6 D² / N`. -/
private lemma goodEvent_sum_sq_le_of_mem {N : ℕ} (hN : 0 < N) {D : ℝ}
    {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) :
    ∑ k, (x k - gamma N k) ^ 2 ≤ 6 * D ^ 2 / N := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : ∀ k : Fin N, (x k - gamma N k) ^ 2 ≤
      D ^ 2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) * (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) := fun k => by
    have h := hx.2.2 k
    calc (x k - gamma N k) ^ 2 = |x k - gamma N k| ^ 2 := (sq_abs _).symm
      _ ≤ (D * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = D ^ 2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) * (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          have e1 : ((rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 =
              (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) := by
            rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
            norm_num
          have e2 : ((N : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = (N : ℝ) ^ (-(4 / 3 : ℝ)) := by
            rw [← Real.rpow_mul_natCast hNpos.le]
            norm_num
          calc _ = D ^ 2 * ((rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 *
                ((N : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 := by ring
            _ = _ := by rw [e1, e2]; ring
  have h2 : (N : ℝ) ^ (-(4 / 3 : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ) = 1 / N := by
    rw [← Real.rpow_add hNpos, show -(4 / 3 : ℝ) + 1 / 3 = -1 by norm_num, Real.rpow_neg_one,
      one_div]
  calc ∑ k, (x k - gamma N k) ^ 2
      ≤ ∑ k : Fin N, D ^ 2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) * (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) :=
        Finset.sum_le_sum fun k _ => h1 k
    _ = D ^ 2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) * ∑ k : Fin N, (rigWeight N k : ℝ) ^ (-(2 / 3 : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ D ^ 2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) * (6 * (N : ℝ) ^ (1 / 3 : ℝ)) := by
        gcongr
        exact goodEvent_sum_rigWeight_le N
    _ = 6 * D ^ 2 * ((N : ℝ) ^ (-(4 / 3 : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ)) := by ring
    _ = 6 * D ^ 2 / N := by rw [h2]; ring

/-! ### Off `Ξ` -/

/-- `|λ(H) - γ|² ≤ 3 |κ H|² + 8 N` for `κ⁻² ≤ 3/2`. -/
private lemma goodEvent_sum_sq_le_Y {N : ℕ} (hN : 16 ≤ N) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ2 : κ⁻¹ - 1 ≤ 1 / (2 * N)) (H : Herm 𝕜 N) :
    ∑ k, (eigVec H k - gamma N k) ^ 2 ≤ 3 * ‖κ • H‖ ^ 2 + 8 * N := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : ∑ k, eigVec H k ^ 2 = κ⁻¹ ^ 2 * ‖κ • H‖ ^ 2 := by
    rw [← sum_sq_eigVec (κ • H), eigVec_smul hκ0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hκinv : κ⁻¹ ^ 2 ≤ 3 / 2 := by
    have h32 : 1 / (2 * (N : ℝ)) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have : κ⁻¹ ≤ 33 / 32 := by linarith
    have h0 : 0 ≤ κ⁻¹ := (inv_pos.mpr hκ0).le
    nlinarith
  have h2 : ∑ k, gamma N k ^ 2 ≤ 4 * N := by
    calc ∑ k, gamma N k ^ 2 ≤ ∑ _k : Fin N, (4 : ℝ) := Finset.sum_le_sum fun k _ => by
          have := gamma_mem k
          nlinarith [this.1, this.2]
      _ = 4 * N := by simp; ring
  calc ∑ k, (eigVec H k - gamma N k) ^ 2
      ≤ ∑ k, (2 * eigVec H k ^ 2 + 2 * gamma N k ^ 2) :=
        Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (eigVec H k + gamma N k)]
    _ = 2 * ∑ k, eigVec H k ^ 2 + 2 * ∑ k, gamma N k ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 3 * ‖κ • H‖ ^ 2 + 8 * N := by
        rw [h1]
        have : 0 ≤ ‖κ • H‖ ^ 2 := by positivity
        nlinarith

/-- `|h_ij| ≤ |x_{min(i,j), max(i,j)}|` for the entries of `H(x)`. -/
private lemma goodEvent_norm_toMatrix_le {N : ℕ} (x : Pair N → 𝕜) (i j : Fin N) :
    ‖Rigidity.toMatrix x i j‖ ≤ ‖x (Pair.mk' i j)‖ := by
  simp only [Rigidity.toMatrix, Matrix.of_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_star]
  · rw [RCLike.norm_ofReal]
    exact RCLike.abs_re_le_norm _

/-- `|H(x)|² ≤ ∑_{i,j} |x_{min(i,j), max(i,j)}|²`. -/
private lemma goodEvent_norm_sq_ofPair_le {N : ℕ} (x : Pair N → 𝕜) :
    ‖Herm.ofPair x‖ ^ 2 ≤ ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2 := by
  rw [Herm.norm_sq_eq, Herm.toMatrix_ofPair, Fintype.sum_prod_type]
  gcongr with i _ j _
  exact goodEvent_norm_toMatrix_le x i j

/-- The second moment of `3 |H(x)|² + 8 N` under an ensemble in `𝓔_N(ϑ, ·, ·, C₀)` is at most
`(18 m C₀² + 128) N²`, where `m = (4 C_ϑ)^{4/ϑ}` is the constant of the fourth-moment bound of
the entries (Lemma 4.1, (RA6)). -/
private lemma goodEvent_lintegral_second_moment {N : ℕ} (hN : 0 < N) {ϑ δm δp C₀ : ℝ}
    (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {M : Ensemble 𝕜 N} (hM : M.Assumptions ϑ δm δp C₀) :
    ∫⁻ x, ENNReal.ofReal ((3 * ‖Herm.ofPair x‖ ^ 2 + 8 * N) ^ 2) ∂M.prodLaw ≤
      ENNReal.ofReal
        ((18 * (cTheta ϑ⁻¹ * 4) ^ (ϑ⁻¹ * 4) * C₀ ^ 2 + 128) * (N : ℝ) ^ 2) := by
  set m : ℝ := (cTheta ϑ⁻¹ * 4) ^ (ϑ⁻¹ * 4) with hm
  have hm0 : 0 ≤ m := Real.rpow_nonneg (by unfold cTheta; positivity) _
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hent : ∀ i j : Fin N, Integrable (fun x : Pair N → 𝕜 => ‖x (Pair.mk' i j)‖ ^ 4) M.prodLaw ∧
      ∫ x, ‖x (Pair.mk' i j)‖ ^ 4 ∂M.prodLaw ≤ m * (C₀ / N) ^ 2 := by
    intro i j
    have hint := Ensemble.Assumptions.integrable_norm_pow M hM hϑ (Pair.mk' i j) 4
    refine ⟨integrable_comp_eval (μ := M.law) (f := fun y : 𝕜 => ‖y‖ ^ 4) hint, ?_⟩
    unfold Ensemble.prodLaw
    rw [integral_comp_eval (μ := M.law) (f := fun y : 𝕜 => ‖y‖ ^ 4) (by fun_prop)]
    have hmom := Ensemble.Assumptions.moment_le hM hϑ hϑ1 (Pair.mk' i j) (q := 4) (by norm_num)
    have e1 : ∫ y, ‖y‖ ^ 4 ∂M.law (Pair.mk' i j) = ∫ y, ‖y‖ ^ (4 : ℝ) ∂M.law (Pair.mk' i j) := by
      congr 1
      funext y
      norm_cast
    rw [e1]
    refine hmom.trans ?_
    have hv0 : 0 ≤ M.varPair (Pair.mk' i j) := integral_nonneg fun y => by positivity
    have e2 : Real.sqrt (M.varPair (Pair.mk' i j)) ^ (4 : ℝ) = M.varPair (Pair.mk' i j) ^ 2 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hv0]
    rw [e2]
    have := hM.boundC i j
    have hvar : M.var i j = M.varPair (Pair.mk' i j) := rfl
    rw [hvar] at this
    gcongr
  have hpt : ∀ x : Pair N → 𝕜, (3 * ‖Herm.ofPair x‖ ^ 2 + 8 * N) ^ 2 ≤
      18 * (N : ℝ) ^ 2 * ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4 +
        128 * (N : ℝ) ^ 2 := by
    intro x
    set h := ‖Herm.ofPair x‖ ^ 2 with hh
    have hh0 : 0 ≤ h := by positivity
    have hs := goodEvent_norm_sq_ofPair_le x
    have hcs : (∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2) ^ 2 ≤
        (N : ℝ) ^ 2 * ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N × Fin N)))
        (f := fun ij => ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2)
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at this
      have e : ∀ ij : Fin N × Fin N, (‖x (Pair.mk' ij.1 ij.2)‖ ^ 2) ^ 2 =
          ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4 := fun ij => by ring
      simp only [e] at this
      linarith [this, show (N : ℝ) * N = (N : ℝ) ^ 2 by ring]
    have hh2 : h ^ 2 ≤ (∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hh0 hs 2
    nlinarith [sq_nonneg (3 * h - 8 * N)]
  set g : (Pair N → 𝕜) → ℝ := fun x =>
    18 * (N : ℝ) ^ 2 * ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4 +
      128 * (N : ℝ) ^ 2 with hg
  have hsumi : Integrable (fun x : Pair N → 𝕜 =>
      ∑ ij : Fin N × Fin N, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4) M.prodLaw :=
    integrable_finsetSum _ fun ij _ => (hent ij.1 ij.2).1
  have hgi : Integrable g M.prodLaw := (hsumi.const_mul _).add (integrable_const _)
  have hgint : ∫ x, g x ∂M.prodLaw ≤ (18 * m * C₀ ^ 2 + 128) * (N : ℝ) ^ 2 := by
    simp only [hg]
    rw [integral_add (hsumi.const_mul _) (integrable_const _), integral_const_mul,
      integral_finsetSum _ fun ij _ => (hent ij.1 ij.2).1]
    simp only [integral_const, probReal_univ, one_smul]
    have hsum : ∑ ij : Fin N × Fin N, ∫ x, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4 ∂M.prodLaw ≤
        (N : ℝ) ^ 2 * (m * (C₀ / N) ^ 2) := by
      calc _ ≤ ∑ _ij : Fin N × Fin N, m * (C₀ / N) ^ 2 :=
            Finset.sum_le_sum fun ij _ => (hent ij.1 ij.2).2
        _ = (N : ℝ) ^ 2 * (m * (C₀ / N) ^ 2) := by
            simp [Fintype.card_prod, sq]
    have e : (N : ℝ) ^ 2 * (m * (C₀ / N) ^ 2) = m * C₀ ^ 2 := by
      field_simp
    calc 18 * (N : ℝ) ^ 2 * ∑ ij : Fin N × Fin N, ∫ x, ‖x (Pair.mk' ij.1 ij.2)‖ ^ 4 ∂M.prodLaw +
          128 * (N : ℝ) ^ 2
        ≤ 18 * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 * (m * (C₀ / N) ^ 2)) + 128 * (N : ℝ) ^ 2 := by
          gcongr
      _ = (18 * m * C₀ ^ 2 + 128) * (N : ℝ) ^ 2 := by rw [e]; ring
  calc ∫⁻ x, ENNReal.ofReal ((3 * ‖Herm.ofPair x‖ ^ 2 + 8 * N) ^ 2) ∂M.prodLaw
      ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂M.prodLaw :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (∫ x, g x ∂M.prodLaw) :=
        (ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun x => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hgint

/-! ### Lemma 13.3 -/

/-- The bound of Lemma 13.3 for the law `ρ` of `H_t` (or `V`), given that `κ H` has the law of an
ensemble in `𝓔_N(ϑ', ·, ·, C₀')` which avoids the event of Theorem 2.2 with probability at least
`1 - N^{-6}`. -/
private lemma goodEvent_lintegral_le {N : ℕ} {A₀ : ℝ} (hN : 16 ≤ N)
    (hNs : 10 * A₀ * Real.log (Real.log N) ^ 2 ≤ Real.log (10 * N)) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hκ2 : κ⁻¹ - 1 ≤ 1 / (2 * N)) {ρ : Measure (Herm 𝕜 N)} {M' : Ensemble 𝕜 N}
    (hρ : M'.hermLaw = ρ.map fun H => κ • H) {ϑ' δm' δp' C₀' : ℝ} (hϑ' : 0 < ϑ')
    (hϑ'1 : ϑ' ≤ 1) (hM' : M'.Assumptions ϑ' δm' δp' C₀')
    (hbad : M'.hermLaw (eigVec ⁻¹' goodEvent_bad A₀ N) ≤ ENNReal.ofReal ((N : ℝ) ^ (-(6 : ℝ))))
    (hC : 18 * (cTheta ϑ'⁻¹ * 4) ^ (ϑ'⁻¹ * 4) * C₀' ^ 2 + 128 + 1 ≤ N) :
    ∫⁻ x, ENNReal.ofReal (∑ k, (x k - gamma N k) ^ 2) ∂ρ.map eigVec ≤
      ENNReal.ofReal (7 * Dpar A₀ N ^ 2 / N) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set C₁ : ℝ := 18 * (cTheta ϑ'⁻¹ * 4) ^ (ϑ'⁻¹ * 4) * C₀' ^ 2 + 128 with hC₁
  set D := Dpar A₀ N with hD
  have hD2 : 2 ≤ D := by
    have : 0 ≤ Real.log N ^ (A₀ * Real.log (Real.log N)) :=
      Real.rpow_nonneg (Real.log_natCast_nonneg N) _
    rw [hD, Dpar]
    linarith
  have : IsProbabilityMeasure M'.hermLaw := by
    unfold Ensemble.hermLaw
    exact (Measure.isProbabilityMeasure_map_iff (Herm.measurable_ofPair N).aemeasurable).2
      inferInstance
  have hρ1 : ρ Set.univ = 1 := by
    have h := congrArg (fun μ : Measure (Herm 𝕜 N) => μ Set.univ) hρ
    simp only [measure_univ] at h
    rw [Measure.map_apply (measurable_const_smul κ) MeasurableSet.univ, Set.preimage_univ] at h
    exact h.symm
  set U : Herm 𝕜 N → ℝ := fun H => 3 * ‖H‖ ^ 2 + 8 * N with hU
  set B : Set (Herm 𝕜 N) := eigVec ⁻¹' goodEvent_bad A₀ N with hB
  have hBm : MeasurableSet B := goodEvent_measurableSet_preimage_bad A₀ N
  have hU0 : ∀ H, 0 ≤ U H := fun H => by simp only [hU]; positivity
  set Ψ : Herm 𝕜 N → ℝ≥0∞ := B.indicator fun H => ENNReal.ofReal (U H) with hΨ
  have hUm : Measurable U := by simp only [hU]; fun_prop
  have hΨm : Measurable Ψ := (hUm.ennreal_ofReal).indicator hBm
  have hpt : ∀ H : Herm 𝕜 N, ENNReal.ofReal (∑ k, (eigVec H k - gamma N k) ^ 2) ≤
      ENNReal.ofReal (6 * D ^ 2 / N) + Ψ (κ • H) := by
    intro H
    by_cases hH : κ • H ∈ B
    · refine le_trans ?_ le_add_self
      rw [hΨ, Set.indicator_of_mem hH]
      exact ENNReal.ofReal_le_ofReal (goodEvent_sum_sq_le_Y hN hκ0 hκ2 H)
    · have hmem : eigVec H ∈ flowGoodSet N D :=
        goodEvent_mem_of_not_bad hN hNs hκ0 hκ1 hκ2 (eigAsc_monotone H.isHermitian)
          (by rw [← eigVec_smul hκ0]; exact hH)
      exact le_trans (ENNReal.ofReal_le_ofReal
        (goodEvent_sum_sq_le_of_mem (by omega) hmem)) le_self_add
  -- the AM-GM bound `U ≤ (s/2) U² + 1/(2s)` on the event
  set s : ℝ := ((N : ℝ) ^ 4)⁻¹ with hs
  have hs0 : 0 < s := by positivity
  have hm0 : 0 ≤ (cTheta ϑ'⁻¹ * 4) ^ (ϑ'⁻¹ * 4) :=
    Real.rpow_nonneg (by unfold cTheta; positivity) _
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hs2 : 0 ≤ s / 2 := by positivity
  have hs3 : 0 ≤ 1 / (2 * s) := by positivity
  have hN60 : 0 ≤ (N : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg hNpos.le _
  have hD4 : 4 ≤ D ^ 2 := by nlinarith
  have hpt2 : ∀ H : Herm 𝕜 N, Ψ H ≤ ENNReal.ofReal (s / 2) * ENNReal.ofReal (U H ^ 2) +
      B.indicator (fun _ => ENNReal.ofReal (1 / (2 * s))) H := by
    intro H
    by_cases hH : H ∈ B
    · rw [hΨ, Set.indicator_of_mem hH, Set.indicator_of_mem hH,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [← sub_nonneg]
      have : s / 2 * U H ^ 2 + 1 / (2 * s) - U H = (s * U H - 1) ^ 2 / (2 * s) := by
        field_simp
        ring
      rw [this]
      positivity
    · rw [hΨ, Set.indicator_of_notMem hH]
      exact zero_le
  have hmom := goodEvent_lintegral_second_moment (by omega : 0 < N) hϑ' hϑ'1 hM'
  have hfm : Measurable fun H : Herm 𝕜 N => ENNReal.ofReal (U H ^ 2) := by
    have : Measurable fun H : Herm 𝕜 N => U H ^ 2 := hUm.pow_const 2
    exact this.ennreal_ofReal
  have hΨint : ∫⁻ H, Ψ H ∂M'.hermLaw ≤
      ENNReal.ofReal (s / 2) * ENNReal.ofReal (C₁ * (N : ℝ) ^ 2) +
        ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal ((N : ℝ) ^ (-(6 : ℝ))) := by
    calc ∫⁻ H, Ψ H ∂M'.hermLaw
        ≤ ∫⁻ H, (ENNReal.ofReal (s / 2) * ENNReal.ofReal (U H ^ 2) +
            B.indicator (fun _ => ENNReal.ofReal (1 / (2 * s))) H) ∂M'.hermLaw :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal (s / 2) * ∫⁻ H, ENNReal.ofReal (U H ^ 2) ∂M'.hermLaw +
            ENNReal.ofReal (1 / (2 * s)) * M'.hermLaw B := by
          rw [lintegral_add_left (hfm.const_mul _), lintegral_const_mul _ hfm,
            lintegral_indicator_const hBm]
      _ ≤ ENNReal.ofReal (s / 2) * ENNReal.ofReal (C₁ * (N : ℝ) ^ 2) +
            ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal ((N : ℝ) ^ (-(6 : ℝ))) := by
          gcongr
          · rw [Ensemble.hermLaw, lintegral_map hfm (Herm.measurable_ofPair N)]
            exact hmom
  have hN6 : (N : ℝ) ^ (-(6 : ℝ)) = ((N : ℝ) ^ 6)⁻¹ := by
    rw [Real.rpow_neg hNpos.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfm2 : Measurable fun x : Fin N → ℝ => ENNReal.ofReal (∑ k, (x k - gamma N k) ^ 2) := by
    fun_prop
  rw [lintegral_map hfm2 (continuous_eigVec N).measurable]
  calc ∫⁻ H, ENNReal.ofReal (∑ k, (eigVec H k - gamma N k) ^ 2) ∂ρ
      ≤ ∫⁻ H, (ENNReal.ofReal (6 * D ^ 2 / N) + Ψ (κ • H)) ∂ρ := lintegral_mono hpt
    _ = ENNReal.ofReal (6 * D ^ 2 / N) * ρ Set.univ + ∫⁻ H, Ψ (κ • H) ∂ρ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ = ENNReal.ofReal (6 * D ^ 2 / N) + ∫⁻ H, Ψ H ∂M'.hermLaw := by
        rw [hρ1, mul_one, hρ, lintegral_map hΨm (measurable_const_smul κ)]
    _ ≤ ENNReal.ofReal (6 * D ^ 2 / N) +
        (ENNReal.ofReal (s / 2) * ENNReal.ofReal (C₁ * (N : ℝ) ^ 2) +
          ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal ((N : ℝ) ^ (-(6 : ℝ)))) := by
        gcongr
    _ = ENNReal.ofReal (6 * D ^ 2 / N + (s / 2 * (C₁ * (N : ℝ) ^ 2) +
          1 / (2 * s) * (N : ℝ) ^ (-(6 : ℝ)))) := by
        rw [← ENNReal.ofReal_mul hs2, ← ENNReal.ofReal_mul hs3,
          ← ENNReal.ofReal_add (mul_nonneg hs2 (by positivity)) (mul_nonneg hs3 hN60),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (7 * D ^ 2 / N) := by
        apply ENNReal.ofReal_le_ofReal
        have e : s / 2 * (C₁ * (N : ℝ) ^ 2) + 1 / (2 * s) * (N : ℝ) ^ (-(6 : ℝ)) =
            (C₁ + 1) / (2 * (N : ℝ) ^ 2) := by
          rw [hN6, hs]
          field_simp
        rw [e]
        have h1 : (C₁ + 1) / (2 * (N : ℝ) ^ 2) ≤ 1 / (2 * (N : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : C₁ + 1 ≤ N := hC
          nlinarith
        have h2 : 1 / (2 * (N : ℝ)) ≤ D ^ 2 / N := by
          rw [div_le_div_iff₀ (by positivity) hNpos]
          nlinarith [mul_le_mul_of_nonneg_right hD4 hNpos.le]
        have h3 : 7 * D ^ 2 / N = 6 * D ^ 2 / N + D ^ 2 / N := by ring
        linarith

/-- Lemma 13.3: `E|λ(H_t) - γ|² ≤ 7D²/N` for every `t`, and for `μ`. -/
theorem lintegral_dist_gamma_le {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 0 < C₀) {A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀)
      A₀ CR cR φ N₀) :
    ∃ N₃ : ℕ, ∀ N : ℕ, N₃ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      (∀ t : ℝ, 0 ≤ t → ∫⁻ x, ENNReal.ofReal (∑ k, (x k - gamma N k) ^ 2) ∂M.eigLaw t ≤
          ENNReal.ofReal (7 * Dpar A₀ N ^ 2 / N)) ∧
        ∫⁻ x, ENNReal.ofReal (∑ k, (x k - gamma N k) ^ 2) ∂gbeLaw 𝕜 N ≤
          ENNReal.ofReal (7 * Dpar A₀ N ^ 2 / N) := by
  obtain ⟨NK, hNK16, hNs, hbad⟩ := goodEvent_exists_NK hR 6
  have hϑ'0 : 0 < tildeTheta ϑ := by
    unfold tildeTheta
    have := lt_min hϑ one_pos
    positivity
  have hϑ'1 : tildeTheta ϑ ≤ 1 := by
    unfold tildeTheta
    have := min_le_right ϑ 1
    linarith
  set C₁ : ℝ := 18 * (cTheta (tildeTheta ϑ)⁻¹ * 4) ^ ((tildeTheta ϑ)⁻¹ * 4) * tildeC C₀ ^ 2 + 128
    with hC₁
  refine ⟨max NK ⌈C₁ + 1⌉₊, fun N hN M hM => ⟨fun t ht => ?_, ?_⟩⟩
  · have hNK : NK ≤ N := (le_max_left _ _).trans hN
    have hCN : C₁ + 1 ≤ N := (Nat.ceil_le.mp ((le_max_right _ _).trans hN))
    have hN16 : 16 ≤ N := hNK16.trans hNK
    obtain ⟨hk1, hk2, -, hk4⟩ := kappaT_bounds (𝕜 := 𝕜) (N := N) (by omega) ht
    have hk0 : 0 < Ensemble.kappaT 𝕜 N t :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) hk2
    have hM' := Ensemble.tildeFlow_assumptions (by omega) hϑ hδm hδp hC₀ hM ht
    exact goodEvent_lintegral_le hN16 (hNs N hNK) hk0 hk1 hk4 (Ensemble.tildeFlow_hermLaw M t)
      hϑ'0 hϑ'1 hM' (hbad N hNK _ hM') hCN
  · have hNK : NK ≤ N := (le_max_left _ _).trans hN
    have hCN : C₁ + 1 ≤ N := (Nat.ceil_le.mp ((le_max_right _ _).trans hN))
    have hN16 : 16 ≤ N := hNK16.trans hNK
    obtain ⟨hr0, hr1⟩ := goodEvent_rN_mem (𝕜 := 𝕜) (N := N) (by omega)
    obtain ⟨hk0, hk1, hk2⟩ := goodEvent_rpow_bounds (by omega) hr0 hr1
    have hM' := gbeTilde_assumptions (𝕜 := 𝕜) (N := N) (by omega) hϑ hδm hδp hC₀
    exact goodEvent_lintegral_le hN16 (hNs N hNK) hk0 hk1 hk2
      (goodEvent_gbe_hermLaw (𝕜 := 𝕜) (N := N) _) hϑ'0 hϑ'1 hM' (hbad N hNK _ hM') hCN

end Rigidity
