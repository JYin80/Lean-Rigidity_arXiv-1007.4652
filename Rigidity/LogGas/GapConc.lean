module

public import Rigidity.LogGas.Defs
public import Rigidity.LogGas.EntropyIneq
public import Rigidity.LogGas.PrekopaLeindler
public import Rigidity.LogGas.TwoPoint

@[expose] public section

/-!
# Gap concentration for convex log-gases

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

The file defines the gap observable `gapObs` `F(x) = N⁻¹ ∑_{i ∈ J} G(N(x_{i+m_k} - x_i))_k` of
(17.4) and the structure `GapHyp` of the hypotheses on `G` in Theorem 17.7, and proves:
* `gapConcentration_of_PL`, `gapConcentration`: Theorem 17.7, the sub-Gaussian bound
  `∫ e^{λ(F - ∫ F dω)} dω ≤ exp(C⋆ (n-1) |J| λ² / N²)` for a convex log-gas `ω`;
* `abs_integral_gapObs_sub_le`: Corollary 17.9,
  `|∫ F dν - ∫ F dω| ≤ (2/N) √(C⋆ (n-1) |J| S(ν|ω))`.

Here `r = n - 1`, indices are 0-based, and `F` is defined on all of `ℝ^N`; off the chamber `Σ`,
which is a null set for `ω` and for every `ν ≪ ω`, its values play no role.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- `x_j` for `j < N`, and `0` for `j ≥ N`. -/
noncomputable def extVec {N : ℕ} (x : Fin N → ℝ) (j : ℕ) : ℝ := if h : j < N then x ⟨j, h⟩ else 0

/-- The gap observable `F` (17.4), `r = n - 1`, 0-based indices:
`F(x) = N⁻¹ ∑_{i ∈ J} G(N(x_{i+m_k} - x_i))_k`. -/
noncomputable def gapObs {N r : ℕ} (J : Finset ℕ) (m : Fin r → ℕ) (G : (Fin r → ℝ) → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ J, G fun k => N * (extVec x (i + m k) - extVec x i)

/-- The hypotheses on `G` in Theorem 17.7. -/
structure GapHyp (r : ℕ) (A A' ρ : ℝ) (G : (Fin r → ℝ) → ℝ) : Prop where
  meas : Measurable G
  bound : ∀ u, (∀ k, 0 < u k) → |G u| ≤ A
  supp : ∀ u, (∀ k, 0 < u k) → (∃ k, ρ < u k) → G u = 0
  lip : ∀ u u' k, (∀ k, 0 < u k) → (∀ k, 0 < u' k) → (∀ k', k' ≠ k → u k' = u' k') →
    |G u - G u'| ≤ A' * |u k - u' k|

/-! ### Elementary facts on `extVec`, `gapObs` and the log-gas -/

/-- `extVec x j = x_j` for `j < N`. -/
private theorem gapConc_extVec_of_lt {N : ℕ} (x : Fin N → ℝ) {j : ℕ} (h : j < N) :
    extVec x j = x ⟨j, h⟩ := by
  simp [extVec, h]

/-- `extVec x i = x_i` for `i : Fin N`. -/
private theorem gapConc_extVec_val {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : extVec x i = x i :=
  gapConc_extVec_of_lt x i.isLt

/-- `x ↦ extVec x j` is measurable. -/
private theorem gapConc_measurable_extVec {N : ℕ} (j : ℕ) :
    Measurable fun x : Fin N → ℝ => extVec x j := by
  by_cases h : j < N
  · simpa [extVec, h] using measurable_pi_apply (⟨j, h⟩ : Fin N)
  · simp [extVec, h]

/-- The gap observable is measurable when `G` is. -/
private theorem gapConc_measurable_gapObs {N r : ℕ} (J : Finset ℕ) (m : Fin r → ℕ)
    {G : (Fin r → ℝ) → ℝ} (hG : Measurable G) : Measurable (gapObs (N := N) J m G) := by
  unfold gapObs
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hG.comp
    (measurable_pi_iff.2 fun k => measurable_const.mul
      ((gapConc_measurable_extVec _).sub (gapConc_measurable_extVec _))))

/-- The Hamiltonian `𝓥` is measurable when `𝓥₀` is continuous. -/
private theorem gapConc_measurable_logGasH {N : ℕ} {β : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hV : Continuous V₀) : Measurable (logGasH β V₀) := by
  unfold logGasH
  exact hV.measurable.sub (measurable_const.mul (Finset.measurable_sum _ fun p _ =>
    Real.measurable_log.comp ((measurable_pi_apply _).sub (measurable_pi_apply _))))

/-- On the chamber, the arguments `N(x_j - x_i)`, `i < j < N`, of `G` are positive. -/
private theorem gapConc_arg_pos {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ chamber N) {i j : ℕ}
    (hij : i < j) (hj : j < N) : 0 < (N : ℝ) * (extVec x j - extVec x i) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [gapConc_extVec_of_lt x hj, gapConc_extVec_of_lt x (hij.trans hj)]
  exact mul_pos hN (sub_pos.2 (hx (Fin.mk_lt_mk.2 hij)))

/-- On the chamber, `|F| ≤ |J| A / N` (Theorem 17.7, comments on the hypotheses). -/
private theorem gapConc_abs_gapObs_le {N r : ℕ} {m : Fin r → ℕ} (hm1 : ∀ k, 1 ≤ m k)
    {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N) {A A' ρ : ℝ} {G : (Fin r → ℝ) → ℝ}
    (hG : GapHyp r A A' ρ G) {x : Fin N → ℝ} (hx : x ∈ chamber N) :
    |gapObs J m G x| ≤ (N : ℝ)⁻¹ * (J.card * A) := by
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg N)
  unfold gapObs
  rw [abs_mul, abs_of_nonneg hN]
  refine mul_le_mul_of_nonneg_left ?_ hN
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun i hi => hG.bound _ fun k =>
    gapConc_arg_pos hx (by have := hm1 k; omega) (hJ i hi k)

/-- The partition function `Z` is positive. -/
private theorem gapConc_Z_ne_zero {N : ℕ} {β : ℝ} {V₀ : (Fin N → ℝ) → ℝ} (hV : Continuous V₀) :
    ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) ≠ 0 := by
  have hm : Measurable fun x => ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (gapConc_measurable_logGasH hV).neg)
  intro h
  rw [lintegral_eq_zero_iff hm] at h
  have hne : (chamber N).Nonempty := ⟨fun i => (i : ℝ), fun a b hab => by simpa using hab⟩
  have hpos : volume.restrict (chamber N) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (isOpen_chamber N).measure_ne_zero volume hne
  have := ae_neBot.2 hpos
  obtain ⟨x, hx⟩ := h.exists
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hx

/-- A convex log-gas is a probability measure. -/
private theorem gapConc_isProb {N : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) : IsProbabilityMeasure (logGasMeasure β V₀) := by
  constructor
  rw [logGasMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (gapConc_Z_ne_zero hω.cont) hω.finite.ne

/-- The log-gas is carried by the chamber. -/
private theorem gapConc_ae_chamber {N : ℕ} {β : ℝ} {V₀ : (Fin N → ℝ) → ℝ} :
    ∀ᵐ x ∂logGasMeasure β V₀, x ∈ chamber N := by
  have hac : logGasMeasure β V₀ ≪ volume.restrict (chamber N) :=
    (withDensity_absolutelyContinuous _ _).smul_left _
  exact hac.ae_le (ae_restrict_mem (isOpen_chamber N).measurableSet)

/-- `∫ g dω = Z⁻¹ ∫_Σ e^{-𝓥} g dx` for measurable `g ≥ 0`. -/
private theorem gapConc_lintegral_eq {N : ℕ} {β : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hV : Continuous V₀) {g : (Fin N → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂logGasMeasure β V₀ =
      (∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)))⁻¹ *
        ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) * g x := by
  have hf : Measurable fun x => ENNReal.ofReal (Real.exp (-logGasH β V₀ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (gapConc_measurable_logGasH hV).neg)
  rw [logGasMeasure, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hf hg,
    smul_eq_mul]
  rfl

/-! ### Steps 1 and 2 of the proof of Theorem 17.7 -/

/-- Step 1 of the proof of Theorem 17.7: for `a, b ∈ (0,∞)^r` and `s ∈ ℝ`,
`s (G(a) - G(b)) ≤ ∑_k [2 Λ(a_k/b_k) + C⋆ s²]`. -/
private theorem gapConc_telesc {r : ℕ} {A A' ρ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ)
    {G : (Fin r → ℝ) → ℝ} (hG : GapHyp r A A' ρ G) {a b : Fin r → ℝ} (ha : ∀ k, 0 < a k)
    (hb : ∀ k, 0 < b k) (s : ℝ) :
    s * (G a - G b) ≤ ∑ k, (2 * logCoshRatio (a k / b k) + cStar A A' ρ * s ^ 2) := by
  classical
  let c : ℕ → Fin r → ℝ := fun j k => if (k : ℕ) < j then b k else a k
  have hc0 : c 0 = a := by
    funext k
    simp [c]
  have hcr : c r = b := by
    funext k
    simp [c, k.isLt]
  have hcpos : ∀ j k, 0 < c j k := by
    intro j k
    simp only [c]
    split_ifs
    · exact hb k
    · exact ha k
  have hstep : ∀ k : Fin r, s * (G (c k) - G (c (k + 1))) ≤
      2 * logCoshRatio (a k / b k) + cStar A A' ρ * s ^ 2 := by
    intro k0
    let g : ℝ → ℝ := fun t => G (Function.update (c k0) k0 t)
    have hupd : ∀ t, 0 < t → ∀ k, 0 < Function.update (c k0) k0 t k := by
      intro t ht k
      rcases eq_or_ne k k0 with rfl | hk
      · simpa using ht
      · rw [Function.update_of_ne hk]
        exact hcpos _ _
    have hga : g (a k0) = G (c k0) := by
      simp only [g]
      congr 1
      funext k
      rcases eq_or_ne k k0 with rfl | hk
      · simp [c]
      · rw [Function.update_of_ne hk]
    have hgb : g (b k0) = G (c (k0 + 1)) := by
      simp only [g]
      congr 1
      funext k
      rcases eq_or_ne k k0 with rfl | hk
      · simp [c]
      · rw [Function.update_of_ne hk]
        have hk' : (k : ℕ) ≠ k0 := fun h => hk (Fin.ext h)
        simp only [c]
        by_cases h1 : (k : ℕ) < k0
        · simp [h1, show (k : ℕ) < k0 + 1 by omega]
        · simp [h1, show ¬ (k : ℕ) < k0 + 1 by omega]
    have h2 := twoPoint_ineq hA hA' hρ (g := g)
      (fun u hu => hG.bound _ (hupd u hu))
      (fun u v hu hv => by
        have := hG.lip _ _ k0 (hupd u hu) (hupd v hv)
          (fun k' hk' => by simp [Function.update_of_ne hk'])
        simpa using this)
      (fun u hu => hG.supp _ (hupd u (hρ.trans hu)) ⟨k0, by simpa using hu⟩)
      (ha k0) (hb k0) s
    rw [hga, hgb] at h2
    exact h2
  calc s * (G a - G b) = s * ∑ j ∈ Finset.range r, (G (c j) - G (c (j + 1))) := by
        rw [Finset.sum_range_sub' (fun j => G (c j)), hc0, hcr]
    _ = ∑ k : Fin r, s * (G (c k) - G (c (k + 1))) := by
        rw [Finset.mul_sum,
          ← Fin.sum_univ_eq_sum_range (fun j => s * (G (c j) - G (c (j + 1))))]
    _ ≤ _ := Finset.sum_le_sum fun k _ => hstep k

/-- The pairs `(i, i + m_k)`, `i ∈ J`, are distinct pairs `i < j < N`, so the sum of
`Λ((x_{i+m_k} - x_i)/(y_{i+m_k} - y_i))` over them is at most the sum over all pairs
(Theorem 17.7, Step 2). -/
private theorem gapConc_pairSum_le {N r : ℕ} {m : Fin r → ℕ} (hm : StrictMono m)
    (hm1 : ∀ k, 1 ≤ m k) {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N) {x y : Fin N → ℝ}
    (hx : x ∈ chamber N) (hy : y ∈ chamber N) :
    ∑ i ∈ J, ∑ k, logCoshRatio ((extVec x (i + m k) - extVec x i) /
        (extVec y (i + m k) - extVec y i)) ≤
      ∑ p : {q : Fin N × Fin N // q.1 < q.2},
        logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) := by
  classical
  let φ : ℕ × ℕ → ℝ := fun q =>
    logCoshRatio ((extVec x q.2 - extVec x q.1) / (extVec y q.2 - extVec y q.1))
  let e : {q : Fin N × Fin N // q.1 < q.2} ↪ ℕ × ℕ :=
    ⟨fun p => ((p.1.1 : ℕ), (p.1.2 : ℕ)), fun p p' h => by
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))⟩
  have hR : ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) =
      ∑ q ∈ Finset.univ.map e, φ q := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun p _ => ?_
    change _ = logCoshRatio ((extVec x (p.1.2 : ℕ) - extVec x (p.1.1 : ℕ)) /
      (extVec y (p.1.2 : ℕ) - extVec y (p.1.1 : ℕ)))
    simp only [gapConc_extVec_val]
  have hL : ∑ i ∈ J, ∑ k, logCoshRatio ((extVec x (i + m k) - extVec x i) /
      (extVec y (i + m k) - extVec y i)) =
      ∑ q ∈ J ×ˢ (Finset.univ : Finset (Fin r)), φ (q.1, q.1 + m q.2) := by
    rw [Finset.sum_product]
  rw [hL, hR]
  refine Finset.sum_le_sum_of_injOn (fun q => (q.1, q.1 + m q.2)) ?_ ?_ (fun _ _ => le_rfl) ?_
  · intro q _ q' _ h
    simp only [Prod.mk.injEq] at h
    have h2 : m q.2 = m q'.2 := by omega
    exact Prod.ext h.1 (hm.injective h2)
  · intro q hq
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true] at hq
    obtain ⟨⟨i, k⟩, hi, rfl⟩ := hq
    have h1 := hJ i hi k
    have h2 := hm1 k
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨⟨(⟨i, by omega⟩, ⟨i + m k, h1⟩), Fin.mk_lt_mk.2 (by omega)⟩, rfl⟩
  · intro q hq _
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hq
    obtain ⟨p, rfl⟩ := hq
    change 0 ≤ logCoshRatio ((extVec x (p.1.2 : ℕ) - extVec x (p.1.1 : ℕ)) /
      (extVec y (p.1.2 : ℕ) - extVec y (p.1.1 : ℕ)))
    simp only [gapConc_extVec_val]
    exact logCoshRatio_nonneg (div_pos (sub_pos.2 (hx p.2)) (sub_pos.2 (hy p.2)))

/-- Step 2 of the proof of Theorem 17.7: for `x, y ∈ Σ`,
`λ(F(x) - F(y)) ≤ 𝓥(x) + 𝓥(y) - 2𝓥((x+y)/2) + C⋆ r |J| λ²/N²`. -/
private theorem gapConc_pointwise {N r : ℕ} {β κ : ℝ} {V₀ : (Fin N → ℝ) → ℝ}
    (hω : IsConvexLogGas N β κ V₀) (hr : 1 ≤ r) {m : Fin r → ℕ} (hm : StrictMono m)
    (hm1 : ∀ k, 1 ≤ m k) {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N) {A A' ρ : ℝ}
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ) {G : (Fin r → ℝ) → ℝ} (hG : GapHyp r A A' ρ G)
    (lam : ℝ) {x y : Fin N → ℝ}
    (hx : x ∈ chamber N) (hy : y ∈ chamber N) :
    lam * (gapObs J m G x - gapObs J m G y) ≤
      logGasH β V₀ x + logGasH β V₀ y - 2 * logGasH β V₀ ((1 / 2 : ℝ) • (x + y)) +
        cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 * lam ^ 2 := by
  set Λx : ℕ → Fin r → ℝ := fun i k => logCoshRatio ((extVec x (i + m k) - extVec x i) /
    (extVec y (i + m k) - extVec y i)) with hΛx
  have h1 : lam * (gapObs J m G x - gapObs J m G y) =
      ∑ i ∈ J, lam / N * ((G fun k => N * (extVec x (i + m k) - extVec x i)) -
        G fun k => N * (extVec y (i + m k) - extVec y i)) := by
    unfold gapObs
    rw [← mul_sub, ← Finset.sum_sub_distrib, ← mul_assoc, Finset.mul_sum]
    rfl
  have h2 : ∀ i ∈ J, lam / N * ((G fun k => N * (extVec x (i + m k) - extVec x i)) -
        G fun k => N * (extVec y (i + m k) - extVec y i)) ≤
      ∑ k, (2 * Λx i k + cStar A A' ρ * (lam / N) ^ 2) := by
    intro i hi
    have hax : ∀ k, 0 < (N : ℝ) * (extVec x (i + m k) - extVec x i) := fun k =>
      gapConc_arg_pos hx (by have := hm1 k; omega) (hJ i hi k)
    have hay : ∀ k, 0 < (N : ℝ) * (extVec y (i + m k) - extVec y i) := fun k =>
      gapConc_arg_pos hy (by have := hm1 k; omega) (hJ i hi k)
    have hN : (N : ℝ) ≠ 0 := by
      have : 0 < N := by
        have := hJ i hi ⟨0, hr⟩
        omega
      exact_mod_cast this.ne'
    refine (gapConc_telesc hA hA' hρ hG hax hay (lam / N)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hΛx, mul_div_mul_left _ _ hN]
  have hsum : ∑ i ∈ J, ∑ k : Fin r, (2 * Λx i k + cStar A A' ρ * (lam / N) ^ 2) =
      2 * ∑ i ∈ J, ∑ k, Λx i k + cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 * lam ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hpairs := gapConc_pairSum_le hm hm1 hJ hx hy
  have hnn : 0 ≤ ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) :=
    Finset.sum_nonneg fun p _ =>
      logCoshRatio_nonneg (div_pos (sub_pos.2 (hx p.2)) (sub_pos.2 (hy p.2)))
  have hβ : ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) ≤
      β * ∑ p : {q : Fin N × Fin N // q.1 < q.2},
        logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) :=
    le_mul_of_one_le_left hnn hω.one_le_beta
  have hmid := logGasH_midpoint hω hx hy
  rw [h1]
  refine (Finset.sum_le_sum h2).trans ?_
  rw [hsum]
  have hpairs' : ∑ i ∈ J, ∑ k, Λx i k ≤ ∑ p : {q : Fin N × Fin N // q.1 < q.2},
      logCoshRatio ((x p.1.2 - x p.1.1) / (y p.1.2 - y p.1.1)) := hpairs
  nlinarith [hpairs', hβ, hmid]


/-! ### Theorem 17.7 -/

/-- `(e^a)^t = e^{a t}` in `ℝ≥0∞` for `t ≥ 0`. -/
private theorem gapConc_ofReal_exp_rpow (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp a) ^ t = ENNReal.ofReal (Real.exp (a * t)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos a).le ht, ← Real.exp_mul]

/-- Theorem 17.7, with the Prékopa–Leindler inequality as an explicit input. -/
theorem gapConcentration_of_PL (hPL : ∀ M, PLStatement M) {N r : ℕ} {β κ : ℝ}
    {V₀ : (Fin N → ℝ) → ℝ} (hω : IsConvexLogGas N β κ V₀) (hr : 1 ≤ r) {m : Fin r → ℕ}
    (hm : StrictMono m) (hm1 : ∀ k, 1 ≤ m k) {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N)
    {A A' ρ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ) {G : (Fin r → ℝ) → ℝ}
    (hG : GapHyp r A A' ρ G) (lam : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (gapObs J m G x -
        ∫ y, gapObs J m G y ∂logGasMeasure β V₀))) ∂logGasMeasure β V₀ ≤
      ENNReal.ofReal (Real.exp (cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 * lam ^ 2)) := by
  classical
  have hprob := gapConc_isProb hω
  have hSm : MeasurableSet (chamber N) := (isOpen_chamber N).measurableSet
  have hFm : Measurable (gapObs (N := N) J m G) := gapConc_measurable_gapObs J m hG.meas
  have hHm : Measurable (logGasH β V₀) := gapConc_measurable_logGasH hω.cont
  have hFb : ∀ x ∈ chamber N, |gapObs J m G x| ≤ (N : ℝ)⁻¹ * (J.card * A) :=
    fun x hx => gapConc_abs_gapObs_le hm1 hJ hG hx
  have hZ0 := gapConc_Z_ne_zero (β := β) hω.cont
  have hZt := hω.finite.ne
  have hpt := fun lam' (x y : Fin N → ℝ) (hx : x ∈ chamber N) (hy : y ∈ chamber N) =>
    gapConc_pointwise hω hr hm hm1 hJ hA hA' hρ hG lam' hx hy
  have hlint := fun (g : (Fin N → ℝ) → ℝ≥0∞) (hg : Measurable g) =>
    gapConc_lintegral_eq (β := β) hω.cont hg
  have haeS : ∀ᵐ x ∂logGasMeasure β V₀, x ∈ chamber N := gapConc_ae_chamber
  set ω := logGasMeasure β V₀ with hωdef
  set F : (Fin N → ℝ) → ℝ := gapObs J m G with hFdef
  set H : (Fin N → ℝ) → ℝ := logGasH β V₀ with hHdef
  set c : ℝ := cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 * lam ^ 2 with hcdef
  set Fbar : ℝ := ∫ y, F y ∂ω with hFbar
  set B : ℝ := (N : ℝ)⁻¹ * (J.card * A) with hBdef
  set Z : ℝ≥0∞ := ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-H x)) with hZdef
  have hFint : Integrable F ω :=
    Integrable.of_bound hFm.aestronglyMeasurable B (haeS.mono fun x hx => by
      rw [Real.norm_eq_abs]
      exact hFb x hx)
  have hexpint : ∀ t : ℝ, Integrable (fun x => Real.exp (t * F x)) ω := by
    intro t
    refine Integrable.of_bound (Real.measurable_exp.comp (hFm.const_mul t)).aestronglyMeasurable
      (Real.exp (|t| * B)) (haeS.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hFb x hx) (abs_nonneg t)
  -- `∫_Σ e^{-𝓥} e^{tF} dx = Z ∫ e^{tF} dω`
  have hIt : ∀ t : ℝ, ∫⁻ x in chamber N, ENNReal.ofReal (Real.exp (-H x)) *
      ENNReal.ofReal (Real.exp (t * F x)) = Z * ENNReal.ofReal (∫ x, Real.exp (t * F x) ∂ω) := by
    intro t
    rw [ofReal_integral_eq_lintegral_ofReal (hexpint t)
        (Eventually.of_forall fun x => (Real.exp_pos _).le),
      hlint (fun x => ENNReal.ofReal (Real.exp (t * F x)))
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFm.const_mul t))),
      ← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZt, one_mul]
  set Ip : ℝ := ∫ x, Real.exp (lam * F x) ∂ω with hIp
  set Im : ℝ := ∫ x, Real.exp ((-lam) * F x) ∂ω with hIm
  have hIp0 : 0 ≤ Ip := integral_nonneg fun x => (Real.exp_pos _).le
  have hIm0 : 0 ≤ Im := integral_nonneg fun x => (Real.exp_pos _).le
  -- Step 3: Prékopa–Leindler with `τ = 1/2`
  have hmeas : ∀ f : (Fin N → ℝ) → ℝ, Measurable f →
      Measurable ((chamber N).indicator fun x => ENNReal.ofReal (Real.exp (f x))) :=
    fun f hf => (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hf)).indicator hSm
  have hcond : ∀ x y : Fin N → ℝ,
      (chamber N).indicator (fun x => ENNReal.ofReal (Real.exp (lam * F x - c - H x))) x ^
          (1 / 2 : ℝ) *
        (chamber N).indicator (fun x => ENNReal.ofReal (Real.exp ((-lam) * F x - H x))) y ^
          (1 - 1 / 2 : ℝ) ≤
      (chamber N).indicator (fun x => ENNReal.ofReal (Real.exp (-H x)))
        ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) := by
    intro x y
    by_cases hx : x ∈ chamber N
    · by_cases hy : y ∈ chamber N
      · have hmid : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y ∈ chamber N :=
          convex_chamber N hx hy (by norm_num) (by norm_num) (by norm_num)
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hmid,
          gapConc_ofReal_exp_rpow _ (by norm_num), gapConc_ofReal_exp_rpow _ (by norm_num),
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h2 := hpt lam x y hx hy
        have he : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) := by
          rw [smul_add]
          norm_num
        rw [he]
        linarith
      · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
        positivity
    · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul]
      positivity
  have hPL' := hPL N (1 / 2) (by norm_num) (by norm_num)
    ((chamber N).indicator fun x => ENNReal.ofReal (Real.exp (lam * F x - c - H x)))
    ((chamber N).indicator fun x => ENNReal.ofReal (Real.exp ((-lam) * F x - H x)))
    ((chamber N).indicator fun x => ENNReal.ofReal (Real.exp (-H x)))
    (hmeas (fun x => lam * F x - c - H x) (((hFm.const_mul lam).sub measurable_const).sub hHm))
    (hmeas (fun x => (-lam) * F x - H x) ((hFm.const_mul (-lam)).sub hHm))
    (hmeas (fun x => -H x) hHm.neg) hcond
  have hu : ∫⁻ x, (chamber N).indicator
      (fun x => ENNReal.ofReal (Real.exp (lam * F x - c - H x))) x =
      ENNReal.ofReal (Real.exp (-c)) * (Z * ENNReal.ofReal Ip) := by
    rw [lintegral_indicator hSm, ← hIt lam, ← lintegral_const_mul _
      (f := fun x => ENNReal.ofReal (Real.exp (-H x)) * ENNReal.ofReal (Real.exp (lam * F x)))
      ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hHm.neg)).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hFm.const_mul lam))))]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hv : ∫⁻ x, (chamber N).indicator
      (fun x => ENNReal.ofReal (Real.exp ((-lam) * F x - H x))) x = Z * ENNReal.ofReal Im := by
    rw [lintegral_indicator hSm, ← hIt (-lam)]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hw : ∫⁻ x, (chamber N).indicator (fun x => ENNReal.ofReal (Real.exp (-H x))) x = Z :=
    lintegral_indicator hSm _
  rw [hu, hv, hw] at hPL'
  -- back to real numbers
  set z : ℝ := Z.toReal with hz
  have hz0 : 0 < z := ENNReal.toReal_pos hZ0 hZt
  have hZz : Z = ENNReal.ofReal z := (ENNReal.ofReal_toReal hZt).symm
  rw [hZz, ← ENNReal.ofReal_mul hz0.le, ← ENNReal.ofReal_mul hz0.le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff hz0.le,
    show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.mul_rpow (by positivity) (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_le_left hz0.le] at hPL'
  have hprod : Ip * Im ≤ Real.exp c := by
    have h1 : z ^ 2 * (Real.exp (-c) * (Ip * Im)) ≤ z ^ 2 * 1 := by
      calc z ^ 2 * (Real.exp (-c) * (Ip * Im))
          = Real.exp (-c) * (z * Ip) * (z * Im) := by ring
        _ ≤ z ^ 2 := hPL'
        _ = z ^ 2 * 1 := (mul_one _).symm
    have h2 := le_of_mul_le_mul_left h1 (by positivity)
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos c), mul_one] at h2
    exact h2
  -- Step 4: `∫ e^{-λF} dω ≥ e^{-λ F̄}`
  have hJen : Real.exp (-lam * Fbar) ≤ Im := by
    have h1 : ∀ x, Real.exp (-lam * Fbar) * ((-lam) * (F x - Fbar) + 1) ≤
        Real.exp ((-lam) * F x) := by
      intro x
      calc Real.exp (-lam * Fbar) * ((-lam) * (F x - Fbar) + 1)
          ≤ Real.exp (-lam * Fbar) * Real.exp ((-lam) * (F x - Fbar)) :=
            mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
        _ = Real.exp ((-lam) * F x) := by
            rw [← Real.exp_add]
            ring_nf
    have hint1 : Integrable (fun x => (-lam) * (F x - Fbar)) ω :=
      (hFint.sub (integrable_const _)).const_mul _
    have h2 := integral_mono ((hint1.add (integrable_const _)).const_mul _) (hexpint (-lam)) h1
    have h3 : ∫ x, Real.exp (-lam * Fbar) * ((-lam) * (F x - Fbar) + 1) ∂ω =
        Real.exp (-lam * Fbar) := by
      rw [integral_const_mul, integral_add hint1 (integrable_const _), integral_const_mul,
        integral_sub hFint (integrable_const _), ← hFbar]
      simp
    exact h3.symm.le.trans h2
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (F x - Fbar))) ∂ω =
      ENNReal.ofReal (Ip * Real.exp (-lam * Fbar)) := by
    have heq : ∀ x, ENNReal.ofReal (Real.exp (lam * (F x - Fbar))) =
        ENNReal.ofReal (Real.exp (lam * F x) * Real.exp (-lam * Fbar)) := by
      intro x
      rw [← Real.exp_add]
      ring_nf
    rw [lintegral_congr heq, ← ofReal_integral_eq_lintegral_ofReal ((hexpint lam).mul_const _)
      (Eventually.of_forall fun x => by positivity), integral_mul_const]
  rw [hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Ip * Real.exp (-lam * Fbar) ≤ Ip * Im := mul_le_mul_of_nonneg_left hJen hIp0
    _ ≤ Real.exp c := hprod


/-- Theorem 17.7 (gap concentration). -/
theorem gapConcentration {N r : ℕ} {β κ : ℝ}
    {V₀ : (Fin N → ℝ) → ℝ} (hω : IsConvexLogGas N β κ V₀) (hr : 1 ≤ r) {m : Fin r → ℕ}
    (hm : StrictMono m) (hm1 : ∀ k, 1 ≤ m k) {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N)
    {A A' ρ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ) {G : (Fin r → ℝ) → ℝ}
    (hG : GapHyp r A A' ρ G) (lam : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (gapObs J m G x -
        ∫ y, gapObs J m G y ∂logGasMeasure β V₀))) ∂logGasMeasure β V₀ ≤
      ENNReal.ofReal (Real.exp (cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 * lam ^ 2)) :=
  gapConcentration_of_PL prekopaLeindler hω hr hm hm1 hJ hA hA' hρ hG lam

/-! ### Corollary 17.9 -/

/-- If `λ D ≤ S + K λ²` for all `λ > 0`, with `S, K, D ≥ 0`, then `D ≤ 2 √(S K)`
(the optimization over `λ` in the proof of Corollary 17.9). -/
private theorem gapConc_opt {S K D : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (h : ∀ lam : ℝ, 0 < lam → lam * D ≤ S + K * lam ^ 2) : D ≤ 2 * Real.sqrt (S * K) := by
  rcases hD.eq_or_lt with hD0 | hDpos
  · rw [← hD0]
    positivity
  rcases hK.eq_or_lt with hK0 | hKpos
  · exfalso
    have h1 := h ((S + 1) / D) (by positivity)
    rw [← hK0, zero_mul, add_zero, div_mul_cancel₀ _ hDpos.ne'] at h1
    linarith
  · have h1 := h (D / (2 * K)) (by positivity)
    have e1 : D / (2 * K) * D = 2 * (D ^ 2 / (4 * K)) := by
      field_simp
      ring
    have e2 : K * (D / (2 * K)) ^ 2 = D ^ 2 / (4 * K) := by
      field_simp
      ring
    rw [e1, e2] at h1
    have h2 : D ^ 2 / (4 * K) ≤ S := by linarith
    rw [div_le_iff₀ (by positivity)] at h2
    have h3 : D / 2 ≤ Real.sqrt (S * K) :=
      (Real.le_sqrt (by positivity) (by positivity)).2 (by nlinarith)
    linarith

/-- Corollary 17.9: `|∫ F dν - ∫ F dω| ≤ (2/N) √(C⋆ (n-1) |J| S(ν|ω))`. -/
theorem abs_integral_gapObs_sub_le {N r : ℕ} {β κ : ℝ}
    {V₀ : (Fin N → ℝ) → ℝ} (hω : IsConvexLogGas N β κ V₀) (hr : 1 ≤ r) {m : Fin r → ℕ}
    (hm : StrictMono m) (hm1 : ∀ k, 1 ≤ m k) {J : Finset ℕ} (hJ : ∀ i ∈ J, ∀ k, i + m k < N)
    {A A' ρ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hρ : 0 < ρ) {G : (Fin r → ℝ) → ℝ}
    (hG : GapHyp r A A' ρ G) (ν : Measure (Fin N → ℝ)) [IsProbabilityMeasure ν]
    (hνω : ν ≪ logGasMeasure β V₀) (hS : InformationTheory.klDiv ν (logGasMeasure β V₀) ≠ ∞) :
    |∫ x, gapObs J m G x ∂ν - ∫ x, gapObs J m G x ∂logGasMeasure β V₀| ≤
      2 / N * Real.sqrt (cStar A A' ρ * r * J.card *
        (InformationTheory.klDiv ν (logGasMeasure β V₀)).toReal) := by
  classical
  have hprob := gapConc_isProb hω
  have hSm : MeasurableSet (chamber N) := (isOpen_chamber N).measurableSet
  have hFm : Measurable (gapObs (N := N) J m G) := gapConc_measurable_gapObs J m hG.meas
  have hFb : ∀ x ∈ chamber N, |gapObs J m G x| ≤ (N : ℝ)⁻¹ * (J.card * A) :=
    fun x hx => gapConc_abs_gapObs_le hm1 hJ hG hx
  have haeS : ∀ᵐ x ∂logGasMeasure β V₀, x ∈ chamber N := gapConc_ae_chamber
  have haeν : ∀ᵐ x ∂ν, x ∈ chamber N := hνω.ae_le haeS
  have hconc := fun lam => gapConcentration hω hr hm hm1 hJ hA hA' hρ hG lam
  have hstar : 0 ≤ cStar A A' ρ :=
    le_trans (div_nonneg (sq_nonneg A) (mul_pos two_pos cZero_pos).le) (le_max_left _ _)
  set ω := logGasMeasure β V₀ with hωdef
  set F : (Fin N → ℝ) → ℝ := gapObs J m G with hFdef
  set Fbar : ℝ := ∫ y, F y ∂ω with hFbar
  set B : ℝ := (N : ℝ)⁻¹ * (J.card * A) with hBdef
  set K : ℝ := cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 with hKdef
  set S : ℝ := (InformationTheory.klDiv ν ω).toReal with hSdef
  have hB0 : 0 ≤ B := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hFintν : Integrable F ν :=
    Integrable.of_bound hFm.aestronglyMeasurable B (haeν.mono fun x hx => by
      rw [Real.norm_eq_abs]
      exact hFb x hx)
  -- `σ λ Δ ≤ S + K λ²` for `σ = ±1` and `λ > 0` (proof of Corollary 17.9)
  have hkey : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ lam : ℝ, 0 < lam →
      lam * (σ * (∫ x, F x ∂ν - Fbar)) ≤ S + K * lam ^ 2 := by
    intro σ hσ lam hlam
    set F' : (Fin N → ℝ) → ℝ := (chamber N).indicator fun x => σ * (F x - Fbar) with hF'
    have hF'm : Measurable F' := (measurable_const.mul (hFm.sub measurable_const)).indicator hSm
    have hF'b : ∃ C, ∀ x, |F' x| ≤ C := ⟨|σ| * (B + |Fbar|), fun x => by
      by_cases hx : x ∈ chamber N
      · rw [hF', Set.indicator_of_mem hx, abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add_left (hFb x hx) _))
          (abs_nonneg _)
      · rw [hF', Set.indicator_of_notMem hx, abs_zero]
        positivity⟩
    have hE := entropy_ineq hνω hF'm hF'b hlam
    have hν' : ∫ x, F' x ∂ν = σ * (∫ x, F x ∂ν - Fbar) := by
      rw [integral_congr_ae (haeν.mono fun x hx =>
          (Set.indicator_of_mem hx (fun x => σ * (F x - Fbar)) : F' x = σ * (F x - Fbar))),
        integral_const_mul, integral_sub hFintν (integrable_const _)]
      simp
    have hω' : ∫ x, Real.exp (lam * F' x) ∂ω = ∫ x, Real.exp ((lam * σ) * (F x - Fbar)) ∂ω := by
      refine integral_congr_ae (haeS.mono fun x hx => ?_)
      simp only [hF', Set.indicator_of_mem hx]
      ring_nf
    have hint : Integrable (fun x => Real.exp ((lam * σ) * (F x - Fbar))) ω := by
      refine Integrable.of_bound
        (Real.measurable_exp.comp ((hFm.sub measurable_const).const_mul _)).aestronglyMeasurable
        (Real.exp (|lam * σ| * (B + |Fbar|))) (haeS.mono fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add_left (hFb x hx) _))
        (abs_nonneg _)
    have hpos : 0 < ∫ x, Real.exp ((lam * σ) * (F x - Fbar)) ∂ω := integral_exp_pos hint
    have hle : ∫ x, Real.exp ((lam * σ) * (F x - Fbar)) ∂ω ≤ Real.exp (K * lam ^ 2) := by
      have h := hconc (lam * σ)
      rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => (Real.exp_pos _).le),
        ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at h
      have e : K * lam ^ 2 = cStar A A' ρ * r * J.card / (N : ℝ) ^ 2 * (lam * σ) ^ 2 := by
        rw [mul_pow, hσ, mul_one]
      rw [e]
      exact h
    have hlog : Real.log (∫ x, Real.exp ((lam * σ) * (F x - Fbar)) ∂ω) ≤ K * lam ^ 2 :=
      (Real.log_le_iff_le_exp hpos).2 hle
    rw [hν', hω', ENNReal.ofReal_le_iff_le_toReal hS] at hE
    linarith
  have hD : |∫ x, F x ∂ν - Fbar| ≤ 2 * Real.sqrt (S * K) := by
    refine gapConc_opt ENNReal.toReal_nonneg hK0 (abs_nonneg _) fun lam hlam => ?_
    rcases abs_cases (∫ x, F x ∂ν - Fbar) with ⟨h, _⟩ | ⟨h, _⟩
    · have := hkey 1 (by norm_num) lam hlam
      rw [h]
      linarith
    · have := hkey (-1) (by norm_num) lam hlam
      rw [h]
      linarith
  refine hD.trans (le_of_eq ?_)
  rw [hKdef, show S * (cStar A A' ρ * r * J.card / (N : ℝ) ^ 2) =
      cStar A A' ρ * r * J.card * S / (N : ℝ) ^ 2 by ring,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (Nat.cast_nonneg N)]
  ring


/-! ### Instances

All instances use `N = 2`, `β = 1`, `κ = 2`, `𝓥₀(x) = x₀² + x₁²`, `r = 1` (`n = 2`), `m₀ = 1`,
`J = {0}`, and `G(u) = max(1 - u₀, 0)` with `A = A' = ρ = 1`, so that
`F(x) = ½ max(1 - 2(x₁ - x₀), 0)`. -/

end Rigidity
