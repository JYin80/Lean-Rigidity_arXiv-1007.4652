module

public import Rigidity.Fluctuation.EventBounds
public import Rigidity.Fluctuation.Tuple

@[expose] public section

/-!
# Fluctuation averaging (NP v1.1, §6.1, §6.7: Theorem 6.1)

Numbers in this file refer to the blueprint NP v1.1; [EYY, …] refers to the original paper
(Erdős–Yau–Yin, arXiv:1007.4652).
-/

/-! Theorem 6.1 is the fluctuation-averaging step of the proof of [EYY, Lemma 4.1]. The proof
follows §6.7: the expansion (6.37) of the `p`-th moment over index tuples `𝐤 : Fin p → Fin N`
(position `s` of §6.6 is `s.val + 1`), the split (6.38) along the event `Ξ_L` of (6.27), the bounds
(6.39), (6.40) for one tuple, the inclusion `Ξ_p(z) ⊆ Ξ_L` (Step 3) and the summation over tuples
with Lemma 6.13 (Step 4). The constants are `C_F` of (6.35), `p₀` of Theorem 6.1, and `N₀` is
given by the conditions (6.36). -/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

section MainHelpers

/-- The conjugation pattern of §6.6: the factor of position `s` is conjugated when `p/2 ≤ s`. -/
private abbrev main_sig (p : ℕ) (s : Fin p) : ℂ →+* ℂ :=
  if p / 2 ≤ s.val then starRingEnd ℂ else RingHom.id ℂ

private lemma main_norm_sig {p : ℕ} (s : Fin p) (w : ℂ) : ‖main_sig p s w‖ = ‖w‖ := by
  unfold main_sig
  split_ifs <;> simp

private lemma main_continuous_sig {p : ℕ} (s : Fin p) : Continuous fun w : ℂ => main_sig p s w := by
  unfold main_sig
  split_ifs
  · exact Complex.continuous_conj
  · exact continuous_id

/-- `|w|^p = w^{p/2} w̄^{p/2}` for even `p` (Step 1 of §6.7). -/
private lemma main_prod_sig {p : ℕ} (hpe : Even p) (w : ℂ) :
    ∏ s : Fin p, main_sig p s w = ((‖w‖ ^ p : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ := hpe
  have h2 : (m + m) / 2 = m := by omega
  have e : ∀ s : Fin (m + m), main_sig (m + m) s w =
      (fun i : ℕ => if m ≤ i then starRingEnd ℂ w else w) s.val := by
    intro s
    unfold main_sig
    rw [h2]
    split_ifs with h <;> simp [h]
  rw [Finset.prod_congr rfl fun s _ => e s,
    Fin.prod_univ_eq_prod_range (fun i => if m ≤ i then starRingEnd ℂ w else w) (m + m),
    ← Finset.prod_range_mul_prod_Ico _ (show m ≤ m + m by omega),
    Finset.prod_congr rfl fun i hi => ite_eq_right (by simp at hi; omega),
    Finset.prod_congr rfl fun i hi => ite_eq_left (by simp at hi; omega)]
  simp only [Finset.prod_const, Finset.card_range, Nat.card_Ico]
  rw [show m + m - m = m by omega, ← mul_pow, Complex.mul_conj']
  push_cast
  ring

/-- The expansion (6.37): `|∑_k t_k X_k|^p = ∑_𝐤 ∏_s t_{k_s}^{#_s} ∏_s X_{k_s}^{#_s}`. -/
private lemma main_expand {N p : ℕ} (hpe : Even p) (t X : Fin N → ℂ) :
    ((‖∑ k, t k * X k‖ ^ p : ℝ) : ℂ) =
      ∑ κ : Fin p → Fin N, (∏ s, main_sig p s (t (κ s))) * ∏ s, main_sig p s (X (κ s)) := by
  classical
  rw [← main_prod_sig hpe]
  simp only [map_sum, map_mul]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun κ _ => Finset.prod_mul_distrib

/-- `C_m ≥ 1` for `a ≥ 1` ((6.9)). -/
private lemma main_one_le_faCm {a : ℝ} (ha : 1 ≤ a) : 1 ≤ faCm a := by
  have hk : 0 ≤ kappaTheta a := by
    unfold kappaTheta cTheta
    have h1 : 0 ≤ Real.log a := Real.log_nonneg ha
    have h2 : 0 ≤ Real.log (4 * (90 * a)) := Real.log_nonneg (by linarith)
    positivity
  have h1 : 1 ≤ cLD a := by
    unfold cLD
    have : 1 ≤ (4 * a + 2 + kappaTheta a) ^ (2 * a + 1) :=
      Real.one_le_rpow (by linarith) (by linarith)
    linarith
  exact le_trans (by nlinarith) (le_max_right (cTheta a ^ a) (cLD a ^ 2))

/-- `c N^α ≤ N` for all large `N`, when `α < 1` (the conditions (6.36)). -/
private lemma main_eventually_le (c : ℝ) {α : ℝ} (hα : α < 1) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ α ≤ N := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - α)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually_ge_atTop c, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  calc c * (N : ℝ) ^ α ≤ (N : ℝ) ^ (1 - α) * (N : ℝ) ^ α :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = N := by rw [← Real.rpow_add hN0]; simp

/-- Lebesgue integrals are superadditive over finite sums. -/
private lemma main_sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- Step 4 of §6.7: with Lemma 6.13 and `N^{-1/2} ≤ y`,
`∑_𝐤 N^{-p} y^{p+ℓ(𝐤)} ≤ (p+1) p^p y^{2p}`. -/
private lemma main_sum_tuples {N p : ℕ} (hN : 0 < N) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : 1 ≤ N * y ^ 2) :
    ∑ κ : Fin p → Fin N, ((1 : ℝ) / N) ^ p * y ^ (p + loneCount κ) ≤
      ((p : ℝ) + 1) * (p : ℝ) ^ p * y ^ (2 * p) := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set u := Real.sqrt N with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hNr
  have hu2 : u ^ 2 = N := Real.sq_sqrt hNr.le
  have huy : 1 ≤ u * y := by
    have h : 1 ≤ (u * y) ^ 2 := by rw [mul_pow, hu2]; exact hy
    nlinarith [mul_nonneg hu0.le hy0]
  have hmaps : ∀ κ ∈ (Finset.univ : Finset (Fin p → Fin N)),
      loneCount κ ∈ Finset.range (p + 1) := fun κ _ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp)))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ ℓ ∈ Finset.range (p + 1),
      ∑ κ ∈ Finset.univ.filter (fun κ : Fin p → Fin N => loneCount κ = ℓ),
        ((1 : ℝ) / N) ^ p * y ^ (p + loneCount κ) ≤ (p : ℝ) ^ p * y ^ (2 * p) := by
    intro ℓ hℓ
    have hℓp : ℓ ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    rw [Finset.sum_congr rfl fun κ hκ => by rw [(Finset.mem_filter.1 hκ).2],
      Finset.sum_const, nsmul_eq_mul]
    have hc := (card_tuples_le N p ℓ hℓp).1
    have hNl : (N : ℝ) ^ (((p : ℝ) + ℓ) / 2) = u ^ (p + ℓ) := by
      rw [hu, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
      congr 1
      push_cast
      ring
    calc ((Finset.univ.filter fun κ : Fin p → Fin N => loneCount κ = ℓ).card : ℝ) *
          (((1 : ℝ) / N) ^ p * y ^ (p + ℓ))
        ≤ ((p : ℝ) ^ p * (N : ℝ) ^ (((p : ℝ) + ℓ) / 2)) * (((1 : ℝ) / N) ^ p * y ^ (p + ℓ)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (p : ℝ) ^ p * ((u * y) ^ (p + ℓ) / u ^ (2 * p)) := by
          rw [hNl, ← hu2, _root_.one_div_pow, ← pow_mul, mul_pow]
          ring
      _ ≤ (p : ℝ) ^ p * ((u * y) ^ (2 * p) / u ^ (2 * p)) := by
          gcongr
          omega
      _ = (p : ℝ) ^ p * y ^ (2 * p) := by
          rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hu0.ne')]
  calc ∑ ℓ ∈ Finset.range (p + 1),
        ∑ κ ∈ Finset.univ.filter (fun κ : Fin p → Fin N => loneCount κ = ℓ),
          ((1 : ℝ) / N) ^ p * y ^ (p + loneCount κ)
      ≤ ∑ _ℓ ∈ Finset.range (p + 1), (p : ℝ) ^ p * y ^ (2 * p) := Finset.sum_le_sum hterm
    _ = ((p : ℝ) + 1) * (p : ℝ) ^ p * y ^ (2 * p) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Cauchy–Schwarz and Hölder with `p` factors, as in (6.40): if `‖g_s‖_{L^{2p}} ≤ K` for every
`s`, then `∫_A ∏_s |g_s| ≤ μ(A)^{1/2} K^p`. -/
private lemma main_setLIntegral_prod_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℕ}
    (hp : 1 ≤ p) (g : Fin p → α → ℂ) (hg : ∀ s, AEStronglyMeasurable (g s) μ) {K : ℝ} (hK : 0 ≤ K)
    (hgK : ∀ s, eLpNorm (g s) (2 * p) μ ≤ ENNReal.ofReal K) (A : Set α) :
    ∫⁻ x in A, ∏ s, ‖g s x‖ₑ ∂μ ≤ μ A ^ (1 / 2 : ℝ) * ENNReal.ofReal (K ^ p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hI : ∀ s, ∫⁻ x, ‖g s x‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂μ ≤
      ENNReal.ofReal K ^ ((2 * p : ℕ) : ℝ) := by
    intro s
    have h := hgK s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; omega)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top p)) (hg s)] at h
    have e : ((2 : ℝ≥0∞) * p).toReal = ((2 * p : ℕ) : ℝ) := by simp
    rw [e, one_div] at h
    exact (ENNReal.rpow_inv_le_iff (by positivity)).1 h
  have hH : ∫⁻ x, (∏ s, ‖g s x‖ₑ) ^ (2 : ℝ) ∂μ ≤ (ENNReal.ofReal K ^ (2 : ℝ)) ^ p := by
    have e1 : ∀ x, (∏ s, ‖g s x‖ₑ) ^ (2 : ℝ) =
        ∏ s, (‖g s x‖ₑ ^ ((2 * p : ℕ) : ℝ)) ^ ((1 : ℝ) / p) := by
      intro x
      rw [← ENNReal.prod_rpow_of_nonneg (by norm_num)]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← ENNReal.rpow_mul]
      congr 1
      push_cast
      field_simp
    simp_rw [e1]
    calc ∫⁻ x, ∏ s, (‖g s x‖ₑ ^ ((2 * p : ℕ) : ℝ)) ^ ((1 : ℝ) / p) ∂μ
        ≤ ∏ s : Fin p, (∫⁻ x, ‖g s x‖ₑ ^ ((2 * p : ℕ) : ℝ) ∂μ) ^ ((1 : ℝ) / p) :=
          ENNReal.lintegral_prod_norm_pow_le Finset.univ
            (fun s _ => (hg s).aemeasurable.enorm.pow_const _) (by simp; field_simp)
            (fun _ _ => by positivity)
      _ ≤ ∏ s : Fin p, (ENNReal.ofReal K ^ ((2 * p : ℕ) : ℝ)) ^ ((1 : ℝ) / p) :=
          Finset.prod_le_prod fun s _ => ENNReal.rpow_le_rpow (hI s) (by positivity)
      _ = (ENNReal.ofReal K ^ (2 : ℝ)) ^ p := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.rpow_mul]
          congr 2
          push_cast
          field_simp
  have hmeas : AEMeasurable (fun x => ∏ s, ‖g s x‖ₑ) (μ.restrict A) :=
    Finset.aemeasurable_fun_prod _ fun s _ => (hg s).aemeasurable.enorm.restrict
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict A) Real.HolderConjugate.two_two
    (f := fun _ => 1) (g := fun x => ∏ s, ‖g s x‖ₑ) aemeasurable_const hmeas
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ] at hCS
  refine hCS.trans ?_
  calc μ A ^ (1 / (2 : ℝ)) * (∫⁻ x, (∏ s, ‖g s x‖ₑ) ^ (2 : ℝ) ∂(μ.restrict A)) ^ (1 / (2 : ℝ))
      ≤ μ A ^ (1 / 2 : ℝ) * ((ENNReal.ofReal K ^ (2 : ℝ)) ^ p) ^ (1 / (2 : ℝ)) := by
        gcongr
        exact (setLIntegral_le_lintegral _ _).trans hH
    _ = μ A ^ (1 / 2 : ℝ) * ENNReal.ofReal (K ^ p) := by
        congr 1
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          show (2 : ℝ) * (p * (1 / 2)) = p by ring, ENNReal.rpow_natCast, ENNReal.ofReal_pow hK]

/-- Step 3 of §6.7: under (6.1) and `12 C₀ p ≤ N`, `Ξ_p(z) ⊆ Ξ_L` for every `L` with
`1 ≤ |L| ≤ p` (Lemma 6.6 (b), (c) and `p ≥ p₀`). -/
private lemma main_apriori_sub {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) {z : ℂ}
    (hz : 0 < z.im) (hη10 : z.im ≤ 10) {p : ℕ} (hp1 : 1 ≤ p) (h12 : 12 * C₀ * p ≤ N)
    (hpNη : (p : ℝ) ≤ N * z.im) (hNη : (p : ℝ) ^ (12 * ϑ⁻¹ + 11) ≤ N * z.im)
    (hp₀ : 25 * Real.exp 1 * C₀ * faCm ϑ⁻¹ * 13 ^ (2 * ϑ⁻¹ + 3 / 2) ≤ p)
    {L : Finset (Fin N)} (hL1 : 1 ≤ L.card) (hLp : L.card ≤ p) :
    aprioriEvent N p z ⊆ faXiL M C₀ ϑ⁻¹ p L z := by
  intro x hx
  obtain ⟨-, hb, hc⟩ := faEvent_bounds M hM hp1 h12 hL1 hLp hz x
  refine ⟨?_, (hb hx).2⟩
  have hΦ2 := hc hη10 hpNη hx
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hCm := main_one_le_faCm ha1
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp1
  have hΦ0 : 0 ≤ phiL C₀ L z x :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 2 * ϑ⁻¹ + 3 / 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (p : ℝ) ^ (3 * r) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := hQ ▸ Real.rpow_pos_of_pos hpos _
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 5 * Real.exp 1 * faCm ϑ⁻¹ * 13 ^ r := ⟨_, rfl⟩
  have hD0 : 0 < D := hD ▸ mul_pos (mul_pos (by positivity) (by linarith)) (by positivity)
  have h13 : (13 * (p : ℝ) ^ 3) ^ r = 13 ^ r * Q := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (p : ℝ) 3,
      ← Real.rpow_mul hpos.le, hQ]
    norm_num
  have hE : (p : ℝ) ^ (12 * ϑ⁻¹ + 11) = Q * Q * (p : ℝ) ^ 2 := by
    rw [hQ, ← Real.rpow_add hpos, ← Real.rpow_two, ← Real.rpow_add hpos]
    congr 1
    rw [hr]
    ring
  have hphi0 : faPhi0 ϑ⁻¹ p = (D * Q)⁻¹ := by
    unfold faPhi0
    rw [← hr, h13, hD]
    ring_nf
  have hp5 : 5 * C₀ * D ≤ p := by
    have e : 5 * C₀ * D = 25 * Real.exp 1 * C₀ * faCm ϑ⁻¹ * 13 ^ (2 * ϑ⁻¹ + 3 / 2) := by
      rw [hD, hr]
      ring
    linarith
  rw [hphi0]
  have hQp : 0 < Q * Q * (p : ℝ) ^ 2 := mul_pos (mul_pos hQ0 hQ0) (pow_pos hpos 2)
  have hb2 : phiL C₀ L z x ^ 2 ≤ ((D * Q)⁻¹) ^ 2 := by
    calc phiL C₀ L z x ^ 2 ≤ 25 * C₀ ^ 2 / (N * z.im) := hΦ2
      _ ≤ 25 * C₀ ^ 2 / (Q * Q * (p : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hQp (by rw [← hE]; exact hNη)
      _ ≤ ((D * Q)⁻¹) ^ 2 := by
          rw [show ((D * Q)⁻¹) ^ 2 = 1 / (D * Q) ^ 2 by rw [inv_pow, one_div],
            div_le_div_iff₀ hQp (pow_pos (mul_pos hD0 hQ0) 2)]
          have h5 : (5 * C₀ * D) ^ 2 ≤ (p : ℝ) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (by linarith) hD0.le) hp5 2
          have := mul_le_mul_of_nonneg_right h5 (sq_nonneg Q)
          calc 25 * C₀ ^ 2 * (D * Q) ^ 2 = (5 * C₀ * D) ^ 2 * Q ^ 2 := by ring
            _ ≤ (p : ℝ) ^ 2 * Q ^ 2 := this
            _ = 1 * (Q * Q * (p : ℝ) ^ 2) := by ring
  exact (pow_le_pow_iff_left₀ hΦ0 (inv_nonneg.2 (mul_pos hD0 hQ0).le) two_ne_zero).1 hb2

/-- The product `∏_s X_{k_s}^{#_s}` of (6.37) lies in the class `𝒜` of (6.4), is integrable,
and satisfies `𝔼[1_A ∏_s |X_{k_s}|] ≤ P(A)^{1/2} N^{2p}` (the bound (6.40), from Lemma 6.7). -/
private lemma main_F {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {z : ℂ} (hz : 0 < z.im)
    (hη : 1 / N ≤ z.im) {p : ℕ} (hp1 : 1 ≤ p) (h20 : 3 * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹) ≤ N)
    (κ : Fin p → Fin N) :
    PolyGrowth (fun x : Pair N → 𝕜 =>
        ∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))) ∧
      (∀ A : Set (Pair N → 𝕜),
        ∫⁻ x in A, ‖∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))‖ₑ ∂M.prodLaw ≤
          M.prodLaw A ^ (1 / 2 : ℝ) * ENNReal.ofReal ((N : ℝ) ^ (2 * p))) ∧
      Integrable (fun x : Pair N → 𝕜 =>
        ∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))) M.prodLaw := by
  have hX : ∀ k : Fin N, Continuous (fun x : Pair N → 𝕜 => selfX (toMatrix x) M.varMatrix z k) ∧
      PolyGrowth (fun x : Pair N → 𝕜 => selfX (toMatrix x) M.varMatrix z k) :=
    fun k => (polyGrowth_schurM M 0 hz ∅).2.2.2.2.1 k
  have hpoly : PolyGrowth (fun x : Pair N → 𝕜 =>
      ∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))) := by
    have h := Finset.prod_induction (s := Finset.univ)
      (fun s : Fin p => fun x : Pair N → 𝕜 => main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s)))
      PolyGrowth (fun f g hf hg => hf.mul hg) ⟨measurable_const, 1, 0, fun x => by simp⟩
      (fun s _ => by
        unfold main_sig
        split_ifs
        · exact (hX _).2.conj
        · simpa using (hX _).2)
    convert h using 1
    funext x
    simp [Finset.prod_apply]
  have hcont : Continuous (fun x : Pair N → 𝕜 =>
      ∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))) :=
    continuous_finsetProd _ fun s _ => (main_continuous_sig s).comp (hX _).1
  have hnorm : ∀ x : Pair N → 𝕜,
      ‖∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))‖ₑ =
        ∏ s, ‖selfX (toMatrix x) M.varMatrix z (κ s)‖ₑ := by
    intro x
    rw [← ofReal_norm, norm_prod,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
    exact Finset.prod_congr rfl fun s _ => by rw [main_norm_sig, ofReal_norm]
  have hA : ∀ A : Set (Pair N → 𝕜),
      ∫⁻ x in A, ‖∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s))‖ₑ ∂M.prodLaw ≤
        M.prodLaw A ^ (1 / 2 : ℝ) * ENNReal.ofReal ((N : ℝ) ^ (2 * p)) := by
    intro A
    simp_rw [hnorm]
    have h := main_setLIntegral_prod_le M.prodLaw hp1
      (fun s x => selfX (toMatrix x) M.varMatrix z (κ s))
      (fun s => (hX _).1.aestronglyMeasurable) (sq_nonneg (N : ℝ))
      (fun s => (faCrude M hM hϑ hϑ1 hη (κ s)).2 p hp1 h20) A
    rwa [← pow_mul] at h
  refine ⟨hpoly, hA, hcont.aestronglyMeasurable, ?_⟩
  have h := hA Set.univ
  rw [Measure.restrict_univ, measure_univ, ENNReal.one_rpow, one_mul] at h
  exact h.trans_lt ENNReal.ofReal_lt_top

/-- (6.38)–(6.40) and Step 3 of §6.7 for one index tuple `𝐤` with `ℓ = ℓ(𝐤)`:
`|𝔼 ∏_s X_{k_s}^{#_s}| ≤ 𝔼 (𝔭 Φ_*)^{p+ℓ} + N^{2p} P(Ξ_p(z)^c)^{1/2}`, `𝔭 = 48√2 C₀ p τ`. -/
private lemma main_tuple {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) {z : ℂ}
    (hz : 0 < z.im) (hη : 1 / N ≤ z.im) {p : ℕ} (hp2 : 2 ≤ p) (hpe : Even p) (hN8 : 8 ≤ N)
    (hlog : Real.log N ≤ p) (hpN : p < N) (h12 : 12 * C₀ * p ≤ N)
    (h20 : 3 * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹) ≤ N)
    (hsub : ∀ L : Finset (Fin N), 1 ≤ L.card → L.card ≤ p →
      aprioriEvent N p z ⊆ faXiL M C₀ ϑ⁻¹ p L z)
    (κ : Fin p → Fin N) :
    ‖∫ x, ∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s)) ∂M.prodLaw‖ₑ ≤
      ∫⁻ x, ENNReal.ofReal ((48 * √2 * C₀ * p * faTau ϑ⁻¹ p * √(phiStarSq p x z)) ^
          (p + loneCount κ)) ∂M.prodLaw +
        ENNReal.ofReal ((N : ℝ) ^ (2 * p)) * M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ) := by
  set L := Finset.univ.image κ with hL
  have hp1 : 1 ≤ p := by omega
  have hL1 : 1 ≤ L.card :=
    Finset.card_pos.2 (Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩ |>.image κ)
  have hLp : L.card ≤ p := Finset.card_image_le.trans (by simp)
  obtain ⟨hFp, hFA, hFi⟩ := main_F M hM hϑ hϑ1 hz hη hp1 h20 κ
  obtain ⟨hcl, hnd⟩ := faXiL_props M C₀ ϑ⁻¹ p L hz
  have hm := hcl.measurableSet
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hτ : 0 ≤ faTau ϑ⁻¹ p :=
    mul_nonneg (by linarith [main_one_le_faCm ha1]) (Real.rpow_nonneg (by positivity) _)
  have hρ : ∀ x : Pair N → 𝕜, 0 ≤ 8 * p * faRho C₀ ϑ⁻¹ p L z x ∧
      8 * p * faRho C₀ ϑ⁻¹ p L z x ≤ 48 * √2 * C₀ * p * faTau ϑ⁻¹ p * √(phiStarSq p x z) := by
    intro x
    obtain ⟨⟨-, ha⟩, -, -⟩ := faEvent_bounds M hM hp1 h12 hL1 hLp hz x
    have hΦ0 : 0 ≤ phiL C₀ L z x :=
      add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
    have hΦ : phiL C₀ L z x ≤ √2 * C₀ * √(phiStarSq p x z) := by
      have e : √2 * C₀ * √(phiStarSq p x z) = √(2 * C₀ ^ 2 * phiStarSq p x z) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by linarith)]
      rw [e]
      exact (le_abs_self _).trans (Real.abs_le_sqrt ha)
    unfold faRho
    refine ⟨mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) hτ) hΦ0), ?_⟩
    calc 8 * (p : ℝ) * (6 * faTau ϑ⁻¹ p * phiL C₀ L z x)
        = 48 * p * faTau ϑ⁻¹ p * phiL C₀ L z x := by ring
      _ ≤ 48 * p * faTau ϑ⁻¹ p * (√2 * C₀ * √(phiStarSq p x z)) :=
          mul_le_mul_of_nonneg_left hΦ (mul_nonneg (by positivity) hτ)
      _ = 48 * √2 * C₀ * p * faTau ϑ⁻¹ p * √(phiStarSq p x z) := by ring
  rw [← integral_add_compl hm hFi, integral_indicator_rowInt M hM hϑ L hm hnd hFp]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (enorm_integral_le_lintegral_enorm _).trans
      ((setLIntegral_mono' hm fun x hx => ?_).trans (setLIntegral_le_lintegral _ _))
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal
      ((faTuple M hM hϑ hϑ1 hp2 hpe hN8 hlog hpN hη κ hx).trans ?_)
    exact pow_le_pow_left₀ (hρ x).1 (hρ x).2 _
  · refine (enorm_integral_le_lintegral_enorm _).trans ((hFA _).trans ?_)
    rw [mul_comm]
    gcongr
    exact hsub L hL1 hLp

end MainHelpers

/-- Theorem 6.1: fluctuation averaging. -/
theorem fluctuationAveraging {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδp : 0 < δp) (hC₀ : 1 ≤ C₀) :
    ∃ CF p₀ : ℝ, 0 < CF ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N,
      M.Assumptions ϑ δm δp C₀ → ∀ z : ℂ, ‖z‖ ≤ N → 1 / N ≤ z.im → z.im ≤ 10 →
      ∀ p : ℕ, Even p → Real.log N ≤ p → (p : ℝ) ≤ (N : ℝ) ^ (1 / (40 * ϑ⁻¹ + 40)) → p₀ ≤ p →
      (p : ℝ) ^ (12 * ϑ⁻¹ + 11) ≤ N * z.im → ∀ t : Fin N → ℂ, (∀ k, ‖t k‖ ≤ 1 / N) →
        ∫⁻ x, ‖∑ k, t k * selfX (toMatrix x) M.varMatrix z k‖ₑ ^ p ∂M.prodLaw ≤
          ENNReal.ofReal ((CF * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p) *
              ∫⁻ x, ENNReal.ofReal (phiStarSq p x z) ^ p ∂M.prodLaw +
            ENNReal.ofReal ((N : ℝ) ^ (2 * p)) *
              M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ) := by
  classical
  have _ := hδm
  have _ := hδp
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hCm := main_one_le_faCm ha1
  have hC₀0 : 0 < C₀ := by linarith
  -- the constant `C_F = 2 B²` of (6.35), `B = 48√2 C₀ C_m 9^{2a+1}`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 48 * √2 * C₀ * faCm ϑ⁻¹ * 9 ^ (2 * ϑ⁻¹ + 1) := ⟨_, rfl⟩
  have hB0 : 0 < B := hB ▸ mul_pos (mul_pos (mul_pos (by positivity) hC₀0) (by linarith))
    (by positivity)
  refine ⟨2 * B ^ 2, 25 * Real.exp 1 * C₀ * faCm ϑ⁻¹ * 13 ^ (2 * ϑ⁻¹ + 3 / 2), by positivity, ?_⟩
  -- the conditions (6.36) on `N`
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((main_eventually_le (12 * C₀) (α := 1 / 80) (by norm_num)).and
      ((main_eventually_le (3 * (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹)) (α := 1 / 20) (by norm_num)).and
        (eventually_ge_atTop 8)))
  refine ⟨N₀, fun N hN M hM z hzN hη hη10 p hpe hlog hpN hp₀ hNη t ht => ?_⟩
  have _ := hzN
  obtain ⟨h80, h20N, hN8⟩ := hN₀ N hN
  -- consequences of (6.1) and (6.36), as in the first paragraph of the proof in §6.7
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hp25 : (25 : ℝ) ≤ p := by
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (1 : ℝ) ≤ 13 ^ (2 * ϑ⁻¹ + 3 / 2) := Real.one_le_rpow (by norm_num) (by linarith)
    have h3 : 1 ≤ Real.exp 1 * C₀ * faCm ϑ⁻¹ * 13 ^ (2 * ϑ⁻¹ + 3 / 2) :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 hC₀) hCm) h2
    calc (25 : ℝ) = 25 * 1 := by ring
      _ ≤ 25 * (Real.exp 1 * C₀ * faCm ϑ⁻¹ * 13 ^ (2 * ϑ⁻¹ + 3 / 2)) := by gcongr
      _ = 25 * Real.exp 1 * C₀ * faCm ϑ⁻¹ * 13 ^ (2 * ϑ⁻¹ + 3 / 2) := by ring
      _ ≤ p := hp₀
  have hp2 : 2 ≤ p := by exact_mod_cast (show (2 : ℝ) ≤ p by linarith)
  have hp1 : 1 ≤ p := by omega
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp1
  have hpr1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp80 : (p : ℝ) ≤ (N : ℝ) ^ (1 / 80 : ℝ) :=
    hpN.trans (Real.rpow_le_rpow_of_exponent_le hN1
      (one_div_le_one_div_of_le (by norm_num) (by linarith)))
  have h12 : 12 * C₀ * p ≤ N := (mul_le_mul_of_nonneg_left hp80 (by linarith)).trans h80
  have hpN' : p < N := by
    have : (p : ℝ) < N := by nlinarith
    exact_mod_cast this
  have h20 : 3 * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹) ≤ N := by
    have hc0 : 0 ≤ 4 * cTheta ϑ⁻¹ := by unfold cTheta; linarith
    have hpow : (p : ℝ) ^ (2 * ϑ⁻¹) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
      calc (p : ℝ) ^ (2 * ϑ⁻¹) ≤ ((N : ℝ) ^ (1 / (40 * ϑ⁻¹ + 40))) ^ (2 * ϑ⁻¹) :=
            Real.rpow_le_rpow hpos.le hpN (by linarith)
        _ = (N : ℝ) ^ (1 / (40 * ϑ⁻¹ + 40) * (2 * ϑ⁻¹)) := (Real.rpow_mul hNr.le _ _).symm
        _ ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by linarith) (by norm_num)]
            linarith
    calc 3 * (4 * cTheta ϑ⁻¹ * p) ^ (2 * ϑ⁻¹)
        = 3 * (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * (p : ℝ) ^ (2 * ϑ⁻¹) := by
          rw [Real.mul_rpow hc0 hpos.le]
          ring
      _ ≤ 3 * (4 * cTheta ϑ⁻¹) ^ (2 * ϑ⁻¹) * (N : ℝ) ^ (1 / 20 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hc0 _))
      _ ≤ N := h20N
  have hpNη : (p : ℝ) ≤ N * z.im := by
    calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (p : ℝ) ^ (12 * ϑ⁻¹ + 11) := Real.rpow_le_rpow_of_exponent_le hpr1 (by linarith)
      _ ≤ N * z.im := hNη
  have hsub : ∀ L : Finset (Fin N), 1 ≤ L.card → L.card ≤ p →
      aprioriEvent N p z ⊆ faXiL M C₀ ϑ⁻¹ p L z := fun L hL1 hLp =>
    main_apriori_sub M hM hϑ hϑ1 hC₀ hz hη10 hp1 h12 hpNη hNη hp₀ hL1 hLp
  -- notation: `X_k`, the products `∏_s X_{k_s}^{#_s}`, the weights `∏_s t_{k_s}^{#_s}`, `𝔭 Φ_*`
  obtain ⟨F, hF⟩ : ∃ F : (Fin p → Fin N) → (Pair N → 𝕜) → ℂ,
      F = fun κ x => ∏ s, main_sig p s (selfX (toMatrix x) M.varMatrix z (κ s)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (Fin p → Fin N) → ℂ, c = fun κ => ∏ s, main_sig p s (t (κ s)) :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 48 * √2 * C₀ * p * faTau ϑ⁻¹ p := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (Pair N → 𝕜) → ℝ, y = fun x => P * √(phiStarSq p x z) := ⟨_, rfl⟩
  have hFi : ∀ κ, Integrable (F κ) M.prodLaw := fun κ => by
    rw [hF]
    exact (main_F M hM hϑ hϑ1 hz hη hp1 h20 κ).2.2
  have hT : ∀ κ, ‖∫ x, F κ x ∂M.prodLaw‖ₑ ≤
      ∫⁻ x, ENNReal.ofReal (y x ^ (p + loneCount κ)) ∂M.prodLaw +
        ENNReal.ofReal ((N : ℝ) ^ (2 * p)) * M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ) :=
    fun κ => by
      rw [hF, hy, hP]
      exact main_tuple M hM hϑ hϑ1 hC₀ hz hη hp2 hpe hN8 hlog hpN' h12 h20 hsub κ
  have hcκ : ∀ κ, ‖c κ‖ₑ ≤ ENNReal.ofReal (((1 : ℝ) / N) ^ p) := fun κ => by
    rw [hc, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_prod]
    calc ∏ s, ‖main_sig p s (t (κ s))‖ ≤ ∏ _s : Fin p, (1 : ℝ) / N :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            fun s _ => (main_norm_sig s _).trans_le (ht _)
      _ = ((1 : ℝ) / N) ^ p := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hexp : ∀ x : Pair N → 𝕜,
      ((‖∑ k, t k * selfX (toMatrix x) M.varMatrix z k‖ ^ p : ℝ) : ℂ) = ∑ κ, c κ * F κ x :=
    fun x => by
      rw [hc, hF]
      exact main_expand hpe t _
  have hGi : Integrable (fun x => ∑ κ, c κ * F κ x) M.prodLaw :=
    integrable_finsetSum _ fun κ _ => (hFi κ).const_mul (c κ)
  -- the pointwise bound of Step 4
  have hP1 : 1 ≤ P := by
    have h9 : (1 : ℝ) ≤ (9 * (p : ℝ) ^ 2) ^ (2 * ϑ⁻¹ + 1) :=
      Real.one_le_rpow (by nlinarith) (by linarith)
    have hτ1 : 1 ≤ faTau ϑ⁻¹ p := one_le_mul_of_one_le_of_one_le hCm h9
    have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
    rw [hP]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hs2) hC₀)
      hpr1) hτ1
  have hcf : 2 * p * P ^ 2 = 2 * B ^ 2 * (p : ℝ) ^ (8 * ϑ⁻¹ + 7) := by
    have h9 : (9 * (p : ℝ) ^ 2) ^ (2 * ϑ⁻¹ + 1) =
        9 ^ (2 * ϑ⁻¹ + 1) * (p : ℝ) ^ (2 * (2 * ϑ⁻¹ + 1)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (p : ℝ) 2,
        ← Real.rpow_mul hpos.le]
      norm_num
    have hp8 : (p : ℝ) ^ (8 * ϑ⁻¹ + 7) = (p : ℝ) ^ 3 * ((p : ℝ) ^ (2 * (2 * ϑ⁻¹ + 1))) ^ 2 := by
      rw [← Real.rpow_natCast ((p : ℝ) ^ (2 * (2 * ϑ⁻¹ + 1))) 2, ← Real.rpow_mul hpos.le,
        ← Real.rpow_natCast (p : ℝ) 3, ← Real.rpow_add hpos]
      congr 1
      push_cast
      ring
    rw [hP, hB, hp8]
    unfold faTau
    rw [h9]
    ring
  have hpt : ∀ x : Pair N → 𝕜, 0 ≤ phiStarSq p x z ∧ 0 ≤ y x ∧
      ∑ κ : Fin p → Fin N, ((1 : ℝ) / N) ^ p * y x ^ (p + loneCount κ) ≤
        (2 * B ^ 2 * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p * phiStarSq p x z ^ p := by
    intro x
    have hS := (faEvent_bounds M hM hp1 h12 (L := {⟨0, hNpos⟩}) (by simp) (by simp; omega)
      hz x).1.1
    have hS0 : 0 ≤ phiStarSq p x z := le_trans (by positivity) hS
    have hy0 : 0 ≤ y x := by rw [hy]; exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have hNS : 1 ≤ N * phiStarSq p x z := by
      have := mul_le_mul_of_nonneg_left hS hNr.le
      rwa [mul_one_div_cancel hNr.ne'] at this
    have hyN : 1 ≤ N * y x ^ 2 := by
      rw [hy]
      simp only
      rw [mul_pow, Real.sq_sqrt hS0]
      have : 1 ≤ P ^ 2 := one_le_pow₀ hP1
      nlinarith
    refine ⟨hS0, hy0, ?_⟩
    have h2p : ((p : ℝ) + 1) ≤ 2 ^ p := by exact_mod_cast Nat.lt_two_pow_self
    calc ∑ κ : Fin p → Fin N, ((1 : ℝ) / N) ^ p * y x ^ (p + loneCount κ)
        ≤ ((p : ℝ) + 1) * (p : ℝ) ^ p * y x ^ (2 * p) := main_sum_tuples hNpos hy0 hyN
      _ ≤ 2 ^ p * (p : ℝ) ^ p * y x ^ (2 * p) := by gcongr
      _ = (2 * p * P ^ 2) ^ p * phiStarSq p x z ^ p := by
          rw [hy]
          simp only
          rw [mul_pow P, pow_mul (√(phiStarSq p x z)), Real.sq_sqrt hS0]
          ring
      _ = (2 * B ^ 2 * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p * phiStarSq p x z ^ p := by rw [hcf]
  -- the chain (6.37)–(6.40), Step 4
  calc ∫⁻ x, ‖∑ k, t k * selfX (toMatrix x) M.varMatrix z k‖ₑ ^ p ∂M.prodLaw
      = ∫⁻ x, ‖∑ κ, c κ * F κ x‖ₑ ∂M.prodLaw := lintegral_congr fun x => by
        rw [← hexp x, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ = ENNReal.ofReal (∫ x, ‖∑ κ, c κ * F κ x‖ ∂M.prodLaw) :=
        (ofReal_integral_norm_eq_lintegral_enorm hGi).symm
    _ ≤ ‖∫ x, ∑ κ, c κ * F κ x ∂M.prodLaw‖ₑ := by
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : ∀ x, ‖∑ κ, c κ * F κ x‖ = RCLike.re (∑ κ, c κ * F κ x) := fun x => by
          rw [← hexp x, RCLike.re_to_complex, Complex.ofReal_re, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        simp_rw [e]
        rw [integral_re hGi]
        exact RCLike.re_le_norm _
    _ = ‖∑ κ, c κ * ∫ x, F κ x ∂M.prodLaw‖ₑ := by
        rw [integral_finsetSum _ fun κ _ => (hFi κ).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ ∑ κ, ‖c κ‖ₑ * ‖∫ x, F κ x ∂M.prodLaw‖ₑ :=
        (enorm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ => (enorm_mul _ _).le)
    _ ≤ ∑ κ, ENNReal.ofReal (((1 : ℝ) / N) ^ p) *
          (∫⁻ x, ENNReal.ofReal (y x ^ (p + loneCount κ)) ∂M.prodLaw +
            ENNReal.ofReal ((N : ℝ) ^ (2 * p)) *
              M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun κ _ => mul_le_mul' (hcκ κ) (hT κ)
    _ = ∑ κ, ENNReal.ofReal (((1 : ℝ) / N) ^ p) *
            ∫⁻ x, ENNReal.ofReal (y x ^ (p + loneCount κ)) ∂M.prodLaw +
          ∑ _κ : Fin p → Fin N, ENNReal.ofReal (((1 : ℝ) / N) ^ p) *
            (ENNReal.ofReal ((N : ℝ) ^ (2 * p)) *
              M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ)) := by
        simp_rw [mul_add]
        exact Finset.sum_add_distrib
    _ ≤ ENNReal.ofReal ((2 * B ^ 2 * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p) *
            ∫⁻ x, ENNReal.ofReal (phiStarSq p x z) ^ p ∂M.prodLaw +
          ENNReal.ofReal ((N : ℝ) ^ (2 * p)) *
            M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ) := by
        gcongr ?_ + ?_
        · calc ∑ κ, ENNReal.ofReal (((1 : ℝ) / N) ^ p) *
                ∫⁻ x, ENNReal.ofReal (y x ^ (p + loneCount κ)) ∂M.prodLaw
              ≤ ∑ κ, ∫⁻ x, ENNReal.ofReal (((1 : ℝ) / N) ^ p) *
                  ENNReal.ofReal (y x ^ (p + loneCount κ)) ∂M.prodLaw :=
                Finset.sum_le_sum fun κ _ => lintegral_const_mul_le _ _
            _ ≤ ∫⁻ x, ∑ κ, ENNReal.ofReal (((1 : ℝ) / N) ^ p) *
                  ENNReal.ofReal (y x ^ (p + loneCount κ)) ∂M.prodLaw :=
                main_sum_lintegral_le _ _ _
            _ ≤ ∫⁻ x, ENNReal.ofReal ((2 * B ^ 2 * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p) *
                  ENNReal.ofReal (phiStarSq p x z) ^ p ∂M.prodLaw := by
                refine lintegral_mono fun x => ?_
                obtain ⟨hS0, hy0, hb⟩ := hpt x
                rw [← ENNReal.ofReal_pow hS0, ← ENNReal.ofReal_mul (by positivity)]
                simp_rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((1 : ℝ) / N) ^ p)]
                rw [← ENNReal.ofReal_sum_of_nonneg
                  (fun κ _ => mul_nonneg (by positivity) (pow_nonneg hy0 _))]
                exact ENNReal.ofReal_le_ofReal hb
            _ = ENNReal.ofReal ((2 * B ^ 2 * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p) *
                  ∫⁻ x, ENNReal.ofReal (phiStarSq p x z) ^ p ∂M.prodLaw :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        · have hcard : (Fintype.card (Fin p → Fin N) : ℝ≥0∞) *
              ENNReal.ofReal (((1 : ℝ) / N) ^ p) = 1 := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            push_cast
            rw [← mul_pow, mul_one_div_cancel hNr.ne', one_pow, ENNReal.ofReal_one]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcard, one_mul]

end Rigidity
