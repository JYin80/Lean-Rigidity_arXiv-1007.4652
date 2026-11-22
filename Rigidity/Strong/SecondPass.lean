module

public import Rigidity.Strong.Lattice

@[expose] public section

/-!
# The improved averaged law, near regime (NP v1.1, §7.3: Proposition 7.3)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `𝒢³(z)`: the points of `𝒢²(z)` at which the improved bound (7.4) of Proposition 7.3 holds. -/
def strongG3 {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  strongG2 M a C₀ K z ∩
    {x | Lam x z ≤ K ^ (ledgerB a + 2) *
      ((msc z).im / (varkappa z * (N * z.im)) + 1 / (varkappa z * (N * z.im) ^ 2))}

/-! The proof of Proposition 7.3 follows its three steps, with `u = Nη`, `w = m - m_sc`,
`w₀ = m_sc (1 - m_sc²)`, `𝔉` replaced by its bound `K^{12a+11}` of (T1), and
`S = Im m_sc/u + 1/u²`. Where the original paper (Erdős–Yau–Yin, arXiv:1007.4652) has a
counterpart, it is cited as [EYY, …].

* Step 1 (`secondPass_step1`), (7.e): on `𝒢²(z)`, Proposition 7.2 (a) gives `Λ ≤ |w₀|/4`, and
  (5.4) of Lemma 5.1 then gives `Λ ≤ (7000/ϰ)(|⟨X⟩| + 𝔈₀ S)`.
* Step 2: `Y₂ = ‖Λ 1_{𝒢²(z)}‖_p` at `p = p₂` is finite (`Λ ≤ 2N`, (T4)); Corollary 6.2,
  Proposition 7.2 and (T6) bound it, and the term with `Y₂` is absorbed because
  `ϰ N η ≥ K^{b+3}`. This gives `Y₂ ≤ 28000 K^b S/ϰ`.
* Step 3: Markov's inequality at `p₂` and `28000 e ≤ K²`. -/

/-! ### 1. Continuity -/

/-- For `Im z > 0`, the diagonal resolvent entries `x ↦ G_kk(z)` are continuous. -/
private lemma secondPass_continuous_green {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im)
    (k : Fin N) : Continuous fun x : Pair N → 𝕜 => green (toMatrix x) z k k := by
  have h := ((polyGrowth_schurM M 0 hz ∅).2.2.2.1 k).1
  have hne : ∀ x : Pair N → 𝕜, 1 / green (toMatrix x) z k k ≠ 0 := fun x => by
    have := green_im_diag_pos (toMatrix_isHermitian x) hz k
    refine one_div_ne_zero fun h0 => ?_
    rw [h0, Complex.zero_im] at this
    exact lt_irrefl _ this
  refine (h.inv₀ hne).congr fun x => ?_
  change (1 / green (toMatrix x) z k k)⁻¹ = _
  rw [one_div, inv_inv]

/-- `m = N⁻¹ ∑ᵢ G_ii`. -/
private lemma secondPass_stieltjes_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (z : ℂ) :
    stieltjesEmp A z = (N : ℂ)⁻¹ * ∑ i, green A z i i := by
  simp only [stieltjesEmp, Fintype.card_fin, Matrix.trace, Matrix.diag]

/-- For `Im z > 0`, `x ↦ m(z)` is continuous. -/
private lemma secondPass_continuous_stieltjes {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ}
    (hz : 0 < z.im) : Continuous fun x : Pair N → 𝕜 => stieltjesEmp (toMatrix x) z := by
  simp only [secondPass_stieltjes_eq]
  exact continuous_const.mul
    (continuous_finsetSum _ fun k _ => secondPass_continuous_green M hz k)

/-- For `Im z > 0`, `x ↦ Λ(z)` is continuous. -/
private lemma secondPass_continuous_Lam {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun x : Pair N → 𝕜 => Lam x z :=
  ((secondPass_continuous_stieltjes M hz).sub continuous_const).norm

/-! ### 2. Step 1: the pointwise bound (7.e) -/

/-- `|w² - w₀ w| ≥ |w| (|w₀| - |w|)`. -/
private lemma secondPass_norm_ge (w w₀ : ℂ) : ‖w‖ * (‖w₀‖ - ‖w‖) ≤ ‖w ^ 2 - w₀ * w‖ := by
  have e : w ^ 2 - w₀ * w = w * (w - w₀) := by ring
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_sub_rev]
  exact norm_sub_norm_le w₀ w

/-- The arithmetic of Step 1, (7.e): if `Λ ≤ W/4`, `Λ (W - Λ) ≤ X + 𝔈₀ ((I + Λ)/u + 1/u²) + ¾Λ²`,
`𝔈₀/u ≤ W/32` and `W ≥ ϰ/1950`, then `Λ ≤ (7000/ϰ) X + (7000/ϰ) 𝔈₀ (I/u + 1/u²)`. -/
private lemma secondPass_step1 {Λ W X E₀ I u ϰ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛW : Λ ≤ W / 4)
    (hQ : Λ * (W - Λ) ≤ X + E₀ * ((I + Λ) / u + 1 / u ^ 2) + 3 / 4 * Λ ^ 2)
    (hE₀u : E₀ / u ≤ W / 32) (hϰ : 0 < ϰ) (hW : ϰ / 1950 ≤ W) (hX : 0 ≤ X) (hE₀ : 0 ≤ E₀)
    (hI : 0 ≤ I) (hu : 0 < u) :
    Λ ≤ 7000 / ϰ * X + 7000 / ϰ * E₀ * (I / u + 1 / u ^ 2) := by
  have hR : 0 ≤ X + E₀ * (I / u + 1 / u ^ 2) := by positivity
  have e1 : E₀ * ((I + Λ) / u + 1 / u ^ 2) = E₀ * (I / u + 1 / u ^ 2) + E₀ / u * Λ := by ring
  have e2 : E₀ / u * Λ ≤ W / 32 * Λ := mul_le_mul_of_nonneg_right hE₀u hΛ0
  have e3 : Λ * Λ ≤ W / 4 * Λ := mul_le_mul_of_nonneg_right hΛW hΛ0
  have e4 : ϰ / 1950 * Λ ≤ W * Λ := mul_le_mul_of_nonneg_right hW hΛ0
  have e5 : Λ * (W - Λ) = W * Λ - Λ * Λ := by ring
  have e6 : Λ ^ 2 = Λ * Λ := by ring
  have hmain : 17 / 32 * (W * Λ) ≤ X + E₀ * (I / u + 1 / u ^ 2) := by
    rw [e5, e1, e6] at hQ
    linarith
  have e7 : 7000 / ϰ * X + 7000 / ϰ * E₀ * (I / u + 1 / u ^ 2) =
      7000 * (X + E₀ * (I / u + 1 / u ^ 2)) / ϰ := by ring
  rw [e7, le_div_iff₀ hϰ]
  nlinarith

/-! ### 3. Steps 2 and 3: absorption and Markov's inequality -/

/-- If `‖f‖ ≤ a ‖h‖ + c` pointwise, then `‖f‖_p ≤ a ‖h‖_p + c` for `p ≥ 1` and a probability
measure. -/
private lemma secondPass_eLpNorm_le {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedAddCommGroup F] {μ : Measure α} [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : α → E} {h : α → F} (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hle : ∀ x, ‖f x‖ ≤ a * ‖h x‖ + c) :
    eLpNorm f p μ ≤ ENNReal.ofReal a * eLpNorm h p μ + ENNReal.ofReal c := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have e : (fun x => a * ‖h x‖ + c) = (a • fun x => ‖h x‖) + fun _ => c := by
    funext x
    simp [smul_eq_mul]
  calc eLpNorm f p μ ≤ eLpNorm (fun x => a * ‖h x‖ + c) p μ := eLpNorm_mono_real hf hle
    _ = eLpNorm ((a • fun x => ‖h x‖) + fun _ => c) p μ := by rw [e]
    _ ≤ eLpNorm (a • fun x => ‖h x‖) p μ + eLpNorm (fun _ => c) p μ := eLpNorm_add_le hp
    _ = ENNReal.ofReal a * eLpNorm h p μ + ENNReal.ofReal c := by
      rw [eLpNorm_const_smul, eLpNorm_norm h hh, eLpNorm_const c hp0 (NeZero.ne μ), measure_univ,
        ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg ha, Real.enorm_of_nonneg hc]

/-- The absorption of Step 2: from `Y ≤ A ‖⟨X⟩‖_p + c₁`, `‖⟨X⟩‖_p ≤ 𝔉 ‖Φ_*²‖_p + N⁻⁸`,
`‖Φ_*²‖_p ≤ ‖Λ‖_p/u + c₂`, `‖Λ‖_p ≤ Y + N⁻⁸`, `Y < ∞` and `2 A 𝔉 ≤ u`, one gets
`Y ≤ N⁻⁸ + 2 A N⁻⁸ + 2 A 𝔉 c₂ + 2 c₁`. -/
private lemma secondPass_absorb {Y Xn Φn Λn : ℝ≥0∞} {A F u n8 c₁ c₂ : ℝ}
    (h1 : Y ≤ ENNReal.ofReal A * Xn + ENNReal.ofReal c₁)
    (h2 : Xn ≤ ENNReal.ofReal F * Φn + ENNReal.ofReal n8)
    (h3 : Φn ≤ ENNReal.ofReal (1 / u) * Λn + ENNReal.ofReal c₂)
    (h4 : Λn ≤ Y + ENNReal.ofReal n8) (hY : Y ≠ ⊤) (hA : 0 ≤ A) (hF : 0 ≤ F) (hu : 0 < u)
    (hAF : 2 * (A * F) ≤ u) (hn8 : 0 ≤ n8) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    Y.toReal ≤ n8 + 2 * A * n8 + 2 * A * F * c₂ + 2 * c₁ := by
  set y := Y.toReal with hy
  have hYe : Y = ENNReal.ofReal y := (ENNReal.ofReal_toReal hY).symm
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hu1 : 0 ≤ 1 / u := by positivity
  have hc : ENNReal.ofReal y ≤ ENNReal.ofReal A * (ENNReal.ofReal F *
      (ENNReal.ofReal (1 / u) * (ENNReal.ofReal y + ENNReal.ofReal n8) + ENNReal.ofReal c₂) +
        ENNReal.ofReal n8) + ENNReal.ofReal c₁ := by
    rw [← hYe]
    calc Y ≤ ENNReal.ofReal A * Xn + ENNReal.ofReal c₁ := h1
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal F * Φn + ENNReal.ofReal n8) +
          ENNReal.ofReal c₁ := by gcongr
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal F *
          (ENNReal.ofReal (1 / u) * Λn + ENNReal.ofReal c₂) + ENNReal.ofReal n8) +
            ENNReal.ofReal c₁ := by gcongr
      _ ≤ _ := by gcongr
  rw [← ENNReal.ofReal_add hy0 hn8, ← ENNReal.ofReal_mul hu1,
    ← ENNReal.ofReal_add (by positivity) hc₂, ← ENNReal.ofReal_mul hF,
    ← ENNReal.ofReal_add (by positivity) hn8, ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_add (by positivity) hc₁, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hc
  have e : A * (F * (1 / u * (y + n8))) ≤ (y + n8) / 2 := by
    have e0 : A * (F * (1 / u * (y + n8))) = (A * F) * (y + n8) / u := by ring
    rw [e0, div_le_div_iff₀ hu (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hAF (by positivity : (0 : ℝ) ≤ y + n8)]
  have e' : A * (F * (1 / u * (y + n8) + c₂) + n8) + c₁ =
      A * (F * (1 / u * (y + n8))) + A * F * c₂ + A * n8 + c₁ := by ring
  rw [e'] at hc
  linarith

/-- Markov's inequality in the form of Step 3: if `‖f‖_p ≤ B` and `e B ≤ t`, `t > 0`, then
`ℙ(|f| ≥ t) ≤ e^{-p}`. -/
private lemma secondPass_markov {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {p : ℕ} (hp : p ≠ 0) {t B : ℝ} (ht0 : 0 < t) (ht : Real.exp 1 * B ≤ t)
    (hY : eLpNorm f p μ ≤ ENNReal.ofReal B) :
    μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} ≤ ENNReal.ofReal (Real.exp (-(p : ℝ))) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp
  have hpr : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hBt : t⁻¹ * B ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_mul_le_iff₀ ht0]
    calc B = (Real.exp 1)⁻¹ * (Real.exp 1 * B) := by field_simp
      _ ≤ (Real.exp 1)⁻¹ * t := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = t * (Real.exp 1)⁻¹ := mul_comm _ _
  calc μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ}
      ≤ (ENNReal.ofReal t)⁻¹ ^ (p : ℝ≥0∞).toReal * eLpNorm f p μ ^ (p : ℝ≥0∞).toReal :=
        meas_ge_le_mul_pow_eLpNorm_enorm μ hp0 (ENNReal.natCast_ne_top p)
          (ENNReal.ofReal_pos.2 ht0).ne' fun h => absurd h ENNReal.ofReal_ne_top
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ (p : ℝ) * ENNReal.ofReal B ^ (p : ℝ) := by
        rw [ENNReal.toReal_natCast]
        gcongr
    _ = ENNReal.ofReal (t⁻¹ * B) ^ (p : ℝ) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hpr, ← ENNReal.ofReal_inv_of_pos ht0,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (Real.exp (-1)) ^ (p : ℝ) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(p : ℝ))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hpr, ← Real.exp_mul]
        ring_nf

/-- Step 2 in `L^p` form: if `0 ≤ Λ ≤ C`, `Λ ≤ A |X| + c₁` on `G`, `|Φ| ≤ Λ/u + c₂`,
`‖X‖_p ≤ 𝔉 ‖Φ‖_p + n₈`, `C ℙ(Gᶜ)^{1/p} ≤ n₈` and `2 A 𝔉 ≤ u`, then `Y = ‖Λ 1_G‖_p` is finite
and `Y ≤ n₈ + 2 A n₈ + 2 A 𝔉 c₂ + 2 c₁`. -/
private lemma secondPass_moment {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {p : ℕ} (hp : 1 ≤ p) {G : Set α} (hG : MeasurableSet G)
    {Λf Φf : α → ℝ} {Xf : α → ℂ} (hΛm : AEStronglyMeasurable Λf μ)
    (hXm : AEStronglyMeasurable Xf μ) (hΦm : AEStronglyMeasurable Φf μ) {A C F u n8 c₁ c₂ : ℝ}
    (hΛ0 : ∀ x, 0 ≤ Λf x) (hΛC : ∀ x, Λf x ≤ C) (hpt : ∀ x ∈ G, Λf x ≤ A * ‖Xf x‖ + c₁)
    (hΦ : ∀ x, ‖Φf x‖ ≤ 1 / u * ‖Λf x‖ + c₂)
    (hX : eLpNorm Xf p μ ≤ ENNReal.ofReal F * eLpNorm Φf p μ + ENNReal.ofReal n8)
    (hT6 : ENNReal.ofReal C * μ Gᶜ ^ (1 / (p : ℝ)) ≤ ENNReal.ofReal n8) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (hu : 0 < u) (hAF : 2 * (A * F) ≤ u) (hn8 : 0 ≤ n8)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    eLpNorm (G.indicator Λf) p μ ≠ ⊤ ∧
      (eLpNorm (G.indicator Λf) p μ).toReal ≤ n8 + 2 * A * n8 + 2 * A * F * c₂ + 2 * c₁ := by
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hfm : AEStronglyMeasurable (G.indicator Λf) μ := hΛm.indicator hG
  have hfC : ∀ x, ‖G.indicator Λf x‖ ≤ C := fun x => by
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (hΛ0 x)]
      exact hΛC x
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact hC
  have hfin : eLpNorm (G.indicator Λf) p μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C))
      ((eLpNorm_le_of_ae_bound hfm (Eventually.of_forall hfC)).trans ?_)
    rw [measure_univ, ENNReal.one_rpow, one_mul]
  refine ⟨hfin, secondPass_absorb (Λn := eLpNorm Λf p μ) ?_ hX ?_ ?_ hfin hA hF hu hAF hn8 hc₁
    hc₂⟩
  · refine secondPass_eLpNorm_le hp1 hfm hXm hA hc₁ fun x => ?_
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (hΛ0 x)]
      exact hpt x hx
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  · exact secondPass_eLpNorm_le hp1 hΦm hΛm (by positivity) hc₂ hΦ
  · have hc : eLpNorm (Gᶜ.indicator Λf) p μ ≤ ENNReal.ofReal n8 := by
      calc eLpNorm (Gᶜ.indicator Λf) p μ ≤ eLpNorm (Gᶜ.indicator fun _ => C) p μ := by
            refine eLpNorm_mono_real (hΛm.indicator hG.compl) fun x => ?_
            by_cases hx : x ∈ Gᶜ
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Real.norm_of_nonneg (hΛ0 x)]
              exact hΛC x
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
        _ = ENNReal.ofReal C * μ Gᶜ ^ (1 / (p : ℝ)) := by
            rw [eLpNorm_indicator_const hG.compl.nullMeasurableSet hp0 (ENNReal.natCast_ne_top _),
              Real.enorm_of_nonneg hC, ENNReal.toReal_natCast]
        _ ≤ ENNReal.ofReal n8 := hT6
    calc eLpNorm Λf p μ = eLpNorm (G.indicator Λf + Gᶜ.indicator Λf) p μ := by
          rw [Set.indicator_self_add_compl]
      _ ≤ eLpNorm (G.indicator Λf) p μ + eLpNorm (Gᶜ.indicator Λf) p μ := eLpNorm_add_le hp1
      _ ≤ _ := by gcongr

/-- The pointwise bound of Step 2: `|Φ_*²| ≤ Λ/u + 1/N + Im m_sc/u + p/u²` with `u = Nη`, from
`|Im m - Im m_sc| ≤ Λ`. -/
private lemma secondPass_phi_le {N : ℕ} (hN : 0 < N) (x : Pair N → 𝕜) {z : ℂ} (hz : 0 < z.im)
    {p : ℝ} (hp : 0 ≤ p) :
    ‖phiStarSq p x z‖ ≤ 1 / (N * z.im) * ‖Lam x z‖ +
      (1 / N + (msc z).im / (N * z.im) + p / (N * z.im) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 < (N : ℝ) * z.im := by positivity
  have hI := Complex.abs_im_le_norm (stieltjesEmp (toMatrix x) z - msc z)
  rw [Complex.sub_im] at hI
  have hΛx : ‖stieltjesEmp (toMatrix x) z - msc z‖ = Lam x z := rfl
  rw [hΛx] at hI
  have hΛ0 : 0 ≤ Lam x z := norm_nonneg _
  rw [Real.norm_of_nonneg hΛ0, Real.norm_eq_abs]
  unfold phiStarSq
  set u := (N : ℝ) * z.im
  set m := (stieltjesEmp (toMatrix x) z).im
  have hu1 : 0 < 1 / u := by positivity
  have e1 : 1 / u * (p / u) = p / u ^ 2 := by field_simp
  have e2 : 1 / u * (msc z).im = (msc z).im / u := by ring
  have hlo := abs_le.1 hI
  have hpu : 0 ≤ p / u := by positivity
  have hmsc := (msc_im_pos hz).le
  have hn : 0 ≤ 1 / (N : ℝ) := by positivity
  have hpu2 : 0 ≤ p / u ^ 2 := by positivity
  have hmu : 0 ≤ (msc z).im / u := by positivity
  have h1 : 1 / u * (-(Lam x z)) ≤ 1 / u * (m + p / u) :=
    mul_le_mul_of_nonneg_left (by linarith) hu1.le
  have h2 : 1 / u * (m + p / u) ≤ 1 / u * ((msc z).im + Lam x z + p / u) :=
    mul_le_mul_of_nonneg_left (by linarith) hu1.le
  have e3 : 1 / u * ((msc z).im + Lam x z + p / u) =
      (msc z).im / u + 1 / u * Lam x z + p / u ^ 2 := by rw [← e1, ← e2]; ring
  have e4 : 1 / u * (-(Lam x z)) = -(1 / u * Lam x z) := by ring
  rw [abs_le]
  constructor <;> linarith

/-- The final constant of Step 2: with `c₂ ≤ (K + 151) S`, `n₈ ≤ S`, `0 < ϰ ≤ 4`, `𝔈₀ ≤ 𝔉`,
`1 ≤ 𝔉` and `K ≥ 1000`,
`n₈ + 2 (7000/ϰ) n₈ + 2 (7000/ϰ) 𝔉 c₂ + 2 (7000/ϰ) 𝔈₀ S ≤ 28000 𝔉 K S/ϰ`. -/
private lemma secondPass_const {n8 F c₂ E₀ S K ϰ : ℝ} (hc₂ : c₂ ≤ (K + 151) * S)
    (hn80 : 0 ≤ n8) (hn8 : n8 ≤ S) (hϰ : 0 < ϰ) (hϰ4 : ϰ ≤ 4) (hE₀ : E₀ ≤ F) (hF : 1 ≤ F)
    (hK : 1000 ≤ K) (hS : 0 ≤ S) :
    n8 + 2 * (7000 / ϰ) * n8 + 2 * (7000 / ϰ) * F * c₂ + 2 * (7000 / ϰ * E₀ * S) ≤
      28000 * (F * K) * S / ϰ := by
  have e : n8 + 2 * (7000 / ϰ) * n8 + 2 * (7000 / ϰ) * F * c₂ + 2 * (7000 / ϰ * E₀ * S) =
      (ϰ * n8 + 14000 * n8 + 14000 * (F * c₂) + 14000 * (E₀ * S)) / ϰ := by
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hϰ.le
  have h1 : ϰ * n8 ≤ 4 * S := mul_le_mul hϰ4 hn8 hn80 (by norm_num)
  have h2 : F * c₂ ≤ F * ((K + 151) * S) := mul_le_mul_of_nonneg_left hc₂ (by linarith)
  have h3 : E₀ * S ≤ F * S := mul_le_mul_of_nonneg_right hE₀ hS
  have h4 : S ≤ F * S := le_mul_of_one_le_left hS hF
  have h5 : 1000 * (F * S) ≤ K * (F * S) := mul_le_mul_of_nonneg_right hK (by positivity)
  nlinarith

/-- The numerical facts on the powers of `K` used in the proof, for `a ≥ 1` and `K ≥ 1000`, with
`𝔉 = K^{12a+11}`: `𝔉 K = K^b`, `𝔉 K⁴ = K^{b+3}`, `K^{b+2} = K^b K²`, `K^{8a+7} ≤ 𝔉`,
`62400 K^{8a+7} ≤ K^{b+3}` and `1 ≤ 𝔉`. -/
private lemma secondPass_powers {a K : ℝ} (ha : 1 ≤ a) (hK : 1000 ≤ K) :
    K ^ (12 * a + 11) * K = K ^ ledgerB a ∧ K ^ (12 * a + 11) * K ^ 4 = K ^ (ledgerB a + 3) ∧
      K ^ (ledgerB a + 2) = K ^ ledgerB a * K ^ 2 ∧ K ^ (8 * a + 7) ≤ K ^ (12 * a + 11) ∧
      62400 * K ^ (8 * a + 7) ≤ K ^ (ledgerB a + 3) ∧ 1 ≤ K ^ (12 * a + 11) := by
  have hKpos : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  refine ⟨?_, ?_, ?_, Real.rpow_le_rpow_of_exponent_le hK1 (by linarith), ?_,
    Real.one_le_rpow hK1 (by linarith)⟩
  · rw [← Real.rpow_add_one hKpos.ne']
    unfold ledgerB
    congr 1
    ring
  · rw [← Real.rpow_natCast, ← Real.rpow_add hKpos]
    unfold ledgerB
    congr 1
    push_cast
    ring
  · rw [Real.rpow_add hKpos, Real.rpow_two]
  · have e : K ^ (ledgerB a + 3) = K ^ (8 * a + 7) * K ^ (4 * a + 8) := by
      rw [← Real.rpow_add hKpos]
      unfold ledgerB
      congr 1
      ring
    have h2 : K ^ (2 : ℝ) ≤ K ^ (4 * a + 8) := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
    rw [Real.rpow_two] at h2
    have h3 : (62400 : ℝ) ≤ K ^ 2 := by nlinarith
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_left (h3.trans h2) (by positivity)

/-- On `𝐃^near`, `ϰ ≤ 4`. -/
private lemma secondPass_varkappa_le {a K : ℝ} {N : ℕ} {z : ℂ} (hz : z ∈ Dnear a K N) :
    varkappa z ≤ 4 := by
  obtain ⟨hre, -, hη⟩ := hz
  unfold varkappa kappaE
  have h1 : |(|z.re| - 2)| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith [abs_nonneg z.re]
  have e : (4 : ℝ) = Real.sqrt (4 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  rw [e]
  exact Real.sqrt_le_sqrt (by linarith)

/-! ### 4. Proposition 7.3 -/

/-- Proposition 7.3: at `z ∈ 𝕃 ∩ 𝐃^near` with `ϰ N η ≥ K^{b+3}`, `𝒢³(z)` is closed and
`ℙ(𝒢²(z) ∖ 𝒢³(z)) ≤ e^{-p₂}`. -/
theorem strong_improved {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ lattice ϑ⁻¹ C₀ K N ∩ Dnear ϑ⁻¹ K N, K ^ (ledgerB ϑ⁻¹ + 3) ≤ varkappa z * (N * z.im) →
        IsClosed (strongG3 M ϑ⁻¹ C₀ K z) ∧
        M.prodLaw (strongG2 M ϑ⁻¹ C₀ K z \ strongG3 M ϑ⁻¹ C₀ K z) ≤
          ENNReal.ofReal (Real.exp (-(levelP2 K : ℝ))) := by
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨N₁, h1⟩ := strong_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := apriori_bounds (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨Cw, -, N₃, h3⟩ := weakLaw_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₄, h4⟩ := fluctuationAveraging_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₅, h5⟩ := strong_T6 (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₆, h6⟩ := standing_ineq hϑ hϑ1 hC₀ 1000
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) 150), ?_⟩
  intro N hN M hM K hK1 hK2 z hz hta
  obtain ⟨⟨hK0, h13, -, -⟩, -, ⟨-, -, hKp2, -, -⟩, -⟩ := h6 N (by omega) K hK1 hK2
  obtain ⟨hG2c, hG2p, hG2a⟩ := h1 N (by omega) M hM K hK1 hK2 z hz
  obtain ⟨-, hE₀K, hAP⟩ := h2 N (by omega) M hM K hK1 hK2
  have hKpos : 0 < K := by linarith
  have hK1' : (1 : ℝ) ≤ K := by linarith
  have hNnat : 0 < N := by omega
  have hNr : (150 : ℝ) ≤ N := by exact_mod_cast (show 150 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hNr1 : (1 : ℝ) ≤ N := by linarith
  have hT4 := fun (x : Pair N → 𝕜) => strong_T4 ha hK1' (by omega : 1 ≤ N) hz.2 x
  obtain ⟨hη1, -, hvk, hmlo, -, -, -, -⟩ := hT4 0
  have hη : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  have hϰ : 0 < varkappa z := lt_of_lt_of_le (by positivity) hvk
  have hϰ4 : varkappa z ≤ 4 := secondPass_varkappa_le hz.2
  have hu0 : 0 < (N : ℝ) * z.im := by positivity
  have hmsc : 0 < (msc z).im := msc_im_pos hη
  obtain ⟨hFK, hFK4, hb2, hE₀F, h62400, hF1⟩ := secondPass_powers ha hK0
  set F := K ^ (12 * ϑ⁻¹ + 11) with hF_def
  set E₀ := aprioriE0 ϑ⁻¹ C₀ δm δp K N with hE₀_def
  have hE₀0 : 0 ≤ E₀ := le_trans zero_le_one (h2 N (by omega) M hM K hK1 hK2).1
  set S := (msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 with hS_def
  have hS0 : 0 < S := by positivity
  -- the column event and the continuity of `Λ`
  have hzz : z ∈ latticeCol ϑ⁻¹ C₀ K N z := ⟨hz.1, rfl, le_rfl⟩
  have hΛc := secondPass_continuous_Lam M hη
  refine ⟨hG2c.inter (isClosed_le hΛc continuous_const), ?_⟩
  -- Step 1: the pointwise bound (7.e) on `𝒢²(z)`
  have hpt : ∀ x ∈ strongG2 M ϑ⁻¹ C₀ K z,
      Lam x z ≤ 7000 / varkappa z * ‖(N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k‖ +
        7000 / varkappa z * E₀ * S := by
    intro x hx
    have hxc : x ∈ goodCol M ϑ⁻¹ C₀ K z := (Set.mem_iInter₂.1 hx z hzz).1
    have hxE : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z := Set.mem_iInter₂.1 hxc z hzz
    obtain ⟨hle, hle'⟩ := ((h3 N (by omega) M hM K hK1 hK2 z hz.1).1 x hxc).1 hz.2
    have hst : 0 < lamSt C₀ δm δp := by unfold lamSt stabCs; positivity
    obtain ⟨-, -, -, -, -, -, -, hq, -, -, -, -, -⟩ :=
      hAP z hz.2 x hxE (by linarith only [hle, hle', hst])
    obtain ⟨-, hA2⟩ := (hG2a x hx).1 hta
    have hA1 := (hG2a x hx).1 hta
    obtain ⟨-, -, -, -, -, hW, -, -⟩ := hT4 x
    have hΛW : Lam x z ≤ ‖msc z * (1 - msc z ^ 2)‖ / 4 := hA1.1.trans hA2
    have hQ := (secondPass_norm_ge (stieltjesEmp (toMatrix x) z - msc z)
      (msc z * (1 - msc z ^ 2))).trans hq
    have hE₀u : E₀ / (N * z.im) ≤ ‖msc z * (1 - msc z ^ 2)‖ / 32 := by
      rw [div_le_div_iff₀ hu0 (by norm_num)]
      have e1 : 62400 * E₀ ≤ varkappa z * (N * z.im) := by
        have := mul_le_mul_of_nonneg_left (hE₀K.trans hE₀F) (by norm_num : (0 : ℝ) ≤ 62400)
        linarith [h62400.trans hta]
      have e2 : varkappa z / 1950 * (N * z.im) ≤ ‖msc z * (1 - msc z ^ 2)‖ * (N * z.im) :=
        mul_le_mul_of_nonneg_right hW hu0.le
      linarith
    exact secondPass_step1 (norm_nonneg _) hΛW hQ hE₀u hϰ hW (norm_nonneg _) hE₀0 hmsc.le hu0
  -- Step 2: the moment bound
  have hp1 : 1 ≤ levelP2 K := by
    have : (1 : ℝ) ≤ levelP2 K := by linarith
    exact_mod_cast this
  have hpK : (levelP2 K : ℝ) ≤ K + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ K / 2 by linarith)
    have e : (levelP2 K : ℝ) = 2 * (⌈K / 2⌉₊ : ℝ) := by unfold levelP2; push_cast; ring
    linarith
  have hT6 : ENNReal.ofReal (2 * N) * M.prodLaw (strongG2 M ϑ⁻¹ C₀ K z)ᶜ ^
      (1 / (levelP2 K : ℝ)) ≤ ENNReal.ofReal ((N : ℝ) ^ (-8 : ℝ)) := by
    have hr := (h5 N (by omega) M hM K hK1 hK2 z hz.1 (levelP2 K) (by simp)).2
    have hB0 : 0 ≤ (N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)) := by positivity
    have hp0 : (0 : ℝ) ≤ 1 / (levelP2 K : ℝ) := by positivity
    calc ENNReal.ofReal (2 * N) * M.prodLaw (strongG2 M ϑ⁻¹ C₀ K z)ᶜ ^ (1 / (levelP2 K : ℝ))
        ≤ ENNReal.ofReal (2 * N) * (ENNReal.ofReal ((N : ℝ) ^ 10 *
            Real.exp (-(levelP1 K : ℝ)))) ^ (1 / (levelP2 K : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (2 * N * ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ))) ^
            (1 / (levelP2 K : ℝ))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB0 hp0]
          exact (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-8 : ℝ)) := ENNReal.ofReal_le_ofReal hr
  have hAF : 2 * (7000 / varkappa z * F) ≤ N * z.im := by
    have e : 2 * (7000 / varkappa z * F) = 14000 * F / varkappa z := by ring
    rw [e, div_le_iff₀ hϰ]
    have hK4 : (14000 : ℝ) ≤ K ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hK0 4
      norm_num at this
      linarith
    have := mul_le_mul_of_nonneg_left hK4 (by linarith : (0 : ℝ) ≤ F)
    calc 14000 * F ≤ F * K ^ 4 := by linarith
      _ = K ^ (ledgerB ϑ⁻¹ + 3) := hFK4
      _ ≤ varkappa z * (N * z.im) := hta
      _ = N * z.im * varkappa z := by ring
  obtain ⟨hYfin, hY⟩ := secondPass_moment hp1 hG2c.measurableSet hΛc.aestronglyMeasurable
    (continuous_const.mul (continuous_finsetSum _ fun k _ =>
      ((polyGrowth_schurM M 0 hη ∅).2.2.2.2.1 k).1)).aestronglyMeasurable
    (by
      refine Continuous.aestronglyMeasurable ?_
      unfold phiStarSq
      exact continuous_const.add (continuous_const.mul
        ((Complex.continuous_im.comp (secondPass_continuous_stieltjes M hη)).add
          continuous_const)))
    (fun x => norm_nonneg _) (fun x => (hT4 x).2.2.2.2.2.2.2) hpt
    (fun x => secondPass_phi_le hNnat x hη (Nat.cast_nonneg _))
    (h4 N (by omega) M hM K hK1 hK2 z hz.1 (levelP2 K) (by simp)) hT6
    (by positivity) (by positivity) (by linarith) hu0 hAF (by positivity) (by positivity)
    (by positivity)
  -- the constant: `Y₂ ≤ 28000 K^b S/ϰ`
  have hNinv : 1 / (N : ℝ) ≤ 150 * ((msc z).im / (N * z.im)) := by
    have e : 1 / (N : ℝ) = z.im / (N * z.im) := by field_simp
    rw [e, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hu0.le
  have hc₂ : 1 / N + (msc z).im / (N * z.im) + (levelP2 K : ℝ) / (N * z.im) ^ 2 ≤
      (K + 151) * S := by
    have hm : 0 ≤ (msc z).im / (N * z.im) := by positivity
    have hu2 : 0 ≤ 1 / ((N : ℝ) * z.im) ^ 2 := by positivity
    have e : (levelP2 K : ℝ) / (N * z.im) ^ 2 = (levelP2 K : ℝ) * (1 / (N * z.im) ^ 2) := by
      ring
    rw [e, hS_def]
    have e2 : (K + 151) * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2) =
        K * ((msc z).im / (N * z.im)) + 151 * ((msc z).im / (N * z.im)) +
          (K + 2) * (1 / (N * z.im) ^ 2) + 149 * (1 / (N * z.im) ^ 2) := by ring
    rw [e2]
    linarith [mul_le_mul_of_nonneg_right hpK hu2, mul_nonneg hKpos.le hm]
  have hn8 : (N : ℝ) ^ (-8 : ℝ) ≤ S := by
    have h1' : (N : ℝ) ^ (-8 : ℝ) = ((N : ℝ) ^ 8)⁻¹ := by
      rw [Real.rpow_neg hNpos.le]
      norm_cast
    have h2' : ((N : ℝ) ^ 8)⁻¹ ≤ 1 / (150 * N) := by
      rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h7 : (N : ℝ) ^ 1 ≤ (N : ℝ) ^ 7 := pow_le_pow_right₀ hNr1 (by norm_num)
      have e8 : (N : ℝ) ^ 8 = N * N ^ 7 := by ring
      rw [e8]
      rw [pow_one] at h7
      nlinarith
    have h3' : 1 / (150 * (N : ℝ)) ≤ (msc z).im / (N * z.im) := by
      have e : 1 / (150 * (N : ℝ)) = 1 / (N : ℝ) / 150 := by field_simp
      rw [e, div_le_iff₀ (by norm_num)]
      linarith
    have : 0 ≤ 1 / ((N : ℝ) * z.im) ^ 2 := by positivity
    rw [hS_def]
    linarith
  have hYB := hY.trans (secondPass_const hc₂ (by positivity) hn8 hϰ hϰ4 (hE₀K.trans hE₀F) hF1
    hK0 hS0.le)
  rw [hFK] at hYB
  -- Step 3: Markov's inequality
  set t := K ^ (ledgerB ϑ⁻¹ + 2) *
    ((msc z).im / (varkappa z * (N * z.im)) + 1 / (varkappa z * (N * z.im) ^ 2)) with ht_def
  have hts : t = K ^ 2 * (K ^ ledgerB ϑ⁻¹ * (S / varkappa z)) := by
    rw [ht_def, hb2, hS_def]
    field_simp
  have hKb0 : 0 < K ^ ledgerB ϑ⁻¹ := Real.rpow_pos_of_pos hKpos _
  have ht0 : 0 < t := by rw [hts]; positivity
  have hsub : strongG2 M ϑ⁻¹ C₀ K z \ strongG3 M ϑ⁻¹ C₀ K z ⊆
      {x | ENNReal.ofReal t ≤
        ‖(strongG2 M ϑ⁻¹ C₀ K z).indicator (fun x => Lam x z) x‖ₑ} := by
    rintro x ⟨hxG, hxF⟩
    have hlt : t < Lam x z := by
      by_contra hc
      exact hxF ⟨hxG, not_lt.1 hc⟩
    change _ ≤ ‖(strongG2 M ϑ⁻¹ C₀ K z).indicator (fun x => Lam x z) x‖ₑ
    rw [Set.indicator_of_mem hxG, Real.enorm_of_nonneg (show 0 ≤ Lam x z from norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hlt.le
  have hK2e : Real.exp 1 * 28000 ≤ K ^ 2 := by
    have h1 := Real.exp_one_lt_d9
    have h2 := pow_le_pow_left₀ (by norm_num) hK0 2
    norm_num at h2
    linarith
  refine (measure_mono hsub).trans (secondPass_markov (by omega)
    (B := 28000 * K ^ ledgerB ϑ⁻¹ * S / varkappa z) ht0 ?_ ?_)
  · rw [hts]
    have e : Real.exp 1 * (28000 * K ^ ledgerB ϑ⁻¹ * S / varkappa z) =
        (Real.exp 1 * 28000) * (K ^ ledgerB ϑ⁻¹ * (S / varkappa z)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hK2e (by positivity)
  · rw [← ENNReal.ofReal_toReal hYfin]
    exact ENNReal.ofReal_le_ofReal hYB

end Rigidity
