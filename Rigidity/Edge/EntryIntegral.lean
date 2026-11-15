import Rigidity.Edge.EdgeEvent
import Rigidity.Edge.EntryDet
import Rigidity.Edge.Expand
import Rigidity.Edge.GoodSet
import Rigidity.Edge.Hybrid
import Rigidity.Edge.Inputs
import Rigidity.Edge.Params
import Rigidity.Edge.Resolvent
import Rigidity.Edge.SmoothCount
import Rigidity.Probability.Moments

/-!
# Integration of the one-entry expansion over an entry law

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Let `ν` be a probability measure on `𝕜` with `σ² = ∫|y|² dν ≤ C₀/N` and the tail bound
`ν{|y| > xσ} ≤ ϑ⁻¹ e^{-x^ϑ}` for `x ≥ 1` ((11.b3:nu)).  The moment bounds (11.b3:M) follow from
Lemma 4.1 (a) with the parameter `ϑ̂ = min(ϑ, 1)`; here they are stated for every `k ∈ ℕ` with an
existential constant.  Corollary 11.17 integrates the expansion of Lemma 11.16 against `ν`: for a
pair `p = (a, b)`, `Q ∈ 𝒢_p` and `F ∈ C³` with `|F^{(k)}| ≤ C_F` (`k ≤ 3`), the integral
`∫ [F(X(Q + V_p(v))) - F(X(Q))] dν(v)` equals `𝔔₂(Q; ν) + 𝟙(a ≠ b) F'(X(Q)) 𝔗₃(Q; ν)` up to
`C₂ C_F N^{-13/6+4ε_g}` for `a ≠ b` and `C₂ C_F N^{-11/6+2ε_g}` for `a = b` ((11.b3:entry),
(11.b3:entryd)).  `𝔔₂` depends on `ν` only through `m₁₁ = ∫|y|²` and `m₂₀ = ∫ y²`, and `𝔗₃`
only through `μ₃ = ∫ |y|² y`.  Entries of `𝕜` enter `ℂ`-matrices through `toC`.

The statement here does not assume the window condition `|E_i - 2| ≤ N^{-2/3+ε_g}` of the
standing assumptions; the proof does not use it.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-! ### Moments of one entry (11.b3:M) -/

/-- For `x ≥ 1`: `ϑ⁻¹ e^{-x^ϑ} ≤ ϑ̂⁻¹ e^{-x^ϑ̂}` with `ϑ̂ = min(ϑ, 1)` (proof of (11.b3:M)). -/
private lemma entryIntegral_tail_min {ϑ : ℝ} (hϑ : 0 < ϑ) {x : ℝ} (hx : 1 ≤ x) :
    ϑ⁻¹ * Real.exp (-(x ^ ϑ)) ≤ (min ϑ 1)⁻¹ * Real.exp (-(x ^ min ϑ 1)) := by
  have _ := hϑ
  rcases le_total ϑ 1 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, inv_one, Real.rpow_one, one_mul]
    have h1 : ϑ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    have h2 : Real.exp (-(x ^ ϑ)) ≤ Real.exp (-x) := by
      apply Real.exp_le_exp.2
      have h3 : x ^ (1 : ℝ) ≤ x ^ ϑ := Real.rpow_le_rpow_of_exponent_le hx h
      rw [Real.rpow_one] at h3
      linarith
    calc ϑ⁻¹ * Real.exp (-(x ^ ϑ)) ≤ 1 * Real.exp (-x) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
      _ = Real.exp (-x) := one_mul _

/-- The moment constant `max(1, (90k/ϑ̂)^{k/ϑ̂})`, `ϑ̂ = min(ϑ, 1)`, of (11.b3:M). -/
private noncomputable def entryIntegral_mk (ϑ : ℝ) (k : ℕ) : ℝ :=
  max 1 ((cTheta (min ϑ 1)⁻¹ * k) ^ ((k : ℝ) / min ϑ 1))

private lemma entryIntegral_mk_pos (ϑ : ℝ) (k : ℕ) : 0 < entryIntegral_mk ϑ k :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- (11.b3:M) at scale `s`, with integrability: Lemma 4.1 (a) with the parameter `min(ϑ, 1)`. -/
private lemma entryIntegral_moment {ϑ : ℝ} (hϑ : 0 < ϑ) {ν : Measure 𝕜} [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 ≤ s)
    (htail : ∀ x : ℝ, 1 ≤ x → ν {y | x * s < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ))))
    (k : ℕ) :
    Integrable (fun y : 𝕜 => ‖y‖ ^ k) ν ∧ ∫ y, ‖y‖ ^ k ∂ν ≤ entryIntegral_mk ϑ k * s ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    exact ⟨integrable_const _, le_max_left _ _⟩
  · have hm : 0 < min ϑ 1 := lt_min hϑ one_pos
    have htail' : ∀ x : ℝ, 1 ≤ x → ν {y | x * s < ‖y‖} ≤
        ENNReal.ofReal ((min ϑ 1)⁻¹ * Real.exp (-x ^ min ϑ 1)) := fun x hx =>
      (htail x hx).trans (ENNReal.ofReal_le_ofReal (entryIntegral_tail_min hϑ hx))
    obtain ⟨hi, hb⟩ := moments_bound hm (min_le_right ϑ 1) hs htail' (q := (k : ℝ))
      (by exact_mod_cast hk)
    simp only [Real.rpow_natCast] at hi hb
    exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hs k))⟩

/-- (11.b3:M) at scale `σ = (∫|y|²)^{1/2} ≤ (C₀/N)^{1/2}`. -/
private lemma entryIntegral_moment_le {ϑ : ℝ} (hϑ : 0 < ϑ) {C₀ : ℝ} {N : ℕ} {ν : Measure 𝕜}
    [IsProbabilityMeasure ν] (hσ : ∫ y, ‖y‖ ^ 2 ∂ν ≤ C₀ / N)
    (htail : ∀ x : ℝ, 1 ≤ x → ν {y | x * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) < ‖y‖} ≤
      ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))) (k : ℕ) :
    Integrable (fun y : 𝕜 => ‖y‖ ^ k) ν ∧
      ∫ y, ‖y‖ ^ k ∂ν ≤ entryIntegral_mk ϑ k * (C₀ / N) ^ ((k : ℝ) / 2) := by
  have h0 : 0 ≤ ∫ y, ‖y‖ ^ 2 ∂ν := integral_nonneg fun y => by positivity
  obtain ⟨hi, hb⟩ := entryIntegral_moment hϑ (Real.sqrt_nonneg _) htail k
  refine ⟨hi, hb.trans (mul_le_mul_of_nonneg_left ?_ (entryIntegral_mk_pos ϑ k).le)⟩
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h0,
    show (1 / 2 : ℝ) * k = k / 2 by ring]
  exact Real.rpow_le_rpow h0 hσ (by positivity)

section EntryIntegralC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `𝔔₂(Q; ν)` of Corollary 11.17 as a function of `m₁₁ = ∫|y|²` and `m₂₀ = ∫ y²`
((11.b3:Q2), (11.b3:Q2d)). -/
noncomputable def entryQ2 (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (F : ℝ → ℝ) (m11 : ℝ)
    (m20 : ℂ) : ℝ :=
  if a = b then
    m11 * (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) / (2 * π) *
        (resolventMat Q ⟨E₂, η⟩ a a ^ 2 - resolventMat Q ⟨E₁, η⟩ a a ^ 2).im +
      iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) / (2 * π ^ 2) *
        ((resolventMat Q ⟨E₂, η⟩ a a - resolventMat Q ⟨E₁, η⟩ a a).im) ^ 2)
  else
    iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) / π *
        ((m11 : ℂ) * (resolventMat Q ⟨E₂, η⟩ a a * resolventMat Q ⟨E₂, η⟩ b b -
            resolventMat Q ⟨E₁, η⟩ a a * resolventMat Q ⟨E₁, η⟩ b b) +
          m20 / 2 * (resolventMat Q ⟨E₂, η⟩ b a ^ 2 - resolventMat Q ⟨E₁, η⟩ b a ^ 2) +
          star m20 / 2 * (resolventMat Q ⟨E₂, η⟩ a b ^ 2 - resolventMat Q ⟨E₁, η⟩ a b ^ 2)).im +
      iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) / (4 * π ^ 2) *
        (‖(resolventMat Q ⟨E₂, η⟩ b a - resolventMat Q ⟨E₁, η⟩ b a) -
            star (resolventMat Q ⟨E₂, η⟩ a b - resolventMat Q ⟨E₁, η⟩ a b)‖ ^ 2 * m11 -
          (((resolventMat Q ⟨E₂, η⟩ b a - resolventMat Q ⟨E₁, η⟩ b a) -
            star (resolventMat Q ⟨E₂, η⟩ a b - resolventMat Q ⟨E₁, η⟩ a b)) ^ 2 * m20).re)

/-- `𝔗₃(Q; ν)` of Corollary 11.17 as a function of `μ₃ = ∫ |y|² y` (11.b3:T3). -/
noncomputable def entryT3 (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (μ3 : ℂ) : ℝ :=
  -π⁻¹ * ((μ3 * resolventMat Q ⟨E₂, η⟩ b a + star μ3 * resolventMat Q ⟨E₂, η⟩ a b) *
      pairG (resolventMat Q ⟨E₂, η⟩) a b -
    (μ3 * resolventMat Q ⟨E₁, η⟩ b a + star μ3 * resolventMat Q ⟨E₁, η⟩ a b) *
      pairG (resolventMat Q ⟨E₁, η⟩) a b).im

end EntryIntegralC

/-- (11.b3:M), existential form. -/
theorem exists_moment_le (ϑ : ℝ) (hϑ : 0 < ϑ) (k : ℕ) :
    ∃ m : ℝ, 0 < m ∧ ∀ (C₀ : ℝ) (N : ℕ) (ν : Measure 𝕜) [IsProbabilityMeasure ν],
      ∫ y, ‖y‖ ^ 2 ∂ν ≤ C₀ / N →
      (∀ x : ℝ, 1 ≤ x → ν {y | x * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) < ‖y‖} ≤
        ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))) →
      ∫ y, ‖y‖ ^ k ∂ν ≤ m * (C₀ / N) ^ ((k : ℝ) / 2) := by
  refine ⟨entryIntegral_mk ϑ k, entryIntegral_mk_pos ϑ k, ?_⟩
  intro C₀ N ν _ hσ htail
  exact (entryIntegral_moment_le hϑ hσ htail k).2

/-! ### Integration of the polynomial part of the expansion -/

private lemma entryIntegral_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

private lemma entryIntegral_continuous_toC : Continuous (toC : 𝕜 → ℂ) := by
  have : (toC : 𝕜 → ℂ) = fun y => (RCLike.re y : ℂ) + (RCLike.im y : ℂ) * Complex.I := by
    funext y; apply Complex.ext <;> simp [toC]
  rw [this]
  fun_prop

private lemma entryIntegral_integrable {E : Type*} [NormedAddCommGroup E] {ν : Measure 𝕜}
    {g : 𝕜 → E} (hg : Continuous g) {k : ℕ} {C : ℝ}
    (hk : Integrable (fun y : 𝕜 => ‖y‖ ^ k) ν) (hb : ∀ y, ‖g y‖ ≤ C * ‖y‖ ^ k) :
    Integrable g ν :=
  (hk.const_mul C).mono' hg.aestronglyMeasurable (Eventually.of_forall hb)

private lemma entryIntegral_add {E : Type*} [NormedAddCommGroup E] {ν : Measure 𝕜}
    {f g : 𝕜 → E} (hf : Integrable f ν) (hg : Integrable g ν) :
    Integrable (fun y => f y + g y) ν :=
  hf.add hg

private lemma entryIntegral_integral_im {ν : Measure 𝕜} {G : 𝕜 → ℂ} (hG : Integrable G ν) :
    ∫ y, (G y).im ∂ν = (∫ y, G y ∂ν).im := by
  simpa only [RCLike.im_to_complex] using integral_im hG

private lemma entryIntegral_integral_re {ν : Measure 𝕜} {G : 𝕜 → ℂ} (hG : Integrable G ν) :
    ∫ y, (G y).re ∂ν = (∫ y, G y ∂ν).re := by
  simpa only [RCLike.re_to_complex] using integral_re hG

private lemma entryIntegral_integrable_im {ν : Measure 𝕜} {G : 𝕜 → ℂ} (hG : Integrable G ν) :
    Integrable (fun y => (G y).im) ν := by
  simpa only [RCLike.im_to_complex] using hG.im

private lemma entryIntegral_integrable_re {ν : Measure 𝕜} {G : 𝕜 → ℂ} (hG : Integrable G ν) :
    Integrable (fun y => (G y).re) ν := by
  simpa only [RCLike.re_to_complex] using hG.re

private lemma entryIntegral_integral_star {ν : Measure 𝕜} (G : 𝕜 → ℂ) :
    ∫ y, star (G y) ∂ν = star (∫ y, G y ∂ν) := by
  simp only [Complex.star_def]
  exact integral_conj

/-- The mean of `toC y` vanishes when `∫ y dν = 0`. -/
private lemma entryIntegral_integral_toC {ν : Measure 𝕜}
    (h1 : Integrable (fun y : 𝕜 => ‖y‖ ^ 1) ν) (hmean : ∫ y, y ∂ν = 0) :
    ∫ y, toC y ∂ν = 0 := by
  have hi : Integrable (fun y : 𝕜 => y) ν :=
    entryIntegral_integrable continuous_id h1 (C := 1) (fun y => by simp)
  have hc : Integrable (fun y : 𝕜 => toC y) ν :=
    entryIntegral_integrable entryIntegral_continuous_toC h1 (C := 1)
      (fun y => by simp [entryIntegral_norm_toC])
  apply Complex.ext
  · rw [← entryIntegral_integral_re hc]
    have h := integral_re hi
    rw [hmean] at h
    simpa [toC] using h
  · rw [← entryIntegral_integral_im hc]
    have h := integral_im hi
    rw [hmean] at h
    simpa [toC] using h

/-- `(Im(c₁ w + c₂ w̄))² = ½(|ϰ|²|w|² - Re(ϰ² w²))` with `ϰ = c₁ - c̄₂` (proof of
Corollary 11.17). -/
private lemma entryIntegral_sq_im (w c1 c2 : ℂ) :
    (w * c1 + star w * c2).im ^ 2 =
      1 / 2 * (‖c1 - star c2‖ ^ 2 * ‖w‖ ^ 2 - ((c1 - star c2) ^ 2 * w ^ 2).re) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, pow_two]
  ring

/-- The integral of `F'Δ₁ + (F'Δ₂ + ½F''Δ₁²) + F'Δ₃` for `a ≠ b`, with the brackets of
(11.27)–(11.29) as constants (proof of Corollary 11.17, case `a ≠ b`). -/
private lemma entryIntegral_alg_offDiag {ν : Measure 𝕜} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun y : 𝕜 => ‖y‖ ^ 1) ν) (h2 : Integrable (fun y : 𝕜 => ‖y‖ ^ 2) ν)
    (h3 : Integrable (fun y : 𝕜 => ‖y‖ ^ 3) ν) (hmean : ∫ y, y ∂ν = 0)
    (F1 F2 : ℝ) (c1 c2 D B C X Y : ℂ) :
    Integrable (fun y : 𝕜 =>
      F1 * (-π⁻¹ * (toC y * c1 + star (toC y) * c2).im) +
      (F1 * (π⁻¹ * (((‖toC y‖ ^ 2 : ℝ) : ℂ) * D + toC y ^ 2 / 2 * B +
          star (toC y) ^ 2 / 2 * C).im) +
        1 / 2 * F2 * (-π⁻¹ * (toC y * c1 + star (toC y) * c2).im) ^ 2) +
      F1 * (-π⁻¹ * (((‖toC y‖ ^ 2 : ℝ) : ℂ) * toC y * X +
        ((‖toC y‖ ^ 2 : ℝ) : ℂ) * star (toC y) * Y).im)) ν ∧
    ∫ y : 𝕜, (F1 * (-π⁻¹ * (toC y * c1 + star (toC y) * c2).im) +
      (F1 * (π⁻¹ * (((‖toC y‖ ^ 2 : ℝ) : ℂ) * D + toC y ^ 2 / 2 * B +
          star (toC y) ^ 2 / 2 * C).im) +
        1 / 2 * F2 * (-π⁻¹ * (toC y * c1 + star (toC y) * c2).im) ^ 2) +
      F1 * (-π⁻¹ * (((‖toC y‖ ^ 2 : ℝ) : ℂ) * toC y * X +
        ((‖toC y‖ ^ 2 : ℝ) : ℂ) * star (toC y) * Y).im)) ∂ν =
      F1 / π * (((∫ y, ‖y‖ ^ 2 ∂ν : ℝ) : ℂ) * D + (∫ y, toC y ^ 2 ∂ν) / 2 * B +
          star (∫ y, toC y ^ 2 ∂ν) / 2 * C).im +
        F2 / (4 * π ^ 2) * (‖c1 - star c2‖ ^ 2 * ∫ y, ‖y‖ ^ 2 ∂ν -
          ((c1 - star c2) ^ 2 * ∫ y, toC y ^ 2 ∂ν).re) +
        F1 * (-π⁻¹ * ((∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν) * X +
          star (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν) * Y).im) := by
  have hct := entryIntegral_continuous_toC (𝕜 := 𝕜)
  have hcn : Continuous fun y : 𝕜 => ((‖y‖ ^ 2 : ℝ) : ℂ) := by fun_prop
  -- the complex monomials and their integrability
  have iw : Integrable (fun y : 𝕜 => toC y) ν :=
    entryIntegral_integrable hct h1 (C := 1) (fun y => by simp [entryIntegral_norm_toC])
  have iws : Integrable (fun y : 𝕜 => star (toC y)) ν :=
    entryIntegral_integrable hct.star h1 (C := 1) (fun y => by simp [entryIntegral_norm_toC])
  have iw2 : Integrable (fun y : 𝕜 => toC y ^ 2) ν :=
    entryIntegral_integrable (hct.pow 2) h2 (C := 1)
      (fun y => by simp [entryIntegral_norm_toC])
  have iws2 : Integrable (fun y : 𝕜 => star (toC y) ^ 2) ν :=
    entryIntegral_integrable (hct.star.pow 2) h2 (C := 1)
      (fun y => by simp [entryIntegral_norm_toC])
  have in2 : Integrable (fun y : 𝕜 => ((‖y‖ ^ 2 : ℝ) : ℂ)) ν :=
    entryIntegral_integrable hcn h2 (C := 1) (fun y => by simp)
  have i3 : Integrable (fun y : 𝕜 => ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y) ν :=
    entryIntegral_integrable (hcn.mul hct) h3 (C := 1)
      (fun y => by simp [entryIntegral_norm_toC]; ring_nf; rfl)
  have i3s : Integrable (fun y : 𝕜 => ((‖y‖ ^ 2 : ℝ) : ℂ) * star (toC y)) ν :=
    entryIntegral_integrable (hcn.mul hct.star) h3 (C := 1)
      (fun y => by simp [entryIntegral_norm_toC]; ring_nf; rfl)
  -- the integrals of the monomials
  have hw0 : ∫ y, toC y ∂ν = 0 := entryIntegral_integral_toC h1 hmean
  have hws0 : ∫ y, star (toC y) ∂ν = 0 := by
    rw [entryIntegral_integral_star, hw0, star_zero]
  have hws2 : ∫ y, star (toC y) ^ 2 ∂ν = star (∫ y, toC y ^ 2 ∂ν) := by
    simp_rw [← star_pow]
    exact entryIntegral_integral_star _
  have hn2 : ∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) ∂ν = ((∫ y, ‖y‖ ^ 2 ∂ν : ℝ) : ℂ) :=
    integral_complex_ofReal
  have h3s : ∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * star (toC y) ∂ν =
      star (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν) := by
    rw [← entryIntegral_integral_star]
    congr 1
    funext y
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  -- the three complex integrands
  set κ := c1 - star c2 with hκ
  have iG1 : Integrable (fun y : 𝕜 => toC y * c1 + star (toC y) * c2) ν :=
    entryIntegral_add (iw.mul_const c1) (iws.mul_const c2)
  have eG1 : ∫ y, (toC y * c1 + star (toC y) * c2) ∂ν = 0 := by
    rw [integral_add (iw.mul_const c1) (iws.mul_const c2), integral_mul_const,
      integral_mul_const, hw0, hws0]
    ring
  have iG2a := entryIntegral_add (in2.mul_const D) ((iw2.div_const 2).mul_const B)
  have iG2 := entryIntegral_add iG2a ((iws2.div_const 2).mul_const C)
  have eG2 : ∫ y, (((‖y‖ ^ 2 : ℝ) : ℂ) * D + toC y ^ 2 / 2 * B +
      star (toC y) ^ 2 / 2 * C) ∂ν = ((∫ y, ‖y‖ ^ 2 ∂ν : ℝ) : ℂ) * D +
        (∫ y, toC y ^ 2 ∂ν) / 2 * B + star (∫ y, toC y ^ 2 ∂ν) / 2 * C := by
    rw [integral_add iG2a ((iws2.div_const 2).mul_const C),
      integral_add (in2.mul_const D) ((iw2.div_const 2).mul_const B),
      integral_mul_const, integral_mul_const, integral_mul_const, integral_div, integral_div,
      hn2, hws2]
  have iG3 := entryIntegral_add (i3.mul_const X) (i3s.mul_const Y)
  have eG3 : ∫ y, (((‖y‖ ^ 2 : ℝ) : ℂ) * toC y * X +
      ((‖y‖ ^ 2 : ℝ) : ℂ) * star (toC y) * Y) ∂ν =
        (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν) * X +
          star (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν) * Y := by
    rw [integral_add (i3.mul_const X) (i3s.mul_const Y), integral_mul_const,
      integral_mul_const, h3s]
  have iK : Integrable (fun y : 𝕜 => (κ ^ 2 * toC y ^ 2).re) ν :=
    entryIntegral_integrable_re (iw2.const_mul _)
  have eK : ∫ y, (κ ^ 2 * toC y ^ 2).re ∂ν = (κ ^ 2 * ∫ y, toC y ^ 2 ∂ν).re := by
    rw [entryIntegral_integral_re (iw2.const_mul _), integral_const_mul]
  -- the integrand as a real linear combination
  have hpt : ∀ y : 𝕜,
      F1 * (-π⁻¹ * (toC y * c1 + star (toC y) * c2).im) +
      (F1 * (π⁻¹ * (((‖toC y‖ ^ 2 : ℝ) : ℂ) * D + toC y ^ 2 / 2 * B +
          star (toC y) ^ 2 / 2 * C).im) +
        1 / 2 * F2 * (-π⁻¹ * (toC y * c1 + star (toC y) * c2).im) ^ 2) +
      F1 * (-π⁻¹ * (((‖toC y‖ ^ 2 : ℝ) : ℂ) * toC y * X +
        ((‖toC y‖ ^ 2 : ℝ) : ℂ) * star (toC y) * Y).im) =
      -(F1 * π⁻¹) * (toC y * c1 + star (toC y) * c2).im +
        F1 * π⁻¹ * (((‖y‖ ^ 2 : ℝ) : ℂ) * D + toC y ^ 2 / 2 * B +
          star (toC y) ^ 2 / 2 * C).im +
        (F2 / (4 * π ^ 2) * ‖κ‖ ^ 2) * ‖y‖ ^ 2 +
        -(F2 / (4 * π ^ 2)) * (κ ^ 2 * toC y ^ 2).re +
        -(F1 * π⁻¹) * (((‖y‖ ^ 2 : ℝ) : ℂ) * toC y * X +
          ((‖y‖ ^ 2 : ℝ) : ℂ) * star (toC y) * Y).im := by
    intro y
    have hsq := entryIntegral_sq_im (toC y) c1 c2
    rw [entryIntegral_norm_toC] at hsq ⊢
    rw [mul_pow, hsq]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  simp_rw [hpt]
  have iA := (entryIntegral_integrable_im iG1).const_mul (-(F1 * π⁻¹))
  have iB := (entryIntegral_integrable_im iG2).const_mul (F1 * π⁻¹)
  have iC := h2.const_mul (F2 / (4 * π ^ 2) * ‖κ‖ ^ 2)
  have iD := iK.const_mul (-(F2 / (4 * π ^ 2)))
  have iE := (entryIntegral_integrable_im iG3).const_mul (-(F1 * π⁻¹))
  have iAB := entryIntegral_add iA iB
  have iABC := entryIntegral_add iAB iC
  have iABCD := entryIntegral_add iABC iD
  refine ⟨entryIntegral_add iABCD iE, ?_⟩
  rw [integral_add iABCD iE, integral_add iABC iD, integral_add iAB iC, integral_add iA iB,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, entryIntegral_integral_im iG1, entryIntegral_integral_im iG2,
    entryIntegral_integral_im iG3, eG1, eG2, eG3, eK]
  simp only [Complex.zero_im, mul_zero, zero_add]
  rw [div_eq_mul_inv F1 π]
  ring

/-- The integral of `F'Δ₁ + (F'Δ₂ + ½F''Δ₁²)` for `a = b` and a law on the real line
(proof of Corollary 11.17, case `a = b`). -/
private lemma entryIntegral_alg_diag {ν : Measure 𝕜} [IsProbabilityMeasure ν]
    (h1 : Integrable (fun y : 𝕜 => ‖y‖ ^ 1) ν) (h2 : Integrable (fun y : 𝕜 => ‖y‖ ^ 2) ν)
    (hmean : ∫ y, y ∂ν = 0) (hreal : ∀ᵐ y ∂ν, RCLike.im y = 0) (F1 F2 K1 K2 : ℝ) :
    Integrable (fun y : 𝕜 => F1 * (-((toC y).re / π) * K1) +
      (F1 * ((toC y).re ^ 2 / (2 * π) * K2) + 1 / 2 * F2 * (-((toC y).re / π) * K1) ^ 2) +
      F1 * 0) ν ∧
    ∫ y : 𝕜, (F1 * (-((toC y).re / π) * K1) +
      (F1 * ((toC y).re ^ 2 / (2 * π) * K2) + 1 / 2 * F2 * (-((toC y).re / π) * K1) ^ 2) +
      F1 * 0) ∂ν = (∫ y, ‖y‖ ^ 2 ∂ν) * (F1 / (2 * π) * K2 + F2 / (2 * π ^ 2) * K1 ^ 2) := by
  have hre : ∀ y : 𝕜, (toC y).re = RCLike.re y := fun _ => rfl
  simp_rw [hre]
  have hi : Integrable (fun y : 𝕜 => y) ν :=
    entryIntegral_integrable continuous_id h1 (C := 1) (fun y => by simp)
  have ir : Integrable (fun y : 𝕜 => RCLike.re y) ν :=
    entryIntegral_integrable RCLike.continuous_re h1 (C := 1)
      (fun y => by simpa using RCLike.abs_re_le_norm y)
  have ir2 : Integrable (fun y : 𝕜 => RCLike.re y ^ 2) ν :=
    entryIntegral_integrable (RCLike.continuous_re.pow 2) h2 (C := 1) (fun y => by
      rw [one_mul, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm y) 2)
  have er : ∫ y, RCLike.re y ∂ν = 0 := by
    rw [integral_re hi, hmean, map_zero]
  have er2 : ∫ y, RCLike.re y ^ 2 ∂ν = ∫ y, ‖y‖ ^ 2 ∂ν := by
    refine integral_congr_ae (hreal.mono fun y hy => ?_)
    simp only
    rw [RCLike.norm_sq_eq_def, hy]
    ring
  have hpt : ∀ y : 𝕜, F1 * (-(RCLike.re y / π) * K1) +
      (F1 * (RCLike.re y ^ 2 / (2 * π) * K2) + 1 / 2 * F2 * (-(RCLike.re y / π) * K1) ^ 2) +
      F1 * 0 = -(F1 * K1 / π) * RCLike.re y +
        (F1 / (2 * π) * K2 + F2 / (2 * π ^ 2) * K1 ^ 2) * RCLike.re y ^ 2 := by
    intro y
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  simp_rw [hpt]
  refine ⟨entryIntegral_add (ir.const_mul _) (ir2.const_mul _), ?_⟩
  rw [integral_add (ir.const_mul _) (ir2.const_mul _), integral_const_mul, integral_const_mul,
    er, er2]
  ring

/-- `F'(x₀)Δ₁(v) + (F'(x₀)Δ₂(v) + ½F''(x₀)Δ₁(v)²) + F'(x₀)Δ₃(v)` with `x₀ = X(Q)`: the polynomial
part `P₁ + P₂ + F'Δ₃` of the expansion in Lemma 11.16 (b). -/
private noncomputable def entryIntegral_P {n : Type*} [Fintype n] [DecidableEq n]
    (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (F : ℝ → ℝ) (v : ℂ) : ℝ :=
  iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a b v +
    (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta2 E₁ E₂ η Q a b v +
      1 / 2 * iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a b v ^ 2) +
    iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta3 E₁ E₂ η Q a b v

/-- `∫ (P₁ + P₂ + F'Δ₃) dν = 𝔔₂(Q; ν) + 𝟙(a ≠ b) F'(X(Q)) 𝔗₃(Q; ν)` (proof of
Corollary 11.17). -/
private lemma entryIntegral_poly {n : Type*} [Fintype n] [DecidableEq n] {ν : Measure 𝕜}
    [IsProbabilityMeasure ν]
    (h1 : Integrable (fun y : 𝕜 => ‖y‖ ^ 1) ν) (h2 : Integrable (fun y : 𝕜 => ‖y‖ ^ 2) ν)
    (h3 : Integrable (fun y : 𝕜 => ‖y‖ ^ 3) ν) (hmean : ∫ y, y ∂ν = 0)
    (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (F : ℝ → ℝ)
    (hreal : a = b → ∀ᵐ y ∂ν, RCLike.im y = 0) :
    Integrable (fun y : 𝕜 => entryIntegral_P E₁ E₂ η Q a b F (toC y)) ν ∧
    ∫ y, entryIntegral_P E₁ E₂ η Q a b F (toC y) ∂ν =
      entryQ2 E₁ E₂ η Q a b F (∫ y, ‖y‖ ^ 2 ∂ν) (∫ y, toC y ^ 2 ∂ν) +
        (if a = b then 0 else
          iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) *
            entryT3 E₁ E₂ η Q a b (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν)) := by
  by_cases hab : a = b
  · subst hab
    simp only [entryIntegral_P, expDelta1, expDelta2, expDelta3, entryQ2, ↓reduceIte, add_zero]
    exact entryIntegral_alg_diag h1 h2 hmean (hreal rfl) _ _ _ _
  · simp only [entryIntegral_P, expDelta1, expDelta2, expDelta3, entryQ2, entryT3, hab,
      ↓reduceIte]
    obtain ⟨hi, he⟩ := entryIntegral_alg_offDiag h1 h2 h3 hmean
      (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q)) (iteratedDeriv 2 F (smoothCount E₁ E₂ η Q))
      (resolventMat Q ⟨E₂, η⟩ b a - resolventMat Q ⟨E₁, η⟩ b a)
      (resolventMat Q ⟨E₂, η⟩ a b - resolventMat Q ⟨E₁, η⟩ a b)
      (resolventMat Q ⟨E₂, η⟩ a a * resolventMat Q ⟨E₂, η⟩ b b -
        resolventMat Q ⟨E₁, η⟩ a a * resolventMat Q ⟨E₁, η⟩ b b)
      (resolventMat Q ⟨E₂, η⟩ b a ^ 2 - resolventMat Q ⟨E₁, η⟩ b a ^ 2)
      (resolventMat Q ⟨E₂, η⟩ a b ^ 2 - resolventMat Q ⟨E₁, η⟩ a b ^ 2)
      (resolventMat Q ⟨E₂, η⟩ b a * pairG (resolventMat Q ⟨E₂, η⟩) a b -
        resolventMat Q ⟨E₁, η⟩ b a * pairG (resolventMat Q ⟨E₁, η⟩) a b)
      (resolventMat Q ⟨E₂, η⟩ a b * pairG (resolventMat Q ⟨E₂, η⟩) a b -
        resolventMat Q ⟨E₁, η⟩ a b * pairG (resolventMat Q ⟨E₁, η⟩) a b)
    refine ⟨hi, he.trans ?_⟩
    congr 5
    ring

/-! ### The error of the expansion and its integral -/

section EntryIntegralErr

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private lemma entryIntegral_continuous_entryMat (a b : n) :
    Continuous fun w : ℂ => entryMat a b w := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold entryMat
  split_ifs with h
  · simp only [Matrix.single_apply]
    split_ifs <;> fun_prop
  · simp only [Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

/-- `v ↦ X(Q + V_p(v))` is continuous on `𝕜` (Lemma 11.8 (c)). -/
private lemma entryIntegral_continuous_smoothCount {E₁ E₂ η : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂)
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) (a b : n) :
    Continuous fun y : 𝕜 => smoothCount E₁ E₂ η (Q + entryMat a b (toC y)) := by
  set g : 𝕜 → Matrix n n ℂ := fun y => Q + entryMat a b (toC y) with hgdef
  have hg : Continuous g :=
    continuous_const.add ((entryIntegral_continuous_entryMat a b).comp
      entryIntegral_continuous_toC)
  have hh : ∀ y, (g y).IsHermitian := fun y => hQ.add (entryMat_isHermitian a b _)
  change Continuous fun y => smoothCount E₁ E₂ η (g y)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Tendsto (fun x => Fintype.card n * (E₂ - E₁) / (π * η ^ 2) * ‖g x - g x₀‖)
      (𝓝 x₀) (𝓝 0) := by
    have h0 : Tendsto (fun x => ‖g x - g x₀‖) (𝓝 x₀) (𝓝 0) := by
      have := hg.tendsto x₀
      rw [tendsto_iff_norm_sub_tendsto_zero] at this
      exact this
    simpa using h0.const_mul (Fintype.card n * (E₂ - E₁) / (π * η ^ 2))
  refine squeeze_zero (fun _ => dist_nonneg) (fun x => ?_) hc
  rw [Real.dist_eq]
  exact abs_smoothCount_sub_le (hh x) (hh x₀) hη hE

/-- The pointwise bound on the error `e(v)` of the proof of Corollary 11.17: Lemma 11.16 (b)
for `|v| ≤ t`, and Lemma 11.16 (a) with `|F| ≤ C_F` for `|v| > t`. -/
private lemma entryIntegral_err {E₁ E₂ η Ψ t : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (hΨ : 0 < Ψ)
    (hΨ' : Ψ ≤ 1 / 8) (ht : 40 * t ≤ Ψ) {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {a b : n}
    (hend : EndpointGood η Ψ E₁ E₂ a b Q) (F : ℝ → ℝ) (CF : ℝ) (hF : ContDiff ℝ 3 F)
    (hFb : ∀ k : ℕ, k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) (y : 𝕜) :
    |(F (smoothCount E₁ E₂ η (Q + entryMat a b (toC y))) - F (smoothCount E₁ E₂ η Q)) -
        entryIntegral_P E₁ E₂ η Q a b F (toC y)| ≤
      4 * CF * (if a = b then Ψ else Ψ ^ 2) * ‖y‖ ^ 3 +
        4 * CF * (if a = b then 1 else Ψ) * ‖y‖ ^ 4 +
        8 * CF * {y : 𝕜 | t < ‖y‖}.indicator 1 y + 4 * CF * ‖y‖ ^ 6 := by
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hFb 0 (by norm_num) 0)
  have hFb' : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF :=
    fun k _ hk => hFb k hk
  have hx0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hA : 0 ≤ (if a = b then Ψ else Ψ ^ 2) := by split_ifs <;> positivity
  have hB : 0 ≤ (if a = b then (1 : ℝ) else Ψ) := by split_ifs <;> positivity
  have hA' : 0 ≤ 4 * CF * (if a = b then Ψ else Ψ ^ 2) * ‖y‖ ^ 3 := by positivity
  have hB' : 0 ≤ 4 * CF * (if a = b then 1 else Ψ) * ‖y‖ ^ 4 := by positivity
  have h6 : 0 ≤ 4 * CF * ‖y‖ ^ 6 := by positivity
  by_cases hy : ‖y‖ ≤ t
  · have hI : {y : 𝕜 | t < ‖y‖}.indicator (1 : 𝕜 → ℝ) y = 0 :=
      Set.indicator_of_notMem (by simpa using hy) _
    rw [hI, mul_zero, add_zero]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      have hre : |RCLike.re y| ≤ ‖y‖ := RCLike.abs_re_le_norm y
      have hre4 : |RCLike.re y| ≤ 1 / 4 := by linarith
      have key := (expand_diag hη hE hΨ hΨ' hQ hend F CF hF hFb' (RCLike.re y) hre4).1
      have hM : entryMat a a (toC y) = entryMat a a ((RCLike.re y : ℝ) : ℂ) := by
        simp [entryMat, toC]
      have hD1 : expDelta1 E₁ E₂ η Q a a (toC y) =
          expDelta1 E₁ E₂ η Q a a ((RCLike.re y : ℝ) : ℂ) := by
        simp [expDelta1, toC]
      have hD2 : expDelta2 E₁ E₂ η Q a a (toC y) =
          expDelta2 E₁ E₂ η Q a a ((RCLike.re y : ℝ) : ℂ) := by
        simp [expDelta2, toC]
      have hD3 : expDelta3 E₁ E₂ η Q a a (toC y) = 0 := by simp [expDelta3]
      rw [entryIntegral_P, hM, hD1, hD2, hD3]
      have h3 : |RCLike.re y| ^ 3 ≤ ‖y‖ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hre 3
      have h4 : RCLike.re y ^ 4 ≤ ‖y‖ ^ 4 := by
        rw [show RCLike.re y ^ 4 = |RCLike.re y| ^ 4 by
          rw [pow_abs, abs_of_nonneg (by positivity)]]
        exact pow_le_pow_left₀ (abs_nonneg _) hre 4
      calc _ = |F (smoothCount E₁ E₂ η (Q + entryMat a a ((RCLike.re y : ℝ) : ℂ))) -
              F (smoothCount E₁ E₂ η Q) -
              iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) *
                expDelta1 E₁ E₂ η Q a a ((RCLike.re y : ℝ) : ℂ) -
              (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) *
                  expDelta2 E₁ E₂ η Q a a ((RCLike.re y : ℝ) : ℂ) +
                1 / 2 * iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) *
                  expDelta1 E₁ E₂ η Q a a ((RCLike.re y : ℝ) : ℂ) ^ 2)| := by
            congr 1; ring
        _ ≤ 4 * CF * (|RCLike.re y| ^ 3 * Ψ + RCLike.re y ^ 4) := key
        _ ≤ 4 * CF * Ψ * ‖y‖ ^ 3 + 4 * CF * 1 * ‖y‖ ^ 4 := by
            have := mul_le_mul_of_nonneg_right h3 hΨ.le
            nlinarith
        _ ≤ _ := le_add_of_nonneg_right h6
    · simp only [hab, ↓reduceIte]
      have hv : ‖toC y‖ ≤ Ψ / 40 := by rw [entryIntegral_norm_toC]; linarith
      have key := (expand_offDiag hη hE hΨ hΨ' hQ hab hend F CF hF hFb' (toC y) hv).1
      rw [entryIntegral_norm_toC] at key
      rw [entryIntegral_P]
      calc _ = |F (smoothCount E₁ E₂ η (Q + entryMat a b (toC y))) - F (smoothCount E₁ E₂ η Q) -
              iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a b (toC y) -
              (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta2 E₁ E₂ η Q a b (toC y) +
                1 / 2 * iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) *
                  expDelta1 E₁ E₂ η Q a b (toC y) ^ 2) -
              iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta3 E₁ E₂ η Q a b (toC y)| := by
            congr 1; ring
        _ ≤ 4 * CF * (‖y‖ ^ 3 * Ψ ^ 2 + ‖y‖ ^ 4 * Ψ) := key
        _ = 4 * CF * Ψ ^ 2 * ‖y‖ ^ 3 + 4 * CF * Ψ * ‖y‖ ^ 4 := by ring
        _ ≤ _ := le_add_of_nonneg_right h6
  · have hy' : t < ‖y‖ := not_le.1 hy
    have hI : {y : 𝕜 | t < ‖y‖}.indicator (1 : 𝕜 → ℝ) y = 1 := Set.indicator_of_mem hy' _
    rw [hI, mul_one]
    obtain ⟨d1, d2, d3⟩ := abs_expDelta_le hη hΨ hΨ' hQ hend (toC y)
    rw [entryIntegral_norm_toC] at d1 d2 d3
    have hF0 : ∀ x, |F x| ≤ CF := fun x => by simpa using hFb 0 (by norm_num) x
    have hF1 := hFb 1 (by norm_num) (smoothCount E₁ E₂ η Q)
    have hF2 := hFb 2 (by norm_num) (smoothCount E₁ E₂ η Q)
    set x := ‖y‖ with hxdef
    set D1 := expDelta1 E₁ E₂ η Q a b (toC y)
    set D2 := expDelta2 E₁ E₂ η Q a b (toC y)
    set D3 := expDelta3 E₁ E₂ η Q a b (toC y)
    set G1 := iteratedDeriv 1 F (smoothCount E₁ E₂ η Q)
    set G2 := iteratedDeriv 2 F (smoothCount E₁ E₂ η Q)
    have e1 : |G1 * D1| ≤ CF * (x / 4) := by
      rw [abs_mul]
      refine (mul_le_mul hF1 d1 (abs_nonneg _) hCF).trans (mul_le_mul_of_nonneg_left ?_ hCF)
      nlinarith
    have e2 : |G1 * D2| ≤ CF * (3 * x ^ 2 / 8) := by
      rw [abs_mul]
      refine (mul_le_mul hF1 d2 (abs_nonneg _) hCF).trans (mul_le_mul_of_nonneg_left ?_ hCF)
      have : 0 ≤ x ^ 2 := by positivity
      nlinarith
    have e3 : |G1 * D3| ≤ CF * (3 * x ^ 3 / 8) := by
      rw [abs_mul]
      refine (mul_le_mul hF1 d3 (abs_nonneg _) hCF).trans (mul_le_mul_of_nonneg_left ?_ hCF)
      have : 0 ≤ x ^ 3 := by positivity
      nlinarith
    have e4 : |1 / 2 * G2 * D1 ^ 2| ≤ CF * (x ^ 2 / 32) := by
      have hd : |D1| ≤ x / 4 := d1.trans (by nlinarith)
      have hd2 : D1 ^ 2 ≤ (x / 4) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_of_nonneg (sq_nonneg D1)]
      have := mul_le_mul hF2 hd2 (sq_nonneg _) hCF
      nlinarith
    have hfa := hF0 (smoothCount E₁ E₂ η (Q + entryMat a b (toC y)))
    have hfb := hF0 (smoothCount E₁ E₂ η Q)
    have hpoly : 2 + x / 4 + 3 * x ^ 2 / 8 + x ^ 2 / 32 + 3 * x ^ 3 / 8 ≤ 8 + 4 * x ^ 6 := by
      rcases le_total x 1 with hx1 | hx1
      · have q2 : x ^ 2 ≤ 1 := pow_le_one₀ hx0 hx1
        have q3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
        have q6 : 0 ≤ x ^ 6 := by positivity
        linarith
      · have q1 : x ≤ x ^ 6 := by
          simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 6)
        have q2 : x ^ 2 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
        have q3 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
        linarith
    have hsum : |(F (smoothCount E₁ E₂ η (Q + entryMat a b (toC y))) -
        F (smoothCount E₁ E₂ η Q)) - entryIntegral_P E₁ E₂ η Q a b F (toC y)| ≤
        CF * (2 + x / 4 + 3 * x ^ 2 / 8 + x ^ 2 / 32 + 3 * x ^ 3 / 8) := by
      rw [entryIntegral_P]
      refine abs_le.2 ⟨?_, ?_⟩
      · linarith [neg_abs_le (G1 * D1), neg_abs_le (G1 * D2), neg_abs_le (G1 * D3),
          neg_abs_le (1 / 2 * G2 * D1 ^ 2), le_abs_self (G1 * D1), le_abs_self (G1 * D2),
          le_abs_self (G1 * D3), le_abs_self (1 / 2 * G2 * D1 ^ 2), abs_le.1 hfa, abs_le.1 hfb]
      · linarith [neg_abs_le (G1 * D1), neg_abs_le (G1 * D2), neg_abs_le (G1 * D3),
          neg_abs_le (1 / 2 * G2 * D1 ^ 2), le_abs_self (G1 * D1), le_abs_self (G1 * D2),
          le_abs_self (G1 * D3), le_abs_self (1 / 2 * G2 * D1 ^ 2), abs_le.1 hfa, abs_le.1 hfb]
    have := mul_le_mul_of_nonneg_left hpoly hCF
    linarith

end EntryIntegralErr

/-- The four error terms of the proof of Corollary 11.17 against the rate `N^{-11/6+2ε_g}`
(`a = b`) or `N^{-13/6+4ε_g}` (`a ≠ b`), with `Ψ = 4N^{-1/3+2ε_g}` and the moment bounds
(11.b3:M). -/
private lemma entryIntegral_rate {εg C₀ CF m3 m4 m6 : ℝ} {N : ℕ} (hN : 1 ≤ (N : ℝ))
    (hεg : 0 < εg) (hC₀ : 0 < C₀) (hCF : 0 ≤ CF) (hm3 : 0 ≤ m3) (hm4 : 0 ≤ m4) (hm6 : 0 ≤ m6)
    (d : Prop) [Decidable d] :
    4 * CF * (if d then edgePsi εg N else edgePsi εg N ^ 2) * (m3 * (C₀ / N) ^ ((3 : ℝ) / 2)) +
        4 * CF * (if d then 1 else edgePsi εg N) * (m4 * (C₀ / N) ^ ((4 : ℝ) / 2)) +
        8 * CF * (N : ℝ) ^ (-20 : ℝ) + 4 * CF * (m6 * (C₀ / N) ^ ((6 : ℝ) / 2)) ≤
      (64 * m3 * C₀ ^ ((3 : ℝ) / 2) + 16 * m4 * C₀ ^ ((4 : ℝ) / 2) + 8 +
          4 * m6 * C₀ ^ ((6 : ℝ) / 2)) * CF *
        (if d then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
          else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hsplit : ∀ k : ℝ, (C₀ / N) ^ k = C₀ ^ k * (N : ℝ) ^ (-k) := fun k => by
    rw [Real.div_rpow hC₀.le hNpos.le, Real.rpow_neg hNpos.le, div_eq_mul_inv]
  have hmono : ∀ x y : ℝ, x ≤ y → (N : ℝ) ^ x ≤ (N : ℝ) ^ y := fun x y h =>
    Real.rpow_le_rpow_of_exponent_le hN h
  have hΨ : edgePsi εg N = 4 * (N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg) := rfl
  set e := (if d then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
    else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) with he
  have he0 : 0 ≤ e := by rw [he]; split_ifs <;> positivity
  have f1 : (if d then edgePsi εg N else edgePsi εg N ^ 2) * (N : ℝ) ^ (-((3 : ℝ) / 2)) ≤
      16 * e := by
    rw [he]
    split_ifs
    · rw [hΨ, mul_assoc, ← Real.rpow_add hNpos]
      have := hmono (-(1 / 3 : ℝ) + 2 * εg + -(3 / 2)) (-(11 / 6 : ℝ) + 2 * εg) (by linarith)
      have h0 : 0 ≤ (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg) := by positivity
      linarith
    · have hsq : ((N : ℝ) ^ (-(1 / 3 : ℝ) + 2 * εg)) ^ 2 =
          (N : ℝ) ^ ((-(1 / 3 : ℝ) + 2 * εg) + (-(1 / 3 : ℝ) + 2 * εg)) := by
        rw [sq, ← Real.rpow_add hNpos]
      rw [hΨ, mul_pow, hsq, mul_assoc, ← Real.rpow_add hNpos]
      have := hmono ((-(1 / 3 : ℝ) + 2 * εg) + (-(1 / 3 : ℝ) + 2 * εg) + -(3 / 2))
        (-(13 / 6 : ℝ) + 4 * εg) (by linarith)
      norm_num
      linarith
  have f2 : (if d then 1 else edgePsi εg N) * (N : ℝ) ^ (-((4 : ℝ) / 2)) ≤ 4 * e := by
    rw [he]
    split_ifs
    · have := hmono (-((4 : ℝ) / 2)) (-(11 / 6 : ℝ) + 2 * εg) (by linarith)
      have h0 : 0 ≤ (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg) := by positivity
      linarith
    · rw [hΨ, mul_assoc, ← Real.rpow_add hNpos]
      have := hmono (-(1 / 3 : ℝ) + 2 * εg + -((4 : ℝ) / 2)) (-(13 / 6 : ℝ) + 4 * εg)
        (by linarith)
      linarith
  have f3 : (N : ℝ) ^ (-20 : ℝ) ≤ e := by
    rw [he]
    split_ifs
    · exact hmono _ _ (by linarith)
    · exact hmono _ _ (by linarith)
  have f4 : (N : ℝ) ^ (-((6 : ℝ) / 2)) ≤ e := by
    rw [he]
    split_ifs
    · exact hmono _ _ (by linarith)
    · exact hmono _ _ (by linarith)
  have hA3 : 0 ≤ C₀ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  have hA4 : 0 ≤ C₀ ^ ((4 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  have hA6 : 0 ≤ C₀ ^ ((6 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  have g1 := mul_le_mul_of_nonneg_left f1
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCF) hm3) hA3)
  have g2 := mul_le_mul_of_nonneg_left f2
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCF) hm4) hA4)
  have g3 := mul_le_mul_of_nonneg_left f3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hCF)
  have g4 := mul_le_mul_of_nonneg_left f4
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCF) hm6) hA6)
  rw [hsplit, hsplit, hsplit]
  calc _ = 4 * CF * m3 * C₀ ^ ((3 : ℝ) / 2) *
          ((if d then edgePsi εg N else edgePsi εg N ^ 2) * (N : ℝ) ^ (-((3 : ℝ) / 2))) +
        4 * CF * m4 * C₀ ^ ((4 : ℝ) / 2) *
          ((if d then 1 else edgePsi εg N) * (N : ℝ) ^ (-((4 : ℝ) / 2))) +
        8 * CF * (N : ℝ) ^ (-20 : ℝ) +
        4 * CF * m6 * C₀ ^ ((6 : ℝ) / 2) * (N : ℝ) ^ (-((6 : ℝ) / 2)) := by ring
    _ ≤ 4 * CF * m3 * C₀ ^ ((3 : ℝ) / 2) * (16 * e) + 4 * CF * m4 * C₀ ^ ((4 : ℝ) / 2) * (4 * e) +
        8 * CF * e + 4 * CF * m6 * C₀ ^ ((6 : ℝ) / 2) * e := by linarith
    _ = _ := by ring

/-- Corollary 11.17. -/
theorem entry_integral_le (ϑ C₀ : ℝ) (hϑ : 0 < ϑ) (hC₀ : 0 < C₀) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (A₀ εg : ℝ), 0 < εg → εg ≤ 1 / 10 → ∀ N : ℕ,
      EdgeLarge ϑ C₀ A₀ εg N → ∀ E₁ E₂ : ℝ, E₁ ≤ E₂ → ∀ (p : Pair N)
      (Q : Matrix (Fin N) (Fin N) ℂ),
      Q ∈ goodSet (edgeEta εg N) (edgePsi εg N) E₁ E₂ p.1.1 p.1.2 →
      ∀ (F : ℝ → ℝ) (CF : ℝ), ContDiff ℝ 3 F →
      (∀ k : ℕ, k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) →
      ∀ (ν : Measure 𝕜) [IsProbabilityMeasure ν],
      (p.1.1 = p.1.2 → ∀ᵐ y ∂ν, RCLike.im y = 0) →
      ∫ y, ‖y‖ ^ 2 ∂ν ≤ C₀ / N →
      (∀ x : ℝ, 1 ≤ x → ν {y | x * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂ν) < ‖y‖} ≤
        ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))) →
      ∫ y, y ∂ν = 0 →
      |∫ v, (F (smoothCount E₁ E₂ (edgeEta εg N) (Q + entryMat p.1.1 p.1.2 (toC v))) -
            F (smoothCount E₁ E₂ (edgeEta εg N) Q)) ∂ν -
          entryQ2 E₁ E₂ (edgeEta εg N) Q p.1.1 p.1.2 F (∫ y, ‖y‖ ^ 2 ∂ν) (∫ y, toC y ^ 2 ∂ν) -
          (if p.1.1 = p.1.2 then 0 else
            iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N) Q) *
              entryT3 E₁ E₂ (edgeEta εg N) Q p.1.1 p.1.2
                (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν))| ≤
        C₂ * CF * (if p.1.1 = p.1.2 then (N : ℝ) ^ (-(11 / 6 : ℝ) + 2 * εg)
          else (N : ℝ) ^ (-(13 / 6 : ℝ) + 4 * εg)) := by
  have hm3 := (entryIntegral_mk_pos ϑ 3).le
  have hm4 := (entryIntegral_mk_pos ϑ 4).le
  have hm6 := (entryIntegral_mk_pos ϑ 6).le
  have hA3 : 0 ≤ C₀ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  have hA4 : 0 ≤ C₀ ^ ((4 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  have hA6 : 0 ≤ C₀ ^ ((6 : ℝ) / 2) := Real.rpow_nonneg hC₀.le _
  refine ⟨64 * entryIntegral_mk ϑ 3 * C₀ ^ ((3 : ℝ) / 2) +
    16 * entryIntegral_mk ϑ 4 * C₀ ^ ((4 : ℝ) / 2) + 8 +
    4 * entryIntegral_mk ϑ 6 * C₀ ^ ((6 : ℝ) / 2), ?_, ?_⟩
  · have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hm3) hA3
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hm4) hA4
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hm6) hA6
    linarith
  intro A₀ εg hεg _ N hN E₁ E₂ hE p Q hQ F CF hF hFb ν _ hreal hσ htail hmean
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_exp (by norm_num)) hN.exp_le
  have hη : 0 < edgeEta εg N := Real.rpow_pos_of_pos hNpos _
  have hΨ : 0 < edgePsi εg N := by
    unfold edgePsi
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hNpos _)
  have hend := endpointGood_of_mem_goodSet hE hQ
  have hQh : Q.IsHermitian := hQ.1
  have hF0 : ∀ x, |F x| ≤ CF := fun x => by simpa using hFb 0 (by norm_num) x
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF0 0)
  obtain ⟨i1, -⟩ := entryIntegral_moment_le hϑ hσ htail 1
  obtain ⟨i2, -⟩ := entryIntegral_moment_le hϑ hσ htail 2
  obtain ⟨i3, b3⟩ := entryIntegral_moment_le hϑ hσ htail 3
  obtain ⟨i4, b4⟩ := entryIntegral_moment_le hϑ hσ htail 4
  obtain ⟨i6, b6⟩ := entryIntegral_moment_le hϑ hσ htail 6
  simp only [Nat.cast_ofNat] at b3 b4 b6
  obtain ⟨iP, eP⟩ := entryIntegral_poly i1 i2 i3 hmean E₁ E₂ (edgeEta εg N) Q p.1.1 p.1.2 F
    hreal
  have hcont : Continuous fun y : 𝕜 =>
      F (smoothCount E₁ E₂ (edgeEta εg N) (Q + entryMat p.1.1 p.1.2 (toC y))) -
        F (smoothCount E₁ E₂ (edgeEta εg N) Q) :=
    (hF.continuous.comp (entryIntegral_continuous_smoothCount hη hE hQh _ _)).sub
      continuous_const
  have iD : Integrable (fun y : 𝕜 =>
      F (smoothCount E₁ E₂ (edgeEta εg N) (Q + entryMat p.1.1 p.1.2 (toC y))) -
        F (smoothCount E₁ E₂ (edgeEta εg N) Q)) ν := by
    refine (integrable_const (2 * CF)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    linarith [hF0 (smoothCount E₁ E₂ (edgeEta εg N) (Q + entryMat p.1.1 p.1.2 (toC y))),
      hF0 (smoothCount E₁ E₂ (edgeEta εg N) Q)]
  have hS : MeasurableSet {y : 𝕜 | edgeT εg N < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hνS : ν.real {y : 𝕜 | edgeT εg N < ‖y‖} ≤ (N : ℝ) ^ (-20 : ℝ) := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      (law_norm_gt_edgeT_le hϑ hεg hN ν hσ htail)
  have ig3 := i3.const_mul
    (4 * CF * (if p.1.1 = p.1.2 then edgePsi εg N else edgePsi εg N ^ 2))
  have ig4 := i4.const_mul (4 * CF * (if p.1.1 = p.1.2 then 1 else edgePsi εg N))
  have igS : Integrable (fun y : 𝕜 => 8 * CF * {y : 𝕜 | edgeT εg N < ‖y‖}.indicator 1 y) ν :=
    ((integrable_const (μ := ν) (1 : ℝ)).indicator hS).const_mul (8 * CF)
  have ig6 := i6.const_mul (4 * CF)
  have ig := entryIntegral_add (entryIntegral_add (entryIntegral_add ig3 ig4) igS) ig6
  have hle := norm_integral_le_of_norm_le ig (Eventually.of_forall fun y =>
    (Real.norm_eq_abs _).trans_le (entryIntegral_err hη hE hΨ hN.psi_le hN.t_le hQh hend F CF hF
      hFb y))
  have eg : ∫ y : 𝕜, (4 * CF * (if p.1.1 = p.1.2 then edgePsi εg N else edgePsi εg N ^ 2) *
          ‖y‖ ^ 3 + 4 * CF * (if p.1.1 = p.1.2 then 1 else edgePsi εg N) * ‖y‖ ^ 4 +
          8 * CF * {y : 𝕜 | edgeT εg N < ‖y‖}.indicator 1 y + 4 * CF * ‖y‖ ^ 6) ∂ν =
      4 * CF * (if p.1.1 = p.1.2 then edgePsi εg N else edgePsi εg N ^ 2) * ∫ y, ‖y‖ ^ 3 ∂ν +
        4 * CF * (if p.1.1 = p.1.2 then 1 else edgePsi εg N) * ∫ y, ‖y‖ ^ 4 ∂ν +
        8 * CF * ν.real {y : 𝕜 | edgeT εg N < ‖y‖} + 4 * CF * ∫ y, ‖y‖ ^ 6 ∂ν := by
    rw [integral_add (entryIntegral_add (entryIntegral_add ig3 ig4) igS) ig6,
      integral_add (entryIntegral_add ig3 ig4) igS,
      integral_add ig3 ig4, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, ← integral_indicator_one hS]
  have hA : 0 ≤ 4 * CF * (if p.1.1 = p.1.2 then edgePsi εg N else edgePsi εg N ^ 2) := by
    split_ifs <;> positivity
  have hB : 0 ≤ 4 * CF * (if p.1.1 = p.1.2 then (1 : ℝ) else edgePsi εg N) := by
    split_ifs <;> positivity
  have hrew : ∫ v, (F (smoothCount E₁ E₂ (edgeEta εg N) (Q + entryMat p.1.1 p.1.2 (toC v))) -
          F (smoothCount E₁ E₂ (edgeEta εg N) Q)) ∂ν -
        entryQ2 E₁ E₂ (edgeEta εg N) Q p.1.1 p.1.2 F (∫ y, ‖y‖ ^ 2 ∂ν) (∫ y, toC y ^ 2 ∂ν) -
        (if p.1.1 = p.1.2 then 0 else
          iteratedDeriv 1 F (smoothCount E₁ E₂ (edgeEta εg N) Q) *
            entryT3 E₁ E₂ (edgeEta εg N) Q p.1.1 p.1.2
              (∫ y, ((‖y‖ ^ 2 : ℝ) : ℂ) * toC y ∂ν)) =
      ∫ y, ((F (smoothCount E₁ E₂ (edgeEta εg N) (Q + entryMat p.1.1 p.1.2 (toC y))) -
          F (smoothCount E₁ E₂ (edgeEta εg N) Q)) -
        entryIntegral_P E₁ E₂ (edgeEta εg N) Q p.1.1 p.1.2 F (toC y)) ∂ν := by
    rw [integral_sub iD iP, eP]
    ring
  rw [hrew, ← Real.norm_eq_abs]
  refine hle.trans ?_
  rw [eg]
  refine le_trans ?_ (entryIntegral_rate hN1 hεg hC₀ hCF hm3 hm4 hm6 (p.1.1 = p.1.2))
  have := mul_le_mul_of_nonneg_left b3 hA
  have := mul_le_mul_of_nonneg_left b4 hB
  have := mul_le_mul_of_nonneg_left hνS (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hCF)
  have := mul_le_mul_of_nonneg_left b6 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCF)
  linarith

end Rigidity
