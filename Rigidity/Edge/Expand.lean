import Rigidity.Edge.GoodSet
import Rigidity.Edge.LogBounds
import Rigidity.Edge.SmoothCount
import Rigidity.Edge.SpecF

/-!
# Expansion of the smoothed counting functional under a one-entry replacement

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian `Q`, a pair `(a, b)` and the endpoints `z_i = E_i + iη`, write `R = G_Q` and
`[f] = f(z₂) - f(z₁)`.  The real numbers `Δ₁(v), Δ₂(v), Δ₃(v)` of Lemma 11.16 (11.27)–(11.29)
are the terms of degree `1, 2, 3` in `v` of `X(Q + V_p(v)) - X(Q)`, and `g = R_aa R_bb - R_ab R_ba`
is the quantity of Lemma 11.10.  Under the endpoint condition (11.25) with `0 < Ψ ≤ 1/8`,
Lemma 11.16 (a) bounds `|Δ_k(v)|` by a constant times `|v|^k Ψ` for every `v`, and `g` by
`|g - 1| ≤ 9/4 Ψ`, `|g| ≤ 4/3`.  Lemma 11.16 (b) is the expansion of `F(X(Q + V_p(v)))` to
third order for `F ∈ C³` with `|F^{(k)}| ≤ C_F` (`k = 1, 2, 3`): for `a ≠ b` and `|v| ≤ Ψ/40`
the error is at most `4 C_F (|v|³Ψ² + |v|⁴Ψ)`; for `a = b`, real `v` and `|v| ≤ 1/4` it is at
most `4 C_F (|v|³Ψ + v⁴)`.  For `a = b` the matrix `V_p(v)` and the numbers `Δ_k(v)` depend on
`v` only through `Re v`, and `Δ₃ = 0`.

The proof follows Lemma 11.16: Corollary 11.11 (i) writes `X(Q + V_p(v)) - X(Q)` as
`-π⁻¹ Im [Log(1 + ζ)]` with `ζ = D_p(v) - 1`; the bounds (L2), (L3) of Section 11.3 control the
logarithm, an exact algebraic split identifies `Δ₁, Δ₂, Δ₃`, and Taylor's formula with Lagrange
remainder handles `F`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section ExpandC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `g = R_aa R_bb - R_ab R_ba` (Lemma 11.10). -/
noncomputable def pairG (R : Matrix n n ℂ) (a b : n) : ℂ := R a a * R b b - R a b * R b a

/-- `Δ₁(v)` of Lemma 11.16 (11.27), both cases. -/
noncomputable def expDelta1 (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (v : ℂ) : ℝ :=
  if a = b then
    -(v.re / π) * (resolventMat Q ⟨E₂, η⟩ a a - resolventMat Q ⟨E₁, η⟩ a a).im
  else
    -π⁻¹ * (v * (resolventMat Q ⟨E₂, η⟩ b a - resolventMat Q ⟨E₁, η⟩ b a) +
      star v * (resolventMat Q ⟨E₂, η⟩ a b - resolventMat Q ⟨E₁, η⟩ a b)).im

/-- `Δ₂(v)` of Lemma 11.16 (11.28), both cases. -/
noncomputable def expDelta2 (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (v : ℂ) : ℝ :=
  if a = b then
    v.re ^ 2 / (2 * π) * (resolventMat Q ⟨E₂, η⟩ a a ^ 2 - resolventMat Q ⟨E₁, η⟩ a a ^ 2).im
  else
    π⁻¹ * (((‖v‖ ^ 2 : ℝ) : ℂ) * (resolventMat Q ⟨E₂, η⟩ a a * resolventMat Q ⟨E₂, η⟩ b b -
        resolventMat Q ⟨E₁, η⟩ a a * resolventMat Q ⟨E₁, η⟩ b b) +
      v ^ 2 / 2 * (resolventMat Q ⟨E₂, η⟩ b a ^ 2 - resolventMat Q ⟨E₁, η⟩ b a ^ 2) +
      star v ^ 2 / 2 * (resolventMat Q ⟨E₂, η⟩ a b ^ 2 - resolventMat Q ⟨E₁, η⟩ a b ^ 2)).im

/-- `Δ₃(v)` of Lemma 11.16 (11.29) for `a ≠ b`; `0` for `a = b`. -/
noncomputable def expDelta3 (E₁ E₂ η : ℝ) (Q : Matrix n n ℂ) (a b : n) (v : ℂ) : ℝ :=
  if a = b then 0
  else
    -π⁻¹ * (((‖v‖ ^ 2 : ℝ) : ℂ) * v *
        (resolventMat Q ⟨E₂, η⟩ b a * pairG (resolventMat Q ⟨E₂, η⟩) a b -
          resolventMat Q ⟨E₁, η⟩ b a * pairG (resolventMat Q ⟨E₁, η⟩) a b) +
      ((‖v‖ ^ 2 : ℝ) : ℂ) * star v *
        (resolventMat Q ⟨E₂, η⟩ a b * pairG (resolventMat Q ⟨E₂, η⟩) a b -
          resolventMat Q ⟨E₁, η⟩ a b * pairG (resolventMat Q ⟨E₁, η⟩) a b)).im

/-- Taylor's formula of order two with Lagrange remainder, for `F ∈ C³`. -/
private lemma expand_taylor {F : ℝ → ℝ} {CF : ℝ} (hF : ContDiff ℝ 3 F)
    (hF3 : ∀ x, |iteratedDeriv 3 F x| ≤ CF) (x y : ℝ) :
    |F y - F x - iteratedDeriv 1 F x * (y - x) - 1 / 2 * iteratedDeriv 2 F x * (y - x) ^ 2| ≤
      CF * |y - x| ^ 3 / 6 := by
  rcases eq_or_ne x y with rfl | hxy
  · have := (abs_nonneg _).trans (hF3 x)
    simp
  obtain ⟨c, -, hc⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy
    (hF.contDiffOn.of_le (by norm_num))
  have hu : UniqueDiffOn ℝ (Set.uIcc x y) := uniqueDiffOn_uIcc hxy
  have hx : x ∈ Set.uIcc x y := Set.left_mem_uIcc
  have h1 : iteratedDerivWithin 1 F (Set.uIcc x y) x = iteratedDeriv 1 F x :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hF.contDiffAt.of_le (by norm_num)) hx
  have h2 : iteratedDerivWithin 2 F (Set.uIcc x y) x = iteratedDeriv 2 F x :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hF.contDiffAt.of_le (by norm_num)) hx
  have e : taylorWithinEval F 2 (Set.uIcc x y) x y =
      F x + iteratedDeriv 1 F x * (y - x) + 1 / 2 * iteratedDeriv 2 F x * (y - x) ^ 2 := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, h1, h2, smul_eq_mul]
    norm_num
    ring
  rw [e] at hc
  have e2 : F y - F x - iteratedDeriv 1 F x * (y - x) - 1 / 2 * iteratedDeriv 2 F x * (y - x) ^ 2
      = iteratedDeriv (2 + 1) F c * (y - x) ^ (2 + 1) / ((2 + 1).factorial : ℝ) := by
    rw [← hc]; ring
  have h6 : ((2 + 1).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [e2, h6, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 6)]
  gcongr
  exact hF3 c

/-- `‖g - 1‖ ≤ 9/4 Ψ` and `‖g‖ ≤ 4/3` for `g = pq - rs`. -/
private lemma expand_g {Ψ : ℝ} (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8) {p q r s : ℂ}
    (hp : ‖p + 1‖ ≤ Ψ) (hq : ‖q + 1‖ ≤ Ψ) (hr : ‖r‖ ≤ Ψ) (hs : ‖s‖ ≤ Ψ) :
    ‖p * q - r * s - 1‖ ≤ 9 / 4 * Ψ ∧ ‖p * q - r * s‖ ≤ 4 / 3 := by
  have e : p * q - r * s - 1 = (p + 1) * (q + 1) - (p + 1) - (q + 1) - r * s := by ring
  have h1 : ‖p * q - r * s - 1‖ ≤ 9 / 4 * Ψ := by
    rw [e]
    have := norm_sub_le ((p + 1) * (q + 1) - (p + 1) - (q + 1)) (r * s)
    have := norm_sub_le ((p + 1) * (q + 1) - (p + 1)) (q + 1)
    have := norm_sub_le ((p + 1) * (q + 1)) (p + 1)
    rw [norm_mul] at *
    have := mul_le_mul hp hq (norm_nonneg _) hΨ.le
    have := mul_le_mul hr hs (norm_nonneg _) hΨ.le
    nlinarith
  refine ⟨h1, ?_⟩
  have := norm_le_norm_add_norm_sub' (p * q - r * s) 1
  rw [norm_one] at this
  nlinarith [norm_sub_rev (p * q - r * s) 1]

/-- Pointwise sizes at one endpoint, `a ≠ b`. -/
private lemma expand_pt {Ψ : ℝ} (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8) {p q r s : ℂ}
    (hp : ‖p + 1‖ ≤ Ψ) (hq : ‖q + 1‖ ≤ Ψ) (hr : ‖r‖ ≤ Ψ) (hs : ‖s‖ ≤ Ψ) (v : ℂ) :
    ‖v * s + star v * r‖ ≤ 2 * ‖v‖ * Ψ ∧
    |(((‖v‖ ^ 2 : ℝ) : ℂ) * (p * q) + v ^ 2 / 2 * s ^ 2 + star v ^ 2 / 2 * r ^ 2).im| ≤
      5 / 2 * ‖v‖ ^ 2 * Ψ ∧
    ‖((‖v‖ ^ 2 : ℝ) : ℂ) * v * (s * (p * q - r * s)) +
        ((‖v‖ ^ 2 : ℝ) : ℂ) * star v * (r * (p * q - r * s))‖ ≤ 8 / 3 * ‖v‖ ^ 3 * Ψ ∧
    |((((‖v‖ ^ 2 : ℝ) : ℂ) * (p * q - r * s)) ^ 2).im| ≤ 6 * ‖v‖ ^ 4 * Ψ := by
  obtain ⟨hg1, hg⟩ := expand_g hΨ hΨ' hp hq hr hs
  set g := p * q - r * s with hg_def
  set N : ℂ := ((‖v‖ ^ 2 : ℝ) : ℂ) with hN_def
  have hN : N = v * star v := by
    rw [hN_def, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hv0 := norm_nonneg v
  set u := v * s + star v * r with hu_def
  have hu : ‖u‖ ≤ 2 * ‖v‖ * Ψ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_star]
    nlinarith [mul_le_mul_of_nonneg_left hs hv0, mul_le_mul_of_nonneg_left hr hv0]
  refine ⟨hu, ?_, ?_, ?_⟩
  · have e : N * (p * q) + v ^ 2 / 2 * s ^ 2 + star v ^ 2 / 2 * r ^ 2 =
        N * (g - 1) + N + u ^ 2 / 2 := by
      rw [hg_def, hu_def]; linear_combination (r * s) * hN
    rw [e, Complex.add_im, Complex.add_im, hN_def, Complex.im_ofReal_mul, Complex.ofReal_im]
    have h1 : |‖v‖ ^ 2 * (g - 1).im| ≤ ‖v‖ ^ 2 * (9 / 4 * Ψ) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hg1) (by positivity)
    have h2 : |(u ^ 2 / 2).im| ≤ (2 * ‖v‖ * Ψ) ^ 2 / 2 := by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_div, norm_pow]
      simp only [Complex.norm_ofNat]
      gcongr
    have h3 : (2 * ‖v‖ * Ψ) ^ 2 / 2 ≤ 1 / 4 * ‖v‖ ^ 2 * Ψ := by
      have : 0 ≤ ‖v‖ ^ 2 * Ψ := by positivity
      nlinarith
    calc |‖v‖ ^ 2 * (g - 1).im + 0 + (u ^ 2 / 2).im|
        ≤ |‖v‖ ^ 2 * (g - 1).im| + |(u ^ 2 / 2).im| := by
          rw [add_zero]; exact abs_add_le _ _
      _ ≤ 5 / 2 * ‖v‖ ^ 2 * Ψ := by nlinarith
  · have e : N * v * (s * g) + N * star v * (r * g) = u * (N * g) := by rw [hu_def]; ring
    rw [e, norm_mul, norm_mul, hN_def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    calc ‖u‖ * (‖v‖ ^ 2 * ‖g‖) ≤ (2 * ‖v‖ * Ψ) * (‖v‖ ^ 2 * (4 / 3)) := by gcongr
      _ = 8 / 3 * ‖v‖ ^ 3 * Ψ := by ring
  · have e : (N * g) ^ 2 = N ^ 2 * ((g - 1) * (g + 1)) + N ^ 2 := by ring
    rw [e, Complex.add_im, hN_def, ← Complex.ofReal_pow, Complex.im_ofReal_mul,
      Complex.ofReal_im, add_zero, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : ‖g + 1‖ ≤ 7 / 3 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have h2 : |((g - 1) * (g + 1)).im| ≤ 9 / 4 * Ψ * (7 / 3) := by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul]
      exact mul_le_mul hg1 h1 (norm_nonneg _) (by positivity)
    calc (‖v‖ ^ 2) ^ 2 * |((g - 1) * (g + 1)).im| ≤ (‖v‖ ^ 2) ^ 2 * (9 / 4 * Ψ * (7 / 3)) := by
          gcongr
      _ ≤ 6 * ‖v‖ ^ 4 * Ψ := by
          have : 0 ≤ ‖v‖ ^ 4 * Ψ := by positivity
          nlinarith

/-- The logarithm remainder at one endpoint, `a ≠ b`. -/
private lemma expand_log_pt {Ψ : ℝ} (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8) {p q r s : ℂ}
    (hp : ‖p + 1‖ ≤ Ψ) (hq : ‖q + 1‖ ≤ Ψ) (hr : ‖r‖ ≤ Ψ) (hs : ‖s‖ ≤ Ψ) {v : ℂ}
    (hv : ‖v‖ ≤ Ψ / 40) :
    |(Complex.log (1 + (v * s + star v * r) - ((‖v‖ ^ 2 : ℝ) : ℂ) * (p * q - r * s)) -
        (v * s + star v * r) +
        (((‖v‖ ^ 2 : ℝ) : ℂ) * (p * q) + v ^ 2 / 2 * s ^ 2 + star v ^ 2 / 2 * r ^ 2) -
        (((‖v‖ ^ 2 : ℝ) : ℂ) * v * (s * (p * q - r * s)) +
          ((‖v‖ ^ 2 : ℝ) : ℂ) * star v * (r * (p * q - r * s)))).im| ≤
      6 * ‖v‖ ^ 3 * Ψ ^ 3 + 3 * ‖v‖ ^ 4 * Ψ := by
  obtain ⟨hu, -, -, hw2⟩ := expand_pt hΨ hΨ' hp hq hr hs v
  obtain ⟨-, hg⟩ := expand_g hΨ hΨ' hp hq hr hs
  set g := p * q - r * s with hg_def
  set N : ℂ := ((‖v‖ ^ 2 : ℝ) : ℂ) with hN_def
  have hN : N = v * star v := by
    rw [hN_def, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hv0 := norm_nonneg v
  set u := v * s + star v * r with hu_def
  set ζ := u - N * g with hζ_def
  have hNg : ‖N * g‖ ≤ ‖v‖ ^ 2 * (4 / 3) := by
    rw [norm_mul, hN_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
  have hζ : ‖ζ‖ ≤ 61 / 30 * ‖v‖ * Ψ := by
    refine (norm_sub_le _ _).trans ?_
    have : ‖v‖ ^ 2 * (4 / 3) ≤ ‖v‖ * (Ψ / 40) * (4 / 3) := by
      rw [pow_two]; gcongr
    nlinarith
  have hζ2 : ‖ζ‖ ≤ 1 / 2 := by
    have : ‖v‖ * Ψ ≤ Ψ / 40 * Ψ := by gcongr
    nlinarith
  have hL := norm_clog_one_add_sub_two_le hζ2
  have e : Complex.log (1 + u - N * g) - u + (N * (p * q) + v ^ 2 / 2 * s ^ 2 +
      star v ^ 2 / 2 * r ^ 2) - (N * v * (s * g) + N * star v * (r * g)) =
      (Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2) - (N * g) ^ 2 / 2 := by
    have h1 : 1 + u - N * g = 1 + ζ := by rw [hζ_def]; ring
    rw [h1, hζ_def, hu_def, hg_def]
    linear_combination (r * s) * hN
  rw [e, Complex.sub_im]
  have h3 : |(Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2).im| ≤ 6 * ‖v‖ ^ 3 * Ψ ^ 3 := by
    refine (Complex.abs_im_le_norm _).trans (hL.trans ?_)
    have h0 : 0 ≤ ‖ζ‖ := norm_nonneg _
    calc 2 / 3 * ‖ζ‖ ^ 3 ≤ 2 / 3 * (61 / 30 * ‖v‖ * Ψ) ^ 3 := by gcongr
      _ ≤ 6 * ‖v‖ ^ 3 * Ψ ^ 3 := by
          have : 0 ≤ ‖v‖ ^ 3 * Ψ ^ 3 := by positivity
          nlinarith
  have h4 : |((N * g) ^ 2 / 2).im| ≤ 3 * ‖v‖ ^ 4 * Ψ := by
    have : ((N * g) ^ 2 / 2).im = ((N * g) ^ 2).im / 2 := by simp
    rw [this, abs_div, abs_two]
    linarith
  exact (abs_sub _ _).trans (add_le_add h3 h4)

/-- Pointwise sizes at one endpoint, `a = b`. -/
private lemma expand_diag_pt {Ψ : ℝ} (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8) {R : ℂ}
    (hR : ‖R + 1‖ ≤ Ψ) :
    |R.im| ≤ Ψ ∧ |(R ^ 2).im| ≤ 17 / 8 * Ψ ∧ ∀ v : ℝ, |v| ≤ 1 / 4 →
      |(Complex.log (1 + (v : ℂ) * R) - (v : ℂ) * R + ((v : ℂ) * R) ^ 2 / 2).im| ≤
        217 / 192 * |v| ^ 3 * Ψ + 6561 / 8192 * v ^ 4 := by
  have hR1 : ‖R‖ ≤ 1 + Ψ := by
    have := norm_sub_le (R + 1) 1
    rw [add_sub_cancel_right, norm_one] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have : R.im = (R + 1).im := by simp
    rw [this]
    exact (Complex.abs_im_le_norm _).trans hR
  · have e : R ^ 2 = (R + 1) * ((R + 1) - 2) + 1 := by ring
    rw [e, Complex.add_im, Complex.one_im, add_zero]
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul]
    have h2 : ‖(R + 1) - 2‖ ≤ Ψ + 2 := (norm_sub_le _ _).trans (by simp; linarith)
    calc ‖R + 1‖ * ‖(R + 1) - 2‖ ≤ Ψ * (Ψ + 2) := mul_le_mul hR h2 (norm_nonneg _) hΨ.le
      _ ≤ 17 / 8 * Ψ := by nlinarith
  · intro v hv
    have hv0 := abs_nonneg v
    set ζ : ℂ := (v : ℂ) * R with hζ_def
    have hζ : ‖ζ‖ ≤ 9 / 8 * |v| := by
      rw [hζ_def, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith
    have hζ2 : ‖ζ‖ ≤ 1 / 2 := by linarith
    have hL := norm_clog_one_add_sub_three_le hζ2
    have hR3 : |(R ^ 3).im| ≤ 217 / 64 * Ψ := by
      have e : R ^ 3 = (R + 1) * ((R + 1) ^ 2 - 3 * (R + 1) + 3) - 1 := by ring
      rw [e, Complex.sub_im, Complex.one_im, sub_zero]
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul]
      have h2 : ‖(R + 1) ^ 2 - 3 * (R + 1) + 3‖ ≤ Ψ ^ 2 + 3 * Ψ + 3 := by
        refine (norm_add_le _ _).trans ?_
        have := norm_sub_le ((R + 1) ^ 2) (3 * (R + 1))
        rw [norm_pow, norm_mul] at this
        rw [show ‖(3 : ℂ)‖ = 3 by simp] at this
        simp only [Complex.norm_ofNat]
        have : ‖R + 1‖ ^ 2 ≤ Ψ ^ 2 := by gcongr
        linarith
      calc ‖R + 1‖ * ‖(R + 1) ^ 2 - 3 * (R + 1) + 3‖ ≤ Ψ * (Ψ ^ 2 + 3 * Ψ + 3) :=
            mul_le_mul hR h2 (norm_nonneg _) hΨ.le
        _ ≤ 217 / 64 * Ψ := by nlinarith
    have e : Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2 =
        (Complex.log (1 + ζ) - ζ + ζ ^ 2 / 2 - ζ ^ 3 / 3) + ((v ^ 3 / 3 : ℝ) : ℂ) * R ^ 3 := by
      rw [hζ_def]; push_cast; ring
    rw [e, Complex.add_im, Complex.im_ofReal_mul]
    refine (abs_add_le _ _).trans ((add_le_add ?_ ?_).trans_eq (add_comm _ _))
    · refine (Complex.abs_im_le_norm _).trans (hL.trans ?_)
      calc 1 / 2 * ‖ζ‖ ^ 4 ≤ 1 / 2 * (9 / 8 * |v|) ^ 4 := by gcongr
        _ = 6561 / 8192 * v ^ 4 := by rw [mul_pow, pow_abs, abs_of_nonneg (by positivity)]; ring
    · rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      calc |v| ^ 3 / 3 * |(R ^ 3).im| ≤ |v| ^ 3 / 3 * (217 / 64 * Ψ) := by gcongr
        _ = 217 / 192 * |v| ^ 3 * Ψ := by ring

/-- The scalar bookkeeping of Step 4 and Step 5 of Lemma 11.16, `a ≠ b`. -/
private lemma expand_offDiag_real {t P CF F1 F2 d d1 d2 d3 ρ : ℝ} (ht : 0 ≤ t) (hP : 0 < P)
    (hP' : P ≤ 1 / 8) (htP : t ≤ P / 40) (hF1 : |F1| ≤ CF) (hF2 : |F2| ≤ CF)
    (h1 : |d1| ≤ 4 / 3 * t * P) (h2 : |d2| ≤ 5 / 3 * t ^ 2 * P) (h3 : |d3| ≤ 16 / 9 * t ^ 3 * P)
    (hr : |d - d1 - d2 - d3| ≤ 4 * t ^ 3 * P ^ 3 + 2 * t ^ 4 * P)
    (hρ : |ρ| ≤ CF * |d| ^ 3 / 6) :
    |ρ + F1 * (d - d1 - d2 - d3) + 1 / 2 * F2 * ((d - d1) * (d + d1))| ≤
        4 * CF * (t ^ 3 * P ^ 2 + t ^ 4 * P) ∧ |d| ≤ 3 / 2 * t * P := by
  have hCF : 0 ≤ CF := (abs_nonneg _).trans hF1
  have ht1 : t ≤ 1 / 320 := by linarith
  have htP0 : 0 ≤ t * P := by positivity
  have hA : |d - d1| ≤ 2 * t ^ 2 * P := by
    have hs := abs_add_le (d2 + d3) (d - d1 - d2 - d3)
    rw [show d2 + d3 + (d - d1 - d2 - d3) = d - d1 by ring] at hs
    have hs' := abs_add_le d2 d3
    have k1 : t ^ 3 * P ≤ 1 / 320 * (t ^ 2 * P) := by
      have : t ^ 3 * P = t * (t ^ 2 * P) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right ht1 (by positivity)
    have k2 : t ^ 3 * P ^ 3 ≤ 1 / 320 * (1 / 64) * (t ^ 2 * P) := by
      have : t ^ 3 * P ^ 3 = (t * P ^ 2) * (t ^ 2 * P) := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : P ^ 2 ≤ 1 / 64 := by nlinarith
      exact mul_le_mul ht1 this (by positivity) (by norm_num)
    have k3 : t ^ 4 * P ≤ (1 / 320) ^ 2 * (t ^ 2 * P) := by
      have : t ^ 4 * P = t ^ 2 * (t ^ 2 * P) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht ht1 2) (by positivity)
    have : 0 ≤ t ^ 2 * P := by positivity
    linarith
  have hd : |d| ≤ 3 / 2 * t * P := by
    have e : d = d1 + (d - d1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : t ^ 2 * P ≤ 1 / 320 * (t * P) := by
      have : t ^ 2 * P = t * (t * P) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right ht1 htP0
    linarith
  have hB : |d + d1| ≤ 3 * t * P := by
    have e : d + d1 = 2 * d1 + (d - d1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two]
    have : t ^ 2 * P ≤ 1 / 320 * (t * P) := by
      have : t ^ 2 * P = t * (t * P) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right ht1 htP0
    linarith
  refine ⟨?_, hd⟩
  have hd3 : |d| ^ 3 ≤ (3 / 2 * t * P) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hd 3
  have e1 : |ρ| ≤ CF * (27 / 48) * (t ^ 3 * P ^ 3) := by
    calc |ρ| ≤ CF * |d| ^ 3 / 6 := hρ
      _ ≤ CF * (3 / 2 * t * P) ^ 3 / 6 := by gcongr
      _ = CF * (27 / 48) * (t ^ 3 * P ^ 3) := by ring
  have e2 : |F1 * (d - d1 - d2 - d3)| ≤ CF * (4 * t ^ 3 * P ^ 3 + 2 * t ^ 4 * P) := by
    rw [abs_mul]; exact mul_le_mul hF1 hr (abs_nonneg _) hCF
  have e3 : |1 / 2 * F2 * ((d - d1) * (d + d1))| ≤ 1 / 2 * CF * (2 * t ^ 2 * P * (3 * t * P)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    gcongr
  have k : t ^ 3 * P ^ 3 ≤ 1 / 8 * (t ^ 3 * P ^ 2) := by
    have : t ^ 3 * P ^ 3 = P * (t ^ 3 * P ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hP' (by positivity)
  have k' : 0 ≤ t ^ 4 * P := by positivity
  have := abs_add_le (ρ + F1 * (d - d1 - d2 - d3)) (1 / 2 * F2 * ((d - d1) * (d + d1)))
  have := abs_add_le ρ (F1 * (d - d1 - d2 - d3))
  have hk : CF * (t ^ 3 * P ^ 3) ≤ CF * (1 / 8 * (t ^ 3 * P ^ 2)) :=
    mul_le_mul_of_nonneg_left k hCF
  have hk' : 0 ≤ CF * (t ^ 4 * P) := mul_nonneg hCF k'
  have hk'' : 0 ≤ CF * (t ^ 3 * P ^ 2) := mul_nonneg hCF (by positivity)
  linarith

/-- The scalar bookkeeping of the case `a = b` of Lemma 11.16. -/
private lemma expand_diag_real {t P CF F1 F2 d d1 d2 ρ : ℝ} (ht : 0 ≤ t) (hP : 0 < P)
    (hP' : P ≤ 1 / 8) (ht1 : t ≤ 1 / 4) (hF1 : |F1| ≤ CF) (hF2 : |F2| ≤ CF)
    (h1 : |d1| ≤ 2 / 3 * t * P) (h2 : |d2| ≤ 17 / 24 * t ^ 2 * P)
    (hr : |d - d1 - d2| ≤ t ^ 3 * P + t ^ 4)
    (hρ : |ρ| ≤ CF * |d| ^ 3 / 6) :
    |ρ + F1 * (d - d1 - d2) + 1 / 2 * F2 * ((d - d1) * (d + d1))| ≤
        4 * CF * (t ^ 3 * P + t ^ 4) ∧ |d| ≤ t * P + t ^ 4 := by
  have hCF : 0 ≤ CF := (abs_nonneg _).trans hF1
  have htP0 : 0 ≤ t * P := by positivity
  have k1 : t ^ 3 * P ≤ 1 / 4 * (t ^ 2 * P) := by
    have : t ^ 3 * P = t * (t ^ 2 * P) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right ht1 (by positivity)
  have hA : |d - d1| ≤ 5 / 4 * t ^ 2 * P + t ^ 4 := by
    have hs := abs_add_le d2 (d - d1 - d2)
    rw [show d2 + (d - d1 - d2) = d - d1 by ring] at hs
    have : 0 ≤ t ^ 2 * P := by positivity
    linarith
  have k2 : t ^ 2 * P ≤ 1 / 4 * (t * P) := by
    have : t ^ 2 * P = t * (t * P) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right ht1 htP0
  have hd : |d| ≤ t * P + t ^ 4 := by
    have e : d = d1 + (d - d1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  have k3 : t ^ 4 ≤ 1 / 64 * t := by
    have : t ^ 4 = t ^ 3 * t := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ ht
    calc t ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ ht ht1 3
      _ ≤ 1 / 64 := by norm_num
  have k4 : t * P ≤ 1 / 8 * t := by nlinarith
  have hd5 : |d| ≤ t / 5 := by linarith
  have hB : |d + d1| ≤ t / 3 := by
    refine (abs_add_le _ _).trans ?_
    linarith
  refine ⟨?_, hd⟩
  have hd3 : |d| ^ 3 ≤ (t / 5) ^ 2 * (t * P + t ^ 4) := by
    have : |d| ^ 3 = |d| ^ 2 * |d| := by ring
    rw [this]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hd5 2) hd (abs_nonneg _) (by positivity)
  have e1 : |ρ| ≤ CF * ((t / 5) ^ 2 * (t * P + t ^ 4)) / 6 := by
    calc |ρ| ≤ CF * |d| ^ 3 / 6 := hρ
      _ ≤ CF * ((t / 5) ^ 2 * (t * P + t ^ 4)) / 6 := by gcongr
  have e2 : |F1 * (d - d1 - d2)| ≤ CF * (t ^ 3 * P + t ^ 4) := by
    rw [abs_mul]; exact mul_le_mul hF1 hr (abs_nonneg _) hCF
  have e3 : |1 / 2 * F2 * ((d - d1) * (d + d1))| ≤
      1 / 2 * CF * ((5 / 4 * t ^ 2 * P + t ^ 4) * (t / 3)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    gcongr
  have := abs_add_le (ρ + F1 * (d - d1 - d2)) (1 / 2 * F2 * ((d - d1) * (d + d1)))
  have := abs_add_le ρ (F1 * (d - d1 - d2))
  have k5 : t ^ 5 ≤ 1 / 4 * t ^ 4 := by
    have : t ^ 5 = t * t ^ 4 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right ht1 (by positivity)
  have k6 : t ^ 6 ≤ 1 / 16 * t ^ 4 := by
    have : t ^ 6 = t ^ 2 * t ^ 4 := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    nlinarith
  have k7 : 0 ≤ t ^ 3 * P := by positivity
  have k8 : CF * t ^ 5 ≤ CF * (1 / 4 * t ^ 4) := mul_le_mul_of_nonneg_left k5 hCF
  have k9 : CF * t ^ 6 ≤ CF * (1 / 16 * t ^ 4) := mul_le_mul_of_nonneg_left k6 hCF
  have k10 : 0 ≤ CF * (t ^ 3 * P) := mul_nonneg hCF k7
  have k11 : 0 ≤ CF * t ^ 4 := mul_nonneg hCF (by positivity)
  nlinarith

/-- `π⁻¹ < 1/3`. -/
private lemma expand_inv_pi_lt : π⁻¹ < 1 / 3 := by
  rw [inv_lt_comm₀ pi_pos (by norm_num)]
  linarith [pi_gt_three]

/-- The two-endpoint bound of Section 11.3 with the factor `π⁻¹`: `|π⁻¹ Im [X]| ≤ 2/3 B` if
`|Im X(z_i)| ≤ B` at both endpoints. -/
private lemma expand_two {X₁ X₂ : ℂ} {B : ℝ} (h₁ : |X₁.im| ≤ B) (h₂ : |X₂.im| ≤ B) :
    |π⁻¹ * (X₂ - X₁).im| ≤ 2 / 3 * B := by
  rw [abs_mul, abs_of_pos (inv_pos.mpr pi_pos), Complex.sub_im]
  have h := abs_sub X₂.im X₁.im
  have hB : 0 ≤ B := (abs_nonneg _).trans h₁
  calc π⁻¹ * |X₂.im - X₁.im| ≤ 1 / 3 * (B + B) :=
        mul_le_mul expand_inv_pi_lt.le (by linarith) (abs_nonneg _) (by norm_num)
    _ = 2 / 3 * B := by ring

/-- The endpoint condition (11.25) at `z = y + iη`, `a ≠ b`, entry by entry. -/
private lemma expand_end_offDiag {η Ψ E₁ E₂ : ℝ} {Q : Matrix n n ℂ} {a b : n} (hab : a ≠ b)
    (hend : EndpointGood η Ψ E₁ E₂ a b Q) {y : ℝ} (hy : y ∈ ({E₁, E₂} : Set ℝ)) :
    ‖resolventMat Q ⟨y, η⟩ a a + 1‖ ≤ Ψ ∧ ‖resolventMat Q ⟨y, η⟩ b b + 1‖ ≤ Ψ ∧
      ‖resolventMat Q ⟨y, η⟩ a b‖ ≤ Ψ ∧ ‖resolventMat Q ⟨y, η⟩ b a‖ ≤ Ψ := by
  have ha : a ∈ ({a, b} : Set n) := by simp
  have hb : b ∈ ({a, b} : Set n) := by simp
  have h1 := hend a ha a ha y hy
  have h2 := hend b hb b hb y hy
  have h3 := hend a ha b hb y hy
  have h4 := hend b hb a ha y hy
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne hab,
    Matrix.one_apply_ne hab.symm, add_zero] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The endpoint condition (11.25) at `z = y + iη`, `a = b`. -/
private lemma expand_end_diag {η Ψ E₁ E₂ : ℝ} {Q : Matrix n n ℂ} {a : n}
    (hend : EndpointGood η Ψ E₁ E₂ a a Q) {y : ℝ} (hy : y ∈ ({E₁, E₂} : Set ℝ)) :
    ‖resolventMat Q ⟨y, η⟩ a a + 1‖ ≤ Ψ := by
  have h := hend a (by simp) a (by simp) y hy
  simpa only [Matrix.add_apply, Matrix.one_apply_eq] using h

/-- Lemma 11.16 (a), case `a ≠ b`, with the constants `4/3, 5/3, 16/9` of its proof. -/
private lemma expand_deltas_offDiag {E₁ E₂ η Ψ : ℝ} (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8)
    {Q : Matrix n n ℂ} {a b : n} (hab : a ≠ b) (hend : EndpointGood η Ψ E₁ E₂ a b Q) (v : ℂ) :
    |expDelta1 E₁ E₂ η Q a b v| ≤ 4 / 3 * ‖v‖ * Ψ ∧
      |expDelta2 E₁ E₂ η Q a b v| ≤ 5 / 3 * ‖v‖ ^ 2 * Ψ ∧
      |expDelta3 E₁ E₂ η Q a b v| ≤ 16 / 9 * ‖v‖ ^ 3 * Ψ := by
  obtain ⟨hp₁, hq₁, hr₁, hs₁⟩ := expand_end_offDiag hab hend (y := E₁) (by simp)
  obtain ⟨hp₂, hq₂, hr₂, hs₂⟩ := expand_end_offDiag hab hend (y := E₂) (by simp)
  obtain ⟨hu₁, hT₁, hU₁, -⟩ := expand_pt hΨ hΨ' hp₁ hq₁ hr₁ hs₁ v
  obtain ⟨hu₂, hT₂, hU₂, -⟩ := expand_pt hΨ hΨ' hp₂ hq₂ hr₂ hs₂ v
  unfold expDelta1 expDelta2 expDelta3 pairG
  simp only [hab, ↓reduceIte]
  set p₁ := resolventMat Q ⟨E₁, η⟩ a a
  set q₁ := resolventMat Q ⟨E₁, η⟩ b b
  set r₁ := resolventMat Q ⟨E₁, η⟩ a b
  set s₁ := resolventMat Q ⟨E₁, η⟩ b a
  set p₂ := resolventMat Q ⟨E₂, η⟩ a a
  set q₂ := resolventMat Q ⟨E₂, η⟩ b b
  set r₂ := resolventMat Q ⟨E₂, η⟩ a b
  set s₂ := resolventMat Q ⟨E₂, η⟩ b a
  set N : ℂ := ((‖v‖ ^ 2 : ℝ) : ℂ)
  refine ⟨?_, ?_, ?_⟩
  · rw [show v * (s₂ - s₁) + star v * (r₂ - r₁) =
        (v * s₂ + star v * r₂) - (v * s₁ + star v * r₁) by ring, neg_mul, abs_neg]
    refine (expand_two ((Complex.abs_im_le_norm _).trans hu₁)
      ((Complex.abs_im_le_norm _).trans hu₂)).trans (le_of_eq ?_)
    ring
  · rw [show N * (p₂ * q₂ - p₁ * q₁) + v ^ 2 / 2 * (s₂ ^ 2 - s₁ ^ 2) +
        star v ^ 2 / 2 * (r₂ ^ 2 - r₁ ^ 2) =
        (N * (p₂ * q₂) + v ^ 2 / 2 * s₂ ^ 2 + star v ^ 2 / 2 * r₂ ^ 2) -
          (N * (p₁ * q₁) + v ^ 2 / 2 * s₁ ^ 2 + star v ^ 2 / 2 * r₁ ^ 2) by ring]
    refine (expand_two hT₁ hT₂).trans (le_of_eq ?_)
    ring
  · rw [show N * v * (s₂ * (p₂ * q₂ - r₂ * s₂) - s₁ * (p₁ * q₁ - r₁ * s₁)) +
        N * star v * (r₂ * (p₂ * q₂ - r₂ * s₂) - r₁ * (p₁ * q₁ - r₁ * s₁)) =
        (N * v * (s₂ * (p₂ * q₂ - r₂ * s₂)) + N * star v * (r₂ * (p₂ * q₂ - r₂ * s₂))) -
          (N * v * (s₁ * (p₁ * q₁ - r₁ * s₁)) + N * star v * (r₁ * (p₁ * q₁ - r₁ * s₁))) by ring,
      neg_mul, abs_neg]
    refine (expand_two ((Complex.abs_im_le_norm _).trans hU₁)
      ((Complex.abs_im_le_norm _).trans hU₂)).trans (le_of_eq ?_)
    ring

/-- Lemma 11.16 (a), case `a = b`, with the constants `2/3, 17/24` of its proof, in terms of
`Re v`. -/
private lemma expand_deltas_diag {E₁ E₂ η Ψ : ℝ} (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8)
    {Q : Matrix n n ℂ} {a : n} (hend : EndpointGood η Ψ E₁ E₂ a a Q) (v : ℂ) :
    |expDelta1 E₁ E₂ η Q a a v| ≤ 2 / 3 * |v.re| * Ψ ∧
      |expDelta2 E₁ E₂ η Q a a v| ≤ 17 / 24 * v.re ^ 2 * Ψ := by
  obtain ⟨hi₁, hs₁, -⟩ := expand_diag_pt hΨ hΨ' (expand_end_diag hend (y := E₁) (by simp))
  obtain ⟨hi₂, hs₂, -⟩ := expand_diag_pt hΨ hΨ' (expand_end_diag hend (y := E₂) (by simp))
  unfold expDelta1 expDelta2
  simp only [↓reduceIte]
  constructor
  · rw [show -(v.re / π) * (resolventMat Q ⟨E₂, η⟩ a a - resolventMat Q ⟨E₁, η⟩ a a).im =
        -v.re * (π⁻¹ * (resolventMat Q ⟨E₂, η⟩ a a - resolventMat Q ⟨E₁, η⟩ a a).im) by ring,
      abs_mul, abs_neg]
    calc |v.re| * |π⁻¹ * (resolventMat Q ⟨E₂, η⟩ a a - resolventMat Q ⟨E₁, η⟩ a a).im|
        ≤ |v.re| * (2 / 3 * Ψ) := by gcongr; exact expand_two hi₁ hi₂
      _ = 2 / 3 * |v.re| * Ψ := by ring
  · rw [show v.re ^ 2 / (2 * π) *
        (resolventMat Q ⟨E₂, η⟩ a a ^ 2 - resolventMat Q ⟨E₁, η⟩ a a ^ 2).im =
        v.re ^ 2 / 2 *
          (π⁻¹ * (resolventMat Q ⟨E₂, η⟩ a a ^ 2 - resolventMat Q ⟨E₁, η⟩ a a ^ 2).im) by
          field_simp,
      abs_mul, abs_of_nonneg (by positivity)]
    calc v.re ^ 2 / 2 *
          |π⁻¹ * (resolventMat Q ⟨E₂, η⟩ a a ^ 2 - resolventMat Q ⟨E₁, η⟩ a a ^ 2).im|
        ≤ v.re ^ 2 / 2 * (2 / 3 * (17 / 8 * Ψ)) := by gcongr; exact expand_two hs₁ hs₂
      _ = 17 / 24 * v.re ^ 2 * Ψ := by ring

/-- The exact split of Step 3 of the proof of Lemma 11.16, `a ≠ b`: if `Y = Log(1+ζ) - u +
(w + u²/2) - uw` at both endpoints, then `Δ - Δ₁ - Δ₂ - Δ₃ = -π⁻¹ Im [Y]`. -/
private lemma expand_split_offDiag {Y₁ Y₂ A B C D : ℂ} {K : ℝ} (hY : Y₂ - Y₁ = A - B + C - D)
    (h₁ : |Y₁.im| ≤ K) (h₂ : |Y₂.im| ≤ K) :
    |-π⁻¹ * A.im - -π⁻¹ * B.im - π⁻¹ * C.im - -π⁻¹ * D.im| ≤ 2 / 3 * K := by
  have e : -π⁻¹ * A.im - -π⁻¹ * B.im - π⁻¹ * C.im - -π⁻¹ * D.im = -(π⁻¹ * (Y₂ - Y₁).im) := by
    rw [hY]
    simp only [Complex.sub_im, Complex.add_im]
    ring
  rw [e, abs_neg]
  exact expand_two h₁ h₂

/-- The exact split of the case `a = b` of the proof of Lemma 11.16, for real `v`: if
`Y = Log(1+ζ) - ζ + ζ²/2` with `ζ = v R_aa` at both endpoints, then
`Δ - Δ₁ - Δ₂ = -π⁻¹ Im [Y]`. -/
private lemma expand_split_diag {L₁ L₂ R₁ R₂ : ℂ} {v K : ℝ}
    (h₁ : |(L₁ - (v : ℂ) * R₁ + ((v : ℂ) * R₁) ^ 2 / 2).im| ≤ K)
    (h₂ : |(L₂ - (v : ℂ) * R₂ + ((v : ℂ) * R₂) ^ 2 / 2).im| ≤ K) :
    |-π⁻¹ * (L₂ - L₁).im - -(v / π) * (R₂ - R₁).im - v ^ 2 / (2 * π) * (R₂ ^ 2 - R₁ ^ 2).im| ≤
      2 / 3 * K := by
  have hY : (L₂ - (v : ℂ) * R₂ + ((v : ℂ) * R₂) ^ 2 / 2) - (L₁ - (v : ℂ) * R₁ +
      ((v : ℂ) * R₁) ^ 2 / 2) = (L₂ - L₁) - (v : ℂ) * (R₂ - R₁) +
        ((v ^ 2 / 2 : ℝ) : ℂ) * (R₂ ^ 2 - R₁ ^ 2) := by
    push_cast; ring
  have e : -π⁻¹ * (L₂ - L₁).im - -(v / π) * (R₂ - R₁).im - v ^ 2 / (2 * π) * (R₂ ^ 2 - R₁ ^ 2).im =
      -(π⁻¹ * ((L₂ - (v : ℂ) * R₂ + ((v : ℂ) * R₂) ^ 2 / 2) - (L₁ - (v : ℂ) * R₁ +
        ((v : ℂ) * R₁) ^ 2 / 2)).im) := by
    rw [hY]
    simp only [Complex.add_im, Complex.sub_im, Complex.im_ofReal_mul]
    field_simp
    ring
  rw [e, abs_neg]
  exact expand_two h₁ h₂

/-- Lemma 11.16 (a), the bounds on `Δ₁, Δ₂, Δ₃`. -/
theorem abs_expDelta_le {E₁ E₂ η Ψ : ℝ} (hη : 0 < η) (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8)
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {a b : n} (hend : EndpointGood η Ψ E₁ E₂ a b Q)
    (v : ℂ) :
    |expDelta1 E₁ E₂ η Q a b v| ≤ 2 * ‖v‖ * Ψ ∧ |expDelta2 E₁ E₂ η Q a b v| ≤ 3 * ‖v‖ ^ 2 * Ψ ∧
      |expDelta3 E₁ E₂ η Q a b v| ≤ 3 * ‖v‖ ^ 3 * Ψ := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨h1, h2⟩ := expand_deltas_diag hΨ hΨ' hend v
    have hre := Complex.abs_re_le_norm v
    have hv0 := norm_nonneg v
    have hre2 : v.re ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
    refine ⟨h1.trans ?_, h2.trans ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right hre hΨ.le
      nlinarith
    · have := mul_le_mul_of_nonneg_right hre2 hΨ.le
      nlinarith
    · unfold expDelta3
      simp only [↓reduceIte, abs_zero]
      positivity
  · obtain ⟨h1, h2, h3⟩ := expand_deltas_offDiag hΨ hΨ' hab hend v
    have k1 : 0 ≤ ‖v‖ * Ψ := mul_nonneg (norm_nonneg v) hΨ.le
    have k2 : 0 ≤ ‖v‖ ^ 2 * Ψ := mul_nonneg (by positivity) hΨ.le
    have k3 : 0 ≤ ‖v‖ ^ 3 * Ψ := mul_nonneg (by positivity) hΨ.le
    refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩ <;> nlinarith

/-- Lemma 11.16 (a), the bounds on `g`. -/
theorem norm_pairG_le {E₁ E₂ η Ψ : ℝ} (hη : 0 < η) (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8)
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {a b : n} (hab : a ≠ b)
    (hend : EndpointGood η Ψ E₁ E₂ a b Q) {y : ℝ} (hy : y ∈ ({E₁, E₂} : Set ℝ)) :
    ‖pairG (resolventMat Q ⟨y, η⟩) a b - 1‖ ≤ 9 / 4 * Ψ ∧
      ‖pairG (resolventMat Q ⟨y, η⟩) a b‖ ≤ 4 / 3 := by
  obtain ⟨hp, hq, hr, hs⟩ := expand_end_offDiag hab hend hy
  unfold pairG
  exact expand_g hΨ hΨ' hp hq hr hs

/-- Lemma 11.16 (b), case `a ≠ b`. -/
theorem expand_offDiag {E₁ E₂ η Ψ : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (hΨ : 0 < Ψ)
    (hΨ' : Ψ ≤ 1 / 8) {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {a b : n} (hab : a ≠ b)
    (hend : EndpointGood η Ψ E₁ E₂ a b Q) (F : ℝ → ℝ) (CF : ℝ) (hF : ContDiff ℝ 3 F)
    (hFb : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) (v : ℂ)
    (hv : ‖v‖ ≤ Ψ / 40) :
    |F (smoothCount E₁ E₂ η (Q + entryMat a b v)) - F (smoothCount E₁ E₂ η Q) -
        iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a b v -
        (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta2 E₁ E₂ η Q a b v +
          1 / 2 * iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a b v ^ 2) -
        iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta3 E₁ E₂ η Q a b v| ≤
      4 * CF * (‖v‖ ^ 3 * Ψ ^ 2 + ‖v‖ ^ 4 * Ψ) ∧
    |smoothCount E₁ E₂ η (Q + entryMat a b v) - smoothCount E₁ E₂ η Q| ≤ 3 / 2 * ‖v‖ * Ψ := by
  have hsc := smoothCount_add_entryMat hQ hη hE a b v
  obtain ⟨h1, h2, h3⟩ := expand_deltas_offDiag hΨ hΨ' hab hend v
  obtain ⟨hp₁, hq₁, hr₁, hs₁⟩ := expand_end_offDiag hab hend (y := E₁) (by simp)
  obtain ⟨hp₂, hq₂, hr₂, hs₂⟩ := expand_end_offDiag hab hend (y := E₂) (by simp)
  have hY₁ := expand_log_pt hΨ hΨ' hp₁ hq₁ hr₁ hs₁ hv
  have hY₂ := expand_log_pt hΨ hΨ' hp₂ hq₂ hr₂ hs₂ hv
  have hr : |(smoothCount E₁ E₂ η (Q + entryMat a b v) - smoothCount E₁ E₂ η Q) -
      expDelta1 E₁ E₂ η Q a b v - expDelta2 E₁ E₂ η Q a b v - expDelta3 E₁ E₂ η Q a b v| ≤
      4 * ‖v‖ ^ 3 * Ψ ^ 3 + 2 * ‖v‖ ^ 4 * Ψ := by
    rw [hsc]
    unfold expDelta1 expDelta2 expDelta3 pairG entryDet
    simp only [hab, ↓reduceIte]
    refine (expand_split_offDiag ?_ hY₁ hY₂).trans (le_of_eq ?_)
    · ring
    · ring
  have hT := expand_taylor hF (fun x => hFb 3 (by norm_num) le_rfl x) (smoothCount E₁ E₂ η Q)
    (smoothCount E₁ E₂ η (Q + entryMat a b v))
  obtain ⟨hm, hd⟩ := expand_offDiag_real (norm_nonneg v) hΨ hΨ' hv
    (hFb 1 le_rfl (by norm_num) _) (hFb 2 (by norm_num) (by norm_num) _) h1 h2 h3 hr hT
  exact ⟨le_trans (le_of_eq (congrArg abs (by ring))) hm, hd⟩

/-- Lemma 11.16 (b), case `a = b`. -/
theorem expand_diag {E₁ E₂ η Ψ : ℝ} (hη : 0 < η) (hE : E₁ ≤ E₂) (hΨ : 0 < Ψ)
    (hΨ' : Ψ ≤ 1 / 8) {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {a : n}
    (hend : EndpointGood η Ψ E₁ E₂ a a Q) (F : ℝ → ℝ) (CF : ℝ) (hF : ContDiff ℝ 3 F)
    (hFb : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → ∀ x, |iteratedDeriv k F x| ≤ CF) (v : ℝ)
    (hv : |v| ≤ 1 / 4) :
    |F (smoothCount E₁ E₂ η (Q + entryMat a a v)) - F (smoothCount E₁ E₂ η Q) -
        iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a a v -
        (iteratedDeriv 1 F (smoothCount E₁ E₂ η Q) * expDelta2 E₁ E₂ η Q a a v +
          1 / 2 * iteratedDeriv 2 F (smoothCount E₁ E₂ η Q) * expDelta1 E₁ E₂ η Q a a v ^ 2)| ≤
      4 * CF * (|v| ^ 3 * Ψ + v ^ 4) ∧
    |smoothCount E₁ E₂ η (Q + entryMat a a v) - smoothCount E₁ E₂ η Q| ≤ |v| * Ψ + v ^ 4 := by
  have hsc := smoothCount_add_entryMat hQ hη hE a a (v : ℂ)
  obtain ⟨h1, h2⟩ := expand_deltas_diag hΨ hΨ' hend (v : ℂ)
  rw [Complex.ofReal_re] at h1 h2
  obtain ⟨-, -, hY₁⟩ := expand_diag_pt hΨ hΨ' (expand_end_diag hend (y := E₁) (by simp))
  obtain ⟨-, -, hY₂⟩ := expand_diag_pt hΨ hΨ' (expand_end_diag hend (y := E₂) (by simp))
  have h4 : |v| ^ 4 = v ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  have hr : |(smoothCount E₁ E₂ η (Q + entryMat a a v) - smoothCount E₁ E₂ η Q) -
      expDelta1 E₁ E₂ η Q a a v - expDelta2 E₁ E₂ η Q a a v| ≤ |v| ^ 3 * Ψ + |v| ^ 4 := by
    rw [hsc]
    unfold expDelta1 expDelta2 entryDet
    simp only [↓reduceIte, Complex.ofReal_re]
    refine (expand_split_diag (hY₁ v hv) (hY₂ v hv)).trans ?_
    have : 0 ≤ |v| ^ 3 * Ψ := by positivity
    rw [h4]
    nlinarith
  have hT := expand_taylor hF (fun x => hFb 3 (by norm_num) le_rfl x) (smoothCount E₁ E₂ η Q)
    (smoothCount E₁ E₂ η (Q + entryMat a a v))
  rw [← sq_abs] at h2
  obtain ⟨hm, hd⟩ := expand_diag_real (abs_nonneg v) hΨ hΨ' hv
    (hFb 1 le_rfl (by norm_num) _) (hFb 2 (by norm_num) (by norm_num) _) h1 h2 hr hT
  rw [h4] at hm hd
  exact ⟨le_trans (le_of_eq (congrArg abs (by ring))) hm, hd⟩

end ExpandC

end Rigidity
