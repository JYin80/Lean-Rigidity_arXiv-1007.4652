module

public import Rigidity.Fluctuation.Lattice
public import Rigidity.Strong.Helpers

@[expose] public section

/-!
# The strong local law, first pass (NP v1.1, §7.1: Proposition 7.1)

Numbers in this file refer to the blueprint NP v1.1.

`b = 12a + 12` is `ledgerB a`, `𝔈 = K^b`; the quantity `𝔉 = C_F p₁^{c_F}` of Corollary 6.2 enters
through its bound `K^{12a+11}`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `𝒢¹(z) = 𝒢_col(z) ∩ {|⟨X⟩(z)| ≤ K𝔈/(Nη) (ϰ + 𝔈/(Nη))}` of Proposition 7.1. -/
def strongG1 {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  goodCol M a C₀ K z ∩
    {x | ‖(N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k‖ ≤
      K * K ^ ledgerB a / (N * z.im) * (varkappa z + K ^ ledgerB a / (N * z.im))}

/-! The proof of Proposition 7.1 follows Steps 1–4 of NP v1.1, §7.1, with `𝔉` replaced by its
bound `K^{12a+11}` of (T1). Where the original paper (Erdős–Yau–Yin, arXiv:1007.4652) has a
counterpart, it is cited as [EYY, …].

* Step 1 (7.a): on `𝒢_col(z)`, Lemma 5.1 (5.4) and the scalar inequality of Lemma 3.11 give
  `Λ ≤ 17ϰ + 7𝔈₀/u + 2|⟨X⟩|^{1/2}`, with `u = Nη`.
* Step 2 (7.b), (7.c): `‖Λ‖_p ≤ Y + N^{-8}` by (T6), `|Φ_*²| ≤ 151ϰ/u + Λ/u + p/u²` by (T4),
  and Corollary 6.2 at `p = p₁`.
* Step 3: Minkowski's inequality and (M) give `Y ≤ 17ϰ + 7𝔈₀/u + 2‖⟨X⟩‖_p^{1/2}`; together with
  (7.c) and `Y ≤ 2N < ∞` this closes to `Y ≤ 42ϰ + 𝔈/u`, and then (7.2) follows from (7.c).
* Step 4: Markov's inequality at `p₁` and `194/K² ≤ e^{-1}`. -/

/-! ### 1. Continuity -/

/-- For `Im z > 0`, the map `x ↦ m(z) = N⁻¹ tr G(z)` is continuous. -/
private lemma firstPass_continuous_m {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun x : Pair N → 𝕜 => stieltjesEmp (toMatrix x) z := by
  have hg : ∀ k : Fin N, Continuous fun x : Pair N → 𝕜 => green (toMatrix x) z k k := by
    intro k
    have h1 := ((polyGrowth_schurM M 0 hz ∅).2.2.2.1 k).1
    have h0 : ∀ x : Pair N → 𝕜, 1 / green (toMatrix x) z k k ≠ 0 := fun x => by
      refine one_div_ne_zero fun h => ?_
      have := green_im_diag_pos (toMatrix_isHermitian x) hz k
      rw [h] at this
      simp at this
    refine (h1.inv₀ h0).congr fun x => ?_
    simp
  unfold stieltjesEmp Matrix.trace
  exact continuous_const.mul (continuous_finsetSum _ fun k _ => hg k)

/-! ### 2. Scalar inequalities -/

/-- The real statement of Lemma 3.11: `x² ≤ βx + r²` with `β, r ≥ 0` gives `x ≤ β + r`. -/
private lemma firstPass_scalar {x β r : ℝ} (hβ : 0 ≤ β) (hr : 0 ≤ r)
    (h : x ^ 2 ≤ β * x + r ^ 2) : x ≤ β + r := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  nlinarith [mul_le_mul_of_nonneg_left hlt.le hr]

/-- The closing step of Step 3: `y ≤ c + 2s` and `s² ≤ r² + B y` with `c, B, r ≥ 0` give
`y ≤ 2c + 4B + 2r`. -/
private lemma firstPass_close {y c s B r : ℝ} (hc : 0 ≤ c)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (h1 : y ≤ c + 2 * s) (h2 : s ^ 2 ≤ r ^ 2 + B * y) :
    y ≤ 2 * c + 4 * B + 2 * r := by
  rcases le_or_gt y c with hyc | hyc
  · linarith
  have h3 : y ^ 2 ≤ (2 * c + 4 * B) * y + (2 * r) ^ 2 := by
    have : (y - c) ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith
  have := firstPass_scalar (by positivity) (by positivity) h3
  linarith

/-! ### 3. Deterministic steps -/

/-- Step 1 of the proof of Proposition 7.1, (7.a): from (5.4) in the form
`|w² - w₀w| ≤ |⟨X⟩| + 𝔈₀((Im m_sc + Λ)/u + 1/u²) + ¾Λ²` with `Λ = |w|`, `|w₀| ≤ 4ϰ`,
`0 ≤ Im m_sc ≤ ϰ` and `𝔈₀ ≥ 1` one has `Λ ≤ 17ϰ + 7𝔈₀/u + 2|⟨X⟩|^{1/2}`. -/
private lemma firstPass_step1 {w w₀ : ℂ} {X ϰ I E₀ u : ℝ} (hX : 0 ≤ X) (hu : 0 < u)
    (hw₀ : ‖w₀‖ ≤ 4 * ϰ) (hI0 : 0 ≤ I) (hI : I ≤ ϰ) (hE₀ : 1 ≤ E₀)
    (hq : ‖w ^ 2 - w₀ * w‖ ≤ X + E₀ * ((I + ‖w‖) / u + 1 / u ^ 2) + 3 / 4 * ‖w‖ ^ 2) :
    ‖w‖ ≤ 17 * ϰ + 7 * (E₀ / u) + 2 * Real.sqrt X := by
  have hsq : ‖w‖ ^ 2 ≤ ‖w₀‖ * ‖w‖ + ‖w ^ 2 - w₀ * w‖ := by
    calc ‖w‖ ^ 2 = ‖w₀ * w + (w ^ 2 - w₀ * w)‖ := by rw [← norm_pow]; ring_nf
      _ ≤ ‖w₀ * w‖ + ‖w ^ 2 - w₀ * w‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul]
  set s := Real.sqrt X with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = X := Real.sq_sqrt hX
  set e := E₀ / u with he_def
  have he0 : 0 ≤ e := by positivity
  have hϰ0 : 0 ≤ ϰ := hI0.trans hI
  have hexp : E₀ * ((I + ‖w‖) / u + 1 / u ^ 2) = e * I + e * ‖w‖ + e * (1 / u) := by
    rw [he_def]; ring
  have he1 : 1 / u ≤ e := by
    rw [he_def]; exact div_le_div_of_nonneg_right hE₀ hu.le
  have hn0 : 0 ≤ ‖w‖ := norm_nonneg _
  have key : ‖w‖ ^ 2 ≤ (16 * ϰ + 4 * e) * ‖w‖ + (2 * s + ϰ + 3 * e) ^ 2 := by
    rw [hexp] at hq
    have h1 : ‖w₀‖ * ‖w‖ ≤ 4 * ϰ * ‖w‖ := mul_le_mul_of_nonneg_right hw₀ hn0
    have h2 : e * I ≤ e * ϰ := mul_le_mul_of_nonneg_left hI he0
    have h3 : e * (1 / u) ≤ e * e := mul_le_mul_of_nonneg_left he1 he0
    nlinarith [mul_nonneg hs0 hϰ0, mul_nonneg hs0 he0, mul_nonneg hϰ0 he0, sq_nonneg ϰ]
  have := firstPass_scalar (by positivity) (by positivity) key
  linarith

/-- The pointwise bound of Step 2: with `u = Nη`, `η/150 ≤ Im m_sc ≤ ϰ` and
`|Im m| ≤ Im m_sc + Λ`, one has `|Φ_*²| ≤ 151ϰ/u + p/u² + Λ/u`. -/
private lemma firstPass_phi {n η t I ϰ Λ p : ℝ} (hn : 0 < n) (hη : 0 < η) (hp : 0 ≤ p)
    (hI : η / 150 ≤ I) (hIϰ : I ≤ ϰ) (ht : |t| ≤ I + Λ) :
    |1 / n + 1 / (n * η) * (t + p / (n * η))| ≤
      151 * ϰ * (1 / (n * η)) + p * (1 / (n * η)) ^ 2 + 1 / (n * η) * Λ := by
  set v := 1 / (n * η) with hv_def
  have hv0 : 0 < v := by positivity
  have hnv : 1 / n = η * v := by rw [hv_def]; field_simp
  have hηv : η * v ≤ 150 * I * v := by
    have := mul_le_mul_of_nonneg_right hI hv0.le
    linarith
  have hexp : 1 / n + v * (t + p / (n * η)) = η * v + v * t + p * v ^ 2 := by
    rw [hnv, hv_def]; ring
  rw [hexp, abs_le]
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self t) hv0.le
  have h2 := mul_le_mul_of_nonneg_left (neg_abs_le t) hv0.le
  have h3 := mul_le_mul_of_nonneg_left ht hv0.le
  have h4 := mul_le_mul_of_nonneg_left hIϰ hv0.le
  have h5 : 0 ≤ p * v ^ 2 := by positivity
  have h6 : 0 ≤ η * v := by positivity
  constructor <;> nlinarith

/-- Step 3 and the derivation of (7.2), in real numbers: from (7.a) in `L^p`, (7.b), the bound on
`‖Φ_*²‖_p` and Corollary 6.2, with `v = 1/u`, `𝔉 = K^{12a+11}`, `𝔈 = K𝔉`, `q = N⁻⁴`, one gets
`Y ≤ 42ϰ + 𝔈/u` and `‖⟨X⟩‖_p ≤ 194 (𝔉/u)(ϰ + 𝔈/u)`. -/
private lemma firstPass_algebra {y ℓ φ ξ ϰ v F E E₀ K p q : ℝ} (hξ0 : 0 ≤ ξ)
    (hϰ : 0 < ϰ) (hv : 0 < v) (hF1 : 1 ≤ F) (hFv : F * v ≤ 1) (hE₀ : E₀ ≤ F) (hE₀1 : 1 ≤ E₀)
    (hp0 : 0 ≤ p) (hp4 : p ≤ 4 * F) (hpE : p ≤ E) (hEF : E = K * F) (hK : 400 ≤ K) (hq0 : 0 < q)
    (hqϰ : q ≤ ϰ) (hq2 : 2 * q ^ 2 ≤ F * ϰ * v)
    (hY : y ≤ 17 * ϰ + 7 * (E₀ * v) + 2 * Real.sqrt ξ) (hℓ : ℓ ≤ y + q ^ 2)
    (hφ : φ ≤ 151 * ϰ * v + p * v ^ 2 + v * ℓ) (hξ : ξ ≤ F * φ + q ^ 2) :
    y ≤ 42 * ϰ + E * v ∧ ξ ≤ 194 * F * v * (ϰ + E * v) := by
  have hF0 : 0 ≤ F := by linarith
  have hE0 : 0 ≤ E := by linarith
  set B := F * v with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hξ' : ξ ≤ 151 * ϰ * B + F * p * v ^ 2 + B * y + B * q ^ 2 + q ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hφ hF0
    have h2 := mul_le_mul_of_nonneg_left hℓ hB0
    have e1 : F * (151 * ϰ * v + p * v ^ 2 + v * ℓ) = 151 * ϰ * B + F * p * v ^ 2 + B * ℓ := by
      rw [hB_def]; ring
    linarith
  set s := Real.sqrt ξ with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = ξ := Real.sq_sqrt hξ0
  have hFpv : F * p * v ^ 2 ≤ 4 * B ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hp4 (by positivity : (0 : ℝ) ≤ F * v ^ 2)
    have e1 : F * v ^ 2 * (4 * F) = 4 * B ^ 2 := by rw [hB_def]; ring
    have e2 : F * v ^ 2 * p = F * p * v ^ 2 := by ring
    linarith
  have hBq : B * q ^ 2 ≤ q ^ 2 := by
    have := mul_le_mul_of_nonneg_right hFv (sq_nonneg q)
    linarith
  set r := (ϰ + 151 * B) / 2 + 2 * B + 3 / 2 * q with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr2 : s ^ 2 ≤ r ^ 2 + B * y := by
    have e1 : r ^ 2 = (ϰ - 151 * B) ^ 2 / 4 + 151 * ϰ * B + 2 * (ϰ + 151 * B) * B +
        3 / 2 * (ϰ + 151 * B) * q + 4 * B ^ 2 + 6 * B * q + 9 / 4 * q ^ 2 := by
      rw [hr_def]; ring
    have h1 := sq_nonneg (ϰ - 151 * B)
    have h2 : 0 ≤ 2 * (ϰ + 151 * B) * B := by positivity
    have h3 : 0 ≤ 3 / 2 * (ϰ + 151 * B) * q := by positivity
    have h4 : 0 ≤ 6 * B * q := by positivity
    have h5 : 0 ≤ q ^ 2 := sq_nonneg q
    rw [hss]
    linarith
  have hc : 0 ≤ 17 * ϰ + 7 * (E₀ * v) := by positivity
  have hYb := firstPass_close hc hB0 hr0 hY hr2
  have hE₀v : E₀ * v ≤ B := mul_le_mul_of_nonneg_right hE₀ hv.le
  have hKF : 173 * B ≤ E * v := by
    have e1 : E * v = K * B := by rw [hEF, hB_def]; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (by linarith) hB0
  have hy42 : y ≤ 42 * ϰ + E * v := by
    have e1 : 2 * (17 * ϰ + 7 * (E₀ * v)) + 4 * B + 2 * r =
        35 * ϰ + 14 * (E₀ * v) + 159 * B + 3 * q := by
      rw [hr_def]; ring
    linarith
  refine ⟨hy42, ?_⟩
  have hpv : F * p * v ^ 2 ≤ B * (E * v) := by
    have h1 := mul_le_mul_of_nonneg_left hpE (by positivity : (0 : ℝ) ≤ F * v ^ 2)
    have e1 : F * v ^ 2 * E = B * (E * v) := by rw [hB_def]; ring
    have e2 : F * v ^ 2 * p = F * p * v ^ 2 := by ring
    linarith
  have hy' := mul_le_mul_of_nonneg_left hy42 hB0
  have hq2' : 2 * q ^ 2 ≤ B * ϰ := by
    have e1 : F * ϰ * v = B * ϰ := by rw [hB_def]; ring
    linarith
  have e2 : 194 * F * v * (ϰ + E * v) = 194 * (B * ϰ) + 194 * (B * (E * v)) := by
    rw [hB_def]; ring
  have h3 : 0 ≤ B * (E * v) := by positivity
  rw [e2]
  nlinarith

/-- The sizes used in the proof of Proposition 7.1, at `z ∈ 𝐃^near`, `K ≥ 400`, `N ≥ 13`, with
`𝔉 = K^{12a+11}`, `𝔈 = K^b`, `u = Nη`, `q = N⁻⁴`: `𝔈 = K𝔉`, `1 ≤ 𝔉 ≤ u` (T4), `𝔈₀ ≤ 𝔉`,
`p₁ ≤ 4𝔉`, `p₁ ≤ 𝔈`, `q ≤ ϰ`, `2q² ≤ 𝔉ϰ/u` and `N^{-8} = q²`. -/
private lemma firstPass_sizes {a K E₀ p : ℝ} {N : ℕ} {z : ℂ} (ha : 1 ≤ a) (hK : 400 ≤ K)
    (hN : 13 ≤ N) (hz : z ∈ Dnear a K N) (hE₀ : E₀ ≤ K ^ (8 * a + 7))
    (hp2 : p ≤ 2 * K ^ (3 / 2 : ℝ)) :
    K ^ ledgerB a = K * K ^ (12 * a + 11) ∧ 1 ≤ K ^ (12 * a + 11) ∧
      K ^ (12 * a + 11) * (1 / (N * z.im)) ≤ 1 ∧ E₀ ≤ K ^ (12 * a + 11) ∧
      p ≤ 4 * K ^ (12 * a + 11) ∧ p ≤ K ^ ledgerB a ∧ 1 / (N : ℝ) ^ 4 ≤ varkappa z ∧
      2 * (1 / (N : ℝ) ^ 4) ^ 2 ≤ K ^ (12 * a + 11) * varkappa z * (1 / (N * z.im)) ∧
      (N : ℝ) ^ (-8 : ℝ) = (1 / (N : ℝ) ^ 4) ^ 2 := by
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hNr : (13 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hη1, hu, hvk, -, -, -, -, -⟩ :=
    strong_T4 (𝕜 := ℂ) ha hK1 (by omega : 1 ≤ N) hz (0 : Pair N → ℂ)
  have hη0 : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  have hη10 : z.im ≤ 10 := hz.2.2
  have hu0 : (0 : ℝ) < N * z.im := mul_pos hNpos hη0
  set F := K ^ (12 * a + 11) with hF_def
  have hEF : K ^ ledgerB a = K * F := by
    rw [hF_def, ledgerB, show 12 * a + 12 = (12 * a + 11) + 1 by ring,
      Real.rpow_add_one hKpos.ne']
    ring
  have hF1 : 1 ≤ F := Real.one_le_rpow hK1 (by linarith)
  have hFu : F ≤ N * z.im :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hK1 (by unfold ledgerC1; linarith)) hu
  have hFv : F * (1 / (N * z.im)) ≤ 1 := by
    rw [mul_one_div, div_le_one hu0]
    exact hFu
  have hE0F : E₀ ≤ F := hE₀.trans (Real.rpow_le_rpow_of_exponent_le hK1 (by linarith))
  have hK32F : K ^ (3 / 2 : ℝ) ≤ F := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hp4F : p ≤ 4 * F := by linarith
  have hpE : p ≤ K ^ ledgerB a := by
    rw [hEF]
    nlinarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsNN : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hn8q : (N : ℝ) ^ (-8 : ℝ) = (1 / (N : ℝ) ^ 4) ^ 2 := by
    rw [show (-8 : ℝ) = -((8 : ℕ) : ℝ) by norm_num, Real.rpow_neg hNpos.le, Real.rpow_natCast]
    ring
  have hqϰ : 1 / (N : ℝ) ^ 4 ≤ varkappa z := by
    refine le_trans (one_div_le_one_div_of_le hsN ?_) hvk
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hϰ0 : 0 < varkappa z := lt_of_lt_of_le (by positivity) hvk
  have hq2 : 2 * (1 / (N : ℝ) ^ 4) ^ 2 ≤ F * varkappa z * (1 / (N * z.im)) := by
    have hvN : 1 / (10 * (N : ℝ)) ≤ 1 / (N * z.im) :=
      one_div_le_one_div_of_le hu0 (by nlinarith)
    have hϰv : 1 / Real.sqrt N * (1 / (10 * N)) ≤ varkappa z * (1 / (N * z.im)) :=
      mul_le_mul hvk hvN (by positivity) hϰ0.le
    have h20 : (20 : ℝ) * N ^ 2 ≤ (N : ℝ) ^ 8 := by
      have : (20 : ℝ) ≤ (N : ℝ) ^ 6 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hNr 6)
      have e : (N : ℝ) ^ 8 = (N : ℝ) ^ 6 * N ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h2 : 2 * (1 / (N : ℝ) ^ 4) ^ 2 ≤ 1 / Real.sqrt N * (1 / (10 * N)) := by
      rw [div_pow, one_pow, ← pow_mul, one_div_mul_one_div, mul_one_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 2 * (Real.sqrt N * (10 * N)) ≤ 20 * (N : ℝ) ^ 2 := by nlinarith
      have e : (N : ℝ) ^ (4 * 2) = (N : ℝ) ^ 8 := by norm_num
      rw [e]
      linarith
    have h3 : varkappa z * (1 / (N * z.im)) ≤ F * varkappa z * (1 / (N * z.im)) := by
      have := mul_le_mul_of_nonneg_right hF1 (by positivity : 0 ≤ varkappa z * (1 / (N * z.im)))
      linarith
    linarith
  exact ⟨hEF, hF1, hFv, hE0F, hp4F, hpE, hqϰ, hq2, hn8q⟩

/-! ### 4. Proposition 7.1 -/

/-- Proposition 7.1: the upper-branch moment bounds (7.1), (7.2) at `p = p₁` on
`𝕃 ∩ 𝐃^near`, and the closed event `𝒢¹(z)` with `ℙ(𝒢_col(z) ∖ 𝒢¹(z)) ≤ e^{-p₁}`. -/
theorem strong_firstPass {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ lattice ϑ⁻¹ C₀ K N ∩ Dnear ϑ⁻¹ K N,
        eLpNorm ((goodCol M ϑ⁻¹ C₀ K z).indicator fun x => Lam x z) (levelP1 K) M.prodLaw ≤
            ENNReal.ofReal (42 * (varkappa z + K ^ ledgerB ϑ⁻¹ / (N * z.im))) ∧
          eLpNorm (fun x => (N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k) (levelP1 K)
              M.prodLaw ≤
            ENNReal.ofReal (194 * K ^ (12 * ϑ⁻¹ + 11) / (N * z.im) *
              (varkappa z + K ^ ledgerB ϑ⁻¹ / (N * z.im))) ∧
          IsClosed (strongG1 M ϑ⁻¹ C₀ K z) ∧ strongG1 M ϑ⁻¹ C₀ K z ⊆ goodCol M ϑ⁻¹ C₀ K z ∧
          M.prodLaw (goodCol M ϑ⁻¹ C₀ K z \ strongG1 M ϑ⁻¹ C₀ K z) ≤
            ENNReal.ofReal (Real.exp (-(levelP1 K : ℝ))) := by
  obtain ⟨N₁, h1⟩ := apriori_bounds (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨Cw, -, N₂, h2⟩ := weakLaw_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₃, h3⟩ := fluctuationAveraging_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₄, h4⟩ := strong_T6 (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₅, h5⟩ := standing_ineq hϑ hϑ1 hC₀ 400
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) N₅, ?_⟩
  intro N hN M hM K hK1 hK2 z hz
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : N₅ ≤ N := by omega
  have ha : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨⟨hK0, h13, -, hκ⟩, -, ⟨-, -, -, hp1lo, hp1hi⟩, -⟩ := h5 N hN5 K hK1 hK2
  have hK1' : (1 : ℝ) ≤ K := by linarith only [hK0]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the inputs: (T4), Lemma 5.1, Theorem 5.5 (a), Corollary 6.2 and (T6) at `p₁`
  obtain ⟨hη1, -, hvk, hmlo, hmhi, -, hw0, -⟩ :=
    strong_T4 ha hK1' (by omega : 1 ≤ N) hz.2 (0 : Pair N → 𝕜)
  have hΛ2N : ∀ x : Pair N → 𝕜, Lam x z ≤ 2 * N := fun x =>
    (strong_T4 ha hK1' (by omega : 1 ≤ N) hz.2 x).2.2.2.2.2.2.2
  have hη0 : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  have hmsc0 : 0 ≤ (msc z).im := le_trans (by positivity) hmlo
  obtain ⟨hE01, hE0K, hAP⟩ := h1 N hN1 M hM K hK1 hK2
  have hWL := (h2 N hN2 M hM K hK1 hK2 z hz.1).1
  have hFA := h3 N hN3 M hM K hK1 hK2 z hz.1 (levelP1 K) (by simp)
  have hT6 := (h4 N hN4 M hM K hK1 hK2 z hz.1 (levelP1 K) (by simp)).1
  obtain ⟨hEF, hF1, hFv, hE0F, hp4F, hpE, hqϰ, hq2, hn8q⟩ :=
    firstPass_sizes ha hK0 h13 hz.2 hE0K hp1hi
  -- notation
  set μ := M.prodLaw with hμ_def
  set p : ℕ := levelP1 K with hp_def
  set u : ℝ := (N : ℝ) * z.im with hu_def
  have hu0 : 0 < u := mul_pos hNpos hη0
  set v : ℝ := 1 / u with hv_def
  have hv0 : 0 < v := by positivity
  set ϰ : ℝ := varkappa z with hϰ_def
  have hϰ0 : 0 < ϰ := lt_of_lt_of_le (by positivity) hvk
  set F : ℝ := K ^ (12 * ϑ⁻¹ + 11) with hF_def
  set E : ℝ := K ^ ledgerB ϑ⁻¹ with hE_def
  set E₀ : ℝ := aprioriE0 ϑ⁻¹ C₀ δm δp K N with hE₀_def
  set q : ℝ := 1 / (N : ℝ) ^ 4 with hq_def
  have hq0 : 0 < q := by positivity
  set G := goodCol M ϑ⁻¹ C₀ K z with hG_def
  set X : (Pair N → 𝕜) → ℂ := fun x => (N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k
    with hX_def
  have hp1 : 1 ≤ p := by
    have : (1 : ℝ) ≤ K ^ (3 / 2 : ℝ) := Real.one_le_rpow hK1' (by norm_num)
    exact_mod_cast this.trans hp1lo
  have hp1E : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp1
  have hpne : (p : ℝ≥0∞) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpt : (p : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top p
  -- continuity and closedness
  have hmc := firstPass_continuous_m M hη0
  have hΛc : Continuous fun x : Pair N → 𝕜 => Lam x z := by
    unfold Lam
    exact (hmc.sub continuous_const).norm
  have hXc : Continuous X :=
    continuous_const.mul (continuous_finsetSum _ fun k _ =>
      ((polyGrowth_schurM M 0 hη0 ∅).2.2.2.2.1 k).1)
  have hΦc : Continuous fun x : Pair N → 𝕜 => phiStarSq (p : ℝ) x z := by
    unfold phiStarSq
    exact continuous_const.add
      (continuous_const.mul ((Complex.continuous_im.comp hmc).add continuous_const))
  have hGc : IsClosed G := isClosed_biInter fun w hw =>
    (goodEvent_level M hM hϑ hϑ1 hC₀ h13 (lt_of_lt_of_le hη0 hw.2.2) hκ).1
  have hGm : MeasurableSet G := hGc.measurableSet
  have hΛm : AEStronglyMeasurable (fun x => Lam x z) μ := hΛc.aestronglyMeasurable
  have hΛ0 : ∀ x : Pair N → 𝕜, 0 ≤ Lam x z := fun x => norm_nonneg _
  -- Step 1, (7.a): the pointwise bound on `𝒢_col(z)`
  have hzcol : z ∈ latticeCol ϑ⁻¹ C₀ K N z := ⟨hz.1, rfl, le_rfl⟩
  have hst : 0 < lamSt C₀ δm δp := by unfold lamSt stabCs; positivity
  have hstep1 : ∀ x ∈ G, Lam x z ≤ 17 * ϰ + 7 * (E₀ * v) + 2 * ‖X x‖ ^ (1 / 2 : ℝ) := by
    intro x hx
    have hxG : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z := Set.mem_iInter₂.1 hx z hzcol
    obtain ⟨hle, hle'⟩ := (hWL x hx).1 hz.2
    obtain ⟨-, -, -, -, -, -, -, hq, -, -, -, -, -⟩ :=
      hAP z hz.2 x hxG (by linarith only [hle, hle', hst])
    have := firstPass_step1 (norm_nonneg (X x)) hu0 hw0 hmsc0 hmhi hE01 hq
    have e : E₀ / u = E₀ * v := by rw [hv_def]; ring
    rwa [Real.sqrt_eq_rpow, e] at this
  -- (7.a) in `L^p`, with Minkowski's inequality and (M)
  have hYi : eLpNorm (G.indicator fun x => Lam x z) p μ ≤
      ENNReal.ofReal (17 * ϰ + 7 * (E₀ * v)) + 2 * eLpNorm X p μ ^ (1 / 2 : ℝ) := by
    have hc : 0 ≤ 17 * ϰ + 7 * (E₀ * v) := by positivity
    have hmono : eLpNorm (G.indicator fun x => Lam x z) p μ ≤
        eLpNorm ((fun _ => 17 * ϰ + 7 * (E₀ * v)) + (2 : ℝ) • fun x => ‖X x‖ ^ (1 / 2 : ℝ))
          p μ := by
      refine eLpNorm_mono_real (hΛm.indicator hGm) fun x => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (hΛ0 x)]
        exact hstep1 x hx
      · rw [Set.indicator_of_notMem hx, norm_zero]
        positivity
    refine hmono.trans ((eLpNorm_add_le hp1E).trans (add_le_add (le_of_eq ?_) ?_))
    · rw [eLpNorm_const' _ hpne hpt, measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal hc]
    · rw [eLpNorm_const_smul, eLpNorm_norm_rpow _ hXc.aestronglyMeasurable (by norm_num),
        Real.enorm_eq_ofReal (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      refine eLpNorm_le_eLpNorm_of_exponent_le ?_
      calc (p : ℝ≥0∞) * ENNReal.ofReal (1 / 2) ≤ p * 1 := by
            gcongr
            exact ENNReal.ofReal_le_one.2 (by norm_num)
        _ = p := mul_one _
  -- (7.b)
  have hΛn : eLpNorm (fun x => Lam x z) p μ ≤
      eLpNorm (G.indicator fun x => Lam x z) p μ + ENNReal.ofReal ((N : ℝ) ^ (-8 : ℝ)) := by
    calc eLpNorm (fun x => Lam x z) p μ =
          eLpNorm (G.indicator (fun x => Lam x z) + Gᶜ.indicator (fun x => Lam x z)) p μ := by
          rw [Set.indicator_self_add_compl]
      _ ≤ eLpNorm (G.indicator fun x => Lam x z) p μ +
          eLpNorm (Gᶜ.indicator fun x => Lam x z) p μ := eLpNorm_add_le hp1E
      _ ≤ _ := by
          gcongr
          calc eLpNorm (Gᶜ.indicator fun x => Lam x z) p μ ≤
                eLpNorm (Gᶜ.indicator fun _ => (2 * N : ℝ)) p μ := by
                refine eLpNorm_mono (hΛm.indicator hGm.compl) fun x => ?_
                by_cases hx : x ∈ Gᶜ
                · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
                    Real.norm_of_nonneg (hΛ0 x), Real.norm_of_nonneg (by positivity)]
                  exact hΛ2N x
                · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
            _ ≤ ‖(2 * N : ℝ)‖ₑ * μ Gᶜ ^ (1 / (p : ℝ≥0∞).toReal) :=
                eLpNorm_indicator_const_le _ _ hGm.compl.nullMeasurableSet
            _ ≤ _ := by
                rw [Real.enorm_eq_ofReal (by positivity), ENNReal.toReal_natCast]
                exact hT6
  -- the bound on `‖Φ_*²‖_p`
  have hΦn : eLpNorm (fun x => phiStarSq (p : ℝ) x z) p μ ≤
      ENNReal.ofReal (151 * ϰ * v + p * v ^ 2) +
        ENNReal.ofReal v * eLpNorm (fun x => Lam x z) p μ := by
    have hmono : eLpNorm (fun x => phiStarSq (p : ℝ) x z) p μ ≤
        eLpNorm ((fun _ => 151 * ϰ * v + p * v ^ 2) + v • fun x => Lam x z) p μ := by
      refine eLpNorm_mono_real hΦc.aestronglyMeasurable fun x => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have ht : |(stieltjesEmp (toMatrix x) z).im| ≤ (msc z).im + Lam x z := by
        have h := Complex.abs_im_le_norm (stieltjesEmp (toMatrix x) z - msc z)
        rw [Complex.sub_im] at h
        have h' := abs_sub_abs_le_abs_sub (stieltjesEmp (toMatrix x) z).im (msc z).im
        rw [abs_of_nonneg hmsc0] at h'
        unfold Lam
        linarith only [h, h']
      rw [Real.norm_eq_abs]
      exact firstPass_phi hNpos hη0 (Nat.cast_nonneg p) hmlo hmhi ht
    refine hmono.trans ((eLpNorm_add_le hp1E).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_)))
    · rw [eLpNorm_const' _ hpne hpt, measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal (by positivity)]
    · rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hv0.le]
  -- passage to real numbers
  have hYfin : eLpNorm (G.indicator fun x => Lam x z) p μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * N))
      ((eLpNorm_le_of_ae_bound (C := 2 * N) (hΛm.indicator hGm) (ae_of_all _ fun x => ?_)).trans
        (by simp [measure_univ]))
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (hΛ0 x)]
      exact hΛ2N x
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  obtain ⟨y, hy0, hYy⟩ : ∃ y : ℝ, 0 ≤ y ∧
      eLpNorm (G.indicator fun x => Lam x z) p μ = ENNReal.ofReal y :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hYfin).symm⟩
  rw [hYy, ← ENNReal.ofReal_add hy0 (by positivity)] at hΛn
  obtain ⟨ℓ, hℓ0, hℓ⟩ : ∃ ℓ : ℝ, 0 ≤ ℓ ∧ eLpNorm (fun x => Lam x z) p μ = ENNReal.ofReal ℓ :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (ne_top_of_le_ne_top
      ENNReal.ofReal_ne_top hΛn)).symm⟩
  rw [hℓ, ← ENNReal.ofReal_mul hv0.le, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hΦn
  obtain ⟨φ, hφ0, hφ⟩ : ∃ φ : ℝ, 0 ≤ φ ∧
      eLpNorm (fun x => phiStarSq (p : ℝ) x z) p μ = ENNReal.ofReal φ :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (ne_top_of_le_ne_top
      ENNReal.ofReal_ne_top hΦn)).symm⟩
  have hF0 : 0 ≤ F := by linarith only [hF1]
  rw [hφ, ← ENNReal.ofReal_mul hF0, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hFA
  obtain ⟨ξ, hξ0, hξ⟩ : ∃ ξ : ℝ, 0 ≤ ξ ∧ eLpNorm X p μ = ENNReal.ofReal ξ :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal (ne_top_of_le_ne_top
      ENNReal.ofReal_ne_top hFA)).symm⟩
  rw [hξ, ENNReal.ofReal_rpow_of_nonneg hξ0 (by norm_num), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by
    simp, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
    hYy, ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.sqrt_eq_rpow] at hYi
  rw [hℓ, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hΛn
  rw [hφ, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hΦn
  rw [hξ, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hFA
  rw [hn8q] at hΛn hFA
  -- Step 3 and (7.2)
  obtain ⟨hY42, hX194⟩ := firstPass_algebra hξ0 hϰ0 hv0 hF1 hFv hE0F hE01 (Nat.cast_nonneg p)
    hp4F hpE hEF hK0 hq0 hqϰ hq2 hYi hΛn hΦn hFA
  have hEv : E / u = E * v := by rw [hv_def]; ring
  have hFu' : 194 * F / u = 194 * F * v := by rw [hv_def]; ring
  refine ⟨?_, ?_, ?_, Set.inter_subset_left, ?_⟩
  · rw [hYy, hEv]
    refine ENNReal.ofReal_le_ofReal (hY42.trans ?_)
    have : 0 ≤ E * v := by positivity
    linarith only [this, hϰ0]
  · rw [hξ, hEv, hFu']
    exact ENNReal.ofReal_le_ofReal hX194
  · exact hGc.inter (isClosed_le hXc.norm continuous_const)
  -- Step 4: Markov's inequality
  set t : ℝ := K * E / u * (ϰ + E / u) with ht_def
  have ht0 : 0 < t := by
    have : 0 < E := by positivity
    positivity
  have hsub : G \ strongG1 M ϑ⁻¹ C₀ K z ⊆ {x | ENNReal.ofReal t ≤ ‖X x‖ₑ} := by
    intro x hx
    have hlt : t < ‖X x‖ := by
      by_contra hle
      exact hx.2 ⟨hx.1, not_lt.1 hle⟩
    change ENNReal.ofReal t ≤ ‖X x‖ₑ
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hlt.le
  have hMk := mul_meas_ge_le_pow_eLpNorm' μ hpne hpt (f := X) (ENNReal.ofReal t)
  rw [ENNReal.toReal_natCast, ENNReal.rpow_natCast, ENNReal.rpow_natCast, hξ] at hMk
  set ρ : ℝ := 194 / K ^ 2 with hρ_def
  have hρ0 : 0 ≤ ρ := by positivity
  have hξρ : ξ ≤ ρ * t := by
    have e : ρ * t = 194 * F * v * (ϰ + E * v) := by
      rw [hρ_def, ht_def, hEv, hEF, hv_def]
      field_simp
    rw [e]
    exact hX194
  have hρe : ρ ≤ Real.exp (-1) := by
    rw [hρ_def, Real.exp_neg, div_le_iff₀ (by positivity), inv_mul_eq_div,
      le_div_iff₀ (Real.exp_pos 1)]
    have he := Real.exp_one_lt_d9
    nlinarith only [he, hK0]
  have htne : ENNReal.ofReal t ^ p ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 ht0).ne'
  have httop : ENNReal.ofReal t ^ p ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc μ (G \ strongG1 M ϑ⁻¹ C₀ K z) ≤ μ {x | ENNReal.ofReal t ≤ ‖X x‖ₑ} := measure_mono hsub
    _ ≤ ENNReal.ofReal ρ ^ p := by
        rw [← ENNReal.mul_le_mul_iff_right htne httop]
        refine hMk.trans ?_
        rw [← mul_pow, ← ENNReal.ofReal_mul ht0.le]
        gcongr
        linarith only [hξρ]
    _ ≤ ENNReal.ofReal (Real.exp (-1)) ^ p := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(p : ℝ))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        congr 2
        ring

end Rigidity
