import Rigidity.Strong.FirstPass

/-!
# The strong local law on the lattice (NP v1.1, §7.2: Proposition 7.2)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `𝒢²(z) = ⋂_{z' ∈ col(z)} 𝒢¹(z')` of Proposition 7.2. -/
def strongG2 {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  ⋂ w ∈ latticeCol a C₀ K N z, strongG1 M a C₀ K w

/-! The proof follows NP v1.1, §7.2. Write `u = Nη`, `𝔈 = K^b`, `β = ϰ + 𝔈/u`, `w = m - m_sc`,
`w₀ = m_sc (1 - m_sc²)`, and let `𝔈₀` be the quantity of Lemma 5.1.

* On `𝒢¹(z')`, (5.4) of Lemma 5.1 and the definition of `𝒢¹(z')` give the quadratic inequality
  `|w² - w₀w| ≤ 2K𝔈β/u + (𝔈₀/u)Λ + ¾Λ²` of the proof of Proposition 7.2.
* (a): the dichotomy (7.d) at the type-(a) points of the column, and the continuity argument along
  the column. It starts from Lemma 5.3 at `Im z' = 10`. The step uses the Lipschitz bound of
  Lemma 3.5 (c) for `Λ`, together with `ϰ(E + i(η + N⁻⁴)) ≤ ϰ(E + iη) + N⁻²` and
  `Λ ≤ K^{b+2}/u ≤ ϰ/7800` at the previous point.
* (b): from (a) at type-(a) points, and from the scalar inequality of Lemma 3.11 otherwise.
* (c): (5.3) and (5.5) in the explicit form of Lemma 5.1, together with (b) and
  `144 C_s λ_st = 1/4`.
* The probability bound: the union bound over the column, with Definition 5.1 and
  Proposition 7.1.

Where the original paper (Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as
[EYY, …]. -/

/-! ### 1. Real-variable steps -/

/-- The real statement of Lemma 3.11: `x² ≤ βx + r²` with `β, r ≥ 0` gives `x ≤ β + r`. -/
private lemma lattice_scalar {x β r : ℝ} (hβ : 0 ≤ β) (hr : 0 ≤ r)
    (h : x ^ 2 ≤ β * x + r ^ 2) : x ≤ β + r := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  nlinarith [mul_le_mul_of_nonneg_left hlt.le hr]

/-- `|w|² ≤ |w₀||w| + |w² - w₀w|`, and `|w| ≤ |w₀|/2` gives `|w₀||w|/2 ≤ |w² - w₀w|`. -/
private lemma lattice_norm_facts (w w₀ : ℂ) :
    ‖w‖ ^ 2 ≤ ‖w₀‖ * ‖w‖ + ‖w ^ 2 - w₀ * w‖ ∧
      (‖w‖ ≤ ‖w₀‖ / 2 → ‖w₀‖ / 2 * ‖w‖ ≤ ‖w ^ 2 - w₀ * w‖) := by
  refine ⟨?_, fun h => ?_⟩
  · calc ‖w‖ ^ 2 = ‖w₀ * w + (w ^ 2 - w₀ * w)‖ := by rw [← norm_pow]; ring_nf
      _ ≤ ‖w₀ * w‖ + ‖w ^ 2 - w₀ * w‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul]
  · have he : w ^ 2 - w₀ * w = w * (w - w₀) := by ring
    have h1 : ‖w₀‖ - ‖w‖ ≤ ‖w - w₀‖ := by
      have := norm_sub_norm_le w₀ w
      rw [norm_sub_rev] at this
      linarith
    rw [he, norm_mul]
    nlinarith [mul_nonneg (norm_nonneg w) (by linarith : 0 ≤ ‖w - w₀‖ - ‖w₀‖ / 2)]

/-- The quadratic inequality of the proof of Proposition 7.2: (5.4) with
`|⟨X⟩| ≤ K𝔈β/u`, `0 ≤ Im m_sc ≤ ϰ`, `𝔈₀ ≤ K𝔈` and `𝔈 ≥ 1`. -/
private lemma lattice_Q1 {q X E₀ I Λ u K E ϰ : ℝ} (hu : 0 < u) (hI0 : 0 ≤ I) (hI : I ≤ ϰ)
    (hE₀ : 0 ≤ E₀) (hE₀K : E₀ ≤ K * E) (hE : 1 ≤ E)
    (hq : q ≤ X + E₀ * ((I + Λ) / u + 1 / u ^ 2) + 3 / 4 * Λ ^ 2)
    (hX : X ≤ K * E / u * (ϰ + E / u)) :
    q ≤ 2 * (K * E / u * (ϰ + E / u)) + E₀ / u * Λ + 3 / 4 * Λ ^ 2 := by
  have he : E₀ * ((I + Λ) / u + 1 / u ^ 2) = E₀ / u * (I + 1 / u) + E₀ / u * Λ := by
    field_simp
    ring
  have h1 : 1 / u ≤ E / u := div_le_div_of_nonneg_right hE hu.le
  have h2 : E₀ / u * (I + 1 / u) ≤ E₀ / u * (ϰ + E / u) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : E₀ / u * (ϰ + E / u) ≤ K * E / u * (ϰ + E / u) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE₀K hu.le)
      (by have := hI0.trans hI; positivity)
  rw [he] at hq
  linarith

/-- The dichotomy (7.d): at a type-(a) point (`ϰu ≥ 𝔈K³`), the quadratic inequality and
`Λ ≤ |w₀|/2` give `Λ ≤ 𝔈K²/u ≤ ϰ/7800`. -/
private lemma lattice_dich {Λ W Q K E E₀ ϰ u : ℝ} (hΛ : 0 ≤ Λ) (hu : 0 < u) (hϰ : 0 < ϰ)
    (hK : 124800 ≤ K) (hE : 0 ≤ E) (hE₀ : 0 ≤ E₀) (hE₀E : E₀ * K ^ 4 ≤ E)
    (hW : ϰ / 1950 ≤ W) (ha : E * K ^ 3 ≤ ϰ * u)
    (hQ : Q ≤ 2 * (K * E / u * (ϰ + E / u)) + E₀ / u * Λ + 3 / 4 * Λ ^ 2)
    (hlow : W / 2 * Λ ≤ Q) (hΛW : Λ ≤ W / 2) :
    Λ ≤ E * K ^ 2 / u ∧ E * K ^ 2 / u ≤ ϰ / 7800 := by
  have hK1 : 1 ≤ K := by linarith
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK1
  have hK4 : K ≤ K ^ 4 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
  have hEu : E ≤ ϰ * u := le_trans (le_mul_of_one_le_right hE hK3) ha
  have hEu' : E / u ≤ ϰ := by rw [div_le_iff₀ hu]; linarith
  have hE₀u : E₀ * 31200 ≤ ϰ * u := by
    have : E₀ * 31200 ≤ E₀ * K ^ 4 := mul_le_mul_of_nonneg_left (by linarith) hE₀
    linarith
  have hϰW : ϰ * u ≤ 1950 * W * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  have hE₀W : E₀ / u ≤ W / 16 := by
    rw [div_le_iff₀ hu]
    linarith
  have hKE0 : 0 ≤ K * E / u := by positivity
  have hb1 : K * E / u * (ϰ + E / u) ≤ K * E / u * (2 * ϰ) :=
    mul_le_mul_of_nonneg_left (by linarith) hKE0
  have hb2 : E₀ / u * Λ ≤ W / 16 * Λ := mul_le_mul_of_nonneg_right hE₀W hΛ
  have hb3 : Λ ^ 2 ≤ W / 2 * Λ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hΛW hΛ
  have hmain : W * Λ ≤ 64 * (K * E / u * ϰ) := by nlinarith
  have hϰΛ : ϰ / 1950 * Λ ≤ W * Λ := mul_le_mul_of_nonneg_right hW hΛ
  have hΛ1 : ϰ * Λ ≤ ϰ * (124800 * K * E / u) := by
    have e : ϰ * (124800 * K * E / u) = 124800 * (K * E / u * ϰ) := by ring
    rw [e]
    have e2 : ϰ * Λ = 1950 * (ϰ / 1950 * Λ) := by ring
    rw [e2]
    linarith
  have hΛ2 : Λ ≤ 124800 * K * E / u := le_of_mul_le_mul_left hΛ1 hϰ
  refine ⟨hΛ2.trans (div_le_div_of_nonneg_right ?_ hu.le), ?_⟩
  · have : 124800 * K * E ≤ K * K * E := by
      have := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ K * E)
      linarith
    nlinarith
  · rw [div_le_div_iff₀ hu (by norm_num)]
    have e : E * K ^ 3 = E * K ^ 2 * K := by ring
    have : E * K ^ 2 * 7800 ≤ E * K ^ 2 * K :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-- Proposition 7.2 (b) at a point which is not of type (a) (`ϰu < 𝔈K³`): the quadratic
inequality and the scalar inequality give `Λ ≤ 𝔈K⁴/u`. -/
private lemma lattice_partb {Λ W Q K E E₀ ϰ u : ℝ} (hu : 0 < u) (hK : 24 ≤ K) (hE : 0 ≤ E)
    (hE₀ : 0 ≤ E₀) (hE₀E : E₀ * K ^ 4 ≤ E) (hW0 : 0 ≤ W)
    (hW : W ≤ 4 * ϰ) (hna : ϰ * u < E * K ^ 3)
    (hQ : Q ≤ 2 * (K * E / u * (ϰ + E / u)) + E₀ / u * Λ + 3 / 4 * Λ ^ 2)
    (hsq : Λ ^ 2 ≤ W * Λ + Q) : Λ ≤ E * K ^ 4 / u := by
  have hK1 : 1 ≤ K := by linarith
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK1
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
  set A := E * K ^ 3 / u with hA
  have hϰA : ϰ ≤ A := by rw [hA, le_div_iff₀ hu]; linarith
  have hEA : E / u ≤ A := div_le_div_of_nonneg_right (le_mul_of_one_le_right hE hK3) hu.le
  have hE₀E' : E₀ ≤ E := le_trans (le_mul_of_one_le_right hE₀ hK4) hE₀E
  have hβ : K * E / u * (ϰ + E / u) ≤ K * E / u * (2 * A) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hr : K * E / u * (2 * A) * 8 = (4 * (E * K ^ 2 / u)) ^ 2 := by
    rw [hA]
    field_simp
    ring
  have hE₀u : 0 ≤ E₀ / u := by positivity
  have hkey : Λ ^ 2 ≤ (4 * (W + E₀ / u)) * Λ + (4 * (E * K ^ 2 / u)) ^ 2 := by
    nlinarith
  have hs := lattice_scalar (by positivity) (by positivity) hkey
  have h1 : E₀ / u ≤ A := div_le_div_of_nonneg_right
    (le_trans hE₀E' (le_mul_of_one_le_right hE hK3)) hu.le
  have h2 : E * K ^ 2 / u ≤ A := by
    rw [hA]
    refine div_le_div_of_nonneg_right ?_ hu.le
    have : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this hE
  have h3 : 24 * A ≤ E * K ^ 4 / u := by
    rw [hA, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hu.le
    have e : E * K ^ 4 = E * K ^ 3 * K := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ E * K ^ 3)
    linarith
  linarith

/-- Proposition 7.2 (c) in real numbers: from (5.3) and (5.5) in the explicit form of Lemma 5.1,
`Λ ≤ λ_st = 1/(576 C_s)`, (b), `2142 C_s 𝔏 ≤ P` and `P K² ≤ 𝔈^{1/2}`, one has
`Λ_d + Λ_o ≤ 𝔈K⁵ (√(Im m_sc/u) + 1/u)`. -/
private lemma lattice_partc {Λ Ld Lo D L Cs I u K E P : ℝ} (hΛ : 0 ≤ Λ) (hu : 0 < u)
    (hI : 0 ≤ I) (hCs : 1 ≤ Cs) (hL : 0 ≤ L) (hK : 3 ≤ K) (hE : 1 ≤ E)
    (hLo : Lo ≤ 35 * L * (√((I + Λ) / u) + 1 / u))
    (hD : D ≤ 1036 * Cs * L * (√((I + Λ) / u) + 1 / u) + 144 * Cs * Λ ^ 2)
    (hLd : Ld ≤ Λ + D) (hst : Λ ≤ 1 / (576 * Cs)) (hb : Λ ≤ E * K ^ 4 / u)
    (hP : 2142 * Cs * L ≤ P) (hPE : P * K ^ 2 ≤ √E) :
    Ld + Lo ≤ E * K ^ 5 * (√(I / u) + 1 / u) := by
  have hK1 : 1 ≤ K := by linarith
  have hCs0 : 0 < Cs := by linarith
  set Ψ := √((I + Λ) / u) + 1 / u with hΨ
  have hΨ0 : 0 ≤ Ψ := by positivity
  have h144 : 144 * Cs * Λ ^ 2 ≤ Λ / 4 := by
    have h := mul_le_mul_of_nonneg_left hst (by positivity : 0 ≤ 144 * Cs * Λ)
    have e : 144 * Cs * Λ * (1 / (576 * Cs)) = Λ / 4 := by field_simp; ring
    rw [e] at h
    nlinarith
  have hLΨ : 0 ≤ L * Ψ := mul_nonneg hL hΨ0
  have hsum : Ld + Lo ≤ 5 / 4 * Λ + 1071 * Cs * L * Ψ := by
    have : 35 * L * Ψ ≤ 35 * Cs * L * Ψ := by nlinarith
    nlinarith
  have hsE : 0 ≤ √E := Real.sqrt_nonneg E
  have hsE2 : √E ^ 2 = E := Real.sq_sqrt (by linarith)
  have hsq : √((I + Λ) / u) ≤ √(I / u) + √E * K ^ 2 / u := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h1 : Λ / u ≤ (√E * K ^ 2 / u) ^ 2 := by
      have e : (√E * K ^ 2 / u) ^ 2 = E * K ^ 4 / u / u := by
        rw [div_pow, mul_pow, hsE2]
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right hb hu.le
    have h2 : √(I / u) ^ 2 = I / u := Real.sq_sqrt (by positivity)
    have h3 : 0 ≤ √(I / u) * (√E * K ^ 2 / u) := by positivity
    have e : (I + Λ) / u = I / u + Λ / u := by ring
    rw [e]
    nlinarith
  have hP0 : 0 ≤ P := le_trans (by positivity) hP
  have hPs : P ≤ √E := le_trans (le_mul_of_one_le_right hP0 (one_le_pow₀ hK1)) hPE
  have hsEE : √E ≤ E := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hPE' : P * K ^ 2 * √E ≤ E := by
    have := mul_le_mul_of_nonneg_right hPE hsE
    nlinarith
  have hK5 : 1 ≤ K ^ 5 := one_le_pow₀ hK1
  have hEK5 : P / 2 ≤ E * K ^ 5 := by
    have := le_mul_of_one_le_right (by linarith : 0 ≤ E) hK5
    linarith
  have hsI : 0 ≤ √(I / u) := Real.sqrt_nonneg _
  have hv : 0 < 1 / u := by positivity
  have hc1 : 1071 * Cs * L * Ψ ≤ P / 2 * Ψ :=
    mul_le_mul_of_nonneg_right (by linarith) hΨ0
  have hc2 : P / 2 * Ψ ≤ P / 2 * (√(I / u) + √E * K ^ 2 / u + 1 / u) :=
    mul_le_mul_of_nonneg_left (by rw [hΨ]; linarith) (by linarith)
  have hc3 : P / 2 * (√(I / u) + √E * K ^ 2 / u + 1 / u) ≤
      E * K ^ 5 * √(I / u) + E / u := by
    have e : P / 2 * (√(I / u) + √E * K ^ 2 / u + 1 / u) =
        P / 2 * √(I / u) + (P * K ^ 2 * √E / 2 + P / 2) * (1 / u) := by ring
    rw [e]
    have h1 : P / 2 * √(I / u) ≤ E * K ^ 5 * √(I / u) := mul_le_mul_of_nonneg_right hEK5 hsI
    have h2 : (P * K ^ 2 * √E / 2 + P / 2) * (1 / u) ≤ E * (1 / u) :=
      mul_le_mul_of_nonneg_right (by linarith) hv.le
    have e2 : E / u = E * (1 / u) := by ring
    rw [e2]
    linarith
  have hc4 : 5 / 4 * Λ ≤ 5 / 4 * E * K ^ 4 * (1 / u) := by
    have e : 5 / 4 * E * K ^ 4 * (1 / u) = 5 / 4 * (E * K ^ 4 / u) := by ring
    rw [e]
    linarith
  have hc5 : 5 / 4 * E * K ^ 4 * (1 / u) + E * (1 / u) ≤ E * K ^ 5 * (1 / u) := by
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hv.le
    have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
    have e : E * K ^ 5 = E * K ^ 4 * K := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ E * K ^ 4)
    have := le_mul_of_one_le_right (by linarith : 0 ≤ E) hK4
    linarith
  have e3 : E / u = E * (1 / u) := by ring
  rw [e3] at hc3
  have e4 : E * K ^ 5 * (√(I / u) + 1 / u) = E * K ^ 5 * √(I / u) + E * K ^ 5 * (1 / u) := by
    ring
  rw [e4]
  linarith

/-- `Λ ≤ Λ_d`: the modulus of an average is at most the largest modulus of its terms. -/
private lemma lattice_lam_le_lamD {N : ℕ} (hN : 0 < N) (x : Pair N → 𝕜) (z : ℂ) :
    Lam x z ≤ LamD x z := by
  have hb : ∀ i : Fin N, ‖green (toMatrix x) z i i - msc z‖ ≤ LamD x z := fun i =>
    le_ciSup (f := fun k : Fin N => ‖green (toMatrix x) z k k - msc z‖)
      (Finite.bddAbove_range _) i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : stieltjesEmp (toMatrix x) z - msc z =
      (N : ℂ)⁻¹ * ∑ i, (green (toMatrix x) z i i - msc z) := by
    unfold stieltjesEmp
    rw [Fintype.card_fin, Matrix.trace, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ hNc, one_mul]
    rfl
  unfold Lam
  rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, (green (toMatrix x) z i i - msc z)‖
      ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, LamD x z := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb i)
    _ = LamD x z := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hNpos.ne', one_mul]

/-! ### 2. Proposition 7.2 -/

/-- Proposition 7.2: `𝒢²(z)` is closed, `ℙ(𝒢²(z)ᶜ) ≤ N^{10} e^{-p₁}`, and on `𝒢²(z)` the bounds
(a) (at points with `ϰ N η ≥ 𝔈₃ = K^{b+3}`), (b), (c) hold. -/
theorem strong_lattice {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ lattice ϑ⁻¹ C₀ K N ∩ Dnear ϑ⁻¹ K N,
        IsClosed (strongG2 M ϑ⁻¹ C₀ K z) ∧
        M.prodLaw (strongG2 M ϑ⁻¹ C₀ K z)ᶜ ≤
          ENNReal.ofReal ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ))) ∧
        ∀ x ∈ strongG2 M ϑ⁻¹ C₀ K z,
          (K ^ (ledgerB ϑ⁻¹ + 3) ≤ varkappa z * (N * z.im) →
            Lam x z ≤ K ^ (ledgerB ϑ⁻¹ + 2) / (N * z.im) ∧
            K ^ (ledgerB ϑ⁻¹ + 2) / (N * z.im) ≤ ‖msc z * (1 - msc z ^ 2)‖ / 4) ∧
          Lam x z ≤ K ^ (ledgerB ϑ⁻¹ + 4) / (N * z.im) ∧
          LamD x z + LamO x z ≤
            K ^ (ledgerB ϑ⁻¹ + 5) * (Real.sqrt ((msc z).im / (N * z.im)) + 1 / (N * z.im)) := by
  obtain ⟨N₁, h1⟩ := strong_firstPass (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := apriori_bounds (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨Cw, -, N₃, h3⟩ := weakLaw_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₄, h4⟩ := initial_estimate (𝕜 := 𝕜) (δm := δm) (δp := δp) hϑ hϑ1 hC₀
  obtain ⟨N₅, h5⟩ := lattice_card (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₆, h6⟩ := standing_ineq hϑ hϑ1 hC₀ (250000 * stabCs C₀ δm δp)
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) ⌈460 / ϑ + 10⌉₊), ?_⟩
  intro N hN M hM K hK1 hK2 z hz
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  have hN5 : N₅ ≤ N := by omega
  have hN6 : N₆ ≤ N := by omega
  have hN7 : ⌈460 / ϑ + 10⌉₊ ≤ N := by omega
  have ha : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨⟨hK0, h13, -, -⟩, ⟨hFL0, hFL, -, -⟩, ⟨hp1K, -, -, -, -⟩, ⟨hS4, hS4'⟩⟩ :=
    h6 N hN6 K hK1 hK2
  set Cs := stabCs C₀ δm δp with hCs_def
  have hCs : 1 ≤ Cs := by
    rw [hCs_def]
    unfold stabCs
    have : 0 ≤ Real.sqrt C₀ / min δm δp :=
      div_nonneg (Real.sqrt_nonneg _) (le_min hδm.le hδp.le)
    linarith
  have hK : 250000 ≤ K := by linarith
  have hKCs : 2142 * Cs ≤ K := by linarith
  have hK1' : (1 : ℝ) ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hNr : (13 : ℝ) ≤ N := by exact_mod_cast h13
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1r : (1 : ℝ) ≤ N := by linarith
  have hNnat : 0 < N := by omega
  -- the exponents
  set E : ℝ := K ^ ledgerB ϑ⁻¹ with hE_def
  have hb0 : 0 ≤ ledgerB ϑ⁻¹ := by unfold ledgerB; linarith
  have hE1 : 1 ≤ E := Real.one_le_rpow hK1' hb0
  have hE0 : 0 ≤ E := by linarith
  have hbn : ∀ n : ℕ, 2 ≤ n → K ^ (ledgerB ϑ⁻¹ + (n : ℝ)) = E * K ^ n := fun n _ => by
    rw [Real.rpow_add hKpos, Real.rpow_natCast]
  have hb2 : K ^ (ledgerB ϑ⁻¹ + 2) = E * K ^ 2 := by exact_mod_cast hbn 2 le_rfl
  have hb3 : K ^ (ledgerB ϑ⁻¹ + 3) = E * K ^ 3 := by exact_mod_cast hbn 3 (by norm_num)
  have hb4 : K ^ (ledgerB ϑ⁻¹ + 4) = E * K ^ 4 := by exact_mod_cast hbn 4 (by norm_num)
  have hb5 : K ^ (ledgerB ϑ⁻¹ + 5) = E * K ^ 5 := by exact_mod_cast hbn 5 (by norm_num)
  rw [hb2, hb3, hb4, hb5]
  obtain ⟨hE01, hE0K, hAP⟩ := h2 N hN2 M hM K hK1 hK2
  set E₀ := aprioriE0 ϑ⁻¹ C₀ δm δp K N with hE₀_def
  have hE₀0 : 0 ≤ E₀ := by linarith
  have hE₀E : E₀ * K ^ 4 ≤ E := by
    calc E₀ * K ^ 4 ≤ K ^ (8 * ϑ⁻¹ + 7) * K ^ ((4 : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]
          exact mul_le_mul_of_nonneg_right hE0K (by positivity)
      _ = K ^ (8 * ϑ⁻¹ + 7 + ((4 : ℕ) : ℝ)) := (Real.rpow_add hKpos _ _).symm
      _ ≤ E := by
          rw [hE_def]
          exact Real.rpow_le_rpow_of_exponent_le hK1' (by unfold ledgerB; push_cast; linarith)
  have hE₀KE : E₀ ≤ K * E := by
    have h4 : 1 ≤ K ^ 4 := one_le_pow₀ hK1'
    have := le_mul_of_one_le_right hE₀0 h4
    have := le_mul_of_one_le_left hE0 hK1'
    linarith
  set FL := levelFL ϑ⁻¹ C₀ K N with hFL_def
  set P : ℝ := K ^ (4 * ϑ⁻¹ + 4) with hP_def
  have hP : 2142 * Cs * FL ≤ P := by
    have e : P = K ^ (4 * ϑ⁻¹ + 3) * K := by
      rw [hP_def, show 4 * ϑ⁻¹ + 4 = 4 * ϑ⁻¹ + 3 + 1 by ring, Real.rpow_add hKpos,
        Real.rpow_one]
    rw [e]
    have := mul_le_mul_of_nonneg_right hKCs (by linarith : 0 ≤ FL)
    have := mul_le_mul_of_nonneg_right hFL hKpos.le
    linarith
  have hPE : P * K ^ 2 ≤ √E := by
    refine (Real.le_sqrt (by positivity) hE0).2 ?_
    have e : (P * K ^ 2) ^ 2 = K ^ (4 * ϑ⁻¹ + 4 + (4 * ϑ⁻¹ + 4) + ((4 : ℕ) : ℝ)) := by
      rw [Real.rpow_add hKpos, Real.rpow_add hKpos, Real.rpow_natCast, hP_def]
      ring
    rw [e, hE_def]
    exact Real.rpow_le_rpow_of_exponent_le hK1' (by unfold ledgerB; push_cast; linarith)
  -- sizes of `N`
  have hN32 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 32 : ℝ) := Real.one_le_rpow hN1r (by norm_num)
  have hN8 : (N : ℝ) ^ (1 / 8 : ℝ) ≤ √N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have hsqN : √(N : ℝ) ≤ N := by
    exact Real.sqrt_le_iff.2 ⟨hNpos.le, le_self_pow₀ hN1r (by norm_num)⟩
  have hNK : (250000 : ℝ) ≤ N := by
    have : 250000 * Cs * 1 ≤ 250000 * Cs * (N : ℝ) ^ (1 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_left hN32 (by positivity)
    linarith
  have hFLN : FL * 250000 ≤ √N := by
    have h1 : FL ≤ (N : ℝ) ^ (1 / 32 : ℝ) := by
      refine hFL.trans (le_trans ?_ hS4)
      exact Real.rpow_le_rpow_of_exponent_le hK1' (by linarith)
    have h2 : FL * (250000 * Cs) ≤ (N : ℝ) ^ (1 / 32 : ℝ) * (250000 * Cs) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : FL * 250000 ≤ FL * (250000 * Cs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- the column of `z`
  obtain ⟨-, m, k, hzk⟩ := id hz.1
  have hk : z.im = 10 - k / (N : ℝ) ^ 4 := by rw [hzk]
  obtain ⟨hcol, -, -, hk1, hnear, -⟩ := latticeCol_eq hNnat hz.1 hk
  set zj : ℕ → ℂ := fun j => ⟨z.re, 10 - j / (N : ℝ) ^ 4⟩ with hzj_def
  have hzj_mem : ∀ j, j ≤ k → zj j ∈ latticeCol ϑ⁻¹ C₀ K N z := fun j hj => by
    rw [hcol]
    exact ⟨j, hj, rfl⟩
  have hzjk : zj k = z := Complex.ext rfl hk.symm
  have hcolD : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z, w ∈ lattice ϑ⁻¹ C₀ K N ∩ Dnear ϑ⁻¹ K N :=
    fun w hw => ⟨hw.1, hnear hz.2 hw⟩
  have hcolsub : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z,
      latticeCol ϑ⁻¹ C₀ K N w ⊆ latticeCol ϑ⁻¹ C₀ K N z := fun w hw v hv =>
    ⟨hv.1, hv.2.1.trans hw.2.1, hw.2.2.trans hv.2.2⟩
  have hT4 := fun (w : ℂ) (hw : w ∈ Dnear ϑ⁻¹ K N) (x : Pair N → 𝕜) =>
    strong_T4 ha hK1' (by omega : 1 ≤ N) hw x
  have hη0 : 0 < z.im := lt_of_lt_of_le (by positivity) (hT4 z hz.2 0).1
  -- the pointwise inputs at a point `w` of the column
  have hpt : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z, ∀ x ∈ strongG1 M ϑ⁻¹ C₀ K w,
      x ∈ goodEvent M ϑ⁻¹ (K ^ 2) w ∧ LamD x w + LamO x w ≤ lamSt C₀ δm δp / 2 ∧
      ‖(stieltjesEmp (toMatrix x) w - msc w) ^ 2 -
          msc w * (1 - msc w ^ 2) * (stieltjesEmp (toMatrix x) w - msc w)‖ ≤
        2 * (K * E / (N * w.im) * (varkappa w + E / (N * w.im))) +
          E₀ / (N * w.im) * Lam x w + 3 / 4 * Lam x w ^ 2 := by
    intro w hw x hx
    have hwD := hcolD w hw
    have hxG : x ∈ goodCol M ϑ⁻¹ C₀ K w :=
      (h1 N hN1 M hM K hK1 hK2 w hwD).2.2.2.1 hx
    have hxE : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) w :=
      Set.mem_iInter₂.1 hxG w ⟨hwD.1, rfl, le_rfl⟩
    obtain ⟨hle, hle'⟩ := ((h3 N hN3 M hM K hK1 hK2 w hwD.1).1 x hxG).1 hwD.2
    have hst : 0 < lamSt C₀ δm δp := by unfold lamSt stabCs; positivity
    obtain ⟨-, -, -, -, -, -, -, hq, -, -, -, -, -⟩ :=
      hAP w hwD.2 x hxE (by linarith only [hle, hle', hst])
    obtain ⟨hη1, -, -, hmlo, hmhi, -, -, -⟩ := hT4 w hwD.2 x
    have hηw : 0 < w.im := lt_of_lt_of_le (by positivity) hη1
    refine ⟨hxE, hle.trans hle', ?_⟩
    exact lattice_Q1 (by positivity) (le_trans (by positivity) hmlo) hmhi hE₀0 hE₀KE hE1 hq hx.2
  -- closedness
  have hclosed : IsClosed (strongG2 M ϑ⁻¹ C₀ K z) :=
    isClosed_biInter fun w hw => (h1 N hN1 M hM K hK1 hK2 w (hcolD w hw)).2.2.1
  -- the probability bound
  have hcover : (strongG2 M ϑ⁻¹ C₀ K z)ᶜ ⊆ (goodCol M ϑ⁻¹ C₀ K z)ᶜ ∪
      ⋃ j ∈ Finset.range (k + 1), goodCol M ϑ⁻¹ C₀ K (zj j) \ strongG1 M ϑ⁻¹ C₀ K (zj j) := by
    intro x hx
    by_cases hxz : x ∈ goodCol M ϑ⁻¹ C₀ K z
    · right
      simp only [strongG2, Set.mem_compl_iff, Set.mem_iInter, not_forall] at hx
      obtain ⟨w, hw, hxw⟩ := hx
      have hw' := hw
      rw [hcol] at hw'
      obtain ⟨j, hj, rfl⟩ := hw'
      refine Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), ?_, hxw⟩
      exact Set.mem_iInter₂.2 fun v hv => Set.mem_iInter₂.1 hxz v (hcolsub _ hw hv)
    · exact Or.inl hxz
  have hkN : (k : ℝ) + 1 ≤ 10 * (N : ℝ) ^ 4 := by exact_mod_cast hk1 hη0
  have hlogN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hp1K2 : (levelP1 K : ℝ) ≤ K ^ 2 := by
    have h0 : (0 : ℝ) ≤ levelP1 K := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hlogN h0
    linarith
  have hNsq : 460 / ϑ + 10 ≤ (N : ℝ) ^ 2 := by
    have h := Nat.le_ceil (460 / ϑ + 10)
    have h' : ((⌈460 / ϑ + 10⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN7
    have := le_self_pow₀ hN1r (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have hprob : M.prodLaw (strongG2 M ϑ⁻¹ C₀ K z)ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ))) := by
    have hgc := (h5 N hN5 K hK1 hK2).2.2 M hM z hz.1
    have hfp : ∀ j ∈ Finset.range (k + 1),
        M.prodLaw (goodCol M ϑ⁻¹ C₀ K (zj j) \ strongG1 M ϑ⁻¹ C₀ K (zj j)) ≤
          ENNReal.ofReal (Real.exp (-(levelP1 K : ℝ))) := fun j hj =>
      (h1 N hN1 M hM K hK1 hK2 (zj j)
        (hcolD _ (hzj_mem j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))))).2.2.2.2
    have hreal : 460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-K ^ 2) +
        ((k : ℝ) + 1) * Real.exp (-(levelP1 K : ℝ)) ≤
          (N : ℝ) ^ 10 * Real.exp (-(levelP1 K : ℝ)) := by
      have hex : Real.exp (-K ^ 2) ≤ Real.exp (-(levelP1 K : ℝ)) :=
        Real.exp_le_exp.2 (by linarith)
      have hep := Real.exp_pos (-(levelP1 K : ℝ))
      have h1' : 460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-K ^ 2) ≤
          460 / ϑ * (N : ℝ) ^ 8 * Real.exp (-(levelP1 K : ℝ)) :=
        mul_le_mul_of_nonneg_left hex (by positivity)
      have h2' : ((k : ℝ) + 1) * Real.exp (-(levelP1 K : ℝ)) ≤
          10 * (N : ℝ) ^ 4 * Real.exp (-(levelP1 K : ℝ)) :=
        mul_le_mul_of_nonneg_right hkN hep.le
      have h48 : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 8 := pow_le_pow_right₀ hN1r (by norm_num)
      have h3' : 460 / ϑ * (N : ℝ) ^ 8 + 10 * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 10 := by
        have := mul_le_mul_of_nonneg_right hNsq (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 8)
        linarith only [this, h48]
      have h4' := mul_le_mul_of_nonneg_right h3' hep.le
      linarith only [h1', h2', h4']
    calc M.prodLaw (strongG2 M ϑ⁻¹ C₀ K z)ᶜ
        ≤ M.prodLaw (goodCol M ϑ⁻¹ C₀ K z)ᶜ + M.prodLaw (⋃ j ∈ Finset.range (k + 1),
            goodCol M ϑ⁻¹ C₀ K (zj j) \ strongG1 M ϑ⁻¹ C₀ K (zj j)) :=
          (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2)) +
            ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (Real.exp (-(levelP1 K : ℝ))) :=
          add_le_add hgc ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hfp))
      _ = ENNReal.ofReal (460 / ϑ * N ^ 8 * Real.exp (-K ^ 2) +
            ((k : ℝ) + 1) * Real.exp (-(levelP1 K : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := (k : ℝ) + 1) (by positivity),
            show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  refine ⟨hclosed, hprob, fun x hx => ?_⟩
  have hxw : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z, x ∈ strongG1 M ϑ⁻¹ C₀ K w :=
    fun w hw => Set.mem_iInter₂.1 hx w hw
  have hzz : z ∈ latticeCol ϑ⁻¹ C₀ K N z := ⟨hz.1, rfl, le_rfl⟩
  -- the dichotomy (7.d) at a type-(a) point of the column
  have hdich : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z, E * K ^ 3 ≤ varkappa w * (N * w.im) →
      Lam x w ≤ ‖msc w * (1 - msc w ^ 2)‖ / 2 →
        Lam x w ≤ E * K ^ 2 / (N * w.im) ∧ E * K ^ 2 / (N * w.im) ≤ varkappa w / 7800 := by
    intro w hw hta hΛ
    obtain ⟨-, -, hQ⟩ := hpt w hw x (hxw w hw)
    obtain ⟨hη1, -, hvk, -, -, hW, -, -⟩ := hT4 w (hcolD w hw).2 x
    have hηw : 0 < w.im := lt_of_lt_of_le (by positivity) hη1
    obtain ⟨-, hlow⟩ :=
      lattice_norm_facts (stieltjesEmp (toMatrix x) w - msc w) (msc w * (1 - msc w ^ 2))
    exact lattice_dich (norm_nonneg _) (by positivity) (lt_of_lt_of_le (by positivity) hvk)
      (by linarith) hE0 hE₀0 hE₀E hW hta hQ (hlow hΛ) hΛ
  have hsN : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNpos
  have him_j : ∀ j : ℕ, (zj j).im = 10 - j / (N : ℝ) ^ 4 := fun j => rfl
  have hre_j : ∀ j : ℕ, (zj j).re = z.re := fun j => rfl
  -- (a): the continuity argument along the column
  have hpartA : E * K ^ 3 ≤ varkappa z * (N * z.im) →
      Lam x z ≤ E * K ^ 2 / (N * z.im) ∧
        E * K ^ 2 / (N * z.im) ≤ ‖msc z * (1 - msc z ^ 2)‖ / 4 := by
    intro hta
    have hta' : ∀ w ∈ latticeCol ϑ⁻¹ C₀ K N z, E * K ^ 3 ≤ varkappa w * (N * w.im) := by
      intro w hw
      have h1 : varkappa z ≤ varkappa w := by
        unfold varkappa
        rw [hw.2.1]
        exact Real.sqrt_le_sqrt (by linarith [hw.2.2])
      have h2 : (N : ℝ) * z.im ≤ N * w.im := mul_le_mul_of_nonneg_left hw.2.2 hNpos.le
      exact hta.trans (mul_le_mul h1 h2 (by positivity) (Real.sqrt_nonneg _))
    set t : ℝ := 1 / (N : ℝ) ^ 2 with ht_def
    have ht0 : 0 < t := by positivity
    have hNt : (N : ℝ) ^ 2 * t = 1 := by rw [ht_def]; field_simp
    have ht_small : 23401 * t ≤ 1 / N := by
      rw [ht_def, mul_one_div, div_le_div_iff₀ (by positivity) hNpos]
      have := mul_le_mul_of_nonneg_right (by linarith : (23401 : ℝ) ≤ N) hNpos.le
      linarith only [this]
    have hind : ∀ j, j ≤ k → Lam x (zj j) ≤ ‖msc (zj j) * (1 - msc (zj j) ^ 2)‖ / 2 := by
      intro j
      induction j with
      | zero =>
        intro _
        have hw := hzj_mem 0 (Nat.zero_le _)
        have him : (zj 0).im = 10 := by rw [him_j]; simp
        have hxE : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) (zj 0) := (hpt _ hw x (hxw _ hw)).1
        obtain ⟨-, hLDO⟩ := h4 N hN4 M hM K hK1 hK2 (zj 0) him x hxE
        have hLO : 0 ≤ LamO x (zj 0) := Real.iSup_nonneg fun _ => norm_nonneg _
        have hΛD := lattice_lam_le_lamD hNnat x (zj 0)
        obtain ⟨-, -, -, -, -, hW, -, -⟩ := hT4 _ (hcolD _ hw).2 x
        have hϰ3 : 3 ≤ varkappa (zj 0) := by
          unfold varkappa
          rw [him]
          have e : (3 : ℝ) = √(3 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
          rw [e]
          refine Real.sqrt_le_sqrt ?_
          have := abs_nonneg (|(zj 0).re| - 2)
          unfold kappaE
          linarith
        have h4L : 4 * FL / √N ≤ 4 / 250000 := by
          rw [div_le_div_iff₀ hsN (by norm_num)]
          linarith
        linarith
      | succ j ih =>
        intro hj
        have hjk : j ≤ k := by omega
        have hw := hzj_mem j hjk
        have hw1 := hzj_mem (j + 1) hj
        obtain ⟨-, hΛj'⟩ := hdich _ hw (hta' _ hw) (ih hjk)
        have hΛj := (hdich _ hw (hta' _ hw) (ih hjk)).1
        obtain ⟨hη1, -, -, -, -, -, -, -⟩ := hT4 _ (hcolD _ hw).2 x
        obtain ⟨hη1', -, hvk', -, -, hW', -, -⟩ := hT4 _ (hcolD _ hw1).2 x
        -- the Lipschitz bound for `Λ`
        have him_diff : (zj j).im = (zj (j + 1)).im + t ^ 2 := by
          rw [him_j, him_j, ht_def]
          push_cast
          field_simp
          ring
        have hdiff : ‖zj j - zj (j + 1)‖ ≤ t ^ 2 := by
          refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
          rw [Complex.sub_re, Complex.sub_im, hre_j j, hre_j (j + 1), sub_self, abs_zero, zero_add,
            him_diff, add_sub_cancel_left, abs_of_nonneg (sq_nonneg t)]
        have hlip := (abs_LamM_sub_le (toMatrix_isHermitian x)
          (by positivity : (0 : ℝ) < 1 / N) hη1 hη1').1
        have eL : ∀ w, LamM (toMatrix x) w = Lam x w := fun w => rfl
        rw [eL, eL, one_div, inv_inv] at hlip
        have hc : ((N : ℝ) ^ 2 + N + 1) * ‖zj j - zj (j + 1)‖ ≤ 3 * t := by
          have h1 : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ hN1r (by norm_num)
          have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1r
          calc ((N : ℝ) ^ 2 + N + 1) * ‖zj j - zj (j + 1)‖ ≤ (3 * (N : ℝ) ^ 2) * t ^ 2 :=
                mul_le_mul (by linarith) hdiff (norm_nonneg _) (by positivity)
            _ = 3 * t * ((N : ℝ) ^ 2 * t) := by ring
            _ = 3 * t := by rw [hNt, mul_one]
        have hΛstep : Lam x (zj (j + 1)) ≤ Lam x (zj j) + 3 * t := by
          have := (abs_le.1 hlip).1
          linarith
        -- the step for `ϰ`
        have hvk_step : varkappa (zj j) ≤ varkappa (zj (j + 1)) + t := by
          unfold varkappa
          rw [him_diff, hre_j, ← hre_j (j + 1), ← add_assoc]
          have hA : 0 ≤ kappaE (zj (j + 1)).re + (zj (j + 1)).im := by
            unfold kappaE
            have := abs_nonneg (|(zj (j + 1)).re| - 2)
            linarith
          refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
          linarith only [Real.sq_sqrt hA, mul_nonneg (Real.sqrt_nonneg
            (kappaE (zj (j + 1)).re + (zj (j + 1)).im)) ht0.le]
        have hNs : 1 / (N : ℝ) ≤ 1 / √N := one_div_le_one_div_of_le hsN hsqN
        linarith
    have hPk := hind k le_rfl
    rw [hzjk] at hPk
    obtain ⟨hA1, hA2⟩ := hdich z hzz hta hPk
    obtain ⟨-, -, -, -, -, hW, -, -⟩ := hT4 z hz.2 x
    exact ⟨hA1, by linarith⟩
  -- (b)
  have hu : 0 < (N : ℝ) * z.im := by positivity
  have hpartB : Lam x z ≤ E * K ^ 4 / (N * z.im) := by
    by_cases hta : E * K ^ 3 ≤ varkappa z * (N * z.im)
    · refine (hpartA hta).1.trans (div_le_div_of_nonneg_right ?_ hu.le)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK1' (by norm_num)) hE0
    · obtain ⟨-, -, -, -, -, -, hW, -⟩ := hT4 z hz.2 x
      obtain ⟨-, -, hQ⟩ := hpt z hzz x (hxw z hzz)
      obtain ⟨hsq, -⟩ :=
        lattice_norm_facts (stieltjesEmp (toMatrix x) z - msc z) (msc z * (1 - msc z ^ 2))
      exact lattice_partb hu (by linarith) hE0 hE₀0 hE₀E (norm_nonneg _) hW (not_le.1 hta) hQ hsq
  -- (c)
  have hpartC : LamD x z + LamO x z ≤
      E * K ^ 5 * (√((msc z).im / (N * z.im)) + 1 / (N * z.im)) := by
    obtain ⟨hxE, hst2, -⟩ := hpt z hzz x (hxw z hzz)
    have hst : 0 < lamSt C₀ δm δp := by unfold lamSt stabCs; positivity
    obtain ⟨-, -, -, -, hLo, -, -, -, hD, hLd, -, -, -⟩ := hAP z hz.2 x hxE (by linarith)
    obtain ⟨-, -, -, hmlo, -, -, -, -⟩ := hT4 z hz.2 x
    have hΛD := lattice_lam_le_lamD hNnat x z
    have hLO : 0 ≤ LamO x z := Real.iSup_nonneg fun _ => norm_nonneg _
    have hΛst : Lam x z ≤ 1 / (576 * Cs) := by
      have : lamSt C₀ δm δp = 1 / (576 * Cs) := rfl
      linarith
    have hΛ0 : 0 ≤ Lam x z := norm_nonneg _
    unfold ctrlPsi at hLo hD
    exact lattice_partc hΛ0 hu (le_trans (by positivity) hmlo) hCs (by linarith) (by linarith)
      hE1 hLo hD hLd hΛst hpartB hP hPE
  exact ⟨hpartA, hpartB, hpartC⟩

end Rigidity
