import Rigidity.Ensemble.SpecB
import Rigidity.LocalLaw.Lattice
import Rigidity.Semicircle.Algebra
import Rigidity.Stability.Equations

/-!
# One step in the far regime (NP v1.1, §5.2: Lemma 5.4)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `λ_f(z) = 1/(2(|z| + 3))` of Lemma 5.4. -/
noncomputable def farLam (z : ℂ) : ℝ := 1 / (2 * (‖z‖ + 3))

/-- The modulus of an average is at most a uniform bound on the moduli of the terms. -/
private theorem weakFar_avg_le {N : ℕ} (hN : 0 < N) {f : Fin N → ℂ} {c : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ c) : ‖(N : ℂ)⁻¹ * ∑ i, f i‖ ≤ c := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ‖∑ i, f i‖ ≤ N * c :=
    calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, c := Finset.sum_le_sum fun i _ => hf i
      _ = N * c := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ i, f i‖ ≤ (N : ℝ)⁻¹ * (N * c) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c := by field_simp

/-- `Im m ≤ 1` when every diagonal entry of the Green function has modulus at most `1`. -/
private theorem weakFar_im_le {N : ℕ} (hN : 0 < N) {A : Matrix (Fin N) (Fin N) 𝕜} {z : ℂ}
    (hG : ∀ i, ‖green A z i i‖ ≤ 1) : (stieltjesEmp A z).im ≤ 1 := by
  have h := weakFar_avg_le hN hG
  have e : stieltjesEmp A z = (N : ℂ)⁻¹ * ∑ i, green A z i i := by
    simp only [stieltjesEmp, Fintype.card_fin, Matrix.trace, Matrix.diag]
  rw [e]
  exact (Complex.im_le_norm _).trans h

/-- `Ψ_m ≤ 6 (Nη)^{-1/2}` for the control parameter (4.10): `Im m ≤ 1`, `Nη ≥ 1`, `η ≤ 10`. -/
private theorem weakFar_psi {N : ℕ} (hN : 0 < N) {η b : ℝ} (hη : 0 < η) (hη10 : η ≤ 10)
    (hb : b ≤ 1) (hu : 1 ≤ N * η) :
    Real.sqrt (b / (N * η)) + 1 / (N * η) + 1 / Real.sqrt N ≤ 6 / Real.sqrt (N * η) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hu0 : 0 < (N : ℝ) * η := by positivity
  have hs0 : 0 < Real.sqrt ((N : ℝ) * η) := Real.sqrt_pos.2 hu0
  have hs2 : Real.sqrt ((N : ℝ) * η) ^ 2 = N * η := Real.sq_sqrt hu0.le
  have hs1 : 1 ≤ Real.sqrt ((N : ℝ) * η) := by nlinarith
  have h1 : Real.sqrt (b / (N * η)) ≤ 1 / Real.sqrt ((N : ℝ) * η) := by
    calc Real.sqrt (b / (N * η)) ≤ Real.sqrt (1 / (N * η)) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hb hu0.le)
      _ = 1 / Real.sqrt ((N : ℝ) * η) := by rw [Real.sqrt_div' _ hu0.le, Real.sqrt_one]
  have h2 : 1 / ((N : ℝ) * η) ≤ 1 / Real.sqrt ((N : ℝ) * η) := by
    have : Real.sqrt ((N : ℝ) * η) ≤ N * η := by nlinarith
    exact one_div_le_one_div_of_le hs0 this
  have h3 : 1 / Real.sqrt N ≤ 4 / Real.sqrt ((N : ℝ) * η) := by
    have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    rw [div_le_div_iff₀ hr hs0]
    have : Real.sqrt ((N : ℝ) * η) ≤ 4 * Real.sqrt N := by
      rw [Real.sqrt_le_left (by positivity)]
      have e : (4 * Real.sqrt N) ^ 2 = 16 * N := by
        rw [mul_pow, Real.sq_sqrt hNr.le]
        norm_num
      rw [e]
      nlinarith
    linarith
  calc _ ≤ 1 / Real.sqrt ((N : ℝ) * η) + 1 / Real.sqrt ((N : ℝ) * η) +
        4 / Real.sqrt ((N : ℝ) * η) := add_le_add (add_le_add h1 h2) h3
    _ = 6 / Real.sqrt ((N : ℝ) * η) := by ring

/-- The standing inequalities of Lemma 4.6 give `P = N^{1/32}` with `P³ ≥ 255`, `√N = P^16`,
`𝔏 ≤ P` and `E_max ≤ P`. -/
private theorem weakFar_levels {N : ℕ} {a C₀ K : ℝ} (hN : 13 ≤ N) (hK : 255 ≤ K)
    (hL : levelFL a C₀ K N ≤ K ^ (4 * a + 3)) (hE : levelEmax a C₀ K N ≤ K ^ (2 * a + 1))
    (ha : 1 ≤ a) (h6 : K ^ (6 * a + 6) ≤ (N : ℝ) ^ (1 / 32 : ℝ))
    (h255 : 255 * (N : ℝ) ^ (1 / 32 : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ)) :
    ∃ P : ℝ, 1 ≤ P ∧ 255 ≤ P ^ 3 ∧ Real.sqrt N = P ^ 16 ∧
      levelFL a C₀ K N ≤ P ∧ levelEmax a C₀ K N ≤ P := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hK1 : 1 ≤ K := by linarith
  set P : ℝ := (N : ℝ) ^ (1 / 32 : ℝ) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 (by norm_num)
  have hpow : ∀ (n : ℕ) (q : ℝ), q = n / 32 → (N : ℝ) ^ q = P ^ n := by
    intro n q hq
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hN0, hq]
    congr 1
    ring
  have h8 : (N : ℝ) ^ (1 / 8 : ℝ) = P ^ 4 := hpow 4 _ (by norm_num)
  have h16 : (N : ℝ) ^ (1 / 2 : ℝ) = P ^ 16 := hpow 16 _ (by norm_num)
  refine ⟨P, hP1, ?_, by rw [Real.sqrt_eq_rpow, h16], ?_, ?_⟩
  · rw [h8] at h255
    have h : P * 255 ≤ P * P ^ 3 := by nlinarith
    exact le_of_mul_le_mul_left h (by linarith)
  · exact hL.trans ((Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)).trans h6)
  · exact hE.trans ((Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)).trans h6)

/-- The size conditions of Lemma 5.4, for `√N = P^16`, `P³ ≥ 255`, `𝔏 ≤ P`, `E_max ≤ P` and
`z ∈ 𝐃^far`: `Nη ≥ 1` and `12 (|z| + 3) 𝔏 ≤ √(Nη)`; also `|z| + 3 ≥ 7`. -/
private theorem weakFar_size {N : ℕ} {L E P : ℝ} {z : ℂ} (hN : 0 < N) (hP1 : 1 ≤ P)
    (hP3 : 255 ≤ P ^ 3) (hPN : Real.sqrt N = P ^ 16) (hL0 : 0 ≤ L) (hLP : L ≤ P) (hE1 : 1 ≤ E)
    (hEP : E ≤ P) (hE4 : 4 ≤ |z.re|) (hEz : |z.re| ≤ E + 1) (hη1 : 1 / (2 * Real.sqrt N) ≤ z.im)
    (hη10 : z.im ≤ 10) :
    0 < z.im ∧ 1 ≤ (N : ℝ) * z.im ∧ 7 ≤ ‖z‖ + 3 ∧
      12 * (‖z‖ + 3) * L ≤ Real.sqrt ((N : ℝ) * z.im) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hη : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  have hu0 : 0 < (N : ℝ) * z.im := by positivity
  have hP0 : 0 < P := by linarith only [hP1]
  have hs2 : Real.sqrt ((N : ℝ) * z.im) ^ 2 = N * z.im := Real.sq_sqrt hu0.le
  have hP16 : 255 ≤ P ^ 16 := hP3.trans (pow_le_pow_right₀ hP1 (by norm_num))
  have hu : P ^ 16 / 2 ≤ N * z.im := by
    have hNr2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
    have h1 : 1 ≤ z.im * (2 * Real.sqrt N) := by
      rwa [div_le_iff₀ (by positivity)] at hη1
    have h2 : Real.sqrt N * 1 ≤ Real.sqrt N * (z.im * (2 * Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left h1 hrN.le
    have h3 : Real.sqrt N * (z.im * (2 * Real.sqrt N)) = 2 * (N * z.im) := by
      linear_combination (2 * z.im) * hNr2
    linarith only [h2, h3, hPN]
  have hs8 : P ^ 8 ≤ 2 * Real.sqrt ((N : ℝ) * z.im) := by
    have h : (P ^ 8) ^ 2 ≤ (2 * Real.sqrt ((N : ℝ) * z.im)) ^ 2 := by
      have e : (P ^ 8) ^ 2 = P ^ 16 := by ring
      have e2 : (2 * Real.sqrt ((N : ℝ) * z.im)) ^ 2 = 4 * (N * z.im) := by
        rw [mul_pow, hs2]
        norm_num
      rw [e, e2]
      linarith only [hu, hP16]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h
  have hzre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hznorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hzim : |z.im| = z.im := abs_of_pos hη
  have hW : ‖z‖ + 3 ≤ 15 * P := by linarith only [hznorm, hzim, hEz, hη10, hE1, hEP]
  refine ⟨hη, by linarith only [hu, hP16], by linarith only [hzre, hE4], ?_⟩
  have h1 : (‖z‖ + 3) * L ≤ (15 * P) * P := mul_le_mul hW hLP hL0 (by positivity)
  have hP6 : 360 ≤ P ^ 6 := by nlinarith only [hP3]
  have h2 : P ^ 2 * 360 ≤ P ^ 2 * P ^ 6 := mul_le_mul_of_nonneg_left hP6 (sq_nonneg P)
  have e : P ^ 8 = P ^ 2 * P ^ 6 := by ring
  nlinarith only [h1, h2, e, hs8]

/-- `𝔏 Ψ_m ≤ 1/8` from `Ψ_m ≤ 6 (Nη)^{-1/2}`, `12 (|z| + 3) 𝔏 ≤ √(Nη)` and `|z| + 3 ≥ 7`. -/
private theorem weakFar_LPsi {L Ψ s W : ℝ} (hs0 : 0 < s) (hΨ : Ψ ≤ 6 / s) (hL0 : 0 ≤ L)
    (hW7 : 7 ≤ W) (hβ : 12 * W * L ≤ s) : L * Ψ ≤ 1 / 8 := by
  have h1 : L * Ψ ≤ L * (6 / s) := mul_le_mul_of_nonneg_left hΨ hL0
  refine h1.trans ?_
  rw [mul_div_assoc', div_le_iff₀ hs0]
  nlinarith only [hβ, hW7, hL0]

/-- (I3) of Lemma 3.6 as used in the proof of Lemma 5.4: if `|G_jj| ≤ 1/2`, `|G_ji|, |G_ij| ≤ λ`
with `λ (w + 3) = 1/2` and `1/|G_ii| ≤ w + 2` for some `w ≥ 0`, then
`|G_jj - G_ji G_ij / G_ii| ≤ 1`. -/
private theorem weakFar_minor {a b c d : ℂ} {lam w : ℝ} (hw : 0 ≤ w) (hlam : lam * (w + 3) = 1 / 2)
    (hlam0 : 0 ≤ lam) (hd : ‖d‖ ≤ 1 / 2) (hb : ‖b‖ ≤ lam) (hc : ‖c‖ ≤ lam)
    (ha : 1 / ‖a‖ ≤ w + 2) : ‖d - b * c / a‖ ≤ 1 := by
  have hlam6 : lam ≤ 1 / 6 := by nlinarith only [hlam, hw, hlam0]
  have hq : ‖b‖ * ‖c‖ / ‖a‖ ≤ lam * lam * (w + 2) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul hb hc (norm_nonneg _) hlam0) ha (by positivity) (by positivity)
  have e : lam * lam * (w + 3) = lam / 2 := by
    rw [mul_assoc, hlam]
    ring
  have hq2 : lam * lam * (w + 2) ≤ 1 / 12 := by
    nlinarith only [e, mul_nonneg hlam0 hlam0, hlam6]
  calc ‖d - b * c / a‖ ≤ ‖d‖ + ‖b * c / a‖ := norm_sub_le _ _
    _ = ‖d‖ + ‖b‖ * ‖c‖ / ‖a‖ := by rw [norm_div, norm_mul]
    _ ≤ 1 := by linarith only [hd, hq, hq2]

/-- The deterministic part of Lemma 5.4: at a point `x` of `𝒢(z)` with `z ∈ 𝐃^far`,
`max |G_ii| ≤ 1` and `Λ_o ≤ λ_f(z)`, given `N ≥ 13`, `κ_ϑ + 3 log N ≤ K²`, `150 ≤ 𝔏`,
`1 ≤ E_max` and `P ≥ 1` with `P³ ≥ 255`, `√N = P^16`, `𝔏 ≤ P`, `E_max ≤ P`. -/
private theorem weakFar_point {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ K P : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) (hN : 13 ≤ N)
    (hκ : kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ K ^ 2) (hP1 : 1 ≤ P) (hP3 : 255 ≤ P ^ 3)
    (hPN : Real.sqrt N = P ^ 16) (hL150 : 150 ≤ levelFL ϑ⁻¹ C₀ K N)
    (hLP : levelFL ϑ⁻¹ C₀ K N ≤ P) (hE1 : 1 ≤ levelEmax ϑ⁻¹ C₀ K N)
    (hEP : levelEmax ϑ⁻¹ C₀ K N ≤ P) {z : ℂ} (hz : z ∈ Dfar ϑ⁻¹ C₀ K N)
    {x : Pair N → 𝕜} (hx : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z)
    (hG1 : ∀ i, ‖green (toMatrix x) z i i‖ ≤ 1) (hO : LamO x z ≤ farLam z) :
    (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2) ∧
      (∀ i, 1 / ‖green (toMatrix x) z i i‖ ≤ ‖z‖ + 2) ∧
      LamD x z ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ∧
      levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ≤
        6 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) ∧
      LamO x z ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z / 2 ∧
      3 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) ≤ farLam z / 2 := by
  have hN0 : 0 < N := by omega
  obtain ⟨hE4, hEz, hη1, hη10⟩ := hz
  obtain ⟨hη, hu1, hW7, hβ⟩ := weakFar_size hN0 hP1 hP3 hPN (by linarith only [hL150]) hLP hE1 hEP
    hE4 hEz hη1 hη10
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hu0 : 0 < (N : ℝ) * z.im := by positivity
  have hs0 : 0 < Real.sqrt ((N : ℝ) * z.im) := Real.sqrt_pos.2 hu0
  -- the control parameter
  have hIm : (stieltjesEmp (toMatrix x) z).im ≤ 1 := weakFar_im_le hN0 hG1
  have hΨ : ctrlPsiM x z ≤ 6 / Real.sqrt ((N : ℝ) * z.im) :=
    weakFar_psi hN0 hη hη10 hIm hu1
  have hΨ0 : 0 ≤ ctrlPsiM x z := by unfold ctrlPsiM; positivity
  have hrpow : ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt ((N : ℝ) * z.im) := by
    rw [Real.rpow_neg hu0.le, ← Real.sqrt_eq_rpow, one_div]
  -- the good event
  obtain ⟨-, -, hS5, -⟩ := goodEvent_level M hM hϑ hϑ1 hC₀ hN hη hκ
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 (by omega)
  -- Lemma 3.12
  have hB := hM.varProfile
  have hrow : ∀ i, ∑ j, M.varMatrix i j = 1 := fun i => by
    rw [← hB.sumA i]
    exact Finset.sum_congr rfl fun j _ => (hB.symm.apply i j).symm
  obtain ⟨hD, -, hinv⟩ := stab_far hN0 (toMatrix_isHermitian x) hrow hB.sumA hB.nonneg hE4 hη hG1
  have hD' : LamD x z ≤ (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) / 2 := hD
  obtain ⟨hm1, -, -⟩ := msc_far hη hE4
  have hdiag : ∀ i, ‖green (toMatrix x) z i i - msc z‖ ≤ LamD x z := fun i =>
    le_ciSup (f := fun k : Fin N => ‖green (toMatrix x) z k k - msc z‖)
      (Set.finite_range _).bddAbove i
  have hOff : ∀ i j, i ≠ j → ‖green (toMatrix x) z i j‖ ≤ LamO x z := fun i j hij =>
    le_ciSup (f := fun q : {q : Fin N × Fin N // q.1 ≠ q.2} =>
      ‖green (toMatrix x) z q.1.1 q.1.2‖) (Set.finite_range _).bddAbove ⟨(i, j), hij⟩
  have hlam : farLam z * (‖z‖ + 3) = 1 / 2 := by unfold farLam; field_simp
  have hlam0 : 0 ≤ farLam z := by unfold farLam; positivity
  have hfl : farLam z / 2 = 1 / (4 * (‖z‖ + 3)) := by unfold farLam; field_simp; ring
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hL0 : 0 ≤ levelFL ϑ⁻¹ C₀ K N := by linarith only [hL150]
  have hLΨ8 : levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ≤ 1 / 8 := weakFar_LPsi hs0 hΨ hL0 hW7 hβ
  have hΨ1 : ctrlPsiM x z ≤ 1 := by nlinarith only [hLΨ8, hL150, hΨ0]
  have hUps : ∀ i, ‖selfUps (toMatrix x) M.varMatrix z i‖ ≤
      2 * (levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z) := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨h1, h2, -⟩ := hS5 x hx i j hj.symm
    have hA : ‖selfA (toMatrix x) M.varMatrix z i‖ ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z := by
      have e1 : ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 ≤ 1 * ctrlPsiM x z :=
        mul_le_mul (hG1 i) (by nlinarith only [hΨ0, hΨ1]) (sq_nonneg _) zero_le_one
      calc ‖selfA (toMatrix x) M.varMatrix z i‖
          ≤ levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 := h2
        _ = levelFL ϑ⁻¹ C₀ K N * (‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2) := by ring
        _ ≤ levelFL ϑ⁻¹ C₀ K N * (1 * ctrlPsiM x z) := mul_le_mul_of_nonneg_left e1 hL0
        _ = levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z := by ring
    have h3 : ‖selfUps (toMatrix x) M.varMatrix z i‖ ≤
        ‖selfA (toMatrix x) M.varMatrix z i‖ + ‖selfX (toMatrix x) M.varMatrix z i‖ :=
      norm_add_le _ _
    linarith only [h1, hA, h3]
  have hUmax : (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
      2 * (levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z) :=
    Real.iSup_le hUps (by positivity)
  have hLD : LamD x z ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z := by
    linarith only [hD', hUmax]
  have hLD8 : LamD x z ≤ 1 / 8 := by linarith only [hD', hUmax, hLΨ8]
  have hGD : ∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2 := by
    intro i
    calc ‖green (toMatrix x) z i i‖ = ‖msc z + (green (toMatrix x) z i i - msc z)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖msc z‖ + ‖green (toMatrix x) z i i - msc z‖ := norm_add_le _ _
      _ ≤ 1 / 2 := by linarith only [hm1, hdiag i, hLD8]
  have hinv2 : ∀ i, 1 / ‖green (toMatrix x) z i i‖ ≤ ‖z‖ + 2 := by
    intro i
    have h := hinv i
    have hΥ : (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤ 1 / 4 := by
      linarith only [hUmax, hLΨ8]
    linarith only [h, hΥ]
  have hGT : ∀ i j, i ≠ j → ‖greenT (toMatrix x) {i} z j j‖ ≤ 1 := by
    intro i j hij
    rw [greenT_single (toMatrix_isHermitian x) hη hij.symm hij.symm]
    exact weakFar_minor hz0 hlam hlam0 (hGD j) ((hOff j i hij.symm).trans hO)
      ((hOff i j hij).trans hO) (hinv2 i)
  have hLO : LamO x z ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z / 2 := by
    refine Real.iSup_le (fun q => ?_) (by positivity)
    obtain ⟨⟨i, j⟩, hij⟩ := q
    obtain ⟨-, -, h3⟩ := hS5 x hx i j hij
    calc ‖green (toMatrix x) z i j‖
        ≤ levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ *
            ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z := h3
      _ ≤ levelFL ϑ⁻¹ C₀ K N * (1 / 2) * 1 * ctrlPsiM x z := by
          gcongr
          · exact hGD i
          · exact hGT i j hij
      _ = levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z / 2 := by ring
  refine ⟨hGD, hinv2, hLD, ?_, hLO, ?_⟩
  · rw [hrpow]
    calc levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z
        ≤ levelFL ϑ⁻¹ C₀ K N * (6 / Real.sqrt ((N : ℝ) * z.im)) :=
          mul_le_mul_of_nonneg_left hΨ hL0
      _ = 6 * levelFL ϑ⁻¹ C₀ K N * (1 / Real.sqrt ((N : ℝ) * z.im)) := by ring
  · rw [hrpow, mul_one_div, hfl, div_le_div_iff₀ hs0 (by positivity)]
    nlinarith only [hβ]

/-- Lemma 5.4: one step in the far regime, on `𝒢(z) ∩ {maxᵢ |Gᵢᵢ| ≤ 1, Λ_o ≤ λ_f(z)}`. -/
theorem far_step {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ Dfar ϑ⁻¹ C₀ K N, ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z,
        (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1) → LamO x z ≤ farLam z →
        (∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2) ∧
        (∀ i, 1 / ‖green (toMatrix x) z i i‖ ≤ ‖z‖ + 2) ∧
        LamD x z ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ∧
        levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ≤
          6 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) ∧
        LamO x z ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z / 2 ∧
        3 * levelFL ϑ⁻¹ C₀ K N * ((N : ℝ) * z.im) ^ (-(1 / 2 : ℝ)) ≤ farLam z / 2 := by
  obtain ⟨N₀, hN₀⟩ := standing_ineq hϑ hϑ1 hC₀ 255
  refine ⟨N₀, fun N hN M hM K hK1 hK2 z hz x hx hG1 hO => ?_⟩
  obtain ⟨⟨hK255, hN13, -, hκ⟩, ⟨hL150, hLK, hE1, hEK⟩, -, h6, h255⟩ := hN₀ N hN K hK1 hK2
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨P, hP1, hP3, hPN, hLP, hEP⟩ := weakFar_levels hN13 hK255 hLK hEK ha h6 h255
  exact weakFar_point M hM hϑ hϑ1 hC₀ hN13 hκ hP1 hP3 hPN hL150 hLP hE1 hEP hz hx hG1 hO

end Rigidity
