module

public import Rigidity.Ensemble.SpecB
public import Rigidity.LocalLaw.Lattice
public import Rigidity.Stability.Near

@[expose] public section

/-!
# Bounds under the a priori assumption (NP v1.1, §5.2: Lemma 5.1)

Numbers in this file refer to the blueprint NP v1.1.

The statement is deterministic at a point `x` of the indicated event, for one fixed `z`; they
are stated for `N ≥ N₀` and `K` in the range `(log N)³ ≤ K ≤ N^{c₀}`, where the standing
inequalities (S1)–(S5) of Lemma 4.6 hold.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `𝔈₀ = 6·10⁶ C_s² 𝔏²` of Lemma 5.1 (`a = 1/ϑ`). -/
noncomputable def aprioriE0 (a C₀ δm δp K : ℝ) (N : ℕ) : ℝ :=
  6 * 10 ^ 6 * stabCs C₀ δm δp ^ 2 * levelFL a C₀ K N ^ 2

/-- `C_a = 3·10⁶ C_s²` of (5.2′). -/
noncomputable def aprioriCa (C₀ δm δp : ℝ) : ℝ := 3 * 10 ^ 6 * stabCs C₀ δm δp ^ 2

/-- The modulus of an average is at most a uniform bound on the moduli of the terms. -/
private theorem weakOnePoint_avg_le {N : ℕ} (hN : 0 < N) {f : Fin N → ℂ} {c : ℝ}
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

/-- On `|E| ≤ 5`, `0 < η ≤ 10`: `|z| ≤ 12`, hence `η ≤ 169 Im m_sc` by Lemma 3.1 (c), and
`Im m_sc ≤ 1`. -/
private theorem weakOnePoint_im {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im) (hη' : z.im ≤ 10) :
    z.im ≤ 169 * (msc z).im ∧ (msc z).im ≤ 1 := by
  obtain ⟨-, hmsc1, hmscIm⟩ := msc_bounds hη
  have hz12 : ‖z‖ ≤ 12 := by
    have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have h2 : z.re * z.re ≤ 25 := by
      have := abs_le.1 hE
      nlinarith only [this]
    have h3 : z.im * z.im ≤ 100 := by nlinarith only [hη, hη']
    nlinarith only [h1, h2, h3, norm_nonneg z]
  have h1 : (‖z‖ + 1) ^ 2 ≤ 169 := by
    have := pow_le_pow_left₀ (by positivity) (by linarith : ‖z‖ + 1 ≤ 13) 2
    norm_num at this ⊢
    linarith
  have h2 : z.im / 169 ≤ z.im / (‖z‖ + 1) ^ 2 :=
    div_le_div_of_nonneg_left hη.le (by positivity) h1
  exact ⟨by linarith, (Complex.im_le_norm _).trans hmsc1⟩

/-- `Ψ_m ≤ 14 Ψ`: for `N ≥ 1`, `η > 0`, `Im m ≤ α` and `η ≤ 169 α` (here `α = Im m_sc + Λ`),
`√(Im m/(Nη)) + 1/(Nη) + N^{-1/2} ≤ 14 (√(α/(Nη)) + 1/(Nη))`. -/
private theorem weakOnePoint_psiM {N : ℕ} (hN : 0 < N) {η b α : ℝ} (hη : 0 < η) (hb : b ≤ α)
    (h169 : η ≤ 169 * α) :
    Real.sqrt (b / (N * η)) + 1 / (N * η) + 1 / Real.sqrt N ≤
      14 * (Real.sqrt (α / (N * η)) + 1 / (N * η)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hu0 : 0 < (N : ℝ) * η := by positivity
  have h1 : Real.sqrt (b / (N * η)) ≤ Real.sqrt (α / (N * η)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hb hu0.le)
  have h2 : 1 / Real.sqrt N ≤ 13 * Real.sqrt (α / (N * η)) := by
    have e1 : 1 / (N : ℝ) ≤ 169 * (α / (N * η)) := by
      calc 1 / (N : ℝ) = η / (N * η) := by field_simp
        _ ≤ (169 * α) / (N * η) := div_le_div_of_nonneg_right h169 hu0.le
        _ = 169 * (α / (N * η)) := by ring
    have e2 := Real.sqrt_le_sqrt e1
    rw [Real.sqrt_mul (by norm_num), show (169 : ℝ) = 13 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), one_div, Real.sqrt_inv] at e2
    rw [one_div]
    exact e2
  have h4 : 0 ≤ 1 / ((N : ℝ) * η) := by positivity
  linarith

/-- The size of `Ψ` in the proof of Lemma 5.1: for `u ≥ 4𝔏²`, `𝔏 ≥ 150` and `α ≤ 9/4`,
`Ψ = √(α/u) + 1/u` satisfies `Ψ ≤ 2u^{-1/2}`, `Ψ ≤ 1` and `𝔏 Ψ ≤ 1`. -/
private theorem weakOnePoint_psi {u L α : ℝ} (hL : 150 ≤ L) (hu : 4 * L ^ 2 ≤ u)
    (hα : α ≤ 9 / 4) :
    Real.sqrt (α / u) + 1 / u ≤ 2 / Real.sqrt u ∧ Real.sqrt (α / u) + 1 / u ≤ 1 ∧
      L * (Real.sqrt (α / u) + 1 / u) ≤ 1 := by
  have hL0 : 0 ≤ L := by linarith
  have hu16 : 16 ≤ u := by nlinarith only [hL, hu]
  have hu0 : 0 < u := by linarith
  have hs4 : 4 ≤ Real.sqrt u := (Real.le_sqrt (by norm_num) hu0.le).2 (by linarith)
  have hss : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  have hs0 : 0 < Real.sqrt u := by linarith
  have hΨ2s : Real.sqrt (α / u) + 1 / u ≤ 2 / Real.sqrt u := by
    have h1 : Real.sqrt (α / u) ≤ (3 / 2) / Real.sqrt u := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_pow, hss]
      exact div_le_div_of_nonneg_right (by linarith) hu0.le
    have h2 : 1 / u ≤ (1 / 4) / Real.sqrt u := by
      rw [div_le_div_iff₀ hu0 hs0]
      nlinarith only [hs4, hss]
    have : (3 / 2) / Real.sqrt u + (1 / 4) / Real.sqrt u ≤ 2 / Real.sqrt u := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by norm_num) hs0.le
    linarith
  have hLs : 2 * L ≤ Real.sqrt u :=
    (Real.le_sqrt (by positivity) hu0.le).2 (by nlinarith only [hu])
  refine ⟨hΨ2s, hΨ2s.trans ?_, ?_⟩
  · rw [div_le_one hs0]; linarith
  · calc L * (Real.sqrt (α / u) + 1 / u) ≤ L * (2 / Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hΨ2s hL0
      _ = (2 * L) / Real.sqrt u := by ring
      _ ≤ 1 := by rw [div_le_one hs0]; exact hLs

/-- `Ψ² ≤ 2α/u + 2/u²` for `Ψ = √(α/u) + 1/u`, `α ≥ 0`, `u > 0`. -/
private theorem weakOnePoint_psi_sq {u α : ℝ} (hu : 0 < u) (hα0 : 0 ≤ α) :
    (Real.sqrt (α / u) + 1 / u) ^ 2 ≤ 2 * (α / u) + 2 * (1 / u ^ 2) := by
  have e1 : Real.sqrt (α / u) ^ 2 = α / u := Real.sq_sqrt (div_nonneg hα0 hu.le)
  have e2 : (1 / u) ^ 2 = 1 / u ^ 2 := by ring
  nlinarith only [e1, e2, sq_nonneg (Real.sqrt (α / u) - 1 / u)]

/-- The final arithmetic of (5.4) and (5.2′): from
`Q ≤ |⟨X⟩| + 245 𝔏 Ψ² + 40 C_s² (259 𝔏 Ψ)² + (3/10) Λ²`, with `𝔏, C_s ≥ 1`, `0 ≤ Ψ ≤ 1`,
`𝔏 Ψ ≤ 1`, `|⟨X⟩| ≤ 14 𝔏 Ψ` and `Ψ² ≤ 2β`, follow `Q ≤ |⟨X⟩| + 6·10⁶ C_s² 𝔏² β + (3/4) Λ²` and
`Q ≤ 3·10⁶ C_s² 𝔏 Ψ + (3/10) Λ²`. -/
private theorem weakOnePoint_alg {Q X L Ψ Cs Λ β : ℝ} (hL1 : 1 ≤ L) (hCs1 : 1 ≤ Cs)
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hLΨ : L * Ψ ≤ 1) (hΨ2 : Ψ ^ 2 ≤ 2 * β) (hX : X ≤ 14 * L * Ψ)
    (hkey : Q ≤ X + 245 * L * Ψ ^ 2 + 40 * Cs ^ 2 * (259 * L * Ψ) ^ 2 + 3 / 10 * Λ ^ 2) :
    Q ≤ X + 6 * 10 ^ 6 * Cs ^ 2 * L ^ 2 * β + 3 / 4 * Λ ^ 2 ∧
      Q ≤ 3 * 10 ^ 6 * Cs ^ 2 * L * Ψ + 3 / 10 * Λ ^ 2 := by
  have hCs2 : 1 ≤ Cs ^ 2 := one_le_pow₀ hCs1
  have hL0 : 0 ≤ L := by linarith
  have hΛ : 0 ≤ Λ ^ 2 := sq_nonneg _
  refine ⟨?_, ?_⟩
  · have hLL : L ≤ Cs ^ 2 * L ^ 2 := by nlinarith only [hCs2, hL1]
    have h1 : 245 * L * Ψ ^ 2 ≤ 245 * (Cs ^ 2 * L ^ 2) * Ψ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hLL (sq_nonneg Ψ)
      linarith
    have h2 : Cs ^ 2 * L ^ 2 * Ψ ^ 2 ≤ Cs ^ 2 * L ^ 2 * (2 * β) :=
      mul_le_mul_of_nonneg_left hΨ2 (by positivity)
    have h3 : 0 ≤ Cs ^ 2 * L ^ 2 * Ψ ^ 2 := by positivity
    have e : 40 * Cs ^ 2 * (259 * L * Ψ) ^ 2 = 2683240 * (Cs ^ 2 * L ^ 2 * Ψ ^ 2) := by ring
    have e' : 245 * (Cs ^ 2 * L ^ 2) * Ψ ^ 2 = 245 * (Cs ^ 2 * L ^ 2 * Ψ ^ 2) := by ring
    have e'' : 6 * 10 ^ 6 * Cs ^ 2 * L ^ 2 * β = 3 * 10 ^ 6 * (Cs ^ 2 * L ^ 2 * (2 * β)) := by
      ring
    linarith
  · have hP0 : 0 ≤ L * Ψ := mul_nonneg hL0 hΨ0
    have hΨsq : Ψ ^ 2 ≤ Ψ := by nlinarith only [hΨ0, hΨ1]
    have h1 : L * Ψ ^ 2 ≤ L * Ψ := mul_le_mul_of_nonneg_left hΨsq hL0
    have h2 : (L * Ψ) ^ 2 ≤ L * Ψ := by nlinarith only [hP0, hLΨ]
    have h3 : Cs ^ 2 * (L * Ψ) ^ 2 ≤ Cs ^ 2 * (L * Ψ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : L * Ψ ≤ Cs ^ 2 * (L * Ψ) := by nlinarith only [hCs2, hP0]
    have e : 40 * Cs ^ 2 * (259 * L * Ψ) ^ 2 = 2683240 * (Cs ^ 2 * (L * Ψ) ^ 2) := by ring
    have e' : 245 * L * Ψ ^ 2 = 245 * (L * Ψ ^ 2) := by ring
    have e'' : 14 * L * Ψ = 14 * (L * Ψ) := by ring
    have e3 : 3 * 10 ^ 6 * Cs ^ 2 * L * Ψ = 3 * 10 ^ 6 * (Cs ^ 2 * (L * Ψ)) := by ring
    linarith

/-- (I3) of Lemma 3.6 as used in the proof of Lemma 5.1: if `3/52 ≤ |G_ii|`, `|G_jj| ≤ 5/4`
and `|G_ij|, |G_ji| ≤ λ ≤ 1/576`, then `|G_jj - G_ji G_ij / G_ii| ≤ 2`. -/
private theorem weakOnePoint_minor {a b c d : ℂ} {lam : ℝ} (ha : 3 / 52 ≤ ‖a‖) (hd : ‖d‖ ≤ 5 / 4)
    (hb : ‖b‖ ≤ lam) (hc : ‖c‖ ≤ lam) (hlam : lam ≤ 1 / 576) :
    ‖d - b * c / a‖ ≤ 2 := by
  have hp : ‖b‖ * ‖c‖ ≤ (1 / 576) ^ 2 := by
    have h0 : 0 ≤ lam := (norm_nonneg _).trans hb
    have := mul_le_mul hb hc (norm_nonneg _) h0
    nlinarith only [this, h0, hlam]
  have hp0 : 0 ≤ ‖b‖ * ‖c‖ := by positivity
  calc ‖d - b * c / a‖ ≤ ‖d‖ + ‖b‖ * ‖c‖ / ‖a‖ := by
        rw [← norm_mul, ← norm_div]; exact norm_sub_le _ _
    _ ≤ 5 / 4 + ‖b‖ * ‖c‖ / (3 / 52) := by
        gcongr
    _ ≤ 2 := by
        have : ‖b‖ * ‖c‖ / (3 / 52) ≤ (1 / 576) ^ 2 / (3 / 52) :=
          div_le_div_of_nonneg_right hp (by norm_num)
        norm_num at this ⊢
        linarith

/-- The deterministic part of Lemma 5.1: at a point `x` of `𝒢(z)` with `Λ_d + Λ_o ≤ λ_st`, for
`|E| ≤ 5`, `0 < η ≤ 10`, `N ≥ 13`, `κ_ϑ + 3 log N ≤ K²`, `𝔏 ≥ 150` and `Nη ≥ 4𝔏²`, the bounds
(5.2)–(5.5) and (5.2′) hold. -/
private theorem weakOnePoint_point {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ K : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm) (hδp : 0 < δp)
    (hC₀ : 1 ≤ C₀) (hN : 13 ≤ N) (hκ : kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ K ^ 2)
    (hL150 : 150 ≤ levelFL ϑ⁻¹ C₀ K N) {z : ℂ} (hE : |z.re| ≤ 5) (hη : 0 < z.im)
    (hη' : z.im ≤ 10) (hu : 4 * levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ N * z.im)
    {x : Pair N → 𝕜} (hx : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z)
    (hs : LamD x z + LamO x z ≤ lamSt C₀ δm δp) :
        (∀ i, 3 / 52 ≤ ‖green (toMatrix x) z i i‖ ∧ ‖green (toMatrix x) z i i‖ ≤ 5 / 4) ∧
        (∀ i j, i ≠ j → ‖greenT (toMatrix x) {i} z j j‖ ≤ 2) ∧
        ctrlPsiM x z ≤ 14 * ctrlPsi x z ∧ ctrlPsi x z ≤ 1 ∧
        LamO x z ≤ 35 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
        (∀ i, ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ 14 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
          ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
            245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2) ∧
        (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
          259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
        ‖(stieltjesEmp (toMatrix x) z - msc z) ^ 2 -
            msc z * (1 - msc z ^ 2) * (stieltjesEmp (toMatrix x) z - msc z)‖ ≤
          ‖(N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i‖ +
            aprioriE0 ϑ⁻¹ C₀ δm δp K N *
              (((msc z).im + Lam x z) / (N * z.im) + 1 / (N * z.im) ^ 2) +
            3 / 4 * Lam x z ^ 2 ∧
        (⨆ i, ‖green (toMatrix x) z i i - msc z - (stieltjesEmp (toMatrix x) z - msc z)‖) ≤
          1036 * stabCs C₀ δm δp * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z +
            144 * stabCs C₀ δm δp * Lam x z ^ 2 ∧
        LamD x z ≤ Lam x z +
          ⨆ i, ‖green (toMatrix x) z i i - msc z - (stieltjesEmp (toMatrix x) z - msc z)‖ ∧
        ctrlPsi x z ≤ 2 / Real.sqrt (N * z.im) ∧ levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ≤ 1 ∧
        ‖(stieltjesEmp (toMatrix x) z - msc z) ^ 2 -
            msc z * (1 - msc z ^ 2) * (stieltjesEmp (toMatrix x) z - msc z)‖ ≤
          aprioriCa C₀ δm δp * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z + 3 / 10 * Lam x z ^ 2 := by
  have hN2 : 2 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hCs1 : 1 ≤ stabCs C₀ δm δp :=
    le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) (lt_min hδm hδp).le)
  have hlamCs : stabCs C₀ δm δp * lamSt C₀ δm δp = 1 / 576 := by
    have : lamSt C₀ δm δp = 1 / (576 * stabCs C₀ δm δp) := rfl
    rw [this]; field_simp
  have hlam0 : 0 ≤ lamSt C₀ δm δp := by
    have : lamSt C₀ δm δp = 1 / (576 * stabCs C₀ δm δp) := rfl
    rw [this]; positivity
  have hlam1 : lamSt C₀ δm δp ≤ 1 / 576 := by nlinarith only [hlamCs, hlam0, hCs1]
  -- the a priori assumption and Lemma 3.10
  have hLO0 : 0 ≤ LamO x z := Real.iSup_nonneg fun _ => norm_nonneg _
  have hLD0 : 0 ≤ LamD x z := Real.iSup_nonneg fun _ => norm_nonneg _
  have hLD : LamDM (toMatrix x) z ≤ lamSt C₀ δm δp := by
    change LamD x z ≤ _
    linarith only [hs, hLO0]
  obtain ⟨hG, hwD, -, hD, hLDle, hquad⟩ :=
    stab_near (toMatrix_isHermitian x) hM.varProfile hδm hδp hN2 hE hη hη' hLD
  have hLam0 : 0 ≤ Lam x z := norm_nonneg _
  have hLam : Lam x z ≤ lamSt C₀ δm δp := hwD.trans hLD
  have hOff : ∀ i j, i ≠ j → ‖green (toMatrix x) z i j‖ ≤ LamO x z := fun i j hij =>
    le_ciSup (f := fun q : {q : Fin N × Fin N // q.1 ≠ q.2} =>
      ‖green (toMatrix x) z q.1.1 q.1.2‖) (Set.finite_range _).bddAbove ⟨(i, j), hij⟩
  have hLO : LamO x z ≤ lamSt C₀ δm δp := by linarith only [hs, hLD0]
  -- `|G^{(i)}_jj| ≤ 2` by (I3)
  have hGT : ∀ i j, i ≠ j → ‖greenT (toMatrix x) {i} z j j‖ ≤ 2 := by
    intro i j hij
    rw [greenT_single (toMatrix_isHermitian x) hη (Ne.symm hij) (Ne.symm hij)]
    exact weakOnePoint_minor (hG i).1 (hG j).2 ((hOff j i (Ne.symm hij)).trans hLO)
      ((hOff i j hij).trans hLO) hlam1
  -- sizes
  obtain ⟨hIm169, hImle⟩ := weakOnePoint_im hE hη hη'
  have hImm : (stieltjesEmp (toMatrix x) z).im ≤ (msc z).im + Lam x z := by
    have := Complex.im_le_norm (stieltjesEmp (toMatrix x) z - msc z)
    rw [Complex.sub_im] at this
    change _ ≤ _ + ‖stieltjesEmp (toMatrix x) z - msc z‖
    linarith only [this]
  have hα0 : 0 ≤ (msc z).im + Lam x z := by
    have := msc_im_pos hη
    linarith only [this, hLam0]
  have hα2 : (msc z).im + Lam x z ≤ 9 / 4 := by linarith only [hImle, hLam, hlam1]
  have hΨdef : ctrlPsi x z = Real.sqrt (((msc z).im + Lam x z) / (N * z.im)) + 1 / (N * z.im) :=
    rfl
  have hΨm : ctrlPsiM x z ≤ 14 * ctrlPsi x z :=
    weakOnePoint_psiM hN0 hη hImm (by linarith only [hIm169, hLam0])
  obtain ⟨hΨ2s, hΨ1, hLΨ⟩ := weakOnePoint_psi hL150 hu hα2
  rw [← hΨdef] at hΨ2s hΨ1 hLΨ
  have hΨ0 : 0 ≤ ctrlPsi x z := by rw [hΨdef]; positivity
  have hΨm0 : 0 ≤ ctrlPsiM x z := by unfold ctrlPsiM; positivity
  have hL0 : 0 ≤ levelFL ϑ⁻¹ C₀ K N := by linarith only [hL150]
  -- (5.3), by (S5) of Lemma 4.6
  obtain ⟨-, -, hS5, -⟩ := goodEvent_level M hM hϑ hϑ1 hC₀ hN hη hκ
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN2
  have hΨm2 : ctrlPsiM x z ^ 2 ≤ (14 * ctrlPsi x z) ^ 2 := pow_le_pow_left₀ hΨm0 hΨm 2
  have hXA : ∀ i, ‖selfX (toMatrix x) M.varMatrix z i‖ ≤
        14 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
      ‖selfA (toMatrix x) M.varMatrix z i‖ ≤ 245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2 := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨h1, h2, -⟩ := hS5 x hx i j hj.symm
    refine ⟨?_, ?_⟩
    · calc ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z := h1
        _ ≤ levelFL ϑ⁻¹ C₀ K N * (14 * ctrlPsi x z) := mul_le_mul_of_nonneg_left hΨm hL0
        _ = 14 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z := by ring
    · calc ‖selfA (toMatrix x) M.varMatrix z i‖
          ≤ levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 := h2
        _ ≤ levelFL ϑ⁻¹ C₀ K N * (5 / 4) * (14 * ctrlPsi x z) ^ 2 := by
          gcongr
          exact (hG i).2
        _ = 245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2 := by ring
  have hLOb : LamO x z ≤ 35 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z := by
    refine Real.iSup_le (fun q => ?_) (by positivity)
    obtain ⟨⟨i, j⟩, hij⟩ := q
    obtain ⟨-, -, h3⟩ := hS5 x hx i j hij
    calc ‖green (toMatrix x) z i j‖
        ≤ levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ *
            ‖greenT (toMatrix x) {i} z j j‖ * ctrlPsiM x z := h3
      _ ≤ levelFL ϑ⁻¹ C₀ K N * (5 / 4) * 2 * (14 * ctrlPsi x z) := by
          gcongr
          · exact (hG i).2
          · exact hGT i j hij
      _ = 35 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z := by ring
  have hΨsq : ctrlPsi x z ^ 2 ≤ ctrlPsi x z := by nlinarith only [hΨ0, hΨ1]
  have hUps : ∀ i, ‖selfUps (toMatrix x) M.varMatrix z i‖ ≤
      259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z := by
    intro i
    obtain ⟨h1, h2⟩ := hXA i
    have h3 : ‖selfUps (toMatrix x) M.varMatrix z i‖ ≤
        ‖selfA (toMatrix x) M.varMatrix z i‖ + ‖selfX (toMatrix x) M.varMatrix z i‖ :=
      norm_add_le _ _
    have h4 : levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2 ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z :=
      mul_le_mul_of_nonneg_left hΨsq hL0
    linarith only [h1, h2, h3, h4]
  have hUpsMax : (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
      259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z :=
    Real.iSup_le hUps (by positivity)
  have hUps0 : 0 ≤ ⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  -- (5.5)
  have hDb : (⨆ i, ‖green (toMatrix x) z i i - msc z -
      (stieltjesEmp (toMatrix x) z - msc z)‖) ≤
        1036 * stabCs C₀ δm δp * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z +
          144 * stabCs C₀ δm δp * Lam x z ^ 2 := by
    have h1 : 4 * stabCs C₀ δm δp * (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
        4 * stabCs C₀ δm δp * (259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z) :=
      mul_le_mul_of_nonneg_left hUpsMax (by positivity)
    have h2 := hD
    change _ ≤ 4 * stabCs C₀ δm δp * (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) +
      144 * stabCs C₀ δm δp * Lam x z ^ 2 at h2
    have e : 4 * stabCs C₀ δm δp * (259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z) =
        1036 * stabCs C₀ δm δp * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z := by ring
    linarith only [h1, h2, e]
  -- (5.4) and (5.2′)
  have hXavg : ‖(N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i‖ ≤
      14 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z :=
    weakOnePoint_avg_le hN0 fun i => (hXA i).1
  have hUavg : ‖(N : ℂ)⁻¹ * ∑ i, selfUps (toMatrix x) M.varMatrix z i‖ ≤
      ‖(N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i‖ +
        245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2 := by
    have hAavg : ‖(N : ℂ)⁻¹ * ∑ i, selfA (toMatrix x) M.varMatrix z i‖ ≤
        245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2 :=
      weakOnePoint_avg_le hN0 fun i => (hXA i).2
    have e : (N : ℂ)⁻¹ * ∑ i, selfUps (toMatrix x) M.varMatrix z i =
        (N : ℂ)⁻¹ * ∑ i, selfA (toMatrix x) M.varMatrix z i +
          (N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i := by
      simp only [selfUps, Finset.sum_add_distrib, mul_add]
    rw [e]
    have := norm_add_le ((N : ℂ)⁻¹ * ∑ i, selfA (toMatrix x) M.varMatrix z i)
      ((N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i)
    linarith only [this, hAavg]
  have hUsq : (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ^ 2 ≤
      (259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z) ^ 2 :=
    pow_le_pow_left₀ hUps0 hUpsMax 2
  have hcube : (90 + 72 * stabCs C₀ δm δp) * Lam x z ^ 3 ≤ 3 / 10 * Lam x z ^ 2 := by
    have h1 : (90 + 72 * stabCs C₀ δm δp) * Lam x z ≤
        162 * (stabCs C₀ δm δp * lamSt C₀ δm δp) := by
      nlinarith only [hCs1, hLam, hLam0]
    rw [hlamCs] at h1
    have h2 : 0 ≤ Lam x z ^ 2 := sq_nonneg _
    have e : (90 + 72 * stabCs C₀ δm δp) * Lam x z ^ 3 =
        ((90 + 72 * stabCs C₀ δm δp) * Lam x z) * Lam x z ^ 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right h1 h2
    linarith only [this, h2]
  have hkey : ‖(stieltjesEmp (toMatrix x) z - msc z) ^ 2 -
      msc z * (1 - msc z ^ 2) * (stieltjesEmp (toMatrix x) z - msc z)‖ ≤
        ‖(N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i‖ +
          245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2 +
          40 * stabCs C₀ δm δp ^ 2 * (259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z) ^ 2 +
          3 / 10 * Lam x z ^ 2 := by
    have h0 := hquad
    change _ ≤ ‖(N : ℂ)⁻¹ * ∑ i, selfUps (toMatrix x) M.varMatrix z i‖ +
      40 * stabCs C₀ δm δp ^ 2 * (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ^ 2 +
      (90 + 72 * stabCs C₀ δm δp) * Lam x z ^ 3 at h0
    have h1 : 40 * stabCs C₀ δm δp ^ 2 * (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ^ 2 ≤
        40 * stabCs C₀ δm δp ^ 2 * (259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z) ^ 2 :=
      mul_le_mul_of_nonneg_left hUsq (by positivity)
    linarith only [h0, h1, hUavg, hcube]
  have hΨ2 : ctrlPsi x z ^ 2 ≤
      2 * (((msc z).im + Lam x z) / (N * z.im) + 1 / (N * z.im) ^ 2) := by
    have hu0 : (0 : ℝ) < N * z.im := by
      have : (0 : ℝ) < N := by exact_mod_cast hN0
      positivity
    have := weakOnePoint_psi_sq hu0 hα0
    rw [← hΨdef] at this
    linarith only [this]
  obtain ⟨hq1, hq2⟩ := weakOnePoint_alg (by linarith only [hL150]) hCs1 hΨ0 hΨ1 hLΨ hΨ2
    hXavg hkey
  have hE0 : aprioriE0 ϑ⁻¹ C₀ δm δp K N =
      6 * 10 ^ 6 * stabCs C₀ δm δp ^ 2 * levelFL ϑ⁻¹ C₀ K N ^ 2 := rfl
  have hCa : aprioriCa C₀ δm δp = 3 * 10 ^ 6 * stabCs C₀ δm δp ^ 2 := rfl
  refine ⟨hG, hGT, hΨm, hΨ1, hLOb, hXA, hUpsMax, ?_, hDb, hLDle, hΨ2s, hLΨ, ?_⟩
  · rw [hE0]; exact hq1
  · rw [hCa]; exact hq2

/-- Lemma 5.1: bounds under the a priori assumption, near regime, with the explicit constants
of (5.2)–(5.5) and (5.2′), together with `1 ≤ 𝔈₀ ≤ K^{8a+7}`. Here `w = m - m_sc`,
`w₀ = m_sc (1 - m_sc²)`, `D = maxᵢ |Gᵢᵢ - m_sc - w|`, `Υ_max = maxᵢ |Υᵢ|`, `Ψ` is (5.1) and
`Ψ_m` is (4.10). -/
theorem apriori_bounds {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδp : 0 < δp) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      1 ≤ aprioriE0 ϑ⁻¹ C₀ δm δp K N ∧ aprioriE0 ϑ⁻¹ C₀ δm δp K N ≤ K ^ (8 * ϑ⁻¹ + 7) ∧
      ∀ z ∈ Dnear ϑ⁻¹ K N, ∀ x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z,
        LamD x z + LamO x z ≤ lamSt C₀ δm δp →
        (∀ i, 3 / 52 ≤ ‖green (toMatrix x) z i i‖ ∧ ‖green (toMatrix x) z i i‖ ≤ 5 / 4) ∧
        (∀ i j, i ≠ j → ‖greenT (toMatrix x) {i} z j j‖ ≤ 2) ∧
        ctrlPsiM x z ≤ 14 * ctrlPsi x z ∧ ctrlPsi x z ≤ 1 ∧
        LamO x z ≤ 35 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
        (∀ i, ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ 14 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
          ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
            245 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ^ 2) ∧
        (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
          259 * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ∧
        ‖(stieltjesEmp (toMatrix x) z - msc z) ^ 2 -
            msc z * (1 - msc z ^ 2) * (stieltjesEmp (toMatrix x) z - msc z)‖ ≤
          ‖(N : ℂ)⁻¹ * ∑ i, selfX (toMatrix x) M.varMatrix z i‖ +
            aprioriE0 ϑ⁻¹ C₀ δm δp K N *
              (((msc z).im + Lam x z) / (N * z.im) + 1 / (N * z.im) ^ 2) +
            3 / 4 * Lam x z ^ 2 ∧
        (⨆ i, ‖green (toMatrix x) z i i - msc z - (stieltjesEmp (toMatrix x) z - msc z)‖) ≤
          1036 * stabCs C₀ δm δp * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z +
            144 * stabCs C₀ δm δp * Lam x z ^ 2 ∧
        LamD x z ≤ Lam x z +
          ⨆ i, ‖green (toMatrix x) z i i - msc z - (stieltjesEmp (toMatrix x) z - msc z)‖ ∧
        ctrlPsi x z ≤ 2 / Real.sqrt (N * z.im) ∧ levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z ≤ 1 ∧
        ‖(stieltjesEmp (toMatrix x) z - msc z) ^ 2 -
            msc z * (1 - msc z ^ 2) * (stieltjesEmp (toMatrix x) z - msc z)‖ ≤
          aprioriCa C₀ δm δp * levelFL ϑ⁻¹ C₀ K N * ctrlPsi x z + 3 / 10 * Lam x z ^ 2 := by
  have hCs1 : 1 ≤ stabCs C₀ δm δp :=
    le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) (lt_min hδm hδp).le)
  obtain ⟨N₀, hN₀⟩ := standing_ineq hϑ hϑ1 hC₀ (6 * 10 ^ 6 * stabCs C₀ δm δp ^ 2)
  refine ⟨N₀, fun N hN M hM K hK1 hK2 => ?_⟩
  obtain ⟨⟨hK₀, hN13, -, hκ⟩, ⟨hL150, hLK, -, -⟩, -, -⟩ := hN₀ N hN K hK1 hK2
  have hCs2 : 1 ≤ stabCs C₀ δm δp ^ 2 := one_le_pow₀ hCs1
  have hK : 6 * 10 ^ 6 ≤ K := by nlinarith
  have hKpos : 0 < K := by linarith
  have hK1' : 1 ≤ K := by linarith
  have hL0 : 0 ≤ levelFL ϑ⁻¹ C₀ K N := by linarith
  have hLsq : levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ K ^ (8 * ϑ⁻¹ + 6) := by
    calc levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ (K ^ (4 * ϑ⁻¹ + 3)) ^ 2 := pow_le_pow_left₀ hL0 hLK 2
      _ = K ^ (8 * ϑ⁻¹ + 6) := by
        rw [sq, ← Real.rpow_add hKpos]
        congr 1
        ring
  have hE0 : aprioriE0 ϑ⁻¹ C₀ δm δp K N =
      6 * 10 ^ 6 * stabCs C₀ δm δp ^ 2 * levelFL ϑ⁻¹ C₀ K N ^ 2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hE0]
    nlinarith
  · rw [hE0, show 8 * ϑ⁻¹ + 7 = 1 + (8 * ϑ⁻¹ + 6) by ring, Real.rpow_add hKpos, Real.rpow_one]
    exact mul_le_mul hK₀ hLsq (sq_nonneg _) hKpos.le
  · intro z hz x hx hs
    obtain ⟨hE, hη1, hη'⟩ := hz
    have hNr : (0 : ℝ) < N := by
      have : 0 < N := by omega
      exact_mod_cast this
    have hKC : 0 < K ^ (ledgerC1 ϑ⁻¹ - 1) := Real.rpow_pos_of_pos hKpos _
    have hη : 0 < z.im := lt_of_lt_of_le (div_pos hKC hNr) hη1
    have hu1 : K ^ (ledgerC1 ϑ⁻¹ - 1) ≤ N * z.im := by
      rw [div_le_iff₀ hNr, mul_comm] at hη1
      exact hη1
    have hu : 4 * levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ N * z.im := by
      have e1 : K ^ (ledgerC1 ϑ⁻¹ - 1) = K ^ (10 * ϑ⁻¹ + 13) * K ^ (8 * ϑ⁻¹ + 6) := by
        rw [← Real.rpow_add hKpos]
        unfold ledgerC1
        congr 1
        ring
      have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
      have e2 : K ≤ K ^ (10 * ϑ⁻¹ + 13) := by
        conv_lhs => rw [← Real.rpow_one K]
        exact Real.rpow_le_rpow_of_exponent_le hK1' (by linarith)
      have e3 : 0 ≤ K ^ (8 * ϑ⁻¹ + 6) := (Real.rpow_pos_of_pos hKpos _).le
      have e4 : 4 * K ^ (8 * ϑ⁻¹ + 6) ≤ K ^ (10 * ϑ⁻¹ + 13) * K ^ (8 * ϑ⁻¹ + 6) :=
        mul_le_mul_of_nonneg_right (by linarith) e3
      linarith
    exact weakOnePoint_point M hM hϑ hϑ1 hδm hδp hC₀ hN13 hκ hL150 hE hη hη' hu hx hs

end Rigidity
