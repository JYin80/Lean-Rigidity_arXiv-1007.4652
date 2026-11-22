module

public import Rigidity.Fluctuation.Lattice
public import Rigidity.Strong.Helpers

@[expose] public section

/-!
# The averaged law, far regime (NP v1.1, §7.3: Proposition 7.4)

Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `𝒢^f(z)`: the points of `𝒢_col(z)` at which the far-regime bound of Proposition 7.4
holds. -/
def strongGf {N : ℕ} (M : Ensemble 𝕜 N) (a C₀ K : ℝ) (z : ℂ) : Set (Pair N → 𝕜) :=
  goodCol M a C₀ K z ∩
    {x | Lam x z ≤ K ^ (ledgerB a + 2) * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N)}

/-! The proof of Proposition 7.4 follows its three steps. Step 1 (`farPass_point`) is the
deterministic bound (7.f) on `𝒢_col(z)`, from Theorem 5.5 (b), Lemma 4.6 (S5) and Lemma 3.12.
Step 2 bounds `Y_f = ‖Λ 1_{𝒢_col(z)}‖_p` at `p = p₂` by Corollary 6.2, (T5) and (T6), absorbing
the term with `Y_f` (finite because `Λ ≤ 2N`). Step 3 is Markov's inequality. -/

/-! ### 1. Continuity and elementary bounds -/

/-- For `Im z > 0`, the diagonal resolvent entries `x ↦ G_kk(z)` are continuous. -/
private lemma farPass_continuous_green {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im)
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
private lemma farPass_stieltjes_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (z : ℂ) :
    stieltjesEmp A z = (N : ℂ)⁻¹ * ∑ i, green A z i i := by
  simp only [stieltjesEmp, Fintype.card_fin, Matrix.trace, Matrix.diag]

/-- For `Im z > 0`, `x ↦ m(z)` is continuous. -/
private lemma farPass_continuous_stieltjes {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun x : Pair N → 𝕜 => stieltjesEmp (toMatrix x) z := by
  simp only [farPass_stieltjes_eq]
  exact continuous_const.mul (continuous_finsetSum _ fun k _ => farPass_continuous_green M hz k)

/-- For `Im z > 0`, `x ↦ Λ(z)` is continuous. -/
private lemma farPass_continuous_Lam {N : ℕ} (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun x : Pair N → 𝕜 => Lam x z :=
  ((farPass_continuous_stieltjes M hz).sub continuous_const).norm

/-- The modulus of an average is at most a uniform bound on the moduli of the terms. -/
private lemma farPass_avg_le {N : ℕ} (hN : 0 < N) {f : Fin N → ℂ} {c : ℝ}
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

/-- The crude bound `Λ ≤ η⁻¹ + 1`. -/
private lemma farPass_Lam_le {N : ℕ} (hN : 0 < N) (x : Pair N → 𝕜) {z : ℂ} (hz : 0 < z.im) :
    Lam x z ≤ 1 / z.im + 1 := by
  have h1 : ‖stieltjesEmp (toMatrix x) z‖ ≤ 1 / z.im := by
    rw [farPass_stieltjes_eq]
    exact farPass_avg_le hN fun i => norm_green_apply_le (toMatrix_isHermitian x) hz i i
  have h2 := (norm_msc_lt_one hz).le
  unfold Lam
  linarith [norm_sub_le (stieltjesEmp (toMatrix x) z) (msc z)]

/-- If `‖f‖ ≤ a ‖h‖ + c` pointwise, then `‖f‖_p ≤ a ‖h‖_p + c` for `p ≥ 1` and a probability
measure. -/
private lemma farPass_eLpNorm_le {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
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

/-! ### 2. Step 1: the pointwise bound (7.f) -/

/-- The control parameter `Ψ_m = √(Im m/u) + 1/u + 1/√N` in the far regime, with `u = Nη`:
`Ψ_m² ≤ 3 (Im m_sc/u + 1/u² + 1/N + Λ/u)` when `Im m ≤ Im m_sc + Λ`, and `𝔏 Ψ_m ≤ 1/8`,
`Ψ_m ≤ 1` when moreover `Im m ≤ 1/2`, `η ≤ 10`, `√N = Q⁸ ≤ 2u`, `Q ≥ 8`, `𝔏 ≥ 150` and
`𝔏² ≤ Q`. -/
private lemma farPass_psi {n s u η m mc Λ L Q : ℝ} (hn : 0 < n) (hs2 : s ^ 2 = n)
    (hs0 : 0 < s) (hu : u = n * η) (hη10 : η ≤ 10) (hQ : 8 ≤ Q) (hQs : s = Q ^ 8)
    (hus : s / 2 ≤ u) (hm1 : m ≤ 1 / 2) (hmΛ : m ≤ mc + Λ) (hmc : 0 ≤ mc) (hΛ : 0 ≤ Λ)
    (hL : 150 ≤ L) (hLQ : L ^ 2 ≤ Q) :
    (Real.sqrt (m / u) + 1 / u + 1 / s) ^ 2 ≤ 3 * (mc / u + 1 / u ^ 2 + 1 / n + Λ / u) ∧
      L * (Real.sqrt (m / u) + 1 / u + 1 / s) ≤ 1 / 8 ∧
      Real.sqrt (m / u) + 1 / u + 1 / s ≤ 1 ∧ 0 ≤ Real.sqrt (m / u) + 1 / u + 1 / s := by
  have hQ7 : 2097152 ≤ Q ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hQ 7
    norm_num at this
    linarith
  have hQ0 : 0 < Q := by linarith
  have hs1 : 8 ≤ s := by
    rw [hQs]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hQ 8]
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  set a₁ := Real.sqrt (m / u) with ha₁
  have ha₁0 : 0 ≤ a₁ := Real.sqrt_nonneg _
  have hsq : ∀ {t : ℝ}, 0 ≤ t → m ≤ t → a₁ ^ 2 ≤ t / u := by
    intro t ht h
    have h1 : a₁ ≤ Real.sqrt (t / u) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h hu0.le)
    calc a₁ ^ 2 ≤ Real.sqrt (t / u) ^ 2 := pow_le_pow_left₀ ha₁0 h1 2
      _ = t / u := Real.sq_sqrt (by positivity)
  have hN1 : (1 / s) ^ 2 = 1 / n := by rw [div_pow, hs2, one_pow]
  have hu2 : (1 / u) ^ 2 = 1 / u ^ 2 := by rw [div_pow, one_pow]
  have hΨ3 : (a₁ + 1 / u + 1 / s) ^ 2 ≤ 3 * (a₁ ^ 2 + (1 / u) ^ 2 + (1 / s) ^ 2) := by
    nlinarith [sq_nonneg (a₁ - 1 / u), sq_nonneg (a₁ - 1 / s), sq_nonneg (1 / u - 1 / s)]
  rw [hN1, hu2] at hΨ3
  have hΨ0 : 0 ≤ a₁ + 1 / u + 1 / s := by positivity
  refine ⟨?_, ?_, ?_, hΨ0⟩
  · have h := hsq (by positivity) hmΛ
    have e : (mc + Λ) / u = mc / u + Λ / u := add_div _ _ _
    linarith
  all_goals
    have h := hsq (by norm_num) hm1
    have e1 : 1 / u ^ 2 ≤ 1 / u := one_div_le_one_div_of_le hu0 (by nlinarith)
    have e2 : 1 / n ≤ 10 / u := by
      rw [div_le_div_iff₀ hn hu0, hu]
      nlinarith [mul_le_mul_of_nonneg_left hη10 hn.le]
    have hΨb : (a₁ + 1 / u + 1 / s) ^ 2 * u ≤ 35 := by
      have : (a₁ + 1 / u + 1 / s) ^ 2 ≤ 35 / u := by
        calc (a₁ + 1 / u + 1 / s) ^ 2 ≤ 3 * (1 / 2 / u + 1 / u + 10 / u) := by linarith
          _ = (69 / 2) / u := by ring
          _ ≤ 35 / u := by gcongr; norm_num
      exact (le_div_iff₀ hu0).1 this
    have hLΨ : L * (a₁ + 1 / u + 1 / s) ≤ 1 / 8 := by
      set Ψ := a₁ + 1 / u + 1 / s
      have e3 : Ψ ^ 2 * Q ^ 8 ≤ 70 := by
        have : Ψ ^ 2 * Q ^ 8 ≤ Ψ ^ 2 * (2 * u) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        linarith
      have h1 : (L * Ψ) ^ 2 * Q ^ 8 ≤ 70 * Q := by
        calc (L * Ψ) ^ 2 * Q ^ 8 = L ^ 2 * (Ψ ^ 2 * Q ^ 8) := by ring
          _ ≤ Q * 70 := mul_le_mul hLQ e3 (by positivity) hQ0.le
          _ = 70 * Q := by ring
      have h2 : (L * Ψ) ^ 2 * 2097152 ≤ 70 := by
        have e4 : (L * Ψ) ^ 2 * Q ^ 8 = Q * ((L * Ψ) ^ 2 * Q ^ 7) := by ring
        rw [e4] at h1
        have h5 : (L * Ψ) ^ 2 * Q ^ 7 ≤ 70 := le_of_mul_le_mul_left (by linarith) hQ0
        have h6 : (L * Ψ) ^ 2 * 2097152 ≤ (L * Ψ) ^ 2 * Q ^ 7 :=
          mul_le_mul_of_nonneg_left hQ7 (sq_nonneg _)
        linarith
      have h7 : (L * Ψ) ^ 2 ≤ (1 / 8) ^ 2 := by norm_num; linarith
      exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) h7
  · exact hLΨ
  · have := mul_le_mul_of_nonneg_right hL hΨ0
    linarith

/-- The arithmetic of Step 1: from the bounds of Lemma 3.12, (S5) and `Ψ_m² ≤ 3 (S + Λ/u)`,
`Λ ≤ |⟨X⟩|/4 + 2 𝔈₀' S` with `𝔈₀' = 3 (E_max + 14) 𝔏² ≤ u/2`. -/
private lemma farPass_arith {Λ X U Ld Υ w L Ψ E S u : ℝ}
    (hLm : Λ ≤ U / 8 + 9 / 8 * Ld ^ 2 * w) (hU : U ≤ X + L * Ψ ^ 2 / 2) (hLd : Ld ≤ Υ / 2)
    (hLd0 : 0 ≤ Ld) (hΥ : Υ ≤ 3 / 2 * (L * Ψ)) (hw : w ≤ E + 12 + 3 / 16) (hw0 : 0 ≤ w)
    (hL : 150 ≤ L) (hE1 : 1 ≤ E) (hΨa : Ψ ^ 2 ≤ 3 * (S + Λ / u))
    (hDu : 3 * (E + 14) * L ^ 2 ≤ u / 2) (hu0 : 0 < u) (hΛ : 0 ≤ Λ) :
    Λ ≤ X / 4 + 2 * (3 * (E + 14) * L ^ 2) * S := by
  have hL0 : 0 ≤ L := by linarith
  have hP0 : 0 ≤ L ^ 2 * Ψ ^ 2 := by positivity
  have hLd2 : Ld ^ 2 ≤ 9 / 16 * (L ^ 2 * Ψ ^ 2) := by
    have : Ld ≤ 3 / 4 * (L * Ψ) := by linarith
    calc Ld ^ 2 ≤ (3 / 4 * (L * Ψ)) ^ 2 := pow_le_pow_left₀ hLd0 this 2
      _ = 9 / 16 * (L ^ 2 * Ψ ^ 2) := by ring
  have h1 : 9 / 8 * Ld ^ 2 * w ≤ 9 / 8 * (9 / 16 * (L ^ 2 * Ψ ^ 2)) * (E + 12 + 3 / 16) :=
    mul_le_mul (by linarith) hw hw0 (by positivity)
  have h2 : L * Ψ ^ 2 ≤ L ^ 2 * Ψ ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hE0 : 0 ≤ E := by linarith
  have hstep : Λ ≤ X / 8 + (E + 14) * (L ^ 2 * Ψ ^ 2) := by
    nlinarith [mul_nonneg hE0 hP0]
  have hEL : 0 ≤ (E + 14) * L ^ 2 := by positivity
  have h3 : (E + 14) * (L ^ 2 * Ψ ^ 2) ≤ 3 * (E + 14) * L ^ 2 * S +
      3 * (E + 14) * L ^ 2 * (Λ / u) := by
    have := mul_le_mul_of_nonneg_left hΨa hEL
    nlinarith
  have h4 : 3 * (E + 14) * L ^ 2 * (Λ / u) ≤ Λ / 2 := by
    calc 3 * (E + 14) * L ^ 2 * (Λ / u) ≤ u / 2 * (Λ / u) :=
          mul_le_mul_of_nonneg_right hDu (by positivity)
      _ = Λ / 2 := by field_simp
  linarith

/-- Step 1 of the proof of Proposition 7.4, (7.f): at a point of `𝒢(z)` with `z ∈ 𝐃^far` and
`max |G_ii| ≤ 1/2`,
`Λ ≤ |⟨X⟩|/4 + 2 𝔈₀' (Im m_sc/(Nη) + 1/(Nη)² + 1/N)` with `𝔈₀' = 3 (E_max + 14) 𝔏²`, given
`N ≥ 13`, `κ_ϑ + 3 log N ≤ K²`, `𝔏 ≥ 150`, `E_max ≥ 1` and `Q ≥ 8` with `√N = Q⁸`,
`𝔈₀' ≤ Q`. -/
private lemma farPass_point {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ K Q : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hC₀ : 1 ≤ C₀) (hN : 13 ≤ N)
    (hκ : kappaTheta ϑ⁻¹ + 3 * Real.log N ≤ K ^ 2) (hQ : 8 ≤ Q) (hQN : Real.sqrt N = Q ^ 8)
    (hL150 : 150 ≤ levelFL ϑ⁻¹ C₀ K N) (hE1 : 1 ≤ levelEmax ϑ⁻¹ C₀ K N)
    (hDQ : 3 * (levelEmax ϑ⁻¹ C₀ K N + 14) * levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ Q)
    {z : ℂ} (hz : z ∈ Dfar ϑ⁻¹ C₀ K N) {x : Pair N → 𝕜} (hx : x ∈ goodEvent M ϑ⁻¹ (K ^ 2) z)
    (hG : ∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 / 2) :
    Lam x z ≤ ‖(N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k‖ / 4 +
      2 * (3 * (levelEmax ϑ⁻¹ C₀ K N + 14) * levelFL ϑ⁻¹ C₀ K N ^ 2) *
        ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N) := by
  have hN0 : 0 < N := by omega
  have : Nonempty (Fin N) := ⟨⟨0, hN0⟩⟩
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨hE4, hEz, hη1, hη10⟩ := hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
  have hη : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  have hus : Real.sqrt N / 2 ≤ N * z.im := by
    have e : (N : ℝ) * (1 / (2 * Real.sqrt N)) = Real.sqrt N / 2 := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by norm_num)]
      nlinarith [hs2]
    rw [← e]
    gcongr
  have hu0 : 0 < (N : ℝ) * z.im := by positivity
  have hL0 : 0 ≤ levelFL ϑ⁻¹ C₀ K N := by linarith
  have hLQ : levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ Q :=
    le_trans (le_mul_of_one_le_left (sq_nonneg _) (by linarith)) hDQ
  -- `Im m ≤ 1/2` and `Im m ≤ Im m_sc + Λ`
  have hIm : (stieltjesEmp (toMatrix x) z).im ≤ 1 / 2 := by
    have h := farPass_avg_le hN0 hG
    rw [← farPass_stieltjes_eq] at h
    exact (Complex.im_le_norm _).trans h
  have hImΛ : (stieltjesEmp (toMatrix x) z).im ≤ (msc z).im + Lam x z := by
    have h := Complex.im_le_norm (stieltjesEmp (toMatrix x) z - msc z)
    rw [Complex.sub_im] at h
    have : ‖stieltjesEmp (toMatrix x) z - msc z‖ = Lam x z := rfl
    linarith
  obtain ⟨hΨa, hLΨ, hΨ1, hΨ0⟩ := farPass_psi hNr hs2 hs0 rfl hη10 hQ hQN hus hIm hImΛ
    (msc_im_pos hη).le (norm_nonneg _) hL150 hLQ
  have hΨe : ctrlPsiM x z = Real.sqrt ((stieltjesEmp (toMatrix x) z).im / (N * z.im)) +
      1 / (N * z.im) + 1 / Real.sqrt N := rfl
  rw [← hΨe] at hΨa hLΨ hΨ1 hΨ0
  -- (S5): `|X_i| ≤ 𝔏 Ψ_m`, `|A_i| ≤ 𝔏 |G_ii| Ψ_m²`
  obtain ⟨-, -, hS5, -⟩ := goodEvent_level M hM hϑ hϑ1 hC₀ hN hη hκ
  have hXi : ∀ i, ‖selfX (toMatrix x) M.varMatrix z i‖ ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z :=
    fun i => by
      obtain ⟨j, hj⟩ := exists_ne i
      exact (hS5 x hx i j hj.symm).1
  have hAi : ∀ i, ‖selfA (toMatrix x) M.varMatrix z i‖ ≤
      levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ^ 2 / 2 := fun i => by
    obtain ⟨j, hj⟩ := exists_ne i
    have h := (hS5 x hx i j hj.symm).2.1
    have : levelFL ϑ⁻¹ C₀ K N * ‖green (toMatrix x) z i i‖ * ctrlPsiM x z ^ 2 ≤
        levelFL ϑ⁻¹ C₀ K N * (1 / 2) * ctrlPsiM x z ^ 2 := by
      gcongr
      exact hG i
    linarith
  -- `Υ_max ≤ (3/2) 𝔏 Ψ_m`
  have hUi : ∀ i, ‖selfUps (toMatrix x) M.varMatrix z i‖ ≤
      3 / 2 * (levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z) := fun i => by
    have h := norm_add_le (selfA (toMatrix x) M.varMatrix z i) (selfX (toMatrix x) M.varMatrix z i)
    have h1 : levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ^ 2 ≤ levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z :=
      mul_le_mul_of_nonneg_left (by nlinarith) hL0
    have : selfUps (toMatrix x) M.varMatrix z i =
        selfA (toMatrix x) M.varMatrix z i + selfX (toMatrix x) M.varMatrix z i := rfl
    rw [this]
    linarith [hXi i, hAi i]
  have hΥ : (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
      3 / 2 * (levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z) := ciSup_le hUi
  have hΥ0 : 0 ≤ ⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖ :=
    (norm_nonneg _).trans (le_ciSup (f := fun i => ‖selfUps (toMatrix x) M.varMatrix z i‖)
      (Set.finite_range _).bddAbove ⟨0, hN0⟩)
  -- Lemma 3.12
  have hV := hM.varProfile
  have hrow : ∀ i, ∑ j, M.varMatrix i j = 1 := fun i => by
    rw [← hV.sumA i]
    exact Finset.sum_congr rfl fun j _ => (hV.symm.apply i j).symm
  have hG1 : ∀ i, ‖green (toMatrix x) z i i‖ ≤ 1 := fun i => (hG i).trans (by norm_num)
  obtain ⟨hD1, hD2, -⟩ :=
    stab_far hN0 (toMatrix_isHermitian x) hrow hV.sumA hV.nonneg hE4 hη hG1
  have hLd0 : 0 ≤ LamDM (toMatrix x) z :=
    (norm_nonneg _).trans (le_ciSup (f := fun k : Fin N => ‖green (toMatrix x) z k k - msc z‖)
      (Set.finite_range _).bddAbove ⟨0, hN0⟩)
  -- `|⟨Υ⟩| ≤ |⟨X⟩| + 𝔏 Ψ_m²/2`
  have hUavg : ‖(N : ℂ)⁻¹ * ∑ i, selfUps (toMatrix x) M.varMatrix z i‖ ≤
      ‖(N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k‖ +
        levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z ^ 2 / 2 := by
    have e : (N : ℂ)⁻¹ * ∑ i, selfUps (toMatrix x) M.varMatrix z i =
        (N : ℂ)⁻¹ * ∑ i, selfA (toMatrix x) M.varMatrix z i +
          (N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k := by
      simp only [selfUps, Finset.sum_add_distrib, mul_add]
    rw [e]
    have := farPass_avg_le hN0 hAi
    linarith [norm_add_le ((N : ℂ)⁻¹ * ∑ i, selfA (toMatrix x) M.varMatrix z i)
      ((N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k)]
  -- `|z| + 1 + Υ_max ≤ E_max + 12 + 3/16`
  have hLΨ' : 3 / 2 * (levelFL ϑ⁻¹ C₀ K N * ctrlPsiM x z) ≤ 3 / 16 := by linarith
  have hzn : ‖z‖ + 1 + (⨆ i, ‖selfUps (toMatrix x) M.varMatrix z i‖) ≤
      levelEmax ϑ⁻¹ C₀ K N + 12 + 3 / 16 := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hη] at h
    linarith
  -- the absorption `𝔈₀'/u ≤ 1/2`
  have hDu : 3 * (levelEmax ϑ⁻¹ C₀ K N + 14) * levelFL ϑ⁻¹ C₀ K N ^ 2 ≤ N * z.im / 2 := by
    have hQ8 : Q ≤ Q ^ 8 / 4 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hQ 7]
    rw [hQN] at hus
    linarith
  exact farPass_arith hD2 hUavg hD1 hLd0 hΥ hzn (by positivity) hL150 hE1 hΨa hDu hu0
    (norm_nonneg _)

/-! ### 3. Steps 2 and 3: absorption and Markov's inequality -/

/-- The absorption of Step 2: from `Y ≤ ‖⟨X⟩‖_p/4 + c₁`, `‖⟨X⟩‖_p ≤ 𝔉 ‖Φ_*²‖_p + N⁻⁸`,
`‖Φ_*²‖_p ≤ ‖Λ‖_p/u + c₂`, `‖Λ‖_p ≤ Y + N⁻⁸`, `Y < ∞` and `𝔉 ≤ u`, one gets
`Y ≤ (2/3) N⁻⁸ + 𝔉 c₂/3 + (4/3) c₁`. -/
private lemma farPass_absorb {Y Xn Φn Λn : ℝ≥0∞} {F u n8 c₁ c₂ : ℝ}
    (h1 : Y ≤ ENNReal.ofReal (1 / 4) * Xn + ENNReal.ofReal c₁)
    (h2 : Xn ≤ ENNReal.ofReal F * Φn + ENNReal.ofReal n8)
    (h3 : Φn ≤ ENNReal.ofReal (1 / u) * Λn + ENNReal.ofReal c₂)
    (h4 : Λn ≤ Y + ENNReal.ofReal n8) (hY : Y ≠ ⊤) (hF : 0 ≤ F) (hu : 0 < u) (hFu : F ≤ u)
    (hn8 : 0 ≤ n8) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    Y.toReal ≤ 2 / 3 * n8 + 1 / 3 * F * c₂ + 4 / 3 * c₁ := by
  set y := Y.toReal with hy
  have hYe : Y = ENNReal.ofReal y := (ENNReal.ofReal_toReal hY).symm
  have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
  have hu1 : 0 ≤ 1 / u := by positivity
  have hc : ENNReal.ofReal y ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal F *
      (ENNReal.ofReal (1 / u) * (ENNReal.ofReal y + ENNReal.ofReal n8) + ENNReal.ofReal c₂) +
        ENNReal.ofReal n8) + ENNReal.ofReal c₁ := by
    rw [← hYe]
    calc Y ≤ ENNReal.ofReal (1 / 4) * Xn + ENNReal.ofReal c₁ := h1
      _ ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal F * Φn + ENNReal.ofReal n8) +
          ENNReal.ofReal c₁ := by gcongr
      _ ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal F *
          (ENNReal.ofReal (1 / u) * Λn + ENNReal.ofReal c₂) + ENNReal.ofReal n8) +
            ENNReal.ofReal c₁ := by gcongr
      _ ≤ _ := by gcongr
  rw [← ENNReal.ofReal_add hy0 hn8, ← ENNReal.ofReal_mul hu1,
    ← ENNReal.ofReal_add (by positivity) hc₂, ← ENNReal.ofReal_mul hF,
    ← ENNReal.ofReal_add (by positivity) hn8, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) hc₁, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hc
  have hFu' : F * (1 / u) ≤ 1 := by
    rw [mul_one_div, div_le_one hu]
    exact hFu
  have e : F * (1 / u * (y + n8)) ≤ y + n8 := by
    rw [← mul_assoc]
    exact mul_le_of_le_one_left (by positivity) hFu'
  nlinarith

/-- Markov's inequality in the form of Step 3: if `‖f‖_p ≤ B` and `e B ≤ t`, `t > 0`, then
`ℙ(|f| ≥ t) ≤ e^{-p}`. -/
private lemma farPass_markov {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
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

/-- The final constant of Step 2: with `c₂ ≤ (K + 2) S`, `N⁻⁸ ≤ S`, `𝔈₀' ≤ 𝔉`, `1 ≤ 𝔉` and
`K ≥ 1000`, `(2/3) N⁻⁸ + 𝔉 c₂/3 + (8/3) 𝔈₀' S ≤ 𝔉 K S = K^b S`. -/
private lemma farPass_const {n8 F c₂ D S K : ℝ} (hc₂ : c₂ ≤ (K + 2) * S) (hn8 : n8 ≤ S)
    (hD : D ≤ F) (hF : 1 ≤ F) (hK : 1000 ≤ K) (hS : 0 ≤ S) :
    2 / 3 * n8 + 1 / 3 * F * c₂ + 4 / 3 * (2 * D * S) ≤ F * K * S := by
  have h1 : F * c₂ ≤ F * ((K + 2) * S) := mul_le_mul_of_nonneg_left hc₂ (by linarith)
  have h2 : D * S ≤ F * S := mul_le_mul_of_nonneg_right hD hS
  have h3 : 1000 * (F * S) ≤ K * (F * S) := mul_le_mul_of_nonneg_right hK (by positivity)
  have h4 : S ≤ F * S := le_mul_of_one_le_left hS hF
  nlinarith

/-- Step 2 in `L^p` form: if `0 ≤ Λ ≤ C`, `Λ ≤ |X|/4 + c₁` on `G`, `|Φ| ≤ Λ/u + c₂`,
`‖X‖_p ≤ 𝔉 ‖Φ‖_p + n₈`, `C ℙ(Gᶜ)^{1/p} ≤ n₈` and `𝔉 ≤ u`, then `Y = ‖Λ 1_G‖_p` is finite and
`Y ≤ (2/3) n₈ + 𝔉 c₂/3 + (4/3) c₁`. -/
private lemma farPass_moment {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {p : ℕ} (hp : 1 ≤ p) {G : Set α} (hG : MeasurableSet G)
    {Λf Φf : α → ℝ} {Xf : α → ℂ} (hΛm : AEStronglyMeasurable Λf μ)
    (hXm : AEStronglyMeasurable Xf μ) (hΦm : AEStronglyMeasurable Φf μ) {C F u n8 c₁ c₂ : ℝ}
    (hΛ0 : ∀ x, 0 ≤ Λf x) (hΛC : ∀ x, Λf x ≤ C) (hpt : ∀ x ∈ G, Λf x ≤ ‖Xf x‖ / 4 + c₁)
    (hΦ : ∀ x, ‖Φf x‖ ≤ 1 / u * ‖Λf x‖ + c₂)
    (hX : eLpNorm Xf p μ ≤ ENNReal.ofReal F * eLpNorm Φf p μ + ENNReal.ofReal n8)
    (hT6 : ENNReal.ofReal C * μ Gᶜ ^ (1 / (p : ℝ)) ≤ ENNReal.ofReal n8) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hu : 0 < u) (hFu : F ≤ u) (hn8 : 0 ≤ n8) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    eLpNorm (G.indicator Λf) p μ ≠ ⊤ ∧
      (eLpNorm (G.indicator Λf) p μ).toReal ≤ 2 / 3 * n8 + 1 / 3 * F * c₂ + 4 / 3 * c₁ := by
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
  refine ⟨hfin, farPass_absorb (Λn := eLpNorm Λf p μ) ?_ hX ?_ ?_ hfin hF hu hFu hn8 hc₁ hc₂⟩
  · refine farPass_eLpNorm_le hp1 hfm hXm (by norm_num) hc₁ fun x => ?_
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (hΛ0 x)]
      linarith [hpt x hx]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  · exact farPass_eLpNorm_le hp1 hΦm hΛm (by positivity) hc₂ hΦ
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
private lemma farPass_phi_le {N : ℕ} (hN : 0 < N) (x : Pair N → 𝕜) {z : ℂ} (hz : 0 < z.im)
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

/-- The numerical facts on the powers of `K` used in Step 2, for `a ≥ 1`, `K ≥ 1000`,
`𝔏 ≤ K^{4a+3}` and `1 ≤ E_max ≤ K^{2a+1}`: `𝔈₀' = 3 (E_max + 14) 𝔏² ≤ 𝔉 = K^{12a+11}`,
`1 ≤ 𝔉` and `𝔉 K = K^{12a+12}`. -/
private lemma farPass_powers {a K L E : ℝ} (ha : 1 ≤ a) (hK : 1000 ≤ K) (hL0 : 0 ≤ L)
    (hL : L ≤ K ^ (4 * a + 3)) (hE1 : 1 ≤ E) (hE : E ≤ K ^ (2 * a + 1)) :
    3 * (E + 14) * L ^ 2 ≤ K ^ (12 * a + 11) ∧ 1 ≤ K ^ (12 * a + 11) ∧
      K ^ (12 * a + 11) * K = K ^ (12 * a + 12) := by
  have hKpos : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  refine ⟨?_, Real.one_le_rpow hK1 (by linarith), ?_⟩
  · have hL2 : L ^ 2 ≤ K ^ ((4 * a + 3) * (2 : ℕ)) := by
      rw [Real.rpow_mul_natCast hKpos.le]
      exact pow_le_pow_left₀ hL0 hL 2
    have hEL : E * L ^ 2 ≤ K ^ (2 * a + 1 + (4 * a + 3) * (2 : ℕ)) := by
      rw [Real.rpow_add hKpos]
      exact mul_le_mul hE hL2 (sq_nonneg _) (by positivity)
    have h45 : 45 * K ^ (2 * a + 1 + (4 * a + 3) * (2 : ℕ)) ≤
        K ^ (2 * a + 1 + (4 * a + 3) * (2 : ℕ) + 1) := by
      rw [Real.rpow_add_one hKpos.ne', mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hexp : K ^ (2 * a + 1 + (4 * a + 3) * (2 : ℕ) + 1) ≤ K ^ (12 * a + 11) :=
      Real.rpow_le_rpow_of_exponent_le hK1 (by push_cast; linarith)
    have h3 : 3 * (E + 14) * L ^ 2 ≤ 45 * (E * L ^ 2) := by
      have : 0 ≤ L ^ 2 := sq_nonneg _
      nlinarith
    linarith
  · rw [← Real.rpow_add_one hKpos.ne']
    ring_nf

/-- For `N ≥ 2⁴⁸`, `Q = N^{1/16}` satisfies `Q ≥ 8` and `√N = Q⁸`. -/
private lemma farPass_Q {N : ℕ} (hN : 2 ^ 48 ≤ N) :
    8 ≤ (N : ℝ) ^ (1 / 16 : ℝ) ∧ Real.sqrt N = ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 8 := by
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have h48 : ((2 : ℝ) ^ 48) ≤ N := by exact_mod_cast hN
    have e : ((2 : ℝ) ^ 48) ^ (1 / 16 : ℝ) = 8 := by
      rw [show ((2 : ℝ) ^ 48) = 8 ^ 16 by norm_num,
        show (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) h48 (by norm_num)
  · rw [← Real.rpow_mul_natCast hNr, Real.sqrt_eq_rpow]
    norm_num

/-- For `z ∈ 𝐃^far`: `Im z > 0`, `N Im z ≥ √N/2` and the crude bound `Λ ≤ 2N` (`N ≥ 13`). -/
private lemma farPass_far {a C₀ K : ℝ} {N : ℕ} (hN : 13 ≤ N) {z : ℂ} (hz : z ∈ Dfar a C₀ K N) :
    0 < z.im ∧ Real.sqrt N / 2 ≤ N * z.im ∧ ∀ x : Pair N → 𝕜, Lam x z ≤ 2 * N := by
  obtain ⟨-, -, hη1, -⟩ := hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
  have hη : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  refine ⟨hη, ?_, fun x => ?_⟩
  · have e : (N : ℝ) * (1 / (2 * Real.sqrt N)) = Real.sqrt N / 2 := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by norm_num)]
      nlinarith [hs2]
    rw [← e]
    gcongr
  · have h := farPass_Lam_le (by omega) x hη
    have hinv : 1 / z.im ≤ 2 * Real.sqrt N := by
      rw [one_div_le hη (by positivity)]
      exact hη1
    have hs13 : 2 ≤ Real.sqrt N :=
      (Real.le_sqrt (by norm_num) hNr.le).2 (by
        have : (13 : ℝ) ≤ N := by exact_mod_cast hN
        linarith)
    have e1 : 2 * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_right hs13 hs0.le
    have e2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
    linarith

/-! ### 4. Proposition 7.4 -/

/-- Proposition 7.4: at `z ∈ 𝕃 ∩ 𝐃^far`, `𝒢^f(z)` is closed and
`ℙ(𝒢_col(z) ∖ 𝒢^f(z)) ≤ e^{-p₂}`. -/
theorem strong_far {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ →
      ∀ z ∈ lattice ϑ⁻¹ C₀ K N ∩ Dfar ϑ⁻¹ C₀ K N,
        IsClosed (strongGf M ϑ⁻¹ C₀ K z) ∧
        M.prodLaw (goodCol M ϑ⁻¹ C₀ K z \ strongGf M ϑ⁻¹ C₀ K z) ≤
          ENNReal.ofReal (Real.exp (-(levelP2 K : ℝ))) := by
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨Cw, -, N₁, h1⟩ := weakLaw_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₂, h2⟩ := fluctuationAveraging_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₃, h3⟩ := strong_T6 (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨N₄, h4⟩ := standing_ineq hϑ hϑ1 hC₀ 1000
  refine ⟨max (max N₁ N₂) (max N₃ (max N₄ (2 ^ 48))), ?_⟩
  intro N hN M hM K hK1 hK2 z hz
  obtain ⟨⟨hK0, h13, -, hκ⟩, ⟨hL150, hLK, hE1, hEK⟩, ⟨-, -, hKp2, -, -⟩, -⟩ :=
    h4 N (by omega) K hK1 hK2
  have hKpos : 0 < K := by linarith
  obtain ⟨hKb, -, -⟩ := strong_T5 ha (N := N) (by omega) (by linarith) hK2
  obtain ⟨hzl, hzf⟩ := hz
  obtain ⟨hη, hus, hΛ2N⟩ := farPass_far (𝕜 := 𝕜) h13 hzf
  obtain ⟨hQ, hQN⟩ := farPass_Q (show 2 ^ 48 ≤ N by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hu0 : 0 < (N : ℝ) * z.im := by positivity
  obtain ⟨hDF, hF1, hFK⟩ := farPass_powers ha hK0 (by linarith) hLK hE1 hEK
  have hFK' : K ^ (12 * ϑ⁻¹ + 11) * K = K ^ ledgerB ϑ⁻¹ := hFK
  have hFQ : K ^ (12 * ϑ⁻¹ + 11) ≤ (N : ℝ) ^ (1 / 16 : ℝ) := by
    have : K ^ (12 * ϑ⁻¹ + 11) ≤ K ^ (12 * ϑ⁻¹ + 11) * K :=
      le_mul_of_one_le_right (by linarith) (by linarith)
    linarith
  have hQ8 : (N : ℝ) ^ (1 / 16 : ℝ) ≤ ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 8 / 2 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hQ 7]
  have hFu : K ^ (12 * ϑ⁻¹ + 11) ≤ N * z.im := by rw [hQN] at hus; linarith
  -- the column event and the continuity of `Λ`
  have hzcol : z ∈ latticeCol ϑ⁻¹ C₀ K N z := ⟨hzl, rfl, le_rfl⟩
  have hGcl : IsClosed (goodCol M ϑ⁻¹ C₀ K z) :=
    isClosed_biInter fun w hw =>
      (goodEvent_level M hM hϑ hϑ1 hC₀ h13 (lt_of_lt_of_le hη hw.2.2) hκ).1
  have hΛc := farPass_continuous_Lam M hη
  refine ⟨hGcl.inter (isClosed_le hΛc continuous_const), ?_⟩
  -- the exponent `p = p₂`
  have hp1 : 1 ≤ levelP2 K := by
    have : (1 : ℝ) ≤ levelP2 K := by linarith
    exact_mod_cast this
  have hpK : (levelP2 K : ℝ) ≤ K + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ K / 2 by linarith)
    have e : (levelP2 K : ℝ) = 2 * (⌈K / 2⌉₊ : ℝ) := by unfold levelP2; push_cast; ring
    linarith
  -- Steps 1 and 2
  have hS0 : 0 < (msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N := by
    have := msc_im_pos hη
    positivity
  have hD0 : 0 ≤ 3 * (levelEmax ϑ⁻¹ C₀ K N + 14) * levelFL ϑ⁻¹ C₀ K N ^ 2 := by
    have : 0 ≤ levelEmax ϑ⁻¹ C₀ K N + 14 := by linarith
    positivity
  obtain ⟨hYfin, hY⟩ := farPass_moment hp1 hGcl.measurableSet hΛc.aestronglyMeasurable
    (continuous_const.mul (continuous_finsetSum _ fun k _ =>
      ((polyGrowth_schurM M 0 hη ∅).2.2.2.2.1 k).1)).aestronglyMeasurable
    (by
      refine Continuous.aestronglyMeasurable ?_
      unfold phiStarSq
      exact continuous_const.add (continuous_const.mul
        ((Complex.continuous_im.comp (farPass_continuous_stieltjes M hη)).add continuous_const)))
    (fun x => norm_nonneg _) hΛ2N
    (fun x hx => farPass_point M hM hϑ hϑ1 hC₀ h13 hκ hQ hQN hL150 hE1 (hDF.trans hFQ) hzf
      (Set.mem_iInter₂.1 hx z hzcol) (((h1 N (by omega) M hM K hK1 hK2 z hzl).1 x hx).2.1 hzf).1)
    (fun x => farPass_phi_le (by omega) x hη (Nat.cast_nonneg _))
    (h2 N (by omega) M hM K hK1 hK2 z hzl (levelP2 K) (by simp))
    (h3 N (by omega) M hM K hK1 hK2 z hzl (levelP2 K) (by simp)).1
    (by positivity) (by positivity) hu0 hFu (by positivity) (by positivity)
    (by have := msc_im_pos hη; positivity)
  -- the constant: `Y_f ≤ K^b S`
  have hc₂ : 1 / N + (msc z).im / (N * z.im) + (levelP2 K : ℝ) / (N * z.im) ^ 2 ≤
      (K + 2) * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N) := by
    have hm : 0 ≤ (msc z).im / (N * z.im) := by have := msc_im_pos hη; positivity
    have hu2 : 0 ≤ 1 / ((N : ℝ) * z.im) ^ 2 := by positivity
    have hn : 0 ≤ 1 / (N : ℝ) := by positivity
    have e : (levelP2 K : ℝ) / (N * z.im) ^ 2 = (levelP2 K : ℝ) * (1 / (N * z.im) ^ 2) := by ring
    rw [e]
    have hK1 : 0 ≤ K + 1 := by linarith
    linarith [mul_le_mul_of_nonneg_right hpK hu2, mul_nonneg hK1 hm, mul_nonneg hK1 hn]
  have hn8 : (N : ℝ) ^ (-8 : ℝ) ≤ (msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N := by
    have : (N : ℝ) ^ (-8 : ℝ) ≤ (N : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNr1 (by norm_num)
    rw [Real.rpow_neg_one, ← one_div] at this
    have := msc_im_pos hη
    have : 0 ≤ (msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 := by positivity
    linarith
  have hYB := hY.trans (farPass_const hc₂ hn8 hDF hF1 hK0 hS0.le)
  rw [hFK'] at hYB
  -- Step 3: Markov's inequality
  have hsub : goodCol M ϑ⁻¹ C₀ K z \ strongGf M ϑ⁻¹ C₀ K z ⊆
      {x | ENNReal.ofReal (K ^ (ledgerB ϑ⁻¹ + 2) *
        ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N)) ≤
          ‖(goodCol M ϑ⁻¹ C₀ K z).indicator (fun x => Lam x z) x‖ₑ} := by
    rintro x ⟨hxG, hxF⟩
    have hlt : K ^ (ledgerB ϑ⁻¹ + 2) * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N) <
        Lam x z := by
      by_contra hc
      exact hxF ⟨hxG, not_lt.1 hc⟩
    change _ ≤ ‖(goodCol M ϑ⁻¹ C₀ K z).indicator (fun x => Lam x z) x‖ₑ
    rw [Set.indicator_of_mem hxG, Real.enorm_of_nonneg (show 0 ≤ Lam x z from norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hlt.le
  have hb2 : K ^ (ledgerB ϑ⁻¹ + 2) = K ^ ledgerB ϑ⁻¹ * K ^ 2 := by
    rw [Real.rpow_add hKpos, Real.rpow_two]
  have hK2e : Real.exp 1 ≤ K ^ 2 := by
    have h : K ≤ K ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) (by linarith)
    linarith [Real.exp_one_lt_d9]
  have hKb0 : 0 < K ^ ledgerB ϑ⁻¹ := Real.rpow_pos_of_pos hKpos _
  refine (measure_mono hsub).trans (farPass_markov (by omega)
    (B := K ^ ledgerB ϑ⁻¹ * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N))
    (by positivity) ?_ ?_)
  · rw [hb2]
    calc Real.exp 1 * (K ^ ledgerB ϑ⁻¹ * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N))
        ≤ K ^ 2 * (K ^ ledgerB ϑ⁻¹ * ((msc z).im / (N * z.im) + 1 / (N * z.im) ^ 2 + 1 / N)) :=
          mul_le_mul_of_nonneg_right hK2e (mul_nonneg hKb0.le hS0.le)
      _ = _ := by ring
  · rw [← ENNReal.ofReal_toReal hYfin]
    exact ENNReal.ofReal_le_ofReal hYB


end Rigidity
