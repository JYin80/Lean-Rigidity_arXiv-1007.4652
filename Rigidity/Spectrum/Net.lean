module

public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# A finite net for the operator norm

Numbers in this file refer to the blueprint NP v1.1; the original paper (Erdős–Yau–Yin,
arXiv:1007.4652, cited as [EYY, …]) has no numbered counterpart of this lemma.

With `n = βN`, `β = dim_ℝ 𝕜 ∈ {1, 2}`, the grid `normNet 𝕜 N` of Lemma 3.14 consists of the
vectors of the unit ball of `𝕜^N` whose `n` real coordinates (real and imaginary parts of the
entries) lie in `δ ℤ`, with `δ = 1/(4√n)`.  This file proves the two statements of Lemma 3.14:
* `normNet_card`: the grid is finite and has at most `e^{3 N log N}` points for `N ≥ 13`;
* `norm_le_two_iSup_net`: for every hermitian matrix `A` over `ℝ` or `ℂ`, with `‖·‖` the `ℓ²`
  operator norm, `‖A‖ ≤ 2 sup_{y ∈ 𝒩} |⟨y, A y⟩|`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The grid step `δ_n = 1/(4√n)`, `n = βN` (Lemma 3.14). -/
noncomputable def gridStep (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : ℝ :=
  1 / (4 * Real.sqrt (Module.finrank ℝ 𝕜 * N))

/-- The grid `𝒩` of Lemma 3.14. -/
def normNet (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Set (Fin N → 𝕜) :=
  {y | (∀ i, ∃ m₁ m₂ : ℤ, RCLike.re (y i) = m₁ * gridStep 𝕜 N ∧ RCLike.im (y i) = m₂ * gridStep 𝕜 N) ∧
    ∑ i, ‖y i‖ ^ 2 ≤ 1}

/-! ### The grid step and the cardinality bound -/

private theorem net_finrank_pos : 0 < Module.finrank ℝ 𝕜 := Module.finrank_pos

private theorem net_gridStep_pos {N : ℕ} (hN : 0 < N) : 0 < gridStep 𝕜 N := by
  have h1 : (0 : ℝ) < Module.finrank ℝ 𝕜 := by exact_mod_cast net_finrank_pos (𝕜 := 𝕜)
  have h2 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold gridStep
  positivity

private theorem net_gridStep_sq {N : ℕ} (hN : 0 < N) :
    gridStep 𝕜 N ^ 2 = 1 / (16 * ((Module.finrank ℝ 𝕜 : ℝ) * N)) := by
  have h1 : (0 : ℝ) < Module.finrank ℝ 𝕜 := by exact_mod_cast net_finrank_pos (𝕜 := 𝕜)
  have h2 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold gridStep
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- The real coordinates of a point of the grid are integer multiples of `δ` of modulus at most
`1`. -/
private theorem net_coord {N : ℕ} {y : Fin N → 𝕜} (hy : y ∈ normNet 𝕜 N) (i : Fin N) :
    ∃ m₁ m₂ : ℤ, RCLike.re (y i) = m₁ * gridStep 𝕜 N ∧ RCLike.im (y i) = m₂ * gridStep 𝕜 N ∧
      |(m₁ : ℝ) * gridStep 𝕜 N| ≤ 1 ∧ |(m₂ : ℝ) * gridStep 𝕜 N| ≤ 1 := by
  obtain ⟨hlat, hsum⟩ := hy
  obtain ⟨m₁, m₂, h₁, h₂⟩ := hlat i
  have hle : ‖y i‖ ^ 2 ≤ 1 :=
    (Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)).trans hsum
  have hle' : ‖y i‖ ≤ 1 := by nlinarith [norm_nonneg (y i)]
  refine ⟨m₁, m₂, h₁, h₂, ?_, ?_⟩
  · rw [← h₁]; exact (RCLike.abs_re_le_norm _).trans hle'
  · rw [← h₂]; exact (RCLike.abs_im_le_norm _).trans hle'

/-- Lemma 3.14: size of the grid. -/
theorem normNet_card {N : ℕ} (hN : 13 ≤ N) :
    (normNet 𝕜 N).Finite ∧ ((normNet 𝕜 N).ncard : ℝ) ≤ Real.exp (3 * N * Real.log N) := by
  have hN0 : 0 < N := by omega
  have hδ : 0 < gridStep 𝕜 N := net_gridStep_pos hN0
  set δ := gridStep 𝕜 N with hδdef
  have hβ1 : 1 ≤ Module.finrank ℝ 𝕜 := net_finrank_pos
  have hβ2 : Module.finrank ℝ 𝕜 ≤ 2 := RCLike.finrank_le_two 𝕜
  have hβ1' : (1 : ℝ) ≤ Module.finrank ℝ 𝕜 := by exact_mod_cast hβ1
  have hβ2' : (Module.finrank ℝ 𝕜 : ℝ) ≤ 2 := by exact_mod_cast hβ2
  have hNr : (13 : ℝ) ≤ N := by exact_mod_cast hN
  set n : ℝ := (Module.finrank ℝ 𝕜 : ℝ) * N with hn
  have hn1 : 1 ≤ n := by rw [hn]; nlinarith
  have hn2 : n ≤ 2 * N := by rw [hn]; nlinarith
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hinv : δ⁻¹ = 4 * Real.sqrt n := by
    rw [hδdef, gridStep, one_div, inv_inv]
  set M : ℤ := ⌊4 * Real.sqrt n⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.mpr (by positivity)
  have hMle : (M : ℝ) ≤ 4 * Real.sqrt n := Int.floor_le _
  -- the coordinate map
  let T : Finset (Fin N → ℤ × ℤ) :=
    Fintype.piFinset (fun _ => Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M)
  let f : (Fin N → 𝕜) → (Fin N → ℤ × ℤ) :=
    fun y i => (⌊RCLike.re (y i) / δ⌋, ⌊RCLike.im (y i) / δ⌋)
  have hfloor : ∀ y ∈ normNet 𝕜 N, ∀ i,
      RCLike.re (y i) = (⌊RCLike.re (y i) / δ⌋ : ℤ) * δ ∧
        RCLike.im (y i) = (⌊RCLike.im (y i) / δ⌋ : ℤ) * δ := by
    intro y hy i
    obtain ⟨m₁, m₂, h₁, h₂, -, -⟩ := net_coord hy i
    rw [h₁, h₂, mul_div_cancel_right₀ _ hδ.ne', mul_div_cancel_right₀ _ hδ.ne',
      Int.floor_intCast, Int.floor_intCast]
    exact ⟨rfl, rfl⟩
  have hbound : ∀ m : ℤ, |(m : ℝ) * δ| ≤ 1 → m ∈ Finset.Icc (-M) M := by
    intro m hm
    have h1 : |(m : ℝ)| ≤ 4 * Real.sqrt n := by
      have h2 : |(m : ℝ)| * δ ≤ 1 := by rwa [abs_mul, abs_of_pos hδ] at hm
      have h3 := (le_div_iff₀ hδ).mpr h2
      rwa [one_div, hinv] at h3
    have h4 := abs_le.mp h1
    rw [Finset.mem_Icc]
    constructor
    · have : (-m : ℤ) ≤ M := Int.le_floor.mpr (by push_cast; linarith)
      omega
    · exact Int.le_floor.mpr h4.2
  have hmaps : Set.MapsTo f (normNet 𝕜 N) (T : Set (Fin N → ℤ × ℤ)) := by
    intro y hy
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product]
    intro i
    obtain ⟨m₁, m₂, h₁, h₂, h₃, h₄⟩ := net_coord hy i
    have e₁ : ⌊RCLike.re (y i) / δ⌋ = m₁ := by
      rw [h₁, mul_div_cancel_right₀ _ hδ.ne', Int.floor_intCast]
    have e₂ : ⌊RCLike.im (y i) / δ⌋ = m₂ := by
      rw [h₂, mul_div_cancel_right₀ _ hδ.ne', Int.floor_intCast]
    exact ⟨by simpa only [f, e₁] using hbound m₁ h₃, by simpa only [f, e₂] using hbound m₂ h₄⟩
  have hinj : Set.InjOn f (normNet 𝕜 N) := by
    intro y hy y' hy' hyy
    funext i
    have h1 := congrArg (fun g => (g i).1) hyy
    have h2 := congrArg (fun g => (g i).2) hyy
    simp only [f] at h1 h2
    refine RCLike.ext ?_ ?_
    · rw [(hfloor y hy i).1, (hfloor y' hy' i).1, h1]
    · rw [(hfloor y hy i).2, (hfloor y' hy' i).2, h2]
  have hfin : (normNet 𝕜 N).Finite := Set.Finite.of_injOn hmaps hinj T.finite_toSet
  refine ⟨hfin, ?_⟩
  have hcard : (normNet 𝕜 N).ncard ≤ T.card := by
    have := Set.ncard_le_ncard_of_injOn f hmaps hinj T.finite_toSet
    rwa [Set.ncard_coe_finset] at this
  have hTcard : (T.card : ℝ) = ((2 * (M : ℝ) + 1) ^ 2) ^ N := by
    have hK : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by
      have h : (((M + 1 - -M).toNat : ℕ) : ℤ) = M + 1 - -M := Int.toNat_of_nonneg (by omega)
      have h' := congrArg (Int.cast (R := ℝ)) h
      push_cast at h'
      linarith
    simp only [T, Fintype.card_piFinset, Finset.card_product, Int.card_Icc, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [hK]
    ring
  have hb1 : (2 * (M : ℝ) + 1) ^ 2 ≤ (N : ℝ) ^ 3 := by
    have h1 : 2 * (M : ℝ) + 1 ≤ 9 * Real.sqrt n := by linarith
    have h2 : (2 * (M : ℝ) + 1) ^ 2 ≤ (9 * Real.sqrt n) ^ 2 :=
      pow_le_pow_left₀ (by have : (0 : ℝ) ≤ M := by exact_mod_cast hM0
                           linarith) h1 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h2
    have h3 : (162 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h4 : (162 : ℝ) * N ≤ (N : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ N)
      nlinarith
    nlinarith
  have hexp : Real.exp (3 * N * Real.log N) = ((N : ℝ) ^ 3) ^ N := by
    rw [← pow_mul, ← Real.exp_log (show (0 : ℝ) < (N : ℝ) ^ (3 * N) by positivity),
      Real.log_pow]
    congr 1
    push_cast
    ring
  calc ((normNet 𝕜 N).ncard : ℝ) ≤ T.card := by exact_mod_cast hcard
    _ = ((2 * (M : ℝ) + 1) ^ 2) ^ N := hTcard
    _ ≤ ((N : ℝ) ^ 3) ^ N := pow_le_pow_left₀ (by positivity) hb1 N
    _ = Real.exp (3 * N * Real.log N) := hexp.symm

/-! ### Rounding to the grid -/

/-- Truncation towards `0` of a nonnegative real onto `δ ℤ`. -/
private theorem net_trunc_nonneg {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ m : ℤ, |(m : ℝ) * δ| ≤ |t| ∧ |t - m * δ| ≤ δ := by
  have h1 : (⌊t / δ⌋ : ℝ) ≤ t / δ := Int.floor_le _
  have h2 : t / δ < ⌊t / δ⌋ + 1 := Int.lt_floor_add_one _
  have h0 : (0 : ℝ) ≤ ⌊t / δ⌋ := by exact_mod_cast Int.floor_nonneg.mpr (div_nonneg ht hδ.le)
  rw [le_div_iff₀ hδ] at h1
  rw [div_lt_iff₀ hδ] at h2
  refine ⟨⌊t / δ⌋, ?_, ?_⟩
  · rw [abs_of_nonneg (mul_nonneg h0 hδ.le), abs_of_nonneg ht]; exact h1
  · rw [abs_le]; constructor <;> nlinarith

/-- Truncation towards `0` of a real onto `δ ℤ`: the result has modulus at most `|t|` and
differs from `t` by at most `δ`. -/
private theorem net_trunc {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ m : ℤ, |(m : ℝ) * δ| ≤ |t| ∧ |t - m * δ| ≤ δ := by
  rcases le_total 0 t with ht | ht
  · exact net_trunc_nonneg hδ ht
  · obtain ⟨m, h1, h2⟩ := net_trunc_nonneg hδ (neg_nonneg.mpr ht)
    refine ⟨-m, ?_, ?_⟩
    · push_cast
      rw [neg_mul, abs_neg]
      simpa [abs_neg] using h1
    · push_cast
      have : t - -(m : ℝ) * δ = -(-t - m * δ) := by ring
      rw [this, abs_neg]
      exact h2

private theorem net_two_le_finrank (hI : RCLike.im (RCLike.I : 𝕜) = 1) :
    2 ≤ Module.finrank ℝ 𝕜 := by
  have hli : LinearIndependent ℝ ![(1 : 𝕜), RCLike.I] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg RCLike.re h
    have h2 := congrArg RCLike.im h
    simp only [RCLike.real_smul_eq_coe_mul, mul_one, map_add, RCLike.ofReal_re, RCLike.mul_re,
      RCLike.I_re, mul_zero, RCLike.ofReal_im, hI, sub_self, add_zero, map_zero, RCLike.mul_im,
      zero_add] at h1 h2
    exact ⟨h1, h2⟩
  simpa using hli.fintype_card_le_finrank

/-- Rounding to the grid: every vector `x` of the unit ball is within `1/4` (in the Euclidean
norm) of a point `y` of the grid with `|y_i| ≤ |x_i|` for all `i`. -/
private theorem net_exists_close {N : ℕ} (hN : 0 < N) {x : Fin N → 𝕜}
    (hx : ∑ i, ‖x i‖ ^ 2 ≤ 1) :
    ∃ y ∈ normNet 𝕜 N, (∀ i, ‖y i‖ ^ 2 ≤ ‖x i‖ ^ 2) ∧ ∑ i, ‖x i - y i‖ ^ 2 ≤ 1 / 16 := by
  have hδ : 0 < gridStep 𝕜 N := net_gridStep_pos hN
  set δ := gridStep 𝕜 N with hδdef
  choose m₁ h₁ using fun i => net_trunc hδ (RCLike.re (x i))
  choose m₂ h₂ using fun i => net_trunc hδ (RCLike.im (x i))
  set y : Fin N → 𝕜 := fun i =>
    ((m₁ i * δ : ℝ) : 𝕜) + ((m₂ i * δ : ℝ) : 𝕜) * RCLike.I with hy
  have hre : ∀ i, RCLike.re (y i) = m₁ i * δ := by
    intro i; simp [hy]
  have hcase : ∃ ε : ℝ, 0 ≤ ε ∧ 1 + ε ≤ (Module.finrank ℝ 𝕜 : ℝ) ∧
      (∀ i, |RCLike.im (y i)| ≤ |RCLike.im (x i)|) ∧
      (∀ i, (RCLike.im (x i) - RCLike.im (y i)) ^ 2 ≤ ε * δ ^ 2) ∧
      ∀ i, ∃ m : ℤ, RCLike.im (y i) = m * δ := by
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
    · refine ⟨0, le_rfl, ?_, fun i => ?_, fun i => ?_, fun i => ⟨0, ?_⟩⟩
      · have : (1 : ℝ) ≤ Module.finrank ℝ 𝕜 := by exact_mod_cast net_finrank_pos (𝕜 := 𝕜)
        linarith
      · rw [RCLike.im_eq_zero hI, RCLike.im_eq_zero hI]
      · rw [RCLike.im_eq_zero hI, RCLike.im_eq_zero hI]; simp
      · rw [RCLike.im_eq_zero hI]; simp
    · have him : ∀ i, RCLike.im (y i) = m₂ i * δ := by
        intro i; simp [hy, hI]
      refine ⟨1, zero_le_one, ?_, fun i => ?_, fun i => ?_, fun i => ⟨m₂ i, him i⟩⟩
      · have : (2 : ℝ) ≤ Module.finrank ℝ 𝕜 := by exact_mod_cast net_two_le_finrank hI
        linarith
      · rw [him]; exact (h₂ i).1
      · rw [him, one_mul, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h₂ i).2 2
  obtain ⟨ε, hε0, hε, himle, himerr, himlat⟩ := hcase
  have hsq : ∀ i, ‖y i‖ ^ 2 ≤ ‖x i‖ ^ 2 := by
    intro i
    rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def, ← sq, ← sq, ← sq, ← sq]
    exact add_le_add (sq_le_sq.mpr (by rw [hre]; exact (h₁ i).1)) (sq_le_sq.mpr (himle i))
  refine ⟨y, ⟨fun i => ?_, ?_⟩, hsq, ?_⟩
  · obtain ⟨m, hm⟩ := himlat i
    exact ⟨m₁ i, m, hre i, hm⟩
  · exact (Finset.sum_le_sum fun i _ => hsq i).trans hx
  · have hterm : ∀ i, ‖x i - y i‖ ^ 2 ≤ (1 + ε) * δ ^ 2 := by
      intro i
      rw [RCLike.norm_sq_eq_def]
      simp only [map_sub]
      rw [← sq, ← sq, hre]
      have h := himerr i
      have h' : (RCLike.re (x i) - m₁ i * δ) ^ 2 ≤ δ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₁ i).2 2
      linarith
    calc ∑ i, ‖x i - y i‖ ^ 2 ≤ ∑ _i : Fin N, (1 + ε) * δ ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = N * ((1 + ε) * δ ^ 2) := by simp
      _ ≤ N * (Module.finrank ℝ 𝕜 * δ ^ 2) := by gcongr
      _ = 1 / 16 := by
          have h1 : (0 : ℝ) < Module.finrank ℝ 𝕜 := by exact_mod_cast net_finrank_pos (𝕜 := 𝕜)
          have h2 : (0 : ℝ) < N := by exact_mod_cast hN
          rw [hδdef, net_gridStep_sq hN]
          field_simp

/-! ### The quadratic form and a maximiser -/

private theorem net_form_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (x : Fin N → 𝕜) :
    star x ⬝ᵥ (A *ᵥ x) = inner 𝕜 (WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin N))
      (Matrix.toEuclideanLin A (WithLp.toLp 2 x)) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

private theorem net_norm_sq {N : ℕ} (x : Fin N → 𝕜) :
    ‖(WithLp.toLp 2 x : EuclideanSpace 𝕜 (Fin N))‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

private theorem net_lin_le {N : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (X : EuclideanSpace 𝕜 (Fin N)) : ‖Matrix.toEuclideanLin M X‖ ≤ ‖M‖ * ‖X‖ := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) M) X

/-- `|⟨X, A X⟩| ≤ ‖A‖ |X|²`. -/
private theorem net_form_le {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (X : EuclideanSpace 𝕜 (Fin N)) :
    ‖inner 𝕜 X (Matrix.toEuclideanLin A X)‖ ≤ ‖A‖ * ‖X‖ ^ 2 := by
  calc ‖inner 𝕜 X (Matrix.toEuclideanLin A X)‖ ≤ ‖X‖ * ‖Matrix.toEuclideanLin A X‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖X‖ * (‖A‖ * ‖X‖) := by gcongr; exact net_lin_le A X
    _ = ‖A‖ * ‖X‖ ^ 2 := by ring

/-- `⟨x, A x⟩ - ⟨y, A y⟩ = ⟨x - y, A x⟩ + ⟨y, A (x - y)⟩`, hence
`|⟨x, A x⟩ - ⟨y, A y⟩| ≤ ‖A‖ |x - y| (|x| + |y|)`. -/
private theorem net_form_sub_le {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (X Y : EuclideanSpace 𝕜 (Fin N)) :
    ‖inner 𝕜 X (Matrix.toEuclideanLin A X) - inner 𝕜 Y (Matrix.toEuclideanLin A Y)‖ ≤
      ‖A‖ * (‖X - Y‖ * (‖X‖ + ‖Y‖)) := by
  have e : inner 𝕜 X (Matrix.toEuclideanLin A X) - inner 𝕜 Y (Matrix.toEuclideanLin A Y) =
      inner 𝕜 (X - Y) (Matrix.toEuclideanLin A X) +
        inner 𝕜 Y (Matrix.toEuclideanLin A (X - Y)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]; ring
  rw [e]
  have h1 : ‖inner 𝕜 (X - Y) (Matrix.toEuclideanLin A X)‖ ≤ ‖X - Y‖ * (‖A‖ * ‖X‖) :=
    (norm_inner_le_norm _ _).trans (by gcongr; exact net_lin_le A X)
  have h2 : ‖inner 𝕜 Y (Matrix.toEuclideanLin A (X - Y))‖ ≤ ‖Y‖ * (‖A‖ * ‖X - Y‖) :=
    (norm_inner_le_norm _ _).trans (by gcongr; exact net_lin_le A (X - Y))
  calc _ ≤ ‖inner 𝕜 (X - Y) (Matrix.toEuclideanLin A X)‖ +
        ‖inner 𝕜 Y (Matrix.toEuclideanLin A (X - Y))‖ := norm_add_le _ _
    _ ≤ ‖X - Y‖ * (‖A‖ * ‖X‖) + ‖Y‖ * (‖A‖ * ‖X - Y‖) := add_le_add h1 h2
    _ = ‖A‖ * (‖X - Y‖ * (‖X‖ + ‖Y‖)) := by ring

/-- A unit vector `x` with `|⟨x, A x⟩| = |λ|` for the `k`-th ordered eigenvalue `λ`. -/
private theorem net_exists_eigvec {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (k : Fin N) :
    ∃ x : Fin N → 𝕜, ∑ i, ‖x i‖ ^ 2 = 1 ∧ ‖star x ⬝ᵥ (A *ᵥ x)‖ = |eigAsc hA k| := by
  let e : Fin (Fintype.card (Fin N)) ≃ Fin N := Fintype.equivOfCardEq (Fintype.card_fin _)
  set j : Fin N := e (Fin.cast (Fintype.card_fin N).symm k.rev) with hj
  have hjk : hA.eigenvalues j = eigAsc hA k := by
    simp [hj, e, Matrix.IsHermitian.eigenvalues, eigAsc]
  set b := hA.eigenvectorBasis j with hb
  have hnorm : ‖b‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
  refine ⟨b.ofLp, ?_, ?_⟩
  · rw [← net_norm_sq]; simp [hnorm]
  · have h := hA.mulVec_eigenvectorBasis j
    rw [← hb] at h
    rw [h, hjk, dotProduct_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, norm_mul,
      RCLike.norm_ofReal]
    have : star b.ofLp ⬝ᵥ b.ofLp = (((∑ i, ‖b.ofLp i‖ ^ 2 : ℝ)) : 𝕜) := by
      simp [dotProduct, RCLike.conj_mul, map_sum]
    have h1 : ∑ i, ‖b.ofLp i‖ ^ 2 = 1 := by rw [← net_norm_sq]; simp [hnorm]
    rw [this, h1]
    simp

/-- There is a unit vector `x` with `‖A‖ ≤ |⟨x, A x⟩|` (in fact equality). -/
private theorem net_exists_top {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (hN : 0 < N) : ∃ x : Fin N → 𝕜, ∑ i, ‖x i‖ ^ 2 = 1 ∧ ‖A‖ ≤ ‖star x ⬝ᵥ (A *ᵥ x)‖ := by
  rw [norm_eq_max_eigAsc hA hN]
  rcases le_total (-eigAsc hA ⟨0, hN⟩) (eigAsc hA ⟨N - 1, by omega⟩) with h | h
  · obtain ⟨x, h1, h2⟩ := net_exists_eigvec hA ⟨N - 1, by omega⟩
    exact ⟨x, h1, by rw [max_eq_left h, h2]; exact le_abs_self _⟩
  · obtain ⟨x, h1, h2⟩ := net_exists_eigvec hA ⟨0, hN⟩
    exact ⟨x, h1, by rw [max_eq_right h, h2]; exact neg_le_abs _⟩

/-- Lemma 3.14: the grid controls the norm. -/
theorem norm_le_two_iSup_net {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    ‖A‖ ≤ 2 * ⨆ y : normNet 𝕜 N, ‖star (y : Fin N → 𝕜) ⬝ᵥ (A *ᵥ (y : Fin N → 𝕜))‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hA0 : A = 0 := by ext i; exact i.elim0
    rw [hA0, norm_zero]
    exact mul_nonneg (by norm_num) (Real.iSup_nonneg fun _ => norm_nonneg _)
  obtain ⟨x, hx1, hxA⟩ := net_exists_top hA hN
  obtain ⟨y, hy, -, hxy⟩ := net_exists_close hN hx1.le
  set X : EuclideanSpace 𝕜 (Fin N) := WithLp.toLp 2 x with hXdef
  set Y : EuclideanSpace 𝕜 (Fin N) := WithLp.toLp 2 y with hYdef
  have hX : ‖X‖ ≤ 1 := by
    have h : ‖X‖ ^ 2 = 1 := by rw [hXdef, net_norm_sq, hx1]
    nlinarith [norm_nonneg X]
  have hY : ‖Y‖ ≤ 1 := by
    have h : ‖Y‖ ^ 2 ≤ 1 := by rw [hYdef, net_norm_sq]; exact hy.2
    nlinarith [norm_nonneg Y]
  have hXY : ‖X - Y‖ ≤ 1 / 4 := by
    have h : ‖X - Y‖ ^ 2 ≤ 1 / 16 := by
      have e : X - Y = WithLp.toLp 2 (x - y) := rfl
      rw [e, net_norm_sq]
      simpa using hxy
    nlinarith [norm_nonneg (X - Y)]
  have hbdd : BddAbove (Set.range fun z : normNet 𝕜 N =>
      ‖star (z : Fin N → 𝕜) ⬝ᵥ (A *ᵥ (z : Fin N → 𝕜))‖) := by
    refine ⟨‖A‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    change ‖star (z : Fin N → 𝕜) ⬝ᵥ (A *ᵥ (z : Fin N → 𝕜))‖ ≤ ‖A‖
    rw [net_form_eq]
    calc _ ≤ ‖A‖ * ‖(WithLp.toLp 2 (z : Fin N → 𝕜) : EuclideanSpace 𝕜 (Fin N))‖ ^ 2 :=
          net_form_le A _
      _ ≤ ‖A‖ * 1 := by
          gcongr
          rw [net_norm_sq]
          exact z.2.2
      _ = ‖A‖ := mul_one _
  have hle := le_ciSup hbdd ⟨y, hy⟩
  have hdiff := net_form_sub_le A X Y
  rw [← net_form_eq, ← net_form_eq] at hdiff
  have h1 : ‖star x ⬝ᵥ (A *ᵥ x)‖ ≤
      ‖star y ⬝ᵥ (A *ᵥ y)‖ + ‖A‖ * (‖X - Y‖ * (‖X‖ + ‖Y‖)) := by
    calc ‖star x ⬝ᵥ (A *ᵥ x)‖
        = ‖(star y ⬝ᵥ (A *ᵥ y)) + (star x ⬝ᵥ (A *ᵥ x) - star y ⬝ᵥ (A *ᵥ y))‖ := by
          congr 1; ring
      _ ≤ ‖star y ⬝ᵥ (A *ᵥ y)‖ + ‖star x ⬝ᵥ (A *ᵥ x) - star y ⬝ᵥ (A *ᵥ y)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hdiff _
  have h2 : ‖A‖ * (‖X - Y‖ * (‖X‖ + ‖Y‖)) ≤ ‖A‖ * (1 / 4 * 2) := by
    gcongr
    linarith
  simp only at hle
  linarith

end Rigidity
