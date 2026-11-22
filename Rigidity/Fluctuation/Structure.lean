module

public import Rigidity.Ensemble.Basic
public import Rigidity.Fluctuation.Calculus
public import Rigidity.Resolvent.Basic
public import Rigidity.Resolvent.Minor
public import Rigidity.Resolvent.Schur
public import Rigidity.Spectrum.Measurable
public import Rigidity.Stability.Equations

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-!
# Structure of the Green function given the minor `H^{(L)}`

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `L ⊆ {1, …, N}` this file introduces `m_a^{(L)}`, `Φ_L` and `Z_a^{(L)}` of (6.6) (`mL`, `phiL`,
`selfZL`), and proves Lemma 6.4 about the block matrix `M = M^L` of (6.5) (`schurM`):
* (a) `schurM_inv`: `(G_ab)_{a,b ∈ L} = M⁻¹`, `M_aa = 1 / G^{(L ∖ {a})}_aa ≠ 0` with
  `|1 / M_aa| ≤ η⁻¹`, `1 / G_kk = M_kk` for `L = {k}`, and, for `|L| ≥ 2` and `k ∈ L`, the
  invertibility of `M_{L'L'}` with `L' = L ∖ {k}`, `(M_{L'L'})⁻¹ = (G^{(k)}_ab)_{a,b ∈ L'}` and
  `1 / G_kk = M_kk - ∑_{a,b ∈ L'} M_ka G^{(k)}_ab M_bk`;
* (b) `noDep_greenT`, `noDep_schurM`: the entries of `G^{(L)}`, `m^{(L)}`, `m_a^{(L)}`, `Φ_L` do not
  depend on the coordinates in `𝒬(L)`, and `M_ab` does not depend on `𝒬({c})` for
  `c ∈ L ∖ {a, b}`;
* (c) `polyGrowth_schurM`: continuity and membership in the class `𝒜` of (6.3);
* (d) `selfX_eq_rowInt`: `X_k = Q_k (1 / G_kk)` with `Q_k = 1 - P_k` and `P_k = rowInt M {k}`; the
  proof computes `P_k (1 / G_kk) = -z - ∑_l σ_kl² G^{(k)}_ll` from Lemma 3.6 (I1), the
  independence of the entries of the row `k` and their mean zero, and also covers the case
  `ϑ ≤ 0` of (2.17).

Every statement holds at every point `x` of the space of entries.
-/

/-- `m_a^{(L)} = ∑_{l ∉ L} σ_al² G^{(L)}_ll` of (6.6). -/
noncomputable def mL {N : ℕ} (M : Ensemble 𝕜 N) (L : Finset (Fin N)) (z : ℂ) (a : Fin N)
    (x : Pair N → 𝕜) : ℂ :=
  ∑ l, (M.var a l : ℂ) * greenT (toMatrix x) L z l l

/-- `Φ_L = √(C₀/N) + C₀ √(Im m^{(L)}/(Nη))` of (6.6). -/
noncomputable def phiL {N : ℕ} (C₀ : ℝ) (L : Finset (Fin N)) (z : ℂ) (x : Pair N → 𝕜) : ℝ :=
  Real.sqrt (C₀ / N) + C₀ * Real.sqrt ((stieltjesT (toMatrix x) L z).im / (N * z.im))

/-- `Z_a^{(L)} = ∑_{k,l ∉ L} h_ak G^{(L)}_kl h_la - ∑_{k ∉ L} σ_ak² G^{(L)}_kk` of (6.6). -/
noncomputable def selfZL {N : ℕ} (M : Ensemble 𝕜 N) (L : Finset (Fin N)) (z : ℂ) (a : Fin N)
    (x : Pair N → 𝕜) : ℂ :=
  ∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) L z k l * toC (toMatrix x l a) -
    ∑ k, (M.var a k : ℂ) * greenT (toMatrix x) L z k k

/-! ### 1. The coordinates used by an entry -/

section Entries

variable {N : ℕ}

/-- The coordinate `{i, j}` lies in the rows `T` exactly when `i` or `j` does. -/
private lemma structure_mk'_mem_rowsQ {T : Finset (Fin N)} {i j : Fin N} :
    Pair.mk' i j ∈ rowsQ T ↔ i ∈ T ∨ j ∈ T := by
  unfold Pair.mk' rowsQ
  by_cases h : i ≤ j
  · simp [h]
  · simp [h, or_comm]

/-- The entry `h_ij` depends only on the coordinate `{i, j}`. -/
private lemma structure_toMatrix_congr {x x' : Pair N → 𝕜} {i j : Fin N}
    (h : x (Pair.mk' i j) = x' (Pair.mk' i j)) : toMatrix x i j = toMatrix x' i j := by
  simp only [toMatrix, Matrix.of_apply, h]

/-- `G^{(L)}` depends only on the coordinates `{i, j}` with `i, j ∉ L`. -/
private lemma structure_greenT_congr (L : Finset (Fin N)) (z : ℂ) {x x' : Pair N → 𝕜}
    (h : ∀ i j, i ∉ L → j ∉ L → x (Pair.mk' i j) = x' (Pair.mk' i j)) (k l : Fin N) :
    greenT (toMatrix x) L z k l = greenT (toMatrix x') L z k l := by
  have hm : minor (toMatrix x) L = minor (toMatrix x') L := by
    ext a b
    exact structure_toMatrix_congr (h a b a.2 b.2)
  have hg : greenMinor (toMatrix x) L z = greenMinor (toMatrix x') L z := by
    unfold greenMinor
    rw [hm]
  simp only [greenT, Matrix.of_apply, hg]

omit [RCLike 𝕜] in
/-- Points agreeing outside `𝒬(L)` agree at the coordinates `{i, j}` with `i, j ∉ L`. -/
private lemma structure_agree_outside {L : Finset (Fin N)} {x x' : Pair N → 𝕜}
    (h : ∀ p, p ∉ rowsQ L → x p = x' p) :
    ∀ i j, i ∉ L → j ∉ L → x (Pair.mk' i j) = x' (Pair.mk' i j) := fun i j hi hj =>
  h _ fun hp => by
    rcases structure_mk'_mem_rowsQ.1 hp with h | h <;> contradiction

/-- `G^{(L)}` vanishes when one of its indices lies in `L`. -/
private lemma structure_greenT_of_mem {A : Matrix (Fin N) (Fin N) 𝕜} {L : Finset (Fin N)} {z : ℂ}
    {k l : Fin N} (h : k ∈ L ∨ l ∈ L) : greenT A L z k l = 0 := by
  rcases h with h | h <;> simp [greenT, h]

/-- Lemma 6.4 (b): the entries of `G^{(L)}`, `m^{(L)}`, `m_a^{(L)}` and `Φ_L` do not depend on the
coordinates in `𝒬(L)`: points agreeing outside `𝒬(L)` give the same values. -/
theorem noDep_greenT (M : Ensemble 𝕜 N) (C₀ : ℝ) (L : Finset (Fin N)) (z : ℂ) :
    (∀ k l : Fin N, ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L → x p = x' p) →
      greenT (toMatrix x) L z k l = greenT (toMatrix x') L z k l) ∧
    (∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L → x p = x' p) →
      stieltjesT (toMatrix x) L z = stieltjesT (toMatrix x') L z) ∧
    (∀ a : Fin N, ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L → x p = x' p) →
      mL M L z a x = mL M L z a x') ∧
    (∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L → x p = x' p) →
      phiL C₀ L z x = phiL C₀ L z x') := by
  have hG : ∀ k l : Fin N, ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L → x p = x' p) →
      greenT (toMatrix x) L z k l = greenT (toMatrix x') L z k l := fun k l x x' h =>
    structure_greenT_congr L z (structure_agree_outside h) k l
  have hS : ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L → x p = x' p) →
      stieltjesT (toMatrix x) L z = stieltjesT (toMatrix x') L z := fun x x' h => by
    simp only [stieltjesT, hG _ _ x x' h]
  refine ⟨hG, hS, fun a x x' h => ?_, fun x x' h => ?_⟩
  · simp only [mL, hG _ _ x x' h]
  · simp only [phiL, hS x x' h]

/-- `M^L_ab` depends only on the coordinates `{a, b}`, `{a, k}`, `{l, b}` and `{i, j}`, with
`i, j, k, l ∉ L`. -/
private lemma structure_schurM_congr (L : Finset (Fin N)) (z : ℂ) {a b : Fin N} (ha : a ∈ L)
    (hb : b ∈ L) {x x' : Pair N → 𝕜}
    (h : ∀ i j, ((i ∉ L ∧ j ∉ L) ∨ (i = a ∧ j ∉ L) ∨ (i ∉ L ∧ j = b) ∨ (i = a ∧ j = b)) →
      x (Pair.mk' i j) = x' (Pair.mk' i j)) :
    schurM (toMatrix x) L z ⟨a, ha⟩ ⟨b, hb⟩ = schurM (toMatrix x') L z ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hGG : ∀ k l, greenT (toMatrix x) L z k l = greenT (toMatrix x') L z k l := fun k l =>
    structure_greenT_congr L z (fun i j hi hj => h i j (Or.inl ⟨hi, hj⟩)) k l
  have hab : toMatrix x a b = toMatrix x' a b :=
    structure_toMatrix_congr (h a b (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  simp only [schurM, Matrix.of_apply, hab]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hk : k ∈ L
  · simp [structure_greenT_of_mem (Or.inl hk)]
  by_cases hl : l ∈ L
  · simp [structure_greenT_of_mem (Or.inr hl)]
  rw [hGG k l, structure_toMatrix_congr (h a k (Or.inr (Or.inl ⟨rfl, hk⟩))),
    structure_toMatrix_congr (h l b (Or.inr (Or.inr (Or.inl ⟨hl, rfl⟩))))]

/-- Lemma 6.4 (b): `M^L_ab` does not depend on `𝒬({c})` for `c ∈ L ∖ {a, b}`, and more generally
only depends on the coordinates in `𝒬({a, b})` and outside `𝒬(L)`. -/
theorem noDep_schurM (L : Finset (Fin N)) (z : ℂ) {a b : Fin N} (ha : a ∈ L) (hb : b ∈ L) :
    (∀ c ∈ L, c ≠ a → c ≠ b → ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ {c} → x p = x' p) →
      schurM (toMatrix x) L z ⟨a, ha⟩ ⟨b, hb⟩ = schurM (toMatrix x') L z ⟨a, ha⟩ ⟨b, hb⟩) ∧
    (∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ L \ rowsQ {a, b} → x p = x' p) →
      schurM (toMatrix x) L z ⟨a, ha⟩ ⟨b, hb⟩ = schurM (toMatrix x') L z ⟨a, ha⟩ ⟨b, hb⟩) := by
  refine ⟨fun c hc hca hcb x x' h => structure_schurM_congr L z ha hb fun i j hij => h _ ?_,
    fun x x' h => structure_schurM_congr L z ha hb fun i j hij => h _ ?_⟩
  · intro hp
    rw [structure_mk'_mem_rowsQ] at hp
    simp only [Finset.mem_singleton] at hp
    rcases hij with ⟨hi, hj⟩ | ⟨rfl, hj⟩ | ⟨hi, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hp with rfl | rfl <;> simp_all
  · intro hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [structure_mk'_mem_rowsQ] at hp1 hp2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp2
    rcases hij with ⟨hi, hj⟩ | ⟨rfl, hj⟩ | ⟨hi, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hp1 with h1 | h1 <;> contradiction
    · exact hp2 (Or.inl (Or.inl rfl))
    · exact hp2 (Or.inr (Or.inr rfl))
    · exact hp2 (Or.inl (Or.inl rfl))

/-! ### 2. Lemma 6.4 (a): algebra -/

/-- Lemma 3.5 (a) for the minors: `‖G^{(T)}_kl‖ ≤ η⁻¹`. -/
private lemma structure_norm_greenT_le {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (k l : Fin N) :
    ‖greenT A T z k l‖ ≤ 1 / z.im := by
  by_cases h : k ∉ T ∧ l ∉ T
  · have hP : (minor A T).IsHermitian :=
      hA.submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    have : greenT A T z k l = green (minor A T) z ⟨k, h.1⟩ ⟨l, h.2⟩ := by
      simp [greenT, greenMinor, h.1, h.2]
    rw [this]
    exact norm_green_apply_le hP hz _ _
  · rw [structure_greenT_of_mem (by tauto : k ∈ T ∨ l ∈ T), norm_zero]
    exact (one_div_pos.2 hz).le

/-- Lemma 3.5 (a) for the minors: `Im G^{(T)}_aa > 0` for `a ∉ T`. -/
private lemma structure_greenT_diag_im_pos {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) {a : Fin N} (ha : a ∉ T) :
    0 < (greenT A T z a a).im := by
  have hP : (minor A T).IsHermitian :=
    hA.submatrix (Subtype.val : {i // i ∉ T} → Fin N)
  have : greenT A T z a a = green (minor A T) z ⟨a, ha⟩ ⟨a, ha⟩ := by
    simp [greenT, greenMinor, ha]
  rw [this]
  exact green_im_diag_pos hP hz _

/-- Lemma 6.4 (a): `(G_ab)_{a,b ∈ L} = M⁻¹`; `M_aa = 1 / G^{(L ∖ {a})}_aa ≠ 0` with
`|1 / M_aa| ≤ η⁻¹`; `1 / G_kk = M_kk` for `L = {k}`; and, for `r = |L| ≥ 2` and `k ∈ L`, the
matrix `M_{L'L'}` with `L' = L ∖ {k}` is invertible with inverse `(G^{(k)}_ab)_{a,b ∈ L'}`,
`|G^{(k)}_ab| ≤ η⁻¹`, and `1 / G_kk = M_kk - ∑_{a,b ∈ L'} M_ka G^{(k)}_ab M_bk`. -/
theorem schurM_inv {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N)) (x : Pair N → 𝕜) :
    (IsUnit (schurM (toMatrix x) L z) ∧
      (Matrix.of fun a b : L => green (toMatrix x) z a b) = (schurM (toMatrix x) L z)⁻¹) ∧
    (∀ a (ha : a ∈ L),
      schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩ = 1 / greenT (toMatrix x) (L.erase a) z a a ∧
      schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩ ≠ 0 ∧
      ‖1 / schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩‖ ≤ 1 / z.im) ∧
    (∀ k, 1 / green (toMatrix x) z k k =
      schurM (toMatrix x) {k} z ⟨k, Finset.mem_singleton_self k⟩
        ⟨k, Finset.mem_singleton_self k⟩) ∧
    (∀ k (hk : k ∈ L), (L.erase k).Nonempty →
      IsUnit (Matrix.of fun a b : L.erase k =>
        schurM (toMatrix x) L z ⟨a, Finset.mem_of_mem_erase a.2⟩
          ⟨b, Finset.mem_of_mem_erase b.2⟩) ∧
      (Matrix.of fun a b : L.erase k =>
        schurM (toMatrix x) L z ⟨a, Finset.mem_of_mem_erase a.2⟩
          ⟨b, Finset.mem_of_mem_erase b.2⟩)⁻¹ =
        (Matrix.of fun a b : L.erase k => greenT (toMatrix x) {k} z a b) ∧
      (∀ a b : L.erase k, ‖greenT (toMatrix x) {k} z a b‖ ≤ 1 / z.im) ∧
      1 / green (toMatrix x) z k k = schurM (toMatrix x) L z ⟨k, hk⟩ ⟨k, hk⟩ -
        ∑ a : L.erase k, ∑ b : L.erase k,
          schurM (toMatrix x) L z ⟨k, hk⟩ ⟨a, Finset.mem_of_mem_erase a.2⟩ *
            greenT (toMatrix x) {k} z a b *
            schurM (toMatrix x) L z ⟨b, Finset.mem_of_mem_erase b.2⟩ ⟨k, hk⟩) := by
  have hA := toMatrix_isHermitian x
  refine ⟨schur_block hA hz L, fun a ha => ?_, fun k => ?_, fun k hk hne => ?_⟩
  · have h1 := schurM_diag_eq hA hz L ha
    have hne : greenT (toMatrix x) (L.erase a) z a a ≠ 0 := fun h => by
      have := structure_greenT_diag_im_pos hA hz (L.erase a) (Finset.notMem_erase a L)
      rw [h, Complex.zero_im] at this
      exact lt_irrefl _ this
    refine ⟨h1, by rw [h1]; exact one_div_ne_zero hne, ?_⟩
    rw [h1, one_div_one_div]
    exact structure_norm_greenT_le hA hz _ a a
  · have h := inv_green_diag hA hz k
    rw [h]
    simp [schurM, greenT, Finset.mem_singleton]
  · obtain ⟨hU, hinv, hform⟩ := inv_green_eq_schurM hA hz L hk hne
    exact ⟨hU, hinv, fun a b => structure_norm_greenT_le hA hz _ a b, hform⟩

/-! ### 3. Lemma 6.4 (c): regularity -/

/-- `‖toC y‖ = ‖y‖`. -/
private lemma structure_norm_toC (y : 𝕜) : ‖toC y‖ = ‖y‖ := by
  have h : ‖toC y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, RCLike.norm_sq_eq_def]
    simp [toC]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- `|h_ij| ≤ |x_ij|`. -/
private lemma structure_norm_toMatrix_le (x : Pair N → 𝕜) (i j : Fin N) :
    ‖toMatrix x i j‖ ≤ ‖x (Pair.mk' i j)‖ := by
  unfold toMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_star]
  · exact (by simpa using RCLike.abs_re_le_norm _)

/-- `|h_ij| ≤ |x|₁`. -/
private lemma structure_norm_entry_le (x : Pair N → 𝕜) (i j : Fin N) :
    ‖toC (toMatrix x i j)‖ ≤ ∑ p, ‖x p‖ := by
  rw [structure_norm_toC]
  exact (structure_norm_toMatrix_le x i j).trans
    (Finset.single_le_sum (f := fun p => ‖x p‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _))

/-- The coordinate map `toC : 𝕜 → ℂ` is continuous. -/
private lemma structure_continuous_toC : Continuous (toC : 𝕜 → ℂ) := by
  have : (toC : 𝕜 → ℂ) =
      fun y => ((RCLike.re y : ℝ) : ℂ) + ((RCLike.im y : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [toC]
  rw [this]
  fun_prop

/-- The entries `x ↦ h_ab(x)` are continuous. -/
private lemma structure_continuous_entry (a b : Fin N) :
    Continuous fun x : Pair N → 𝕜 => toC (toMatrix x a b) := by
  refine structure_continuous_toC.comp ?_
  unfold toMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).star
  · exact RCLike.continuous_ofReal.comp (RCLike.continuous_re.comp (continuous_apply _))

/-- For fixed `z` with `Im z > 0`, the entries `x ↦ G^{(T)}_ij(x)` are continuous. -/
private lemma structure_continuous_greenT {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N))
    (i j : Fin N) : Continuous fun x : Pair N → 𝕜 => greenT (toMatrix x) T z i j := by
  have h : Continuous fun x : Pair N → 𝕜 =>
      (fun q : (Pair N → 𝕜) × {z : ℂ // 0 < z.im} => greenT (toMatrix q.1) T q.2 i j)
        (x, ⟨z, hz⟩) :=
    (continuous_greenT T i j).comp (continuous_id.prodMk continuous_const)
  exact h

/-- A continuous function with a polynomial bound lies in the class `𝒜`. -/
private lemma structure_polyGrowth_of_bound {f : (Pair N → 𝕜) → ℂ} (hf : Continuous f) {c : ℝ}
    {m : ℕ} (h : ∀ x, ‖f x‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m) : PolyGrowth f :=
  ⟨hf.measurable, c, m, h⟩

/-- `α + β S + γ S² ≤ (α + β + γ) (1 + S)²` for nonnegative `α, β, γ, S`. -/
private lemma structure_quad_le {S α β γ : ℝ} (hS : 0 ≤ S) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) : α + β * S + γ * S ^ 2 ≤ (α + β + γ) * (1 + S) ^ 2 := by
  nlinarith [mul_nonneg hα hS, mul_nonneg hβ hS, mul_nonneg hγ hS, mul_nonneg hα (sq_nonneg S),
    mul_nonneg hβ (sq_nonneg S), mul_nonneg hγ (sq_nonneg S)]

/-- The quadratic form `∑_{k,l} h_ak G^{(T)}_kl h_lb` is at most `N² η⁻¹ |x|₁²`. -/
private lemma structure_norm_bilin_le {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N)) (a b : Fin N)
    (x : Pair N → 𝕜) :
    ‖∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)‖ ≤
      (N : ℝ) ^ 2 * (1 / z.im) * (∑ p, ‖x p‖) ^ 2 := by
  have hA := toMatrix_isHermitian x
  have hS : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)‖
      ≤ ∑ k, ∑ l, ‖toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ _k : Fin N, ∑ _l : Fin N, (∑ p, ‖x p‖) * (1 / z.im) * (∑ p, ‖x p‖) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (structure_norm_entry_le x a k)
          (structure_norm_greenT_le hA hz T k l) (norm_nonneg _) hS)
          (structure_norm_entry_le x l b) (norm_nonneg _) (mul_nonneg hS (one_div_pos.2 hz).le)
    _ = (N : ℝ) ^ 2 * (1 / z.im) * (∑ p, ‖x p‖) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The common shape of `M^L_ab` and `1 / G_kk`: continuity and polynomial growth of
`h_ab - w - ∑_{k,l} h_ak G^{(T)}_kl h_lb`. -/
private lemma structure_polyGrowth_expr {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N))
    (a b : Fin N) (w : ℂ) :
    Continuous (fun x : Pair N → 𝕜 => toC (toMatrix x a b) - w -
      ∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)) ∧
    PolyGrowth (fun x : Pair N → 𝕜 => toC (toMatrix x a b) - w -
      ∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)) := by
  have hc : Continuous (fun x : Pair N → 𝕜 => toC (toMatrix x a b) - w -
      ∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)) :=
    ((structure_continuous_entry a b).sub continuous_const).sub
      (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
        ((structure_continuous_entry a k).mul (structure_continuous_greenT hz T k l)).mul
          (structure_continuous_entry l b))
  refine ⟨hc, structure_polyGrowth_of_bound hc (c := ‖w‖ + 1 + (N : ℝ) ^ 2 * (1 / z.im)) (m := 2)
    fun x => ?_⟩
  have hS : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc _ ≤ ‖toC (toMatrix x a b)‖ + ‖w‖ +
        ‖∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) T z k l * toC (toMatrix x l b)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖w‖ + 1 * (∑ p, ‖x p‖) + (N : ℝ) ^ 2 * (1 / z.im) * (∑ p, ‖x p‖) ^ 2 := by
        have := structure_norm_entry_le x a b
        have := structure_norm_bilin_le hz T a b x
        linarith
    _ ≤ _ := structure_quad_le hS (norm_nonneg _) zero_le_one
        (mul_nonneg (sq_nonneg _) (one_div_pos.2 hz).le)

/-- `‖m_a^{(L)}‖ ≤ η⁻¹ ∑_l σ_al²`. -/
private lemma structure_norm_mL_le (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N))
    (a : Fin N) (x : Pair N → 𝕜) :
    ‖mL M L z a x‖ ≤ (∑ l, |M.var a l|) * (1 / z.im) := by
  have hA := toMatrix_isHermitian x
  unfold mL
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (structure_norm_greenT_le hA hz L l l) (abs_nonneg _)

/-- `m_a^{(L)}` is continuous in the entries. -/
private lemma structure_continuous_mL (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) (a : Fin N) : Continuous (mL M L z a) :=
  continuous_finsetSum _ fun l _ => continuous_const.mul (structure_continuous_greenT hz L l l)

/-- `Z_a^{(L)}` is continuous in the entries. -/
private lemma structure_continuous_selfZL (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) (a : Fin N) : Continuous (selfZL M L z a) :=
  (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((structure_continuous_entry a k).mul (structure_continuous_greenT hz L k l)).mul
      (structure_continuous_entry l a)).sub (structure_continuous_mL M hz L a)

/-- `‖Z_a^{(L)}‖ ≤ η⁻¹ (N² |x|₁² + ∑_l σ_al²)`. -/
private lemma structure_norm_selfZL_le (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) (a : Fin N) (x : Pair N → 𝕜) :
    ‖selfZL M L z a x‖ ≤ (∑ l, |M.var a l|) * (1 / z.im) +
      (N : ℝ) ^ 2 * (1 / z.im) * (∑ p, ‖x p‖) ^ 2 := by
  have h1 := structure_norm_bilin_le hz L a a x
  have h2 := structure_norm_mL_le M hz L a x
  have : selfZL M L z a x = (∑ k, ∑ l, toC (toMatrix x a k) * greenT (toMatrix x) L z k l *
      toC (toMatrix x l a)) - mL M L z a x := rfl
  rw [this]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Lemma 6.4 (c): `M_ab`, `1 / M_aa`, `G^{(k)}_ab`, `1 / G_kk`, `X_k`, `Z_a^{(L)}` are continuous
and in the class `𝒜` of (6.3); `m_a^{(L)}` and `Φ_L` are continuous and bounded. -/
theorem polyGrowth_schurM (M : Ensemble 𝕜 N) (C₀ : ℝ) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) :
    (∀ a b (ha : a ∈ L) (hb : b ∈ L),
      Continuous (fun x : Pair N → 𝕜 => schurM (toMatrix x) L z ⟨a, ha⟩ ⟨b, hb⟩) ∧
      PolyGrowth (fun x : Pair N → 𝕜 => schurM (toMatrix x) L z ⟨a, ha⟩ ⟨b, hb⟩)) ∧
    (∀ a (ha : a ∈ L),
      Continuous (fun x : Pair N → 𝕜 => 1 / schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩) ∧
      PolyGrowth (fun x : Pair N → 𝕜 => 1 / schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩)) ∧
    (∀ k a b : Fin N, Continuous (fun x : Pair N → 𝕜 => greenT (toMatrix x) {k} z a b) ∧
      PolyGrowth (fun x : Pair N → 𝕜 => greenT (toMatrix x) {k} z a b)) ∧
    (∀ k : Fin N, Continuous (fun x : Pair N → 𝕜 => 1 / green (toMatrix x) z k k) ∧
      PolyGrowth (fun x : Pair N → 𝕜 => 1 / green (toMatrix x) z k k)) ∧
    (∀ k : Fin N, Continuous (fun x : Pair N → 𝕜 => selfX (toMatrix x) M.varMatrix z k) ∧
      PolyGrowth (fun x : Pair N → 𝕜 => selfX (toMatrix x) M.varMatrix z k)) ∧
    (∀ a : Fin N, Continuous (selfZL M L z a) ∧ PolyGrowth (selfZL M L z a)) ∧
    (∀ a : Fin N, Continuous (mL M L z a) ∧ ∃ c : ℝ, ∀ x : Pair N → 𝕜, ‖mL M L z a x‖ ≤ c) ∧
    (Continuous (phiL (𝕜 := 𝕜) C₀ L z) ∧ ∃ c : ℝ, ∀ x : Pair N → 𝕜, |phiL C₀ L z x| ≤ c) := by
  have hGc : ∀ (T : Finset (Fin N)) (a b : Fin N), Continuous (fun x : Pair N → 𝕜 =>
      greenT (toMatrix x) T z a b) := fun T a b => structure_continuous_greenT hz T a b
  have hGp : ∀ (T : Finset (Fin N)) (a b : Fin N), PolyGrowth (fun x : Pair N → 𝕜 =>
      greenT (toMatrix x) T z a b) := fun T a b =>
    structure_polyGrowth_of_bound (hGc T a b) (c := 1 / z.im) (m := 0) fun x => by
      simpa using structure_norm_greenT_le (toMatrix_isHermitian x) hz T a b
  refine ⟨fun a b ha hb => ?_, fun a ha => ?_, fun k a b => ⟨hGc _ a b, hGp _ a b⟩,
    fun k => ?_, fun k => ?_, fun a => ?_, fun a => ?_, ?_⟩
  · exact structure_polyGrowth_expr hz L a b _
  · have h : (fun x : Pair N → 𝕜 => 1 / schurM (toMatrix x) L z ⟨a, ha⟩ ⟨a, ha⟩) =
        fun x => greenT (toMatrix x) (L.erase a) z a a := by
      funext x
      rw [schurM_diag_eq (toMatrix_isHermitian x) hz L ha, one_div_one_div]
    rw [h]
    exact ⟨hGc _ a a, hGp _ a a⟩
  · have h : (fun x : Pair N → 𝕜 => 1 / green (toMatrix x) z k k) =
        fun x => toC (toMatrix x k k) - z -
          ∑ a, ∑ b,
            toC (toMatrix x k a) * greenT (toMatrix x) {k} z a b * toC (toMatrix x b k) := by
      funext x
      exact inv_green_diag (toMatrix_isHermitian x) hz k
    rw [h]
    exact structure_polyGrowth_expr hz {k} k k z
  · have hc : Continuous (fun x : Pair N → 𝕜 => selfX (toMatrix x) M.varMatrix z k) :=
      (structure_continuous_entry k k).sub (structure_continuous_selfZL M hz {k} k)
    refine ⟨hc, structure_polyGrowth_of_bound hc
      (c := (∑ l, |M.var k l|) * (1 / z.im) + 1 + (N : ℝ) ^ 2 * (1 / z.im)) (m := 2) fun x => ?_⟩
    have hS : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hX : selfX (toMatrix x) M.varMatrix z k =
        toC (toMatrix x k k) - selfZL M {k} z k x := rfl
    rw [hX]
    calc _ ≤ ‖toC (toMatrix x k k)‖ + ‖selfZL M {k} z k x‖ := norm_sub_le _ _
      _ ≤ (∑ l, |M.var k l|) * (1 / z.im) + 1 * (∑ p, ‖x p‖) +
          (N : ℝ) ^ 2 * (1 / z.im) * (∑ p, ‖x p‖) ^ 2 := by
        have := structure_norm_entry_le x k k
        have := structure_norm_selfZL_le M hz {k} k x
        linarith
      _ ≤ _ := structure_quad_le hS (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (one_div_pos.2 hz).le) zero_le_one (mul_nonneg (sq_nonneg _) (one_div_pos.2 hz).le)
  · refine ⟨structure_continuous_selfZL M hz L a, structure_polyGrowth_of_bound
      (structure_continuous_selfZL M hz L a)
      (c := (∑ l, |M.var a l|) * (1 / z.im) + 0 + (N : ℝ) ^ 2 * (1 / z.im)) (m := 2) fun x => ?_⟩
    have hS : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine (structure_norm_selfZL_le M hz L a x).trans ?_
    have hα : 0 ≤ (∑ l, |M.var a l|) * (1 / z.im) :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (one_div_pos.2 hz).le
    have hγ : 0 ≤ (N : ℝ) ^ 2 * (1 / z.im) := mul_nonneg (sq_nonneg _) (one_div_pos.2 hz).le
    have := structure_quad_le hS hα le_rfl hγ
    simpa using this
  · exact ⟨structure_continuous_mL M hz L a, _, fun x => structure_norm_mL_le M hz L a x⟩
  · have hm : Continuous (fun x : Pair N → 𝕜 => stieltjesT (toMatrix x) L z) :=
      continuous_const.mul (continuous_finsetSum _ fun k _ => hGc L k k)
    have hmb : ∀ x : Pair N → 𝕜, ‖stieltjesT (toMatrix x) L z‖ ≤ 1 / z.im := fun x => by
      have hA := toMatrix_isHermitian x
      have h1 : ‖∑ k, greenT (toMatrix x) L z k k‖ ≤ N * (1 / z.im) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ k, ‖greenT (toMatrix x) L z k k‖ ≤ ∑ _k : Fin N, 1 / z.im :=
              Finset.sum_le_sum fun k _ => structure_norm_greenT_le hA hz L k k
          _ = N * (1 / z.im) := by simp
      unfold stieltjesT
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0
        simp only [Nat.cast_zero, _root_.inv_zero, zero_mul]
        exact (one_div_pos.2 hz).le
      · have hN : (0 : ℝ) < N := by exact_mod_cast h0
        calc (N : ℝ)⁻¹ * ‖∑ k, greenT (toMatrix x) L z k k‖ ≤ (N : ℝ)⁻¹ * (N * (1 / z.im)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 1 / z.im := by field_simp
    refine ⟨?_, Real.sqrt (C₀ / N) + |C₀| * Real.sqrt ((1 / z.im) / (N * z.im)), fun x => ?_⟩
    · unfold phiL
      refine continuous_const.add (continuous_const.mul (Real.continuous_sqrt.comp ?_))
      exact (Complex.continuous_im.comp hm).div_const _
    · unfold phiL
      have hsq : Real.sqrt ((stieltjesT (toMatrix x) L z).im / (N * z.im)) ≤
          Real.sqrt ((1 / z.im) / (N * z.im)) := by
        refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (by positivity))
        exact (Complex.im_le_norm _).trans (hmb x)
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))

/-! ### 4. Lemma 6.4 (d): the expectation in one row -/

section Expectation

variable (M : Ensemble 𝕜 N)

/-- Every moment of an entry is finite: under (2.17) with `ϑ > 0` by Lemma 4.1 (a), and for
`ϑ ≤ 0` the right-hand side of (2.17) vanishes, so that the entry is bounded almost surely. -/
private lemma structure_integrable_norm_pow {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) (m : ℕ) : Integrable (fun y : 𝕜 => ‖y‖ ^ m) (M.law p) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  by_cases hϑ : 0 < ϑ
  · have hϑ' : 0 < min ϑ 1 := lt_min hϑ one_pos
    have hM' := Ensemble.Assumptions.mono M hM hϑ' (min_le_left _ _) le_rfl le_rfl le_rfl
    have hmom := (moments_bound hϑ' (min_le_right _ _) (μ := M.law p)
      (s := Real.sqrt (M.varPair p)) (Real.sqrt_nonneg _) (hM'.subexp p)
      (q := (m : ℝ)) (by exact_mod_cast hm)).1
    simpa only [Real.rpow_natCast] using hmom
  · have hϑ0 : ϑ⁻¹ ≤ 0 := inv_nonpos.2 (not_lt.1 hϑ)
    have h0 : M.law p {y | 1 * Real.sqrt (M.varPair p) < ‖y‖} = 0 := by
      refine le_antisymm ((hM.subexp p 1 le_rfl).trans ?_) zero_le
      refine le_of_eq (ENNReal.ofReal_of_nonpos ?_)
      nlinarith [Real.exp_pos (-((1 : ℝ) ^ ϑ))]
    have hae : ∀ᵐ y ∂M.law p, ‖y‖ ≤ Real.sqrt (M.varPair p) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with y hy
      simpa using hy
    refine (integrable_const ((Real.sqrt (M.varPair p)) ^ m)).mono'
      (measurable_norm.pow_const m).aestronglyMeasurable ?_
    filter_upwards [hae] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hy m

omit [RCLike 𝕜] in
/-- The coordinate `{k, a}` lies in the row `k`. -/
private lemma structure_mk'_mem_self (k a : Fin N) :
    Pair.mk' k a ∈ rowsQ ({k} : Finset (Fin N)) :=
  structure_mk'_mem_rowsQ.2 (Or.inl (Finset.mem_singleton_self k))

omit [RCLike 𝕜] in
/-- Distinct entries of the row `k` are distinct coordinates. -/
private lemma structure_mk'_injective (k : Fin N) : Function.Injective (Pair.mk' k) := by
  intro a b h
  unfold Pair.mk' at h
  by_cases h1 : k ≤ a <;> by_cases h2 : k ≤ b <;>
    simp [h1, h2, Subtype.ext_iff, Prod.ext_iff] at h <;> omega

/-- The coordinate of the row `k` as a subtype element. -/
private abbrev structure_pk (k a : Fin N) : rowsQ ({k} : Finset (Fin N)) :=
  ⟨Pair.mk' k a, structure_mk'_mem_self k a⟩

/-- `h_ka` as a function of the coordinate `x_{ka}`, for `a ≠ k`. -/
private def structure_coord (k a : Fin N) (u : 𝕜) : 𝕜 := if k < a then u else star u

private lemma structure_norm_coord (k a : Fin N) (u : 𝕜) : ‖structure_coord k a u‖ = ‖u‖ := by
  unfold structure_coord
  split_ifs
  · rfl
  · exact norm_star u

private lemma structure_continuous_coord (k a : Fin N) :
    Continuous (structure_coord k a : 𝕜 → 𝕜) := by
  unfold structure_coord
  split_ifs
  · exact continuous_id
  · exact continuous_star

/-- `h_ka` for the point equal to `x` outside the row `k` and to `y` on it. -/
private lemma structure_toMatrix_merge_off (k : Fin N) (x : Pair N → 𝕜)
    (y : rowsQ ({k} : Finset (Fin N)) → 𝕜) {a : Fin N} (ha : a ≠ k) :
    toMatrix (piMerge (rowsQ {k}) x y) k a = structure_coord k a (y (structure_pk k a)) := by
  have hm : piMerge (rowsQ {k}) x y (Pair.mk' k a) = y (structure_pk k a) := by
    simp [piMerge, structure_mk'_mem_self k a]
  unfold toMatrix structure_coord
  simp only [Matrix.of_apply]
  rcases lt_or_gt_of_ne ha.symm with h | h
  · simp [h, hm]
  · simp [not_lt.2 h.le, h, hm]

/-- `h_kk` for the point equal to `x` outside the row `k` and to `y` on it. -/
private lemma structure_toMatrix_merge_diag (k : Fin N) (x : Pair N → 𝕜)
    (y : rowsQ ({k} : Finset (Fin N)) → 𝕜) :
    toMatrix (piMerge (rowsQ {k}) x y) k k =
      ((RCLike.re (y (structure_pk k k)) : ℝ) : 𝕜) := by
  have hm : piMerge (rowsQ {k}) x y (Pair.mk' k k) = y (structure_pk k k) := by
    simp [piMerge, structure_mk'_mem_self k k]
  unfold toMatrix
  simp [hm]

/-- The row `k` of the point equal to `x` outside the row `k` leaves `G^{({k})}` unchanged. -/
private lemma structure_greenT_merge (k : Fin N) (z : ℂ) (x : Pair N → 𝕜)
    (y : rowsQ ({k} : Finset (Fin N)) → 𝕜) (a b : Fin N) :
    greenT (toMatrix (piMerge (rowsQ {k}) x y)) {k} z a b = greenT (toMatrix x) {k} z a b :=
  structure_greenT_congr {k} z (fun i j hi hj => by
    have hmem : Pair.mk' i j ∉ rowsQ ({k} : Finset (Fin N)) := fun hm => by
      rcases structure_mk'_mem_rowsQ.1 hm with h | h <;> contradiction
    simp [piMerge, hmem]) a b

/-- `toC y = (re y : ℂ)` for real `y`. -/
private lemma structure_toC_ofReal (r : ℝ) : toC (RCLike.ofReal r : 𝕜) = (r : ℂ) := by
  apply Complex.ext <;> simp [toC]

/-- `toC c · toC (star c) = |c|²`. -/
private lemma structure_toC_mul_star (c : 𝕜) : toC c * toC (star c) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [toC, RCLike.norm_sq_eq_def, RCLike.star_def]
  ring

/-- The integral commutes with `toC`. -/
private lemma structure_integral_toC {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) : ∫ a, toC (f a) ∂μ = toC (∫ a, f a ∂μ) := by
  have hre := integral_re hf
  have him := integral_im hf
  have h : (fun a => toC (f a)) =
      fun a => ((RCLike.re (f a) : ℝ) : ℂ) + ((RCLike.im (f a) : ℝ) : ℂ) * Complex.I := by
    funext a
    apply Complex.ext <;> simp [toC]
  rw [h, integral_add hf.re.ofReal (hf.im.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hre, him]
  apply Complex.ext <;> simp [toC]

/-- A function of one coordinate of the product law is integrable when it is integrable against
the entry law. -/
private lemma structure_integrable_coord (T : Finset (Fin N)) (p : rowsQ T) {E : Type*}
    [NormedAddCommGroup E] {g : 𝕜 → E} (hg : Integrable g (M.law p)) :
    Integrable (fun y : rowsQ T → 𝕜 => g (y p)) (Measure.pi fun q : rowsQ T => M.law q) :=
  (measurePreserving_eval (fun q : rowsQ T => M.law q) p).integrable_comp_of_integrable hg

/-- The integral of a function of one coordinate of the product law is the integral against the
entry law. -/
private lemma structure_integral_coord (T : Finset (Fin N)) (p : rowsQ T) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : 𝕜 → E}
    (hg : AEStronglyMeasurable g (M.law p)) :
    ∫ y : rowsQ T → 𝕜, g (y p) ∂(Measure.pi fun q : rowsQ T => M.law q) =
      ∫ u, g u ∂M.law p := by
  have hmp := measurePreserving_eval (fun q : rowsQ T => M.law q) p
  calc ∫ y : rowsQ T → 𝕜, g (y p) ∂(Measure.pi fun q : rowsQ T => M.law q)
      = ∫ u, g u ∂((Measure.pi fun q : rowsQ T => M.law q).map (Function.eval p)) :=
        (integral_map hmp.measurable.aemeasurable (by rwa [hmp.map_eq])).symm
    _ = ∫ u, g u ∂M.law p := by rw [hmp.map_eq]

/-- `h_ka` as a random variable on the row `k`. -/
private noncomputable def structure_ua (k a : Fin N) (y : rowsQ ({k} : Finset (Fin N)) → 𝕜) : ℂ :=
  toC (structure_coord k a (y (structure_pk k a)))

/-- `h_ak` as a random variable on the row `k`. -/
private noncomputable def structure_va (k a : Fin N) (y : rowsQ ({k} : Finset (Fin N)) → 𝕜) : ℂ :=
  toC (star (structure_coord k a (y (structure_pk k a))))

/-- A continuous function of an entry with the same norm is integrable against the entry law. -/
private lemma structure_integrable_toC_comp {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) {f : 𝕜 → 𝕜} (hf : Continuous f) (hn : ∀ u, ‖f u‖ = ‖u‖) :
    Integrable (fun u => toC (f u)) (M.law p) := by
  refine (structure_integrable_norm_pow M hM p 1).mono'
    (structure_continuous_toC.comp hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [structure_norm_toC, hn, pow_one]

/-- A continuous function of an entry with the same norm has the integral `0` against the entry
law when the entry has mean zero, if it is `u ↦ u` or `u ↦ star u`. -/
private lemma structure_integral_coord_zero (hM0 : M.MeanZero) (k a : Fin N) (p : Pair N) :
    ∫ u, structure_coord k a u ∂M.law p = 0 := by
  unfold structure_coord
  split_ifs
  · exact hM0 p
  · have : ∫ u, star u ∂M.law p = star (∫ u, u ∂M.law p) := integral_conj
    rw [this, hM0 p, star_zero]

/-- The expectation of a quadratic form `∑_{a,b} G_ab h_ka h_bk` in the row `k`: the off-diagonal
terms vanish by independence and mean zero, and `E|h_ka|² = σ_ka²`; the coefficients `G_ab` with
`a = k` or `b = k` are zero. -/
private lemma structure_integral_quadratic {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (k : Fin N) (G : Fin N → Fin N → ℂ) (hG : ∀ a b, (a = k ∨ b = k) → G a b = 0) :
    Integrable (fun y : rowsQ ({k} : Finset (Fin N)) → 𝕜 =>
        ∑ a, ∑ b, G a b * (structure_ua k a y * structure_va k b y))
        (Measure.pi fun p : rowsQ ({k} : Finset (Fin N)) => M.law p) ∧
      ∫ y : rowsQ ({k} : Finset (Fin N)) → 𝕜,
        ∑ a, ∑ b, G a b * (structure_ua k a y * structure_va k b y)
        ∂(Measure.pi fun p : rowsQ ({k} : Finset (Fin N)) => M.law p) =
      ∑ a, (M.var k a : ℂ) * G a a := by
  set ν := Measure.pi fun p : rowsQ ({k} : Finset (Fin N)) => M.law p with hν
  have hind : iIndepFun (fun (p : rowsQ ({k} : Finset (Fin N)))
      (y : rowsQ ({k} : Finset (Fin N)) → 𝕜) => y p) ν :=
    iIndepFun_pi (μ := fun p : rowsQ ({k} : Finset (Fin N)) => M.law p)
      (X := fun _ (z : 𝕜) => z) fun _ => aemeasurable_id
  have hφc : ∀ a, Continuous fun u : 𝕜 => toC (structure_coord k a u) := fun a =>
    structure_continuous_toC.comp (structure_continuous_coord k a)
  have hψc : ∀ a, Continuous fun u : 𝕜 => toC (star (structure_coord k a u)) := fun a =>
    structure_continuous_toC.comp (continuous_star.comp (structure_continuous_coord k a))
  have hua_cont : ∀ a, Continuous (structure_ua k a) := fun a =>
    (hφc a).comp (continuous_apply _)
  have hva_cont : ∀ a, Continuous (structure_va k a) := fun a =>
    (hψc a).comp (continuous_apply _)
  have hφi : ∀ a, Integrable (fun u : 𝕜 => toC (structure_coord k a u))
      (M.law (structure_pk k a)) := fun a =>
    structure_integrable_toC_comp M hM _ (structure_continuous_coord k a)
      (structure_norm_coord k a)
  have hψi : ∀ a, Integrable (fun u : 𝕜 => toC (star (structure_coord k a u)))
      (M.law (structure_pk k a)) := fun a =>
    structure_integrable_toC_comp M hM _ (continuous_star.comp (structure_continuous_coord k a))
      (fun u => by rw [norm_star, structure_norm_coord])
  have hua_int : ∀ a, Integrable (structure_ua k a) ν := fun a =>
    structure_integrable_coord M {k} (structure_pk k a) (hφi a)
  have hva_int : ∀ a, Integrable (structure_va k a) ν := fun a =>
    structure_integrable_coord M {k} (structure_pk k a) (hψi a)
  have hcoord_int : ∀ a, Integrable (structure_coord k a) (M.law (structure_pk k a)) := fun a =>
    (structure_integrable_norm_pow M hM _ 1).mono'
      (structure_continuous_coord k a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [structure_norm_coord, pow_one])
  have hcoord_int' : ∀ a, Integrable (fun u : 𝕜 => star (structure_coord k a u))
      (M.law (structure_pk k a)) := fun a =>
    (structure_integrable_norm_pow M hM _ 1).mono'
      (continuous_star.comp (structure_continuous_coord k a)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [norm_star, structure_norm_coord, pow_one])
  have hzero : toC (0 : 𝕜) = 0 := by apply Complex.ext <;> simp [toC]
  have hua_mean : ∀ a, ∫ y, structure_ua k a y ∂ν = 0 := fun a => by
    unfold structure_ua
    rw [structure_integral_coord M {k} (structure_pk k a) (hφc a).aestronglyMeasurable,
      structure_integral_toC (hcoord_int a), structure_integral_coord_zero M hM.meanZero, hzero]
  have hva_mean : ∀ a, ∫ y, structure_va k a y ∂ν = 0 := fun a => by
    unfold structure_va
    rw [structure_integral_coord M {k} (structure_pk k a) (hψc a).aestronglyMeasurable,
      structure_integral_toC (hcoord_int' a)]
    have : ∫ u, star (structure_coord k a u) ∂M.law (structure_pk k a) =
        star (∫ u, structure_coord k a u ∂M.law (structure_pk k a)) := integral_conj
    rw [this, structure_integral_coord_zero M hM.meanZero, star_zero, hzero]
  have hindep : ∀ a b, a ≠ b → IndepFun (structure_ua k a) (structure_va k b) ν := fun a b hab => by
    have hne : structure_pk k a ≠ structure_pk k b := fun h =>
      hab (structure_mk'_injective k (congrArg Subtype.val h))
    exact (hind.indepFun hne).comp (hφc a).measurable (hψc b).measurable
  have hoff : ∀ a b, a ≠ b → ∫ y, structure_ua k a y * structure_va k b y ∂ν = 0 :=
      fun a b hab => by
    rw [(hindep a b hab).integral_fun_mul_eq_mul_integral (hua_cont a).aestronglyMeasurable
      (hva_cont b).aestronglyMeasurable, hua_mean, zero_mul]
  have hoff_int : ∀ a b, a ≠ b → Integrable (fun y => structure_ua k a y * structure_va k b y) ν :=
    fun a b hab => (hindep a b hab).integrable_mul (hua_int a) (hva_int b)
  have hdiag_eq : ∀ (a : Fin N) (y : rowsQ ({k} : Finset (Fin N)) → 𝕜),
      structure_ua k a y * structure_va k a y = (((‖y (structure_pk k a)‖ ^ 2 : ℝ)) : ℂ) :=
    fun a y => by
    unfold structure_ua structure_va
    rw [structure_toC_mul_star, structure_norm_coord]
  have hdiag_int : ∀ a, Integrable (fun y => structure_ua k a y * structure_va k a y) ν :=
      fun a => by
    have hg : Integrable (fun u : 𝕜 => (((‖u‖ ^ 2 : ℝ)) : ℂ)) (M.law (structure_pk k a)) :=
      (structure_integrable_norm_pow M hM _ 2).ofReal
    exact (structure_integrable_coord M {k} (structure_pk k a) hg).congr
      (Filter.Eventually.of_forall fun y => (hdiag_eq a y).symm)
  have hdiag : ∀ a, ∫ y, structure_ua k a y * structure_va k a y ∂ν = (M.var k a : ℂ) := fun a => by
    simp only [hdiag_eq]
    rw [integral_complex_ofReal]
    have h := structure_integral_coord M {k} (structure_pk k a) (g := fun u : 𝕜 => ‖u‖ ^ 2)
      (measurable_norm.pow_const 2).aestronglyMeasurable
    have h' : ∫ y : rowsQ ({k} : Finset (Fin N)) → 𝕜, ‖y (structure_pk k a)‖ ^ 2 ∂ν =
        M.var k a := h
    rw [h']
  have hterm_int : ∀ a b, Integrable
      (fun y => G a b * (structure_ua k a y * structure_va k b y)) ν := fun a b => by
    by_cases h : a = k ∨ b = k
    · simp [hG a b h]
    · by_cases hab : a = b
      · subst hab
        exact (hdiag_int a).const_mul _
      · exact (hoff_int a b hab).const_mul _
  have hterm : ∀ a b, ∫ y, G a b * (structure_ua k a y * structure_va k b y) ∂ν =
      if a = b then (M.var k a : ℂ) * G a a else 0 := fun a b => by
    by_cases h : a = k ∨ b = k
    · have h0 : G a b = 0 := hG a b h
      split_ifs with hab
      · subst hab
        simp [h0]
      · simp [h0]
    · rw [integral_const_mul]
      split_ifs with hab
      · subst hab
        rw [hdiag]
        ring
      · rw [hoff a b hab, mul_zero]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hterm_int a b, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hterm_int a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hterm_int a b]
  simp only [hterm]
  simp

/-- The real part of an entry is integrable against the entry law. -/
private lemma structure_integrable_re {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) : Integrable (fun u : 𝕜 => ((RCLike.re u : ℝ) : ℂ)) (M.law p) :=
  (structure_integrable_norm_pow M hM p 1).mono'
    (Complex.continuous_ofReal.comp RCLike.continuous_re).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Complex.norm_real, Real.norm_eq_abs, pow_one]
      exact RCLike.abs_re_le_norm u)

/-- The real part of a mean-zero entry has expectation `0`. -/
private lemma structure_integral_re_zero {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (p : Pair N) : ∫ u : 𝕜, ((RCLike.re u : ℝ) : ℂ) ∂M.law p = 0 := by
  have hint : Integrable (fun u : 𝕜 => u) (M.law p) :=
    (structure_integrable_norm_pow M hM p 1).mono' aestronglyMeasurable_id
      (Filter.Eventually.of_forall fun u => by rw [pow_one])
  rw [integral_complex_ofReal, integral_re hint, hM.meanZero p]
  simp

end Expectation

end Entries

/-- Lemma 6.4 (d): `X_k = Q_k (1/G_kk)`. -/
theorem selfX_eq_rowInt {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) {z : ℂ} (hz : 0 < z.im) (k : Fin N) (x : Pair N → 𝕜) :
    selfX (toMatrix x) M.varMatrix z k =
      1 / green (toMatrix x) z k k - rowInt M {k} (fun w => 1 / green (toMatrix w) z k k) x := by
  have hA := toMatrix_isHermitian x
  set ν := Measure.pi fun p : rowsQ ({k} : Finset (Fin N)) => M.law p with hν
  have hG0 : ∀ a b, (a = k ∨ b = k) → greenT (toMatrix x) {k} z a b = 0 := fun a b h =>
    structure_greenT_of_mem (by simpa [Finset.mem_singleton] using h)
  have hslice : ∀ y : rowsQ ({k} : Finset (Fin N)) → 𝕜,
      1 / green (toMatrix (piMerge (rowsQ {k}) x y)) z k k =
        ((RCLike.re (y (structure_pk k k)) : ℝ) : ℂ) - z -
          ∑ a, ∑ b, greenT (toMatrix x) {k} z a b *
            (structure_ua k a y * structure_va k b y) := fun y => by
    have hAw := toMatrix_isHermitian (piMerge (rowsQ {k}) x y)
    rw [inv_green_diag hAw hz k, structure_toMatrix_merge_diag, structure_toC_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [structure_greenT_merge]
    by_cases h : a = k ∨ b = k
    · simp [hG0 a b h]
    · obtain ⟨h1, h2⟩ := not_or.1 h
      have hb : toMatrix (piMerge (rowsQ {k}) x y) b k =
          star (toMatrix (piMerge (rowsQ {k}) x y) k b) := (hAw.apply b k).symm
      rw [structure_toMatrix_merge_off k x y h1, hb, structure_toMatrix_merge_off k x y h2]
      unfold structure_ua structure_va
      ring
  have hrow : rowInt M {k} (fun w => 1 / green (toMatrix w) z k k) x =
      -z - ∑ l, (M.var k l : ℂ) * greenT (toMatrix x) {k} z l l := by
    change ∫ y, 1 / green (toMatrix (piMerge (rowsQ {k}) x y)) z k k ∂ν = _
    simp only [hslice]
    obtain ⟨hSint, hSval⟩ := structure_integral_quadratic M hM k (greenT (toMatrix x) {k} z) hG0
    have hSint' : Integrable (fun y : rowsQ ({k} : Finset (Fin N)) → 𝕜 =>
        ∑ a, ∑ b, greenT (toMatrix x) {k} z a b * (structure_ua k a y * structure_va k b y)) ν :=
      hSint
    have hSval' : ∫ y : rowsQ ({k} : Finset (Fin N)) → 𝕜,
        ∑ a, ∑ b, greenT (toMatrix x) {k} z a b * (structure_ua k a y * structure_va k b y) ∂ν =
        ∑ a, (M.var k a : ℂ) * greenT (toMatrix x) {k} z a a := hSval
    have hAint : Integrable (fun y : rowsQ ({k} : Finset (Fin N)) → 𝕜 =>
        ((RCLike.re (y (structure_pk k k)) : ℝ) : ℂ)) ν :=
      structure_integrable_coord M {k} _ (structure_integrable_re M hM _)
    have hAz : Integrable (fun y : rowsQ ({k} : Finset (Fin N)) → 𝕜 =>
        ((RCLike.re (y (structure_pk k k)) : ℝ) : ℂ) - z) ν :=
      hAint.sub (integrable_const z)
    have hAval : ∫ y : rowsQ ({k} : Finset (Fin N)) → 𝕜,
        ((RCLike.re (y (structure_pk k k)) : ℝ) : ℂ) ∂ν = 0 := by
      have h := structure_integral_coord M {k} (structure_pk k k)
        (g := fun u : 𝕜 => ((RCLike.re u : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp RCLike.continuous_re).aestronglyMeasurable
      have h' : ∫ y : rowsQ ({k} : Finset (Fin N)) → 𝕜,
          ((RCLike.re (y (structure_pk k k)) : ℝ) : ℂ) ∂ν = 0 :=
        h.trans (structure_integral_re_zero M hM _)
      exact h'
    rw [integral_sub hAz hSint', integral_sub hAint (integrable_const z), hAval, hSval',
      integral_const]
    simp
  rw [hrow, inv_green_diag hA hz k]
  unfold selfX selfZ
  simp only [Ensemble.varMatrix, Matrix.of_apply]
  ring

end Rigidity
