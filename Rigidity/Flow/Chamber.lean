module

public import Mathlib

@[expose] public section

/-!
# The Weyl chamber

The open Weyl chamber `Σ_N = {x_1 < ⋯ < x_N}` of §12.1 (numbers refer to the blueprint NP v1.1): it
is open and convex, its closure is the set of monotone tuples, and the file proves the divergence
theorem on it for fields vanishing on the walls (Lemma 16.1).
-/

open MeasureTheory Real
open scoped ENNReal NNReal

namespace Rigidity

/-- The open Weyl chamber `Σ_N = {x_1 < ⋯ < x_N}` (§12.1). -/
def chamber (N : ℕ) : Set (Fin N → ℝ) := {x | StrictMono x}

theorem isOpen_chamber (N : ℕ) : IsOpen (chamber N) := by
  have : chamber N = ⋂ i : Fin N, ⋂ j : Fin N, ⋂ _ : i < j, {x : Fin N → ℝ | x i < x j} := by
    ext x
    simp [chamber, StrictMono]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)

theorem convex_chamber (N : ℕ) : Convex ℝ (chamber N) := by
  intro x hx y hy a b ha hb hab i j hij
  have hxij : x i < x j := hx hij
  have hyij : y i < y j := hy hij
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : b = 1 := by linarith
    subst hb'
    simpa using hyij
  · nlinarith [mul_pos ha' (sub_pos.2 hxij), mul_nonneg hb (sub_pos.2 hyij).le]

theorem closure_chamber (N : ℕ) : closure (chamber N) = {x : Fin N → ℝ | Monotone x} := by
  apply Set.Subset.antisymm
  · have hcl : IsClosed {x : Fin N → ℝ | Monotone x} := by
      have : {x : Fin N → ℝ | Monotone x} =
          ⋂ i : Fin N, ⋂ j : Fin N, ⋂ _ : i ≤ j, {x : Fin N → ℝ | x i ≤ x j} := by
        ext x
        simp [Monotone]
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply i) (continuous_apply j)
    exact closure_minimal (fun x hx => hx.monotone) hcl
  · intro x hx
    let v : Fin N → ℝ := fun i => (i : ℝ)
    have hlim : Filter.Tendsto (fun ε : ℝ => x + ε • v) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      have : Filter.Tendsto (fun ε : ℝ => x + ε • v) (nhds 0) (nhds (x + (0 : ℝ) • v)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε i j hij
    have hε' : (0 : ℝ) < ε := hε
    have h1 : x i ≤ x j := hx hij.le
    have h2 : (i : ℝ) < j := by exact_mod_cast hij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, v]
    nlinarith

/-- The partial derivative `∂_i φ(x)` on `ℝ^N`. -/
noncomputable def pderiv {N : ℕ} (i : Fin N) (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  fderiv ℝ φ x (Pi.single i 1)

/-- `div Y(x) = ∑_i ∂_i Y_i(x)`. -/
noncomputable def divergence {N : ℕ} (Y : (Fin N → ℝ) → Fin N → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, fderiv ℝ Y x (Pi.single i 1) i

/-- The generator `L` (15.2):
`L = (βN)⁻¹ Δ + ∑_i (-x_i/2 + N⁻¹ ∑_{j ≠ i} (x_i - x_j)⁻¹) ∂_i`. -/
noncomputable def dysonGen (β : ℝ) (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  (β * N)⁻¹ * ∑ i, pderiv i (pderiv i φ) x +
    ∑ i, (-x i / 2 + (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) * pderiv i φ x

/-! ### Divergence theorem on `Σ_N` (NP §16, proof of Lemma 16.1)

The proof integrates `∂_iY_i` over `Σ_N` by Fubini along the lines parallel to `e_i` (each such
line meets `Σ_N` in an open convex subset of `ℝ`) for fields with compact support, and then removes
the support condition with the cut-offs `ψ m = φ(·/(m+1))`. -/

/-- An open convex subset of `ℝ` is empty, an open interval, an open ray, or `ℝ`. -/
private lemma isOpen_convex_real_cases {S : Set ℝ} (hS : IsOpen S) (hc : Convex ℝ S) :
    S = ∅ ∨ (∃ c d, S = Set.Ioo c d) ∨ (∃ c, S = Set.Ioi c) ∨ (∃ d, S = Set.Iio d) ∨
      S = Set.univ := by
  have h := hc.isPreconnected.mem_intervals
  have hint : S = interior S := hS.interior_eq.symm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨a, b, hab⟩ : ∃ a b, S = Set.Icc a b := ⟨_, _, h⟩
    have h2 := hint
    rw [hab, interior_Icc] at h2
    exact Or.inr (Or.inl ⟨a, b, hab.trans h2⟩)
  · obtain ⟨a, b, hab⟩ : ∃ a b, S = Set.Ico a b := ⟨_, _, h⟩
    have h2 := hint
    rw [hab, interior_Ico] at h2
    exact Or.inr (Or.inl ⟨a, b, hab.trans h2⟩)
  · obtain ⟨a, b, hab⟩ : ∃ a b, S = Set.Ioc a b := ⟨_, _, h⟩
    have h2 := hint
    rw [hab, interior_Ioc] at h2
    exact Or.inr (Or.inl ⟨a, b, hab.trans h2⟩)
  · exact Or.inr (Or.inl ⟨_, _, h⟩)
  · obtain ⟨a, hab⟩ : ∃ a, S = Set.Ici a := ⟨_, h⟩
    have h2 := hint
    rw [hab, interior_Ici] at h2
    exact Or.inr (Or.inr (Or.inl ⟨a, hab.trans h2⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨_, h⟩))
  · obtain ⟨a, hab⟩ : ∃ a, S = Set.Iic a := ⟨_, h⟩
    have h2 := hint
    rw [hab, interior_Iic] at h2
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hab.trans h2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inl h

/-- Fundamental theorem of calculus on an open convex subset `S ⊆ ℝ`, for a `C¹` function that
vanishes outside a compact set and on the frontier of `S`. -/
private lemma integral_deriv_eq_zero_of_isOpen_convex {S : Set ℝ} (hS : IsOpen S)
    (hc : Convex ℝ S) {h h' : ℝ → ℝ} (hd : ∀ r, HasDerivAt h (h' r) r) (hcont : Continuous h')
    {T : ℝ} (hT : ∀ r, T ≤ |r| → h r = 0) (hfr : ∀ r ∈ closure S \ S, h r = 0) :
    ∫ r in S, h' r = 0 := by
  have hh : Continuous h := continuous_iff_continuousAt.2 fun r => (hd r).continuousAt
  have hzero : ∀ r, T < |r| → h' r = 0 := by
    intro r hr
    have hev : h =ᶠ[nhds r] fun _ => (0 : ℝ) := by
      have : IsOpen {s : ℝ | T < |s|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [this.mem_nhds hr] with s hs using hT s hs.le
    exact (hd r).unique ((hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq hev)
  have hsupp : HasCompactSupport h' := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun r hr => ?_
    apply hzero
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hr
    rcases hr with hr | hr
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs r)
    · exact lt_of_lt_of_le hr (le_abs_self r)
  have hint : Integrable h' volume := hcont.integrable_of_hasCompactSupport hsupp
  have hbot : Filter.Tendsto h Filter.atBot (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_le_atBot (-|T|)] with r hr
    exact (hT r (le_trans (le_abs_self T) (le_trans (by linarith) (neg_le_abs r)))).symm
  have htop : Filter.Tendsto h Filter.atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop |T|] with r hr
    exact (hT r (le_trans (le_abs_self T) (le_trans hr (le_abs_self r)))).symm
  rcases isOpen_convex_real_cases hS hc with rfl | ⟨c, d, rfl⟩ | ⟨c, rfl⟩ | ⟨d, rfl⟩ | rfl
  · simp
  · rcases le_or_gt d c with hcd | hcd
    · simp [Set.Ioo_eq_empty_of_le hcd]
    · have hc0 : h c = 0 := hfr c ⟨by rw [closure_Ioo hcd.ne]; exact ⟨le_rfl, hcd.le⟩, by simp⟩
      have hd0 : h d = 0 := hfr d ⟨by rw [closure_Ioo hcd.ne]; exact ⟨hcd.le, le_rfl⟩, by simp⟩
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcd.le,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
          (hint.intervalIntegrable), hc0, hd0, sub_zero]
  · have hc0 : h c = 0 := hfr c ⟨by rw [closure_Ioi]; exact Set.mem_Ici.2 le_rfl, by simp⟩
    have := integral_Ioi_of_hasDerivAt_of_tendsto (a := c) hh.continuousWithinAt
      (fun r _ => hd r) hint.integrableOn htop
    rw [this, hc0, sub_zero]
  · have hd0 : h d = 0 := hfr d ⟨by rw [closure_Iio]; exact Set.mem_Iic.2 le_rfl, by simp⟩
    rw [← integral_Iic_eq_integral_Iio]
    have := integral_Iic_of_hasDerivAt_of_tendsto (a := d) hh.continuousWithinAt
      (fun r _ => hd r) hint.integrableOn hbot
    rw [this, hd0, sub_zero]
  · rw [Measure.restrict_univ]
    rw [integral_of_hasDerivAt_of_tendsto hd hint hbot htop, sub_zero]

/-- The function `x ↦ ∂_iY_i(x)` of a `C¹` field `Y` is continuous. -/
private lemma continuous_fderiv_apply {N : ℕ} {Y : (Fin N → ℝ) → Fin N → ℝ}
    (hY : ContDiff ℝ 1 Y) (i : Fin N) :
    Continuous fun x => fderiv ℝ Y x (Pi.single i 1) i :=
  (continuous_apply i).comp
    ((hY.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- The function `x ↦ ∂_iY_i(x)` has compact support when `Y` does. -/
private lemma hasCompactSupport_fderiv_apply {N : ℕ} {Y : (Fin N → ℝ) → Fin N → ℝ}
    (hsupp : HasCompactSupport Y) (i : Fin N) :
    HasCompactSupport fun x => fderiv ℝ Y x (Pi.single i 1) i :=
  (hsupp.fderiv ℝ).comp_left (g := fun L : (Fin N → ℝ) →L[ℝ] Fin N → ℝ =>
    L (Pi.single i 1) i) (by simp)

/-- Inserting the coordinate `r` at position `i` is affine in `r`, with direction `e_i`. -/
private lemma insertNth_eq_add {n : ℕ} (i : Fin (n + 1)) (r : ℝ) (y : Fin n → ℝ) :
    (Fin.insertNth i r y : Fin (n + 1) → ℝ) = Fin.insertNth i 0 y + r • Pi.single i 1 := by
  ext j
  refine Fin.succAboveCases i ?_ ?_ j
  · simp
  · intro k
    simp [Fin.succAbove_ne]

/-- `∫_{Σ_N} ∂_iY_i = 0` for a `C¹` field `Y` with compact support that vanishes on
`∂Σ_N = closure Σ_N \ Σ_N`. -/
private lemma integral_fderiv_chamber_eq_zero {n : ℕ} {Y : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hY : ContDiff ℝ 1 Y) (hsupp : HasCompactSupport Y)
    (hwall : ∀ x ∈ closure (chamber (n + 1)) \ chamber (n + 1), Y x = 0) (i : Fin (n + 1)) :
    ∫ x in chamber (n + 1), fderiv ℝ Y x (Pi.single i 1) i = 0 := by
  obtain ⟨R, -, hR⟩ := hsupp.exists_pos_le_norm
  set g : (Fin (n + 1) → ℝ) → ℝ := fun x => fderiv ℝ Y x (Pi.single i 1) i with hg
  have hgc : Continuous g := continuous_fderiv_apply hY i
  have hgsupp : HasCompactSupport g := hasCompactSupport_fderiv_apply hsupp i
  have hmeas : MeasurableSet (chamber (n + 1)) := (isOpen_chamber _).measurableSet
  have hF : Integrable (Set.indicator (chamber (n + 1)) g) volume :=
    (hgc.integrable_of_hasCompactSupport hgsupp).indicator hmeas
  rw [← integral_indicator hmeas]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have hmp : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
  rw [← hmp.integral_comp' (Set.indicator (chamber (n + 1)) g)]
  have hFi : Integrable (fun p => Set.indicator (chamber (n + 1)) g (e.symm p)) volume :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod] at hFi ⊢
  rw [integral_prod_symm _ hFi]
  have hslice : ∀ y : Fin n → ℝ,
      ∫ r, Set.indicator (chamber (n + 1)) g (e.symm (r, y)) = 0 := by
    intro y
    set p : Fin (n + 1) → ℝ := Fin.insertNth i 0 y with hp
    set ℓ : ℝ → (Fin (n + 1) → ℝ) := fun r => Fin.insertNth i r y with hℓ
    have hℓp : ∀ r, ℓ r = p + r • (Pi.single i 1 : Fin (n + 1) → ℝ) := fun r =>
      insertNth_eq_add i r y
    have hℓe : ∀ r, e.symm (r, y) = ℓ r := by
      intro r
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, ℓ]
    have hℓd : ∀ r, HasDerivAt ℓ (Pi.single i 1 : Fin (n + 1) → ℝ) r := by
      intro r
      have h1 : ℓ = fun r : ℝ => p + r • (Pi.single i 1 : Fin (n + 1) → ℝ) := funext hℓp
      rw [h1]
      simpa using ((hasDerivAt_id r).smul_const (Pi.single i 1 : Fin (n + 1) → ℝ)).const_add p
    have hℓc : Continuous ℓ := continuous_iff_continuousAt.2 fun r => (hℓd r).continuousAt
    set S : Set ℝ := ℓ ⁻¹' chamber (n + 1) with hS
    have hSopen : IsOpen S := (isOpen_chamber _).preimage hℓc
    have hSconv : Convex ℝ S := by
      intro r₁ hr₁ r₂ hr₂ a b ha hb hab
      have := convex_chamber (n + 1) hr₁ hr₂ ha hb hab
      have hl : ℓ (a • r₁ + b • r₂) = a • ℓ r₁ + b • ℓ r₂ := by
        ext j
        have hb' : b = 1 - a := by linarith
        rw [hℓp, hℓp, hℓp]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        subst hb'
        ring
      change ℓ (a • r₁ + b • r₂) ∈ chamber (n + 1)
      rw [hl]
      exact this
    have hind : ∀ r, Set.indicator (chamber (n + 1)) g (e.symm (r, y)) =
        S.indicator (fun r => g (ℓ r)) r := by
      intro r
      rw [hℓe]
      by_cases hr : ℓ r ∈ chamber (n + 1)
      · have hr' : r ∈ S := hr
        simp [Set.indicator_of_mem hr, Set.indicator_of_mem hr']
      · have hr' : r ∉ S := hr
        simp [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr']
    simp_rw [hind]
    rw [integral_indicator hSopen.measurableSet]
    refine integral_deriv_eq_zero_of_isOpen_convex hSopen hSconv
      (h := fun r => Y (ℓ r) i) (h' := fun r => g (ℓ r)) ?_ (hgc.comp hℓc)
      (T := R + ‖p‖ + 1) ?_ ?_
    · intro r
      have h1 : HasDerivAt (Y ∘ ℓ) (fderiv ℝ Y (ℓ r) (Pi.single i 1)) r :=
        ((hY.differentiable (by norm_num) (ℓ r)).hasFDerivAt).comp_hasDerivAt r (hℓd r)
      exact hasDerivAt_pi.1 h1 i
    · intro r hr
      apply congrFun (hR (ℓ r) ?_) i
      have h1 : ‖ℓ r i‖ ≤ ‖ℓ r‖ := norm_le_pi_norm (ℓ r) i
      have h2 : ℓ r i = p i + r := by
        rw [hℓp]
        simp
      have h3 : ‖p i‖ ≤ ‖p‖ := norm_le_pi_norm _ i
      have h4 : |r| ≤ |p i| + |ℓ r i| := by
        rw [h2]
        calc |r| = |(p i + r) + (-p i)| := by ring_nf
          _ ≤ _ := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_neg, add_comm]
      rw [Real.norm_eq_abs] at h1 h3
      linarith
    · intro r hr
      apply congrFun (hwall (ℓ r) ?_) i
      refine ⟨?_, hr.2⟩
      have := image_closure_subset_closure_image (f := ℓ) hℓc ⟨r, hr.1, rfl⟩
      exact closure_mono (Set.image_preimage_subset ℓ _) this
  simp_rw [hslice]
  simp

/-- `∫_{Σ_N} div Y = 0` for a `C¹` field `Y` with compact support that vanishes on
`∂Σ_N`. -/
private lemma integral_divergence_chamber_of_hasCompactSupport {n : ℕ}
    {Y : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hY : ContDiff ℝ 1 Y) (hsupp : HasCompactSupport Y)
    (hwall : ∀ x ∈ closure (chamber (n + 1)) \ chamber (n + 1), Y x = 0) :
    ∫ x in chamber (n + 1), divergence Y x = 0 := by
  unfold divergence
  rw [integral_finsetSum]
  · simp [integral_fderiv_chamber_eq_zero hY hsupp hwall]
  · intro i _
    exact ((continuous_fderiv_apply hY i).integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hsupp i)).integrableOn

/-- Lemma 16.1: divergence theorem on `Σ_N` for fields vanishing on the walls. -/
theorem integral_divergence_chamber {N : ℕ} {Y : (Fin N → ℝ) → Fin N → ℝ}
    (hY : ContDiff ℝ 1 Y) (hwall : ∀ x ∈ closure (chamber N) \ chamber N, Y x = 0)
    (hint : IntegrableOn (fun x => ∑ i, |Y x i|) (chamber N))
    (hdiv : IntegrableOn (divergence Y) (chamber N)) :
    ∫ x in chamber N, divergence Y x = 0 := by
  rcases N with _ | n
  · simp [divergence]
  -- a fixed bump function and its dilations `ψ m`
  let φ : ContDiffBump (0 : Fin (n + 1) → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set c : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hc
  have hcpos : ∀ m, 0 < c m := fun m => by positivity
  set ψ : ℕ → (Fin (n + 1) → ℝ) → ℝ := fun m x => φ (c m • x) with hψdef
  have hφ : ContDiff ℝ 1 φ := φ.contDiff
  have hψ : ∀ m, ContDiff ℝ 1 (ψ m) := fun m =>
    hφ.comp (contDiff_const_smul (c m))
  have hψd : ∀ m x, HasFDerivAt (ψ m)
      ((fderiv ℝ φ (c m • x)).comp (c m • ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ))) x :=
    fun m x => HasFDerivAt.comp (g := (φ : (Fin (n + 1) → ℝ) → ℝ))
      (f := fun y : Fin (n + 1) → ℝ => c m • y) x
      ((hφ.differentiable (by norm_num) _).hasFDerivAt)
      ((hasFDerivAt_id x).const_smul (c m))
  have hψone : ∀ (m : ℕ) (x : Fin (n + 1) → ℝ), ‖x‖ ≤ (m : ℝ) + 1 → ψ m x = 1 := by
    intro m x hx
    apply φ.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos m)]
    have : (0 : ℝ) < m + 1 := by positivity
    change 1 / ((m : ℝ) + 1) * ‖x‖ ≤ 1
    rw [one_div, inv_mul_le_iff₀ this]
    linarith
  have hψzero : ∀ (m : ℕ) (x : Fin (n + 1) → ℝ), 2 * ((m : ℝ) + 1) ≤ ‖x‖ → ψ m x = 0 := by
    intro m x hx
    apply φ.zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos m)]
    have : (0 : ℝ) < m + 1 := by positivity
    change 2 ≤ 1 / ((m : ℝ) + 1) * ‖x‖
    rw [one_div, inv_mul_eq_div, le_div_iff₀ this]
    linarith
  have hψnn : ∀ m x, 0 ≤ ψ m x := fun m x => φ.nonneg
  have hψle : ∀ m x, ψ m x ≤ 1 := fun m x => φ.le_one
  -- a uniform bound on the derivative of the bump function
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y, ‖fderiv ℝ φ y‖ ≤ M :=
    (hφ.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      (φ.hasCompactSupport.fderiv ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hdψ : ∀ m x (i : Fin (n + 1)), |fderiv ℝ (ψ m) x (Pi.single i 1)| ≤ M * c m := by
    intro m x i
    rw [(hψd m x).fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    calc |fderiv ℝ φ (c m • x) (c m • Pi.single i 1)|
        ≤ ‖fderiv ℝ φ (c m • x)‖ * ‖c m • (Pi.single i 1 : Fin (n + 1) → ℝ)‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * c m := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcpos m), Pi.norm_single, norm_one,
            mul_one]
          exact mul_le_mul_of_nonneg_right (hM _) (hcpos m).le
  -- the cut-off fields
  set Z : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun m x => ψ m x • Y x with hZ
  have hZc : ∀ m, ContDiff ℝ 1 (Z m) := fun m => (hψ m).smul hY
  have hZsupp : ∀ m, HasCompactSupport (Z m) := by
    intro m
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin (n + 1) → ℝ)
      (2 * ((m : ℝ) + 1))) fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    simp only [hZ, hψzero m x hx.le, zero_smul]
  have hZwall : ∀ m, ∀ x ∈ closure (chamber (n + 1)) \ chamber (n + 1), Z m x = 0 := by
    intro m x hx
    simp only [hZ, hwall x hx, smul_zero]
  have hZ0 : ∀ m, ∫ x in chamber (n + 1), divergence (Z m) x = 0 := fun m =>
    integral_divergence_chamber_of_hasCompactSupport (hZc m) (hZsupp m) (hZwall m)
  -- product rule
  have hprod : ∀ m x, divergence (Z m) x = ψ m x * divergence Y x +
      ∑ i, fderiv ℝ (ψ m) x (Pi.single i 1) * Y x i := by
    intro m x
    have h1 := ((hψ m).differentiable (by norm_num) x).hasFDerivAt.smul
      ((hY.differentiable (by norm_num) x).hasFDerivAt)
    have h2 : fderiv ℝ (Z m) x = ψ m x • fderiv ℝ Y x + (fderiv ℝ (ψ m) x).smulRight (Y x) :=
      h1.fderiv
    unfold divergence
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2]
    simp
  -- measurability and integrability of the pieces
  have hdivc : Continuous (divergence Y) :=
    continuous_finsetSum _ fun i _ => continuous_fderiv_apply hY i
  have hYc : Continuous Y := hY.continuous
  set Φ : ℕ → (Fin (n + 1) → ℝ) → ℝ := fun m x =>
    ∑ i, fderiv ℝ (ψ m) x (Pi.single i 1) * Y x i with hΦ
  have hΦc : ∀ m, Continuous (Φ m) := fun m =>
    continuous_finsetSum _ fun i _ =>
      (((hψ m).continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
        ((continuous_apply i).comp hYc)
  have hAint : ∀ m, IntegrableOn (fun x => ψ m x * divergence Y x) (chamber (n + 1)) := by
    intro m
    refine Integrable.mono' hdiv.norm ((hψ m).continuous.mul hdivc).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs (ψ m x), abs_of_nonneg (hψnn m x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψle m x)
  have hΦbound : ∀ m x, ‖Φ m x‖ ≤ M * c m * ∑ i, |Y x i| := by
    intro m x
    calc ‖Φ m x‖ ≤ ∑ i, ‖fderiv ℝ (ψ m) x (Pi.single i 1) * Y x i‖ := norm_sum_le _ _
      _ ≤ ∑ i, M * c m * |Y x i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hdψ m x i) (abs_nonneg _)
      _ = M * c m * ∑ i, |Y x i| := by rw [Finset.mul_sum]
  have hBint : ∀ m, IntegrableOn (Φ m) (chamber (n + 1)) := by
    intro m
    refine Integrable.mono' (hint.const_mul (M * c m)) (hΦc m).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => hΦbound m x
  set A : ℕ → ℝ := fun m => ∫ x in chamber (n + 1), ψ m x * divergence Y x with hA
  set B : ℕ → ℝ := fun m => ∫ x in chamber (n + 1), Φ m x with hB
  have hAB : ∀ m, A m + B m = 0 := by
    intro m
    have h := hZ0 m
    simp_rw [hprod] at h
    rw [integral_add (hAint m) (hBint m)] at h
    exact h
  have hAlim : Filter.Tendsto A Filter.atTop
      (nhds (∫ x in chamber (n + 1), divergence Y x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖divergence Y x‖)
      ?_ ?_ hdiv.norm ?_
    · exact Filter.Eventually.of_forall fun m => (hAint m).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun m => Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs (ψ m x), abs_of_nonneg (hψnn m x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψle m x)
    · refine Filter.Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨⌈‖x‖⌉₊, fun m hm => ?_⟩)
      have hx : ‖x‖ ≤ (m : ℝ) + 1 := by
        have := Nat.le_ceil ‖x‖
        have : (⌈‖x‖⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      change divergence Y x = ψ m x * divergence Y x
      rw [hψone m x hx, one_mul]
  have hBlim : Filter.Tendsto B Filter.atTop (nhds 0) := by
    set K : ℝ := ∫ x in chamber (n + 1), ∑ i, |Y x i| with hK
    have hBle : ∀ m, ‖B m‖ ≤ M * c m * K := by
      intro m
      calc ‖B m‖ ≤ ∫ x in chamber (n + 1), M * c m * ∑ i, |Y x i| :=
            norm_integral_le_of_norm_le (hint.const_mul _)
              (Filter.Eventually.of_forall fun x => hΦbound m x)
        _ = M * c m * K := integral_const_mul _ _
    have hc0 : Filter.Tendsto c Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Filter.Tendsto (fun m => M * c m * K) Filter.atTop (nhds (M * 0 * K)) :=
      (hc0.const_mul M).mul_const K
    exact squeeze_zero_norm hBle (by simpa using h1)
  have hsum := hAlim.add hBlim
  have h0 : (fun m => A m + B m) = fun _ => (0 : ℝ) := funext hAB
  rw [h0] at hsum
  have := tendsto_nhds_unique tendsto_const_nhds hsum
  linarith


end Rigidity
