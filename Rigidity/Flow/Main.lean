module

public import Rigidity.Ensemble.Basic
public import Rigidity.Flow.Correlation
public import Rigidity.Flow.Ensembles
public import Rigidity.Flow.GapUniv
public import Rigidity.Flow.GoodEvent
public import Rigidity.Flow.GoodSet

@[expose] public section

/-!
# The quantitative local ergodicity bound (Theorem 12.1), conditional on the rigidity bound

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

`dbm_quantitative_of_rigidityBound` is Theorem 12.1, (12.4), for one tuple `(A₀, C_R, c_R, φ, N₀)`
of constants of the rigidity bound of Theorem 2.2 at the parameters
`(tildeTheta ϑ, tildeDelta δ₋, tildeDelta δ₊, tildeC C₀)`, given as the hypothesis
`RigidityBound`.  The constants of §19.3 are:
* `exists_Nq`: (i), the threshold beyond which `N ≥ 16`, `2 ≤ D ≤ N^{1/5} + 2 ≤ N` and
  `(D + ℓ)/(N ϱ_*) ≤ c/8`;
* `corrC_le_two`: (iii), `C_{N,n} ≤ 2` for `n² ≤ N`;
* `Dpar_pow_le`: (v), `D^n (log N)^{1/2} ≤ 3^n e^{(n A₀ + 1)(log log N)²}`.

The proof is that of §19.4.  Step 1 is Fubini in `E'`: the integrand `(E', x) ↦ 𝒳^O_{E',ϱ}(x)` is
jointly continuous and dominated by the constant `N^n ‖O‖_∞`, so `corrLHS` equals
`(2b)⁻¹ C_{N,n} |𝔼_{ν_t} 𝒵 - 𝔼_μ 𝒵|` with `𝒵(x) = ∫_{E-b}^{E+b} 𝒳^O_{E',ϱ}(x) dE'`.  Step 2
(`b < 1/N`) is the trivial bound on the good set `Ξ` (13.3) and on its complement.  Steps 3–6
(`b ≥ 1/N`) use Lemma 19.3, the bound on `Ξᶜ` with `K = n + 2`, and Proposition 19.1 for each
index tuple; `ν_t = M.eigLaw t` and `μ = gbeLaw` are carried by the chamber `Σ_N`
(Theorem 16.3), so the extension by `0` in Proposition 19.1 does not change the expectations.
Step 7 collects the terms and applies (v).  Here `ϱ_* = rhoStar c`, `ℓ = max(1, ρ_O/ϱ_*)` and
`ϱ = ϱ_sc(E) ≥ ϱ_*`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
open scoped NNReal

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


private lemma Main_rhoStar_pos {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) : 0 < rhoStar c := by
  unfold rhoStar
  have : 0 < c - c ^ 2 / 16 := by nlinarith
  have := Real.sqrt_pos.2 this
  positivity

/-- For `N ≥ 16`, `D = e^{A₀ (log log N)²} + 2` (13.2). -/
private lemma Main_Dpar_eq {A₀ : ℝ} {N : ℕ} (hN : 16 ≤ N) :
    Dpar A₀ N = Real.exp (A₀ * Real.log (Real.log N) ^ 2) + 2 := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  unfold Dpar
  rw [Real.rpow_def_of_pos hlog]
  ring_nf

/-- Eventually `A (log log N)² ≤ ε log N`. -/
private lemma Main_eventually_loglog {A ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, A * Real.log (Real.log N) ^ 2 ≤ ε * Real.log N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA : 0 < (|A| + 1) / ε := by positivity
  have h := Real.isLittleO_pow_log_id_atTop (n := 2) |>.def (show 0 < ε / (|A| + 1) by positivity)
  filter_upwards [hlog.eventually h, hlog.eventually (eventually_ge_atTop 0)] with N hN hN0
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hN0,
    abs_of_nonneg (sq_nonneg (Real.log (Real.log N)))] at hN
  have h1 : A * Real.log (Real.log N) ^ 2 ≤ (|A| + 1) * Real.log (Real.log N) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) (sq_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ |A| + 1)
  have h3 : (|A| + 1) * (ε / (|A| + 1) * Real.log N) = ε * Real.log N := by
    field_simp
  linarith

/-- If `T ≥ 0` and `T^5 ≤ N`, then `T ≤ N^{1/5}`; and `(N^{1/5})^5 = N`. -/
private lemma Main_rpow_fifth {N : ℕ} :
    ((N : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

private lemma Main_le_rpow_fifth {N : ℕ} {T : ℝ} (h : T ^ 5 ≤ N) :
    T ≤ (N : ℝ) ^ (1 / 5 : ℝ) := by
  by_contra hlt
  push Not at hlt
  have h0 : 0 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := pow_lt_pow_left₀ hlt h0 (by norm_num : (5 : ℕ) ≠ 0)
  rw [Main_rpow_fifth] at this
  linarith

/-- NP §19.3 (i): for all `A₀`, `ℓ` and `0 < c ≤ 2` there is a threshold `N_c` such that for
`N ≥ N_c`: `N ≥ 16`, `2 ≤ D ≤ N^{1/5} + 2 ≤ N` and `(D + ℓ)/(N ϱ_*) ≤ c/8` (the hypothesis of
Lemma 13.4), where `D = Dpar A₀ N` is the parameter (13.2) and `ϱ_* = rhoStar c`. -/
theorem exists_Nq (A₀ ℓ : ℝ) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) :
    ∃ Nc : ℕ, ∀ N : ℕ, Nc ≤ N → 16 ≤ N ∧ 2 ≤ Dpar A₀ N ∧
      Dpar A₀ N ≤ (N : ℝ) ^ (1 / 5 : ℝ) + 2 ∧ (N : ℝ) ^ (1 / 5 : ℝ) + 2 ≤ N ∧
      (Dpar A₀ N + ℓ) / (N * rhoStar c) ≤ c / 8 := by
  have hρ := Main_rhoStar_pos hc hc2
  set κ : ℝ := c * rhoStar c / 8 with hκ
  have hκ0 : 0 < κ := by positivity
  set T : ℝ := max 2 (2 / κ + 1)
  have hT2 : 2 ≤ T := le_max_left _ _
  have hT3 : 2 / κ + 1 ≤ T := le_max_right _ _
  have h1 := Main_eventually_loglog (A := A₀) (show (0 : ℝ) < 1 / 5 by norm_num)
  have h2 : ∀ᶠ N : ℕ in atTop, T ^ 5 ≤ (N : ℝ) ∧ (2 + ℓ) * 2 / κ ≤ (N : ℝ) ∧ (16 : ℝ) ≤ N := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    filter_upwards [this.eventually_ge_atTop (T ^ 5), this.eventually_ge_atTop ((2 + ℓ) * 2 / κ),
      this.eventually_ge_atTop 16] with N a b c
    exact ⟨a, b, c⟩
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨Nc, fun N hN => ?_⟩
  obtain ⟨hl, hT5, hN2, hN16⟩ := hNc N hN
  have hN16' : 16 ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set y : ℝ := (N : ℝ) ^ (1 / 5 : ℝ) with hy
  have hy5 : y ^ 5 = N := Main_rpow_fifth
  have hyT : T ≤ y := Main_le_rpow_fifth hT5
  have hD : Dpar A₀ N = Real.exp (A₀ * Real.log (Real.log N) ^ 2) + 2 := Main_Dpar_eq hN16'
  have hexp : Real.exp (A₀ * Real.log (Real.log N) ^ 2) ≤ y := by
    rw [hy, Real.rpow_def_of_pos hNpos]
    exact Real.exp_le_exp.2 (by linarith)
  have hDy : Dpar A₀ N ≤ y + 2 := by rw [hD]; linarith
  have hy1 : 1 ≤ y := by linarith
  have hy4 : y ≤ y ^ 4 := by
    calc y = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have hyN : y + 2 ≤ N := by
    rw [← hy5]
    have : 16 * y ≤ y ^ 5 := by
      have : (2 : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      nlinarith
    linarith
  refine ⟨hN16', ?_, hDy, hyN, ?_⟩
  · rw [hD]; linarith [Real.exp_pos (A₀ * Real.log (Real.log N) ^ 2)]
  · rw [div_le_iff₀ (by positivity)]
    have hyκ : y ≤ κ * N / 2 := by
      rw [← hy5]
      have : 2 / κ ≤ y ^ 4 := by linarith
      have h' : 2 ≤ κ * y ^ 4 := by
        rw [div_le_iff₀ hκ0] at this
        linarith
      nlinarith
    have hℓκ : 2 + ℓ ≤ κ * N / 2 := by
      rw [div_le_iff₀ hκ0] at hN2
      linarith
    have : c / 8 * (N * rhoStar c) = κ * N := by rw [hκ]; ring
    rw [this]
    linarith

/-- NP §19.3 (iii): `C_{N,n} = N^n (N - n)!/N! ≤ 2` for `1 ≤ n` and `n² ≤ N`. -/
theorem corrC_le_two {N n : ℕ} (hn : 1 ≤ n) (hnN : n ^ 2 ≤ N) : corrC N n ≤ 2 := by
  have hnN' : n ≤ N := by nlinarith
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  -- `N^k (1 - k(k-1)/(2N)) ≤ N (N-1) ⋯ (N-k+1)` for `k ≤ N`
  have key : ∀ k : ℕ, k ≤ N →
      (N : ℝ) ^ k * (1 - (k : ℝ) * (k - 1) / (2 * N)) ≤ (N.descFactorial k : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
      have hNk : (0 : ℝ) ≤ (N : ℝ) - k := by
        have : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
        linarith
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hs : 0 ≤ (k : ℝ) * (k - 1) / (2 * N) := by
        rcases Nat.eq_zero_or_pos k with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ k := by exact_mod_cast h
          positivity
      calc (N : ℝ) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) - 1) / (2 * N))
          = (N : ℝ) ^ k * ((N - k) - N * ((k : ℝ) * (k - 1) / (2 * N))) := by
            push_cast; field_simp; ring
        _ ≤ (N : ℝ) ^ k * ((N - k) * (1 - (k : ℝ) * (k - 1) / (2 * N))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith
        _ = ((N : ℝ) - k) * ((N : ℝ) ^ k * (1 - (k : ℝ) * (k - 1) / (2 * N))) := by ring
        _ ≤ ((N : ℝ) - k) * (N.descFactorial k : ℝ) := mul_le_mul_of_nonneg_left ih' hNk
  have h := key n hnN'
  have hhalf : (1 : ℝ) / 2 ≤ 1 - (n : ℝ) * (n - 1) / (2 * N) := by
    have : (n : ℝ) ^ 2 ≤ N := by exact_mod_cast hnN
    have : (n : ℝ) * (n - 1) / (2 * N) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    linarith
  have hdf : ((N - n).factorial : ℝ) * N.descFactorial n = N.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hnN'
  have hfpos : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNn : (0 : ℝ) < (N : ℝ) ^ n := by positivity
  unfold corrC
  rw [div_le_iff₀ hfpos, ← hdf]
  have hf0 : (0 : ℝ) < (N - n).factorial := by exact_mod_cast Nat.factorial_pos _
  have : (N : ℝ) ^ n ≤ 2 * N.descFactorial n := by nlinarith
  nlinarith

/-- NP §19.3 (v): for `N ≥ 16` and `A₀ ≥ 0`, `D^n (log N)^{1/2} ≤ 3^n e^{A₁ (log log N)²}` with
`A₁ = n A₀ + 1`, where `D = Dpar A₀ N` (13.2). -/
theorem Dpar_pow_le {A₀ : ℝ} {N : ℕ} (hN : 16 ≤ N) (hA₀ : 0 ≤ A₀) (n : ℕ) :
    Dpar A₀ N ^ n * Real.sqrt (Real.log N) ≤
      3 ^ n * Real.exp ((n * A₀ + 1) * Real.log (Real.log N) ^ 2) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  set L := Real.log (Real.log N) with hL
  have hD := Main_Dpar_eq (A₀ := A₀) hN
  have he1 : 1 ≤ Real.exp (A₀ * L ^ 2) := Real.one_le_exp (by positivity)
  have hD3 : Dpar A₀ N ≤ 3 * Real.exp (A₀ * L ^ 2) := by rw [hD]; linarith
  have hD0 : 0 ≤ Dpar A₀ N := by rw [hD]; positivity
  -- `log log N ≥ 1/2`
  have hL2 : 1 / 2 ≤ L := by
    have h16 : (2 : ℝ) ≤ Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    have he : Real.exp (1 / 2) ≤ 2 := by
      have h := Real.exp_one_lt_d9
      have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    rw [hL, Real.le_log_iff_exp_le hlog]
    exact he.trans (h16.trans (Real.log_le_log (by norm_num) hNr))
  have hsq : Real.sqrt (Real.log N) ≤ Real.exp (L ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlog, ← hL]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Dpar A₀ N ^ n * Real.sqrt (Real.log N)
      ≤ (3 * Real.exp (A₀ * L ^ 2)) ^ n * Real.exp (L ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ hD0 hD3 n) hsq (Real.sqrt_nonneg _) (by positivity)
    _ = 3 ^ n * Real.exp ((n * A₀ + 1) * L ^ 2) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        ring_nf


/-! ### Step 1: Fubini in `E'` -/

private lemma Main_isProbabilityMeasure_gbeLaw (N : ℕ) : IsProbabilityMeasure (gbeLaw 𝕜 N) := by
  have : IsProbabilityMeasure (gaussH 𝕜 N) := gaussE_isProbabilityMeasure _
  exact (Measure.isProbabilityMeasure_map_iff (continuous_eigVec N).measurable.aemeasurable).2
    inferInstance

private lemma Main_isProbabilityMeasure_eigLaw {N : ℕ} (M : Ensemble 𝕜 N) (t : ℝ) :
    IsProbabilityMeasure (M.eigLaw t) := by
  have hρ : IsProbabilityMeasure M.hermLaw := by
    unfold Ensemble.hermLaw
    exact (Measure.isProbabilityMeasure_map_iff
      (Herm.measurable_ofPair (𝕜 := 𝕜) N).aemeasurable).2 inferInstance
  have := gaussE_isProbabilityMeasure (E := Herm 𝕜 N) (gaussVar 𝕜 N)
  unfold Ensemble.eigLaw eigFlow ouLaw
  infer_instance

/-- A bounded continuous function is integrable for a finite measure. -/
private lemma Main_integrable_of_bound {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hf : Continuous f)
    {C : ℝ} (h : ∀ x, |f x| ≤ C) : Integrable f ν :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ fun x => h x)⟩

/-- `𝒵(x) = ∫_{E-b}^{E+b} 𝒳^O_{E',ϱ}(x) dE'` (§19.4, Step 1). -/
private noncomputable def Main_Z {N n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (E b ϱ : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∫ E' in (E - b)..(E + b), corrX O E' ϱ x

private lemma Main_continuous_Z {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} (hO : Continuous O)
    (E b ϱ : ℝ) : Continuous (Main_Z (N := N) O E b ϱ) := by
  unfold Main_Z
  have h := continuous_corrX (N := N) hO ϱ
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x E' => corrX O E' ϱ x) (h.comp continuous_swap) _ _

/-- `|𝒵| ≤ 2b N^n ‖O‖_∞` (Lemma 19.2 (d)). -/
private lemma Main_abs_Z_le {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hB : ∀ α, |O α| ≤ B) {E b : ℝ} (hb : 0 < b) (ϱ : ℝ) (x : Fin N → ℝ) :
    |Main_Z O E b ϱ x| ≤ 2 * b * ((N : ℝ) ^ n * B) := by
  unfold Main_Z
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := E - b) (b := E + b)
    (C := (N : ℝ) ^ n * B) (f := fun E' => corrX O E' ϱ x)
    (fun E' _ => by rw [Real.norm_eq_abs]; exact abs_corrX_le hB E' ϱ x)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [show E + b - (E - b) = 2 * b by ring, abs_of_pos (by positivity)]
  ring

/-- On `Ξ`, `|𝒵| ≤ 2b K_ℓ^n ‖O‖_∞` (Lemma 19.3 (a)). -/
private lemma Main_abs_Z_le_of_mem {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B ρO ℓ ϱ D c E b : ℝ} (hN : 3 ≤ N) (hD : 0 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ)
    (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) (hB : ∀ α, |O α| ≤ B)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) (hE : E ∈ Set.Icc (-2 + c) (2 - c)) (hb : 0 < b) (hb2 : b < c / 2)
    {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) :
    |Main_Z O E b ϱ x| ≤ 2 * b * ((2 * ℓ / π + 2 * D) ^ n * B) := by
  unfold Main_Z
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := E - b) (b := E + b)
    (C := (2 * ℓ / π + 2 * D) ^ n * B) (f := fun E' => corrX O E' ϱ x) (fun E' hE' => by
      rw [Real.norm_eq_abs]
      rw [Set.uIoc_of_le (by linarith)] at hE'
      refine abs_corrX_le_of_mem_flowGoodSet hN hD hc hc2 hℓ hH hB hsupp hϱ hρℓ hx ?_
      obtain ⟨h1, h2⟩ := hE'
      obtain ⟨h3, h4⟩ := hE
      constructor <;> linarith)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [show E + b - (E - b) = 2 * b by ring, abs_of_pos (by positivity)]
  ring

/-- Fubini in `E'` (§19.4, Step 1): `∫_{E-b}^{E+b} 𝔼_ν 𝒳 dE' = 𝔼_ν 𝒵`, with the bounded joint
integrand `(E', x) ↦ 𝒳^O_{E',ϱ}(x)` (dominated by the constant `N^n ‖O‖_∞`). -/
private lemma Main_fubini {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hO : Continuous O) (hB : ∀ α, |O α| ≤ B) {E b : ℝ} (hb : 0 < b) (ϱ : ℝ)
    (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν] :
    IntervalIntegrable (fun E' => ∫ x, corrX O E' ϱ x ∂ν) volume (E - b) (E + b) ∧
    (∫ E' in (E - b)..(E + b), ∫ x, corrX O E' ϱ x ∂ν) = ∫ x, Main_Z O E b ϱ x ∂ν := by
  have hab : E - b ≤ E + b := by linarith
  set μE : Measure ℝ := volume.restrict (Set.Ioc (E - b) (E + b)) with hμE
  have : IsFiniteMeasure μE := by
    rw [hμE]
    exact isFiniteMeasure_restrict.2 (measure_Ioc_lt_top).ne
  have hint : Integrable (Function.uncurry fun E' (x : Fin N → ℝ) => corrX O E' ϱ x)
      (μE.prod ν) :=
    Main_integrable_of_bound (continuous_corrX hO ϱ) (fun p => abs_corrX_le hB p.1 ϱ p.2)
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint.integral_prod_left
  · rw [intervalIntegral.integral_of_le hab, integral_integral_swap hint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Main_Z]
    rw [intervalIntegral.integral_of_le hab]

/-- Step 1: `corrLHS = |(2b)⁻¹ C_{N,n} (𝔼_{ν_t} 𝒵 - 𝔼_μ 𝒵)|`. -/
private lemma Main_corrLHS_eq {N n : ℕ} (M : Ensemble 𝕜 N) {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B : ℝ} (hO : Continuous O) (hB : ∀ α, |O α| ≤ B) {E b : ℝ} (hb : 0 < b) (t : ℝ) :
    corrLHS M O E b t = |(2 * b)⁻¹ * corrC N n *
      ((∫ x, Main_Z O E b (rhoSc E) x ∂M.eigLaw t) -
        ∫ x, Main_Z O E b (rhoSc E) x ∂gbeLaw 𝕜 N)| := by
  have := Main_isProbabilityMeasure_eigLaw M t
  have := Main_isProbabilityMeasure_gbeLaw (𝕜 := 𝕜) N
  obtain ⟨h1i, h1⟩ := Main_fubini hO hB hb (rhoSc E) (M.eigLaw t)
  obtain ⟨h2i, h2⟩ := Main_fubini hO hB hb (rhoSc E) (gbeLaw 𝕜 N)
  unfold corrLHS
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h1i h2i, h1, h2]

/-- `|𝔼_ν f| ≤ a + a' ε` if `|f| ≤ a'` everywhere, `|f| ≤ a` on `S` and `ν(Sᶜ) ≤ ε`. -/
private lemma Main_abs_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Integrable f ν) {S : Set α} (hS : MeasurableSet S)
    {a a' ε : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hε : 0 ≤ ε) (hf' : ∀ x, |f x| ≤ a')
    (hfS : ∀ x ∈ S, |f x| ≤ a) (hSc : ν Sᶜ ≤ ENNReal.ofReal ε) :
    |∫ x, f x ∂ν| ≤ a + a' * ε := by
  have hgi : Integrable (fun x => a + Sᶜ.indicator (fun _ => a') x) ν :=
    (integrable_const a).add ((integrable_const a').indicator hS.compl)
  have hSr : ν.real Sᶜ ≤ ε := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hε hSc
  calc |∫ x, f x ∂ν| ≤ ∫ x, |f x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, (a + Sᶜ.indicator (fun _ => a') x) ∂ν := by
        refine integral_mono hf.abs hgi fun x => ?_
        by_cases hx : x ∈ S
        · have : x ∉ Sᶜ := fun h => h hx
          simp only [Set.indicator_of_notMem this, add_zero]
          exact hfS x hx
        · have : x ∈ Sᶜ := hx
          simp only [Set.indicator_of_mem this]
          linarith [hf' x]
    _ = a + a' * ν.real Sᶜ := by
        rw [integral_add (integrable_const a) ((integrable_const a').indicator hS.compl),
          integral_const, integral_indicator_const _ hS.compl]
        simp [mul_comm]
    _ ≤ a + a' * ε := by gcongr


private lemma Main_corrC_nonneg (N n : ℕ) : 0 ≤ corrC N n := by
  unfold corrC
  positivity

private lemma Main_integrable_Z {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hO : Continuous O) (hB : ∀ α, |O α| ≤ B) {E b : ℝ} (hb : 0 < b) (ϱ : ℝ)
    (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν] : Integrable (Main_Z O E b ϱ) ν :=
  Main_integrable_of_bound (Main_continuous_Z hO E b ϱ) (Main_abs_Z_le hB hb ϱ)

/-- Steps 1, 2 of §19.4 (the trivial bound): for continuous `P` bounded by `B` and vanishing outside
`[-ρ_O, ρ_O]ⁿ`, `corrLHS ≤ 4 B (K_ℓ^n + 1)` once `N^n ν(Ξᶜ) ≤ 1` for `ν = ν_t, μ`. -/
private lemma Main_trivial {N n : ℕ} (M : Ensemble 𝕜 N) {P : EuclideanSpace ℝ (Fin n) → ℝ}
    {B ρO ℓ D c E b ε : ℝ} (hN : 3 ≤ N) (hD : 0 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ)
    (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) (hP : Continuous P) (hB : ∀ α, |P α| ≤ B)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → P α = 0)
    (hϱ : 0 < rhoSc E) (hρℓ : ρO ≤ ℓ * rhoSc E) (hE : E ∈ Set.Icc (-2 + c) (2 - c))
    (hb : 0 < b) (hb2 : b < c / 2) (hC : corrC N n ≤ 2) (hε : 0 ≤ ε) (hNε : (N : ℝ) ^ n * ε ≤ 1)
    (t : ℝ) (h1 : M.eigLaw t (flowGoodSet N D)ᶜ ≤ ENNReal.ofReal ε)
    (h2 : gbeLaw 𝕜 N (flowGoodSet N D)ᶜ ≤ ENNReal.ofReal ε) :
    corrLHS M P E b t ≤ 4 * B * ((2 * ℓ / π + 2 * D) ^ n + 1) := by
  have := Main_isProbabilityMeasure_eigLaw M t
  have := Main_isProbabilityMeasure_gbeLaw (𝕜 := 𝕜) N
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hKl : 0 ≤ 2 * ℓ / π + 2 * D := by positivity
  have hS := measurableSet_flowGoodSet N D
  have hI : ∀ (ν : Measure (Fin N → ℝ)) [IsProbabilityMeasure ν],
      ν (flowGoodSet N D)ᶜ ≤ ENNReal.ofReal ε →
      |∫ x, Main_Z P E b (rhoSc E) x ∂ν| ≤ 2 * b * (B * ((2 * ℓ / π + 2 * D) ^ n + 1)) := by
    intro ν _ hν
    refine (Main_abs_integral_le (Main_integrable_Z hP hB hb _ ν) hS (by positivity)
      (by positivity) hε (Main_abs_Z_le hB hb _)
      (fun x hx => Main_abs_Z_le_of_mem hN hD hc hc2 hℓ hH hB hsupp hϱ hρℓ hE hb hb2 hx)
      hν).trans ?_
    have : 2 * b * ((N : ℝ) ^ n * B) * ε ≤ 2 * b * B := by
      have := mul_le_mul_of_nonneg_left hNε (by positivity : (0 : ℝ) ≤ 2 * b * B)
      nlinarith
    nlinarith
  rw [Main_corrLHS_eq M hP hB hb, abs_mul, abs_of_nonneg (by
    have := Main_corrC_nonneg N n
    positivity)]
  have hsub := (abs_sub _ _).trans (add_le_add (hI (M.eigLaw t) h1) (hI (gbeLaw 𝕜 N) h2))
  calc (2 * b)⁻¹ * corrC N n * |(∫ x, Main_Z P E b (rhoSc E) x ∂M.eigLaw t) -
        ∫ x, Main_Z P E b (rhoSc E) x ∂gbeLaw 𝕜 N|
      ≤ (2 * b)⁻¹ * 2 * (2 * b * (B * ((2 * ℓ / π + 2 * D) ^ n + 1)) +
          2 * b * (B * ((2 * ℓ / π + 2 * D) ^ n + 1))) := by
        gcongr
    _ = 4 * B * ((2 * ℓ / π + 2 * D) ^ n + 1) := by field_simp; ring

/-! ### Step 6: gap universality for each index tuple -/

/-- For a measure carried by the chamber `Σ_N`, the extension by `0` off `Σ_N` does not change the
expectation. -/
private lemma Main_integral_indicator_chamber {N : ℕ} {ν : Measure (Fin N → ℝ)}
    (hch : ∀ᵐ x ∂ν, x ∈ chamber N) (f : (Fin N → ℝ) → ℝ) :
    ∫ x, (chamber N).indicator f x ∂ν = ∫ x, f x ∂ν := by
  rw [integral_indicator (isOpen_chamber N).measurableSet, Measure.restrict_eq_self_of_ae_mem hch]

/-- The gap-universality bound (19.1) for `ν₁, ν₂`, as it is used in Step 6. -/
private def Main_GapBound (N : ℕ) (ν₁ ν₂ : Measure (Fin N → ℝ)) (S : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ m : Fin r → ℕ, StrictMono m → (∀ k, 1 ≤ m k) →
    ∀ J : Finset ℕ, (∀ i ∈ J, ∀ k, i + m k < N) →
    ∀ A A' ρ : ℝ, 0 ≤ A → 0 ≤ A' → 0 < ρ → ∀ G : (Fin r → ℝ) → ℝ, GapHyp r A A' ρ G →
      |∫ x, (chamber N).indicator (gapObs J m G) x ∂ν₁ -
          ∫ x, (chamber N).indicator (gapObs J m G) x ∂ν₂| ≤
        4 / N * Real.sqrt (cStar A A' ρ * r * J.card) * Real.sqrt S

private lemma Main_cStar_nonneg (A A' ρ : ℝ) : 0 ≤ cStar A A' ρ :=
  le_trans (div_nonneg (sq_nonneg A) (mul_pos two_pos cZero_pos).le) (le_max_left _ _)

/-- Step 6: for every index tuple `m`, `|𝔼_{ν₁} F_m - 𝔼_{ν₂} F_m|` is bounded by (19.1) with
`(A, A', ρ) = (2ℓ‖O‖_∞, 2ρ_O Lip(O), 2ℓ)`; for `n = 1`, `F_m` is constant. -/
private lemma Main_F_diff {N n : ℕ} (hn : 0 < n) {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B K ρO ℓ ϱ : ℝ} (hB : ∀ α, |O α| ≤ B) (hLip : ∀ α β, |O α - O β| ≤ K * ‖α - β‖)
    (hK : 0 ≤ K) (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0)
    (hρ : 0 ≤ ρO) (hϱ : 0 < ϱ) (hρℓ : ρO ≤ ℓ * ϱ) (hℓ : 0 < ℓ) {ν₁ ν₂ : Measure (Fin N → ℝ)}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (hch₁ : ∀ᵐ x ∂ν₁, x ∈ chamber N)
    (hch₂ : ∀ᵐ x ∂ν₂, x ∈ chamber N) {S : ℝ} (hgap : Main_GapBound N ν₁ ν₂ S)
    (J : Finset ℕ) {m : Fin n → ℕ} (hm : IsIndexTuple m) :
    |∫ x, corrF O ϱ J m x ∂ν₁ - ∫ x, corrF O ϱ J m x ∂ν₂| ≤
      4 / N * Real.sqrt (cStar (2 * ℓ * B) (2 * ρO * K) (2 * ℓ) * n * J.card) * Real.sqrt S := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hR0 : 0 ≤ 4 / (N : ℝ) * Real.sqrt (cStar (2 * ℓ * B) (2 * ρO * K) (2 * ℓ) * n * J.card) *
      Real.sqrt S := by positivity
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- `n = 1`: `F_m` is constant
    have hm0 : ∀ k, m k = 0 := fun k => by
      have hk : k = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := k.isLt; omega)
      rw [hk]; exact hm.2 Nat.one_pos
    have hconst : ∀ x : Fin N → ℝ, corrF O ϱ J m x =
        corrF O ϱ J m (0 : Fin N → ℝ) := by
      intro x
      unfold corrF
      simp only [hm0, add_zero, sub_self, mul_zero]
    simp only [hconst, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    exact hR0
  · have hlast : lastIdx m = m ⟨r, by omega⟩ := by
      unfold lastIdx; simp
    set J' := J.filter fun i => i + lastIdx m < N with hJ'
    have hJ'N : ∀ i ∈ J', ∀ k : Fin r, i + m k.succ < N := by
      intro i hi k
      rw [hJ', Finset.mem_filter, hlast] at hi
      have : m k.succ ≤ m ⟨r, by omega⟩ :=
        hm.1.monotone (Fin.mk_le_mk.2 (by simp) : k.succ ≤ ⟨r, by omega⟩)
      omega
    have hsm : StrictMono fun k : Fin r => m k.succ := hm.1.comp (Fin.strictMono_succ)
    have hm1 : ∀ k : Fin r, 1 ≤ m k.succ := by
      intro k
      have := hm.1 (Fin.succ_pos k)
      rw [show (0 : Fin (r + 1)) = ⟨0, Nat.succ_pos r⟩ from rfl, hm.2 (Nat.succ_pos r)] at this
      omega
    have hG := corrG_gapHyp hB hLip hK hsupp hρ hϱ hρℓ
    have h := hgap r hr _ hsm hm1 J' hJ'N _ _ _ (by positivity) (by positivity) (by positivity) _ hG
    rw [Main_integral_indicator_chamber hch₁, Main_integral_indicator_chamber hch₂,
      ← corrF_eq_gapObs] at h
    refine h.trans ?_
    have hc0 := Main_cStar_nonneg (2 * ℓ * B) (2 * ρO * K) (2 * ℓ)
    have hJc : (J'.card : ℝ) ≤ J.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hrr : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by push_cast; linarith
    gcongr

/-! ### Steps 3–7 -/

/-- The constant `C₁''` of §19.3 (with `C_♯ = ℓ (√(2/c₀) + 3√2 e ρ_O)`,
`C_𝓑 = 4/ϱ_* + 4ℓ + 2`, `|J| ≤ 3Nb` and the trivial counts in Step 4). -/
private noncomputable def Main_C1 (n : ℕ) (ℓ ρO c : ℝ) : ℝ :=
  8 * (ℓ + 2) ^ n +
  32 * Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) *
    (ℓ * (Real.sqrt (2 / cZero) + 3 * Real.sqrt 2 * Real.exp 1 * ρO)) +
  4 * n.factorial * ℓ * (4 / rhoStar c + 4 * ℓ + 2) * (ℓ + 2) ^ (n - 1) +
  (4 + 4 * n.factorial * ℓ)

private lemma Main_C1_pos {n : ℕ} {ℓ ρO c : ℝ} (hℓ : 0 < ℓ) (hρ : 0 ≤ ρO) (hc : 0 < c)
    (hc2 : c ≤ 2) : 0 < Main_C1 n ℓ ρO c := by
  have := Main_rhoStar_pos hc hc2
  have := cZero_pos
  unfold Main_C1
  positivity

private lemma Main_Kl_le {ℓ D : ℝ} (hℓ : 0 ≤ ℓ) (hD : 1 ≤ D) :
    2 * ℓ / π + 2 * D ≤ (ℓ + 2) * D := by
  have hπ := Real.pi_gt_three
  have : 2 * ℓ / π ≤ ℓ := by rw [div_le_iff₀ Real.pi_pos]; nlinarith
  nlinarith

private lemma Main_J_le {x N b : ℝ} (h : x ≤ 2 * N * b / π + 1) (hNb : 1 ≤ N * b) :
    x ≤ 3 * (N * b) := by
  have hπ := Real.pi_gt_three
  have : 2 * N * b / π ≤ N * b := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  linarith

private lemma Main_Bs_le {x D ρ ℓ : ℝ} (h : x ≤ 4 * (D / ρ + ℓ) / π + 2) (hρ : 0 < ρ)
    (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) : x ≤ (4 / ρ + 4 * ℓ + 2) * D := by
  have hπ := Real.pi_gt_three
  have hx : 0 ≤ D / ρ := by positivity
  have h4 : 4 * (D / ρ + ℓ) / π ≤ 4 * (D / ρ) + 4 * ℓ * D := by
    rw [div_le_iff₀ Real.pi_pos]
    have h5 : 4 * (D / ρ) ≤ 4 * (D / ρ) * π := by nlinarith
    have h6 : 4 * ℓ ≤ 4 * ℓ * D * π := by
      have : 1 ≤ D * π := by nlinarith
      nlinarith
    nlinarith
  have e : 4 / ρ * D = 4 * (D / ρ) := by ring
  nlinarith

/-- Step 6 arithmetic: `b⁻¹ n! K_ℓ^{n-1} (4/N) √(C⋆ n |J|) √S` is at most
`32 √(3n) n! (ℓ+2)^{n-1} C_♯ (‖O‖_∞ + Lip O) D^n (log N)^{1/2} [b⁻¹N⁻¹ + b^{-1/2}(Nt)^{-1/2}]`. -/
private lemma Main_arith_i {n : ℕ} (hn : 0 < n) {NR b t D Λ B K ℓ Kl J S cS Cs : ℝ}
    (hN1 : 1 ≤ NR) (hb : 0 < b) (hb1 : b ≤ 1) (ht : 0 < t) (hD1 : 1 ≤ D) (hΛ : 1 ≤ Λ)
    (hBK : 0 ≤ B + K) (hℓ : 0 ≤ ℓ) (hKl0 : 0 ≤ Kl) (hKlD : Kl ≤ (ℓ + 2) * D)
    (hJ : J ≤ 3 * (NR * b)) (hcS0 : 0 ≤ cS) (hcS : Real.sqrt cS ≤ Cs * (B + K)) (hCs : 0 ≤ Cs)
    (hS : Real.sqrt S ≤ (Real.sqrt NR)⁻¹ + 8 * D * Λ * (Real.sqrt t)⁻¹) :
    b⁻¹ * (n.factorial * (Kl ^ (n - 1) * (4 / NR * Real.sqrt (cS * n * J) * Real.sqrt S))) ≤
      32 * Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) * Cs * (B + K) * (D ^ n * Λ) *
        (b⁻¹ * NR⁻¹ + (Real.sqrt b)⁻¹ * (Real.sqrt (NR * t))⁻¹) := by
  obtain ⟨sN, hsN, rfl⟩ : ∃ s, 0 < s ∧ NR = s ^ 2 :=
    ⟨Real.sqrt NR, Real.sqrt_pos.2 (by linarith), (Real.sq_sqrt (by linarith)).symm⟩
  obtain ⟨sb, hsb, rfl⟩ : ∃ s, 0 < s ∧ b = s ^ 2 :=
    ⟨Real.sqrt b, Real.sqrt_pos.2 hb, (Real.sq_sqrt hb.le).symm⟩
  obtain ⟨st, hst, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
    ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
  have e1 : Real.sqrt (sN ^ 2) = sN := Real.sqrt_sq hsN.le
  have e2 : Real.sqrt (sb ^ 2) = sb := Real.sqrt_sq hsb.le
  have e3 : Real.sqrt (st ^ 2) = st := Real.sqrt_sq hst.le
  have e4 : Real.sqrt (sN ^ 2 * st ^ 2) = sN * st := by
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  rw [e1, e3] at hS
  rw [e2, e4]
  have hD0 : 0 ≤ D := by linarith
  have hn3 : (0 : ℝ) ≤ 3 * n := by positivity
  have h1 : Real.sqrt (cS * n * J) ≤ Cs * (B + K) * (Real.sqrt (3 * n) * (sN * sb)) := by
    calc Real.sqrt (cS * n * J) = Real.sqrt cS * Real.sqrt (n * J) := by
          rw [mul_assoc, Real.sqrt_mul hcS0]
      _ ≤ Cs * (B + K) * Real.sqrt (3 * n * (sN ^ 2 * sb ^ 2)) := by
          refine mul_le_mul hcS (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) (by positivity)
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
      _ = Cs * (B + K) * (Real.sqrt (3 * n) * (sN * sb)) := by
          rw [Real.sqrt_mul hn3, ← mul_pow, Real.sqrt_sq (by positivity)]
  have hSq0 := Real.sqrt_nonneg S
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hDn : D ^ n = D ^ (n - 1) * D := by
    rw [← pow_succ]; congr 1; omega
  have hsb1 : sb ≤ 1 := by nlinarith
  have hX : (sb)⁻¹ * (sN ^ 2)⁻¹ ≤ (sb ^ 2)⁻¹ * (sN ^ 2)⁻¹ := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact inv_anti₀ (by positivity) (by nlinarith)
  set X := (sb ^ 2)⁻¹ * (sN ^ 2)⁻¹ with hXdef
  set Y := sb⁻¹ * (sN * st)⁻¹ with hYdef
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hP : 0 ≤ Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) * Cs * (B + K) * D ^ (n - 1) :=
    by positivity
  calc (sb ^ 2)⁻¹ * (n.factorial * (Kl ^ (n - 1) *
        (4 / sN ^ 2 * Real.sqrt (cS * n * J) * Real.sqrt S)))
      ≤ (sb ^ 2)⁻¹ * (n.factorial * (((ℓ + 2) * D) ^ (n - 1) *
        (4 / sN ^ 2 * (Cs * (B + K) * (Real.sqrt (3 * n) * (sN * sb))) *
          (sN⁻¹ + 8 * D * Λ * st⁻¹)))) := by
        gcongr
    _ = Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) * Cs * (B + K) * D ^ (n - 1) *
          (4 * (sb⁻¹ * (sN ^ 2)⁻¹ + 8 * D * Λ * Y)) := by
        rw [hYdef, mul_pow]
        field_simp
    _ ≤ Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) * Cs * (B + K) * D ^ (n - 1) *
          (32 * D * Λ * (X + Y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        have h8 : 1 ≤ 8 * D * Λ := by nlinarith
        have : X ≤ 8 * D * Λ * X := le_mul_of_one_le_left hX0 h8
        nlinarith
    _ = 32 * Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) * Cs * (B + K) * (D ^ n * Λ) *
          (X + Y) := by
        rw [hDn]; ring

/-- Step 5 arithmetic. -/
private lemma Main_arith_ii {n : ℕ} (hn : 0 < n) {NR b D Λ B K ℓ Kl Bs CB X Y : ℝ}
    (hN1 : 1 ≤ NR) (hb : 0 < b) (hD1 : 1 ≤ D) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hℓ : 0 ≤ ℓ) (hKl0 : 0 ≤ Kl) (hKlD : Kl ≤ (ℓ + 2) * D) (hBs0 : 0 ≤ Bs) (hBsD : Bs ≤ CB * D)
    (hX : X = b⁻¹ * NR⁻¹) (hY : 0 ≤ Y) :
    b⁻¹ * (2 * (n.factorial * Bs * Kl ^ (n - 1) * (2 * ℓ * B / NR))) ≤
      4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) * (B + K) * (D ^ n * Λ) * (X + Y) := by
  have hD0 : 0 ≤ D := by linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hDn : D ^ n = D ^ (n - 1) * D := by
    rw [← pow_succ]; congr 1; omega
  have hX0 : 0 ≤ X := by rw [hX]; have : 0 < NR := by linarith
                         positivity
  have hCB : 0 ≤ CB * D := hBs0.trans hBsD
  calc b⁻¹ * (2 * (n.factorial * Bs * Kl ^ (n - 1) * (2 * ℓ * B / NR)))
      = 4 * n.factorial * ℓ * B * (Bs * Kl ^ (n - 1)) * X := by rw [hX]; ring
    _ ≤ 4 * n.factorial * ℓ * B * ((CB * D) * ((ℓ + 2) * D) ^ (n - 1)) * X := by gcongr
    _ = 4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) * B * D ^ n * X := by rw [hDn, mul_pow]; ring
    _ ≤ 4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) * (B + K) * (D ^ n * Λ) * (X + Y) := by
        have hCB' : 0 ≤ CB := by
          by_contra h
          push Not at h
          nlinarith
        have hc : 0 ≤ 4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) := by positivity
        have hDn0 : 0 ≤ D ^ n := by positivity
        have h1 : D ^ n ≤ D ^ n * Λ := le_mul_of_one_le_right hDn0 hΛ
        have h2 : B * D ^ n * X ≤ (B + K) * (D ^ n * Λ) * (X + Y) := by
          have := mul_le_mul (mul_le_mul (le_add_of_nonneg_right hK : B ≤ B + K) h1 hDn0
            (by positivity)) (le_add_of_nonneg_right hY : X ≤ X + Y) hX0 (by positivity)
          linarith
        calc 4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) * B * D ^ n * X
            = 4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) * (B * D ^ n * X) := by ring
          _ ≤ 4 * n.factorial * ℓ * CB * (ℓ + 2) ^ (n - 1) *
              ((B + K) * (D ^ n * Λ) * (X + Y)) := mul_le_mul_of_nonneg_left h2 hc
          _ = _ := by ring

/-- Step 4 arithmetic. -/
private lemma Main_arith_iii {n : ℕ} {NR b D Λ B K ℓ ε X Y : ℝ}
    (hN1 : 1 ≤ NR) (hb : 0 < b) (hb1 : b ≤ 1) (hD1 : 1 ≤ D) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (hℓ : 0 ≤ ℓ) (hε : 0 ≤ ε) (hNε : NR ^ n * ε ≤ (NR ^ 2)⁻¹)
    (hX : X = b⁻¹ * NR⁻¹) (hY : 0 ≤ Y) :
    b⁻¹ * (2 * ((2 * b * (NR ^ n * B) + n.factorial * (NR ^ n * (2 * ℓ * B))) * ε)) ≤
      (4 + 4 * n.factorial * ℓ) * (B + K) * (D ^ n * Λ) * (X + Y) := by
  have hNR : 0 < NR := by linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hb' : 1 ≤ b⁻¹ := by rw [le_inv_comm₀ one_pos hb]; simpa using hb1
  have hN' : NR⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hN2 : (NR ^ 2)⁻¹ ≤ X := by
    rw [hX, pow_two, mul_inv]
    exact mul_le_mul_of_nonneg_right (hN'.trans hb') (by positivity)
  have hN3 : b⁻¹ * (NR ^ 2)⁻¹ ≤ X := by
    rw [hX, pow_two, mul_inv]
    have : NR⁻¹ * NR⁻¹ ≤ NR⁻¹ := mul_le_of_le_one_left (by positivity) hN'
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hNn : 0 ≤ NR ^ n * ε := by positivity
  have e : b⁻¹ * (2 * ((2 * b * (NR ^ n * B) + n.factorial * (NR ^ n * (2 * ℓ * B))) * ε)) =
      4 * B * (NR ^ n * ε) + 4 * n.factorial * ℓ * B * (b⁻¹ * (NR ^ n * ε)) := by
    field_simp
    ring
  rw [e]
  have hDn0 : (1 : ℝ) ≤ D ^ n := one_le_pow₀ hD1
  have hW : 1 ≤ D ^ n * Λ := by nlinarith
  have hQ : B * X ≤ (B + K) * (D ^ n * Λ) * (X + Y) := by
    have := mul_le_mul (mul_le_mul (le_add_of_nonneg_right hK : B ≤ B + K) hW zero_le_one
      (by positivity)) (le_add_of_nonneg_right hY : X ≤ X + Y) hX0 (by positivity)
    linarith
  have h1 : 4 * B * (NR ^ n * ε) ≤ 4 * (B * X) := by
    have := mul_le_mul_of_nonneg_left (hNε.trans hN2) hB
    linarith
  have h2 : 4 * n.factorial * ℓ * B * (b⁻¹ * (NR ^ n * ε)) ≤ 4 * n.factorial * ℓ * (B * X) := by
    have := mul_le_mul_of_nonneg_left hNε (by positivity : (0 : ℝ) ≤ b⁻¹)
    have := mul_le_mul_of_nonneg_left (this.trans hN3) hB
    have hc : (0 : ℝ) ≤ 4 * n.factorial * ℓ := by positivity
    have := mul_le_mul_of_nonneg_left this hc
    linarith
  have hc : (0 : ℝ) ≤ 4 * n.factorial * ℓ := by positivity
  have := mul_le_mul_of_nonneg_left hQ hc
  have e' : (4 + 4 * n.factorial * ℓ) * (B + K) * (D ^ n * Λ) * (X + Y) =
      4 * ((B + K) * (D ^ n * Λ) * (X + Y)) +
        4 * n.factorial * ℓ * ((B + K) * (D ^ n * Λ) * (X + Y)) := by ring
  rw [e']
  linarith

open Classical in
/-- Steps 3–7 of §19.4 (case `b ≥ 1/N`), for two probability measures `ν₁, ν₂` carried by the
chamber, with `ν_i(Ξᶜ) ≤ ε` and the gap-universality bound (19.1). -/
private lemma Main_core {N n : ℕ} (hn : 0 < n) {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B K ρO ℓ ϱ D c E b t S ε : ℝ} (hN : 3 ≤ N) (hD1 : 1 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2)
    (hℓ : 0 < ℓ) (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) (hO : Continuous O)
    (hB : ∀ α, |O α| ≤ B) (hLip : ∀ α β, |O α - O β| ≤ K * ‖α - β‖) (hK : 0 ≤ K)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hρ : 0 ≤ ρO)
    (hϱ : 0 < ϱ) (hρℓ : ρO ≤ ℓ * ϱ) (hE : E ∈ Set.Icc (-2 + c) (2 - c)) (hb : 0 < b)
    (hb2 : b < c / 2) (hNb : 1 ≤ N * b) (ht : 0 < t) {ν₁ ν₂ : Measure (Fin N → ℝ)}
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (hch₁ : ∀ᵐ x ∂ν₁, x ∈ chamber N)
    (hch₂ : ∀ᵐ x ∂ν₂, x ∈ chamber N) (hgap : Main_GapBound N ν₁ ν₂ S)
    (hS : Real.sqrt S ≤ (Real.sqrt N)⁻¹ + 8 * D * Real.sqrt (Real.log N) * (Real.sqrt t)⁻¹)
    (hlog : 1 ≤ Real.sqrt (Real.log N)) (hε : 0 ≤ ε) (hNε : (N : ℝ) ^ n * ε ≤ ((N : ℝ) ^ 2)⁻¹)
    (h1 : ν₁ (flowGoodSet N D)ᶜ ≤ ENNReal.ofReal ε)
    (h2 : ν₂ (flowGoodSet N D)ᶜ ≤ ENNReal.ofReal ε) :
    b⁻¹ * |(∫ x, Main_Z O E b ϱ x ∂ν₁) - ∫ x, Main_Z O E b ϱ x ∂ν₂| ≤
      Main_C1 n ℓ ρO c * (B + K) * (D ^ n * Real.sqrt (Real.log N)) *
        (b⁻¹ * (N : ℝ)⁻¹ + (Real.sqrt b)⁻¹ * (Real.sqrt (N * t))⁻¹) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hπ := Real.pi_gt_three
  have hρs := Main_rhoStar_pos hc hc2
  have hb1 : b ≤ 1 := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  set Kl : ℝ := 2 * ℓ / π + 2 * D with hKl
  have hKl0 : 0 ≤ Kl := by positivity
  have hKlD : Kl ≤ (ℓ + 2) * D := Main_Kl_le hℓ.le hD1
  set J : Finset ℕ := (Finset.univ.filter fun j : Fin N =>
    gamma N j ∈ Set.Icc (E - b) (E + b)).map Fin.valEmbedding with hJdef
  have hJ : ∀ i : ℕ, i ∈ J ↔ ∃ j : Fin N, (j : ℕ) = i ∧ gamma N j ∈ Set.Icc (E - b) (E + b) := by
    intro i
    rw [hJdef, Finset.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, rfl, (Finset.mem_filter.1 hj).2⟩
    · rintro ⟨j, rfl, hj⟩
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩
  obtain ⟨hJc, hBc⟩ := card_indexSets_le hN hD0 hc hc2 hℓ hH hE hb hb2
  have hJcard : (J.card : ℝ) ≤ 3 * (N * b) := by
    rw [hJdef, Finset.card_map]
    exact Main_J_le hJc hNb
  have hJN : (J.card : ℝ) ≤ N := by
    rw [hJdef, Finset.card_map]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  set Bs := (Finset.univ.filter fun i : Fin N =>
    min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ D / (N * rhoStar c) + ℓ / N).card with hBs
  have hBsD : (Bs : ℝ) ≤ (4 / rhoStar c + 4 * ℓ + 2) * D := Main_Bs_le hBc hρs hD1 hℓ.le
  set T := Finset.univ.filter (fun m : Fin n → Fin N =>
    (IsIndexTuple fun k => (m k : ℕ)) ∧ ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < Kl) with hT
  have hTK : (T.card : ℝ) ≤ Kl ^ (n - 1) := card_indexTuples_le hn hKl0
  have hTN : (T.card : ℝ) ≤ (N : ℝ) ^ n := by
    have : T.card ≤ N ^ n := (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hFm_bd : ∀ (m : Fin n → ℕ) x, |corrF O ϱ J m x| ≤ 2 * ℓ * B * J.card / N :=
    fun m x => abs_corrF_le hn hϱ hρ hρℓ hB hsupp J m x
  have hFm_int : ∀ (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν] (m : Fin n → ℕ),
      Integrable (corrF O ϱ J m) ν := fun ν _ m =>
    Main_integrable_of_bound (continuous_corrF hn hϱ hO hsupp J m) (hFm_bd m)
  set F : (Fin N → ℝ) → ℝ := fun x =>
    n.factorial * ∑ m ∈ T, corrF O ϱ J (fun k => (m k : ℕ)) x with hF
  have hFint : ∀ (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν], Integrable F ν := fun ν _ =>
    (integrable_finsetSum _ fun m _ => hFm_int ν _).const_mul _
  have hFI : ∀ (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν], ∫ x, F x ∂ν =
      n.factorial * ∑ m ∈ T, ∫ x, corrF O ϱ J (fun k => (m k : ℕ)) x ∂ν := by
    intro ν _
    rw [hF, integral_const_mul, integral_finsetSum _ fun m _ => hFm_int ν _]
  set G0 := 4 / (N : ℝ) * Real.sqrt (cStar (2 * ℓ * B) (2 * ρO * K) (2 * ℓ) * n * J.card) *
    Real.sqrt S with hG0
  have hG00 : 0 ≤ G0 := by positivity
  have hΔF : |(∫ x, F x ∂ν₁) - ∫ x, F x ∂ν₂| ≤ n.factorial * (Kl ^ (n - 1) * G0) := by
    rw [hFI ν₁, hFI ν₂, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_nonneg hfac.le]
    refine mul_le_mul_of_nonneg_left ?_ hfac.le
    calc |∑ m ∈ T, ((∫ x, corrF O ϱ J (fun k => (m k : ℕ)) x ∂ν₁) -
          ∫ x, corrF O ϱ J (fun k => (m k : ℕ)) x ∂ν₂)|
        ≤ ∑ m ∈ T, |(∫ x, corrF O ϱ J (fun k => (m k : ℕ)) x ∂ν₁) -
          ∫ x, corrF O ϱ J (fun k => (m k : ℕ)) x ∂ν₂| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ T, G0 := Finset.sum_le_sum fun m hm =>
          Main_F_diff hn hB hLip hK hsupp hρ hϱ hρℓ hℓ hch₁ hch₂ hgap J
            (Finset.mem_filter.1 hm).2.1
      _ = T.card * G0 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Kl ^ (n - 1) * G0 := mul_le_mul_of_nonneg_right hTK hG00
  set a : ℝ := n.factorial * Bs * Kl ^ (n - 1) * (2 * ℓ * B / N) with ha
  set a' : ℝ := 2 * b * ((N : ℝ) ^ n * B) + n.factorial * ((N : ℝ) ^ n * (2 * ℓ * B)) with ha'
  have hJB : 2 * ℓ * B * J.card / N ≤ 2 * ℓ * B := by
    rw [div_le_iff₀ hNR]
    have : 0 ≤ 2 * ℓ * B := by positivity
    nlinarith
  have hErrG : ∀ x, |Main_Z O E b ϱ x - F x| ≤ a' := by
    intro x
    refine (abs_sub _ _).trans (add_le_add (Main_abs_Z_le hB hb ϱ x) ?_)
    rw [hF]
    simp only
    rw [abs_mul, abs_of_nonneg hfac.le]
    refine mul_le_mul_of_nonneg_left ?_ hfac.le
    calc |∑ m ∈ T, corrF O ϱ J (fun k => (m k : ℕ)) x|
        ≤ ∑ m ∈ T, |corrF O ϱ J (fun k => (m k : ℕ)) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ T, 2 * ℓ * B := Finset.sum_le_sum fun m _ =>
          (hFm_bd (fun k => (m k : ℕ)) x).trans hJB
      _ = T.card * (2 * ℓ * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ n * (2 * ℓ * B) := mul_le_mul_of_nonneg_right hTN (by positivity)
  have hErrS : ∀ x ∈ flowGoodSet N D, |Main_Z O E b ϱ x - F x| ≤ a := fun x hx =>
    abs_integral_corrX_sub_le hn hN hD0 hc hc2 hℓ hH hB hLip hK hsupp hϱ hρℓ hE hb hb2 hJ hx
  have ha0 : 0 ≤ a := by positivity
  have ha'0 : 0 ≤ a' := by positivity
  have hErrI : ∀ (ν : Measure (Fin N → ℝ)) [IsProbabilityMeasure ν],
      ν (flowGoodSet N D)ᶜ ≤ ENNReal.ofReal ε →
      |∫ x, (Main_Z O E b ϱ x - F x) ∂ν| ≤ a + a' * ε := fun ν _ hν =>
    Main_abs_integral_le ((Main_integrable_Z hO hB hb ϱ ν).sub (hFint ν))
      (measurableSet_flowGoodSet N D) ha0 ha'0 hε hErrG hErrS hν
  have hsplit : ∀ (ν : Measure (Fin N → ℝ)) [IsFiniteMeasure ν],
      ∫ x, Main_Z O E b ϱ x ∂ν = (∫ x, F x ∂ν) + ∫ x, (Main_Z O E b ϱ x - F x) ∂ν := by
    intro ν _
    rw [integral_sub (Main_integrable_Z hO hB hb ϱ ν) (hFint ν)]
    ring
  have hΔZ : |(∫ x, Main_Z O E b ϱ x ∂ν₁) - ∫ x, Main_Z O E b ϱ x ∂ν₂| ≤
      n.factorial * (Kl ^ (n - 1) * G0) + 2 * (a + a' * ε) := by
    rw [hsplit ν₁, hsplit ν₂]
    have e1 := hErrI ν₁ h1
    have e2 := hErrI ν₂ h2
    have e3 := abs_sub (∫ x, (Main_Z O E b ϱ x - F x) ∂ν₁) (∫ x, (Main_Z O E b ϱ x - F x) ∂ν₂)
    have e4 := abs_add_le ((∫ x, F x ∂ν₁) - ∫ x, F x ∂ν₂)
      ((∫ x, (Main_Z O E b ϱ x - F x) ∂ν₁) - ∫ x, (Main_Z O E b ϱ x - F x) ∂ν₂)
    have e5 : (∫ x, F x ∂ν₁) + (∫ x, (Main_Z O E b ϱ x - F x) ∂ν₁) -
        ((∫ x, F x ∂ν₂) + ∫ x, (Main_Z O E b ϱ x - F x) ∂ν₂) =
        ((∫ x, F x ∂ν₁) - ∫ x, F x ∂ν₂) +
          ((∫ x, (Main_Z O E b ϱ x - F x) ∂ν₁) - ∫ x, (Main_Z O E b ϱ x - F x) ∂ν₂) := by ring
    rw [e5]
    linarith
  set X : ℝ := b⁻¹ * (N : ℝ)⁻¹ with hX
  set Y : ℝ := (Real.sqrt b)⁻¹ * (Real.sqrt (N * t))⁻¹ with hY
  have hY0 : 0 ≤ Y := by positivity
  have hX0 : 0 ≤ X := by positivity
  set Cs : ℝ := ℓ * (Real.sqrt (2 / cZero) + 3 * Real.sqrt 2 * Real.exp 1 * ρO) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hi := Main_arith_i hn hN1 hb hb1 ht hD1 hlog (by positivity : 0 ≤ B + K) hℓ.le hKl0 hKlD
    hJcard (Main_cStar_nonneg _ _ _) (sqrt_cStar_le hB0 hK hρ hℓ.le) hCs0 hS
  have hii := Main_arith_ii (X := X) hn hN1 hb hD1 hlog hB0 hK hℓ.le hKl0 hKlD
    (Nat.cast_nonneg Bs) hBsD rfl hY0
  have hiii := Main_arith_iii (n := n) (X := X) hN1 hb hb1 hD1 hlog hB0 hK hℓ.le hε hNε rfl hY0
  have hQ : 0 ≤ 8 * (ℓ + 2) ^ n * ((B + K) * (D ^ n * Real.sqrt (Real.log N)) * (X + Y)) := by
    positivity
  have eC : Main_C1 n ℓ ρO c * (B + K) * (D ^ n * Real.sqrt (Real.log N)) * (X + Y) =
      8 * (ℓ + 2) ^ n * ((B + K) * (D ^ n * Real.sqrt (Real.log N)) * (X + Y)) +
      32 * Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) * Cs * (B + K) *
        (D ^ n * Real.sqrt (Real.log N)) * (X + Y) +
      4 * n.factorial * ℓ * (4 / rhoStar c + 4 * ℓ + 2) * (ℓ + 2) ^ (n - 1) * (B + K) *
        (D ^ n * Real.sqrt (Real.log N)) * (X + Y) +
      (4 + 4 * n.factorial * ℓ) * (B + K) * (D ^ n * Real.sqrt (Real.log N)) * (X + Y) := by
    unfold Main_C1; ring
  have hbinv : 0 ≤ b⁻¹ := by positivity
  calc b⁻¹ * |(∫ x, Main_Z O E b ϱ x ∂ν₁) - ∫ x, Main_Z O E b ϱ x ∂ν₂|
      ≤ b⁻¹ * (n.factorial * (Kl ^ (n - 1) * G0) + 2 * (a + a' * ε)) :=
        mul_le_mul_of_nonneg_left hΔZ hbinv
    _ = b⁻¹ * (n.factorial * (Kl ^ (n - 1) * G0)) + b⁻¹ * (2 * a) + b⁻¹ * (2 * (a' * ε)) := by
        ring
    _ ≤ Main_C1 n ℓ ρO c * (B + K) * (D ^ n * Real.sqrt (Real.log N)) * (X + Y) := by
        rw [eC]
        linarith

/-! ### Theorem 12.1 -/

/-- `ϱ_*(c) ≤ ϱ_sc(E)` for `E ∈ [-2 + c, 2 - c]` (Lemma 3.4 (d)). -/
private lemma Main_rhoStar_le_rhoSc {c E : ℝ} (hc : 0 < c) (hc2 : c ≤ 2)
    (hE : E ∈ Set.Icc (-2 + c) (2 - c)) : rhoStar c ≤ rhoSc E := by
  have h := rhoSc_bulk hc hc2 (x := E) (by rw [abs_le]; constructor <;> linarith [hE.1, hE.2])
  unfold rhoStar
  rwa [one_div] at h

/-- The chamber carries `μ` and `ν_t` (`t > 0`): Theorem 16.3. -/
private lemma Main_ae_chamber {N : ℕ} (M : Ensemble 𝕜 N) {t : ℝ} (ht : 0 < t) :
    (∀ᵐ x ∂M.eigLaw t, x ∈ chamber N) ∧ ∀ᵐ x ∂gbeLaw 𝕜 N, x ∈ chamber N := by
  have hμ : ∀ᵐ x ∂gbeLaw 𝕜 N, x ∈ chamber N := by
    rw [gbeLaw_eq_muStar]
    unfold muStar
    refine Measure.ae_smul_measure ?_ _
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (isOpen_chamber N).measurableSet)
  have hρ : IsProbabilityMeasure M.hermLaw := by
    unfold Ensemble.hermLaw
    exact (Measure.isProbabilityMeasure_map_iff
      (Herm.measurable_ofPair (𝕜 := 𝕜) N).aemeasurable).2 inferInstance
  exact ⟨(eigFlow_ac M.hermLaw ht).1.ae_le hμ, hμ⟩

/-- `√(1/N + 32 β D² log N / t) ≤ N^{-1/2} + 8 D (log N)^{1/2} t^{-1/2}` for `β ≤ 2`. -/
private lemma Main_sqrt_S_le {N D t β : ℝ} (hN : 0 < N) (hlog : 0 ≤ Real.log N) (ht : 0 < t)
    (hD : 0 ≤ D) (hβ : β ≤ 2) :
    Real.sqrt (1 / N + 32 * β * D ^ 2 * Real.log N / t) ≤
      (Real.sqrt N)⁻¹ + 8 * D * Real.sqrt (Real.log N) * (Real.sqrt t)⁻¹ := by
  rw [Real.sqrt_le_left (by positivity)]
  have hu : ((Real.sqrt N)⁻¹) ^ 2 = 1 / N := by rw [inv_pow, Real.sq_sqrt hN.le, one_div]
  have hv : (8 * D * Real.sqrt (Real.log N) * (Real.sqrt t)⁻¹) ^ 2 =
      64 * D ^ 2 * Real.log N / t := by
    rw [mul_pow, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hlog, Real.sq_sqrt ht.le]
    ring
  have h32 : 32 * β * D ^ 2 * Real.log N / t ≤ 64 * D ^ 2 * Real.log N / t := by
    gcongr
    linarith
  have huv : 0 ≤ (Real.sqrt N)⁻¹ * (8 * D * Real.sqrt (Real.log N) * (Real.sqrt t)⁻¹) := by
    positivity
  nlinarith

/-- Theorem 12.1 (quantitative form), for one tuple of (RA1) constants. -/
theorem dbm_quantitative_of_rigidityBound {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hδm : 0 < δm)
    (hδp : 0 < δp) (hC₀ : 0 < C₀) {A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀)
      A₀ CR cR φ N₀) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) {n : ℕ} (hn : 1 ≤ n) {ρO : ℝ}
    (hρO : 0 < ρO) :
    ∃ A₁ : ℝ, 1 ≤ A₁ ∧ ∃ Nq : ℕ, 3 ≤ Nq ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ N : ℕ, max Nq n ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ t : ℝ, 0 < t → Real.log N ^ 2 ≤ N * t →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
      corrLHS M O E b t ≤ C₁ * (Bd + K) * Real.exp (A₁ * Real.log (Real.log N) ^ 2) *
        (b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N * t) ^ (-(1 / 2 : ℝ))) := by
  have hA₀ : 1 < A₀ := hR.1
  have hρs := Main_rhoStar_pos hc hc2
  have hn0 : 0 < n := hn
  set ℓ : ℝ := max 1 (ρO / rhoStar c) with hℓdef
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hℓ : 0 < ℓ := by linarith
  obtain ⟨Nc, hNc⟩ := exists_Nq A₀ ℓ hc hc2
  obtain ⟨NK, hNK⟩ := flowGoodSet_compl_le hϑ hδm hδp hC₀ hR ((n : ℝ) + 2) (by positivity)
  obtain ⟨N₄, hN₄⟩ := gapUniversality hϑ hδm hδp hC₀ hR
  refine ⟨n * A₀ + 1, by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
    max (max (max Nc NK) (max N₄ (n ^ 2))) 16, le_trans (by norm_num) (le_max_right _ _),
    3 ^ n * Main_C1 n ℓ ρO c, by have := Main_C1_pos (n := n) hℓ hρO.le hc hc2; positivity, ?_⟩
  intro N hN M hM O Bd K hB hL hsupp t ht hNt E hE b hb hb2
  have hNq : max (max (max Nc NK) (max N₄ (n ^ 2))) 16 ≤ N := (le_max_left _ _).trans hN
  have hNcN : Nc ≤ N := by omega
  have hNKN : NK ≤ N := by omega
  have hN₄N : N₄ ≤ N := by omega
  have hn2 : n ^ 2 ≤ N := by omega
  obtain ⟨h16, hD2, hDle, hDN', hH⟩ := hNc N hNcN
  have hN3 : 3 ≤ N := by omega
  have hNR : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hNpos : (0 : ℝ) < N := by linarith
  set D := Dpar A₀ N with hDdef
  have hD1 : 1 ≤ D := by linarith
  have hDN : D ≤ N := hDle.trans hDN'
  obtain ⟨hct, hcμ⟩ := hNK N hNKN M hM
  have h1 := hct t ht.le
  obtain ⟨hch₁, hch₂⟩ := Main_ae_chamber M ht
  have := Main_isProbabilityMeasure_eigLaw M t
  have := Main_isProbabilityMeasure_gbeLaw (𝕜 := 𝕜) N
  have hϱs := Main_rhoStar_le_rhoSc hc hc2 hE
  have hϱ : 0 < rhoSc E := lt_of_lt_of_le hρs hϱs
  have hρℓ : ρO ≤ ℓ * rhoSc E := by
    have : ρO = ρO / rhoStar c * rhoStar c := by field_simp
    calc ρO = ρO / rhoStar c * rhoStar c := this
      _ ≤ ℓ * rhoSc E := mul_le_mul (le_max_right _ _) hϱs hρs.le (by linarith)
  have hC := corrC_le_two hn hn2
  have hLip : ∀ α β, |O α - O β| ≤ (K : ℝ) * ‖α - β‖ := fun α β => by
    have := hL.dist_le_mul α β
    rwa [Real.dist_eq, dist_eq_norm] at this
  have hO : Continuous O := hL.continuous
  set ε : ℝ := (N : ℝ) ^ (-((n : ℝ) + 2)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hNε : (N : ℝ) ^ n * ε = ((N : ℝ) ^ 2)⁻¹ := by
    rw [hε, ← Real.rpow_natCast, ← Real.rpow_add hNpos, ← Real.rpow_natCast, ← Real.rpow_neg
      hNpos.le]
    congr 1
    push_cast
    ring
  have hlog0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog : 1 ≤ Real.sqrt (Real.log N) := by
    rw [Real.le_sqrt zero_le_one hlog0.le, one_pow, Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  set W : ℝ := D ^ n * Real.sqrt (Real.log N) with hW
  set X : ℝ := b⁻¹ * (N : ℝ)⁻¹ with hX
  set Y : ℝ := (Real.sqrt b)⁻¹ * (Real.sqrt (N * t))⁻¹ with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hB0 : 0 ≤ Bd := le_trans (abs_nonneg _) (hB 0)
  have hmain : corrLHS M O E b t ≤ Main_C1 n ℓ ρO c * (Bd + K) * W * (X + Y) := by
    rcases lt_or_ge ((N : ℝ) * b) 1 with hNb | hNb
    · -- Step 2: `b < 1/N`
      have htr := Main_trivial M hN3 (by linarith) hc hc2 hℓ hH hO hB hsupp hϱ hρℓ hE hb hb2 hC
        hε0 (by rw [hNε]; exact inv_le_one_of_one_le₀ (by nlinarith)) t h1 hcμ
      refine htr.trans ?_
      have hX1 : 1 ≤ X := by
        rw [hX, ← mul_inv, one_le_inv₀ (by positivity)]
        linarith [mul_comm b (N : ℝ)]
      have hKl := Main_Kl_le hℓ.le hD1
      have hl2 : (1 : ℝ) ≤ (ℓ + 2) ^ n := one_le_pow₀ (by linarith)
      have hDn : (1 : ℝ) ≤ D ^ n := one_le_pow₀ hD1
      have hKn : (2 * ℓ / π + 2 * D) ^ n ≤ (ℓ + 2) ^ n * D ^ n := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hKl n
      have hW1 : D ^ n ≤ W := le_mul_of_one_le_right (by positivity) hlog
      have hC1 := Main_C1_pos (n := n) hℓ hρO.le hc hc2
      have h8 : 8 * (ℓ + 2) ^ n ≤ Main_C1 n ℓ ρO c := by
        unfold Main_C1
        have := Main_rhoStar_pos hc hc2
        have := cZero_pos
        have : 0 ≤ 32 * Real.sqrt (3 * n) * n.factorial * (ℓ + 2) ^ (n - 1) *
            (ℓ * (Real.sqrt (2 / cZero) + 3 * Real.sqrt 2 * Real.exp 1 * ρO)) := by positivity
        have : 0 ≤ 4 * n.factorial * ℓ * (4 / rhoStar c + 4 * ℓ + 2) * (ℓ + 2) ^ (n - 1) := by
          positivity
        have : (0 : ℝ) ≤ 4 + 4 * n.factorial * ℓ := by positivity
        linarith
      calc 4 * Bd * ((2 * ℓ / π + 2 * D) ^ n + 1)
          ≤ 4 * Bd * (2 * ((ℓ + 2) ^ n * D ^ n)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith
        _ = 8 * (ℓ + 2) ^ n * (Bd * D ^ n * 1) := by ring
        _ ≤ Main_C1 n ℓ ρO c * ((Bd + K) * W * (X + Y)) := by
            refine mul_le_mul h8 ?_ (by positivity) hC1.le
            refine mul_le_mul (mul_le_mul (by linarith) hW1 (by positivity) (by positivity))
              (by linarith) zero_le_one (by positivity)
        _ = Main_C1 n ℓ ρO c * (Bd + K) * W * (X + Y) := by ring
    · -- Steps 3–7: `b ≥ 1/N`
      have hgap : Main_GapBound N (M.eigLaw t) (gbeLaw 𝕜 N)
          (1 / N + 32 * betaF 𝕜 * D ^ 2 * Real.log N / t) :=
        hN₄ N hN₄N M hM t ht hNt
      have hβ : betaF 𝕜 ≤ 2 := by
        unfold betaF
        exact_mod_cast RCLike.finrank_le_two 𝕜
      have hS := Main_sqrt_S_le (D := D) hNpos hlog0.le ht (by linarith) hβ
      have hcore := Main_core hn0 hN3 hD1 hc hc2 hℓ hH hO hB hLip hK0 hsupp hρO.le hϱ hρℓ hE
        hb hb2 hNb ht hch₁ hch₂ hgap hS hlog hε0 hNε.le h1 hcμ
      rw [Main_corrLHS_eq M hO hB hb t, abs_mul, abs_of_nonneg (by
        have := Main_corrC_nonneg N n
        positivity)]
      refine le_trans ?_ hcore
      have hk : (2 * b)⁻¹ * corrC N n ≤ b⁻¹ := by
        rw [mul_inv, mul_comm (2 : ℝ)⁻¹, mul_assoc]
        refine mul_le_of_le_one_right (by positivity) ?_
        linarith
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have hWE : W ≤ 3 ^ n * Real.exp ((n * A₀ + 1) * Real.log (Real.log N) ^ 2) :=
    Dpar_pow_le h16 (by linarith) n
  have hYr : b ^ (-(1 / 2 : ℝ)) * ((N : ℝ) * t) ^ (-(1 / 2 : ℝ)) = Y := by
    rw [hY, Real.rpow_neg hb.le, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow]
  rw [hYr]
  refine hmain.trans ?_
  have hC1 := Main_C1_pos (n := n) hℓ hρO.le hc hc2
  calc Main_C1 n ℓ ρO c * (Bd + K) * W * (X + Y)
      ≤ Main_C1 n ℓ ρO c * (Bd + K) *
          (3 ^ n * Real.exp ((n * A₀ + 1) * Real.log (Real.log N) ^ 2)) * (X + Y) := by
        gcongr
    _ = 3 ^ n * Main_C1 n ℓ ρO c * (Bd + K) *
          Real.exp ((n * A₀ + 1) * Real.log (Real.log N) ^ 2) * (X + Y) := by ring

/-! ### Corollary 19.5: Hölder test functions

The proof of Corollary 19.5: the Lipschitz approximation `O_r = φ_{ε_r} ∘ Õ_r` with
`Õ_r(u) = inf_v (O(v) + L_r ‖u - v‖)`, `L_r = [O]_α r^{α-1}`, `ε_r = [O]_α r^α` and
`φ_ε(τ) = sign(τ) (|τ| - ε)_+`; the trivial bound of Steps 1, 2 of §19.4 for `O - O_r`;
Theorem 12.1 for `O_r` with `r` the bracket `b⁻¹N⁻¹ + b^{-1/2}N^{-δ/2}` when it is `< 1`. -/

/-- `φ_ε(τ) = sign(τ) (|τ| - ε)_+ = max(τ - ε, 0) + min(τ + ε, 0)`. -/
private noncomputable def Main_shrink (ε τ : ℝ) : ℝ := max (τ - ε) 0 + min (τ + ε) 0

/-- `φ_ε` is `1`-Lipschitz. -/
private lemma Main_shrink_lip {ε : ℝ} (hε : 0 ≤ ε) (a b : ℝ) :
    |Main_shrink ε a - Main_shrink ε b| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  unfold Main_shrink
  simp only [max_def, min_def]
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-- `|φ_ε(τ) - τ| ≤ ε`. -/
private lemma Main_shrink_sub {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ) : |Main_shrink ε τ - τ| ≤ ε := by
  unfold Main_shrink
  simp only [max_def, min_def]
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-- `φ_ε = 0` on `[-ε, ε]`. -/
private lemma Main_shrink_eq_zero {ε τ : ℝ} (h1 : -ε ≤ τ) (h2 : τ ≤ ε) : Main_shrink ε τ = 0 := by
  unfold Main_shrink
  rw [max_eq_right (by linarith), min_eq_right (by linarith)]
  ring

/-- `min(τ + ε, 0) ≤ φ_ε(τ) ≤ max(τ - ε, 0)`. -/
private lemma Main_shrink_le (ε τ : ℝ) :
    min (τ + ε) 0 ≤ Main_shrink ε τ ∧ Main_shrink ε τ ≤ max (τ - ε) 0 := by
  unfold Main_shrink
  constructor <;> linarith [le_max_right (τ - ε) 0, min_le_right (τ + ε) 0]

/-- `τ^α ≤ r^{α-1} τ + r^α` for `τ ≥ 0`, `r > 0`, `0 < α ≤ 1`. -/
private lemma Main_rpow_le {α r τ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) (hτ : 0 ≤ τ) :
    τ ^ α ≤ r ^ (α - 1) * τ + r ^ α := by
  rcases le_or_gt τ r with h | h
  · have h1 := Real.rpow_le_rpow hτ h hα.le
    have h2 : 0 ≤ r ^ (α - 1) * τ := by positivity
    linarith
  · have hτ0 : 0 < τ := hr.trans h
    have e : τ ^ α = τ ^ (α - 1) * τ := by
      rw [Real.rpow_sub_one hτ0.ne', div_mul_cancel₀ _ hτ0.ne']
    have h1 := Real.rpow_le_rpow_of_nonpos hr h.le (by linarith : α - 1 ≤ 0)
    have h2 : τ ^ (α - 1) * τ ≤ r ^ (α - 1) * τ := mul_le_mul_of_nonneg_right h1 hτ
    have h3 : 0 ≤ r ^ α := by positivity
    linarith

/-- A function with `|O(u) - O(v)| ≤ [O]_α ‖u - v‖^α`, `α > 0`, is continuous. -/
private lemma Main_continuous_of_hoelder {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {Hα α : ℝ}
    (hα : 0 < α) (hH : ∀ u v, |O u - O v| ≤ Hα * ‖u - v‖ ^ α) : Continuous O := by
  rw [continuous_iff_continuousAt]
  intro u
  have hc : Continuous fun v : EuclideanSpace ℝ (Fin n) => Hα * ‖v - u‖ ^ α :=
    continuous_const.mul
      (((continuous_id.sub continuous_const).norm).rpow_const fun _ => Or.inr hα.le)
  have h0 : Tendsto (fun v : EuclideanSpace ℝ (Fin n) => Hα * ‖v - u‖ ^ α) (𝓝 u) (𝓝 0) := by
    have := hc.tendsto u
    simpa [Real.zero_rpow hα.ne'] using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun v => by rw [Real.norm_eq_abs]; exact hH v u) h0

/-- For `n ≥ 1` a Hölder constant is nonnegative. -/
private lemma Main_hoelder_nonneg {n : ℕ} (hn : 1 ≤ n) {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {Hα α : ℝ} (hH : ∀ u v, |O u - O v| ≤ Hα * ‖u - v‖ ^ α) : 0 ≤ Hα := by
  have h := hH (EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1) 0
  have e : ‖EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) - 0‖ = 1 := by simp
  rw [e, Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

/-- The Lipschitz approximation in the proof of Corollary 19.5: for `r > 0` the function
`O_r = φ_{ε_r} ∘ Õ_r`, `Õ_r(u) = inf_v (O(v) + L_r ‖u - v‖)`, is `L_r`-Lipschitz, bounded by any
bound of `O`, vanishes outside `[-ρ_O, ρ_O]ⁿ`, and `|O - O_r| ≤ 2 ε_r`, where
`L_r = [O]_α r^{α-1}` and `ε_r = [O]_α r^α`. -/
private lemma Main_approx {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {Bd Hα α r ρO : ℝ}
    (hB : ∀ u, |O u| ≤ Bd) (hH : ∀ u v, |O u - O v| ≤ Hα * ‖u - v‖ ^ α)
    (hsupp : ∀ u, (∃ k, ρO < |u k|) → O u = 0) (hHα : 0 ≤ Hα) (hα : 0 < α) (hα1 : α ≤ 1)
    (hr : 0 < r) :
    ∃ Q : EuclideanSpace ℝ (Fin n) → ℝ, (∀ u, |Q u| ≤ Bd) ∧
      LipschitzWith (Real.toNNReal (Hα * r ^ (α - 1))) Q ∧
      (∀ u, (∃ k, ρO < |u k|) → Q u = 0) ∧ ∀ u, |O u - Q u| ≤ 2 * (Hα * r ^ α) := by
  set L := Hα * r ^ (α - 1) with hL
  set ε := Hα * r ^ α with hε
  have hL0 : 0 ≤ L := by positivity
  have hε0 : 0 ≤ ε := by positivity
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans (hB 0)
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun u => ⨅ v, (O v + L * ‖u - v‖) with hg
  have hbdd : ∀ u, BddBelow (Set.range fun v => O v + L * ‖u - v‖) := fun u =>
    ⟨-Bd, by
      rintro _ ⟨v, rfl⟩
      have h1 := (abs_le.1 (hB v)).1
      have h2 : 0 ≤ L * ‖u - v‖ := by positivity
      linarith⟩
  have hgle : ∀ u v, g u ≤ O v + L * ‖u - v‖ := fun u v => ciInf_le (hbdd u) v
  have hgge : ∀ u a, (∀ v, a ≤ O v + L * ‖u - v‖) → a ≤ g u := fun u a h => le_ciInf h
  have hgO : ∀ u, g u ≤ O u := fun u => by simpa using hgle u u
  have hOg : ∀ u, O u - ε ≤ g u := fun u => hgge u _ fun v => by
    have h1 := (abs_le.1 (hH u v)).2
    have h2 := mul_le_mul_of_nonneg_left (Main_rpow_le hα hα1 hr (norm_nonneg (u - v))) hHα
    have e : Hα * (r ^ (α - 1) * ‖u - v‖ + r ^ α) = L * ‖u - v‖ + ε := by rw [hL, hε]; ring
    linarith
  have hglip : ∀ u u', g u ≤ g u' + L * ‖u - u'‖ := fun u u' => by
    have : g u - L * ‖u - u'‖ ≤ g u' := hgge u' _ fun v => by
      have h1 := hgle u v
      have h2 := mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub u u' v) hL0
      linarith
    linarith
  refine ⟨fun u => Main_shrink ε (g u), fun u => ?_, ?_, fun u hu => ?_, fun u => ?_⟩
  · obtain ⟨h1, h2⟩ := Main_shrink_le ε (g u)
    have h3 := abs_le.1 (hB u)
    have h4 : -Bd ≤ min (g u + ε) 0 := le_min (by linarith [hOg u]) (by linarith)
    have h5 : max (g u - ε) 0 ≤ Bd := max_le (by linarith [hgO u]) hBd0
    rw [abs_le]
    constructor <;> linarith
  · refine LipschitzWith.of_dist_le_mul fun u u' => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]
    refine (Main_shrink_lip hε0 _ _).trans (abs_sub_le_iff.2 ⟨?_, ?_⟩)
    · linarith [hglip u u']
    · have h := hglip u' u
      rw [norm_sub_rev] at h
      linarith
  · have h0 := hsupp u hu
    have h1 := hgO u
    have h2 := hOg u
    exact Main_shrink_eq_zero (by linarith) (by linarith)
  · refine (abs_sub_le (O u) (g u) _).trans ?_
    have h1 : |O u - g u| ≤ ε := by
      rw [abs_le]
      constructor <;> linarith [hgO u, hOg u]
    have h2 : |g u - Main_shrink ε (g u)| ≤ ε := by
      rw [abs_sub_comm]
      exact Main_shrink_sub hε0 _
    linarith

/-- Subadditivity of `corrLHS` in the test function (from Step 1 of §19.4): for continuous bounded
`Q, P` and `O = Q + P`, `corrLHS(O) ≤ corrLHS(Q) + corrLHS(P)`. -/
private lemma Main_corrLHS_le_add {N n : ℕ} (M : Ensemble 𝕜 N)
    {O Q P : EuclideanSpace ℝ (Fin n) → ℝ} {B B' : ℝ} (hQ : Continuous Q) (hP : Continuous P)
    (hQB : ∀ u, |Q u| ≤ B) (hPB : ∀ u, |P u| ≤ B') (hO : ∀ u, O u = Q u + P u) {E b : ℝ}
    (hb : 0 < b) (t : ℝ) :
    corrLHS M O E b t ≤ corrLHS M Q E b t + corrLHS M P E b t := by
  obtain rfl : O = fun u => Q u + P u := funext hO
  have hS : Continuous (fun u => Q u + P u) := hQ.add hP
  have hSB : ∀ u, |Q u + P u| ≤ B + B' := fun u =>
    (abs_add_le _ _).trans (add_le_add (hQB u) (hPB u))
  have := Main_isProbabilityMeasure_eigLaw M t
  have := Main_isProbabilityMeasure_gbeLaw (𝕜 := 𝕜) N
  have hZ : ∀ x : Fin N → ℝ, Main_Z (fun u => Q u + P u) E b (rhoSc E) x =
      Main_Z Q E b (rhoSc E) x + Main_Z P E b (rhoSc E) x := by
    intro x
    have hc : ∀ {F : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous F →
        Continuous fun E' => corrX (N := N) F E' (rhoSc E) x := fun hF =>
      (continuous_corrX hF (rhoSc E)).comp (continuous_id.prodMk continuous_const)
    unfold Main_Z
    rw [← intervalIntegral.integral_add ((hc hQ).intervalIntegrable _ _)
      ((hc hP).intervalIntegrable _ _)]
    congr 1
    funext E'
    unfold corrX
    rw [← Finset.sum_add_distrib]
  rw [Main_corrLHS_eq M hS hSB hb, Main_corrLHS_eq M hQ hQB hb, Main_corrLHS_eq M hP hPB hb]
  simp only [hZ]
  rw [integral_add (Main_integrable_Z hQ hQB hb _ _) (Main_integrable_Z hP hPB hb _ _),
    integral_add (Main_integrable_Z hQ hQB hb _ _) (Main_integrable_Z hP hPB hb _ _)]
  refine le_trans (le_of_eq ?_) (abs_add_le _ _)
  congr 1
  ring

/-- Eventually `(log N)² ≤ N^s`, for `s > 0`. -/
private lemma Main_eventually_log_sq {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ 2 ≤ (N : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 hs).bound one_pos
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with N hN
  rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hN
  calc Real.log N ^ 2 = |Real.log N ^ 2| := (abs_of_nonneg (sq_nonneg _)).symm
    _ ≤ |(N : ℝ) ^ s| := hN
    _ = (N : ℝ) ^ s := abs_of_nonneg (by positivity)

/-- Corollary 19.5 (Hölder test functions), for one tuple of (RA1) constants. -/
theorem dbm_localErgodicity_hoelder_of_rigidityBound {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ)
    (hδm : 0 < δm) (hδp : 0 < δp) (hC₀ : 0 < C₀) {A₀ CR cR φ : ℝ} {N₀ : ℕ}
    (hR : RigidityBound 𝕜 (tildeTheta ϑ) (tildeDelta δm) (tildeDelta δp) (tildeC C₀)
      A₀ CR cR φ N₀) {ε' δ : ℝ} (hε' : 0 < ε') (hδ : 0 < δ) {c : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 2) {n : ℕ} (hn : 1 ≤ n) {ρO : ℝ} (hρO : 0 < ρO) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∃ N₂ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, N₂ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd Hα : ℝ, (∀ u, |O u| ≤ Bd) →
      (∀ u v, |O u - O v| ≤ Hα * ‖u - v‖ ^ α) → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + Hα) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2)) ^ α := by
  have hA₀ : 1 < A₀ := hR.1
  have hρs := Main_rhoStar_pos hc hc2
  set ℓ : ℝ := max 1 (ρO / rhoStar c) with hℓdef
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hℓ : 0 < ℓ := by linarith
  obtain ⟨A₁, -, Nq, -, C₁, hC₁, hT⟩ :=
    dbm_quantitative_of_rigidityBound (𝕜 := 𝕜) hϑ hδm hδp hC₀ hR hc hc2 hn hρO
  obtain ⟨Nc, hNc⟩ := exists_Nq A₀ ℓ hc hc2
  obtain ⟨NK, hNK⟩ := flowGoodSet_compl_le hϑ hδm hδp hC₀ hR ((n : ℝ) + 2) (by positivity)
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp ((Main_eventually_loglog (A := A₁) hε').and
    ((Main_eventually_loglog (A := n * A₀ + 1) hε').and
      (Main_eventually_log_sq (s := δ + ε') (by linarith))))
  set K0 : ℝ := 8 * 3 ^ n * (ℓ + 2) ^ n with hK0
  have hK00 : 0 < K0 := by positivity
  refine ⟨max (max (max Nq n) (max Nc NK)) (max (n ^ 2) Ne), 2 * K0 + C₁, by positivity, ?_⟩
  intro N hN M hM O Bd Hα hB hH hsupp E hE b hb hb2 t ht
  have hNqN : max Nq n ≤ N := by omega
  have hNcN : Nc ≤ N := by omega
  have hNKN : NK ≤ N := by omega
  have hn2 : n ^ 2 ≤ N := by omega
  have hNeN : Ne ≤ N := by omega
  obtain ⟨h16, hD2, -, -, hHc⟩ := hNc N hNcN
  obtain ⟨hE1, hE2, hE3⟩ := hNe N hNeN
  have hN3 : 3 ≤ N := by omega
  have hNR : (16 : ℝ) ≤ N := by exact_mod_cast h16
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set D := Dpar A₀ N with hDdef
  have hD0 : 0 ≤ D := by linarith
  obtain ⟨hct, hcμ⟩ := hNK N hNKN M hM
  have hϱs := Main_rhoStar_le_rhoSc hc hc2 hE
  have hϱ : 0 < rhoSc E := lt_of_lt_of_le hρs hϱs
  have hρℓ : ρO ≤ ℓ * rhoSc E := by
    have : ρO = ρO / rhoStar c * rhoStar c := by field_simp
    calc ρO = ρO / rhoStar c * rhoStar c := this
      _ ≤ ℓ * rhoSc E := mul_le_mul (le_max_right _ _) hϱs hρs.le (by linarith)
  have hC := corrC_le_two hn hn2
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans (hB 0)
  have hHα0 : 0 ≤ Hα := Main_hoelder_nonneg hn hH
  have hO : Continuous O := Main_continuous_of_hoelder hα hH
  -- the time: `N t ≥ N^{δ+ε'} ≥ (log N)²`
  have hNt : (N : ℝ) ^ (δ + ε') ≤ N * t := by
    rw [show δ + ε' = 1 + (-1 + δ + ε') by ring, Real.rpow_add hNpos, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left ht hNpos.le
  have htpos : 0 < t := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) ht
  have hlogt : Real.log N ^ 2 ≤ N * t := hE3.trans hNt
  -- the good set: `N^n ν(Ξᶜ) ≤ 1`
  set ε : ℝ := (N : ℝ) ^ (-((n : ℝ) + 2)) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hNε : (N : ℝ) ^ n * ε ≤ 1 := by
    have e : (N : ℝ) ^ n * ε = ((N : ℝ) ^ 2)⁻¹ := by
      rw [hε, ← Real.rpow_natCast, ← Real.rpow_add hNpos, ← Real.rpow_natCast,
        ← Real.rpow_neg hNpos.le]
      congr 1
      push_cast
      ring
    rw [e]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have h1 := hct t htpos.le
  -- `e^{A (log log N)²} ≤ N^{ε'}` and `D^n ≤ 3^n N^{ε'}`
  have hS1 : 1 ≤ (N : ℝ) ^ ε' := Real.one_le_rpow hN1 hε'.le
  have hS2 : (N : ℝ) ^ ε' ≤ (N : ℝ) ^ (2 * ε') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hexpS : ∀ A : ℝ, A * Real.log (Real.log N) ^ 2 ≤ ε' * Real.log N →
      Real.exp (A * Real.log (Real.log N) ^ 2) ≤ (N : ℝ) ^ ε' := fun A h => by
    rw [Real.rpow_def_of_pos hNpos]
    exact Real.exp_le_exp.2 (by linarith [mul_comm (Real.log N) ε'])
  have hlog0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hsqrt : 1 ≤ Real.sqrt (Real.log N) := by
    rw [Real.le_sqrt zero_le_one hlog0.le, one_pow, Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    linarith
  have hDn : D ^ n ≤ 3 ^ n * (N : ℝ) ^ ε' := by
    have h := Dpar_pow_le (A₀ := A₀) h16 (by linarith) n
    have hD0' : 0 ≤ D ^ n := by positivity
    calc D ^ n ≤ D ^ n * Real.sqrt (Real.log N) := le_mul_of_one_le_right hD0' hsqrt
      _ ≤ 3 ^ n * Real.exp ((n * A₀ + 1) * Real.log (Real.log N) ^ 2) := h
      _ ≤ 3 ^ n * (N : ℝ) ^ ε' := mul_le_mul_of_nonneg_left (hexpS _ hE2) (by positivity)
  -- the trivial bound, `corrLHS(P) ≤ 8 (ℓ + 2)^n D^n ‖P‖_∞ ≤ K0 N^{ε'} ‖P‖_∞`
  have htriv : ∀ (P : EuclideanSpace ℝ (Fin n) → ℝ) (B : ℝ), Continuous P →
      (∀ u, |P u| ≤ B) → (∀ u, (∃ k, ρO < |u k|) → P u = 0) →
      corrLHS M P E b t ≤ K0 * (N : ℝ) ^ ε' * B := by
    intro P B hP hPB hPs
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hPB 0)
    have h := Main_trivial M hN3 hD0 hc hc2 hℓ hHc hP hPB hPs hϱ hρℓ hE hb hb2 hC hε0 hNε t h1
      hcμ
    have hKl := Main_Kl_le hℓ.le (by linarith : 1 ≤ D)
    have hDn1 : (1 : ℝ) ≤ D ^ n := one_le_pow₀ (by linarith)
    have hl2 : (1 : ℝ) ≤ (ℓ + 2) ^ n := one_le_pow₀ (by linarith)
    have hKn : (2 * ℓ / π + 2 * D) ^ n ≤ (ℓ + 2) ^ n * D ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hKl n
    refine h.trans ?_
    calc 4 * B * ((2 * ℓ / π + 2 * D) ^ n + 1) ≤ 4 * B * (2 * ((ℓ + 2) ^ n * D ^ n)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := one_le_mul_of_one_le_of_one_le hl2 hDn1
          linarith
      _ = 8 * (ℓ + 2) ^ n * B * D ^ n := by ring
      _ ≤ 8 * (ℓ + 2) ^ n * B * (3 ^ n * (N : ℝ) ^ ε') :=
          mul_le_mul_of_nonneg_left hDn (by positivity)
      _ = K0 * (N : ℝ) ^ ε' * B := by rw [hK0]; ring
  -- Theorem 12.1 with `e^{A₁ (log log N)²} ≤ N^{ε'}` and `(N t)^{-1/2} ≤ N^{-δ/2}`
  set R : ℝ := b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2) with hRdef
  have hRpos : 0 < R := by positivity
  have hLip : ∀ (Q : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0), (∀ u, |Q u| ≤ Bd) →
      LipschitzWith K Q → (∀ u, (∃ k, ρO < |u k|) → Q u = 0) →
      corrLHS M Q E b t ≤ C₁ * (Bd + K) * (N : ℝ) ^ ε' * R := by
    intro Q K hQB hQL hQs
    have h := hT N hNqN M hM Q Bd K hQB hQL hQs t htpos hlogt E hE b hb hb2
    refine h.trans ?_
    have hbr : b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * ((N : ℝ) * t) ^ (-(1 / 2 : ℝ)) ≤ R := by
      have hNδ : (N : ℝ) ^ δ ≤ N * t :=
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hNt
      have h2 : ((N : ℝ) * t) ^ (-(1 / 2 : ℝ)) ≤ (N : ℝ) ^ (-δ / 2) := by
        have := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos δ) hNδ
          (by norm_num : -(1 / 2 : ℝ) ≤ 0)
        rwa [← Real.rpow_mul hNpos.le, show δ * (-(1 / 2 : ℝ)) = -δ / 2 by ring] at this
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ b ^ (-(1 / 2 : ℝ)))
      rw [hRdef]
      linarith
    have hK : (0 : ℝ) ≤ Bd + K := by linarith [NNReal.coe_nonneg K]
    have hbr0 : 0 ≤ b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * ((N : ℝ) * t) ^ (-(1 / 2 : ℝ)) := by
      positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hexpS _ hE1) (by positivity)) hbr hbr0
      (by positivity)
  rcases le_or_gt 1 R with hR1 | hR1
  · -- `R ≥ 1`: the trivial bound for `O`
    have hRα : 1 ≤ R ^ α := Real.one_le_rpow hR1 hα.le
    calc corrLHS M O E b t ≤ K0 * (N : ℝ) ^ ε' * Bd := htriv O Bd hO hB hsupp
      _ = K0 * Bd * (N : ℝ) ^ ε' * 1 := by ring
      _ ≤ (2 * K0 + C₁) * (Bd + Hα) * (N : ℝ) ^ (2 * ε') * R ^ α :=
          mul_le_mul (mul_le_mul (mul_le_mul (by linarith) (by linarith) hBd0 (by positivity))
            hS2 (by positivity) (by positivity)) hRα zero_le_one (by positivity)
  · -- `R < 1`: the approximation `O_r` with `r = R`
    obtain ⟨Q, hQB, hQL, hQs, hOQ⟩ := Main_approx hB hH hsupp hHα0 hα hα1 hRpos
    have hQc : Continuous Q := hQL.continuous
    have hPc : Continuous fun u => O u - Q u := hO.sub hQc
    have hPs : ∀ u : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |u k|) → O u - Q u = 0 :=
      fun u hu => by rw [hsupp u hu, hQs u hu, sub_self]
    have hsplit : corrLHS M O E b t ≤
        corrLHS M Q E b t + corrLHS M (fun u => O u - Q u) E b t :=
      Main_corrLHS_le_add M hQc hPc hQB hOQ (fun u => by ring) hb t
    have hmain := hLip Q _ hQB hQL hQs
    rw [Real.coe_toNNReal _ (by positivity)] at hmain
    have herr := htriv (fun u => O u - Q u) _ hPc hOQ hPs
    have hRα0 : 0 < R ^ α := Real.rpow_pos_of_pos hRpos α
    have hRRα : R ≤ R ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge hRpos hR1.le hα1
      rwa [Real.rpow_one] at this
    have hRe : R ^ (α - 1) * R = R ^ α := by
      rw [Real.rpow_sub_one hRpos.ne', div_mul_cancel₀ _ hRpos.ne']
    set S : ℝ := (N : ℝ) ^ ε' with hS
    set T : ℝ := R ^ α with hTdef
    have hS0 : 0 ≤ S := by linarith
    have hm : C₁ * (Bd + Hα * R ^ (α - 1)) * S * R ≤ C₁ * ((Bd + Hα) * S * T) := by
      have e : C₁ * (Bd + Hα * R ^ (α - 1)) * S * R =
          C₁ * S * (Bd * R + Hα * (R ^ (α - 1) * R)) := by ring
      have e2 : C₁ * ((Bd + Hα) * S * T) = C₁ * S * (Bd * T + Hα * T) := by ring
      rw [e, e2, hRe]
      have : Bd * R ≤ Bd * T := mul_le_mul_of_nonneg_left hRRα hBd0
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have he : K0 * S * (2 * (Hα * T)) ≤ 2 * K0 * ((Bd + Hα) * S * T) := by
      have h3 : Hα * S * T ≤ (Bd + Hα) * S * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hS0) hRα0.le
      have e : K0 * S * (2 * (Hα * T)) = 2 * K0 * (Hα * S * T) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    calc corrLHS M O E b t ≤ corrLHS M Q E b t + corrLHS M (fun u => O u - Q u) E b t := hsplit
      _ ≤ C₁ * ((Bd + Hα) * S * T) + 2 * K0 * ((Bd + Hα) * S * T) :=
          add_le_add (hmain.trans hm) (herr.trans he)
      _ = (2 * K0 + C₁) * (Bd + Hα) * S * T := by ring
      _ ≤ (2 * K0 + C₁) * (Bd + Hα) * (N : ℝ) ^ (2 * ε') * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS2 (by positivity)) hRα0.le

end Rigidity
