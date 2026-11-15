import Rigidity.Fluctuation.Main
import Rigidity.LocalLaw.Weak

/-!
# Fluctuation averaging on the lattice (NP v1.1, §6.8: Corollary 6.2)

Numbers in this file refer to the blueprint NP v1.1.
-/

/-! Corollary 6.2 is the form of Theorem 6.1 used in §7: at `p ∈ {p₁, p₂}` and `z` in the lattice
`𝕃`, the averaged quantity `N⁻¹ ∑ₖ Xₖ(z)` has `L^p` norm at most
`K^{12ϑ⁻¹+11} ‖Φ_*(z)²‖_p + N^{-8}`. The proof applies Theorem 6.1 with `tₖ = 1/N`: its hypotheses
follow from the standing inequalities of Lemma 4.6, the definition of the lattice and
Definition 5.1. The tail `N² ℙ(Ξ_p(z)ᶜ)^{1/(2p)}` is bounded by Theorem 5.5 (c) through the
inclusion `Ξ(z) = Ξ_{p₁}(z) ⊆ Ξ_p(z)`. Numerically it needs `C_F p^{8ϑ⁻¹+7} ≤ K^{12ϑ⁻¹+11}`,
`p^{12ϑ⁻¹+11} ≤ N η` and `p ≤ N^{1/(40ϑ⁻¹+40)}`, which use the ledger (A.1). The compiled example
at the end instantiates the statement at the Rademacher ensemble. -/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For an a.e. strongly measurable `f` and an exponent `p ∈ ℕ`, `p ≠ 0`, the `L^p` seminorm is
`(∫⁻ ‖f‖ₑ^p)^{1/p}`. -/
private lemma faLat_eLpNorm_nat {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) {p : ℕ} (hp : p ≠ 0) :
    eLpNorm f (p : ℝ≥0∞) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by simp) hf]
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast]

/-- Taking `p`-th roots in a bound of the shape (6.3), with `(u + v)^{1/p} ≤ u^{1/p} + v^{1/p}`
in `[0, ∞]`. -/
private lemma faLat_root {I J ν : ℝ≥0∞} {b n : ℝ} (hb : 0 ≤ b) (hn : 0 ≤ n) {p : ℕ} (hp : p ≠ 0)
    (h : I ≤ ENNReal.ofReal (b ^ p) * J + ENNReal.ofReal (n ^ p) * ν ^ (1 / 2 : ℝ)) :
    I ^ (1 / (p : ℝ)) ≤ ENNReal.ofReal b * J ^ (1 / (p : ℝ)) +
      ENNReal.ofReal n * ν ^ (1 / (2 * (p : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]; exact_mod_cast Nat.pos_of_ne_zero hp
  have e : ∀ c : ℝ, 0 ≤ c → ENNReal.ofReal (c ^ p) ^ (1 / (p : ℝ)) = ENNReal.ofReal c :=
      fun c hc => by
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hc _) hq0, ← Real.rpow_natCast,
      ← Real.rpow_mul hc, mul_one_div_cancel hp0.ne', Real.rpow_one]
  calc I ^ (1 / (p : ℝ))
      ≤ (ENNReal.ofReal (b ^ p) * J + ENNReal.ofReal (n ^ p) * ν ^ (1 / 2 : ℝ)) ^ (1 / (p : ℝ)) :=
        ENNReal.rpow_le_rpow h hq0
    _ ≤ (ENNReal.ofReal (b ^ p) * J) ^ (1 / (p : ℝ)) +
          (ENNReal.ofReal (n ^ p) * ν ^ (1 / 2 : ℝ)) ^ (1 / (p : ℝ)) :=
        ENNReal.rpow_add_le_add_rpow _ _ hq0 hq1
    _ = ENNReal.ofReal b * J ^ (1 / (p : ℝ)) + ENNReal.ofReal n * ν ^ (1 / (2 * (p : ℝ))) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.mul_rpow_of_nonneg _ _ hq0, e b hb, e n hn,
        ← ENNReal.rpow_mul]
      congr 3
      field_simp

/-- The tail term of the proof of Corollary 6.2: `N² (C N⁹ e^{-K²})^{1/(2p)} ≤ N^{-8}` when
`C ≤ N`, `p ≥ 2` and `K² ≥ 40 p log N`. -/
private lemma faLat_tail {N p : ℕ} {C K : ℝ} (hN : 2 ≤ N) (hp : 2 ≤ p) (hC0 : 0 ≤ C)
    (hC : C ≤ N) (hK : 40 * p * Real.log N ≤ K ^ 2) :
    (N : ℝ) ^ 2 * (C * (N : ℝ) ^ 9 * Real.exp (-K ^ 2)) ^ (1 / (2 * (p : ℝ))) ≤
      (N : ℝ) ^ (-8 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set L := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hN1
  have hNe : (N : ℝ) = Real.exp L := (Real.exp_log hN0).symm
  have hq0 : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
  have hX : C * (N : ℝ) ^ 9 * Real.exp (-K ^ 2) ≤ Real.exp (10 * L - 40 * p * L) := by
    have h1 : C * (N : ℝ) ^ 9 ≤ Real.exp (10 * L) := by
      calc C * (N : ℝ) ^ 9 ≤ (N : ℝ) * (N : ℝ) ^ 9 := by gcongr
        _ = Real.exp (10 * L) := by
          rw [show (N : ℝ) * (N : ℝ) ^ 9 = (N : ℝ) ^ 10 by ring, hNe, ← Real.exp_nat_mul]
          norm_num
    have h2 : Real.exp (-K ^ 2) ≤ Real.exp (-(40 * p * L)) :=
      Real.exp_le_exp.2 (by linarith)
    calc C * (N : ℝ) ^ 9 * Real.exp (-K ^ 2) ≤ Real.exp (10 * L) * Real.exp (-(40 * p * L)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (10 * L - 40 * p * L) := by rw [← Real.exp_add]; ring_nf
  have hXr : (C * (N : ℝ) ^ 9 * Real.exp (-K ^ 2)) ^ (1 / (2 * (p : ℝ))) ≤
      Real.exp (5 * L / 2 - 20 * L) := by
    calc (C * (N : ℝ) ^ 9 * Real.exp (-K ^ 2)) ^ (1 / (2 * (p : ℝ)))
        ≤ (Real.exp (10 * L - 40 * p * L)) ^ (1 / (2 * (p : ℝ))) :=
          Real.rpow_le_rpow (by positivity) hX hq0
      _ = Real.exp ((10 * L - 40 * p * L) * (1 / (2 * (p : ℝ)))) := (Real.exp_mul _ _).symm
      _ ≤ Real.exp (5 * L / 2 - 20 * L) := by
          apply Real.exp_le_exp.2
          have : (10 * L - 40 * p * L) * (1 / (2 * (p : ℝ))) = 5 * L / p - 20 * L := by
            field_simp; ring
          rw [this]
          have : 5 * L / p ≤ 5 * L / 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hp2
          linarith
  have h8 : (N : ℝ) ^ (-8 : ℝ) = Real.exp (-8 * L) := by
    rw [Real.rpow_def_of_pos hN0, ← hL]; ring_nf
  calc (N : ℝ) ^ 2 * (C * (N : ℝ) ^ 9 * Real.exp (-K ^ 2)) ^ (1 / (2 * (p : ℝ)))
      ≤ Real.exp (2 * L) * Real.exp (5 * L / 2 - 20 * L) := by
        refine mul_le_mul ?_ hXr (by positivity) (Real.exp_pos _).le
        rw [hNe, ← Real.exp_nat_mul]; norm_num
    _ = Real.exp (2 * L + (5 * L / 2 - 20 * L)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-8 * L) := Real.exp_le_exp.2 (by linarith)
    _ = (N : ℝ) ^ (-8 : ℝ) := h8.symm


/-- `p^s ≤ 2^s K^{3s/2}` from `p ≤ 2 K^{3/2}` and `s ≥ 0`. -/
private lemma faLat_pow_le {p K s : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (h : p ≤ 2 * K ^ (3 / 2 : ℝ)) : p ^ s ≤ 2 ^ s * K ^ (3 / 2 * s) := by
  calc p ^ s ≤ (2 * K ^ (3 / 2 : ℝ)) ^ s := Real.rpow_le_rpow hp h hs
    _ = 2 ^ s * (K ^ (3 / 2 : ℝ)) ^ s := Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK _)
    _ = 2 ^ s * K ^ (3 / 2 * s) := by rw [← Real.rpow_mul hK]

/-- The constant of Corollary 6.2: `C_F p^{8a+7} ≤ K^{12a+11}` for `p ≤ 2 K^{3/2}` and
`K ≥ (C_F 2^{8a+7})²`. -/
private lemma faLat_rowA {a K p CF : ℝ} (hCF : 0 < CF) (ha : 1 ≤ a) (hK : 1 ≤ K) (hp0 : 0 ≤ p)
    (hp : p ≤ 2 * K ^ (3 / 2 : ℝ)) (hK0 : (CF * 2 ^ (8 * a + 7)) ^ 2 ≤ K) :
    CF * p ^ (8 * a + 7) ≤ K ^ (12 * a + 11) := by
  have hK0' : 0 < K := by linarith
  have h1 := faLat_pow_le hp0 hK0'.le (by linarith : 0 ≤ 8 * a + 7) hp
  have h2 : CF * 2 ^ (8 * a + 7) ≤ K ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by positivity) hK0'.le).2 hK0
  calc CF * p ^ (8 * a + 7) ≤ CF * (2 ^ (8 * a + 7) * K ^ (3 / 2 * (8 * a + 7))) := by gcongr
    _ = (CF * 2 ^ (8 * a + 7)) * K ^ (3 / 2 * (8 * a + 7)) := by ring
    _ ≤ K ^ (1 / 2 : ℝ) * K ^ (3 / 2 * (8 * a + 7)) := by gcongr
    _ = K ^ (12 * a + 11) := by
      rw [← Real.rpow_add hK0']; congr 1; ring

/-- In the near regime, `p^{12a+11} ≤ K^{18a+19}` for `p ≤ 2 K^{3/2}` and `K ≥ 2^{12a+11}`;
this gives the hypothesis `N η ≥ p^{12a+11}` of Theorem 6.1 since `N η ≥ K^{18a+19}`. -/
private lemma faLat_near_pow {a K p : ℝ} (ha : 1 ≤ a) (hK : 1 ≤ K) (hp0 : 0 ≤ p)
    (hp : p ≤ 2 * K ^ (3 / 2 : ℝ)) (hK0 : 2 ^ (12 * a + 11) ≤ K) :
    p ^ (12 * a + 11) ≤ K ^ (18 * a + 19) := by
  have hK0' : 0 < K := by linarith
  have h1 := faLat_pow_le hp0 hK0'.le (by linarith : 0 ≤ 12 * a + 11) hp
  have h2 : K ≤ K ^ (5 / 2 : ℝ) := by
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ ≤ K ^ (5 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by norm_num)
  calc p ^ (12 * a + 11) ≤ 2 ^ (12 * a + 11) * K ^ (3 / 2 * (12 * a + 11)) := h1
    _ ≤ K ^ (5 / 2 : ℝ) * K ^ (3 / 2 * (12 * a + 11)) := by
        gcongr; exact hK0.trans h2
    _ = K ^ (18 * a + 19) := by
      rw [← Real.rpow_add hK0']; congr 1; ring

/-- The hypothesis `p ≤ N^{1/(40a+40)}` of Theorem 6.1 from `p ≤ 2 K^{3/2}` and
`2 ≤ K ≤ N^{c₀}`, with `c₀` of the exponent ledger (A.1). -/
private lemma faLat_p_le {a N K p : ℝ} (ha : 1 ≤ a) (hN : 1 ≤ N) (hK2 : 2 ≤ K)
    (hKN : K ≤ N ^ ledgerc0 a) (hp : p ≤ 2 * K ^ (3 / 2 : ℝ)) :
    p ≤ N ^ (1 / (40 * a + 40)) := by
  have hK0' : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have h1 : 2 * K ^ (3 / 2 : ℝ) ≤ K ^ (5 / 2 : ℝ) := by
    calc 2 * K ^ (3 / 2 : ℝ) ≤ K * K ^ (3 / 2 : ℝ) := by gcongr
      _ = K ^ (5 / 2 : ℝ) := by
        rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hK0', Real.rpow_one]
  have h2 : K ^ (5 / 2 : ℝ) ≤ N ^ (1 / (40 * a + 40)) := by
    calc K ^ (5 / 2 : ℝ) ≤ (N ^ ledgerc0 a) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow hK0'.le hKN (by norm_num)
      _ = N ^ (ledgerc0 a * (5 / 2)) := (Real.rpow_mul hN0.le _ _).symm
      _ ≤ N ^ (1 / (40 * a + 40)) := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        have : ledgerc0 a * (5 / 2) = 5 / (384 * a + 576) := by
          unfold ledgerc0 ledgerC3; field_simp; ring
        rw [this]
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
  exact hp.trans (h1.trans h2)

/-- The hypothesis `p^{12a+11} ≤ N η` of Theorem 6.1 in the far regime, from
`p ≤ N^{1/(40a+40)}`, `η ≥ 1/(2√N)` and `N ≥ 32`. -/
private lemma faLat_far_pow {a N p η : ℝ} (ha : 1 ≤ a) (hN : 32 ≤ N) (hp0 : 0 ≤ p)
    (hp : p ≤ N ^ (1 / (40 * a + 40))) (hη : 1 / (2 * Real.sqrt N) ≤ η) :
    p ^ (12 * a + 11) ≤ N * η := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h5 : (2 : ℝ) ≤ N ^ (1 / 5 : ℝ) := by
    have h32 : (32 : ℝ) ^ (1 / 5 : ℝ) ≤ N ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hN (by norm_num)
    have : (32 : ℝ) ^ (1 / 5 : ℝ) = 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have h1 : p ^ (12 * a + 11) ≤ N ^ (3 / 10 : ℝ) := by
    calc p ^ (12 * a + 11) ≤ (N ^ (1 / (40 * a + 40))) ^ (12 * a + 11) :=
          Real.rpow_le_rpow hp0 hp (by linarith)
      _ = N ^ (1 / (40 * a + 40) * (12 * a + 11)) := (Real.rpow_mul hN0.le _ _).symm
      _ ≤ N ^ (3 / 10 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          rw [one_div_mul_eq_div, div_le_div_iff₀ (by linarith) (by norm_num)]
          linarith
  have h2 : N ^ (3 / 10 : ℝ) * 2 ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = 3 / 10 + 1 / 5 by norm_num, Real.rpow_add hN0]
    gcongr
  have h3 : Real.sqrt N / 2 ≤ N * η := by
    calc Real.sqrt N / 2 = N * (1 / (2 * Real.sqrt N)) := by
          have := Real.mul_self_sqrt hN0.le
          field_simp
          nlinarith
      _ ≤ N * η := by gcongr
  linarith

/-- The hypothesis `|z| ≤ N` of Theorem 6.1 in the near regime, from `|Re z| ≤ 5`,
`0 ≤ Im z ≤ 10` and `N ≥ 15`. -/
private lemma faLat_norm_near {z : ℂ} {N : ℝ} (hN : 15 ≤ N) (hre : |z.re| ≤ 5) (him : z.im ≤ 10)
    (him0 : 0 ≤ z.im) : ‖z‖ ≤ N := by
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg him0] at this
  linarith

/-- The hypothesis `|z| ≤ N` of Theorem 6.1 in the far regime, from `|Re z| ≤ E + 1`,
`E ≤ N^{1/32}`, `0 ≤ Im z ≤ 10` and `N ≥ 32`. -/
private lemma faLat_norm_far {z : ℂ} {N E : ℝ} (hN : 32 ≤ N) (hE : E ≤ N ^ (1 / 32 : ℝ))
    (hre : |z.re| ≤ E + 1) (him : z.im ≤ 10) (him0 : 0 ≤ z.im) : ‖z‖ ≤ N := by
  have hN0 : 0 < N := by linarith
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg him0] at h
  have h1 : N ^ (1 / 32 : ℝ) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hs4 : 4 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) hN0.le).2 (by linarith)
  have hss := Real.mul_self_sqrt hN0.le
  nlinarith


/-- Corollary 6.2: the form used in §7, at `p ∈ {p₁, p₂}` on the lattice. -/
theorem fluctuationAveraging_lattice {ϑ δm δp C₀ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hδm : 0 < δm)
    (hδm1 : δm ≤ 1) (hδp : 0 < δp) (hδp1 : δp ≤ 1) (hC₀ : 1 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
      ∀ K : ℝ, Real.log N ^ 3 ≤ K → K ≤ (N : ℝ) ^ ledgerc0 ϑ⁻¹ → ∀ z ∈ lattice ϑ⁻¹ C₀ K N,
      ∀ p ∈ ({levelP1 K, levelP2 K} : Finset ℕ),
        eLpNorm (fun x => (N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k) p M.prodLaw ≤
          ENNReal.ofReal (K ^ (12 * ϑ⁻¹ + 11)) *
              eLpNorm (fun x => phiStarSq p x z) p M.prodLaw +
            ENNReal.ofReal ((N : ℝ) ^ (-8 : ℝ)) := by
  classical
  have ha : 1 ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  obtain ⟨CF, p₀, hCF, N₁, h1⟩ := fluctuationAveraging (𝕜 := 𝕜) hϑ hϑ1 hδm hδp hC₀
  obtain ⟨Cw, hCw, N₂, h2⟩ := weakLaw_lattice (𝕜 := 𝕜) hϑ hϑ1 hδm hδm1 hδp hδp1 hC₀
  obtain ⟨N₃, h3⟩ := standing_ineq hϑ hϑ1 hC₀
    (max (max 2 p₀) (max (2 ^ (12 * ϑ⁻¹ + 11)) ((CF * 2 ^ (8 * ϑ⁻¹ + 7)) ^ 2)))
  obtain ⟨N₄, h4⟩ := Filter.eventually_atTop.1
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop Cw |>.and
      (Filter.eventually_ge_atTop 32))
  refine ⟨max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro N hN M hM K hK1 hK2 z hz p hp
  have hN1 : N₁ ≤ N := by omega
  have hN2 : N₂ ≤ N := by omega
  have hN3 : N₃ ≤ N := by omega
  have hN4 : N₄ ≤ N := by omega
  obtain ⟨hCwN, hN32⟩ := h4 N hN4
  obtain ⟨⟨hK0, h13, -, -⟩, ⟨-, -, -, hEmax⟩, ⟨hlev1, hlev2, hKp2, hKp1, hp1le⟩, hS4⟩ :=
    h3 N hN3 K hK1 hK2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN32r : (32 : ℝ) ≤ N := by exact_mod_cast hN32
  -- consequences of the choice of `K₀`
  have hK2' : 2 ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK0
  have hKp₀ : p₀ ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK0
  have hK2pow : (2 : ℝ) ^ (12 * ϑ⁻¹ + 11) ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK0
  have hKCF : (CF * 2 ^ (8 * ϑ⁻¹ + 7)) ^ 2 ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK0
  have hKpos : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  -- `log N ≥ 1`
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := Real.exp_one_lt_d9
    have h13r : (13 : ℝ) ≤ N := by exact_mod_cast h13
    linarith
  have hlogK : Real.log N ≤ K := by
    have : Real.log N ≤ Real.log N ^ 3 := le_self_pow₀ hL1 (by norm_num)
    linarith
  have hp12 : (levelP2 K : ℝ) ≤ levelP1 K := by
    have h0 : (0 : ℝ) ≤ levelP2 K := Nat.cast_nonneg _
    nlinarith
  -- the properties of `p`
  obtain ⟨hpe, hKp, hpp1⟩ : Even p ∧ K ≤ (p : ℝ) ∧ (p : ℝ) ≤ levelP1 K := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨_, two_mul _⟩, hKp2.trans hp12, le_rfl⟩
    · exact ⟨⟨_, two_mul _⟩, hKp2, hp12⟩
  have hp0r : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hp2r : (2 : ℝ) ≤ p := by linarith
  have hp2 : 2 ≤ p := by exact_mod_cast hp2r
  have hpne : p ≠ 0 := by omega
  have hp32 : (p : ℝ) ≤ 2 * K ^ (3 / 2 : ℝ) := hpp1.trans hp1le
  -- the hypotheses of Theorem 6.1
  have hlog : Real.log N ≤ p := hlogK.trans hKp
  have hp0 : p₀ ≤ p := hKp₀.trans hKp
  have hpN : (p : ℝ) ≤ (N : ℝ) ^ (1 / (40 * ϑ⁻¹ + 40)) := faLat_p_le ha hN1r hK2' hK2 hp32
  have hη10 : z.im ≤ 10 := by
    rcases hz.1 with h | h
    · exact h.2.2
    · exact h.2.2.2
  have hC1 : ledgerC1 ϑ⁻¹ - 1 = 18 * ϑ⁻¹ + 19 := by unfold ledgerC1; ring
  have hη1 : 1 / (N : ℝ) ≤ z.im ∧ (p : ℝ) ^ (12 * ϑ⁻¹ + 11) ≤ N * z.im ∧ ‖z‖ ≤ N := by
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
    have hss := Real.mul_self_sqrt hNpos.le
    have hs2 : 2 ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) hNpos.le).2 (by linarith)
    rcases hz.1 with h | h
    · -- near
      obtain ⟨hre, himl, him⟩ := h
      rw [hC1] at himl
      have hKpow : 1 ≤ K ^ (18 * ϑ⁻¹ + 19) := Real.one_le_rpow hKone (by linarith)
      have h1N : 1 / (N : ℝ) ≤ z.im :=
        le_trans (div_le_div_of_nonneg_right hKpow hNpos.le) himl
      have him0 : 0 ≤ z.im := le_trans (by positivity) h1N
      refine ⟨h1N, ?_, faLat_norm_near (by linarith) hre him him0⟩
      have := (div_le_iff₀ hNpos).1 himl
      calc (p : ℝ) ^ (12 * ϑ⁻¹ + 11) ≤ K ^ (18 * ϑ⁻¹ + 19) :=
            faLat_near_pow ha hKone hp0r hp32 hK2pow
        _ ≤ N * z.im := by linarith
    · -- far
      obtain ⟨-, hre, himl, him⟩ := h
      have h1N : 1 / (N : ℝ) ≤ z.im := by
        refine le_trans ?_ himl
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have him0 : 0 ≤ z.im := le_trans (by positivity) h1N
      refine ⟨h1N, faLat_far_pow ha hN32r hp0r hpN himl, ?_⟩
      have hE : levelEmax ϑ⁻¹ C₀ K N ≤ (N : ℝ) ^ (1 / 32 : ℝ) :=
        hEmax.trans ((Real.rpow_le_rpow_of_exponent_le hKone (by linarith)).trans hS4.1)
      exact faLat_norm_far hN32r hE hre him him0
  obtain ⟨hη1, hNη, hzN⟩ := hη1
  have ht : ∀ k : Fin N, ‖(fun _ : Fin N => (N : ℂ)⁻¹) k‖ ≤ 1 / N := fun k => by
    simp [norm_inv]
  have hFA := h1 N hN1 M hM z hzN hη1 hη10 p hpe hlog hpN hp0 hNη _ ht
  -- the tail: `Ξ(z) = Ξ_{p₁}(z) ⊆ Ξ_p(z)` and Theorem 5.5 (c)
  have hsub : (aprioriEvent N (levelP1 K) z : Set (Pair N → 𝕜)) ⊆ aprioriEvent N p z := by
    intro x hx
    refine ⟨hx.1, hx.2.trans ?_⟩
    have hp0' : (0 : ℝ) < p := by linarith
    gcongr
  have htail : M.prodLaw (aprioriEvent N p z)ᶜ ≤ ENNReal.ofReal (Cw * N ^ 9 * Real.exp (-K ^ 2)) :=
    (measure_mono (Set.compl_subset_compl.2 hsub)).trans (h2 N hN2 M hM K hK1 hK2 z hz).2
  -- the bounds of the constant and of the tail term
  have hK40 : 40 * (p : ℝ) * Real.log N ≤ K ^ 2 := by
    have hL0 : 0 ≤ Real.log N := by linarith
    calc 40 * (p : ℝ) * Real.log N ≤ 40 * (levelP1 K : ℝ) * Real.log N := by gcongr
      _ ≤ K ^ 2 := hlev1
  have hq0 : (0 : ℝ) ≤ 1 / (2 * (p : ℝ)) := by positivity
  have hX0 : 0 ≤ Cw * (N : ℝ) ^ 9 * Real.exp (-K ^ 2) := by positivity
  have hνb : M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / (2 * (p : ℝ))) ≤
      ENNReal.ofReal ((Cw * (N : ℝ) ^ 9 * Real.exp (-K ^ 2)) ^ (1 / (2 * (p : ℝ)))) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hX0 hq0]
    exact ENNReal.rpow_le_rpow htail hq0
  have htl := faLat_tail (by omega : 2 ≤ N) hp2 hCw.le hCwN hK40
  have hrowA := faLat_rowA hCF ha hKone hp0r hp32 hKCF
  -- the integrability of `X` and the passage to `L^p` norms
  have hz0 : 0 < z.im := lt_of_lt_of_le (by positivity) hη1
  have hFmeas : AEStronglyMeasurable
      (fun x => (N : ℂ)⁻¹ * ∑ k, selfX (toMatrix x) M.varMatrix z k) M.prodLaw := by
    refine (continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)).aestronglyMeasurable
    exact ((polyGrowth_schurM M 0 hz0 ∅).2.2.2.2.1 k).1
  rw [faLat_eLpNorm_nat hFmeas hpne]
  by_cases hΦ : AEStronglyMeasurable (fun x => phiStarSq (p : ℝ) x z) M.prodLaw
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hΦ,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hKpos _)).ne', top_add]
    exact le_top
  rw [faLat_eLpNorm_nat hΦ hpne]
  have hb0 : 0 ≤ CF * (p : ℝ) ^ (8 * ϑ⁻¹ + 7) := by positivity
  have hFA2 : ∫⁻ x, ‖∑ k, (N : ℂ)⁻¹ * selfX (toMatrix x) M.varMatrix z k‖ₑ ^ p ∂M.prodLaw ≤
      ENNReal.ofReal ((CF * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) ^ p) *
          ∫⁻ x, ENNReal.ofReal (phiStarSq (p : ℝ) x z) ^ p ∂M.prodLaw +
        ENNReal.ofReal (((N : ℝ) ^ 2) ^ p) * M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / 2 : ℝ) := by
    rw [← pow_mul]
    exact hFA
  have hFA' := faLat_root hb0 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2) hpne hFA2
  have hJ : (∫⁻ x, ENNReal.ofReal (phiStarSq (p : ℝ) x z) ^ p ∂M.prodLaw) ^ (1 / (p : ℝ)) ≤
      (∫⁻ x, ‖phiStarSq (p : ℝ) x z‖ₑ ^ p ∂M.prodLaw) ^ (1 / (p : ℝ)) := by
    refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
    gcongr
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  simp only [Finset.mul_sum]
  calc _ ≤ ENNReal.ofReal (CF * (p : ℝ) ^ (8 * ϑ⁻¹ + 7)) *
          (∫⁻ x, ENNReal.ofReal (phiStarSq (p : ℝ) x z) ^ p ∂M.prodLaw) ^ (1 / (p : ℝ)) +
        ENNReal.ofReal ((N : ℝ) ^ 2) *
          M.prodLaw (aprioriEvent N p z)ᶜ ^ (1 / (2 * (p : ℝ))) := hFA'
    _ ≤ ENNReal.ofReal (K ^ (12 * ϑ⁻¹ + 11)) *
          (∫⁻ x, ‖phiStarSq (p : ℝ) x z‖ₑ ^ p ∂M.prodLaw) ^ (1 / (p : ℝ)) +
        ENNReal.ofReal ((N : ℝ) ^ 2) *
          ENNReal.ofReal ((Cw * (N : ℝ) ^ 9 * Real.exp (-K ^ 2)) ^ (1 / (2 * (p : ℝ)))) := by
        gcongr
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        gcongr

end Rigidity
