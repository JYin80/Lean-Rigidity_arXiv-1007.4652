module

public import Rigidity.Edge.Continuity
public import Rigidity.Edge.EdgeEvent
public import Rigidity.Edge.Hybrid
public import Rigidity.Edge.Inputs
public import Rigidity.Edge.LogBounds
public import Rigidity.Edge.Params
public import Rigidity.Edge.SmoothCount
public import Rigidity.Edge.SpecF
public import Rigidity.Ensemble.Basic
public import Rigidity.Resolvent.Basic
public import Rigidity.Semicircle.Density
public import Rigidity.Semicircle.Locations
public import Rigidity.Semicircle.Stieltjes
public import Rigidity.Spectrum.Eigenvalues

@[expose] public section

/-!
# The law of `λ_N` against the smoothed counting functional

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

Lemma 11.12 is the edge bound `2 - γ_j ≥ (3π (N - j) / (2N))^{2/3}` on the classical locations; it
follows from `n_sc(2) = 1` and `ϱ_sc(2 - u) ≤ √u / π` (Lemma 3.4 (a), (b)).  The smoothed counting
functional of a complex matrix `toMatrixC x` is the sum `∑_k f(λ_k)` over the ordered eigenvalues
`eig x k` (Lemma 11.8).  Proposition 11.13 is the sandwich: for `E` in the window
`[2 - 2W, 2 + W]` the probability of `{λ_N < E}` lies between the expectations of `q (X⁻_E)` and
`q (X⁺_E)`, up to `N^{-20}`, where `X^±_E = X_{E ± ℓ, E_L, η}` and `q` is a cut-off equal to `1`
on `(-∞, 1/9]` and to `0` on `[2/9, ∞)`.  The proof uses only the rigidity event of (BB2):
on its complement `λ_N` is within `W` of `2`, the eigenvalue `λ_N` itself makes `X⁻_E ≥ 8/9` if
`λ_N ≥ E`, and if `λ_N < E` the `K₁` largest eigenvalues each contribute at most `η / (π ℓ)`
while the others are placed by their classical locations and contribute at most
`4 N^{-2ε}(log N)^{L₀}` in total, using `∑_{m ≥ 1} m^{-4/3} ≤ 4`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- Lemma 11.12, with `j = k + 1`. -/
theorem gamma_edge_le {N : ℕ} (k : Fin N) :
    (3 * π * ((N : ℝ) - 1 - k) / (2 * N)) ^ (2 / 3 : ℝ) ≤ 2 - gamma N k := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos k
  have hk : (k.val : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
  have hr0 : 0 ≤ 2 - gamma N k := by linarith [(gamma_mem k).2]
  have h1 := nsc_gamma k
  have h2 := nsc_props.2.2.2.2.2.2.1 (gamma N k)
  have h3 := (rhoSc_nsc_edge hr0).2.1
  have e : -2 + (2 - gamma N k) = -gamma N k := by ring
  rw [e, h2] at h3
  have h4 : nsc (gamma N k) = ((k.val : ℝ) + 1) / N := by
    field_simp
    linarith
  rw [h4] at h3
  have hpi : 0 < π := Real.pi_pos
  have ht : 3 * π * ((N : ℝ) - 1 - k) / (2 * N) ≤ (2 - gamma N k) ^ (3 / 2 : ℝ) := by
    have h5 : 1 - ((k.val : ℝ) + 1) / N = ((N : ℝ) - 1 - k) / N := by
      field_simp
      ring
    rw [h5] at h3
    have h6 : 3 * π * ((N : ℝ) - 1 - k) / (2 * N) = (3 * π / 2) * (((N : ℝ) - 1 - k) / N) := by
      field_simp
    rw [h6]
    calc 3 * π / 2 * (((N : ℝ) - 1 - k) / N)
        ≤ 3 * π / 2 * (2 / (3 * π) * (2 - gamma N k) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (2 - gamma N k) ^ (3 / 2 : ℝ) := by field_simp
  have ht0 : 0 ≤ 3 * π * ((N : ℝ) - 1 - k) / (2 * N) := by
    have : 0 ≤ (N : ℝ) - 1 - k := by linarith
    positivity
  calc (3 * π * ((N : ℝ) - 1 - k) / (2 * N)) ^ (2 / 3 : ℝ)
      ≤ ((2 - gamma N k) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow ht0 ht (by norm_num)
    _ = 2 - gamma N k := by
        rw [← Real.rpow_mul hr0]
        norm_num

/-- The bijection of `Fin N` sending `k` to the index, in `hA.eigenvalues`, of the `(k+1)`-st
smallest eigenvalue. -/
private noncomputable def sandwichPerm (N : ℕ) : Equiv.Perm (Fin N) :=
  Fin.revPerm.trans ((finCongr (Fintype.card_fin N).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)))

private theorem sandwich_eigenvalues_perm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (k : Fin N) : hA.eigenvalues (sandwichPerm N k) = eigAsc hA k := by
  simp [sandwichPerm, Matrix.IsHermitian.eigenvalues, eigAsc]

theorem smoothCount_toMatrixC_eq_sum {N : ℕ} (x : Pair N → 𝕜) {E₁ E₂ η : ℝ} (hη : 0 < η) :
    smoothCount E₁ E₂ η (toMatrixC x) = ∑ k, specF E₁ E₂ η (eig x k) := by
  have hB := toMatrixC_isHermitian x
  rw [smoothCount_eq_sum hB hη, ← Equiv.sum_comp (sandwichPerm N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sandwich_eigenvalues_perm hB k]
  have := congrFun (eigAsc_map_toC (toMatrix_isHermitian x)) k
  unfold eig
  rw [← this]
  rfl


/-! ### The sum `∑ m^{-4/3}` and the splitting of the eigenvalue sum -/

/-- `∑_{m=1}^{n} m^{-4/3} + 3 n^{-1/3} ≤ 4` for `n ≥ 1`: for `n = 1` the left side is `4`, and the
step uses `(n+1)^{-4/3} ≤ 3 (n^{-1/3} - (n+1)^{-1/3})`. -/
private lemma sandwich_sum_aux (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Finset.range (n + 1), (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) +
      3 * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 4 := by
  induction n, hn using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]; norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ _ (n + 1)]
    simp only [show 1 ≤ n + 1 from by omega, ite_true]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    set t : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ)) with ht
    set s : ℝ := ((n + 1 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) with hs
    have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
    have hs0 : 0 < s := Real.rpow_pos_of_pos hn1 _
    have hcube : ∀ y : ℝ, 0 < y → (y ^ (-(1 / 3 : ℝ))) ^ 3 = y⁻¹ := by
      intro y hy
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
      norm_num
      exact Real.rpow_neg_one y
    have ht3 : t ^ 3 = (n : ℝ)⁻¹ := hcube _ hn0
    have hs3 : s ^ 3 = ((n + 1 : ℕ) : ℝ)⁻¹ := hcube _ hn1
    have h4 : ((n + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) = s ^ 4 := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hn1.le]
      norm_num
    have hst : s ≤ t := by
      by_contra h
      have h' : t < s := not_le.1 h
      have : t ^ 3 < s ^ 3 := pow_lt_pow_left₀ h' ht0.le (by norm_num)
      rw [ht3, hs3] at this
      push_cast at this
      have h5 : ((n : ℝ) + 1)⁻¹ < (n : ℝ)⁻¹ := inv_strictAnti₀ hn0 (by linarith)
      linarith
    have h1 : s ^ 3 * t ^ 3 = t ^ 3 - s ^ 3 := by
      rw [ht3, hs3]
      push_cast
      field_simp
      ring
    have h2 : (t - s) * (t ^ 2 + t * s + s ^ 2) = t ^ 3 - s ^ 3 := by ring
    have h3 : s ^ 3 * t ^ 3 ≤ (t - s) * (3 * t ^ 2) := by
      rw [h1, ← h2]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith
    have h6 : s ^ 3 * t ≤ 3 * (t - s) := by
      have : t ^ 2 * (s ^ 3 * t) ≤ t ^ 2 * (3 * (t - s)) := by nlinarith [h3]
      exact le_of_mul_le_mul_left this (by positivity)
    have h7 : s ^ 4 ≤ s ^ 3 * t := by nlinarith [pow_pos hs0 3]
    rw [h4]
    linarith

private lemma sandwich_sum_le (n : ℕ) :
    ∑ m ∈ Finset.range n, (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) ≤ 4 := by
  rcases n with _ | n
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := sandwich_sum_aux n hn
    have h0 : 0 ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith

/-- The sum over `k : Fin N`, grouped by `m = N - 1 - k`: the `K` values `m < K` contribute at most
`c` each, and the others at most `C m^{-4/3}`. -/
private lemma sandwich_split_sum {N K : ℕ} (hK : 1 ≤ K) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (f : Fin N → ℝ)
    (hf : ∀ k : Fin N, f k ≤
      if N - 1 - k.val < K then c else C * ((N - 1 - k.val : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) :
    ∑ k, f k ≤ c * K + 4 * C := by
  set G : ℕ → ℝ := fun m => if m < K then c else C * (m : ℝ) ^ (-(4 / 3 : ℝ)) with hG
  have h1 : ∑ k, f k ≤ ∑ k : Fin N, G (N - 1 - k.val) := Finset.sum_le_sum fun k _ => hf k
  have h2 : ∑ k : Fin N, G (N - 1 - k.val) = ∑ m ∈ Finset.range N, G m := by
    rw [Fin.sum_univ_eq_sum_range (fun j => G (N - 1 - j)) N, Finset.sum_range_reflect G N]
  have h3 : ∀ m : ℕ, G m ≤ (if m < K then c else 0) +
      C * (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) := by
    intro m
    simp only [hG]
    by_cases hm : m < K
    · simp only [hm, ite_true]
      have : 0 ≤ C * (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) := by
        refine mul_nonneg hC ?_
        split_ifs
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        · exact le_rfl
      linarith
    · have hm1 : 1 ≤ m := by omega
      simp [hm, hm1]
  have h4 : ∑ m ∈ Finset.range N, (if m < K then c else 0) ≤ c * K := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hc
    have : ((Finset.range N).filter (· < K)).card ≤ K := by
      calc ((Finset.range N).filter (· < K)).card ≤ (Finset.range K).card := by
            refine Finset.card_le_card fun m hm => ?_
            simp only [Finset.mem_filter] at hm
            exact Finset.mem_range.2 hm.2
        _ = K := Finset.card_range K
    exact_mod_cast this
  have h5 : ∑ m ∈ Finset.range N, C * (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) ≤
      4 * C := by
    rw [← Finset.mul_sum]
    nlinarith [sandwich_sum_le N]
  calc ∑ k, f k ≤ ∑ k : Fin N, G (N - 1 - k.val) := h1
    _ = ∑ m ∈ Finset.range N, G m := h2
    _ ≤ ∑ m ∈ Finset.range N, ((if m < K then c else 0) +
          C * (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0)) :=
        Finset.sum_le_sum fun m _ => h3 m
    _ = ∑ m ∈ Finset.range N, (if m < K then c else 0) +
          ∑ m ∈ Finset.range N, C * (if 1 ≤ m then ((m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) else 0) :=
        Finset.sum_add_distrib
    _ ≤ c * K + 4 * C := add_le_add h4 h5

/-! ### Elementary facts on the edge parameters -/

private lemma sandwich_Npos {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN.exp_le

private lemma sandwich_logpos {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    0 < Real.log N := by
  have h : (1 : ℝ) + 27 ≤ Real.exp 27 := by linarith [Real.add_one_le_exp (27 : ℝ)]
  exact Real.log_pos (by linarith [hN.exp_le])

private lemma sandwich_W_pos {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    0 < edgeW A₀ N :=
  mul_pos (Real.rpow_pos_of_pos (sandwich_logpos hN) _) (Real.rpow_pos_of_pos (sandwich_Npos hN) _)

private lemma sandwich_ell_pos {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    0 < edgeEll εg N :=
  mul_pos (by norm_num) (Real.rpow_pos_of_pos (sandwich_Npos hN) _)

private lemma sandwich_eta_pos {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    0 < edgeEta εg N := Real.rpow_pos_of_pos (sandwich_Npos hN) _

/-- `η = 3 ℓ N^{-ε}` with `ε = ε_g / 2` (11.2). -/
private lemma sandwich_eta_eq {N : ℕ} (hN : (0 : ℝ) < N) (εg : ℝ) :
    edgeEta εg N = 3 * edgeEll εg N * (N : ℝ) ^ (-(εg / 2)) := by
  unfold edgeEta edgeEll
  rw [show 3 * (1 / 3 * (N : ℝ) ^ (-(2 / 3 : ℝ) - εg / 2)) * (N : ℝ) ^ (-(εg / 2)) =
    (N : ℝ) ^ (-(2 / 3 : ℝ) - εg / 2) * (N : ℝ) ^ (-(εg / 2)) by ring, ← Real.rpow_add hN]
  congr 1
  ring

/-- `η W N^{4/3} = N^{-ε_g} (log N)^{L₀}`. -/
private lemma sandwich_etaW {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) :
    edgeEta εg N * edgeW A₀ N * (N : ℝ) ^ (4 / 3 : ℝ) =
      (N : ℝ) ^ (-εg) * Real.log N ^ edgeL0 A₀ N := by
  have hNpos := sandwich_Npos hN
  unfold edgeEta edgeW
  have : (N : ℝ) ^ (-(2 / 3 : ℝ) - εg) * (Real.log N ^ edgeL0 A₀ N * (N : ℝ) ^ (-(2 / 3 : ℝ))) *
      (N : ℝ) ^ (4 / 3 : ℝ) = ((N : ℝ) ^ (-(2 / 3 : ℝ) - εg) * (N : ℝ) ^ (-(2 / 3 : ℝ)) *
      (N : ℝ) ^ (4 / 3 : ℝ)) * Real.log N ^ edgeL0 A₀ N := by ring
  rw [this, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  congr 2
  ring

/-- `y ≤ x^{2/3}` once `y³ ≤ x²`. -/
private lemma sandwich_le_rpow_two_thirds {x y : ℝ} (hx : 0 ≤ x) (h : y ^ 3 ≤ x ^ 2) :
    y ≤ x ^ (2 / 3 : ℝ) := by
  by_contra hc
  have hc' : x ^ (2 / 3 : ℝ) < y := not_le.1 hc
  have h0 : 0 ≤ x ^ (2 / 3 : ℝ) := Real.rpow_nonneg hx _
  have h1 : (x ^ (2 / 3 : ℝ)) ^ 3 < y ^ 3 := pow_lt_pow_left₀ hc' h0 (by norm_num)
  have h2 : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast]
    norm_num
  linarith

/-- `(3π/2)^{2/3} ≥ 5/2`. -/
private lemma sandwich_c_ge : (5 / 2 : ℝ) ≤ (3 * π / 2) ^ (2 / 3 : ℝ) := by
  refine sandwich_le_rpow_two_thirds (by positivity) ?_
  nlinarith [Real.pi_gt_three]

/-- `4^{2/3} ≥ 5/2`. -/
private lemma sandwich_four_ge : (5 / 2 : ℝ) ≤ (4 : ℝ) ^ (2 / 3 : ℝ) :=
  sandwich_le_rpow_two_thirds (by norm_num) (by norm_num)

/-- `((3π m)/(2N))^{2/3} = (3π/2)^{2/3} · (m^{2/3} N^{-2/3})`. -/
private lemma sandwich_a_decomp {N m : ℕ} (hN : 0 < N) :
    (3 * π * (m : ℝ) / (2 * N)) ^ (2 / 3 : ℝ) =
      (3 * π / 2) ^ (2 / 3 : ℝ) * ((m : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : 3 * π * (m : ℝ) / (2 * N) = (3 * π / 2) * ((m : ℝ) * (N : ℝ)⁻¹) := by
    field_simp
  rw [e, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
    (by positivity), Real.inv_rpow hN'.le, ← Real.rpow_neg hN'.le]

/-- Step 2 of Proposition 11.13: `a_k > 6W` for `k - 1 ≥ K₁ > 4 (log N)^{3L₀/2}`. -/
private lemma sandwich_a_gt {ϑ C₀ A₀ εg : ℝ} {N m : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N)
    (hm : 4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) < m) :
    6 * edgeW A₀ N < (3 * π * (m : ℝ) / (2 * N)) ^ (2 / 3 : ℝ) := by
  have hNpos := sandwich_Npos hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hT := sandwich_logpos hN
  have hW := sandwich_W_pos hN
  rw [sandwich_a_decomp hN0]
  have h1 : (4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N)) ^ (2 / 3 : ℝ) < (m : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow (by positivity) hm (by norm_num)
  have h2 : (4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N)) ^ (2 / 3 : ℝ) =
      (4 : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ edgeL0 A₀ N := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT.le _), ← Real.rpow_mul hT.le]
    congr 2
    ring
  rw [h2] at h1
  have hQ : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have h3 : (4 : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ edgeL0 A₀ N * (N : ℝ) ^ (-(2 / 3 : ℝ)) <
      (m : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ)) := mul_lt_mul_of_pos_right h1 hQ
  have hc := sandwich_c_ge
  have h4 := sandwich_four_ge
  have hWe : edgeW A₀ N = Real.log N ^ edgeL0 A₀ N * (N : ℝ) ^ (-(2 / 3 : ℝ)) := rfl
  have h5 : (4 : ℝ) ^ (2 / 3 : ℝ) * Real.log N ^ edgeL0 A₀ N * (N : ℝ) ^ (-(2 / 3 : ℝ)) =
      (4 : ℝ) ^ (2 / 3 : ℝ) * edgeW A₀ N := by rw [hWe]; ring
  rw [h5] at h3
  have h6 : (5 / 2 : ℝ) * ((5 / 2 : ℝ) * edgeW A₀ N) ≤
      (3 * π / 2) ^ (2 / 3 : ℝ) * ((4 : ℝ) ^ (2 / 3 : ℝ) * edgeW A₀ N) := by
    have : (5 / 2 : ℝ) * edgeW A₀ N ≤ (4 : ℝ) ^ (2 / 3 : ℝ) * edgeW A₀ N :=
      mul_le_mul_of_nonneg_right h4 hW.le
    exact mul_le_mul hc this (by positivity) (by positivity)
  have h7 : (3 * π / 2) ^ (2 / 3 : ℝ) * ((4 : ℝ) ^ (2 / 3 : ℝ) * edgeW A₀ N) <
      (3 * π / 2) ^ (2 / 3 : ℝ) * ((m : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (-(2 / 3 : ℝ))) :=
    mul_lt_mul_of_pos_left h3 (by positivity)
  nlinarith

/-- The bound `(η/π) · 16 W / a² ≤ η W N^{4/3} m^{-4/3}` with `a = (3π m / (2N))^{2/3}`. -/
private lemma sandwich_rest_term {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {η W : ℝ} (hη : 0 ≤ η)
    (hW : 0 ≤ W) :
    η / π * (16 * W / ((3 * π * (m : ℝ) / (2 * N)) ^ (2 / 3 : ℝ)) ^ 2) ≤
      η * W * (N : ℝ) ^ (4 / 3 : ℝ) * (m : ℝ) ^ (-(4 / 3 : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℝ := (3 * π / 2) ^ (2 / 3 : ℝ) with hc
  have hc2 : (5 / 2 : ℝ) ≤ c := sandwich_c_ge
  have hP : 0 < (m : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hm' _
  have hQ : 0 < (N : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hN' _
  have e1 : ((m : ℝ) ^ (2 / 3 : ℝ)) ^ 2 = (m : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le]
    norm_num
  have e2 : ((N : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = ((N : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le, ← Real.rpow_neg hN'.le]
    norm_num
  have e3 : (m : ℝ) ^ (-(4 / 3 : ℝ)) = ((m : ℝ) ^ (4 / 3 : ℝ))⁻¹ := Real.rpow_neg hm'.le _
  rw [sandwich_a_decomp hN, mul_pow, mul_pow, e1, e2, ← hc, e3]
  have hπ3 := Real.pi_gt_three
  have hc2' : 0 < c ^ 2 := by positivity
  have : η / π * (16 * W / (c ^ 2 * ((m : ℝ) ^ (4 / 3 : ℝ) * ((N : ℝ) ^ (4 / 3 : ℝ))⁻¹))) =
      (η * W * (N : ℝ) ^ (4 / 3 : ℝ) * ((m : ℝ) ^ (4 / 3 : ℝ))⁻¹) * (16 / (π * c ^ 2)) := by
    field_simp
  rw [this]
  have h16 : 16 / (π * c ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have h0 : 0 ≤ η * W * (N : ℝ) ^ (4 / 3 : ℝ) * ((m : ℝ) ^ (4 / 3 : ℝ))⁻¹ := by positivity
  calc (η * W * (N : ℝ) ^ (4 / 3 : ℝ) * ((m : ℝ) ^ (4 / 3 : ℝ))⁻¹) * (16 / (π * c ^ 2))
      ≤ (η * W * (N : ℝ) ^ (4 / 3 : ℝ) * ((m : ℝ) ^ (4 / 3 : ℝ))⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left h16 h0
    _ = _ := mul_one _

/-! ### The rigidity event and the largest eigenvalue -/

private lemma sandwich_eig_le_lamMax {N : ℕ} (x : Pair N → 𝕜) (k : Fin N) :
    eig x k ≤ lamMax x := by
  have hN0 : 0 < N := Fin.pos k
  unfold lamMax
  simp only [hN0, dite_true]
  exact eigAsc_monotone (toMatrix_isHermitian x)
    (by rw [Fin.le_iff_val_le_val]; have := k.isLt; simp; omega)

private lemma sandwich_lamMax_eq {N : ℕ} (hN0 : 0 < N) (x : Pair N → 𝕜) :
    lamMax x = eig x ⟨N - 1, by omega⟩ := by
  unfold lamMax
  simp only [hN0, dite_true]

/-- Off the event of (BB2) at `L = L₀`, every `λ_k` is within `W` of `γ_k`: the weight
`min(j, N - j + 1)` is at least `1`. -/
private lemma sandwich_good {A₀ : ℝ} {N : ℕ} (hT : 0 ≤ Real.log N) {x : Pair N → 𝕜}
    (hx : x ∉ rigidityEvent N (edgeL0 A₀ N)) (k : Fin N) :
    |eig x k - gamma N k| < edgeW A₀ N := by
  simp only [rigidityEvent, Set.mem_ofPred_eq, not_exists, not_le] at hx
  refine lt_of_lt_of_le (hx k) ?_
  have hw : (1 : ℝ) ≤ (rigWeight N k : ℝ) := by
    have : 1 ≤ rigWeight N k := by
      unfold rigWeight
      have := k.isLt
      omega
    exact_mod_cast this
  have h1 : (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw (by norm_num)
  unfold edgeW
  have h2 : Real.log N ^ edgeL0 A₀ N * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) ≤
      Real.log N ^ edgeL0 A₀ N * 1 :=
    mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hT _)
  have h3 : (0 : ℝ) ≤ (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact Fin.elim0 k
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc Real.log N ^ edgeL0 A₀ N * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ))
      ≤ Real.log N ^ edgeL0 A₀ N * 1 * (N : ℝ) ^ (-(2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 h3
    _ = Real.log N ^ edgeL0 A₀ N * (N : ℝ) ^ (-(2 / 3 : ℝ)) := by ring

/-! ### Steps 1 and 2 of Proposition 11.13 -/

/-- Step 1: if `λ_N ≥ E` and `λ_N` is within `W` of `2`, then `X⁻_E ≥ 8/9`. -/
private lemma sandwich_step1 {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) {E : ℝ}
    (x : Pair N → 𝕜) (hR : ∀ k, |eig x k - gamma N k| < edgeW A₀ N) (hE : E ≤ lamMax x) :
    8 / 9 ≤ smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x) := by
  have hNpos := sandwich_Npos hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hη := sandwich_eta_pos hN
  have hℓ := sandwich_ell_pos hN
  have hW := sandwich_W_pos hN
  have hℓW := hN.ell_le
  rw [smoothCount_toMatrixC_eq_sum x hη]
  set k₀ : Fin N := ⟨N - 1, by omega⟩ with hk₀
  have hlam : lamMax x = eig x k₀ := sandwich_lamMax_eq hN0 x
  have hg : gamma N k₀ = 2 := gamma_last hN0
  have hR1 := abs_lt.1 (hR k₀)
  rw [hg] at hR1
  rw [hlam] at hE
  have hE₂ : eig x k₀ < edgeEL A₀ N := by unfold edgeEL; linarith [hR1.2]
  have hE₁ : E - edgeEll εg N < eig x k₀ := by linarith
  have hle : E - edgeEll εg N ≤ edgeEL A₀ N := by linarith
  have hf := one_sub_le_specF hη hE₁ hE₂
  have hsum : specF (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (eig x k₀) ≤
      ∑ k, specF (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (eig x k) :=
    Finset.single_le_sum (fun k _ => (specF_mem hη hle (eig x k)).1) (Finset.mem_univ k₀)
  have h1 : 1 / (edgeEL A₀ N - eig x k₀) ≤ 1 / edgeEll εg N :=
    one_div_le_one_div_of_le hℓ (by unfold edgeEL; linarith [hR1.2])
  have h2 : 1 / (eig x k₀ - (E - edgeEll εg N)) ≤ 1 / edgeEll εg N :=
    one_div_le_one_div_of_le hℓ (by linarith)
  have h3 : edgeEta εg N / π * (1 / (edgeEL A₀ N - eig x k₀) + 1 / (eig x k₀ - (E - edgeEll εg N)))
      ≤ edgeEta εg N / π * (2 * (1 / edgeEll εg N)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : edgeEta εg N / π * (2 * (1 / edgeEll εg N)) = 6 / π * (N : ℝ) ^ (-(εg / 2)) := by
    rw [sandwich_eta_eq hNpos εg]
    field_simp
    norm_num
  have h5 := hN.sandwich_le'
  linarith

/-- Step 2: if every `λ_k` is within `W` of `γ_k`, `E ∈ [2 - 2W, 2 + W]` and `λ_N < E`, then
`X⁺_E ≤ 1/9`. -/
private lemma sandwich_step2 {ϑ C₀ A₀ εg : ℝ} {N : ℕ} (hN : EdgeLarge ϑ C₀ A₀ εg N) {E : ℝ}
    (hE : 2 - 2 * edgeW A₀ N ≤ E) (hE' : E ≤ 2 + edgeW A₀ N) (x : Pair N → 𝕜)
    (hR : ∀ k, |eig x k - gamma N k| < edgeW A₀ N) (hlt : lamMax x < E) :
    smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x) ≤ 1 / 9 := by
  have hNpos := sandwich_Npos hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hT := sandwich_logpos hN
  have hη := sandwich_eta_pos hN
  have hℓ := sandwich_ell_pos hN
  have hW := sandwich_W_pos hN
  have hℓW := hN.ell_le
  rw [smoothCount_toMatrixC_eq_sum x hη]
  have hE12 : E + edgeEll εg N ≤ edgeEL A₀ N := by unfold edgeEL; linarith
  have hE2E1 : edgeEL A₀ N - (E + edgeEll εg N) ≤ 4 * edgeW A₀ N := by unfold edgeEL; linarith
  have hy0 : 0 ≤ 4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) := by
    have := Real.rpow_nonneg hT.le (3 / 2 * edgeL0 A₀ N)
    linarith
  set K : ℕ := ⌊4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N)⌋₊ + 1 with hKdef
  have hK1 : 1 ≤ K := Nat.le_add_left _ _
  have hKlt : 4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) < K := by
    rw [hKdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hKle : (K : ℝ) ≤ 4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) + 1 := by
    rw [hKdef]
    push_cast
    linarith [Nat.floor_le hy0]
  have hq0 : 0 < (N : ℝ) ^ (-(εg / 2)) := Real.rpow_pos_of_pos hNpos _
  have hc : 0 ≤ 3 / π * (N : ℝ) ^ (-(εg / 2)) := by positivity
  have hC : 0 ≤ edgeEta εg N * edgeW A₀ N * (N : ℝ) ^ (4 / 3 : ℝ) := by positivity
  refine le_trans (sandwich_split_sum hK1 hc hC
    (fun k => specF (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (eig x k)) ?_) ?_
  · intro k
    have hkE : eig x k < E := lt_of_le_of_lt (sandwich_eig_le_lamMax x k) hlt
    have hd : edgeEll εg N < E + edgeEll εg N - eig x k := by linarith
    have hkN : k.val + 1 ≤ N := k.isLt
    split_ifs with hm
    · -- the `K` largest eigenvalues
      have h1 := specF_le_inv hη hE12 (show eig x k < E + edgeEll εg N by linarith)
      have h2 : 1 / (E + edgeEll εg N - eig x k) ≤ 1 / edgeEll εg N :=
        one_div_le_one_div_of_le hℓ hd.le
      have h3 : edgeEta εg N / π * (1 / (E + edgeEll εg N - eig x k)) ≤
          edgeEta εg N / π * (1 / edgeEll εg N) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : edgeEta εg N / π * (1 / edgeEll εg N) = 3 / π * (N : ℝ) ^ (-(εg / 2)) := by
        rw [sandwich_eta_eq hNpos εg]
        field_simp
      linarith
    · -- the other eigenvalues
      have hmK : K ≤ N - 1 - k.val := not_lt.1 hm
      have hm0 : 0 < N - 1 - k.val := by omega
      have hmreal : 4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) < ((N - 1 - k.val : ℕ) : ℝ) :=
        lt_of_lt_of_le hKlt (by exact_mod_cast hmK)
      have ha6 := sandwich_a_gt hN hmreal
      have hcast : ((N - 1 - k.val : ℕ) : ℝ) = (N : ℝ) - 1 - k.val := by
        have h : (N - 1 - k.val : ℕ) + 1 + k.val = N := by omega
        have h' := congrArg (Nat.cast (R := ℝ)) h
        push_cast at h'
        linarith
      have hγ := gamma_edge_le k
      rw [← hcast] at hγ
      set a : ℝ := (3 * π * ((N - 1 - k.val : ℕ) : ℝ) / (2 * N)) ^ (2 / 3 : ℝ) with ha
      have hR2 := abs_lt.1 (hR k)
      have hd2 : a / 2 < E + edgeEll εg N - eig x k := by linarith [hR2.2]
      have ha0 : 0 < a := by linarith
      have h1 := specF_le_sq hη hE12 (show eig x k < E + edgeEll εg N by linarith)
      have hdsq : a ^ 2 / 4 ≤ (E + edgeEll εg N - eig x k) ^ 2 := by nlinarith
      have h2 : (edgeEL A₀ N - (E + edgeEll εg N)) / (E + edgeEll εg N - eig x k) ^ 2 ≤
          16 * edgeW A₀ N / a ^ 2 := by
        have h2a : (edgeEL A₀ N - (E + edgeEll εg N)) / (E + edgeEll εg N - eig x k) ^ 2 ≤
            4 * edgeW A₀ N / (a ^ 2 / 4) :=
          div_le_div₀ (by linarith) hE2E1 (by positivity) hdsq
        have h2b : 4 * edgeW A₀ N / (a ^ 2 / 4) = 16 * edgeW A₀ N / a ^ 2 := by
          field_simp
          ring
        linarith
      have h3 : edgeEta εg N / π * ((edgeEL A₀ N - (E + edgeEll εg N)) /
            (E + edgeEll εg N - eig x k) ^ 2) ≤ edgeEta εg N / π * (16 * edgeW A₀ N / a ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 := sandwich_rest_term hN0 hm0 hη.le hW.le
      rw [← ha] at h4
      linarith
  · have h1 := hN.sandwich_le
    have h2 := sandwich_etaW hN
    have h3 : 3 / π * (N : ℝ) ^ (-(εg / 2)) * (K : ℝ) ≤
        3 / π * (4 * Real.log N ^ (3 / 2 * edgeL0 A₀ N) + 1) * (N : ℝ) ^ (-(εg / 2)) := by
      have : 3 / π * (N : ℝ) ^ (-(εg / 2)) * (K : ℝ) =
          3 / π * (K : ℝ) * (N : ℝ) ^ (-(εg / 2)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKle (by positivity)) hq0.le
    rw [h2]
    linarith

/-! ### Proposition 11.13 -/

/-- Proposition 11.13. -/
theorem sandwich {ϑ δm δp C₀ A₀ εg : ℝ} {N : ℕ} (hεg : 0 < εg) (hεg' : εg ≤ 1 / 10)
    (hN : EdgeLarge ϑ C₀ A₀ εg N) (hIn : EdgeInputs 𝕜 ϑ δm δp C₀ A₀ N) (q : ℝ → ℝ)
    (hq : Measurable q) (hq01 : ∀ x, q x ∈ Set.Icc 0 1) (hq1 : ∀ x, x ≤ 1 / 9 → q x = 1)
    (hq0 : ∀ x, 2 / 9 ≤ x → q x = 0) {E : ℝ}
    (hE : E ∈ Set.Icc (2 - 2 * edgeW A₀ N) (2 + edgeW A₀ N)) (M : Ensemble 𝕜 N)
    (hM : M.Assumptions ϑ δm δp C₀) :
    ∫ x, q (smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x))
          ∂M.prodLaw - (N : ℝ) ^ (-20 : ℝ) ≤ M.prodLaw.real {x | lamMax x < E} ∧
      M.prodLaw.real {x | lamMax x < E} ≤
        ∫ x, q (smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x))
          ∂M.prodLaw + (N : ℝ) ^ (-20 : ℝ) := by
  have _ := hεg
  have _ := hεg'
  have hNpos := sandwich_Npos hN
  have hT := sandwich_logpos hN
  have hη := sandwich_eta_pos hN
  have hℓ := sandwich_ell_pos hN
  have hW := sandwich_W_pos hN
  have hℓW := hN.ell_le
  set μ := M.prodLaw with hμ
  set B : Set (Pair N → 𝕜) := rigidityEvent N (edgeL0 A₀ N) with hB
  set S : Set (Pair N → 𝕜) := {x | lamMax x < E} with hS
  have hSm : MeasurableSet S := (isOpen_lt continuous_lamMax continuous_const).measurableSet
  have hBm : MeasurableSet B := by
    have h : B = ⋃ k : Fin N, {x : Pair N → 𝕜 | Real.log N ^ edgeL0 A₀ N *
        (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          |eig x k - gamma N k|} := by
      ext x
      simp [hB, rigidityEvent]
    rw [h]
    exact MeasurableSet.iUnion fun k => measurableSet_le measurable_const
      (((continuous_eig k).sub continuous_const).abs.measurable)
  have hBreal : μ.real B ≤ (N : ℝ) ^ (-20 : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hIn.rigidity M hM)
  have hE1 : E - edgeEll εg N ≤ edgeEL A₀ N := by unfold edgeEL; linarith [hE.2]
  have hE2 : E + edgeEll εg N ≤ edgeEL A₀ N := by unfold edgeEL; linarith [hE.2]
  have hXm : Measurable fun x : Pair N → 𝕜 =>
      q (smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x)) :=
    hq.comp (continuous_smoothCount_toMatrixC hη hE1).measurable
  have hXp : Measurable fun x : Pair N → 𝕜 =>
      q (smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x)) :=
    hq.comp (continuous_smoothCount_toMatrixC hη hE2).measurable
  have hint : ∀ f : (Pair N → 𝕜) → ℝ, Measurable f → (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      Integrable f μ := fun f hf h01 =>
    Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]
      exact (h01 x).2)
  have hSi : Integrable (S.indicator (1 : (Pair N → 𝕜) → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hSm
  have hBi : Integrable (B.indicator (1 : (Pair N → 𝕜) → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hBm
  have hSint : ∫ x, S.indicator (1 : (Pair N → 𝕜) → ℝ) x ∂μ = μ.real S :=
    integral_indicator_one hSm
  have hBint : ∫ x, B.indicator (1 : (Pair N → 𝕜) → ℝ) x ∂μ = μ.real B :=
    integral_indicator_one hBm
  have hXi : Integrable (fun x : Pair N → 𝕜 =>
      q (smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x))) μ :=
    hint _ hXm fun x => hq01 _
  have hXpi : Integrable (fun x : Pair N → 𝕜 =>
      q (smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x))) μ :=
    hint _ hXp fun x => hq01 _
  have hS0 : ∀ x, 0 ≤ S.indicator (1 : (Pair N → 𝕜) → ℝ) x := fun x =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hS1 : ∀ x, S.indicator (1 : (Pair N → 𝕜) → ℝ) x ≤ 1 := fun x =>
    Set.indicator_le_self' (fun _ _ => zero_le_one) x
  have hpw1 : ∀ x : Pair N → 𝕜,
      q (smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x)) ≤
        S.indicator (1 : (Pair N → 𝕜) → ℝ) x + B.indicator (1 : (Pair N → 𝕜) → ℝ) x := by
    intro x
    by_cases hxB : x ∈ B
    · have h1 : B.indicator (1 : (Pair N → 𝕜) → ℝ) x = 1 := Set.indicator_of_mem hxB _
      have h2 := hS0 x
      have h3 := (hq01 (smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N)
        (toMatrixC x))).2
      linarith
    · have hR := sandwich_good hT.le hxB
      have hB0 : B.indicator (1 : (Pair N → 𝕜) → ℝ) x = 0 := Set.indicator_of_notMem hxB _
      by_cases hxS : x ∈ S
      · have h1 : S.indicator (1 : (Pair N → 𝕜) → ℝ) x = 1 := Set.indicator_of_mem hxS _
        have h3 := (hq01 (smoothCount (E - edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N)
          (toMatrixC x))).2
        linarith
      · have h1 : S.indicator (1 : (Pair N → 𝕜) → ℝ) x = 0 := Set.indicator_of_notMem hxS _
        have hge : E ≤ lamMax x := not_lt.1 hxS
        have h8 := sandwich_step1 hN x hR hge
        rw [hq0 _ (by linarith), h1, hB0]
        simp
  have hpw2 : ∀ x : Pair N → 𝕜,
      S.indicator (1 : (Pair N → 𝕜) → ℝ) x ≤
        q (smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N) (toMatrixC x)) +
          B.indicator (1 : (Pair N → 𝕜) → ℝ) x := by
    intro x
    by_cases hxB : x ∈ B
    · have h1 : B.indicator (1 : (Pair N → 𝕜) → ℝ) x = 1 := Set.indicator_of_mem hxB _
      have h2 := hS1 x
      have h3 := (hq01 (smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N)
        (toMatrixC x))).1
      linarith
    · have hR := sandwich_good hT.le hxB
      have hB0 : B.indicator (1 : (Pair N → 𝕜) → ℝ) x = 0 := Set.indicator_of_notMem hxB _
      by_cases hxS : x ∈ S
      · have h1 : S.indicator (1 : (Pair N → 𝕜) → ℝ) x = 1 := Set.indicator_of_mem hxS _
        have h8 := sandwich_step2 hN hE.1 hE.2 x hR hxS
        rw [hq1 _ h8, h1, hB0]
        simp
      · have h1 : S.indicator (1 : (Pair N → 𝕜) → ℝ) x = 0 := Set.indicator_of_notMem hxS _
        have h3 := (hq01 (smoothCount (E + edgeEll εg N) (edgeEL A₀ N) (edgeEta εg N)
          (toMatrixC x))).1
        linarith
  constructor
  · have h := integral_mono hXi (hSi.add hBi) hpw1
    simp only [Pi.add_apply] at h
    rw [integral_add hSi hBi, hSint, hBint] at h
    linarith
  · have h := integral_mono hSi (hXpi.add hBi) hpw2
    simp only [Pi.add_apply] at h
    rw [integral_add hXpi hBi, hBint, hSint] at h
    linarith

end Rigidity
