# The paper and the Lean code

This document states what the Lean code in `Rigidity/` proves, and how its statements relate to the main results of

> L. Erdős, H.-T. Yau, J. Yin, *Rigidity of eigenvalues of generalized Wigner matrices*, arXiv:1007.4652.

Equation, theorem and section numbers of the paper refer to the final version `paper/rigi-10-25-11-final.pdf`, whose numbering is identical to arXiv:1007.4652v7. "The printed text" means arXiv:1007.4652v7. "NP" is the blueprint `blueprint/NP.pdf` (version 1.2), a self-contained proof written as the source of the formalization; its numbers are written "NP Theorem 12.1", "NP §17", and so on. The labels PD-01, …, PD-21 are those of NP Appendix C.1, which lists every difference between the statements of the paper and those of NP.

All declarations quoted below lie in `namespace Rigidity`, in a section with the variable

```lean
variable {𝕜 : Type*} [RCLike 𝕜]
```

so every statement holds for an arbitrary `RCLike` field 𝕜: 𝕜 = ℂ is the hermitian case and 𝕜 = ℝ the symmetric case of the paper. The `lean` blocks are copied verbatim from the source files; proofs are omitted.

## 1. What is proved

### Common objects

- **Ensembles.** `Ensemble 𝕜 N` is a family of probability laws on 𝕜, one for each index pair i ≤ j (`Pair N`); `Ensemble.prodLaw` is their product, the law of the independent entries. `toMatrix` builds the hermitian matrix with h_ij = x_ij and h_ji = conj(x_ij) for i < j, and h_ii = Re x_ii. `Ensemble.varPair` is σ_ij² = 𝔼|h_ij|² of (2.1).
- **The class of Theorems 2.1–2.4.** `Ensemble.Assumptions` ϑ δ₋ δ₊ C₀ is the conjunction of: mean zero (2.1); real diagonal entries almost surely; (A) (2.2); (B) as the quadratic-form bound on 𝐞^⊥ (`Ensemble.AssumptionB`; see §2, item 5); (C) (2.4); and the subexponential decay (2.17) for x ≥ 1, ℙ(|h_ij| > x σ_ij) ≤ ϑ⁻¹ exp(−x^ϑ) (`Ensemble.SubexpDecay`). A law with σ_ij = 0 that satisfies (2.17) is the point mass at 0, so the integral defining σ_ij² cannot hide a law without second moment.
- **Spectral objects.** `eig x k` is the (k+1)-st smallest eigenvalue λ_{k+1} of H (indices `Fin N` are 0-based); `lamMax`, `lamMin` are λ_N and λ_1. `green` is G(z) = (H − z)⁻¹ (2.10), `stieltjesEmp` is m(z) = N⁻¹ tr G(z) (2.11). `msc` is (−z + √(z−2) √(z+2))/2 with principal square roots, which equals (2.13) on the upper half plane; `msc_add_inv` is (2.12) and `msc_im_pos` gives Im m_sc > 0. `Lam`, `LamD`, `LamO` are Λ, Λ_d, Λ_o of (2.16); `SL` is S_L of (2.20); `LRange` is the range (2.18) of L. `rhoSc` is ϱ_sc (2.14), `nsc` is n_sc (2.24), `countFn` is 𝔫 (2.23), `gamma N k` is the classical location γ_{k+1} of (1.3), and `rigWeight N k` = min(k+1, N−k) = min(j, N−j+1) for j = k+1.
- **Probabilities.** Probabilities are values of measures in `ℝ≥0∞`; `ENNReal.ofReal` maps the real bound into `ℝ≥0∞`. A measure applied to an arbitrary set is its outer measure.
- In every statement `Real.log N ^ (…)` parses as (log N)^(…).

### Theorem 2.1 (i), (2.19): `strongLocalLaw_avg`

File `Rigidity/LocalLaw/Strong.lean`.

```lean
theorem strongLocalLaw_avg :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) / (N * z.im) ≤ Lam x z}) ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L)))
```

For all model parameters ϑ, δ₋, δ₊, C₀ > 0 there are constants A₀ > 1, C, c > 0 and φ ∈ (0, 1), and a threshold N₀, such that for every N ≥ N₀, every ensemble of size N in the class with these parameters, and every L in the range (2.18), the probability of the union over z ∈ S_L of the events {Λ(z) ≥ (log N)^{4L}/(Nη)}, η = Im z, is at most C exp(−c (log N)^{φL}). This is (2.19) with the quantifiers in the paper's order; the constants and N₀ are chosen before N, the ensemble and L.

### Theorem 2.1 (ii), (2.21): `strongLocalLaw_entries`

File `Rigidity/LocalLaw/Strong.lean`.

```lean
theorem strongLocalLaw_entries :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw (⋃ z ∈ SL N L, {x | Real.log N ^ (4 * L) * Real.sqrt ((msc z).im / (N * z.im)) +
          Real.log N ^ (4 * L) / (N * z.im) ≤ LamD x z + LamO x z}) ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L)))
```

The same quantifiers as above; the event is the union over z ∈ S_L of {Λ_d(z) + Λ_o(z) ≥ (log N)^{4L} (Im m_sc(z)/(Nη))^{1/2} + (log N)^{4L}/(Nη)}. This is (2.21).

### Theorem 2.1 (iii), (2.22): `extremeEigenvalues_le`

File `Rigidity/LocalLaw/Strong.lean`.

```lean
theorem extremeEigenvalues_le :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | ∃ k : Fin N,
          2 + (N : ℝ) ^ (-(2 / 3 : ℝ)) * Real.log N ^ (9 * L) ≤ |eig x k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L)))
```

The same quantifiers; the event is that some eigenvalue satisfies |λ_j| ≥ 2 + N^{−2/3}(log N)^{9L}, i.e. max_j |λ_j| ≥ 2 + N^{−2/3}(log N)^{9L}. This is (2.22).

### Theorem 2.2, (2.25): `rigidity`

File `Rigidity/LocalLaw/Strong.lean`.

```lean
theorem rigidity :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | ∃ k : Fin N, Real.log N ^ L * (rigWeight N k : ℝ) ^ (-(1 / 3 : ℝ)) *
          (N : ℝ) ^ (-(2 / 3 : ℝ)) ≤ |eig x k - gamma N k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L)))
```

The same quantifiers; the event is that some j satisfies |λ_j − γ_j| ≥ (log N)^L min(j, N−j+1)^{−1/3} N^{−2/3}. This is (2.25), written with the 0-based index k = j − 1.

### Theorem 2.2, (2.26): `countingFunction_close`

File `Rigidity/LocalLaw/Strong.lean`.

```lean
theorem countingFunction_close :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
      M.prodLaw {x | Real.log N ^ L / N ≤ ⨆ E : Set.Icc (-5 : ℝ) 5, |countFn x E - nsc E|} ≤
        ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L)))
```

The same quantifiers; the event is sup_{|E| ≤ 5} |𝔫(E) − n_sc(E)| ≥ (log N)^L/N, with the supremum itself (the family is bounded by 1, so the real supremum `⨆` is the least upper bound). This is (2.26).

### Theorem 2.3, (2.36): `dbm_localErgodicity`

File `Rigidity/Flow/Endpoint.lean`.

```lean
theorem dbm_localErgodicity :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO →
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, max n 3 ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + K) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ) ^ (-1 + ε') + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2))
```

The objects (files `Rigidity/Flow/Correlation.lean`, `Rigidity/Flow/Ensembles.lean`, `Rigidity/Flow/GaussEnsemble.lean`):

- `gaussH 𝕜 N` is the centred Gaussian measure on the hermitian matrices `Herm 𝕜 N` with covariance (2/(βN))·Id for the inner product ⟨X, Y⟩ = Tr XY, β = `betaF 𝕜` = dim_ℝ 𝕜. This is the GUE (𝕜 = ℂ) and the GOE with diagonal variance 2/N (𝕜 = ℝ), the matrix V of (2.29).
- `Ensemble.eigLaw M t` is ν_t, the law of the ordered eigenvalues of H_t = e^{−t/2} H₀ + (1 − e^{−t})^{1/2} V, with H₀ distributed as the matrix of M and V independent with law `gaussH 𝕜 N`; this is (2.29). `gbeLaw 𝕜 N` is μ, the law of the ordered eigenvalues of V.
- `corrX O E' ϱ x` is 𝒳 = Σ O(Nϱ(x_{i_1} − E'), …, Nϱ(x_{i_n} − E')), summed over the pairwise distinct (i_1, …, i_n); `corrC N n` is C_{N,n} = N^n (N−n)!/N!; and `corrLHS M O E b t` = |∫_{E−b}^{E+b} (2b)⁻¹ C_{N,n} (𝔼_{ν_t} 𝒳 − 𝔼_μ 𝒳) dE'| with ϱ = ϱ_sc(E).

For all model parameters, all ε′, δ > 0, all c ∈ (0, 2], all n ≥ 1 and all ρ_O > 0 there is a constant C > 0 such that for all N ≥ max(n, 3), every ensemble of the class, every O : ℝⁿ → ℝ bounded by Bd, K-Lipschitz for the Euclidean norm and vanishing outside [−ρ_O, ρ_O]ⁿ, every E ∈ [−2+c, 2−c], every b ∈ (0, c/2) and every t ≥ N^{−1+δ+ε′}, the left side of (2.36) is at most C (Bd + K) N^{2ε′} (b⁻¹ N^{−1+ε′} + b^{−1/2} N^{−δ/2}). The constant C does not depend on N, the ensemble, O, E, b or t; it depends on O only through ρ_O, and the bound is linear in Bd + K, so with Bd = ‖O‖_∞ and K = Lip(O) it is the form C′(‖O‖_∞ + Lip(O)) of the final version. By the change of variables α = Nϱ(x − E′), `corrLHS` is the left side of (2.36), with p^{(n)} the n-point marginal of the symmetrised eigenvalue law (§2, item 3); the supremum over t of (2.36) is the universal quantifier over t.

### Theorem 2.4, (2.41): `edgeUniversality_max`

File `Rigidity/Edge/Universality.lean`.

```lean
theorem edgeUniversality_max :
    ∀ ϑ : ℝ, 0 < ϑ → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ δm δp C₀ : ℝ, 0 < δm → 0 < δp → 0 < C₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Mv Mw : Ensemble 𝕜 N,
      Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ → Ensemble.MomentMatch2 Mv Mw →
      ∀ s : ℝ,
        Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s - (N : ℝ) ^ (-ε)} ≤
            Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) ∧
          Mw.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s} ≤
            Mv.prodLaw {x | (N : ℝ) ^ (2 / 3 : ℝ) * (lamMax x - 2) ≤ s + (N : ℝ) ^ (-ε)} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ))
```

For every ϑ > 0 there are ε, δ > 0 such that for all δ₋, δ₊, C₀ > 0 there is N₀ with the following property: for every N ≥ N₀, any two ensembles M^v, M^w of size N in the class with parameters (ϑ, δ₋, δ₊, C₀) whose entries have the same moments 𝔼 h̄^l h^u for l + u ≤ 2 (`Ensemble.MomentMatch2`, (2.40)), and every real s, both inequalities of (2.41) hold, written additively: ℙ^v(N^{2/3}(λ_N − 2) ≤ s − N^{−ε}) ≤ ℙ^w(N^{2/3}(λ_N − 2) ≤ s) + N^{−δ} and ℙ^w(N^{2/3}(λ_N − 2) ≤ s) ≤ ℙ^v(N^{2/3}(λ_N − 2) ≤ s + N^{−ε}) + N^{−δ}. The exponents depend on ϑ only, and N₀ does not depend on s, as in the paper. The proof takes ε = 1/100 and δ = 1/20 for every ϑ (NP Theorem 11.1).

### Theorem 2.4, the smallest eigenvalue: `edgeUniversality_min`

File `Rigidity/Edge/Universality.lean`.

```lean
theorem edgeUniversality_min :
    ∀ ϑ : ℝ, 0 < ϑ → ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
    ∀ δm δp C₀ : ℝ, 0 < δm → 0 < δp → 0 < C₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Mv Mw : Ensemble 𝕜 N,
      Mv.Assumptions ϑ δm δp C₀ → Mw.Assumptions ϑ δm δp C₀ → Ensemble.MomentMatch2 Mv Mw →
      ∀ s : ℝ,
        Mv.prodLaw {x | s + (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} ≤
            Mw.prodLaw {x | s ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ)) ∧
          Mw.prodLaw {x | s ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} ≤
            Mv.prodLaw {x | s - (N : ℝ) ^ (-ε) ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (lamMin x + 2)} +
              ENNReal.ofReal ((N : ℝ) ^ (-δ))
```

The paper's "Analogous result holds for the smallest eigenvalue λ₁", with the same ε, δ, stated for the events {s ≤ N^{2/3}(λ_1 + 2)}: the image of (2.41) under H ↦ −H. It is equivalent to the form with the events {N^{2/3}(λ_1 + 2) ≤ s} (§2, item 8).

### Further statements

**`mainTheorems_event`** (`Rigidity/Rigidity/Main.lean`; NP Proposition 2.7). Theorems 2.1 and 2.2 with one tuple of constants and one measurable event Ξ of probability at least 1 − C exp(−c(log N)^{φL}) on which the five bounds (2.19), (2.21), (2.22), (2.25), (2.26) hold simultaneously, for all z ∈ S_L, all j and all |E| ≤ 5 (`MainGood`). The paper has no counterpart; the five statements above are derived from it.

```lean
theorem mainTheorems_event :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∃ A₀ C c φ : ℝ, 1 < A₀ ∧ 0 < C ∧ 0 < c ∧ 0 < φ ∧ φ < 1 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ L : ℝ, LRange A₀ N L →
    ∃ Ξ : Set (Pair N → 𝕜), MeasurableSet Ξ ∧
      M.prodLaw Ξᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * Real.log N ^ (φ * L))) ∧
      ∀ x ∈ Ξ, MainGood L x
```

**`dbm_localErgodicity_uniform`** (`Rigidity/Flow/Endpoint.lean`). Theorem 2.3 with one constant C valid for 𝕜 = ℝ and 𝕜 = ℂ at once; `ErgodicityBound` is the bound of `dbm_localErgodicity` for one field and one constant.

```lean
def ErgodicityBound (𝕜 : Type*) [RCLike 𝕜] (ϑ δm δp C₀ ε' δ c : ℝ) (n : ℕ) (ρO C : ℝ) : Prop :=
  ∀ N : ℕ, max n 3 ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + K) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ) ^ (-1 + ε') + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2))
```

```lean
theorem dbm_localErgodicity_uniform :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO →
    ∃ C : ℝ, 0 < C ∧ ErgodicityBound ℝ ϑ δm δp C₀ ε' δ c n ρO C ∧
      ErgodicityBound ℂ ϑ δm δp C₀ ε' δ c n ρO C
```

**`dbm_quantitative`** (`Rigidity/Flow/Endpoint.lean`; NP Theorem 12.1). A sharper form of Theorem 2.3: for all t > 0 with Nt ≥ (log N)² and N ≥ max(N_q, n), the left side of (2.36) is at most C₁ (Bd + K) exp(A₁ (log log N)²) (b⁻¹ N⁻¹ + b^{−1/2} (Nt)^{−1/2}). The paper has no counterpart.

```lean
theorem dbm_quantitative :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n → ∀ ρO : ℝ, 0 < ρO →
    ∃ A₁ : ℝ, 1 ≤ A₁ ∧ ∃ Nq : ℕ, 3 ≤ Nq ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ N : ℕ, max Nq n ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ t : ℝ, 0 < t → Real.log N ^ 2 ≤ N * t →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
      corrLHS M O E b t ≤ C₁ * (Bd + K) * Real.exp (A₁ * Real.log (Real.log N) ^ 2) *
        (b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N * t) ^ (-(1 / 2 : ℝ)))
```

**`dbm_localErgodicity_hoelder`** (`Rigidity/Flow/Endpoint.lean`; NP Corollary 19.5). For O Hölder continuous with exponent α ∈ (0, 1] and seminorm at most H_α, bounded by Bd and vanishing outside [−ρ_O, ρ_O]ⁿ: for N ≥ N₂ and t ≥ N^{−1+δ+ε′}, the left side of (2.36) is at most C (Bd + H_α) N^{2ε′} (b⁻¹ N⁻¹ + b^{−1/2} N^{−δ/2})^α. This is the Hölder statement of the remark after Theorem 2.3 in the final version.

```lean
theorem dbm_localErgodicity_hoelder :
    ∀ ϑ δm δp C₀ : ℝ, 0 < ϑ → 0 < δm → 0 < δp → 0 < C₀ →
    ∀ ε' δ : ℝ, 0 < ε' → 0 < δ → ∀ c : ℝ, 0 < c → c ≤ 2 → ∀ n : ℕ, 1 ≤ n →
    ∀ ρO : ℝ, 0 < ρO → ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ N₂ : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, N₂ ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd Hα : ℝ, (∀ u, |O u| ≤ Bd) →
      (∀ u v, |O u - O v| ≤ Hα * ‖u - v‖ ^ α) → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + Hα) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ)⁻¹ + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2)) ^ α
```

The statements `localLaw_i_ii` (`Rigidity/Strong/Extension.lean`) and `localLaw_i_iii` (`Rigidity/Strong/Event.lean`) are the level-K form of NP Theorem 2.6, under the normalisation ϑ ≤ 1, δ± ≤ 1, C₀ ≥ 1 and with the exponents of the level parameter K in place of powers of log N. They are internal statements, not Theorem 2.1; `mainTheorems_event` removes the normalisation and has the exact exponents 4L, 9L, L, 10L of the paper.

### Statements that identify the paper's objects

**`gbeLaw_eq_muStar`** (`Rigidity/Flow/JointDensity.lean`; NP Theorem 16.3). The law μ of the ordered eigenvalues of V is `muStar β N`, the probability measure with density proportional to Δ(x)^β exp(−βN Σ x_i²/4) on the chamber x_1 < ⋯ < x_N, where Δ(x) = ∏_{i<j}(x_j − x_i) (`vandermonde`, `gbeWeight`). This is μ of (2.30) restricted to the ordered chamber and renormalised; since 𝒳 is a symmetric function, expectations of 𝒳 under the two agree. So the reference measure in `corrLHS` is the paper's μ.

```lean
theorem gbeLaw_eq_muStar (N : ℕ) : gbeLaw 𝕜 N = muStar (betaF 𝕜) N
```

**`Ensemble.assumptionB_iff`** (`Rigidity/Ensemble/SpecB.lean`). Under (A), N > 0 and δ₊ > 0, the quadratic-form version `Ensemble.AssumptionB` of (B) is equivalent to `Ensemble.AssumptionBSpec`, which is (2.3) as printed: one eigenvalue of B equals 1 and all others lie in [−1+δ₋, 1−δ₊] (so 1 is a simple eigenvalue). Here `M : Ensemble 𝕜 N` is a section variable.

```lean
theorem assumptionB_iff (hN : 0 < N) (hA : M.AssumptionA) {δm δp : ℝ} (hδp : 0 < δp) :
    M.AssumptionB δm δp ↔ M.AssumptionBSpec δm δp
```

**`gbeEnsemble_hermLaw`** (`Rigidity/Flow/GaussEnsemble.lean`; NP Lemma 14.C). The ensemble `gbeEnsemble 𝕜 N` with independent entries v_ii ∼ N(0, 2/(βN)) real and, for i < j, v_ij = ξ + iη with ξ, η ∼ N(0, 1/(βN)) independent (for 𝕜 = ℝ, v_ij = ξ ∼ N(0, 1/N)) has matrix law `gaussH 𝕜 N`. So V is the GUE, resp. the GOE, with the variances stated after (2.29) in the final version.

```lean
theorem gbeEnsemble_hermLaw (N : ℕ) : (gbeEnsemble 𝕜 N).hermLaw = gaussH 𝕜 N
```

**`Ensemble.ouFlow_gbe_hermLaw`** (`Rigidity/Flow/Ensembles.lean`). The ensemble `Ensemble.ouFlow` M (gbeEnsemble 𝕜 N) t, whose entry laws are the convolutions of the laws of e^{−t/2} h_ij and (1 − e^{−t})^{1/2} v_ij, has matrix law `Ensemble.flowLaw M t`, the law of H_t of (2.29). So H_t is itself an ensemble with independent entries.

```lean
theorem Ensemble.ouFlow_gbe_hermLaw {N : ℕ} (M : Ensemble 𝕜 N) (t : ℝ) :
    (M.ouFlow (gbeEnsemble 𝕜 N) t).hermLaw = M.flowLaw t
```

## 2. Differences from the printed statements

The Lean statements say what Theorems 2.1–2.4 say, or more, with two exceptions, items 1 and 2, where the Lean statement of Theorem 2.3 is narrower than the printed text. Both are corrections of the printed text. The final version of the paper (`paper/`) already incorporates PD-04, PD-21 and the other corrections of the printed text: γ_N := 2 (PD-03), the GOE normalisation in the symmetric case (PD-06), the reading of p^{(n)} as marginals of the symmetrised eigenvalue law (PD-05), the dependence of C in Theorem 2.3 on (ϑ, δ±, C₀) and the condition N ≥ max(n, 3) (PD-16), the scale invariance of (2.17) and (2.40) in Theorem 2.4 (PD-15), and the remarks on the range (2.18) (PD-01, PD-02). Items 3–10 are formulations of the Lean code that are equivalent to the printed statement, or stronger.

1. **Energy range in Theorem 2.3 (PD-04).** Printed: "for any fixed E ∈ [2 − c, 2 + c]"; there ϱ(E) is not defined, and ϱ_sc(E) = 0 for E ≥ 2. Lean: `E ∈ Set.Icc (-2 + c) (2 - c)` with 0 < c ≤ 2, b ∈ (0, c/2) and ϱ = ϱ_sc(E). Why: the printed interval is a misprint; the argument of the paper (through Theorem 2.1 of [ESYY]) needs ϱ_sc bounded below on the window, i.e. the bulk. The final version states [−2+c, 2−c].
2. **Test functions in Theorem 2.3 (PD-21).** Printed: O compactly supported and continuous, C depending on O. Lean: O Lipschitz, vanishing outside [−ρ_O, ρ_O]ⁿ, with the bound C (Bd + K) N^{2ε′}(…) and C depending on O only through ρ_O. Why: the argument gives the rate of (2.36) only when the regularity of O is controlled (the source of the paper's proof applies a result stated for smooth observables), and a bound of this form for all continuous O would amount to a total-variation bound, which the method does not give (NP PD-21, NP Remark 19.6). For Hölder O the rate holds raised to the power α (`dbm_localErgodicity_hoelder`). The final version states Theorem 2.3 for Lipschitz O and gives the Hölder form in the remark after it.
3. **Correlation functions and the reference measure (PD-05).** Printed: (2.36) with the densities p^{(n)}_{t,N}, p^{(n)}_{μ,N} of (2.33), (2.34). Lean: the density-free form `corrLHS`, with the symmetric statistic 𝒳 (`corrX`) and C_{N,n} (`corrC`); N^n ∫ F dp^{(n)} = C_{N,n} 𝔼 Σ_{distinct} F(x_{i_1}, …, x_{i_n}) for the n-point marginal p^{(n)} of the symmetrised law, so no density is needed. The reference measure is the law of the eigenvalues of V, identified with μ of (2.30) by `gbeLaw_eq_muStar`. Why: the statement then needs no existence or regularity of densities.
4. **The flow; symmetric case (PD-06).** Printed: in the symmetric case "the matrix elements of β_t in (2.28) are real Brownian motions and V in (2.29) is a GOE matrix". Lean: V has law `gaussH 𝕜 N`; for 𝕜 = ℝ this is the GOE with off-diagonal variance 1/N and diagonal variance 2/N. Dyson Brownian motion enters only through the law of H_t at fixed time t, (2.29), as in the statement of Theorem 2.3; the SDE (2.28) and the equation (2.31) are not part of any Lean statement. Why: with this normalisation the GOE is invariant under the flow and its eigenvalue law is μ of (2.30) with β = 1.
5. **Assumption (B) (PD-14).** Printed (2.3): 1 is a simple eigenvalue of B and Spec(B) ⊆ [−1+δ₋, 1−δ₊] ∪ {1}. Lean: `Ensemble.AssumptionB`, (−1+δ₋)|v|² ≤ ⟨v, Bv⟩ ≤ (1−δ₊)|v|² for all real v with Σ v_i = 0. Why: the quadratic form is the form used in the proofs; `Ensemble.assumptionB_iff` proves the equivalence with (2.3) under (A).
6. **Classical locations, the supremum in (2.26), indices (PD-03, PD-20).** γ_N: (1.3) does not determine γ_N (N n_sc(x) = N for all x ≥ 2); Lean: `gamma N k` = inf{x : k + 1 ≤ N n_sc(x)}, so γ_N = 2 (`gamma_last`). (2.26): the supremum need not be attained (𝔫 is right-continuous); Lean uses the supremum itself, not a form "there is E with …". Indices: `Fin N` is 0-based, so `eig x k` is λ_{k+1} and `rigWeight N k` is min(j, N−j+1) for j = k+1; max_j |λ_j| ≥ … in (2.22) is written as ∃ k, … ≤ |λ_{k+1}|, and ∃ j in (2.25) as ∃ k.
7. **Conditions on the laws of the entries; constants of Theorem 2.3 (PD-15, PD-16).** Printed: (2.17) and (2.40) in Theorem 2.4 are stated for the rescaled entries v_ij = N^{1/2} h_ij. Lean: both are stated for the laws of h_ij; both conditions are invariant under this rescaling. In Theorem 2.4 both ensembles are taken with the same parameters (ϑ, δ₋, δ₊, C₀); this loses nothing, because the class is monotone in the parameters (`Ensemble.Assumptions.mono`). In Theorem 2.3, C depends also on (ϑ, δ₋, δ₊, C₀) (printed: "depending on all these parameters and on O") and N ≥ max(n, 3) is a hypothesis (implicit in the printed text, which needs N ≥ n).
8. **Exponents in Theorem 2.4; the statement for λ₁.** The exponents ε, δ are chosen after ϑ and before (δ₋, δ₊, C₀), as in the paper; the proof gives the absolute values ε = 1/100, δ = 1/20. The inequalities are in additive form in `ℝ≥0∞`, which is equivalent to the subtracted form of (2.41). For λ₁ the Lean statement uses the events {s ≤ N^{2/3}(λ_1 + 2)}, the mirror image of (2.41) under H ↦ −H. The form with the events X ≤ s, X = N^{2/3}(λ_1 + 2), follows: taking complements gives ℙ^w(X < s) ≤ ℙ^v(X < s + N^{−ε}) + N^{−δ} and ℙ^v(X < s − N^{−ε}) ≤ ℙ^w(X < s) + N^{−δ} for every real s, and ℙ(X ≤ s) = lim_{s′↓s} ℙ(X < s′) on both sides. Since both forms hold for every real s, they are equivalent.
9. **Dependence on the field.** The field 𝕜 is fixed before all other quantifiers, so thresholds and constants may depend on whether 𝕜 is ℝ or ℂ. The paper states the hermitian and the symmetric case separately, so this is its content. `dbm_localErgodicity_uniform` gives one constant for both fields in Theorem 2.3.
10. **The events of (2.19) and (2.21).** They are unions over the uncountable set S_L; the Lean statements bound the measure of these unions themselves, which is their outer measure (no measurability is claimed or needed). `mainTheorems_event` gives in addition one measurable event of large probability on which all five bounds hold.

**Auxiliary facts without a standalone Lean counterpart.** Some auxiliary facts stated in the paper and in NP have no separate Lean statement, because the Lean proof does not need them: the uniqueness of the solution of (2.12) with positive imaginary part (NP Lemma 3.1 (a); the Lean code defines `msc` by the explicit formula and proves (2.12) and Im m_sc > 0 for it, `msc_add_inv` and `msc_im_pos`), and the strict monotonicity γ_j < γ_{j+1} of the classical locations (NP Lemma 3.4 (c)). The internal statements of the paper's own proofs (Sections 3–7 of the paper) are not formalized, since the Lean proof follows NP (§5).

## 3. Consistency of the hypotheses

The hypotheses of the Lean statements can hold together, and the bounds are not trivially true.

- **Witnesses for the class.**
  - `rademacher_assumptions` (`Rigidity/Ensemble/Basic.lean`): for every N > 0 and every 𝕜, the ensemble `rademacher` with entries ±N^{−1/2} with probability 1/2 each satisfies `Ensemble.Assumptions` with (ϑ, δ₋, δ₊, C₀) = (1/2, 1, 1, 1).
  - `bandEnsemble8_assumptions` (`Rigidity/Ensemble/SpecB.lean`): the band ensemble of size 8 with variance 1/5 for |[i−j]_8| ≤ 2 and the point mass at 0 otherwise is in the class with parameters (1/2, 1/2, 1/4, 2). So the class contains ensembles with vanishing variances (Example 2 of the paper).
  - `gbeTilde_assumptions` (`Rigidity/Flow/Ensembles.lean`): for N ≥ 3, the Gaussian ensemble rescaled by (1 + (2−β)/(βN))^{−1/2} is in the class with parameters (min(ϑ,1)/14, (3/4)min(δ₋,1), (3/4)min(δ₊,1), max(C₀,2)) for any ϑ, δ±, C₀ > 0. Its entries are Gaussian, and complex for 𝕜 = ℂ.
- **Compiled instances in the four endpoint files.** Each file contains `example`s that apply the statements to the Rademacher ensemble:
  - `Rigidity/LocalLaw/Strong.lean`: over ℂ with parameters (1/2, 1, 1, 1), one tuple of constants, one size N and one L in the range (2.18) at which all five bounds (2.19), (2.21), (2.22), (2.25), (2.26) hold.
  - `Rigidity/Rigidity/Main.lean`: the same for `mainTheorems_event`, with the measurable event.
  - `Rigidity/Edge/Universality.lean`: the inputs `EdgeInputs` of the edge argument over ℂ; (2.41) for M^v = M^w = Rademacher over ℂ, and the λ₁ statement over ℝ, at a size N ≥ 2 and for all s.
  - `Rigidity/Flow/Endpoint.lean`, for every `RCLike` 𝕜 and the parameters (1, 1, 1, 1): the bound `RigidityBound` (Theorem 2.2 with one tuple of constants) at one admissible (N, L); NP Theorem 12.1 for O(u) = max(0, 1 − ‖u‖) on ℝ², E = 0, b = 1/4, t = 1; Theorem 2.3 with ε′ = δ = 1/4, c = 1, n = 2, ρ_O = 1, E = 0, b = 1/4, t = N^{−1/2}, for every N ≥ 3; the uniform form for ℝ and ℂ with one constant; and the Hölder form for O(u) = max(0, 1 − ‖u‖)^{1/2}, α = 1/2. Two further `example`s check that these test functions equal 1 at 0.
- **The range of L is not empty for large N** (`exists_LRange_nonempty`), and S_L is not empty below the upper end of (2.18).
- **The bounds are not trivial.** In Theorems 2.1 and 2.2 the proof gives C = 1 and c = 1/2, so the right side exp(−(log N)^{φL}/2) is < 1; the thresholds are within reach, since (log N)^{4L} ≤ (10N)^{2/5} on the range (2.18). In Theorem 2.4, N^{−δ} < 1 and the shift N^{−ε} tends to 0. In Theorem 2.3 the right side tends to 0 for fixed b when 3ε′ < 1 and 4ε′ < δ.
- **No junk values.** `green` is used only for Im z > 0 (on S_L). `corrX` is a finite sum of values of a bounded continuous O, so both expectations in `corrLHS` are integrals of bounded continuous functions against probability measures. `lamMax`, `lamMin` are used only for N ≥ N₀ > 0. `Ensemble.MomentMatch2` compares integrals of polynomially bounded functions, which are integrable under (2.17).
- **No conditional statement.** The intermediate statements whose hypotheses are themselves statements (`EdgeInputs`, `EdgeLarge`, `RigidityBound`) are proved inside the proofs of `edgeUniversality_max` and of the Theorem 2.3 statements; none of them appears as a hypothesis of a statement of §1.

## 4. External inputs

None. The Lean code uses Mathlib and nothing else. The results of [EYY], [EYY2] and [ESYY] that the paper quotes (among them the large deviation bounds, the properties of m_sc, the a priori norm bound, the counting-function lemma, and Theorem 2.1 of [ESYY] on Dyson Brownian motion) are proved inside the library, following NP. No hypothesis of a statement of §1 stands for an external theorem: the hypotheses are the model parameters, the class `Ensemble.Assumptions`, the moment matching (2.40), and the conditions on N, L, O, E, b, t of the paper.

## 5. Proof strategy

The Lean proof follows NP, a self-contained proof written for the formalization, which proves the paper's results at the paper's precision: the error factors (log N)^L and the probability bounds C exp(−c(log N)^{φL}) of Theorems 2.1 and 2.2, and the rate of (2.36). NP keeps the statements of the paper (up to the differences of §2) but replaces many of its proofs. NP §1 and the introductions of its parts describe the differences; NP Appendix C lists them.

- **Part I (Theorems 2.1, 2.2; NP §1–§10).** One level parameter K with (log N)³ ≤ K ≤ N^{c₀} replaces the coupled exponents of the paper: every error factor is a power of K and every exceptional probability is at most N^C e^{−K} (NP Theorem 2.6); Theorems 2.1 and 2.2 follow by K = (log N)^{φL} (NP Proposition 2.7). The large deviation bounds are proved for unequal, possibly vanishing variances from Hoeffding's inequality after truncation (NP §4). The weak law uses a deterministic continuity argument along a finite lattice in Im z (NP §5). Fluctuation averaging conditions on a minor and uses a finite Neumann expansion (NP §6), in place of Section 7 of the paper. The strong law uses a moment inequality that improves itself in one step, with no iteration (NP §7). The norm bound comes from a grid net and the averaged law outside the spectrum (NP §8). Rigidity uses the Helffer–Sjöstrand formula proved from the divergence theorem on rectangles, a deterministic bound of the counting function by m − m_sc, and a deterministic conversion lemma that treats both spectral edges directly (NP §3, §9).
- **Part II (Theorem 2.4; NP §11).** The input from Part I is (2.21) and (2.25) only. The law of λ_N is compared with a smoothed counting functional directly on the rigidity event of (2.25) (NP §11.4), in place of Lemma 6.1 and Corollary 6.2 of the paper. The Green function comparison (NP §11.7) is a Lindeberg replacement in which the change of the functional under the replacement of one entry is given exactly by a 2 × 2 determinant (NP §11.5); the third-order term is bounded by a decorrelation lemma for one off-diagonal resolvent entry (NP §11.6). The statement for λ₁ follows by H ↦ −H. The exponents are explicit, ε = 1/100, δ = 1/20 (NP Appendix C.3).
- **Part III (Theorem 2.3; NP §12–§20).** The paper derives (2.36) from Theorem 2.1 of [ESYY], whose proof uses the SDE for the eigenvalues, the logarithmic Sobolev inequality by the Bakry–Émery argument, and the Dirichlet form inequality with an auxiliary dynamics. NP keeps the idea of the relative entropy with respect to a local relaxation measure but replaces these tools (NP §12.3): the flow is the Ornstein–Uhlenbeck (Mehler) semigroup at matrix level, restricted to invariant functions (NP §14, §15); the joint eigenvalue density of the Gaussian ensembles is proved by an ergodicity argument (NP §16, Theorem 16.3); the Prékopa–Leindler inequality gives the logarithmic Sobolev inequality for the local relaxation measure and a sub-Gaussian bound for gap observables under convex log-gases (NP §17), which replaces the Dirichlet form inequality; an entropy bound (NP §18) and a deterministic bookkeeping on a rigidity event (NP §19) give the sharper NP Theorem 12.1, from which (2.36) follows. The only input from Part I is Theorem 2.2.

NP Lemma 17.6, Theorem 17.7 and Corollary 17.9 (the two-point inequality, gap concentration under convex log-gases, and its consequence for gap observables) are described in NP (§20) as new in this form; their attribution in the literature has not been checked yet.

## 6. Not formalized

The following statements of the paper have no Lean counterpart:

- (2.37), universality for all t ≥ 0 (the paper refers to the argument of [EYY2] and does not give the proof);
- (2.42), the extension of (2.41) to several extreme eigenvalues, together with Theorem 6.4 (Green function comparison in general form), whose proof the paper omits;
- the quaternion self-dual case;
- decay conditions weaker than (2.17).

The Tracy–Widom limit (2.39) is background quoted by the paper, not a result of it.

## 7. Axioms and build

Every theorem named in §1–§3 depends only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. The source contains no `sorry`, no `axiom` declaration and no `native_decide`. To reproduce the check, build the library with `lake build` and run `lake env lean` on a scratch file outside the source tree, for example:

```
import Rigidity

#print axioms Rigidity.strongLocalLaw_avg
#print axioms Rigidity.strongLocalLaw_entries
#print axioms Rigidity.extremeEigenvalues_le
#print axioms Rigidity.rigidity
#print axioms Rigidity.countingFunction_close
#print axioms Rigidity.mainTheorems_event
#print axioms Rigidity.dbm_localErgodicity
#print axioms Rigidity.dbm_localErgodicity_uniform
#print axioms Rigidity.dbm_quantitative
#print axioms Rigidity.dbm_localErgodicity_hoelder
#print axioms Rigidity.edgeUniversality_max
#print axioms Rigidity.edgeUniversality_min
#print axioms Rigidity.gbeLaw_eq_muStar
#print axioms Rigidity.Ensemble.assumptionB_iff
#print axioms Rigidity.gbeEnsemble_hermLaw
#print axioms Rigidity.Ensemble.ouFlow_gbe_hermLaw
#print axioms Rigidity.rademacher_assumptions
#print axioms Rigidity.bandEnsemble8_assumptions
#print axioms Rigidity.gbeTilde_assumptions
```

Each line prints `[propext, Classical.choice, Quot.sound]`.
