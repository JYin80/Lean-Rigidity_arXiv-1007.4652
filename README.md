# Lean formalization of Erdős, Yau, Yin, "Rigidity of eigenvalues of generalized Wigner matrices"

This repository contains a Lean 4 / Mathlib proof of the main results of

> László Erdős, Horng-Tzer Yau, Jun Yin, *Rigidity of eigenvalues of generalized Wigner matrices*,
> [arXiv:1007.4652](https://arxiv.org/abs/1007.4652).

The version of the paper that the Lean statements follow is [`paper/rigi-10-25-11-final.pdf`](paper/rigi-10-25-11-final.pdf)
(LaTeX source in `paper/tex/`): arXiv:1007.4652v7 with a small number of corrections, listed in
[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md). Theorem and equation numbers are those of the paper.

The Lean proof does not follow the paper line by line. It follows a self-contained proof written for the
formalization by Jun Yin and Claude, [`blueprint/NP.pdf`](blueprint/NP.pdf) (LaTeX source in `blueprint/`), which proves the paper's
results at the paper's precision without citing other papers for any step. Numbers in the Lean comments refer to
this blueprint; results of the paper are cited there as [EYY, …].

## Main results

Both symmetry classes are covered by one statement over `{𝕜 : Type*} [RCLike 𝕜]` (`𝕜 = ℝ`: real symmetric,
`𝕜 = ℂ`: complex hermitian).

| Paper | Lean | File |
|---|---|---|
| Theorem 2.1 (i), (2.19) — strong local semicircle law, averaged | `Rigidity.strongLocalLaw_avg` | `Rigidity/LocalLaw/Strong.lean` |
| Theorem 2.1 (ii), (2.21) — entrywise law | `Rigidity.strongLocalLaw_entries` | `Rigidity/LocalLaw/Strong.lean` |
| Theorem 2.1 (iii), (2.22) — extreme eigenvalues | `Rigidity.extremeEigenvalues_le` | `Rigidity/LocalLaw/Strong.lean` |
| Theorem 2.2, (2.25) — rigidity of eigenvalues | `Rigidity.rigidity` | `Rigidity/LocalLaw/Strong.lean` |
| Theorem 2.2, (2.26) — counting function | `Rigidity.countingFunction_close` | `Rigidity/LocalLaw/Strong.lean` |
| Theorem 2.3, (2.36) — local ergodicity of Dyson Brownian motion | `Rigidity.dbm_localErgodicity`, `Rigidity.dbm_localErgodicity_uniform` | `Rigidity/Flow/Endpoint.lean` |
| Theorem 2.4, (2.41) and λ₁ — universality of extreme eigenvalues | `Rigidity.edgeUniversality_max`, `Rigidity.edgeUniversality_min` | `Rigidity/Edge/Universality.lean` |

For example, Theorem 2.2, (2.25):

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

Theorem 2.3 is stated for bulk energies `E ∈ [-2 + c, 2 - c]` and compactly supported Lipschitz test functions,
as in the final version of the paper; a Hölder version is `Rigidity.dbm_localErgodicity_hoelder`. The full list of
statements, every difference from the printed text, and what is not formalized are in
[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md).

## External inputs

None. The library depends only on Mathlib. The results of other papers that the paper cites (in particular the
local relaxation flow of Erdős–Schlein–Yau–Yin) are proved inside the library, and no hypothesis of a main theorem
stands for an external result.

## Axioms

Every main theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`
and no declared `axiom`. To check, compile a file containing

```lean
import Rigidity
#print axioms Rigidity.rigidity
#print axioms Rigidity.dbm_localErgodicity_uniform
#print axioms Rigidity.edgeUniversality_max
```

with `lake env lean <file>`.

## Build

The toolchain is `leanprover/lean4:v4.36.0-rc2` (file `lean-toolchain`) with Mathlib `v4.36.0-rc2`.

```
lake exe cache get
lake build
```

The hypotheses of the theorems can be satisfied: `Rigidity.rademacher_assumptions` (Rademacher entries),
`Rigidity.bandEnsemble8_assumptions` (a band matrix with vanishing variances) and `Rigidity.gbeTilde_assumptions`
(Gaussian entries) are members of the ensemble class, and the four files of the main results end with compiled
examples that instantiate each main theorem.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail: what is proved,
every difference between the Lean statements and the printed ones, the external inputs, and where the Lean proof
takes a different route from the paper.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Original paper: László Erdős, Horng-Tzer Yau and Jun Yin. Paper version that the Lean proof follows
([`blueprint/NP.pdf`](blueprint/NP.pdf)): Jun Yin, Claude. Lean formalization: Jun Yin, Claude.

## Palomar

The repository is laid out for the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics.
All source files use Lean's module system. [`Rigidity/MainDefs.lean`](Rigidity/MainDefs.lean) holds every definition
used by the statements of Theorems 2.1–2.4 and depends on Mathlib only; [`Challenge.lean`](Challenge.lean) is the
statement to audit (it imports Mathlib only and repeats `Rigidity/MainDefs.lean` verbatim),
[`Solution.lean`](Solution.lean) proves it from the library, [`comparator.json`](comparator.json) names the compared
theorems and [`formalization.yaml`](formalization.yaml) holds the metadata. `lake build` also builds `Challenge.lean`
(eight `sorry` warnings, by design) and `Solution.lean`. `python3 scripts/check-lean-sources.py` and
`./scripts/verify-comparator.sh` (Linux, needs `bwrap`) run the checks locally; submissions go to
<https://submit.palomar-registry.org/>.
