module

public import Mathlib

@[expose] public section

/-! ### From `Rigidity/Ensemble/Basic.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Index pairs `(i, j)` with `i ≤ j`: the independent entries of an `N × N` hermitian matrix. -/
abbrev Pair (N : ℕ) := {p : Fin N × Fin N // p.1 ≤ p.2}

/-- The pair `(min i j, max i j)`. -/
def Pair.mk' {N : ℕ} (i j : Fin N) : Pair N :=
  if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), (not_le.mp h).le⟩

theorem Pair.mk'_comm {N : ℕ} (i j : Fin N) : Pair.mk' i j = Pair.mk' j i := by
  unfold Pair.mk'
  by_cases h₁ : i ≤ j <;> by_cases h₂ : j ≤ i
  · have : i = j := le_antisymm h₁ h₂
    subst this; rfl
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · exact absurd (le_total i j) (by tauto)

/-- The hermitian matrix with upper-triangular entries `x`: `h_ij = x_ij` for `i < j`,
`h_ji = conj h_ij`, and real diagonal `h_ii = re x_ii`. -/
def toMatrix {N : ℕ} (x : Pair N → 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j =>
    if i < j then x (Pair.mk' i j)
    else if j < i then star (x (Pair.mk' i j))
    else ((RCLike.re (x (Pair.mk' i j)) : ℝ) : 𝕜)

theorem toMatrix_isHermitian {N : ℕ} (x : Pair N → 𝕜) : (toMatrix x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, toMatrix, Matrix.of_apply]
  rw [Pair.mk'_comm j i]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · simp
  · simp [h, not_lt_of_gt h]

/-- One `N × N` ensemble: a probability law for each entry `h_ij`, `i ≤ j`. -/
structure Ensemble (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) where
  law : Pair N → Measure 𝕜
  isProb : ∀ p, IsProbabilityMeasure (law p)

attribute [instance] Ensemble.isProb

namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- The joint law of the entries: the product of the entry laws. -/
noncomputable def prodLaw : Measure (Pair N → 𝕜) := Measure.pi M.law

theorem prodLaw_isProbabilityMeasure : IsProbabilityMeasure M.prodLaw := by
  unfold prodLaw; infer_instance

attribute [instance] prodLaw_isProbabilityMeasure

/-- `σ_p² = 𝔼|h_p|²` (2.1). -/
noncomputable def varPair (p : Pair N) : ℝ := ∫ y, ‖y‖ ^ 2 ∂M.law p

/-- `σ_ij²` for all `i, j`, with `σ_ji = σ_ij`. -/
noncomputable def var (i j : Fin N) : ℝ := M.varPair (Pair.mk' i j)

/-- The matrix of variances `B = (σ_ij²)`. -/
noncomputable def varMatrix : Matrix (Fin N) (Fin N) ℝ := Matrix.of M.var

/-- Mean zero (2.1). -/
def MeanZero : Prop := ∀ p, ∫ y, y ∂M.law p = 0

/-- The diagonal entries are real. -/
def DiagReal : Prop := ∀ i : Fin N, ∀ᵐ y ∂M.law (Pair.mk' i i), RCLike.im y = 0

/-- Assumption (A) (2.2). -/
def AssumptionA : Prop := ∀ j, ∑ i, M.var i j = 1

/-- Assumption (B) as the quadratic-form bound on `𝐞^⊥`. -/
def AssumptionB (δm δp : ℝ) : Prop :=
  ∀ v : Fin N → ℝ, ∑ i, v i = 0 →
    (-1 + δm) * ∑ i, v i ^ 2 ≤ v ⬝ᵥ (M.varMatrix *ᵥ v) ∧
      v ⬝ᵥ (M.varMatrix *ᵥ v) ≤ (1 - δp) * ∑ i, v i ^ 2

/-- Assumption (C) (2.4). -/
def AssumptionC (C₀ : ℝ) : Prop := ∀ i j, M.var i j ≤ C₀ / N

/-- Uniform subexponential decay (2.17). -/
def SubexpDecay (ϑ : ℝ) : Prop :=
  ∀ p, ∀ x : ℝ, 1 ≤ x →
    M.law p {y | x * Real.sqrt (M.varPair p) < ‖y‖} ≤ ENNReal.ofReal (ϑ⁻¹ * Real.exp (-(x ^ ϑ)))

/-- The hypotheses of Theorems 2.1 and 2.2: (2.1), real diagonal, (A), (B), (C), (2.17). -/
structure Assumptions (ϑ δm δp C₀ : ℝ) : Prop where
  meanZero : M.MeanZero
  diagReal : M.DiagReal
  sumA : M.AssumptionA
  specB : M.AssumptionB δm δp
  boundC : M.AssumptionC C₀
  subexp : M.SubexpDecay ϑ

/-- The moment-matching condition (2.40) for `l + u ≤ 2`, on the laws of `h_ij`. -/
def MomentMatch2 (Mv Mw : Ensemble 𝕜 N) : Prop :=
  ∀ p, ∀ l u : ℕ, l + u ≤ 2 →
    ∫ y, star y ^ l * y ^ u ∂Mv.law p = ∫ y, star y ^ l * y ^ u ∂Mw.law p

end Ensemble

end Rigidity

end

/-! ### From `Rigidity/Spectrum/Eigenvalues.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The eigenvalues of a hermitian matrix in increasing order, `k = 0, …, N - 1`; the
`λ_j` of §2 is `eigAsc hA ⟨j - 1, _⟩`. -/
noncomputable def eigAsc {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (k : Fin N) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm k.rev)

/-- The ordered eigenvalues `λ_0 ≤ … ≤ λ_{N-1}` of `H` as functions of the entries. -/
noncomputable def eig {N : ℕ} (x : Pair N → 𝕜) (k : Fin N) : ℝ :=
  eigAsc (toMatrix_isHermitian x) k

/-- The largest eigenvalue `λ_N`. -/
noncomputable def lamMax {N : ℕ} (x : Pair N → 𝕜) : ℝ :=
  if h : 0 < N then eig x ⟨N - 1, Nat.sub_lt h Nat.one_pos⟩ else 0

/-- The smallest eigenvalue `λ_1`. -/
noncomputable def lamMin {N : ℕ} (x : Pair N → 𝕜) : ℝ :=
  if h : 0 < N then eig x ⟨0, h⟩ else 0

/-- The weight `min(j, N - j + 1)` of (2.25) at `j = k + 1`. -/
def rigWeight (N : ℕ) (k : Fin N) : ℕ := min (k.val + 1) (N - k.val)

end Rigidity

end

/-! ### From `Rigidity/Resolvent/Basic.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The coordinate map `𝕜 → ℂ`, `y ↦ re y + i im y`. -/
def toC (y : 𝕜) : ℂ := ⟨RCLike.re y, RCLike.im y⟩

/-- The Green function `G(z) = (H - z)⁻¹` (2.8). -/
noncomputable def green {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (z : ℂ) :
    Matrix n n ℂ :=
  (A.map toC - z • (1 : Matrix n n ℂ))⁻¹

/-- `m(z) = N⁻¹ tr G(z)` (2.9). -/
noncomputable def stieltjesEmp {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜)
    (z : ℂ) : ℂ :=
  ((Fintype.card n : ℂ))⁻¹ * (green A z).trace

end Rigidity

end

/-! ### From `Rigidity/Semicircle/Basic.lean` -/

section

open MeasureTheory Real

open scoped ENNReal

namespace Rigidity

/-- `m_sc(z) = (-z + √(z-2) √(z+2)) / 2` with principal square roots: the branch of (2.13)
with cut `[-2, 2]`. -/
noncomputable def msc (z : ℂ) : ℂ := (-z + Complex.sqrt (z - 2) * Complex.sqrt (z + 2)) / 2

end Rigidity

end

/-! ### From `Rigidity/Semicircle/Stieltjes.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- The semicircle density (2.14). -/
noncomputable def rhoSc (E : ℝ) : ℝ := (2 * π)⁻¹ * Real.sqrt (max (4 - E ^ 2) 0)

end Rigidity

end

/-! ### From `Rigidity/Semicircle/Density.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- `n_sc(E) = ∫_{-∞}^E ϱ_sc` (2.24). -/
noncomputable def nsc (E : ℝ) : ℝ := ∫ x in Set.Iic E, rhoSc x

/-- The classical location `γ_{k+1}` (1.3): the least `x` with `N n_sc(x) ≥ k + 1`;
`γ_N = 2`. -/
noncomputable def gamma (N : ℕ) (k : Fin N) : ℝ := sInf {x : ℝ | (k.val + 1 : ℝ) ≤ N * nsc x}

end Rigidity

end

/-! ### From `Rigidity/LocalLaw/Defs.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- The normalised counting function `𝔫(E)` (2.23). -/
noncomputable def countFn {N : ℕ} (x : Pair N → 𝕜) (E : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ((Finset.univ.filter fun k => eig x k ≤ E).card : ℝ)

/-- `Λ = |m - m_sc|` (2.16). -/
noncomputable def Lam {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  ‖stieltjesEmp (toMatrix x) z - msc z‖

/-- `Λ_d = max_k |G_kk - m_sc|` (2.16). -/
noncomputable def LamD {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  ⨆ k : Fin N, ‖green (toMatrix x) z k k - msc z‖

/-- `Λ_o = max_{k ≠ l} |G_kl|` (2.16). -/
noncomputable def LamO {N : ℕ} (x : Pair N → 𝕜) (z : ℂ) : ℝ :=
  ⨆ q : {q : Fin N × Fin N // q.1 ≠ q.2}, ‖green (toMatrix x) z q.1.1 q.1.2‖

/-- The spectral domain `S_L` (2.20). -/
def SL (N : ℕ) (L : ℝ) : Set ℂ :=
  {z | |z.re| ≤ 5 ∧ (N : ℝ)⁻¹ * Real.log N ^ (10 * L) < z.im ∧ z.im ≤ 10}

/-- The range (2.18) of `L`. -/
def LRange (A₀ : ℝ) (N : ℕ) (L : ℝ) : Prop :=
  A₀ * Real.log (Real.log N) ≤ L ∧ L ≤ Real.log (10 * N) / (10 * Real.log (Real.log N))

end Rigidity

end

/-! ### From `Rigidity/Flow/Gaussian.lean` -/

section

open MeasureTheory Real

open scoped ENNReal NNReal

namespace Rigidity

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Definition 14.A: the centred Gaussian measure `g_v` on `E` with covariance `v · Id`
(the image of `stdGaussian E` under `z ↦ √v z`; `g_0 = δ_0`). -/
noncomputable def gaussE (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] (v : ℝ) : Measure E :=
  (ProbabilityTheory.stdGaussian E).map fun z => Real.sqrt v • z

end Gaussian

end Rigidity

end

/-! ### From `Rigidity/Flow/Herm.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `β = dim_ℝ 𝕜` (§12.1). -/
noncomputable def betaF (𝕜 : Type*) [RCLike 𝕜] : ℝ := Module.finrank ℝ 𝕜

/-- Real coordinates of a matrix: `(i, j, 0) ↦ Re h_ij`, `(i, j, 1) ↦ Im h_ij`. -/
abbrev HCoord (N : ℕ) := EuclideanSpace ℝ (Fin N × Fin N × Fin 2)

/-- The set of coordinate vectors of the self-adjoint matrices is closed under addition. -/
theorem hermSub_add_mem (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) {v w : HCoord N}
    (hv : v ∈ ({v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)} : Set (HCoord N)))
    (hw : w ∈ ({v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)} : Set (HCoord N))) :
    v + w ∈ ({v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)} : Set (HCoord N)) := by
  intro i j
  obtain ⟨h1, h2, h3⟩ := hv i j
  obtain ⟨h1', h2', h3'⟩ := hw i j
  refine ⟨by simp [h1, h1'], by simp [h2, h2']; ring, fun hI => by simp [h3 hI, h3' hI]⟩

/-- The set of coordinate vectors of the self-adjoint matrices contains `0`. -/
theorem hermSub_zero_mem (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) :
    (0 : HCoord N) ∈ ({v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)} : Set (HCoord N)) := by
  intro i j; simp

/-- The set of coordinate vectors of the self-adjoint matrices is closed under real multiples. -/
theorem hermSub_smul_mem (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) (c : ℝ) {v : HCoord N}
    (hv : v ∈ ({v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)} : Set (HCoord N))) :
    c • v ∈ ({v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)} : Set (HCoord N)) := by
  intro i j
  obtain ⟨h1, h2, h3⟩ := hv i j
  exact ⟨by simp [h1], by simp [h2], fun hI => by simp [h3 hI]⟩

/-- The coordinate vectors of the self-adjoint matrices over `𝕜`. -/
def hermSub (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Submodule ℝ (HCoord N) where
  carrier := {v | ∀ i j, v (j, i, 0) = v (i, j, 0) ∧ v (j, i, 1) = -v (i, j, 1) ∧
      (RCLike.I (K := 𝕜) = 0 → v (i, j, 1) = 0)}
  add_mem' := fun hv hw => hermSub_add_mem 𝕜 N hv hw
  zero_mem' := hermSub_zero_mem 𝕜 N
  smul_mem' := fun c _ hv => hermSub_smul_mem 𝕜 N c hv

/-- `𝓗_N(𝕜)` (§12.1): the real inner product space of self-adjoint `N × N` matrices over `𝕜`
with `⟨X, Y⟩ = Tr(XY)` and `|X|² = ∑_{i,j} |x_ij|²`. -/
def Herm (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Type := hermSub 𝕜 N

namespace Herm

variable {N : ℕ}

noncomputable instance : NormedAddCommGroup (Herm 𝕜 N) :=
  inferInstanceAs (NormedAddCommGroup (hermSub 𝕜 N))

noncomputable instance : InnerProductSpace ℝ (Herm 𝕜 N) :=
  inferInstanceAs (InnerProductSpace ℝ (hermSub 𝕜 N))

theorem instFiniteDimensionalReal : FiniteDimensional ℝ (Herm 𝕜 N) :=
  (inferInstance : FiniteDimensional ℝ (hermSub 𝕜 N))

attribute [instance] instFiniteDimensionalReal

noncomputable instance : MeasurableSpace (Herm 𝕜 N) := borel _

theorem instBorelSpace : BorelSpace (Herm 𝕜 N) := ⟨rfl⟩

attribute [instance] instBorelSpace

/-- The real coordinates of `H`. -/
def coord (H : Herm 𝕜 N) (q : Fin N × Fin N × Fin 2) : ℝ := (H : hermSub 𝕜 N).1 q

/-- The upper-triangular entries `h_ij = Re h_ij + i Im h_ij`, `i ≤ j`. -/
def toPair (H : Herm 𝕜 N) : Pair N → 𝕜 := fun p =>
  ((H.coord (p.1.1, p.1.2, 0) : ℝ) : 𝕜) + ((H.coord (p.1.1, p.1.2, 1) : ℝ) : 𝕜) * RCLike.I

/-- The matrix of `H`. -/
def toMatrix (H : Herm 𝕜 N) : Matrix (Fin N) (Fin N) 𝕜 := Rigidity.toMatrix H.toPair

/-- The coordinate vector of `H(x)` is a coordinate vector of a self-adjoint matrix. -/
theorem ofPair_mem (x : Pair N → 𝕜) :
    ((WithLp.toLp 2 fun q => if q.2.2 = 0 then RCLike.re (Rigidity.toMatrix x q.1 q.2.1)
      else RCLike.im (Rigidity.toMatrix x q.1 q.2.1)) : HCoord N) ∈ hermSub 𝕜 N := by
  intro i j
  have h : Rigidity.toMatrix x j i = star (Rigidity.toMatrix x i j) := by
    have := congrFun (congrFun (toMatrix_isHermitian x) j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  exact ⟨by simp [h, RCLike.star_def], by simp [h, RCLike.star_def], fun hI => by
    simp [RCLike.im_eq_zero hI]⟩

/-- `H(x)` (Definition 2.1) as an element of `𝓗`. -/
noncomputable def ofPair (x : Pair N → 𝕜) : Herm 𝕜 N :=
  ⟨WithLp.toLp 2 fun q => if q.2.2 = 0 then RCLike.re (Rigidity.toMatrix x q.1 q.2.1)
      else RCLike.im (Rigidity.toMatrix x q.1 q.2.1), ofPair_mem x⟩

theorem isHermitian (H : Herm 𝕜 N) : H.toMatrix.IsHermitian := toMatrix_isHermitian _

end Herm

/-- `λ(H)`: the ordered eigenvalues of `H ∈ 𝓗` (§12.1). -/
noncomputable def eigVec {N : ℕ} (H : Herm 𝕜 N) : Fin N → ℝ := fun k => eigAsc H.isHermitian k

section Entries

variable {N : ℕ}

end Entries

section Spectral

variable {N : ℕ}

end Spectral

section Dimension

variable {N : ℕ}

end Dimension

section EigVec

variable {N : ℕ}

end EigVec

end Rigidity

end

/-! ### From `Rigidity/Flow/GaussEnsemble.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- `σ² = 2/(βN)` (§12.1). -/
noncomputable def gaussVar (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : ℝ := 2 / (betaF 𝕜 * N)

/-- `𝐆 = 𝐆_{N,β}`, the centred Gaussian measure on `𝓗` with covariance `σ² Id` (§12.1). -/
noncomputable def gaussH (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Measure (Herm 𝕜 N) :=
  gaussE (Herm 𝕜 N) (gaussVar 𝕜 N)

/-- `μ = λ_* 𝐆` (§12.1). -/
noncomputable def gbeLaw (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) : Measure (Fin N → ℝ) :=
  (gaussH 𝕜 N).map eigVec

namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- The law of `H_0 = H(x)`, `x ∼ ℙ_ν`, on `𝓗`. -/
noncomputable def hermLaw : Measure (Herm 𝕜 N) := M.prodLaw.map Herm.ofPair

end Ensemble

section Elementary

variable {N : ℕ}

end Elementary

section Conj

variable {N : ℕ}

end Conj

section CharFun

variable {N : ℕ}

end CharFun

section Variance

end Variance

end Rigidity

end

/-! ### From `Rigidity/Flow/Mehler.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
section Mehler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `a_u = e^{-u/2}` (§14.3). -/
noncomputable def ouA (u : ℝ) : ℝ := Real.exp (-u / 2)

/-- `s_u = 1 - e^{-u}` (§14.3). -/
noncomputable def ouS (u : ℝ) : ℝ := 1 - Real.exp (-u)

/-- `ρ_u = law(a_u Y + s_u^{1/2} Z)`, `Y ∼ ρ`, `Z ∼ g_v` independent (§14.3). -/
noncomputable def ouLaw (v : ℝ) (ρ : Measure E) (u : ℝ) : Measure E :=
  (ρ.prod (gaussE E v)).map fun p => ouA u • p.1 + Real.sqrt (ouS u) • p.2

end Mehler

end Rigidity

end

/-! ### From `Rigidity/Flow/Invariant.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- The law of `λ(H_t)` for `H_0 ∼ ρ` (§12.1): `ν_t = λ_* ρ_t`. -/
noncomputable def eigFlow {N : ℕ} (ρ : Measure (Herm 𝕜 N)) (t : ℝ) : Measure (Fin N → ℝ) :=
  (ouLaw (gaussVar 𝕜 N) ρ t).map eigVec

section Conj

variable {N : ℕ}

end Conj

section Derivatives

variable {N : ℕ}

end Derivatives

end Rigidity

end

/-! ### From `Rigidity/Flow/Ensembles.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
namespace Ensemble

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `ν_t`, the law of `λ(H_t)` (§12.1). -/
noncomputable def eigLaw (t : ℝ) : Measure (Fin N → ℝ) := eigFlow M.hermLaw t

end Ensemble

section Entries

variable {N : ℕ}

end Entries

section Moments

variable {N : ℕ}

end Moments

end Rigidity

end

/-! ### From `Rigidity/Flow/Correlation.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- `𝒳^O_{E',ϱ}(x) = ∑_{i_1, …, i_n distinct} O(Nϱ(x_{i_1} - E'), …, Nϱ(x_{i_n} - E'))` (12.2). -/
noncomputable def corrX {N n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (E' ϱ : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin n ↪ Fin N, O (WithLp.toLp 2 fun k => N * ϱ * (x (i k) - E'))

/-- `C_{N,n} = N^n (N - n)!/N!` (12.2). -/
noncomputable def corrC (N n : ℕ) : ℝ := (N : ℝ) ^ n * (N - n).factorial / N.factorial

/-- The left side of (2.36) (NP (12.3)), with `ϱ = ϱ_sc(E)`. -/
noncomputable def corrLHS {N n : ℕ} (M : Ensemble 𝕜 N) (O : EuclideanSpace ℝ (Fin n) → ℝ)
    (E b t : ℝ) : ℝ :=
  |∫ E' in (E - b)..(E + b), (2 * b)⁻¹ * corrC N n *
      ((∫ x, corrX O E' (rhoSc E) x ∂M.eigLaw t) - ∫ x, corrX O E' (rhoSc E) x ∂gbeLaw 𝕜 N)|

end Rigidity

end

/-! ### From `Rigidity/Flow/Endpoint.lean` -/

section

open MeasureTheory Real Matrix Filter Topology

open scoped ENNReal Matrix.Norms.L2Operator

open scoped NNReal

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]
/-- The bound (2.36) for one field and one constant `C`. -/
def ErgodicityBound (𝕜 : Type*) [RCLike 𝕜] (ϑ δm δp C₀ ε' δ c : ℝ) (n : ℕ) (ρO C : ℝ) : Prop :=
  ∀ N : ℕ, max n 3 ≤ N → ∀ M : Ensemble 𝕜 N, M.Assumptions ϑ δm δp C₀ →
    ∀ O : EuclideanSpace ℝ (Fin n) → ℝ, ∀ Bd : ℝ, ∀ K : ℝ≥0, (∀ u, |O u| ≤ Bd) →
      LipschitzWith K O → (∀ u, (∃ k, ρO < |u k|) → O u = 0) →
    ∀ E ∈ Set.Icc (-2 + c) (2 - c), ∀ b : ℝ, 0 < b → b < c / 2 →
    ∀ t : ℝ, (N : ℝ) ^ (-1 + δ + ε') ≤ t →
      corrLHS M O E b t ≤ C * (Bd + K) * (N : ℝ) ^ (2 * ε') *
        (b⁻¹ * (N : ℝ) ^ (-1 + ε') + b ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-δ / 2))

end Rigidity

end

