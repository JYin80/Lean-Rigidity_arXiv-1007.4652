module

public import Rigidity.Ensemble.Basic
public import Rigidity.Flow.Ensembles
public import Rigidity.Flow.GaussEnsemble
public import Rigidity.Flow.GoodSet
public import Rigidity.LogGas.GapConc
public import Rigidity.Semicircle.Stieltjes
public import Rigidity.MainDefs

@[expose] public section

/-!
# Correlation functionals and their reduction to gap observables

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …]. Indices are 0-based.

The file defines the correlation functional `𝒳^O_{E',ϱ}` and the constant `C_{N,n}` of (12.2), the
left side `corrLHS` of (12.3), and the objects of §19.2: the symmetrisation `O^s`, the index tuples
`𝔖_n`, `Y_{i,m}`, `G_ϱ` and `F_m`. It proves:
* `corrX_eq_sum_corrY`: Lemma 19.2 (a), `𝒳 = n! ∑_i ∑_m Y_{i,m}`;
* `corrY_support`, `integral_corrY`: Lemma 19.2 (b), the support and the integral of `Y_{i,m}`;
* `corrG_gapHyp`, `sqrt_cStar_le`, `corrF_eq_gapObs`: Lemma 19.2 (c), (d), `G_ϱ` satisfies the
  hypotheses of Theorem 17.7 and `F_m` is a gap observable (17.4);
* `corrY_eq_zero_of_mem_flowGoodSet`, `abs_integral_corrX_sub_le`: Lemma 19.3, localisation on the
  good set `Ξ` (13.3) and the reduction of `∫ 𝒳 dE'` to the observables `F_m`;
* `card_indexTuples_le`, `abs_corrX_le_of_mem_flowGoodSet`, `abs_corrX_le`: the counting bound of
  Lemma 19.3 (b) and the trivial bounds on `𝒳` of Lemmas 19.3 (a) and 19.2 (d).

Here `O` is bounded by `B`, `K`-Lipschitz for the Euclidean norm and vanishes outside
`[-ρ_O, ρ_O]ⁿ`; `ϱ > 0` and `ℓ` satisfy `ρ_O ≤ ℓ ϱ` (in the paper `ℓ = max(1, ρ_O/ϱ_*)` and
`ϱ = ϱ_sc(E) ≥ ϱ_*`). For `G_ϱ` as a function on `ℝ^{n-1}` the index `n` is written `r + 1`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


/-- The symmetrisation `O^s` (§19.2). -/
noncomputable def symmetrize {n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ)
    (α : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (n.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), O (WithLp.toLp 2 fun k => α (σ k))

/-- An index tuple `0 = m_1 < m_2 < ⋯ < m_n` of `𝔖_n` (§19.2), 0-based in `k`. -/
def IsIndexTuple {n : ℕ} (m : Fin n → ℕ) : Prop := StrictMono m ∧ ∀ h : 0 < n, m ⟨0, h⟩ = 0

/-- `m_n` (and `0` for `n = 0`). -/
def lastIdx {n : ℕ} (m : Fin n → ℕ) : ℕ := if h : 0 < n then m ⟨n - 1, by omega⟩ else 0

/-- `Y_{i,m}(E', x)` (§19.2), 0-based `i`. -/
noncomputable def corrY {N n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (ϱ E' : ℝ)
    (m : Fin n → ℕ) (i : ℕ) (x : Fin N → ℝ) : ℝ :=
  if i + lastIdx m < N then
    symmetrize O (WithLp.toLp 2 fun k => N * ϱ * (extVec x (i + m k) - E'))
  else 0

/-- `G_ϱ(u) = ∫ O^s(ϱy, ϱ(y + u_2), …, ϱ(y + u_n)) dy` (§19.2), with `u_1 := 0` implicit
through `m_1 = 0`: the argument is `u : Fin n → ℝ` and the `k = 0` coordinate is not used. -/
noncomputable def corrG {n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (ϱ : ℝ) (u : Fin n → ℝ) :
    ℝ :=
  ∫ y, symmetrize O (WithLp.toLp 2 fun k => ϱ * (y + if k.val = 0 then 0 else u k))

/-- `F_m(x) = N⁻¹ ∑_{i ∈ J, i + m_n < N} G_ϱ(N(x_{i+m_k} - x_i))_k` (§19.2). -/
noncomputable def corrF {N n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (ϱ : ℝ) (J : Finset ℕ)
    (m : Fin n → ℕ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ J.filter (fun i => i + lastIdx m < N),
    corrG O ϱ fun k => N * (extVec x (i + m k) - extVec x i)

/-! ### Lemma 19.2 (a) -/

/-- Sum over embeddings, split into increasing tuples and permutations. -/
private theorem corr_sum_embedding {N n : ℕ} (Φ : (Fin n → Fin N) → ℝ) :
    ∑ f : Fin n ↪ Fin N, Φ f =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n → Fin N => StrictMono j),
        ∑ σ : Equiv.Perm (Fin n), Φ (j ∘ σ) := by
  classical
  rw [← Finset.sum_product']
  refine (Finset.sum_bij (fun p hp => (⟨p.1 ∘ p.2, ?_⟩ : Fin n ↪ Fin N)) ?_ ?_ ?_ ?_).symm
  · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp.1.injective.comp p.2.injective
  · intro p hp; exact Finset.mem_univ _
  · rintro ⟨j, σ⟩ hp ⟨j', σ'⟩ hq h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have h' : j ∘ σ = j' ∘ σ' := congrArg (fun f : Fin n ↪ Fin N => (f : Fin n → Fin N)) h
    have e1 : (j ∘ σ) ∘ ⇑σ.symm = j := by ext k; simp
    have e2 : (j ∘ σ) ∘ ⇑σ'.symm = j' := by rw [h']; ext k; simp
    have hm1 : Monotone ((j ∘ σ) ∘ ⇑σ.symm) := by rw [e1]; exact hp.monotone
    have hm2 : Monotone ((j ∘ σ) ∘ ⇑σ'.symm) := by rw [e2]; exact hq.monotone
    have h1 : j = j' := by
      have := Tuple.unique_monotone hm1 hm2
      rwa [e1, e2] at this
    subst h1
    refine Prod.ext rfl ?_
    ext k
    exact congrArg Fin.val (hp.injective (congrFun h' k))
  · intro f _
    set σ := Tuple.sort (f : Fin n → Fin N) with hσ
    have hmono : Monotone ((f : Fin n → Fin N) ∘ σ) := Tuple.monotone_sort _
    have hsm : StrictMono ((f : Fin n → Fin N) ∘ σ) :=
      hmono.strictMono_of_injective (f.injective.comp σ.injective)
    refine ⟨(((f : Fin n → Fin N) ∘ σ), σ.symm), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact hsm
    · ext k; simp
  · intro p hp; rfl

private theorem corr_lastIdx_eq {n : ℕ} (hn : 0 < n) (m : Fin n → ℕ) :
    lastIdx m = m ⟨n - 1, by omega⟩ := by
  simp [lastIdx, hn]

private theorem corr_le_lastIdx {n : ℕ} {m : Fin n → ℕ} (hm : Monotone m) (k : Fin n) :
    m k ≤ lastIdx m := by
  have hn : 0 < n := k.pos
  rw [corr_lastIdx_eq hn]
  exact hm (by simp [Fin.le_def]; omega)

open Classical in
/-- Increasing tuples of `Fin N` correspond to pairs `(i, m)` of a first index and an index
tuple with `i + m_n < N`. -/
private theorem corr_sum_increasing {N n : ℕ} (hn : 0 < n) (h : ℕ → ℝ) (S : (Fin n → ℝ) → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin n → Fin N => StrictMono j), S (fun k => h (j k)) =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ.filter
          (fun m : Fin n → Fin N => IsIndexTuple fun k => (m k : ℕ))).filter
        (fun p : Fin N × (Fin n → Fin N) => p.1.val + lastIdx (fun k => (p.2 k : ℕ)) < N),
        S (fun k => h (p.1 + p.2 k)) := by
  classical
  have h0 : (⟨0, hn⟩ : Fin n) ≤ ⟨0, hn⟩ := le_rfl
  refine Finset.sum_bij
    (fun j hj => ((j ⟨0, hn⟩, fun k => ⟨(j k : ℕ) - (j ⟨0, hn⟩ : ℕ),
      lt_of_le_of_lt (Nat.sub_le _ _) (j k).isLt⟩) : Fin N × (Fin n → Fin N))) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hmono : ∀ k : Fin n, (j ⟨0, hn⟩ : ℕ) ≤ j k := fun k =>
      Fin.le_def.mp (hj.monotone (Fin.mk_le_of_le_val (Nat.zero_le _)))
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    have hI : IsIndexTuple fun k : Fin n => (((j k : ℕ) - (j ⟨0, hn⟩ : ℕ) : ℕ)) := by
      refine ⟨fun a b hab => ?_, fun _ => by simp⟩
      have := hj hab
      have h1 := hmono a
      simp only [Fin.lt_def] at this
      change (j a : ℕ) - (j ⟨0, hn⟩ : ℕ) < (j b : ℕ) - (j ⟨0, hn⟩ : ℕ)
      omega
    refine ⟨hI, ?_⟩
    have hmo : Monotone fun k : Fin n => (((j k : ℕ) - (j ⟨0, hn⟩ : ℕ) : ℕ)) := hI.1.monotone
    rw [corr_lastIdx_eq hn _]
    have h2 := hmono ⟨n - 1, by omega⟩
    have h3 := (j ⟨n - 1, by omega⟩).isLt
    change (j ⟨0, hn⟩ : ℕ) + ((j ⟨n - 1, by omega⟩ : ℕ) - (j ⟨0, hn⟩ : ℕ)) < N
    omega
  · intro a ha b hb hab
    have hmono : ∀ (j : Fin n → Fin N), StrictMono j → ∀ k : Fin n, (j ⟨0, hn⟩ : ℕ) ≤ j k :=
      fun j hj k => Fin.le_def.mp (hj.monotone (Fin.mk_le_of_le_val (Nat.zero_le _)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    simp only [Prod.mk.injEq] at hab
    obtain ⟨hab1, hab2⟩ := hab
    funext k
    have h3 := congrFun hab2 k
    simp only [Fin.mk.injEq] at h3
    have h4 := hmono a ha k
    have h5 := hmono b hb k
    have h6 := congrArg Fin.val hab1
    apply Fin.ext
    omega
  · rintro ⟨i, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    obtain ⟨hI, hlt⟩ := hp
    have hle : ∀ k, (m k : ℕ) ≤ lastIdx fun k => (m k : ℕ) := fun k =>
      corr_le_lastIdx (m := fun k => (m k : ℕ)) hI.1.monotone k
    have hm0 : (m ⟨0, hn⟩ : ℕ) = 0 := hI.2 hn
    refine ⟨fun k => ⟨(i : ℕ) + m k, by have := hle k; omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro a b hab
      have : (m a : ℕ) < m b := hI.1 hab
      simp only [Fin.lt_def]
      change (i : ℕ) + m a < (i : ℕ) + m b
      omega
    · refine Prod.ext (Fin.ext ?_) ?_
      · change (i : ℕ) + m ⟨0, hn⟩ = i
        omega
      · funext k
        apply Fin.ext
        change (i : ℕ) + m k - ((i : ℕ) + m ⟨0, hn⟩) = m k
        omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hmono : ∀ k : Fin n, (j ⟨0, hn⟩ : ℕ) ≤ j k := fun k =>
      Fin.le_def.mp (hj.monotone (Fin.mk_le_of_le_val (Nat.zero_le _)))
    congr 2
    funext k
    have := hmono k
    change h (j k) = h ((j ⟨0, hn⟩ : ℕ) + ((j k : ℕ) - (j ⟨0, hn⟩ : ℕ)))
    congr 1
    omega

private theorem corr_extVec_of_lt {N : ℕ} (x : Fin N → ℝ) {j : ℕ} (h : j < N) :
    extVec x j = x ⟨j, h⟩ := by
  simp [extVec, h]

private theorem corr_extVec_val {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : extVec x i = x i :=
  corr_extVec_of_lt x i.isLt

open Classical in
/-- Lemma 19.2 (a): `𝒳 = n! ∑_i ∑_m Y_{i,m}` on the closed chamber. -/
theorem corrX_eq_sum_corrY {N n : ℕ} (hn : 0 < n) (O : EuclideanSpace ℝ (Fin n) → ℝ) (E' ϱ : ℝ)
    {x : Fin N → ℝ} (hx : Monotone x) :
    corrX O E' ϱ x = n.factorial * ∑ i : Fin N,
      ∑ m ∈ (Finset.univ.filter fun m : Fin n → Fin N => IsIndexTuple fun k => (m k : ℕ)),
        corrY O ϱ E' (fun k => (m k : ℕ)) i x := by
  have _ := hx
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  set h : ℕ → ℝ := fun t => N * ϱ * (extVec x t - E') with hh
  set S : (Fin n → ℝ) → ℝ := fun α => symmetrize O (WithLp.toLp 2 α) with hS
  have step1 : corrX O E' ϱ x =
      n.factorial * ∑ j ∈ Finset.univ.filter (fun j : Fin n → Fin N => StrictMono j),
        S (fun k => h (j k)) := by
    unfold corrX
    rw [corr_sum_embedding (fun f => O (WithLp.toLp 2 fun k => N * ϱ * (x (f k) - E'))),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hS, symmetrize]
    rw [mul_inv_cancel_left₀ hfac]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    ext k
    simp [hh, corr_extVec_val]
  rw [step1, corr_sum_increasing hn h S, ← Finset.sum_product']
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [corrY, hS, hh]

/-! ### The symmetrisation -/

private theorem corr_norm_toLp_perm {n : ℕ} (v : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    ‖(WithLp.toLp 2 fun k => v (σ k) : EuclideanSpace ℝ (Fin n))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp σ fun k => ‖v k‖ ^ 2

private theorem corr_continuous_symmetrize {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ}
    (hO : Continuous O) : Continuous (symmetrize O) := by
  unfold symmetrize
  refine continuous_const.mul (continuous_multiset_sum _ fun σ _ => hO.comp ?_)
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun k => (continuous_apply (σ k)).comp (PiLp.continuous_ofLp 2 _))

private theorem corr_abs_symmetrize_le {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hB : ∀ α, |O α| ≤ B) (α : EuclideanSpace ℝ (Fin n)) : |symmetrize O α| ≤ B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  unfold symmetrize
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹)]
  have h1 : |∑ σ : Equiv.Perm (Fin n), O (WithLp.toLp 2 fun k => α (σ k))| ≤
      ∑ σ : Equiv.Perm (Fin n), B :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => hB _)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at h1
  have hf : (0 : ℝ) < n.factorial := by positivity
  calc (n.factorial : ℝ)⁻¹ * |∑ σ : Equiv.Perm (Fin n), O (WithLp.toLp 2 fun k => α (σ k))|
      ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * B) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := by field_simp

private theorem corr_symmetrize_eq_zero {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO : ℝ}
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0)
    {α : EuclideanSpace ℝ (Fin n)} (h : ∃ k, ρO < |α k|) : symmetrize O α = 0 := by
  obtain ⟨k, hk⟩ := h
  unfold symmetrize
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ _
  apply hsupp
  exact ⟨σ.symm k, by simpa using hk⟩

private theorem corr_abs_symmetrize_sub_le {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
    (hLip : ∀ α β, |O α - O β| ≤ K * ‖α - β‖) (α β : EuclideanSpace ℝ (Fin n)) :
    |symmetrize O α - symmetrize O β| ≤ K * ‖α - β‖ := by
  unfold symmetrize
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ)⁻¹),
    ← Finset.sum_sub_distrib]
  have h1 : |∑ σ : Equiv.Perm (Fin n), (O (WithLp.toLp 2 fun k => α (σ k)) -
      O (WithLp.toLp 2 fun k => β (σ k)))| ≤ ∑ σ : Equiv.Perm (Fin n), K * ‖α - β‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    refine (hLip _ _).trans (le_of_eq ?_)
    have e1 : (WithLp.toLp 2 fun k => α (σ k) : EuclideanSpace ℝ (Fin n)) -
        (WithLp.toLp 2 fun k => β (σ k)) = WithLp.toLp 2 fun k => (α - β).ofLp (σ k) := by
      ext k; simp
    rw [e1, corr_norm_toLp_perm (α - β).ofLp σ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at h1
  have hf : (0 : ℝ) < n.factorial := by positivity
  calc (n.factorial : ℝ)⁻¹ * |∑ σ : Equiv.Perm (Fin n), (O (WithLp.toLp 2 fun k => α (σ k)) -
      O (WithLp.toLp 2 fun k => β (σ k)))|
      ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * (K * ‖α - β‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * ‖α - β‖ := by field_simp

/-! ### The functions `G_ϱ` -/

/-- The integrand of `corrG`. -/
private noncomputable def corrGInt {n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (ϱ : ℝ)
    (u : Fin n → ℝ) (y : ℝ) : ℝ :=
  symmetrize O (WithLp.toLp 2 fun k => ϱ * (y + if k.val = 0 then 0 else u k))

private theorem corr_continuous_of_lip {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hLip : ∀ α β, |O α - O β| ≤ K * ‖α - β‖) : Continuous O := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨K, hK⟩) fun α β => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact hLip α β

private theorem corrGInt_continuous {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} (ϱ : ℝ)
    (hO : Continuous O) : Continuous (Function.uncurry fun (u : Fin n → ℝ) (y : ℝ) =>
      corrGInt O ϱ u y) := by
  unfold corrGInt
  refine (corr_continuous_symmetrize hO).comp ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => ?_)
  by_cases hk : k.val = 0
  · simp only [hk, ↓reduceIte, add_zero]
    fun_prop
  · simp only [hk, ↓reduceIte]
    fun_prop

private theorem corrGInt_eq_zero {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ϱ : ℝ}
    (hn : 0 < n) (hϱ : 0 < ϱ)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0)
    (u : Fin n → ℝ) {y : ℝ} (hy : ρO / ϱ < |y|) : corrGInt O ϱ u y = 0 := by
  unfold corrGInt
  refine corr_symmetrize_eq_zero hsupp ⟨⟨0, hn⟩, ?_⟩
  simp only [↓reduceIte, add_zero, abs_mul, abs_of_pos hϱ]
  rwa [div_lt_iff₀ hϱ, mul_comm] at hy

/-- `corrG` is the integral over the window `|y| ≤ ρ_O/ϱ`. -/
private theorem corrG_eq_setIntegral {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ϱ : ℝ}
    (hn : 0 < n) (hϱ : 0 < ϱ)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (u : Fin n → ℝ) :
    corrG O ϱ u = ∫ y in Set.Icc (-(ρO / ϱ)) (ρO / ϱ), corrGInt O ϱ u y := by
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  refine corrGInt_eq_zero hn hϱ hsupp u ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  rcases hy with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs y)
  · exact lt_of_lt_of_le h (le_abs_self y)

private theorem abs_corrG_le {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B ρO ℓ ϱ : ℝ}
    (hn : 0 < n) (hϱ : 0 < ϱ) (hρ : 0 ≤ ρO) (hρℓ : ρO ≤ ℓ * ϱ) (hB : ∀ α, |O α| ≤ B)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (u : Fin n → ℝ) :
    |corrG O ϱ u| ≤ 2 * ℓ * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hρϱ : ρO / ϱ ≤ ℓ := by rw [div_le_iff₀ hϱ]; exact hρℓ
  rw [corrG_eq_setIntegral hn hϱ hsupp u]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Icc (-(ρO / ϱ)) (ρO / ϱ)) (f := corrGInt O ϱ u) (C := B)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun y _ => by rw [Real.norm_eq_abs]; exact corr_abs_symmetrize_le hB _)
  rw [Real.volume_real_Icc_of_le (by have := div_nonneg hρ hϱ.le; linarith)] at h
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have : ρO / ϱ - -(ρO / ϱ) ≤ 2 * ℓ := by linarith
  nlinarith

private theorem corrG_continuous {n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ϱ : ℝ}
    (hn : 0 < n) (hϱ : 0 < ϱ) (hO : Continuous O)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) :
    Continuous (corrG O ϱ) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ))
    (corrGInt_continuous ϱ hO) (isCompact_Icc (a := -(ρO / ϱ)) (b := ρO / ϱ))
  have e : corrG O ϱ = fun u => ∫ y in Set.Icc (-(ρO / ϱ)) (ρO / ϱ), corrGInt O ϱ u y := by
    funext u; exact corrG_eq_setIntegral hn hϱ hsupp u
  rw [e]
  exact h

private theorem corr_norm_eq_abs_of_single {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (j₀ : Fin n)
    (hw : ∀ j, j ≠ j₀ → w j = 0) : ‖w‖ = |w j₀| := by
  rw [EuclideanSpace.norm_eq, Finset.sum_eq_single j₀ (fun j _ hj => by simp [hw j hj])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [Real.sqrt_sq_eq_abs]

/-- Lemma 19.2 (c): the function `u ↦ G_ϱ(0, u)` satisfies the hypotheses of Theorem 17.7 with
`(A, A', ρ) = (2ℓ‖O‖_∞, 2ρ_O Lip(O), 2ℓ)`; here `n = r + 1`. -/
theorem corrG_gapHyp {r : ℕ} {O : EuclideanSpace ℝ (Fin (r + 1)) → ℝ} {B K ρO ℓ ϱ : ℝ}
    (hB : ∀ α, |O α| ≤ B) (hLip : ∀ α β, |O α - O β| ≤ K * ‖α - β‖) (hK : 0 ≤ K)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin (r + 1)), (∃ k, ρO < |α k|) → O α = 0)
    (hρ : 0 ≤ ρO) (hϱ : 0 < ϱ) (hρℓ : ρO ≤ ℓ * ϱ) :
    GapHyp r (2 * ℓ * B) (2 * ρO * K) (2 * ℓ)
      (fun u : Fin r → ℝ => corrG O ϱ (Fin.cons 0 u)) := by
  have hn : 0 < r + 1 := Nat.succ_pos r
  have hO : Continuous O := corr_continuous_of_lip hK hLip
  have hcons : Continuous fun u : Fin r → ℝ => (Fin.cons (0 : ℝ) u : Fin (r + 1) → ℝ) := by
    refine continuous_pi fun k => ?_
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa using continuous_const
    · simpa using continuous_apply j
  refine ⟨?_, fun u _ => abs_corrG_le hn hϱ hρ hρℓ hB hsupp _, ?_, ?_⟩
  · exact ((corrG_continuous hn hϱ hO hsupp).comp hcons).measurable
  · intro u _ ⟨k, hk⟩
    have h0 : ∀ y, corrGInt O ϱ (Fin.cons 0 u) y = 0 := by
      intro y
      unfold corrGInt
      refine corr_symmetrize_eq_zero hsupp ?_
      by_contra hcon
      push Not at hcon
      have h1 := hcon 0
      have h2 := hcon k.succ
      simp only [Fin.val_zero, ↓reduceIte, add_zero, abs_mul, abs_of_pos hϱ,
        Fin.val_succ, Nat.succ_ne_zero, Fin.cons_succ] at h1 h2
      have h3 := mul_le_mul_of_nonneg_left (le_abs_self (y + u k)) hϱ.le
      have h4 := mul_le_mul_of_nonneg_left (neg_abs_le y) hϱ.le
      have : ϱ * u k ≤ 2 * ρO := by nlinarith
      nlinarith
    change corrG O ϱ (Fin.cons 0 u) = 0
    have : corrG O ϱ (Fin.cons 0 u) = ∫ y, corrGInt O ϱ (Fin.cons 0 u) y := rfl
    rw [this]
    simp [h0]
  · intro u u' k _ _ hk
    show |corrG O ϱ (Fin.cons 0 u) - corrG O ϱ (Fin.cons 0 u')| ≤ 2 * ρO * K * |u k - u' k|
    rw [corrG_eq_setIntegral hn hϱ hsupp, corrG_eq_setIntegral hn hϱ hsupp]
    have hcont : ∀ v : Fin (r + 1) → ℝ, Continuous fun y => corrGInt O ϱ v y := fun v =>
      (corrGInt_continuous ϱ hO).comp (continuous_const.prodMk continuous_id)
    rw [← integral_sub ((hcont _).integrableOn_Icc) ((hcont _).integrableOn_Icc)]
    have hpt : ∀ y ∈ Set.Icc (-(ρO / ϱ)) (ρO / ϱ),
        ‖corrGInt O ϱ (Fin.cons 0 u) y - corrGInt O ϱ (Fin.cons 0 u') y‖ ≤
          K * ϱ * |u k - u' k| := by
      intro y _
      rw [Real.norm_eq_abs]
      refine (corr_abs_symmetrize_sub_le hLip _ _).trans ?_
      have hnorm : ‖(WithLp.toLp 2 fun j : Fin (r + 1) =>
          ϱ * (y + if j.val = 0 then 0 else (Fin.cons 0 u : Fin (r + 1) → ℝ) j) :
            EuclideanSpace ℝ (Fin (r + 1))) -
          (WithLp.toLp 2 fun j : Fin (r + 1) =>
          ϱ * (y + if j.val = 0 then 0 else (Fin.cons 0 u' : Fin (r + 1) → ℝ) j))‖ =
          ϱ * |u k - u' k| := by
        have e : (WithLp.toLp 2 fun j : Fin (r + 1) =>
            ϱ * (y + if j.val = 0 then 0 else (Fin.cons 0 u : Fin (r + 1) → ℝ) j) :
              EuclideanSpace ℝ (Fin (r + 1))) -
            (WithLp.toLp 2 fun j : Fin (r + 1) =>
            ϱ * (y + if j.val = 0 then 0 else (Fin.cons 0 u' : Fin (r + 1) → ℝ) j)) =
            WithLp.toLp 2 fun j : Fin (r + 1) => ϱ * ((Fin.cons 0 u : Fin (r + 1) → ℝ) j -
              (Fin.cons 0 u' : Fin (r + 1) → ℝ) j) := by
          ext j
          refine Fin.cases ?_ (fun j' => ?_) j <;> simp
          ring
        rw [e, corr_norm_eq_abs_of_single _ k.succ]
        · simp [abs_mul, abs_of_pos hϱ]
        · intro j hj
          refine Fin.cases ?_ (fun j' hj' => ?_) j hj
          · simp
          · have : j' ≠ k := fun h => hj' (by rw [h])
            simp [hk j' this]
      rw [hnorm]
      linarith
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Icc (-(ρO / ϱ)) (ρO / ϱ))
      (f := fun y => corrGInt O ϱ (Fin.cons 0 u) y - corrGInt O ϱ (Fin.cons 0 u') y)
      (C := K * ϱ * |u k - u' k|) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hpt
    rw [Real.volume_real_Icc_of_le (by have := div_nonneg hρ hϱ.le; linarith),
      Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring

/-! ### The constant `C⋆` and the gap observable -/

/-- Lemma 19.2 (c): `√C⋆(2ℓ‖O‖_∞, 2ρ_O Lip(O), 2ℓ) ≤ C_♯ (‖O‖_∞ + Lip(O))` with
`C_♯ = ℓ (√(2/c₀) + 3√2 e ρ_O)`. -/
theorem sqrt_cStar_le {B K ρO ℓ : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hρ : 0 ≤ ρO) (hℓ : 0 ≤ ℓ) :
    Real.sqrt (cStar (2 * ℓ * B) (2 * ρO * K) (2 * ℓ)) ≤
      ℓ * (Real.sqrt (2 / cZero) + 3 * Real.sqrt 2 * Real.exp 1 * ρO) * (B + K) := by
  have hc := cZero_pos
  have ha : Real.sqrt (2 / cZero) ^ 2 = 2 / cZero := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ Real.sqrt (2 / cZero) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have he0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  set a := Real.sqrt (2 / cZero) with hadef
  set s := Real.sqrt 2 with hsdef
  set T1 := ℓ * B * a with hT1
  set T2 := 3 * s * Real.exp 1 * ℓ * ρO * K with hT2
  have hT1n : 0 ≤ T1 := by positivity
  have hT2n : 0 ≤ T2 := by positivity
  have hR : T1 + T2 ≤ ℓ * (a + 3 * s * Real.exp 1 * ρO) * (B + K) := by
    have h1 : 0 ≤ ℓ * a * K := by positivity
    have h2 : 0 ≤ ℓ * (3 * s * Real.exp 1 * ρO) * B := by positivity
    nlinarith
  rw [Real.sqrt_le_iff]
  refine ⟨by nlinarith, max_le ?_ ?_⟩
  · have e1 : (2 * ℓ * B) ^ 2 / (2 * cZero) = T1 ^ 2 := by
      have : T1 ^ 2 = (ℓ * B) ^ 2 * a ^ 2 := by rw [hT1]; ring
      rw [this, ha]
      field_simp
    rw [e1]
    exact pow_le_pow_left₀ hT1n (by linarith) 2
  · have e2 : 9 / 8 * (Real.exp 1 * (2 * ℓ) * (2 * ρO * K)) ^ 2 = T2 ^ 2 := by
      rw [hT2]
      have : (3 * s * Real.exp 1 * ℓ * ρO * K) ^ 2 =
          9 * s ^ 2 * (Real.exp 1 * ℓ * ρO * K) ^ 2 := by ring
      rw [this, hs]
      ring
    rw [e2]
    exact pow_le_pow_left₀ hT2n (by linarith) 2

/-- `corrG` does not depend on the coordinate `k = 0`. -/
private theorem corrG_congr {n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (ϱ : ℝ) {u u' : Fin n → ℝ}
    (h : ∀ k : Fin n, k.val ≠ 0 → u k = u' k) : corrG O ϱ u = corrG O ϱ u' := by
  unfold corrG
  congr 1
  funext y
  congr 2
  ext k
  by_cases hk : k.val = 0
  · simp [hk]
  · simp [hk, h k hk]

/-- `corrF` is the gap observable of (17.4) built from `G_ϱ(0, ·)`; here `n = r + 1`. -/
theorem corrF_eq_gapObs {N r : ℕ} (O : EuclideanSpace ℝ (Fin (r + 1)) → ℝ) (ϱ : ℝ) (J : Finset ℕ)
    (m : Fin (r + 1) → ℕ) :
    corrF (N := N) O ϱ J m =
      gapObs (J.filter fun i => i + lastIdx m < N) (fun k : Fin r => m k.succ)
        (fun u : Fin r → ℝ => corrG O ϱ (Fin.cons 0 u)) := by
  funext x
  unfold corrF gapObs
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine corrG_congr O ϱ fun k hk => ?_
  obtain ⟨j, rfl⟩ : ∃ j : Fin r, k = j.succ := by
    refine Fin.cases ?_ (fun j _ => ⟨j, rfl⟩) k hk
    intro h; exact absurd rfl h
  simp

/-! ### The functions `Y_{i,m}` -/

/-- Lemma 19.2 (b): `Y_{i,m}(E', x) = 0` unless `|x_{i+m_k} - E'| ≤ ℓ/N` for all `k`. -/
theorem corrY_support {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ℓ ϱ : ℝ}
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) {E' : ℝ} {m : Fin n → ℕ} {i : ℕ} {x : Fin N → ℝ}
    (h : ∃ k, ℓ / N < |extVec x (i + m k) - E'|) : corrY O ϱ E' m i x = 0 := by
  unfold corrY
  split_ifs with hlt
  · have hN : (0 : ℝ) < N := by
      have : 0 < N := by omega
      exact_mod_cast this
    obtain ⟨k, hk⟩ := h
    refine corr_symmetrize_eq_zero hsupp ⟨k, ?_⟩
    simp only [abs_mul, abs_of_pos hN, abs_of_pos hϱ]
    rw [div_lt_iff₀ hN] at hk
    nlinarith
  · rfl

private theorem corrY_continuous {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ}
    (hO : Continuous O) (ϱ : ℝ) (m : Fin n → ℕ) (i : ℕ) (x : Fin N → ℝ) :
    Continuous fun E' => corrY O ϱ E' m i x := by
  by_cases h : i + lastIdx m < N
  · simp only [corrY, h, ↓reduceIte]
    refine (corr_continuous_symmetrize hO).comp ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun k => ?_))
    fun_prop
  · simp only [corrY, h, ↓reduceIte]
    exact continuous_const

private theorem abs_corrY_le {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hB : ∀ α, |O α| ≤ B) (ϱ E' : ℝ) (m : Fin n → ℕ) (i : ℕ) (x : Fin N → ℝ) :
    |corrY O ϱ E' m i x| ≤ B := by
  unfold corrY
  split_ifs
  · exact corr_abs_symmetrize_le hB _
  · simpa using le_trans (abs_nonneg _) (hB 0)

/-- Lemma 19.2 (b): `∫ Y_{i,m}(E', x) dE' = N⁻¹ G_ϱ(N(x_{i+m_k} - x_i))_k`. -/
theorem integral_corrY {N n : ℕ} (O : EuclideanSpace ℝ (Fin n) → ℝ) (ϱ : ℝ) {m : Fin n → ℕ}
    (hm : IsIndexTuple m) {i : ℕ} (hi : i + lastIdx m < N) (x : Fin N → ℝ) :
    ∫ E', corrY O ϱ E' m i x =
      (N : ℝ)⁻¹ * corrG O ϱ fun k => N * (extVec x (i + m k) - extVec x i) := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set u : Fin n → ℝ := fun k => N * (extVec x (i + m k) - extVec x i) with hu
  set e : ℝ := extVec x i with he
  have hY : ∀ E', corrY O ϱ E' m i x = corrGInt O ϱ u (N * (e - E')) := by
    intro E'
    simp only [corrY, hi, ↓reduceIte, corrGInt]
    congr 2
    ext k
    by_cases hk : k.val = 0
    · have hmk : m k = 0 := by
        have h0 : k = ⟨0, k.pos⟩ := Fin.ext hk
        rw [h0]; exact hm.2 k.pos
      simp [hk, hmk, he]
      ring
    · simp [hk, hu]
      ring
  have h1 : ∫ E', corrY O ϱ E' m i x = ∫ E', (fun s => corrGInt O ϱ u (N * s)) (e - E') := by
    simp only [hY]
  rw [h1, integral_sub_left_eq_self (fun s => corrGInt O ϱ u (N * s)) volume e,
    Measure.integral_comp_mul_left (fun t => corrGInt O ϱ u t) (N : ℝ), abs_of_pos (inv_pos.mpr hN)]
  rfl

private theorem corrY_eq_zero_of_far {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ℓ ϱ : ℝ}
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) {m : Fin n → ℕ} (hm : IsIndexTuple m) (hn : 0 < n) {i : ℕ}
    {x : Fin N → ℝ} {E' : ℝ} (h : ℓ / N < |extVec x i - E'|) : corrY O ϱ E' m i x = 0 := by
  refine corrY_support hsupp hϱ hρℓ ⟨⟨0, hn⟩, ?_⟩
  rw [hm.2 hn, add_zero]
  exact h

private theorem corrY_integrable {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ℓ ϱ : ℝ}
    (hO : Continuous O)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) {m : Fin n → ℕ} (hm : IsIndexTuple m) (hn : 0 < n) (i : ℕ)
    (x : Fin N → ℝ) : Integrable fun E' => corrY O ϱ E' m i x := by
  refine (corrY_continuous hO ϱ m i x).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := extVec x i - ℓ / N) (b := extVec x i + ℓ / N))
      fun E' hE' => ?_)
  refine corrY_eq_zero_of_far hsupp hϱ hρℓ hm hn ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hE'
  rcases hE' with h | h
  · exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

private theorem abs_setIntegral_le_integral_abs {f : ℝ → ℝ} (hf : Integrable f) (s : Set ℝ) :
    |∫ x in s, f x| ≤ ∫ x, |f x| := by
  calc |∫ x in s, f x| = ‖∫ x in s, f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in s, ‖f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ :=
      setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ = ∫ x, |f x| := by simp

/-- Lemma 19.2 (b): `∫ |Y_{i,m}(E', x)| dE' ≤ 2ℓ‖O‖_∞/N`. -/
private theorem integral_abs_corrY_le {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B ρO ℓ ϱ : ℝ} (hB : ∀ α, |O α| ≤ B)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) (hℓ : 0 ≤ ℓ) {m : Fin n → ℕ} (hm : IsIndexTuple m) (hn : 0 < n) {i : ℕ}
    (hi : i + lastIdx m < N) (x : Fin N → ℝ) :
    ∫ E', |corrY O ϱ E' m i x| ≤ 2 * ℓ * B / N := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hz : ∀ E' ∉ Set.Icc (extVec x i - ℓ / N) (extVec x i + ℓ / N),
      |corrY O ϱ E' m i x| = 0 := by
    intro E' hE'
    rw [abs_eq_zero]
    refine corrY_eq_zero_of_far hsupp hϱ hρℓ hm hn ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hE'
    rcases hE' with h | h
    · exact lt_of_lt_of_le (by linarith) (le_abs_self _)
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Icc (extVec x i - ℓ / N) (extVec x i + ℓ / N))
    (f := fun E' => |corrY O ϱ E' m i x|) (C := B)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun E' _ => by rw [Real.norm_eq_abs, abs_abs]; exact abs_corrY_le hB ϱ E' m i x)
  rw [Real.volume_real_Icc_of_le (by have : 0 ≤ ℓ / N := by positivity
                                     linarith), Real.norm_eq_abs] at h
  refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
  field_simp
  ring

/-! ### Localisation on the good set -/

/-- Lemma 19.3 (a): on `Ξ`, for `E' ∈ [-3, 3]`, `Y_{i,m}(E', x) = 0` whenever `m_n ≥ K_ℓ`, where
`K_ℓ = 2ℓ/π + 2D`. -/
theorem corrY_eq_zero_of_mem_flowGoodSet {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {ρO ℓ ϱ D c : ℝ} (hN : 3 ≤ N) (hD : 0 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ)
    (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) {E' : ℝ}
    (hE' : E' ∈ Set.Icc (-3 : ℝ) 3) {m : Fin n → ℕ} (hm : IsIndexTuple m)
    (hlast : 2 * ℓ / π + 2 * D ≤ lastIdx m) (i : ℕ) : corrY O ϱ E' m i x = 0 := by
  by_contra hne
  have hKpos : 0 < 2 * ℓ / π + 2 * D := by positivity
  have hn : 0 < n := by
    by_contra h
    have : lastIdx m = 0 := by simp [lastIdx, h]
    rw [this] at hlast
    simp at hlast
    linarith
  have hi : i + lastIdx m < N := by
    by_contra h
    exact hne (by simp [corrY, h])
  have hcl : ∀ k, |extVec x (i + m k) - E'| ≤ ℓ / N := by
    intro k
    by_contra hk
    exact hne (corrY_support hsupp hϱ hρℓ ⟨k, not_le.mp hk⟩)
  set L := lastIdx m with hL
  have h0 := hcl ⟨0, hn⟩
  have h1 := hcl ⟨n - 1, by omega⟩
  rw [hm.2 hn, add_zero, corr_extVec_of_lt x (by omega)] at h0
  rw [← corr_lastIdx_eq hn m, ← hL, corr_extVec_of_lt x hi] at h1
  have hmono := hx.1
  have hsub : L + 1 ≤ (Finset.univ.filter fun j : Fin N => |x j - E'| ≤ ℓ / N).card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (L + 1))))
      (t := Finset.univ.filter fun j : Fin N => |x j - E'| ≤ ℓ / N)
      (fun t => (⟨i + t, by have := t.isLt; omega⟩ : Fin N)) ?_ ?_
    · simpa using this
    · intro t _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      have hlo : x ⟨i, by omega⟩ ≤ x ⟨i + t, by have := t.isLt; omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hhi : x ⟨i + t, by have := t.isLt; omega⟩ ≤ x ⟨i + L, hi⟩ :=
        hmono (Fin.mk_le_mk.mpr (by have := t.isLt; omega))
      rw [abs_le] at h0 h1 ⊢
      constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
    · intro s _ t _ hst
      simp only [Fin.mk.injEq] at hst
      exact Fin.ext (by omega)
  have hcard := card_near_le_of_mem_flowGoodSet hN hD hc hc2 hℓ hH hx hE'
  have : ((L + 1 : ℕ) : ℝ) ≤ ((Finset.univ.filter fun j : Fin N => |x j - E'| ≤ ℓ / N).card : ℝ) :=
    by exact_mod_cast hsub
  push_cast at this
  linarith

open Classical in
/-- Lemma 19.3 (b), counting: for `K ≥ 0` the index tuples `m ∈ 𝔖_n` with `m_n < K` number at most
`K^{n-1}`. -/
theorem card_indexTuples_le {N n : ℕ} (hn : 0 < n) {K : ℝ} (hK : 0 ≤ K) :
    ((Finset.univ.filter fun m : Fin n → Fin N =>
        (IsIndexTuple fun k => (m k : ℕ)) ∧ ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < K).card : ℝ) ≤
      K ^ (n - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set M : ℕ := ⌈K⌉₊ - 1 with hM
  have hMK : (M : ℝ) ≤ K := by
    rcases Nat.eq_zero_or_pos ⌈K⌉₊ with h | h
    · simp [hM, h, hK]
    · have := Nat.ceil_lt_add_one hK
      rw [hM, Nat.cast_sub h]
      push_cast
      linarith
  have hcard : (Finset.univ.filter fun m : Fin (r + 1) → Fin N =>
      (IsIndexTuple fun k => (m k : ℕ)) ∧ ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < K).card ≤
        (Fintype.piFinset fun _ : Fin r => Finset.Icc 1 M).card := by
    refine Finset.card_le_card_of_injOn (fun m (k : Fin r) => (m k.succ : ℕ)) ?_ ?_
    · intro m hm
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm
      obtain ⟨⟨hmono, hm0⟩, hlt⟩ := hm
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_Icc]
      have hpos : (m 0 : ℕ) < m k.succ := hmono (Fin.succ_pos k)
      rw [show (m 0 : ℕ) = 0 from hm0 (Nat.succ_pos r)] at hpos
      have hle : (m k.succ : ℕ) ≤ lastIdx fun k => (m k : ℕ) :=
        corr_le_lastIdx (m := fun k => (m k : ℕ)) hmono.monotone k.succ
      have : (m k.succ : ℕ) < ⌈K⌉₊ := Nat.lt_ceil.mpr (lt_of_le_of_lt (by exact_mod_cast hle) hlt)
      change 1 ≤ (m k.succ : ℕ) ∧ (m k.succ : ℕ) ≤ M
      omega
    · intro m hm m' hm' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm hm'
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · apply Fin.ext
        rw [show (m 0 : ℕ) = 0 from hm.1.2 (Nat.succ_pos r),
          show (m' 0 : ℕ) = 0 from hm'.1.2 (Nat.succ_pos r)]
      · exact Fin.ext (congrFun h j)
  rw [Fintype.card_piFinset] at hcard
  simp only [Nat.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel] at hcard
  have : ((Finset.univ.filter fun m : Fin (r + 1) → Fin N =>
      (IsIndexTuple fun k => (m k : ℕ)) ∧ ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < K).card : ℝ) ≤
        (M : ℝ) ^ r := by exact_mod_cast hcard
  exact this.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hMK r)

/-! ### The reduction of `∫ 𝒳 dE'` -/

private theorem corr_rhoStar_pos {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) : 0 < rhoStar c := by
  unfold rhoStar
  have : 0 < c - c ^ 2 / 16 := by nlinarith
  positivity

private theorem corr_rhoStar_le_one {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) : rhoStar c ≤ 1 := by
  unfold rhoStar
  have hπ := Real.pi_gt_three
  have : Real.sqrt (c - c ^ 2 / 16) ≤ 2 * π :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  rw [inv_mul_eq_div, div_le_one (by positivity)]
  exact this

/-- The two scales of Lemma 13.4: `D/(N ϱ_*) ≤ c/8` and `ℓ/N ≤ c/8`. -/
private theorem corr_scales {N : ℕ} {D c ℓ : ℝ} (hN : 0 < N) (hD : 0 ≤ D) (hc : 0 < c)
    (hc2 : c ≤ 2) (hℓ : 0 < ℓ) (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) :
    D / (N * rhoStar c) ≤ c / 8 ∧ ℓ / N ≤ c / 8 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ := corr_rhoStar_pos hc hc2
  have hρ1 := corr_rhoStar_le_one hc hc2
  rw [add_div] at hH
  have h1 : 0 ≤ ℓ / (N * rhoStar c) := by positivity
  have h2 : 0 ≤ D / (N * rhoStar c) := by positivity
  refine ⟨by linarith, ?_⟩
  have : ℓ / N ≤ ℓ / (N * rhoStar c) := by
    apply div_le_div_of_nonneg_left hℓ.le (by positivity)
    nlinarith
  linarith

open Classical in
/-- The `i`-th summand of Lemma 19.3 (b): the difference between the integral of `Y_{i,m}` over
`[E - b, E + b]` and the contribution `1_{i ∈ J} ∫ Y_{i,m}` to `F_m` is controlled by `2ℓ‖O‖_∞/N`
and vanishes unless `i ∈ 𝓑`. -/
private theorem corrY_delta_le {N n : ℕ} (hn : 0 < n) {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B ρO ℓ ϱ D c E b : ℝ} (hN : 3 ≤ N) (hD : 0 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ)
    (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) (hB : ∀ α, |O α| ≤ B) (hO : Continuous O)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) (hE : E ∈ Set.Icc (-2 + c) (2 - c)) (hb : 0 < b) (hb2 : b < c / 2)
    {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) {J : Finset ℕ} {m : Fin n → ℕ}
    (hm : IsIndexTuple m) (i : Fin N)
    (hiJ : (i : ℕ) ∈ J ↔ gamma N i ∈ Set.Icc (E - b) (E + b)) :
    |(∫ E' in (E - b)..(E + b), corrY O ϱ E' m i x) -
        (if (i : ℕ) ∈ J then ∫ E', corrY O ϱ E' m i x else 0)| ≤
      if min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ D / (N * rhoStar c) + ℓ / N
        then 2 * ℓ * B / N else 0 := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hrhs : 0 ≤ 2 * ℓ * B / N := by positivity
  obtain ⟨hξ, hδ⟩ := corr_scales hNpos hD hc hc2 hℓ hH
  set ξ : ℝ := D / (N * rhoStar c) with hξdef
  set δ : ℝ := ℓ / N with hδdef
  have hab : E - b ≤ E + b := by linarith
  have hEb1 : -2 + c / 2 < E - b := by linarith [hE.1]
  have hEb2 : E + b < 2 - c / 2 := by linarith [hE.2]
  -- the vanishing set of `Y`
  have hnz : ∀ E', corrY O ϱ E' m i x ≠ 0 → |x i - E'| ≤ δ := by
    intro E' hne
    by_contra hlt
    refine hne (corrY_eq_zero_of_far hsupp hϱ hρℓ hm hn ?_)
    rw [corr_extVec_val]
    exact not_le.mp hlt
  by_cases hi : i + lastIdx m < N
  swap
  · have h0 : ∀ E', corrY O ϱ E' m i x = 0 := fun E' => by simp [corrY, hi]
    simp only [h0, intervalIntegral.integral_zero, integral_zero, ite_self, sub_zero, abs_zero]
    split_ifs <;> first | exact hrhs | exact le_rfl
  have hint := corrY_integrable hO hsupp hϱ hρℓ hm hn i x
  have hL1 := integral_abs_corrY_le hB hsupp hϱ hρℓ hℓ.le hm hn hi x
  have hcont := corrY_continuous hO ϱ m i x
  rw [intervalIntegral.integral_of_le hab]
  by_cases hB' : min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ ξ + δ
  · simp only [hB', ↓reduceIte]
    by_cases hJ' : (i : ℕ) ∈ J
    · -- `i ∈ 𝓑`, `i ∈ J`
      simp only [hJ', ↓reduceIte]
      have := integral_add_compl (μ := volume) (measurableSet_Ioc (a := E - b) (b := E + b)) hint
      have h2 : (∫ E' in Set.Ioc (E - b) (E + b), corrY O ϱ E' m i x) -
          ∫ E', corrY O ϱ E' m i x = -∫ E' in (Set.Ioc (E - b) (E + b))ᶜ, corrY O ϱ E' m i x := by
        linarith
      rw [h2, abs_neg]
      exact (abs_setIntegral_le_integral_abs hint _).trans hL1
    · -- `i ∈ 𝓑`, `i ∉ J`
      simp only [hJ', ↓reduceIte, sub_zero]
      exact (abs_setIntegral_le_integral_abs hint _).trans hL1
  · simp only [hB', ↓reduceIte]
    have hmin : ξ + δ < min |gamma N i - (E - b)| |gamma N i - (E + b)| := not_le.mp hB'
    by_cases hJ' : (i : ℕ) ∈ J
    · -- `i ∉ 𝓑`, `i ∈ J`
      simp only [hJ', ↓reduceIte]
      have hγ := hiJ.mp hJ'
      have hbulk : gamma N i ∈ Set.Icc (-2 + 3 / 8 * c) (2 - 3 / 8 * c) :=
        ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
      have hxγ := abs_sub_gamma_le_of_mem_flowGoodSet hN hD hc hc2 hℓ hH hx i (Or.inr hbulk)
      rw [← hξdef] at hxγ
      have hsub : ∀ E' ∉ Set.Ioc (E - b) (E + b), corrY O ϱ E' m i x = 0 := by
        intro E' hE'
        by_contra hne
        have h1 := hnz E' hne
        rw [abs_le] at h1
        have h2 := abs_le.mp hxγ
        have h3 := lt_min_iff.mp hmin
        rw [abs_of_nonneg (by linarith [hγ.1] : 0 ≤ gamma N i - (E - b))] at h3
        rw [abs_of_nonpos (by linarith [hγ.2] : gamma N i - (E + b) ≤ 0)] at h3
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hE'
        rcases hE' with h | h
        · linarith [h3.1]
        · linarith [h3.2]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsub, sub_self, abs_zero]
    · -- `i ∉ 𝓑`, `i ∉ J`
      simp only [hJ', ↓reduceIte]
      have hγ : gamma N i ∉ Set.Icc (E - b) (E + b) := fun h => hJ' (hiJ.mpr h)
      have hz : ∀ E' ∈ Set.Ioc (E - b) (E + b), corrY O ϱ E' m i x = 0 := by
        intro E' hE'
        by_contra hne
        have h1 := hnz E' hne
        rw [abs_le] at h1
        have hxi : x i ∈ Set.Icc (-2 + 3 / 8 * c) (2 - 3 / 8 * c) :=
          ⟨by linarith [hE'.1, h1.2], by linarith [hE'.2, h1.1]⟩
        have hxγ := abs_sub_gamma_le_of_mem_flowGoodSet hN hD hc hc2 hℓ hH hx i (Or.inl hxi)
        rw [← hξdef] at hxγ
        have h2 := abs_le.mp hxγ
        have h3 := lt_min_iff.mp hmin
        simp only [Set.mem_Icc, not_and_or, not_le] at hγ
        rcases hγ with h | h
        · rw [abs_of_neg (by linarith : gamma N i - (E - b) < 0)] at h3
          linarith [h3.1, hE'.1]
        · rw [abs_of_pos (by linarith : 0 < gamma N i - (E + b))] at h3
          linarith [h3.2, hE'.2]
      rw [sub_zero, setIntegral_congr_fun measurableSet_Ioc hz]
      simp

open Classical in
/-- Lemma 19.3 (b), reduction: on `Ξ`, `∫_{E-b}^{E+b} 𝒳^O_{E',ϱ}(x) dE'` differs from
`n! ∑_{m ∈ 𝔖_n, m_n < K_ℓ} F_m(x)` by at most `n! |𝓑| K_ℓ^{n-1} 2ℓ‖O‖_∞/N`, where `K_ℓ = 2ℓ/π + 2D`,
`J = {i : γ_i ∈ [E-b, E+b]}` and `𝓑` is the set of Lemma 13.4 (c). -/
theorem abs_integral_corrX_sub_le {N n : ℕ} (hn : 0 < n) {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B K ρO ℓ ϱ D c E b : ℝ} (hN : 3 ≤ N) (hD : 0 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ)
    (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) (hB : ∀ α, |O α| ≤ B)
    (hLip : ∀ α β, |O α - O β| ≤ K * ‖α - β‖) (hK : 0 ≤ K)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) (hE : E ∈ Set.Icc (-2 + c) (2 - c)) (hb : 0 < b) (hb2 : b < c / 2)
    {J : Finset ℕ}
    (hJ : ∀ i : ℕ, i ∈ J ↔ ∃ j : Fin N, (j : ℕ) = i ∧ gamma N j ∈ Set.Icc (E - b) (E + b))
    {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) :
    |(∫ E' in (E - b)..(E + b), corrX O E' ϱ x) -
        n.factorial * ∑ m ∈ Finset.univ.filter (fun m : Fin n → Fin N =>
            (IsIndexTuple fun k => (m k : ℕ)) ∧
              ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < 2 * ℓ / π + 2 * D),
          corrF O ϱ J (fun k => (m k : ℕ)) x| ≤
      n.factorial * (Finset.univ.filter fun i : Fin N =>
          min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ D / (N * rhoStar c) + ℓ / N).card *
        (2 * ℓ / π + 2 * D) ^ (n - 1) * (2 * ℓ * B / N) := by
  have hO := corr_continuous_of_lip hK hLip
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hKl0 : 0 ≤ 2 * ℓ / π + 2 * D := by positivity
  have hab : E - b ≤ E + b := by linarith
  have hJi : ∀ i : Fin N, (i : ℕ) ∈ J ↔ gamma N i ∈ Set.Icc (E - b) (E + b) := by
    intro i
    rw [hJ]
    exact ⟨fun ⟨j, hj, hg⟩ => by rwa [← Fin.ext hj], fun h => ⟨i, rfl, h⟩⟩
  have hJsub : J ⊆ Finset.range N := by
    intro i hi
    obtain ⟨j, hj, -⟩ := (hJ i).mp hi
    exact Finset.mem_range.mpr (hj ▸ j.isLt)
  set Kl : ℝ := 2 * ℓ / π + 2 * D with hKl
  set Mset := Finset.univ.filter (fun m : Fin n → Fin N => IsIndexTuple fun k => (m k : ℕ))
    with hMset
  set Ml := Finset.univ.filter (fun m : Fin n → Fin N => (IsIndexTuple fun k => (m k : ℕ)) ∧
    ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < Kl) with hMl
  set Bs := Finset.univ.filter (fun i : Fin N =>
    min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤ D / (N * rhoStar c) + ℓ / N) with hBs
  set Y : Fin N → (Fin n → Fin N) → ℝ → ℝ := fun i m E' =>
    corrY O ϱ E' (fun k => (m k : ℕ)) i x with hY
  have hYc : ∀ i m, Continuous (Y i m) := fun i m => corrY_continuous hO ϱ _ _ x
  have hYi : ∀ i m, IntervalIntegrable (Y i m) volume (E - b) (E + b) := fun i m =>
    (hYc i m).intervalIntegrable _ _
  -- the integral of `𝒳` as a sum over `(i, m)`
  have step1 : (∫ E' in (E - b)..(E + b), corrX O E' ϱ x) =
      n.factorial * ∑ i : Fin N, ∑ m ∈ Mset, ∫ E' in (E - b)..(E + b), Y i m E' := by
    have e1 : (∫ E' in (E - b)..(E + b), corrX O E' ϱ x) =
        ∫ E' in (E - b)..(E + b), (n.factorial : ℝ) * ∑ i : Fin N, ∑ m ∈ Mset, Y i m E' :=
      intervalIntegral.integral_congr fun E' _ => corrX_eq_sum_corrY hn O E' ϱ hx.1
    rw [e1, intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_finsetSum fun i _ => ?_]
    swap
    · have := IntervalIntegrable.sum Mset (f := fun m E' => Y i m E') fun m _ => hYi i m
      rwa [Finset.sum_fn] at this
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun m _ => hYi i m]
  -- terms with `m_n ≥ K_ℓ` do not contribute
  have step2 : ∀ i : Fin N, ∑ m ∈ Mset, ∫ E' in (E - b)..(E + b), Y i m E' =
      ∑ m ∈ Ml, ∫ E' in (E - b)..(E + b), Y i m E' := by
    intro i
    have hMl' : Ml = Mset.filter (fun m => ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) < Kl) := by
      rw [hMl, hMset, Finset.filter_filter]
    rw [hMl', Finset.sum_filter (s := Mset)]
    refine Finset.sum_congr rfl fun m hm => ?_
    split_ifs with hlt
    · rfl
    · have hmI : IsIndexTuple fun k => (m k : ℕ) := by simpa [hMset] using hm
      have hge : Kl ≤ ((lastIdx fun k => (m k : ℕ) : ℕ) : ℝ) := not_lt.mp hlt
      have hz : ∀ E' ∈ Set.uIcc (E - b) (E + b), Y i m E' = 0 := by
        intro E' hE'
        rw [Set.uIcc_of_le hab] at hE'
        exact corrY_eq_zero_of_mem_flowGoodSet hN hD hc hc2 hℓ hH hsupp hϱ hρℓ hx
          ⟨by linarith [hE'.1, hE.1], by linarith [hE'.2, hE.2]⟩ hmI hge i
      rw [intervalIntegral.integral_congr hz]
      simp
  -- `F_m` as a sum over `i : Fin N`
  have step3 : ∀ m ∈ Ml, corrF O ϱ J (fun k => (m k : ℕ)) x =
      ∑ i : Fin N, if (i : ℕ) ∈ J then ∫ E', Y i m E' else 0 := by
    intro m hm
    have hmI : IsIndexTuple fun k => (m k : ℕ) := by
      rw [hMl, Finset.mem_filter] at hm
      exact hm.2.1
    unfold corrF
    have e1 : (N : ℝ)⁻¹ * ∑ i ∈ J.filter (fun i => i + lastIdx (fun k => (m k : ℕ)) < N),
        corrG O ϱ (fun k => N * (extVec x (i + (m k : ℕ)) - extVec x i)) =
        ∑ i ∈ J.filter (fun i => i + lastIdx (fun k => (m k : ℕ)) < N),
          ∫ E', corrY O ϱ E' (fun k => (m k : ℕ)) i x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [integral_corrY O ϱ hmI (Finset.mem_filter.mp hi).2 x]
    rw [e1, Finset.sum_filter_of_ne]
    · have e3 := Fin.sum_univ_eq_sum_range
        (fun i : ℕ => if i ∈ J then ∫ E', corrY O ϱ E' (fun k => (m k : ℕ)) i x else 0) N
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hJsub] at e3
      refine e3.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
      rfl
    · intro i _ hne
      by_contra hlt
      exact hne (by simp [corrY, hlt])
  have hdiff : (∫ E' in (E - b)..(E + b), corrX O E' ϱ x) -
      n.factorial * ∑ m ∈ Ml, corrF O ϱ J (fun k => (m k : ℕ)) x =
      n.factorial * ∑ m ∈ Ml, ∑ i : Fin N, ((∫ E' in (E - b)..(E + b), Y i m E') -
        if (i : ℕ) ∈ J then ∫ E', Y i m E' else 0) := by
    rw [step1, Finset.sum_congr rfl fun i _ => step2 i, Finset.sum_comm,
      Finset.sum_congr rfl step3, ← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
    rw [← Finset.sum_sub_distrib]
  -- the bound
  have hT : 0 ≤ 2 * ℓ * B / N := by positivity
  have hterm : ∀ m ∈ Ml, |∑ i : Fin N, ((∫ E' in (E - b)..(E + b), Y i m E') -
        if (i : ℕ) ∈ J then ∫ E', Y i m E' else 0)| ≤ Bs.card * (2 * ℓ * B / N) := by
    intro m hm
    have hmI : IsIndexTuple fun k => (m k : ℕ) := by
      rw [hMl, Finset.mem_filter] at hm
      exact hm.2.1
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin N, |(∫ E' in (E - b)..(E + b), Y i m E') -
          if (i : ℕ) ∈ J then ∫ E', Y i m E' else 0|
        ≤ ∑ i : Fin N, if i ∈ Bs then 2 * ℓ * B / N else 0 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := corrY_delta_le hn hN hD hc hc2 hℓ hH hB hO hsupp hϱ hρℓ hE hb hb2 hx hmI i
            (hJi i)
          have hmem : i ∈ Bs ↔ min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤
              D / (N * rhoStar c) + ℓ / N := by rw [hBs, Finset.mem_filter]; simp
          by_cases h : min |gamma N i - (E - b)| |gamma N i - (E + b)| ≤
              D / (N * rhoStar c) + ℓ / N
          · simp only [hmem.mpr h, ↓reduceIte]
            simpa only [h, ↓reduceIte] using this
          · simp only [mt hmem.mp h, ↓reduceIte]
            simpa only [h, ↓reduceIte] using this
      _ = Bs.card * (2 * ℓ * B / N) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 3
          ext i; simp [hBs]
  rw [hdiff, abs_mul, abs_of_pos hfac]
  have hcard := card_indexTuples_le (N := N) hn hKl0
  calc (n.factorial : ℝ) * |∑ m ∈ Ml, ∑ i : Fin N, ((∫ E' in (E - b)..(E + b), Y i m E') -
        if (i : ℕ) ∈ J then ∫ E', Y i m E' else 0)|
      ≤ n.factorial * (Ml.card * (Bs.card * (2 * ℓ * B / N))) := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hfac.le
        calc ∑ m ∈ Ml, |∑ i : Fin N, ((∫ E' in (E - b)..(E + b), Y i m E') -
              if (i : ℕ) ∈ J then ∫ E', Y i m E' else 0)|
            ≤ ∑ m ∈ Ml, (Bs.card * (2 * ℓ * B / N)) := Finset.sum_le_sum hterm
          _ = Ml.card * (Bs.card * (2 * ℓ * B / N)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n.factorial * (Kl ^ (n - 1) * (Bs.card * (2 * ℓ * B / N))) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac.le
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = n.factorial * Bs.card * Kl ^ (n - 1) * (2 * ℓ * B / N) := by ring

/-! ### Bounds on `𝒳` -/

/-- Lemma 19.2 (d): `|𝒳^O_{E',ϱ}(x)| ≤ N^n ‖O‖_∞` for all `x`. -/
theorem abs_corrX_le {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ}
    (hB : ∀ α, |O α| ≤ B) (E' ϱ : ℝ) (x : Fin N → ℝ) : |corrX O E' ϱ x| ≤ (N : ℝ) ^ n * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  unfold corrX
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ f : Fin n ↪ Fin N, |O (WithLp.toLp 2 fun k => N * ϱ * (x (f k) - E'))|
      ≤ ∑ f : Fin n ↪ Fin N, B := Finset.sum_le_sum fun f _ => hB _
    _ = (Fintype.card (Fin n ↪ Fin N) : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ n * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
        exact_mod_cast Nat.descFactorial_le_pow N n

open Classical in
/-- Lemma 19.3 (a), last claim: on `Ξ`, for `E' ∈ [-3, 3]`, `|𝒳^O_{E',ϱ}(x)| ≤ K_ℓ^n ‖O‖_∞` with
`K_ℓ = 2ℓ/π + 2D`. -/
theorem abs_corrX_le_of_mem_flowGoodSet {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ}
    {B ρO ℓ ϱ D c : ℝ} (hN : 3 ≤ N) (hD : 0 ≤ D) (hc : 0 < c) (hc2 : c ≤ 2) (hℓ : 0 < ℓ)
    (hH : (D + ℓ) / (N * rhoStar c) ≤ c / 8) (hB : ∀ α, |O α| ≤ B)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0) (hϱ : 0 < ϱ)
    (hρℓ : ρO ≤ ℓ * ϱ) {x : Fin N → ℝ} (hx : x ∈ flowGoodSet N D) {E' : ℝ}
    (hE' : E' ∈ Set.Icc (-3 : ℝ) 3) :
    |corrX O E' ϱ x| ≤ (2 * ℓ / π + 2 * D) ^ n * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hNR : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set S : Finset (Fin N) := Finset.univ.filter fun j => |x j - E'| ≤ ℓ / N with hS
  have hSc : (S.card : ℝ) ≤ 2 * ℓ / π + 2 * D :=
    card_near_le_of_mem_flowGoodSet hN hD hc hc2 hℓ hH hx hE'
  unfold corrX
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ f : Fin n ↪ Fin N, |O (WithLp.toLp 2 fun k => N * ϱ * (x (f k) - E'))|
      ≤ ∑ f : Fin n ↪ Fin N, if ∀ k, f k ∈ S then B else 0 := by
        refine Finset.sum_le_sum fun f _ => ?_
        by_cases hf : ∀ k, f k ∈ S
        · simp only [hf, implies_true, ↓reduceIte]
          exact hB _
        · simp only [hf, ↓reduceIte]
          push Not at hf
          obtain ⟨k, hk⟩ := hf
          rw [hS, Finset.mem_filter] at hk
          have hk' : ℓ / N < |x (f k) - E'| := by
            by_contra h
            exact hk ⟨Finset.mem_univ _, not_lt.mp h⟩
          rw [hsupp _ ⟨k, ?_⟩, abs_zero]
          simp only [abs_mul, abs_of_pos hNR, abs_of_pos hϱ]
          rw [div_lt_iff₀ hNR] at hk'
          nlinarith
    _ = ((Finset.univ.filter fun f : Fin n ↪ Fin N => ∀ k, f k ∈ S).card : ℝ) * B := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ) ^ n * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        have : (Finset.univ.filter fun f : Fin n ↪ Fin N => ∀ k, f k ∈ S).card ≤
            (Fintype.piFinset fun _ : Fin n => S).card := by
          refine Finset.card_le_card_of_injOn (fun f k => f k) ?_ ?_
          · intro f hf
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
            rw [Finset.mem_coe, Fintype.mem_piFinset]
            exact hf
          · intro f _ g _ h
            exact DFunLike.ext _ _ fun k => congrFun h k
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
    _ ≤ (2 * ℓ / π + 2 * D) ^ n * B :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hSc n) hB0

/-! ### Lemma 19.2 (c), (d): bounds and continuity -/

/-- Lemma 19.2 (c), (d): `|F_m| ≤ A|J|/N` with `A = 2ℓ‖O‖_∞`. -/
theorem abs_corrF_le {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {B ρO ℓ ϱ : ℝ}
    (hn : 0 < n) (hϱ : 0 < ϱ) (hρ : 0 ≤ ρO) (hρℓ : ρO ≤ ℓ * ϱ) (hB : ∀ α, |O α| ≤ B)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0)
    (J : Finset ℕ) (m : Fin n → ℕ) (x : Fin N → ℝ) :
    |corrF O ϱ J m x| ≤ 2 * ℓ * B * J.card / N := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hℓ0 : 0 ≤ ℓ := (mul_nonneg_iff_of_pos_right hϱ).mp (hρ.trans hρℓ)
  have hA : 0 ≤ 2 * ℓ * B := by positivity
  unfold corrF
  set S := J.filter (fun i => i + lastIdx m < N) with hS
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have h1 : |∑ i ∈ S, corrG O ϱ fun k => N * (extVec x (i + m k) - extVec x i)| ≤
      (S.card : ℝ) * (2 * ℓ * B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ S, |corrG O ϱ fun k => N * (extVec x (i + m k) - extVec x i)|
        ≤ ∑ i ∈ S, (2 * ℓ * B) :=
          Finset.sum_le_sum fun i _ => abs_corrG_le hn hϱ hρ hρℓ hB hsupp _
      _ = (S.card : ℝ) * (2 * ℓ * B) := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (S.card : ℝ) ≤ J.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  calc (N : ℝ)⁻¹ * |∑ i ∈ S, corrG O ϱ fun k => N * (extVec x (i + m k) - extVec x i)|
      ≤ (N : ℝ)⁻¹ * ((S.card : ℝ) * (2 * ℓ * B)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ ≤ (N : ℝ)⁻¹ * ((J.card : ℝ) * (2 * ℓ * B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hA)
          (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = 2 * ℓ * B * J.card / N := by rw [div_eq_inv_mul]; ring

private theorem corr_continuous_extVec {N : ℕ} (j : ℕ) :
    Continuous fun x : Fin N → ℝ => extVec x j := by
  unfold extVec
  by_cases h : j < N
  · simp only [h, ↓reduceDIte]
    exact continuous_apply _
  · simp only [h, ↓reduceDIte]
    exact continuous_const

/-- Lemma 19.2 (d): `F_m` is continuous on `ℝ^N`. -/
theorem continuous_corrF {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} {ρO ϱ : ℝ}
    (hn : 0 < n) (hϱ : 0 < ϱ) (hO : Continuous O)
    (hsupp : ∀ α : EuclideanSpace ℝ (Fin n), (∃ k, ρO < |α k|) → O α = 0)
    (J : Finset ℕ) (m : Fin n → ℕ) :
    Continuous (corrF (N := N) O ϱ J m) := by
  unfold corrF
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  refine (corrG_continuous hn hϱ hO hsupp).comp ?_
  refine continuous_pi fun k => continuous_const.mul ?_
  exact (corr_continuous_extVec _).sub (corr_continuous_extVec _)

/-- `(E', x) ↦ 𝒳^O_{E',ϱ}(x)` is jointly continuous. -/
theorem continuous_corrX {N n : ℕ} {O : EuclideanSpace ℝ (Fin n) → ℝ} (hO : Continuous O)
    (ϱ : ℝ) : Continuous fun p : ℝ × (Fin N → ℝ) => corrX O p.1 ϱ p.2 := by
  unfold corrX
  refine continuous_finsetSum _ fun i _ => hO.comp ?_
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_const.mul ?_)
  exact ((continuous_apply (i k)).comp continuous_snd).sub continuous_fst

end Rigidity
