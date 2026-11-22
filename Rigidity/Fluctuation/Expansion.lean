module

public import Rigidity.Fluctuation.Structure

@[expose] public section

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

open ProbabilityTheory

/-!
# The finite expansion of `1 / G_kk` and the vanishing of terms

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For `L ⊆ {1, …, N}`, `M = M^L` of (6.6) (`schurM`) and `k ∈ L`, this file formalizes Section 6.5:
* Definition 6.1: the set `𝒯(k)` of paths in `L ∖ {k}` of length `< n₀` together with the empty
  path (`faPath`), the terms `W_k(γ)` of (6.19) (`faW`) and the remainder `R_k` of (6.20) (`faR`).
  A path `(a₀, …, a_n)` is the list `[a₀, …, a_n]` of elements of `L`, the empty path is `[]`;
  so `ε(γ) = (-1)^{length γ}`, `o(γ) = length γ + 1` and `V(γ)` is the set of entries of `γ`;
* Lemma 6.9 (`inv_green_expansion`): the expansion (6.21) of `1 / G_kk`, the class `𝒜` for
  `W_k(γ)` and `R_k`, the expansion (6.22) of `X_k`, and the counts (6.23);
* Lemma 6.10 (`rowInt_lone_eq_zero`): row dependence of `W_k(γ)`, and the vanishing of
  `P_L(∏_u (Q_{k_u} W_{k_u}(γ_u))^{#_u})` under (6.25).

Every identity holds at every point `x` of the space of entries.
-/

/-! ### 1. Paths (Definition 6.1) -/

section Paths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set `𝒯(k)` of Definition 6.1 for `n₀`: the empty path `[]` and the paths
`γ = [a₀, …, a_n]` with `n < n₀`, entries `a_t ≠ k` and `a_t ≠ a_{t+1}`; that is, all lists of
length at most `n₀` with entries different from `k` and consecutive entries distinct. For `ι = L`
the entries lie in `L' = L ∖ {k}`. -/
def faPath (k : ι) (n₀ : ℕ) : Finset (List ι) :=
  ((Finset.range (n₀ + 1)).biUnion fun m =>
      (Finset.univ : Finset (Fin m → ι)).image List.ofFn).filter
    fun γ => (∀ a ∈ γ, a ≠ k) ∧ γ.IsChain (· ≠ ·)

/-- Membership in `𝒯(k)` (Definition 6.1). -/
theorem expansion_mem_faPath {k : ι} {n₀ : ℕ} {γ : List ι} :
    γ ∈ faPath k n₀ ↔ γ.length ≤ n₀ ∧ (∀ a ∈ γ, a ≠ k) ∧ γ.IsChain (· ≠ ·) := by
  simp only [faPath, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨m, hm, f, rfl⟩, h⟩
    exact ⟨by simp only [List.length_ofFn]; omega, h⟩
  · rintro ⟨hl, h⟩
    exact ⟨⟨γ.length, by omega, γ.get, List.ofFn_get γ⟩, h⟩

/-- The continuations `ρ` of length `m` of a path starting at `a`, i.e. `a :: ρ` is a path. -/
private def expansion_tails (k : ι) : ℕ → ι → Finset (List ι)
  | 0, _ => {[]}
  | m + 1, a => ((Finset.univ.erase k).erase a).biUnion fun c =>
      (expansion_tails k m c).map ⟨List.cons c, List.cons_injective⟩

private lemma expansion_mem_tails {k : ι} : ∀ {m : ℕ} {a : ι} {ρ : List ι},
    ρ ∈ expansion_tails k m a ↔ ρ.length = m ∧ (∀ b ∈ ρ, b ≠ k) ∧ (a :: ρ).IsChain (· ≠ ·)
  | 0, a, ρ => by
    cases ρ <;> simp [expansion_tails]
  | m + 1, a, ρ => by
    cases ρ with
    | nil => simp [expansion_tails]
    | cons c ρ =>
      simp only [expansion_tails, Finset.mem_biUnion, Finset.mem_map, Finset.mem_erase,
        Finset.mem_univ, Function.Embedding.coeFn_mk, List.cons.injEq, and_true,
        List.isChain_cons_cons, List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨c', ⟨hca, hck⟩, ρ', hρ', rfl, rfl⟩
        obtain ⟨h1, h2, h3⟩ := expansion_mem_tails.1 hρ'
        exact ⟨by omega, ⟨hck, h2⟩, Ne.symm hca, h3⟩
      · rintro ⟨h1, ⟨h2, h2'⟩, h3, h4⟩
        exact ⟨c, ⟨Ne.symm h3, h2⟩, ρ, expansion_mem_tails.2 ⟨by omega, h2', h4⟩, rfl, rfl⟩

private lemma expansion_sum_tails_succ {β : Type*} [AddCommMonoid β] (k : ι) (m : ℕ) (a : ι)
    (F : List ι → β) :
    ∑ ρ ∈ expansion_tails k (m + 1) a, F ρ =
      ∑ c ∈ (Finset.univ.erase k).erase a, ∑ ρ ∈ expansion_tails k m c, F (c :: ρ) := by
  rw [expansion_tails, Finset.sum_biUnion]
  · simp [Finset.sum_map]
  · intro c _ c' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ρ h1 h2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨_, _, rfl⟩ := h1
    obtain ⟨_, _, h⟩ := h2
    exact hne (List.cons.inj h).1.symm

/-- The paths of length `n` (lists with `n + 1` entries) are `a :: ρ` with `a ≠ k` and `ρ` a
continuation of length `n` of `a`. -/
private lemma expansion_sum_pi {β : Type*} [AddCommMonoid β] (k : ι) (n : ℕ)
    (F : List ι → β) :
    ∑ γ ∈ (faPath k (n + 1)).filter (fun γ => γ.length = n + 1), F γ =
      ∑ a ∈ Finset.univ.erase k, ∑ ρ ∈ expansion_tails k n a, F (a :: ρ) := by
  have hset : (faPath k (n + 1)).filter (fun γ => γ.length = n + 1) =
      (Finset.univ.erase k).biUnion fun a =>
        (expansion_tails k n a).map ⟨List.cons a, List.cons_injective⟩ := by
    ext γ
    cases γ with
    | nil => simp [expansion_mem_faPath]
    | cons a ρ =>
      simp only [Finset.mem_filter, expansion_mem_faPath, Finset.mem_biUnion, Finset.mem_erase,
        Finset.mem_univ, and_true, Finset.mem_map, Function.Embedding.coeFn_mk, List.cons.injEq,
        expansion_mem_tails, List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨-, ⟨ha, hρ⟩, hc⟩, hl⟩
        exact ⟨a, ha, ρ, ⟨by omega, hρ, hc⟩, rfl, rfl⟩
      · rintro ⟨a', ha', ρ', ⟨hl, hρ, hc⟩, rfl, rfl⟩
        exact ⟨⟨by omega, ⟨ha', hρ⟩, hc⟩, by omega⟩
  rw [hset, Finset.sum_biUnion]
  · simp [Finset.sum_map]
  · intro c _ c' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro ρ h1 h2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨_, _, rfl⟩ := h1
    obtain ⟨_, _, h⟩ := h2
    exact hne (List.cons.inj h).1.symm

private lemma expansion_faPath_zero (k : ι) : faPath k 0 = {[]} := by
  ext γ
  cases γ <;> simp [expansion_mem_faPath]

private lemma expansion_sum_faPath_succ {β : Type*} [AddCommMonoid β] (k : ι) (n : ℕ)
    (F : List ι → β) :
    ∑ γ ∈ faPath k (n + 1), F γ = ∑ γ ∈ faPath k n, F γ +
      ∑ γ ∈ (faPath k (n + 1)).filter (fun γ => γ.length = n + 1), F γ := by
  rw [← Finset.sum_filter_add_sum_filter_not (faPath k (n + 1)) (fun γ => γ.length = n + 1),
    add_comm]
  congr 2
  ext γ
  simp only [Finset.mem_filter, expansion_mem_faPath]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by omega, h2, h3⟩, by omega⟩

end Paths

/-! ### 2. The expansion for an abstract matrix -/

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mx G : ι → ι → ℂ) (k : ι) (g : ι → ℂ)

/-- `W_k(γ)` of (6.19) for a matrix `Mx`. -/
private noncomputable def expansion_W (γ : List ι) : ℂ :=
  (List.zipWith Mx (k :: γ) (γ ++ [k])).prod / (γ.map fun a => Mx a a).prod

/-- The summand of (6.20) after the sum over `b`, with `g_a = ∑_{b ≠ k} G_ab Mx_bk`. -/
private noncomputable def expansion_Rterm (γ : List ι) : ℂ :=
  (List.zipWith Mx (k :: γ) γ).prod / (γ.dropLast.map fun a => Mx a a).prod * g (γ.getLastD k)

/-- `R_k` of (6.20) for matrices `Mx`, `G`. -/
private noncomputable def expansion_R (n₀ : ℕ) : ℂ :=
  (-1) ^ n₀ * ∑ γ ∈ (faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1),
    ∑ b ∈ Finset.univ.erase k,
      (List.zipWith Mx (k :: γ) γ).prod / (γ.dropLast.map fun a => Mx a a).prod *
        G (γ.getLastD k) b * Mx b k

/-- `∏_{t<n} (Mx_{a_t a_{t+1}} / Mx_{a_t a_t}) · Mx_{a_n k} / Mx_{a_n a_n}` for the path
`a₀ = a, a₁, …, a_n`. -/
private noncomputable def expansion_chainE : ι → List ι → ℂ
  | a, [] => Mx a k / Mx a a
  | a, b :: ρ => Mx a b / Mx a a * expansion_chainE b ρ

/-- `∏_{t<n} (Mx_{a_t a_{t+1}} / Mx_{a_t a_t}) · g_{a_n}` for the path `a₀ = a, a₁, …, a_n`. -/
private noncomputable def expansion_chainU : ι → List ι → ℂ
  | a, [] => g a
  | a, b :: ρ => Mx a b / Mx a a * expansion_chainU b ρ

omit [Fintype ι] [DecidableEq ι] in
private lemma expansion_chainE_eq : ∀ (a : ι) (ρ : List ι), expansion_chainE Mx k a ρ =
    (List.zipWith Mx (a :: ρ) (ρ ++ [k])).prod / ((a :: ρ).map fun b => Mx b b).prod
  | a, [] => by simp [expansion_chainE]
  | a, b :: ρ => by
    rw [expansion_chainE, expansion_chainE_eq b ρ]
    simp only [List.cons_append, List.zipWith_cons_cons, List.prod_cons, List.map_cons]
    rw [mul_div_mul_comm]

omit [Fintype ι] [DecidableEq ι] in
private lemma expansion_chainU_eq : ∀ (a : ι) (ρ : List ι), expansion_chainU Mx g a ρ =
    (List.zipWith Mx (a :: ρ) ρ).prod / ((a :: ρ).dropLast.map fun b => Mx b b).prod *
      g ((a :: ρ).getLastD k)
  | a, [] => by simp [expansion_chainU]
  | a, b :: ρ => by
    rw [expansion_chainU, expansion_chainU_eq b ρ]
    simp only [List.zipWith_cons_cons, List.prod_cons, List.dropLast_cons_cons, List.map_cons,
      List.getLastD_cons]
    rw [mul_div_mul_comm, mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
private lemma expansion_W_nil : expansion_W Mx k [] = Mx k k := by
  simp [expansion_W]

omit [Fintype ι] [DecidableEq ι] in
private lemma expansion_W_cons (a : ι) (ρ : List ι) :
    expansion_W Mx k (a :: ρ) = Mx k a * expansion_chainE Mx k a ρ := by
  rw [expansion_chainE_eq, expansion_W]
  simp only [List.cons_append, List.zipWith_cons_cons, List.prod_cons]
  rw [mul_div_assoc]

omit [Fintype ι] [DecidableEq ι] in
private lemma expansion_Rterm_cons (a : ι) (ρ : List ι) :
    expansion_Rterm Mx k g (a :: ρ) = Mx k a * expansion_chainU Mx g a ρ := by
  rw [expansion_chainU_eq Mx k, expansion_Rterm]
  simp only [List.zipWith_cons_cons, List.prod_cons]
  rw [mul_div_assoc, mul_assoc]

variable {Mx k g}

/-- One step of the expansion: substituting `g_a = Mx_ak / Mx_aa - ∑_{c ≠ a, k} (Mx_ac / Mx_aa) g_c`
at the end of the paths of length `m` starting at `a`. -/
private lemma expansion_step (hdiag : ∀ a, a ≠ k → Mx a a ≠ 0)
    (hkey : ∀ a, a ≠ k → ∑ c ∈ Finset.univ.erase k, Mx a c * g c = Mx a k) :
    ∀ (m : ℕ) (a : ι), a ≠ k →
      ∑ ρ ∈ expansion_tails k m a, expansion_chainU Mx g a ρ =
        ∑ ρ ∈ expansion_tails k m a, expansion_chainE Mx k a ρ -
          ∑ ρ ∈ expansion_tails k (m + 1) a, expansion_chainU Mx g a ρ
  | 0, a, ha => by
    rw [expansion_sum_tails_succ]
    simp only [expansion_tails, Finset.sum_singleton, expansion_chainU, expansion_chainE]
    have h := hkey a ha
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩)] at h
    have hd := hdiag a ha
    have hs : ∑ c ∈ (Finset.univ.erase k).erase a, Mx a c / Mx a a * g c =
        (∑ c ∈ (Finset.univ.erase k).erase a, Mx a c * g c) / Mx a a := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hs, ← sub_div, eq_div_iff hd, ← h]
    ring
  | m + 1, a, ha => by
    rw [expansion_sum_tails_succ, expansion_sum_tails_succ, expansion_sum_tails_succ k (m + 1),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hck : c ≠ k := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hc)).1
    simp only [expansion_chainU, expansion_chainE, ← Finset.mul_sum]
    rw [expansion_step hdiag hkey m c hck, mul_sub]

/-- The expansion (6.21) for an abstract matrix: from `Mx_aa ≠ 0` and
`∑_{c ≠ k} Mx_ac g_c = Mx_ak` for `a ≠ k`. -/
private lemma expansion_of_key (hdiag : ∀ a, a ≠ k → Mx a a ≠ 0)
    (hkey : ∀ a, a ≠ k → ∑ c ∈ Finset.univ.erase k, Mx a c * g c = Mx a k) (n₀ : ℕ) :
    Mx k k - ∑ a ∈ Finset.univ.erase k, Mx k a * g a =
      ∑ γ ∈ faPath k n₀, (-1) ^ γ.length * expansion_W Mx k γ -
        (-1) ^ n₀ * ∑ γ ∈ (faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1),
          expansion_Rterm Mx k g γ := by
  set S : ℕ → ℂ := fun m => ∑ a ∈ Finset.univ.erase k,
    Mx k a * ∑ ρ ∈ expansion_tails k m a, expansion_chainU Mx g a ρ with hS
  set E : ℕ → ℂ := fun m => ∑ a ∈ Finset.univ.erase k,
    Mx k a * ∑ ρ ∈ expansion_tails k m a, expansion_chainE Mx k a ρ with hE
  have hstep : ∀ m, S m = E m - S (m + 1) := fun m => by
    simp only [hS, hE, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.sum_congr rfl fun a ha =>
      by rw [expansion_step hdiag hkey m a (Finset.mem_erase.1 ha).1]
  have hR : ∀ n, ∑ γ ∈ (faPath k (n + 1)).filter (fun γ => γ.length = n + 1),
      expansion_Rterm Mx k g γ = S n := fun n => by
    rw [expansion_sum_pi]
    simp only [expansion_Rterm_cons, ← Finset.mul_sum, hS]
  have hWs : ∀ n, ∑ γ ∈ (faPath k (n + 1)).filter (fun γ => γ.length = n + 1),
      (-1) ^ γ.length * expansion_W Mx k γ = (-1) ^ (n + 1) * E n := fun n => by
    rw [expansion_sum_pi]
    simp only [expansion_W_cons, List.length_cons, hE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ρ hρ => ?_
    rw [(expansion_mem_tails.1 hρ).1]
  have h0 : S 0 = ∑ a ∈ Finset.univ.erase k, Mx k a * g a := by
    simp [hS, expansion_tails, expansion_chainU]
  rw [hR, ← h0]
  induction n₀ with
  | zero => simp [expansion_faPath_zero, expansion_W_nil]
  | succ n ih =>
    rw [expansion_sum_faPath_succ, hWs, hstep n] at *
    rw [ih, hstep (n + 1)]
    ring

/-- The expansion (6.21) for an abstract matrix, from `Mx_aa ≠ 0` and from `G` being the inverse
of `(Mx_ab)_{a,b ≠ k}`. -/
private lemma expansion_of_inv (hdiag : ∀ a, a ≠ k → Mx a a ≠ 0)
    (hinv : ∀ a b, a ≠ k → b ≠ k →
      ∑ c ∈ Finset.univ.erase k, Mx a c * G c b = if a = b then 1 else 0) (n₀ : ℕ) :
    Mx k k - ∑ a ∈ Finset.univ.erase k, ∑ b ∈ Finset.univ.erase k, Mx k a * G a b * Mx b k =
      ∑ γ ∈ faPath k n₀, (-1) ^ γ.length * expansion_W Mx k γ - expansion_R Mx G k n₀ := by
  set g : ι → ℂ := fun a => ∑ b ∈ Finset.univ.erase k, G a b * Mx b k with hg
  have hkey : ∀ a, a ≠ k → ∑ c ∈ Finset.univ.erase k, Mx a c * g c = Mx a k := fun a ha => by
    have hamem : a ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩
    calc ∑ c ∈ Finset.univ.erase k, Mx a c * g c
        = ∑ b ∈ Finset.univ.erase k, (∑ c ∈ Finset.univ.erase k, Mx a c * G c b) * Mx b k := by
          simp only [hg, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
      _ = ∑ b ∈ Finset.univ.erase k, (if a = b then Mx b k else 0) := by
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [hinv a b ha (Finset.mem_erase.1 hb).1]
          split_ifs <;> simp
      _ = Mx a k := by simp [Finset.sum_ite_eq, hamem]
  have h := expansion_of_key hdiag hkey n₀
  have hl : ∑ a ∈ Finset.univ.erase k, ∑ b ∈ Finset.univ.erase k, Mx k a * G a b * Mx b k =
      ∑ a ∈ Finset.univ.erase k, Mx k a * g a := by
    simp only [hg, Finset.mul_sum, mul_assoc]
  have hr : expansion_R Mx G k n₀ = (-1) ^ n₀ *
      ∑ γ ∈ (faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1),
        expansion_Rterm Mx k g γ := by
    simp only [expansion_R, expansion_Rterm, hg, Finset.mul_sum, mul_assoc]
  rw [hl, hr, h]

end Abstract

/-! ### 3. The terms `W_k(γ)` and the remainder `R_k` (Definition 6.1) -/

/-- `W_k(γ)` of (6.19), with `M = M^L` of (6.6): for the path `γ = [a₀, …, a_n]` the product
`M_{ka₀} M_{a₀a₁} ⋯ M_{a_{n-1}a_n} M_{a_nk}` of the entries along `k, a₀, …, a_n, k`, divided by
`M_{a₀a₀} ⋯ M_{a_na_n}`; for the empty path `γ = []` it is `M_kk`. -/
noncomputable def faW {N : ℕ} (L : Finset (Fin N)) (z : ℂ) (k : L) (γ : List L)
    (x : Pair N → 𝕜) : ℂ :=
  (List.zipWith (fun a b => schurM (toMatrix x) L z a b) (k :: γ) (γ ++ [k])).prod /
    (γ.map fun a => schurM (toMatrix x) L z a a).prod

/-- The remainder `R_k` of (6.20), with `M = M^L` of (6.6) and `G^{(k)}` the resolvent of the minor
`H^{(k)}`: `(-1)^{n₀}` times the sum over the paths `γ = [a₀, …, a_{n₀}]` of length `n₀` (lists with
`n₀ + 1` entries, entries `≠ k`, consecutive entries distinct) and over `b ∈ L ∖ {k}` of
`M_{ka₀} M_{a₀a₁} ⋯ M_{a_{n₀-1}a_{n₀}} / (M_{a₀a₀} ⋯ M_{a_{n₀-1}a_{n₀-1}})` times
`G^{(k)}_{a_{n₀}b} M_{bk}`.
It is `0` for `L = {k}`. -/
noncomputable def faR {N : ℕ} (L : Finset (Fin N)) (z : ℂ) (k : L) (n₀ : ℕ)
    (x : Pair N → 𝕜) : ℂ :=
  (-1) ^ n₀ * ∑ γ ∈ (faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1),
    ∑ b ∈ Finset.univ.erase k,
      (List.zipWith (fun a c => schurM (toMatrix x) L z a c) (k :: γ) γ).prod /
        (γ.dropLast.map fun a => schurM (toMatrix x) L z a a).prod *
        greenT (toMatrix x) {k.1} z (γ.getLastD k).1 b.1 * schurM (toMatrix x) L z b k

/-! ### 4. The expansion (6.21) -/

section Identity

variable {N : ℕ}

/-- Sums over `L ∖ {k}` as a subtype of `Fin N` are sums over `L ∖ {k}` as a subset of `L`. -/
private lemma expansion_sum_erase (L : Finset (Fin N)) (k : L) (F : L → ℂ) :
    ∑ a : L.erase k.1, F ⟨a.1, Finset.mem_of_mem_erase a.2⟩ = ∑ a ∈ Finset.univ.erase k, F a := by
  refine Finset.sum_bij' (fun a _ => ⟨a.1, Finset.mem_of_mem_erase a.2⟩)
    (fun a ha => ⟨a.1, Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 ha).1 (Subtype.ext h),
      a.2⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro a _
    refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_univ _⟩
    exact (Finset.mem_erase.1 a.2).1 (congrArg Subtype.val h)
  · intro a _
    exact Finset.mem_univ _
  · intro a _
    rfl
  · intro a _
    rfl
  · intro a _
    rfl

/-- Lemma 6.4 (a) in the form used for (6.21): `M_aa ≠ 0`, `(G^{(k)}_ab)_{a,b ≠ k}` is the inverse
of `(M_ab)_{a,b ≠ k}`, and (6.8) with the sums over `L ∖ {k}` as a subset of `L`. -/
private lemma expansion_block {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N)) (k : L)
    (x : Pair N → 𝕜) :
    (∀ a : L, a ≠ k → schurM (toMatrix x) L z a a ≠ 0) ∧
    (∀ a b : L, a ≠ k → b ≠ k → ∑ c ∈ Finset.univ.erase k,
      schurM (toMatrix x) L z a c * greenT (toMatrix x) {k.1} z c.1 b.1 =
        if a = b then 1 else 0) ∧
    1 / green (toMatrix x) z k.1 k.1 = schurM (toMatrix x) L z k k -
      ∑ a ∈ Finset.univ.erase k, ∑ b ∈ Finset.univ.erase k,
        schurM (toMatrix x) L z k a * greenT (toMatrix x) {k.1} z a.1 b.1 *
          schurM (toMatrix x) L z b k := by
  obtain ⟨-, hd, h1, hr⟩ := schurM_inv hz L x
  refine ⟨fun a _ => (hd a.1 a.2).2.1, fun a b ha hb => ?_, ?_⟩
  · have ha' : a.1 ∈ L.erase k.1 := Finset.mem_erase.2 ⟨fun h => ha (Subtype.ext h), a.2⟩
    have hb' : b.1 ∈ L.erase k.1 := Finset.mem_erase.2 ⟨fun h => hb (Subtype.ext h), b.2⟩
    obtain ⟨hU, hinv, -, -⟩ := hr k.1 k.2 ⟨a.1, ha'⟩
    have hmul := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
    rw [hinv] at hmul
    have he := congrFun (congrFun hmul ⟨a.1, ha'⟩) ⟨b.1, hb'⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at he
    simp only [Matrix.of_apply] at he
    rw [← expansion_sum_erase L k
      (fun c => schurM (toMatrix x) L z a c * greenT (toMatrix x) {k.1} z c.1 b.1), he]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : ¬ (⟨a.1, ha'⟩ : L.erase k.1) = ⟨b.1, hb'⟩ := fun h =>
        hab (Subtype.ext (by simpa using congrArg Subtype.val h))
      simp [hab, hne]
  · by_cases hne : (L.erase k.1).Nonempty
    · obtain ⟨-, -, -, hform⟩ := hr k.1 k.2 hne
      rw [hform]
      congr 1
      rw [← expansion_sum_erase L k]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← expansion_sum_erase L k]
    · have hE : (Finset.univ.erase k : Finset L) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun a ha => hne ⟨a.1, ?_⟩
        exact Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 ha).1 (Subtype.ext h), a.2⟩
      rw [hE, Finset.sum_empty, sub_zero]
      have hL : L = {k.1} := by
        ext i
        refine ⟨fun hi => ?_, fun hi => ?_⟩
        · by_contra hik
          exact hne ⟨i, Finset.mem_erase.2 ⟨by simpa using hik, hi⟩⟩
        · rw [Finset.mem_singleton.1 hi]
          exact k.2
      obtain ⟨k, hk⟩ := k
      simp only at hL
      subst hL
      exact h1 k

/-- (6.21) at a point. -/
private lemma expansion_identity {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N)) (k : L) (n₀ : ℕ)
    (x : Pair N → 𝕜) :
    1 / green (toMatrix x) z k.1 k.1 =
      ∑ γ ∈ faPath k n₀, (-1) ^ γ.length * faW L z k γ x - faR L z k n₀ x := by
  obtain ⟨hdiag, hinv, h68⟩ := expansion_block hz L k x
  rw [h68]
  exact expansion_of_inv (Mx := fun a b => schurM (toMatrix x) L z a b)
    (G := fun a b => greenT (toMatrix x) {k.1} z a.1 b.1) hdiag hinv n₀

end Identity

/-! ### 5. Integrable slices and linearity of `P_T` (Lemma 6.3 (F0)) -/

section Slices

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `1 + ∑ aᵢ ≤ ∏ (1 + aᵢ)` for nonnegative `aᵢ`. -/
private lemma expansion_one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
    have h2 := ha i
    nlinarith [mul_nonneg h2 h1, mul_nonneg h2 (sub_nonneg.2 ih)]

/-- `(1 + a)^m ≤ 2^m (1 + a^m)` for `a ≥ 0`. -/
private lemma expansion_one_add_pow_le {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (1 + a) ^ m ≤ 2 ^ m * (1 + a ^ m) := by
  have hp : 0 ≤ a ^ m := pow_nonneg ha m
  by_cases h : a ≤ 1
  · calc (1 + a) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + a ^ m) := le_mul_of_one_le_right (by positivity) (by linarith)
  · replace h := not_le.1 h
    calc (1 + a) ^ m ≤ (2 * a) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * a ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + a ^ m) := by gcongr; linarith

/-- Every power of `1 + |y|` is integrable against an entry law (Lemma 4.1 (a)). -/
private lemma expansion_integrable_one_add_norm_pow {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (p : Pair N) (m : ℕ) :
    Integrable (fun y : 𝕜 => (1 + ‖y‖) ^ m) (M.law p) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hϑ' : 0 < min ϑ 1 := lt_min hϑ one_pos
    have hM' := Ensemble.Assumptions.mono M hM hϑ' (min_le_left _ _) le_rfl le_rfl le_rfl
    have hmom := (moments_bound hϑ' (min_le_right _ _) (μ := M.law p)
      (s := Real.sqrt (M.varPair p)) (Real.sqrt_nonneg _) (hM'.subexp p)
      (q := (m : ℝ)) (by exact_mod_cast hm)).1
    simp only [Real.rpow_natCast] at hmom
    have hdom : Integrable (fun y : 𝕜 => (2 : ℝ) ^ m * (1 + ‖y‖ ^ m)) (M.law p) :=
      ((integrable_const (1 : ℝ)).add hmom).const_mul _
    refine hdom.mono' ((measurable_const.add measurable_norm).pow_const m).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact expansion_one_add_pow_le (norm_nonneg y) m

variable (J : Set (Pair N)) [DecidablePred (· ∈ J)]

/-- `piMerge` is jointly measurable in `(x, y)`. -/
private lemma expansion_measurable_merge :
    Measurable (fun p : (Pair N → 𝕜) × (J → 𝕜) => piMerge J p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ J
  · have : (fun p : (Pair N → 𝕜) × (J → 𝕜) => piMerge J p.1 p.2 i) = fun p => p.2 ⟨i, h⟩ := by
      funext p
      simp [piMerge, h]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_snd
  · have : (fun p : (Pair N → 𝕜) × (J → 𝕜) => piMerge J p.1 p.2 i) = fun p => p.1 i := by
      funext p
      simp [piMerge, h]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst

/-- For fixed `x`, `y ↦ piMerge J x y` is measurable. -/
private lemma expansion_measurable_merge_right (x : Pair N → 𝕜) :
    Measurable (fun y : J → 𝕜 => piMerge J x y) :=
  (expansion_measurable_merge J).comp (measurable_const.prodMk measurable_id)

/-- The coordinates of `piMerge J x y` are bounded by those of `x` and `y`. -/
private lemma expansion_sum_norm_merge_le (x : Pair N → 𝕜) (y : J → 𝕜) :
    ∑ p, ‖piMerge J x y p‖ ≤ ∑ p, ‖x p‖ + ∑ q : J, ‖y q‖ := by
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun p => ‖piMerge J x y p‖)]
  have h1 : ∑ i : {p // p ∈ J}, ‖piMerge J x y i‖ = ∑ q : J, ‖y q‖ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [piMerge, i.2]
  have h2 : ∑ i : {p // ¬ p ∈ J}, ‖piMerge J x y i‖ ≤ ∑ p, ‖x p‖ := by
    have h3 : ∑ i : {p // ¬ p ∈ J}, ‖piMerge J x y i‖ = ∑ i : {p // ¬ p ∈ J}, ‖x i‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [piMerge, i.2]
    have h4 := Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun p => ‖x p‖)
    have h5 : 0 ≤ ∑ i : {p // p ∈ J}, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  linarith

/-- The polynomial bound along a slice `y ↦ f (piMerge J x y)`. -/
private lemma expansion_norm_merge_le {f : (Pair N → 𝕜) → ℂ} {c : ℝ} (hc : 0 ≤ c) {m : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m) (x : Pair N → 𝕜) (y : J → 𝕜) :
    ‖f (piMerge J x y)‖ ≤ c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m := by
  have ha : 0 ≤ ∑ p, ‖x p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb : 0 ≤ ∑ q : J, ‖y q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : 1 + ∑ p, ‖piMerge J x y p‖ ≤ (1 + ∑ p, ‖x p‖) * (1 + ∑ q : J, ‖y q‖) := by
    nlinarith [expansion_sum_norm_merge_le J x y, mul_nonneg ha hb]
  have h2 : 1 + ∑ q : J, ‖y q‖ ≤ ∏ q : J, (1 + ‖y q‖) := by
    simpa using expansion_one_add_sum_le_prod_one_add Finset.univ (fun q : J => ‖y q‖)
      (fun _ => norm_nonneg _)
  have hs : 0 ≤ ∑ p, ‖piMerge J x y p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ‖f (piMerge J x y)‖ ≤ c * (1 + ∑ p, ‖piMerge J x y p‖) ^ m := hf _
    _ ≤ c * ((1 + ∑ p, ‖x p‖) * (∏ q : J, (1 + ‖y q‖))) ^ m := by
        gcongr
        exact h1.trans (by gcongr)
    _ = c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m := by
        rw [mul_pow, Finset.prod_pow]; ring

/-- The dominating function of a slice is integrable. -/
private lemma expansion_integrable_prod_one_add_pow {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (m : ℕ) :
    Integrable (fun y : J → 𝕜 => ∏ q : J, (1 + ‖y q‖) ^ m) (Measure.pi fun p : J => M.law p) :=
  Integrable.fintype_prod (f := fun (_ : J) (z : 𝕜) => (1 + ‖z‖) ^ m)
    (μ := fun q : J => M.law q) fun q => expansion_integrable_one_add_norm_pow M hM hϑ q m

/-- Every slice of a function of `𝒜` is integrable (Lemma 6.3 (F0)). -/
private lemma expansion_integrable_slice {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀)
    (hϑ : 0 < ϑ) {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (x : Pair N → 𝕜) :
    Integrable (fun y : J → 𝕜 => f (piMerge J x y)) (Measure.pi fun p : J => M.law p) := by
  obtain ⟨hfm, c₀, m, hb₀⟩ := hf
  have hc : 0 ≤ |c₀| := abs_nonneg _
  have hb : ∀ x, ‖f x‖ ≤ |c₀| * (1 + ∑ p, ‖x p‖) ^ m := fun x =>
    (hb₀ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  set c := |c₀|
  have hdom : Integrable (fun y : J → 𝕜 => c * (1 + ∑ p, ‖x p‖) ^ m * ∏ q : J, (1 + ‖y q‖) ^ m)
      (Measure.pi fun p : J => M.law p) :=
    (expansion_integrable_prod_one_add_pow M J hM hϑ m).const_mul _
  exact hdom.mono' (hfm.comp (expansion_measurable_merge_right J x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => expansion_norm_merge_le J hc hb x y)

/-- `P_T` is additive on `𝒜`. -/
private lemma expansion_rowInt_sub {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (T : Finset (Fin N)) {f g : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (hg : PolyGrowth g)
    (x : Pair N → 𝕜) :
    rowInt M T (fun w => f w - g w) x = rowInt M T f x - rowInt M T g x := by
  unfold rowInt partialInt
  exact integral_sub (expansion_integrable_slice M (rowsQ T) hM hϑ hf x)
    (expansion_integrable_slice M (rowsQ T) hM hϑ hg x)

/-- `P_T` commutes with finite sums on `𝒜`. -/
private lemma expansion_rowInt_sum {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
    (T : Finset (Fin N)) {α : Type*} (s : Finset α) {F : α → (Pair N → 𝕜) → ℂ}
    (hF : ∀ a ∈ s, PolyGrowth (F a)) (x : Pair N → 𝕜) :
    rowInt M T (fun w => ∑ a ∈ s, F a w) x = ∑ a ∈ s, rowInt M T (F a) x := by
  unfold rowInt partialInt
  exact integral_finsetSum s fun a ha => expansion_integrable_slice M (rowsQ T) hM hϑ (hF a ha) x

/-- `P_T (c f) = c P_T f` for a constant `c`. -/
private lemma expansion_rowInt_const_mul (T : Finset (Fin N)) (c : ℂ) (f : (Pair N → 𝕜) → ℂ)
    (x : Pair N → 𝕜) : rowInt M T (fun w => c * f w) x = c * rowInt M T f x :=
  rowInt_mul_left M T (g := fun _ => c) (fun _ _ _ => rfl) f x

/-- `P_T` commutes with complex conjugation (Lemma 6.3 (F0)). -/
private lemma expansion_rowInt_conj (T : Finset (Fin N)) (f : (Pair N → 𝕜) → ℂ)
    (x : Pair N → 𝕜) :
    rowInt M T (fun w => starRingEnd ℂ (f w)) x = starRingEnd ℂ (rowInt M T f x) := by
  unfold rowInt partialInt
  exact integral_conj

/-- If `f` does not depend on `𝒬(S)`, neither does `P_T f` (Lemma 6.3 (F0)). -/
private lemma expansion_rowInt_noDep (T S : Finset (Fin N)) {f : (Pair N → 𝕜) → ℂ}
    (hf : ∀ x x', (∀ p, p ∉ rowsQ S → x p = x' p) → f x = f x') :
    ∀ x x', (∀ p, p ∉ rowsQ S → x p = x' p) → rowInt M T f x = rowInt M T f x' := by
  intro x x' h
  unfold rowInt partialInt
  congr 1
  funext y
  refine hf _ _ fun p hp => ?_
  unfold piMerge
  split_ifs
  · rfl
  · exact h p hp

end Slices

/-! ### 6. The class `𝒜` -/

section Growth

variable {N : ℕ}

private lemma expansion_pg_const (c : ℂ) : PolyGrowth (fun _ : Pair N → 𝕜 => c) :=
  ⟨measurable_const, ‖c‖, 0, fun _ => by simp⟩

private lemma expansion_pg_sub {f g : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun x => f x - g x) := by
  have h := hf.add ((expansion_pg_const (-1)).mul hg)
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

private lemma expansion_pg_sum {α : Type*} (s : Finset α) {F : α → (Pair N → 𝕜) → ℂ}
    (hF : ∀ a ∈ s, PolyGrowth (F a)) : PolyGrowth (fun x => ∑ a ∈ s, F a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expansion_pg_const (N := N) (𝕜 := 𝕜) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

private lemma expansion_pg_prod {α : Type*} (s : Finset α) {F : α → (Pair N → 𝕜) → ℂ}
    (hF : ∀ a ∈ s, PolyGrowth (F a)) : PolyGrowth (fun x => ∏ a ∈ s, F a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expansion_pg_const (N := N) (𝕜 := 𝕜) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).mul
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

private lemma expansion_pg_listProd {α : Type*} (l : List α) {F : α → (Pair N → 𝕜) → ℂ}
    (hF : ∀ a, PolyGrowth (F a)) : PolyGrowth (fun x => (l.map fun a => F a x).prod) := by
  induction l with
  | nil => simpa using expansion_pg_const (N := N) (𝕜 := 𝕜) 1
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF a).mul ih

private lemma expansion_pg_zipWith {α β : Type*} (l₁ : List α) (l₂ : List β)
    {F : α → β → (Pair N → 𝕜) → ℂ} (hF : ∀ a b, PolyGrowth (F a b)) :
    PolyGrowth (fun x => (List.zipWith (fun a b => F a b x) l₁ l₂).prod) := by
  induction l₁ generalizing l₂ with
  | nil => simpa using expansion_pg_const (N := N) (𝕜 := 𝕜) 1
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simpa using expansion_pg_const (N := N) (𝕜 := 𝕜) 1
    | cons b l₂ =>
      simp only [List.zipWith_cons_cons, List.prod_cons]
      exact (hF a b).mul (ih l₂)

private lemma expansion_one_div_listProd {α : Type*} (l : List α) (F : α → ℂ) :
    1 / (l.map F).prod = (l.map fun a => 1 / F a).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih,
      one_div_mul_one_div]

/-- `W_k(γ)` and `R_k` are in the class `𝒜` (Lemma 6.9). -/
private lemma expansion_pg (M : Ensemble 𝕜 N) {z : ℂ} (hz : 0 < z.im) (L : Finset (Fin N))
    (k : L) (n₀ : ℕ) :
    (∀ γ : List L, PolyGrowth (faW (𝕜 := 𝕜) L z k γ)) ∧ PolyGrowth (faR (𝕜 := 𝕜) L z k n₀) := by
  have h := polyGrowth_schurM M 0 hz L
  have hM : ∀ a b : L, PolyGrowth (fun x : Pair N → 𝕜 => schurM (toMatrix x) L z a b) :=
    fun a b => (h.1 a.1 b.1 a.2 b.2).2
  have hD : ∀ a : L, PolyGrowth (fun x : Pair N → 𝕜 => 1 / schurM (toMatrix x) L z a a) :=
    fun a => (h.2.1 a.1 a.2).2
  have hdiv : ∀ (l : List L) {f : (Pair N → 𝕜) → ℂ}, PolyGrowth f →
      PolyGrowth (fun x => f x / (l.map fun a => schurM (toMatrix x) L z a a).prod) := by
    intro l f hf
    have := hf.mul (expansion_pg_listProd l hD)
    simp only [← expansion_one_div_listProd, ← div_eq_mul_one_div] at this
    exact this
  refine ⟨fun γ => hdiv γ (expansion_pg_zipWith _ _ hM), ?_⟩
  refine (expansion_pg_const _).mul (expansion_pg_sum _ fun γ _ => expansion_pg_sum _ fun b _ => ?_)
  exact ((hdiv _ (expansion_pg_zipWith _ _ hM)).mul (h.2.2.1 k.1 _ _).2).mul (hM b k)

end Growth

/-! ### 7. Counting paths (6.23) -/

private lemma expansion_card_length_le {ι : Type*} [Fintype ι] (s : Finset (List ι)) (m : ℕ)
    (P : List ι → Prop) [DecidablePred P] (hP : ∀ γ, P γ → γ.length = m) :
    (s.filter P).card ≤ Fintype.card ι ^ m := by
  classical
  have hsub : s.filter P ⊆ (Finset.univ : Finset (Fin m → ι)).image List.ofFn := by
    intro γ hγ
    have hl := hP γ (Finset.mem_filter.1 hγ).2
    subst hl
    exact Finset.mem_image.2 ⟨γ.get, Finset.mem_univ _, List.ofFn_get γ⟩
  calc (s.filter P).card ≤ ((Finset.univ : Finset (Fin m → ι)).image List.ofFn).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin m → ι)).card := Finset.card_image_le
    _ = Fintype.card ι ^ m := by simp

/-! ### 8. Lemma 6.9 -/

/-- Lemma 6.9, with `M = M^L` of (6.6), `k ∈ L`, `𝒯(k)` = `faPath k n₀`, `ε(γ) = (-1)^{length γ}`,
`o(γ) = length γ + 1`, `V(γ)` the set of entries of `γ`, `r = |L|`, `P_k` = `rowInt M {k}` and
`Q_k f = f - P_k f`; for every `n₀`:
* (6.21): `1 / G_kk = ∑_{γ ∈ 𝒯(k)} ε(γ) W_k(γ) - R_k` at every point;
* `W_k(γ)` (for every list `γ` of elements of `L`) and `R_k` are in the class `𝒜` of (6.4);
* (6.22): `X_k = ∑_{γ ∈ 𝒯(k)} ε(γ) Q_k W_k(γ) - Q_k R_k` at every point;
* (6.23): `o(γ) ≥ |V(γ)| + 1` for `γ ∈ 𝒯(k)`, `#{γ ∈ 𝒯(k) : o(γ) = o} ≤ r^{o-1}`, and
  `|Π_{n₀}(k)| · |L ∖ {k}| ≤ r^{n₀+2}`, where `Π_{n₀}(k)` is the set of paths of length `n₀`
  (lists with `n₀ + 1` entries). -/
theorem inv_green_expansion {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) (k : L) (n₀ : ℕ) :
    (∀ x : Pair N → 𝕜, 1 / green (toMatrix x) z k.1 k.1 =
      ∑ γ ∈ faPath k n₀, (-1) ^ γ.length * faW L z k γ x - faR L z k n₀ x) ∧
    (∀ γ : List L, PolyGrowth (faW (𝕜 := 𝕜) L z k γ)) ∧ PolyGrowth (faR (𝕜 := 𝕜) L z k n₀) ∧
    (∀ x : Pair N → 𝕜, selfX (toMatrix x) M.varMatrix z k.1 =
      ∑ γ ∈ faPath k n₀, (-1) ^ γ.length *
        (faW L z k γ x - rowInt M {k.1} (faW L z k γ) x) -
        (faR L z k n₀ x - rowInt M {k.1} (faR L z k n₀) x)) ∧
    (∀ γ ∈ faPath k n₀, γ.toFinset.card + 1 ≤ γ.length + 1) ∧
    (∀ o : ℕ, ((faPath k n₀).filter (fun γ => γ.length + 1 = o)).card ≤ L.card ^ (o - 1)) ∧
    ((faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1)).card * (L.erase k.1).card ≤
      L.card ^ (n₀ + 2) := by
  obtain ⟨hW, hR⟩ := expansion_pg M hz L k n₀
  have hS : PolyGrowth (fun w : Pair N → 𝕜 =>
      ∑ γ ∈ faPath k n₀, (-1) ^ γ.length * faW L z k γ w) :=
    expansion_pg_sum _ fun γ _ => (expansion_pg_const _).mul (hW γ)
  refine ⟨expansion_identity hz L k n₀, hW, hR, fun x => ?_, fun γ _ => ?_, fun o => ?_, ?_⟩
  · have hfun : (fun w : Pair N → 𝕜 => 1 / green (toMatrix w) z k.1 k.1) = fun w =>
        (∑ γ ∈ faPath k n₀, (-1) ^ γ.length * faW L z k γ w) - faR L z k n₀ w :=
      funext fun w => expansion_identity hz L k n₀ w
    rw [selfX_eq_rowInt M hM hz k.1 x, hfun, expansion_identity hz L k n₀ x,
      expansion_rowInt_sub M hM hϑ _ hS hR,
      expansion_rowInt_sum M hM hϑ _ _ fun γ _ => (expansion_pg_const _).mul (hW γ)]
    simp only [expansion_rowInt_const_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  · have := List.toFinset_card_le γ
    omega
  · calc ((faPath k n₀).filter (fun γ => γ.length + 1 = o)).card
        ≤ Fintype.card L ^ (o - 1) :=
          expansion_card_length_le _ _ _ fun γ h => by omega
      _ = L.card ^ (o - 1) := by rw [Fintype.card_coe]
  · have h1 : ((faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1)).card ≤
        L.card ^ (n₀ + 1) := by
      rw [← Fintype.card_coe L]
      exact expansion_card_length_le _ _ _ fun γ h => h
    calc ((faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1)).card * (L.erase k.1).card
        ≤ L.card ^ (n₀ + 1) * L.card := Nat.mul_le_mul h1 (Finset.card_erase_le)
      _ = L.card ^ (n₀ + 2) := by ring

/-! ### 9. Lemma 6.10 -/

private lemma expansion_zipWith_congr {α β δ : Type*} (f f' : α → β → δ) :
    ∀ (l₁ : List α) (l₂ : List β), (∀ a ∈ l₁, ∀ b ∈ l₂, f a b = f' a b) →
      List.zipWith f l₁ l₂ = List.zipWith f' l₁ l₂
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons,
      h a List.mem_cons_self b List.mem_cons_self,
      expansion_zipWith_congr f f' l₁ l₂ fun a ha b hb =>
        h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)]

/-- Lemma 6.10 (a) for `W_k(γ)`: its factors `M_ab`, `1 / M_aa` have `a, b ∈ {k} ∪ V(γ)`. -/
private lemma expansion_faW_noDep {N : ℕ} {L : Finset (Fin N)} {z : ℂ} (k : L) (γ : List L)
    (c : L) (hck : c ≠ k) (hcγ : c ∉ γ) :
    ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ {c.1} → x p = x' p) →
      faW L z k γ x = faW L z k γ x' := by
  intro x x' h
  have hne : ∀ a : L, a ∈ k :: γ → c.1 ≠ a.1 := fun a ha hca => by
    rcases List.mem_cons.1 ha with ha | ha
    · exact hck ((Subtype.ext hca).trans ha)
    · exact hcγ (Subtype.ext hca ▸ ha)
  have hM : ∀ a b : L, a ∈ k :: γ → b ∈ k :: γ →
      schurM (toMatrix x) L z a b = schurM (toMatrix x') L z a b := fun a b ha hb =>
    (noDep_schurM L z a.2 b.2).1 c.1 c.2 (hne a ha) (hne b hb) x x' h
  unfold faW
  rw [expansion_zipWith_congr _ _ (k :: γ) (γ ++ [k]) fun a ha b hb =>
      hM a b ha (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at hb ⊢; tauto),
    List.map_congr_left fun a ha => hM a a (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ ha)]

/-- Lemma 6.10, with `M = M^L` of (6.6), `P_T` = `rowInt M T` and `Q_k f = f - P_k f`:
* (a) for `k, c ∈ L` and a list `γ` of elements of `L` with `c ∉ {k} ∪ V(γ)`, the functions
  `W_k(γ)` and `Q_k W_k(γ)` do not depend on `𝒬({c})`;
* (b) for `k_1, …, k_j ∈ L`, lists `γ_1, …, γ_j` of elements of `L` and `f^{#_u}` equal to
  `f` or to its complex conjugate, if (6.25) holds for some `s` (`k_s ≠ k_u` and `k_s ∉ V(γ_u)`
  for all `u ≠ s`), then `P_L(∏_u (Q_{k_u} W_{k_u}(γ_u))^{#_u}) = 0` at every point.
NP states (a), (b) for `γ ∈ 𝒯(k)`; only the entries of `γ` enter. -/
theorem rowInt_lone_eq_zero {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) {z : ℂ} (hz : 0 < z.im)
    (L : Finset (Fin N)) :
    (∀ (k : L) (γ : List L) (c : L), c ≠ k → c ∉ γ →
      ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ {c.1} → x p = x' p) →
        faW L z k γ x = faW L z k γ x' ∧
        faW L z k γ x - rowInt M {k.1} (faW L z k γ) x =
          faW L z k γ x' - rowInt M {k.1} (faW L z k γ) x') ∧
    (∀ (j : ℕ) (k : Fin j → L) (γ : Fin j → List L) (flag : Fin j → Bool),
      (∃ s, ∀ u, u ≠ s → k s ≠ k u ∧ k s ∉ γ u) →
      ∀ x : Pair N → 𝕜,
        rowInt M L (fun w => ∏ u, (if flag u then starRingEnd ℂ else RingHom.id ℂ)
          (faW L z (k u) (γ u) w - rowInt M {(k u).1} (faW L z (k u) (γ u)) w)) x = 0) := by
  have hA : ∀ (k : L) (γ : List L) (c : L), c ≠ k → c ∉ γ →
      ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ {c.1} → x p = x' p) →
        faW L z k γ x = faW L z k γ x' ∧
        faW L z k γ x - rowInt M {k.1} (faW L z k γ) x =
          faW L z k γ x' - rowInt M {k.1} (faW L z k γ) x' := fun k γ c hck hcγ x x' h =>
    ⟨expansion_faW_noDep k γ c hck hcγ x x' h, by
      rw [expansion_faW_noDep k γ c hck hcγ x x' h,
        expansion_rowInt_noDep M {k.1} {c.1} (expansion_faW_noDep k γ c hck hcγ) x x' h]⟩
  refine ⟨hA, fun j k γ flag ⟨s, hs⟩ x => ?_⟩
  set c := k s
  set Y : Fin j → (Pair N → 𝕜) → ℂ := fun u w => (if flag u then starRingEnd ℂ else RingHom.id ℂ)
    (faW L z (k u) (γ u) w - rowInt M {(k u).1} (faW L z (k u) (γ u)) w) with hY
  have hW := fun u => (expansion_pg M hz L (k u) 0).1 (γ u)
  have hYpg : ∀ u, PolyGrowth (Y u) := fun u => by
    have hQ := expansion_pg_sub (hW u) (rowInt_polyGrowth M hM hϑ {(k u).1} (hW u))
    simp only [hY]
    cases flag u
    · simpa using hQ
    · simpa using hQ.conj
  have hYnd : ∀ u, u ≠ s → ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ {c.1} → x p = x' p) →
      Y u x = Y u x' := fun u hu x x' h => by
    obtain ⟨h1, h2⟩ := hs u hu
    simp only [hY, (hA (k u) (γ u) c h1 h2 x x' h).2]
  set g : (Pair N → 𝕜) → ℂ := fun w => ∏ u ∈ Finset.univ.erase s, Y u w with hg
  have hgnd : ∀ x x' : Pair N → 𝕜, (∀ p, p ∉ rowsQ {c.1} → x p = x' p) → g x = g x' :=
    fun x x' h => Finset.prod_congr rfl fun u hu => hYnd u (Finset.ne_of_mem_erase hu) x x' h
  have hgpg : PolyGrowth g := expansion_pg_prod _ fun u _ => hYpg u
  have hprod : (fun w => ∏ u, Y u w) = fun w => g w * Y s w := funext fun w => by
    rw [mul_comm]
    exact (Finset.mul_prod_erase _ (fun u => Y u w) (Finset.mem_univ s)).symm
  have hPs : ∀ w, rowInt M {c.1} (Y s) w = 0 := fun w => by
    have hQ : rowInt M {c.1} (fun w => faW L z c (γ s) w -
        rowInt M {c.1} (faW L z c (γ s)) w) w = 0 := by
      rw [expansion_rowInt_sub M hM hϑ _ (hW s) (rowInt_polyGrowth M hM hϑ _ (hW s)),
        rowInt_rowInt M hM hϑ (subset_refl _) (hW s), sub_self]
    simp only [hY]
    cases flag s
    · simpa using hQ
    · simp only [↓reduceIte]
      rw [expansion_rowInt_conj M, hQ, map_zero]
  change rowInt M L (fun w => ∏ u, Y u w) x = 0
  rw [hprod, ← rowInt_rowInt M hM hϑ (Finset.singleton_subset_iff.2 c.2) (hgpg.mul (hYpg s))]
  have h0 : rowInt M {c.1} (fun w => g w * Y s w) = fun _ => 0 := funext fun w => by
    rw [rowInt_mul_left M {c.1} hgnd (Y s) w, hPs w, mul_zero]
  rw [h0]
  unfold rowInt partialInt
  simp

end Rigidity
