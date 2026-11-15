import Rigidity.Fluctuation.Expansion
import Rigidity.Fluctuation.Moments

/-!
# Size of the terms (NP v1.1, §6.6: (6.26), (6.27), Lemma 6.11)

Numbers in this file refer to the blueprint NP v1.1.

A path of `faPath k n₀` is a list `γ` of vertices; its order is `o(γ) = γ.length + 1`.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `n₀ = 2p + ⌈log N⌉` of (6.26). -/
noncomputable def faN0 (p N : ℕ) : ℕ := 2 * p + ⌈Real.log N⌉₊

/-- `τ = C_m (9p²)^{2a+1}` of (6.26). -/
noncomputable def faTau (a : ℝ) (p : ℕ) : ℝ := faCm a * (9 * (p : ℝ) ^ 2) ^ (2 * a + 1)

/-- `φ₀ = (5e C_m (13p³)^{2a+3/2})⁻¹` of (6.26). -/
noncomputable def faPhi0 (a : ℝ) (p : ℕ) : ℝ :=
  (5 * Real.exp 1 * faCm a * (13 * (p : ℝ) ^ 3) ^ (2 * a + 3 / 2))⁻¹

/-- The event `Ξ_L = {Φ_L ≤ φ₀} ∩ ⋂_{b ∈ L} {|z + m_b^{(L)}| ≥ 2/5}` of (6.27). -/
def faXiL {N : ℕ} (M : Ensemble 𝕜 N) (C₀ a : ℝ) (p : ℕ) (L : Finset (Fin N)) (z : ℂ) :
    Set (Pair N → 𝕜) :=
  {x | phiL C₀ L z x ≤ faPhi0 a p ∧ ∀ b ∈ L, 2 / 5 ≤ ‖z + mL M L z b x‖}

/-- `ρ = 6 τ Φ_L` of (6.27). -/
noncomputable def faRho {N : ℕ} (C₀ a : ℝ) (p : ℕ) (L : Finset (Fin N)) (z : ℂ)
    (x : Pair N → 𝕜) : ℝ :=
  6 * faTau a p * phiL C₀ L z x

/-- The event `Ξ_L` is closed, and membership in it does not depend on the coordinates in the
rows `L` (Lemma 6.4 (b), (c)). -/
theorem faXiL_props {N : ℕ} (M : Ensemble 𝕜 N) (C₀ a : ℝ) (p : ℕ) (L : Finset (Fin N))
    {z : ℂ} (hz : 0 < z.im) :
    IsClosed (faXiL M C₀ a p L z) ∧
      ∀ x x' : Pair N → 𝕜, (∀ q, q ∉ rowsQ L → x q = x' q) →
        (x ∈ faXiL M C₀ a p L z ↔ x' ∈ faXiL M C₀ a p L z) := by
  obtain ⟨-, -, -, -, -, -, hmL, hphi, -⟩ := polyGrowth_schurM M C₀ hz L
  obtain ⟨-, -, hmL', hphi'⟩ := noDep_greenT M C₀ L z
  refine ⟨?_, fun x x' h => ?_⟩
  · have h1 : IsClosed {x : Pair N → 𝕜 | phiL C₀ L z x ≤ faPhi0 a p} :=
      isClosed_le hphi continuous_const
    have h2 : IsClosed {x : Pair N → 𝕜 | ∀ b ∈ L, 2 / 5 ≤ ‖z + mL M L z b x‖} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun b => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_const.add (hmL b).1).norm
    exact h1.inter h2
  · simp only [faXiL, Set.mem_ofPred_eq, hphi' x x' h, hmL' _ x x' h]

/-! ### Row norms -/

section RowNorm

variable {N : ℕ} (M : Ensemble 𝕜 N)

/-- `‖f‖_{q,T} ≥ 0`. -/
private lemma size_rowNorm_nonneg (T : Finset (Fin N)) (q : ℝ) (f : (Pair N → 𝕜) → ℂ)
    (x : Pair N → 𝕜) : 0 ≤ rowNorm M T q f x :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- `‖f‖_{q,T}` depends only on `|f|`. -/
private lemma size_rowNorm_congr_norm (T : Finset (Fin N)) (q : ℝ) {f g : (Pair N → 𝕜) → ℂ}
    (h : ∀ w, ‖f w‖ = ‖g w‖) (x : Pair N → 𝕜) : rowNorm M T q f x = rowNorm M T q g x := by
  have h' : ∀ w, ‖f w‖ₑ = ‖g w‖ₑ := fun w => by rw [← ofReal_norm, ← ofReal_norm, h w]
  simp only [rowNorm, h']

/-- `‖0‖_{q,T} = 0` for `q > 0`. -/
private lemma size_rowNorm_zero (T : Finset (Fin N)) {q : ℝ} (hq : 0 < q) (x : Pair N → 𝕜) :
    rowNorm M T q (fun _ => (0 : ℂ)) x = 0 := by
  simp only [rowNorm, partialLInt, enorm_zero, ENNReal.zero_rpow_of_pos hq, lintegral_zero,
    ENNReal.toReal_zero]
  exact Real.zero_rpow (one_div_pos.2 hq).ne'

/-- A function bounded by `c` has `‖f‖_{q,T} ≤ c` (the laws are probability measures). -/
private lemma size_rowNorm_le_of_bound (T : Finset (Fin N)) {g : (Pair N → 𝕜) → ℂ}
    (hg : Measurable g) {c : ℝ} (hc : 0 ≤ c) (hb : ∀ w, ‖g w‖ ≤ c) {q : ℝ} (hq : 1 ≤ q)
    (x : Pair N → 𝕜) : rowNorm M T q g x ≤ c := by
  have hmerge : Measurable (fun y : rowsQ T → 𝕜 => piMerge (rowsQ T) x y) := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases h : i ∈ rowsQ T
    · simp only [piMerge, h]
      exact measurable_pi_apply _
    · simp only [piMerge, h]
      exact measurable_const
  rw [(rowInt_freeze M T hg x).2.2.2 q hq]
  refine ENNReal.toReal_le_of_le_ofReal hc ?_
  refine (eLpNorm_le_of_ae_bound (hg.comp hmerge).aestronglyMeasurable
    (ae_of_all _ fun y => hb _)).trans ?_
  simp

variable {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
include hM hϑ

/-- Lemma 6.3 (F3) for `Q_k = 1 - P_k`: `‖Q_k f‖_{q,T} ≤ 2 ‖f‖_{q,T}` for `k ∈ T`, `q ≥ 1`. -/
private lemma size_rowNorm_Q_le {T : Finset (Fin N)} {k : Fin N} (hk : k ∈ T)
    {f : (Pair N → 𝕜) → ℂ} (hf : PolyGrowth f) {q : ℝ} (hq : 1 ≤ q) (x : Pair N → 𝕜) :
    rowNorm M T q (fun w => f w - rowInt M {k} f w) x ≤ 2 * rowNorm M T q f x := by
  have hP := rowInt_polyGrowth M hM hϑ {k} hf
  have hneg : PolyGrowth (fun w => -rowInt M {k} f w) := by
    obtain ⟨hm, c, m, hb⟩ := hP
    exact ⟨hm.neg, c, m, fun w => by simpa using hb w⟩
  calc rowNorm M T q (fun w => f w - rowInt M {k} f w) x
      = rowNorm M T q (fun w => f w + -rowInt M {k} f w) x := by simp only [sub_eq_add_neg]
    _ ≤ rowNorm M T q f x + rowNorm M T q (fun w => -rowInt M {k} f w) x :=
        rowNorm_add_le M hM hϑ T hf hneg hq x
    _ = rowNorm M T q f x + rowNorm M T q (rowInt M {k} f) x := by
        rw [size_rowNorm_congr_norm M T q (fun w => norm_neg _)]
    _ ≤ rowNorm M T q f x + rowNorm M T q f x :=
        add_le_add le_rfl (rowNorm_rowInt_le M hM hϑ (Finset.singleton_subset_iff.2 hk) hf hq x)
    _ = 2 * rowNorm M T q f x := by ring

omit hM hϑ in
/-- Finite sums of functions of `𝒜` are in `𝒜`. -/
private lemma size_pg_sum {ι : Type*} (s : Finset ι) {F : ι → (Pair N → 𝕜) → ℂ}
    (hF : ∀ i ∈ s, PolyGrowth (F i)) : PolyGrowth (fun w => ∑ i ∈ s, F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨measurable_const, 0, 0, fun w => by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- Lemma 6.3 (F3), Minkowski for finite sums. -/
private lemma size_rowNorm_sum_le (T : Finset (Fin N)) {ι : Type*} (s : Finset ι)
    {F : ι → (Pair N → 𝕜) → ℂ} (hF : ∀ i ∈ s, PolyGrowth (F i)) {q : ℝ} (hq : 1 ≤ q)
    (x : Pair N → 𝕜) :
    rowNorm M T q (fun w => ∑ i ∈ s, F i w) x ≤ ∑ i ∈ s, rowNorm M T q (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (size_rowNorm_zero M T (by linarith) x).le
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs : ∀ j ∈ s, PolyGrowth (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    exact (rowNorm_add_le M hM hϑ T (hF i (Finset.mem_insert_self i s))
      (size_pg_sum s hs) hq x).trans (add_le_add le_rfl (ih hs))

omit hM hϑ in
/-- Finite products (along a list) of functions of `𝒜` are in `𝒜`. -/
private lemma size_pg_listProd :
    ∀ l : List ((Pair N → 𝕜) → ℂ), (∀ f ∈ l, PolyGrowth f) →
      PolyGrowth (fun w => (l.map (· w)).prod)
  | [], _ => ⟨measurable_const, 1, 0, fun w => by simp⟩
  | f :: l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact (h f List.mem_cons_self).mul
      (size_pg_listProd l fun g hg => h g (List.mem_cons_of_mem f hg))

/-- Lemma 6.3 (F3), Hölder for a product of `n ≥ 1` factors, each in `L^{nq}`. -/
private lemma size_rowNorm_listProd_le (T : Finset (Fin N)) (x : Pair N → 𝕜) :
    ∀ l : List ((Pair N → 𝕜) → ℂ), l ≠ [] → (∀ f ∈ l, PolyGrowth f) → ∀ q : ℝ, 1 ≤ q →
      rowNorm M T q (fun w => (l.map (· w)).prod) x ≤
        (l.map fun f => rowNorm M T (q * l.length) f x).prod
  | [], h, _, _, _ => absurd rfl h
  | [f], _, _, q, _ => by simp
  | f :: g :: l, _, hf, q, hq => by
    set P : (Pair N → 𝕜) → ℂ := fun w => ((g :: l).map (· w)).prod with hPdef
    set n : ℝ := ((g :: l).length : ℝ) with hn
    have hn1 : 1 ≤ n := by rw [hn]; simp
    have hn0 : 0 < n := by linarith
    have hq0 : 0 < q := by linarith
    have hfl : ∀ h ∈ g :: l, PolyGrowth h := fun h hh => hf h (List.mem_cons_of_mem f hh)
    have hP : PolyGrowth P := size_pg_listProd (g :: l) hfl
    have hq' : 1 ≤ q * (n + 1) / n := by
      rw [le_div_iff₀ hn0]; nlinarith
    have IH := size_rowNorm_listProd_le T x (g :: l) (List.cons_ne_nil g l) hfl _ hq'
    have hexp : q * (n + 1) / n * ((g :: l).length : ℝ) = q * (n + 1) := by
      rw [← hn]; field_simp
    rw [hexp] at IH
    have H := rowNorm_prod_le M hM hϑ T (Finset.univ : Finset (Fin 2)) ![f, P]
      ![q * (n + 1), q * (n + 1) / n] hq
      (fun i _ => by
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; nlinarith
        · simpa using hq')
      (by
        rw [Fin.sum_univ_two]
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp
        ring)
      (fun i _ => by
        fin_cases i
        · simpa using hf f List.mem_cons_self
        · simpa using hP) x
    simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at H
    have hlen : (((f :: g :: l).length : ℕ) : ℝ) = n + 1 := by
      rw [hn]; simp
    have hfun : (fun w => ((f :: g :: l).map (· w)).prod) = fun w => f w * P w := by
      funext w; simp [hPdef]
    rw [hfun, hlen, List.map_cons, List.prod_cons]
    refine H.trans ?_
    exact mul_le_mul_of_nonneg_left IH (size_rowNorm_nonneg M T _ f x)

end RowNorm

/-! ### Products along lists -/

/-- A product of reals in `[0, c]` along a list is in `[0, c^{length}]`. -/
private lemma size_listProd_le_pow {β : Type*} (g : β → ℝ) (c : ℝ) :
    ∀ l : List β, (∀ f ∈ l, 0 ≤ g f ∧ g f ≤ c) →
      0 ≤ (l.map g).prod ∧ (l.map g).prod ≤ c ^ l.length
  | [], _ => by simp
  | f :: l, h => by
    obtain ⟨h0, h1⟩ := size_listProd_le_pow g c l fun f' hf' => h f' (List.mem_cons_of_mem f hf')
    obtain ⟨hf0, hf1⟩ := h f List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    refine ⟨mul_nonneg hf0 h0, ?_⟩
    calc g f * (l.map g).prod ≤ c * c ^ l.length := mul_le_mul hf1 h1 h0 (hf0.trans hf1)
      _ = c ^ l.length * c := mul_comm _ _

/-- `1 / ∏ F = ∏ 1 / F` along a list. -/
private lemma size_one_div_listProd {α : Type*} (l : List α) (F : α → ℂ) :
    1 / (l.map F).prod = (l.map fun a => 1 / F a).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih,
      one_div_mul_one_div]

/-- Consecutive entries of `c :: ρ ++ [k]` are distinct when `c :: ρ` is a chain of distinct
consecutive entries avoiding `k`. -/
private lemma size_zipWith_append_ne {α β : Type*} (F : α → α → β) (k : α) :
    ∀ (ρ : List α) (c : α), c ≠ k → (∀ d ∈ ρ, d ≠ k) → (c :: ρ).IsChain (· ≠ ·) →
      ∀ f ∈ List.zipWith F (c :: ρ) (ρ ++ [k]), ∃ u v, u ≠ v ∧ f = F u v
  | [], c, hc, _, _, f, hf => by
    simp only [List.nil_append, List.zipWith_cons_cons, List.zipWith_nil_left,
      List.mem_singleton] at hf
    exact ⟨c, k, hc, hf⟩
  | d :: ρ, c, _, hρ, hch, f, hf => by
    simp only [List.cons_append, List.zipWith_cons_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨c, d, (List.isChain_cons_cons.1 hch).1, rfl⟩
    · exact size_zipWith_append_ne F k ρ d (hρ d List.mem_cons_self)
        (fun e he => hρ e (List.mem_cons_of_mem d he)) (List.isChain_cons_cons.1 hch).2 f hf

/-- Consecutive entries of a chain `c :: ρ` of distinct consecutive entries are distinct. -/
private lemma size_zipWith_self_ne {α β : Type*} (F : α → α → β) :
    ∀ (ρ : List α) (c : α), (c :: ρ).IsChain (· ≠ ·) →
      ∀ f ∈ List.zipWith F (c :: ρ) ρ, ∃ u v, u ≠ v ∧ f = F u v
  | [], _, _, f, hf => by simp at hf
  | d :: ρ, c, hch, f, hf => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact ⟨c, d, (List.isChain_cons_cons.1 hch).1, rfl⟩
    · exact size_zipWith_self_ne F ρ d (List.isChain_cons_cons.1 hch).2 f hf

/-- The factors `M_{k a₀}, M_{a₀ a₁}, …, M_{a_n k}` of `W_k(γ)` are off-diagonal for a nonempty
path `γ`. -/
private lemma size_zip_k_ne {α β : Type*} (F : α → α → β) (k : α) {γ : List α} (hγ : γ ≠ [])
    (hk : ∀ d ∈ γ, d ≠ k) (hch : γ.IsChain (· ≠ ·)) :
    ∀ f ∈ List.zipWith F (k :: γ) (γ ++ [k]), ∃ u v, u ≠ v ∧ f = F u v := by
  obtain ⟨c, ρ, rfl⟩ := List.exists_cons_of_ne_nil hγ
  intro f hf
  rw [List.cons_append, List.zipWith_cons_cons, List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact ⟨k, c, (hk c List.mem_cons_self).symm, rfl⟩
  · exact size_zipWith_append_ne F k ρ c (hk c List.mem_cons_self)
      (fun d hd => hk d (List.mem_cons_of_mem c hd)) hch f hf

/-- The factors `M_{k a₀}, M_{a₀ a₁}, …, M_{a_{n-1} a_n}` of a term of `R_k` are off-diagonal. -/
private lemma size_zip_k_self_ne {α β : Type*} (F : α → α → β) (k : α) {γ : List α}
    (hγ : γ ≠ []) (hk : ∀ d ∈ γ, d ≠ k) (hch : γ.IsChain (· ≠ ·)) :
    ∀ f ∈ List.zipWith F (k :: γ) γ, ∃ u v, u ≠ v ∧ f = F u v := by
  obtain ⟨c, ρ, rfl⟩ := List.exists_cons_of_ne_nil hγ
  exact size_zipWith_self_ne F (c :: ρ) k
    (List.isChain_cons_cons.2 ⟨(hk c List.mem_cons_self).symm, hch⟩)

/-! ### The factors of `W_k(γ)` and of the terms of `R_k` -/

section Factors

variable {N : ℕ}

/-- The `2 o(γ) - 1` factors of `W_k(γ)` (6.19): `M_{k a₀}, …, M_{a_n k}` and
`1/M_{a₀a₀}, …, 1/M_{a_na_n}`. -/
private noncomputable def size_Wfac (L : Finset (Fin N)) (z : ℂ) (k : L) (γ : List L) :
    List ((Pair N → 𝕜) → ℂ) :=
  List.zipWith (fun a b => fun w => schurM (toMatrix w) L z a b) (k :: γ) (γ ++ [k]) ++
    γ.map fun a => fun w => 1 / schurM (toMatrix w) L z a a

/-- The factors of the term of `R_k` (6.20) for the path `γ = [a₀, …, a_{n₀}]` and `b`:
`M_{k a₀}, …, M_{a_{n₀-1} a_{n₀}}`, `1/M_{a₀a₀}, …, 1/M_{a_{n₀-1}a_{n₀-1}}`, `M_{bk}` and
`G^{(k)}_{a_{n₀} b}`. -/
private noncomputable def size_Rfac (L : Finset (Fin N)) (z : ℂ) (k : L) (γ : List L) (b : L) :
    List ((Pair N → 𝕜) → ℂ) :=
  List.zipWith (fun a c => fun w => schurM (toMatrix w) L z a c) (k :: γ) γ ++
    γ.dropLast.map (fun a => fun w => 1 / schurM (toMatrix w) L z a a) ++
    [fun w => schurM (toMatrix w) L z b k,
      fun w => greenT (toMatrix w) {k.1} z (γ.getLastD k).1 b.1]

private lemma size_faW_eq (L : Finset (Fin N)) (z : ℂ) (k : L) (γ : List L) (w : Pair N → 𝕜) :
    faW L z k γ w = ((size_Wfac (𝕜 := 𝕜) L z k γ).map (· w)).prod := by
  simp only [faW, size_Wfac, List.map_append, List.prod_append, List.map_zipWith, List.map_map,
    Function.comp_def]
  rw [div_eq_mul_one_div, size_one_div_listProd]

private lemma size_faR_eq (L : Finset (Fin N)) (z : ℂ) (k : L) (n₀ : ℕ) (w : Pair N → 𝕜) :
    faR L z k n₀ w = (-1) ^ n₀ * ∑ γ ∈ (faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1),
      ∑ b ∈ Finset.univ.erase k, ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod := by
  unfold faR
  congr 1
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [size_Rfac, List.map_append, List.prod_append, List.map_zipWith, List.map_map,
    Function.comp_def, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [div_eq_mul_one_div, size_one_div_listProd]
  ring

private lemma size_length_Wfac (L : Finset (Fin N)) (z : ℂ) (k : L) (γ : List L) :
    (size_Wfac (𝕜 := 𝕜) L z k γ).length = 2 * γ.length + 1 := by
  simp only [size_Wfac, List.length_append, List.length_zipWith, List.length_cons,
    List.length_map]
  omega

private lemma size_length_Rfac (L : Finset (Fin N)) (z : ℂ) (k : L) (γ : List L) (b : L)
    (hγ : γ ≠ []) : (size_Rfac (𝕜 := 𝕜) L z k γ b).length = 2 * γ.length + 1 := by
  have := List.length_pos_iff.2 hγ
  simp only [size_Rfac, List.length_append, List.length_zipWith, List.length_cons,
    List.length_map, List.length_dropLast, List.length_nil]
  omega

/-- `‖G^{(T)}_uv‖ ≤ η⁻¹` (Lemma 3.5 (a) for the minors). -/
private lemma size_norm_greenT_le (x : Pair N → 𝕜) {z : ℂ} (hz : 0 < z.im) (T : Finset (Fin N))
    (u v : Fin N) : ‖greenT (toMatrix x) T z u v‖ ≤ 1 / z.im := by
  by_cases h : u ∉ T ∧ v ∉ T
  · have hP : (minor (toMatrix x) T).IsHermitian :=
      (toMatrix_isHermitian x).submatrix (Subtype.val : {i // i ∉ T} → Fin N)
    have e : greenT (toMatrix x) T z u v = green (minor (toMatrix x) T) z ⟨u, h.1⟩ ⟨v, h.2⟩ := by
      simp [greenT, greenMinor, h.1, h.2]
    rw [e]
    exact norm_green_apply_le hP hz _ _
  · have e : greenT (toMatrix x) T z u v = 0 := by simp [greenT, h]
    rw [e, norm_zero]
    positivity

end Factors

/-! ### Constants -/

/-- `C_m ≥ 1` for `a ≥ 1`. -/
private lemma size_one_le_faCm {a : ℝ} (ha : 1 ≤ a) : 1 ≤ faCm a := by
  have hk : 0 ≤ kappaTheta a := by
    unfold kappaTheta cTheta
    have h1 : 0 ≤ Real.log a := Real.log_nonneg ha
    have h2 : 0 ≤ Real.log (4 * (90 * a)) := Real.log_nonneg (by linarith)
    positivity
  have h1 : 1 ≤ cLD a := by
    unfold cLD
    have : 1 ≤ (4 * a + 2 + kappaTheta a) ^ (2 * a + 1) :=
      Real.one_le_rpow (by linarith) (by linarith)
    linarith
  exact le_trans (by nlinarith) (le_max_right (cTheta a ^ a) (cLD a ^ 2))

/-- `C₀ ≥ 0` under (C). -/
private lemma size_C₀_nonneg {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hN : 0 < N) : 0 ≤ C₀ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ C₀ / N :=
    (integral_nonneg fun _ => sq_nonneg _).trans (hM.boundC ⟨0, hN⟩ ⟨0, hN⟩)
  have := mul_nonneg hC hNr.le
  rwa [div_mul_cancel₀ _ hNr.ne'] at this

/-- `Φ_L ≥ 0` for `C₀ ≥ 0`. -/
private lemma size_phiL_nonneg {N : ℕ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (L : Finset (Fin N)) (z : ℂ)
    (x : Pair N → 𝕜) : 0 ≤ phiL C₀ L z x :=
  add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC₀ (Real.sqrt_nonneg _))

/-! ### The preparations of Lemma 6.11 -/

section Preparations

variable {N : ℕ}

/-- (6.28) at `Q = p (2n₀ + 3) = q_max + p`: `Q ≥ 2`, `Q + log N ≤ 9p²` and
`(Q + 1)⌈log N⌉ ≤ 13p³`. -/
private lemma size_Q_bounds {p : ℕ} (hp : 2 ≤ p) (hlog : Real.log N ≤ p) :
    2 ≤ (p : ℝ) * ((2 * faN0 p N + 3 : ℕ) : ℝ) ∧
    (p : ℝ) * ((2 * faN0 p N + 3 : ℕ) : ℝ) + Real.log N ≤ 9 * (p : ℝ) ^ 2 ∧
    ((p : ℝ) * ((2 * faN0 p N + 3 : ℕ) : ℝ) + 1) * ⌈Real.log N⌉₊ ≤ 13 * (p : ℝ) ^ 3 := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hcp : (⌈Real.log N⌉₊ : ℝ) ≤ p := by exact_mod_cast Nat.ceil_le.2 hlog
  have hc0 : (0 : ℝ) ≤ ⌈Real.log N⌉₊ := Nat.cast_nonneg _
  have hQ : (p : ℝ) * ((2 * faN0 p N + 3 : ℕ) : ℝ) =
      2 * p * (2 * p + ⌈Real.log N⌉₊) + 3 * p := by
    unfold faN0; push_cast; ring
  rw [hQ]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h2 : 0 ≤ (2 * p * (2 * p + ⌈Real.log N⌉₊) + 3 * p + 1 : ℝ) := by positivity
  have h1 : (2 * p * (2 * p + ⌈Real.log N⌉₊) + 3 * p + 1) * (⌈Real.log N⌉₊ : ℝ) ≤
      (2 * p * (2 * p + p) + 3 * p + 1) * (p : ℝ) :=
    calc (2 * p * (2 * p + ⌈Real.log N⌉₊) + 3 * p + 1) * (⌈Real.log N⌉₊ : ℝ)
        ≤ (2 * p * (2 * p + ⌈Real.log N⌉₊) + 3 * p + 1) * (p : ℝ) :=
          mul_le_mul_of_nonneg_left hcp h2
      _ ≤ (2 * p * (2 * p + p) + 3 * p + 1) * (p : ℝ) := by gcongr
  have hp3 : 3 * (p : ℝ) ^ 2 + p ≤ 7 * (p : ℝ) ^ 3 := by
    nlinarith [pow_pos (by linarith : (0 : ℝ) < p) 2]
  nlinarith

variable (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
  (hϑ1 : ϑ ≤ 1)
include hM hϑ hϑ1

/-- The bound (6.29), `‖M_uv‖_{q,L} ≤ τ Φ_L` for `u ≠ v` in `L`, on `2 ≤ q ≤ Q` for any `Q` with
`Q + log N ≤ 9p²` (Lemma 6.5 (m1)). -/
private lemma size_m1 {p : ℕ} {z : ℂ} (hz : 0 < z.im) {L : Finset (Fin N)} (hLN : L.card < N)
    {Q : ℝ} (hQ9 : Q + Real.log N ≤ 9 * (p : ℝ) ^ 2) (x : Pair N → 𝕜) (u v : L) (huv : u ≠ v)
    (q : ℝ) (hq2 : 2 ≤ q) (hqQ : q ≤ Q) :
    rowNorm M L q (fun w => schurM (toMatrix w) L z u v) x ≤
      faTau ϑ⁻¹ p * phiL C₀ L z x := by
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hCm0 : 0 ≤ faCm ϑ⁻¹ := by linarith [size_one_le_faCm ha1]
  have hΦ := size_phiL_nonneg (size_C₀_nonneg M hM hNpos) L z x
  have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  refine (rowNorm_schurM_offdiag_le M hM hϑ hϑ1 hz hLN u.2 v.2 huv' hq2 x).trans ?_
  have h1 : (q + Real.log N) ^ (2 * ϑ⁻¹ + 1) ≤ (9 * (p : ℝ) ^ 2) ^ (2 * ϑ⁻¹ + 1) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCm0) hΦ

/-- The bound (6.30): at a point of `Ξ_L`, (6.10) holds with `q_* = Q` for any `Q ≥ 2` with
`(Q + 1)⌈log N⌉ ≤ 13p³`, hence `‖1/M_uu‖_{q,L} ≤ 6` for `u ∈ L` and `1 ≤ q ≤ Q`
(Lemma 6.5 (m3)). -/
private lemma size_m3 {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hη : 1 / N ≤ z.im) {L : Finset (Fin N)}
    (hLN : L.card < N)
    {Q : ℝ} (hQ2 : 2 ≤ Q) (hQ13 : (Q + 1) * ⌈Real.log N⌉₊ ≤ 13 * (p : ℝ) ^ 3)
    {x : Pair N → 𝕜} (hx : x ∈ faXiL M C₀ ϑ⁻¹ p L z) (u : L) (q : ℝ) (hq1 : 1 ≤ q)
    (hqQ : q ≤ Q) :
    rowNorm M L q (fun w => 1 / schurM (toMatrix w) L z u u) x ≤ 6 := by
  have hNpos : 0 < N := by omega
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hCm0 : 0 < faCm ϑ⁻¹ := by linarith [size_one_le_faCm ha1]
  have hΦ := size_phiL_nonneg (size_C₀_nonneg M hM hNpos) L z x
  have hx1 : phiL C₀ L z x ≤
      (5 * Real.exp 1 * faCm ϑ⁻¹ * (13 * (p : ℝ) ^ 3) ^ (2 * ϑ⁻¹ + 3 / 2))⁻¹ := hx.1
  have hc0 : (0 : ℝ) ≤ ⌈Real.log N⌉₊ := Nat.cast_nonneg _
  have hY : ((Q + 1) * (⌈Real.log N⌉₊ : ℝ)) ^ (2 * ϑ⁻¹ + 3 / 2) ≤
      (13 * (p : ℝ) ^ 3) ^ (2 * ϑ⁻¹ + 3 / 2) :=
    Real.rpow_le_rpow (mul_nonneg (by linarith) hc0) hQ13 (by linarith)
  have hA : 0 < 5 * Real.exp 1 * faCm ϑ⁻¹ * (13 * (p : ℝ) ^ 3) ^ (2 * ϑ⁻¹ + 3 / 2) :=
    mul_pos (mul_pos (by positivity) hCm0) (Real.rpow_pos_of_pos (by
      have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      positivity) _)
  have hφ : 5 * Real.exp 1 * faCm ϑ⁻¹ * ((Q + 1) * ⌈Real.log N⌉₊) ^ (2 * ϑ⁻¹ + 3 / 2) *
      phiL C₀ L z x ≤ 1 :=
    calc 5 * Real.exp 1 * faCm ϑ⁻¹ * ((Q + 1) * ⌈Real.log N⌉₊) ^ (2 * ϑ⁻¹ + 3 / 2) *
          phiL C₀ L z x
        ≤ 5 * Real.exp 1 * faCm ϑ⁻¹ * (13 * (p : ℝ) ^ 3) ^ (2 * ϑ⁻¹ + 3 / 2) *
          phiL C₀ L z x := by gcongr
      _ ≤ 5 * Real.exp 1 * faCm ϑ⁻¹ * (13 * (p : ℝ) ^ 3) ^ (2 * ϑ⁻¹ + 3 / 2) *
          (5 * Real.exp 1 * faCm ϑ⁻¹ * (13 * (p : ℝ) ^ 3) ^ (2 * ϑ⁻¹ + 3 / 2))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hA.ne'
  exact rowNorm_inv_schurM_diag_le M hM hϑ hϑ1 hη hLN u.2 hQ2 x (hx.2 u.1 u.2) hφ hq1 hqQ

omit hM hϑ hϑ1 in
/-- `‖G^{(k)}_uv‖_{q,L} ≤ η⁻¹ ≤ N` for `η ≥ 1/N`. -/
private lemma size_G {C₀ : ℝ} {z : ℂ} (hN : 0 < N) (hη : 1 / N ≤ z.im) (L : Finset (Fin N))
    (k u v : Fin N) {q : ℝ} (hq : 1 ≤ q) (x : Pair N → 𝕜) :
    rowNorm M L q (fun w => greenT (toMatrix w) {k} z u v) x ≤ N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have hηN : 1 / z.im ≤ N := by
    have h := hη
    rw [div_le_iff₀ hN0] at h
    rw [div_le_iff₀ hz]
    linarith
  exact size_rowNorm_le_of_bound M L ((polyGrowth_schurM M C₀ hz L).2.2.1 k u v).2.1 hN0.le
    (fun w => (size_norm_greenT_le w hz _ u v).trans hηN) hq x

end Preparations

/-- Lemma 6.11 (a): `p ρ ≤ 1/8` where `Φ_L ≤ φ₀`. -/
private lemma size_part_a {N : ℕ} {C₀ a : ℝ} (ha : 1 ≤ a) {p : ℕ} (hp : 2 ≤ p)
    {L : Finset (Fin N)} {z : ℂ} {x : Pair N → 𝕜} (hx1 : phiL C₀ L z x ≤ faPhi0 a p) :
    (p : ℝ) * faRho C₀ a p L z x ≤ 1 / 8 := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hCm : 1 ≤ faCm a := size_one_le_faCm ha
  have hCm0 : 0 < faCm a := by linarith
  have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hX : (9 * (p : ℝ) ^ 2) ^ (2 * a + 1) ≤ (13 * (p : ℝ) ^ 3) ^ (2 * a + 1) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
  have hY : (13 * (p : ℝ) ^ 3) ^ (2 * a + 3 / 2) =
      (13 * (p : ℝ) ^ 3) ^ (2 * a + 1) * (13 * (p : ℝ) ^ 3) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hS : 5 * (p : ℝ) ≤ (13 * (p : ℝ) ^ 3) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by positivity) (by positivity)).2 (by nlinarith)
  have hx2 : phiL C₀ L z x ≤ (5 * Real.exp 1 * faCm a *
      ((13 * (p : ℝ) ^ 3) ^ (2 * a + 1) * (13 * (p : ℝ) ^ 3) ^ (1 / 2 : ℝ)))⁻¹ := by
    rw [← hY]; exact hx1
  have hX0 : 0 < (9 * (p : ℝ) ^ 2) ^ (2 * a + 1) := Real.rpow_pos_of_pos (by positivity) _
  have hW0 : 0 < (13 * (p : ℝ) ^ 3) ^ (2 * a + 1) := Real.rpow_pos_of_pos (by positivity) _
  have hS0 : 0 < (13 * (p : ℝ) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  unfold faRho faTau
  generalize (9 * (p : ℝ) ^ 2) ^ (2 * a + 1) = X at hX hX0 ⊢
  generalize (13 * (p : ℝ) ^ 3) ^ (2 * a + 1) = W at hX hW0 hx2
  generalize (13 * (p : ℝ) ^ 3) ^ (1 / 2 : ℝ) = S at hS hS0 hx2
  have hA : 0 < 5 * Real.exp 1 * faCm a * (W * S) :=
    mul_pos (mul_pos (by positivity) hCm0) (mul_pos hW0 hS0)
  have ht : 0 ≤ (p : ℝ) * faCm a * X := by positivity
  calc (p : ℝ) * (6 * (faCm a * X) * phiL C₀ L z x) = 6 * p * faCm a * X * phiL C₀ L z x := by
        ring
    _ ≤ 6 * p * faCm a * X * (5 * Real.exp 1 * faCm a * (W * S))⁻¹ := by gcongr
    _ ≤ 1 / 8 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hA]
      calc 6 * (p : ℝ) * faCm a * X = 6 * ((p : ℝ) * faCm a * X) := by ring
        _ ≤ 25 / 4 * ((p : ℝ) * faCm a * X) := by linarith
        _ = (5 * 2 / 8) * faCm a * (X * (5 * p)) := by ring
        _ ≤ (5 * Real.exp 1 / 8) * faCm a * (W * S) := by gcongr
        _ = 1 / 8 * (5 * Real.exp 1 * faCm a * (W * S)) := by ring

section Parts

variable {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ} (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ)
include hM hϑ

/-- Lemma 6.11 (b) for the empty path: `‖Q_k M_kk‖_{p,L} ≤ τ Φ_L ≤ 2ρ` (Lemma 6.5 (m2)). -/
private lemma size_part_b_nil (hϑ1 : ϑ ≤ 1) {p : ℕ} (hp : 2 ≤ p) (hlog : Real.log N ≤ p)
    {z : ℂ} (hz : 0 < z.im) {L : Finset (Fin N)} (hLN : L.card < N) (k : L) (x : Pair N → 𝕜) :
    rowNorm M L p (fun w => faW L z k [] w - rowInt M {k.1} (faW L z k []) w) x ≤
      2 * faRho C₀ ϑ⁻¹ p L z x ^ (([] : List L).length + 1) := by
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hCm0 : 0 ≤ faCm ϑ⁻¹ := by linarith [size_one_le_faCm ha1]
  have hΦ := size_phiL_nonneg (size_C₀_nonneg M hM hNpos) L z x
  have hW : faW L z k [] = fun w : Pair N → 𝕜 => schurM (toMatrix w) L z k k := by
    funext w; simp [faW]
  rw [hW]
  refine (rowNorm_Q_schurM_diag_le M hM hϑ hϑ1 hz hLN k.2 (q := p) hpr x).trans ?_
  have hb1 : ((p : ℝ) + Real.log N) ^ (2 * ϑ⁻¹ + 3 / 2) ≤ (9 * (p : ℝ) ^ 2) ^ (2 * ϑ⁻¹ + 1) :=
    calc ((p : ℝ) + Real.log N) ^ (2 * ϑ⁻¹ + 3 / 2) ≤ (2 * (p : ℝ)) ^ (2 * ϑ⁻¹ + 3 / 2) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ ≤ (2 * (p : ℝ)) ^ ((2 : ℝ) * (2 * ϑ⁻¹ + 1)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = ((2 * (p : ℝ)) ^ (2 : ℝ)) ^ (2 * ϑ⁻¹ + 1) := Real.rpow_mul (by positivity) _ _
      _ ≤ (9 * (p : ℝ) ^ 2) ^ (2 * ϑ⁻¹ + 1) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
          rw [Real.rpow_two]; nlinarith
  have h1 : faCm ϑ⁻¹ * ((p : ℝ) + Real.log N) ^ (2 * ϑ⁻¹ + 3 / 2) * phiL C₀ L z x ≤
      faTau ϑ⁻¹ p * phiL C₀ L z x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 hCm0) hΦ
  have hτ : 0 ≤ faTau ϑ⁻¹ p * phiL C₀ L z x :=
    mul_nonneg (mul_nonneg hCm0 (Real.rpow_nonneg (by positivity) _)) hΦ
  have hρ : faRho C₀ ϑ⁻¹ p L z x = 6 * (faTau ϑ⁻¹ p * phiL C₀ L z x) := by unfold faRho; ring
  rw [List.length_nil, zero_add, pow_one, hρ]
  linarith

/-- Lemma 6.11 (b) for a nonempty path `γ ∈ 𝒯(k)`: Hölder with `2 o(γ) - 1` factors in
`L^{p(2o(γ)-1)}`, given (6.29) and (6.30) up to `Q ≥ p(2n₀+3)`. -/
private lemma size_part_b_cons {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.im)
    {L : Finset (Fin N)} (k : L) {n₀ : ℕ} {Q : ℝ}
    (hQ : (p : ℝ) * ((2 * n₀ + 3 : ℕ) : ℝ) ≤ Q) (x : Pair N → 𝕜)
    (hm1 : ∀ u v : L, u ≠ v → ∀ q : ℝ, 2 ≤ q → q ≤ Q →
      rowNorm M L q (fun w => schurM (toMatrix w) L z u v) x ≤ faTau ϑ⁻¹ p * phiL C₀ L z x)
    (hm3 : ∀ u : L, ∀ q : ℝ, 1 ≤ q → q ≤ Q →
      rowNorm M L q (fun w => 1 / schurM (toMatrix w) L z u u) x ≤ 6)
    (hτ : 0 ≤ faTau ϑ⁻¹ p * phiL C₀ L z x)
    {γ : List L} (hγ : γ ∈ faPath k n₀) (hne : γ ≠ []) :
    rowNorm M L p (fun w => faW L z k γ w - rowInt M {k.1} (faW L z k γ) w) x ≤
      2 * faRho C₀ ϑ⁻¹ p L z x ^ (γ.length + 1) := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by linarith
  obtain ⟨hlen, hk, hch⟩ := expansion_mem_faPath.1 hγ
  have hW := (inv_green_expansion M hM hϑ hz L k n₀).2.1 γ
  refine (size_rowNorm_Q_le M hM hϑ k.2 hW hp1 x).trans ?_
  rw [show faW L z k γ = fun w => ((size_Wfac (𝕜 := 𝕜) L z k γ).map (· w)).prod from
    funext (size_faW_eq L z k γ)]
  have hZ := size_zip_k_ne
    (fun a b : L => (fun w => schurM (toMatrix w) L z a b : (Pair N → 𝕜) → ℂ)) k hne hk hch
  have hpgZ : ∀ f ∈ List.zipWith
      (fun a b : L => (fun w => schurM (toMatrix w) L z a b : (Pair N → 𝕜) → ℂ)) (k :: γ)
      (γ ++ [k]), PolyGrowth f ∧ ∀ q, 2 ≤ q → q ≤ Q →
        rowNorm M L q f x ≤ faTau ϑ⁻¹ p * phiL C₀ L z x := by
    intro f hf
    obtain ⟨u, v, huv, rfl⟩ := hZ f hf
    exact ⟨((polyGrowth_schurM M C₀ hz L).1 u.1 v.1 u.2 v.2).2, hm1 u v huv⟩
  have hpgD : ∀ f ∈ γ.map
      (fun a : L => (fun w => 1 / schurM (toMatrix w) L z a a : (Pair N → 𝕜) → ℂ)),
      PolyGrowth f ∧ ∀ q, 1 ≤ q → q ≤ Q → rowNorm M L q f x ≤ 6 := by
    intro f hf
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hf
    exact ⟨((polyGrowth_schurM M C₀ hz L).2.1 u.1 u.2).2, hm3 u⟩
  have hpg : ∀ f ∈ size_Wfac (𝕜 := 𝕜) L z k γ, PolyGrowth f := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact (hpgZ f hf).1
    · exact (hpgD f hf).1
  have hne' : size_Wfac (𝕜 := 𝕜) L z k γ ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [size_length_Wfac] at this
    simp at this
  have hA := size_rowNorm_listProd_le M hM hϑ L x _ hne' hpg p hp1
  rw [size_length_Wfac] at hA
  have hE2 : (2 : ℝ) ≤ (p : ℝ) * ((2 * γ.length + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((2 * γ.length + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith
  have hEQ : (p : ℝ) * ((2 * γ.length + 1 : ℕ) : ℝ) ≤ Q := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hQ
    exact_mod_cast (by omega : 2 * γ.length + 1 ≤ 2 * n₀ + 3)
  have hprod : ((size_Wfac (𝕜 := 𝕜) L z k γ).map fun f =>
      rowNorm M L ((p : ℝ) * ((2 * γ.length + 1 : ℕ) : ℝ)) f x).prod ≤
      (faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (γ.length + 1) * 6 ^ γ.length := by
    obtain ⟨h10, h11⟩ := size_listProd_le_pow
      (fun f => rowNorm M L ((p : ℝ) * ((2 * γ.length + 1 : ℕ) : ℝ)) f x)
      (faTau ϑ⁻¹ p * phiL C₀ L z x) _
      (fun f hf => ⟨size_rowNorm_nonneg M L _ f x, (hpgZ f hf).2 _ hE2 hEQ⟩)
    obtain ⟨h20, h21⟩ := size_listProd_le_pow
      (fun f => rowNorm M L ((p : ℝ) * ((2 * γ.length + 1 : ℕ) : ℝ)) f x) 6 _
      (fun f hf => ⟨size_rowNorm_nonneg M L _ f x, (hpgD f hf).2 _ (by linarith) hEQ⟩)
    simp only [List.length_zipWith, List.length_cons, List.length_append, List.length_nil,
      List.length_map, min_self] at h11 h21
    simp only [size_Wfac, List.map_append, List.prod_append]
    exact mul_le_mul h11 h21 h20 (pow_nonneg hτ _)
  have hρ : faRho C₀ ϑ⁻¹ p L z x = 6 * (faTau ϑ⁻¹ p * phiL C₀ L z x) := by unfold faRho; ring
  calc 2 * rowNorm M L p (fun w => ((size_Wfac (𝕜 := 𝕜) L z k γ).map (· w)).prod) x
      ≤ 2 * ((faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (γ.length + 1) * 6 ^ γ.length) := by
        gcongr
        exact hA.trans hprod
    _ ≤ 2 * ((faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (γ.length + 1) * 6 ^ (γ.length + 1)) := by
        gcongr
        · norm_num
        · omega
    _ = 2 * faRho C₀ ϑ⁻¹ p L z x ^ (γ.length + 1) := by rw [hρ, mul_pow]; ring

/-- A term of `R_k` (6.20): Hölder with `2n₀ + 3` factors in `L^{p(2n₀+3)}`, the factor
`G^{(k)}_{a_{n₀} b}` being bounded by `N`. -/
private lemma size_term {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : 0 < z.im)
    {L : Finset (Fin N)} (k : L) (n₀ : ℕ) (x : Pair N → 𝕜)
    (hm1 : ∀ u v : L, u ≠ v → ∀ q : ℝ, 2 ≤ q → q ≤ (p : ℝ) * ((2 * n₀ + 3 : ℕ) : ℝ) →
      rowNorm M L q (fun w => schurM (toMatrix w) L z u v) x ≤ faTau ϑ⁻¹ p * phiL C₀ L z x)
    (hm3 : ∀ u : L, ∀ q : ℝ, 1 ≤ q → q ≤ (p : ℝ) * ((2 * n₀ + 3 : ℕ) : ℝ) →
      rowNorm M L q (fun w => 1 / schurM (toMatrix w) L z u u) x ≤ 6)
    (hG : ∀ u v : Fin N, ∀ q : ℝ, 1 ≤ q →
      rowNorm M L q (fun w => greenT (toMatrix w) {k.1} z u v) x ≤ N)
    (hτ : 0 ≤ faTau ϑ⁻¹ p * phiL C₀ L z x)
    {γ : List L} (hγ : γ ∈ (faPath k (n₀ + 1)).filter (fun γ => γ.length = n₀ + 1))
    {b : L} (hb : b ∈ (Finset.univ.erase k : Finset L)) :
    PolyGrowth (fun w => ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod) ∧
    rowNorm M L p (fun w => ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod) x ≤
      N * (faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (n₀ + 2) * 6 ^ n₀ := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by linarith
  set Q : ℝ := (p : ℝ) * ((2 * n₀ + 3 : ℕ) : ℝ) with hQdef
  have hQ2 : 2 ≤ Q := by
    rw [hQdef]
    have : (1 : ℝ) ≤ ((2 * n₀ + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith
  obtain ⟨hγ1, hγlen⟩ := Finset.mem_filter.1 hγ
  obtain ⟨-, hk, hch⟩ := expansion_mem_faPath.1 hγ1
  have hne : γ ≠ [] := by
    intro h
    rw [h] at hγlen
    simp at hγlen
  have hbk : b ≠ k := Finset.ne_of_mem_erase hb
  have hZ := size_zip_k_self_ne
    (fun a c : L => (fun w => schurM (toMatrix w) L z a c : (Pair N → 𝕜) → ℂ)) k hne hk hch
  have hpgZ : ∀ f ∈ List.zipWith
      (fun a c : L => (fun w => schurM (toMatrix w) L z a c : (Pair N → 𝕜) → ℂ)) (k :: γ) γ,
      PolyGrowth f ∧ ∀ q, 2 ≤ q → q ≤ Q → rowNorm M L q f x ≤ faTau ϑ⁻¹ p * phiL C₀ L z x := by
    intro f hf
    obtain ⟨u, v, huv, rfl⟩ := hZ f hf
    exact ⟨((polyGrowth_schurM M C₀ hz L).1 u.1 v.1 u.2 v.2).2, hm1 u v huv⟩
  have hpgD : ∀ f ∈ γ.dropLast.map
      (fun a : L => (fun w => 1 / schurM (toMatrix w) L z a a : (Pair N → 𝕜) → ℂ)),
      PolyGrowth f ∧ ∀ q, 1 ≤ q → q ≤ Q → rowNorm M L q f x ≤ 6 := by
    intro f hf
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hf
    exact ⟨((polyGrowth_schurM M C₀ hz L).2.1 u.1 u.2).2, hm3 u⟩
  have hpgM : PolyGrowth (fun w : Pair N → 𝕜 => schurM (toMatrix w) L z b k) :=
    ((polyGrowth_schurM M C₀ hz L).1 b.1 k.1 b.2 k.2).2
  have hpgG : PolyGrowth (fun w : Pair N → 𝕜 =>
      greenT (toMatrix w) {k.1} z (γ.getLastD k).1 b.1) :=
    ((polyGrowth_schurM M C₀ hz L).2.2.1 k.1 _ _).2
  have hpg : ∀ f ∈ size_Rfac (𝕜 := 𝕜) L z k γ b, PolyGrowth f := by
    intro f hf
    simp only [size_Rfac, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with (hf | hf) | rfl | rfl
    · exact (hpgZ f hf).1
    · exact (hpgD f hf).1
    · exact hpgM
    · exact hpgG
  have hlenR := size_length_Rfac (𝕜 := 𝕜) L z k γ b hne
  rw [hγlen] at hlenR
  have hne' : size_Rfac (𝕜 := 𝕜) L z k γ b ≠ [] := by
    intro h
    rw [h] at hlenR
    simp at hlenR
  have hA := size_rowNorm_listProd_le M hM hϑ L x _ hne' hpg p hp1
  have hEQ : (p : ℝ) * ((size_Rfac (𝕜 := 𝕜) L z k γ b).length : ℝ) = Q := by
    rw [hlenR, hQdef]
    congr 2
  rw [hEQ] at hA
  refine ⟨size_pg_listProd _ hpg, hA.trans ?_⟩
  obtain ⟨h10, h11⟩ := size_listProd_le_pow (fun f => rowNorm M L Q f x)
    (faTau ϑ⁻¹ p * phiL C₀ L z x) _
    (fun f hf => ⟨size_rowNorm_nonneg M L _ f x, (hpgZ f hf).2 _ hQ2 le_rfl⟩)
  obtain ⟨h20, h21⟩ := size_listProd_le_pow (fun f => rowNorm M L Q f x) 6 _
    (fun f hf => ⟨size_rowNorm_nonneg M L _ f x, (hpgD f hf).2 _ (by linarith) le_rfl⟩)
  simp only [List.length_zipWith, List.length_cons, List.length_map, List.length_dropLast,
    hγlen] at h11 h21
  rw [min_eq_right (by omega)] at h11
  have h3 : rowNorm M L Q (fun w => schurM (toMatrix w) L z b k) x ≤
      faTau ϑ⁻¹ p * phiL C₀ L z x := hm1 b k hbk Q hQ2 le_rfl
  have h4 : rowNorm M L Q (fun w => greenT (toMatrix w) {k.1} z (γ.getLastD k).1 b.1) x ≤ N :=
    hG _ _ Q (by linarith)
  simp only [size_Rfac, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  have h5 := size_rowNorm_nonneg M L Q (fun w => schurM (toMatrix w) L z b k) x
  have h6 := size_rowNorm_nonneg M L Q
    (fun w => greenT (toMatrix w) {k.1} z (γ.getLastD k).1 b.1) x
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc _ ≤ (faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (n₀ + 1) * 6 ^ (n₀ + 1 - 1) *
        (faTau ϑ⁻¹ p * phiL C₀ L z x * N) :=
        mul_le_mul (mul_le_mul h11 h21 h20 (pow_nonneg hτ _)) (mul_le_mul h3 h4 h6 hτ)
          (mul_nonneg h5 h6) (mul_nonneg (pow_nonneg hτ _) (by positivity))
    _ = N * (faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (n₀ + 2) * 6 ^ n₀ := by
        rw [Nat.add_sub_cancel]; ring

/-- Lemma 6.11 (c): Minkowski over the at most `r^{n₀+2}` terms of `R_k`, then
`N (rρ)^{⌈log N⌉} ≤ 1` from `rρ ≤ 1/8`. -/
private lemma size_part_c {p : ℕ} (hp : 2 ≤ p) (hN : 0 < N) {z : ℂ} (hz : 0 < z.im)
    {L : Finset (Fin N)} (k : L) (x : Pair N → 𝕜)
    (hm1 : ∀ u v : L, u ≠ v → ∀ q : ℝ, 2 ≤ q → q ≤ (p : ℝ) * ((2 * faN0 p N + 3 : ℕ) : ℝ) →
      rowNorm M L q (fun w => schurM (toMatrix w) L z u v) x ≤ faTau ϑ⁻¹ p * phiL C₀ L z x)
    (hm3 : ∀ u : L, ∀ q : ℝ, 1 ≤ q → q ≤ (p : ℝ) * ((2 * faN0 p N + 3 : ℕ) : ℝ) →
      rowNorm M L q (fun w => 1 / schurM (toMatrix w) L z u u) x ≤ 6)
    (hG : ∀ u v : Fin N, ∀ q : ℝ, 1 ≤ q →
      rowNorm M L q (fun w => greenT (toMatrix w) {k.1} z u v) x ≤ N)
    (hτ : 0 ≤ faTau ϑ⁻¹ p * phiL C₀ L z x)
    (hrρ : (L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x ≤ 1 / 8) :
    rowNorm M L p (fun w => faR L z k (faN0 p N) w - rowInt M {k.1} (faR L z k (faN0 p N)) w) x ≤
      2 * (L.card * faRho C₀ ϑ⁻¹ p L z x) ^ (2 * p + 2) := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR := (inv_green_expansion M hM hϑ hz L k (faN0 p N)).2.2.1
  refine (size_rowNorm_Q_le M hM hϑ k.2 hR hp1 x).trans ?_
  have hterm := fun γ hγ b hb =>
    size_term M hM hϑ hp hz k (faN0 p N) x hm1 hm3 hG hτ (γ := γ) hγ (b := b) hb
  have hfun : faR L z k (faN0 p N) = fun w => (-1) ^ faN0 p N *
      ∑ γ ∈ (faPath k (faN0 p N + 1)).filter (fun γ => γ.length = faN0 p N + 1),
        ∑ b ∈ Finset.univ.erase k, ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod :=
    funext (size_faR_eq L z k (faN0 p N))
  rw [hfun, size_rowNorm_congr_norm M L p (g := fun w =>
      ∑ γ ∈ (faPath k (faN0 p N + 1)).filter (fun γ => γ.length = faN0 p N + 1),
        ∑ b ∈ Finset.univ.erase k, ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod)
      (fun w => by simp)]
  set S := (faPath k (faN0 p N + 1)).filter (fun γ => γ.length = faN0 p N + 1) with hSdef
  set B : ℝ := N * (faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (faN0 p N + 2) * 6 ^ faN0 p N with hB
  have hB0 : 0 ≤ B := by positivity
  have hsum : rowNorm M L p (fun w => ∑ γ ∈ S, ∑ b ∈ Finset.univ.erase k,
      ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod) x ≤
      ∑ γ ∈ S, ∑ b ∈ (Finset.univ.erase k : Finset L), B := by
    refine (size_rowNorm_sum_le M hM hϑ L S
      (fun γ hγ => size_pg_sum _ fun b hb => (hterm γ hγ b hb).1) hp1 x).trans ?_
    refine Finset.sum_le_sum fun γ hγ => ?_
    refine (size_rowNorm_sum_le M hM hϑ L _ (fun b hb => (hterm γ hγ b hb).1) hp1 x).trans ?_
    exact Finset.sum_le_sum fun b hb => (hterm γ hγ b hb).2
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcount := (inv_green_expansion M hM hϑ hz L k (faN0 p N)).2.2.2.2.2.2
  have hcardE : (Finset.univ.erase k : Finset L).card = (L.erase k.1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_erase_of_mem k.2,
      Finset.card_univ, Fintype.card_coe]
  have hcount' : (S.card : ℝ) * ((Finset.univ.erase k : Finset L).card : ℝ) ≤
      (L.card : ℝ) ^ (faN0 p N + 2) := by
    rw [hcardE]; exact_mod_cast hcount
  have hρ : faRho C₀ ϑ⁻¹ p L z x = 6 * (faTau ϑ⁻¹ p * phiL C₀ L z x) := by unfold faRho; ring
  have hrρ0 : 0 ≤ (L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hρ]; positivity)
  set c := ⌈Real.log N⌉₊ with hcdef
  have hNc : (N : ℝ) * ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ c ≤ 1 := by
    have h1 : ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ c ≤ (1 / 8) ^ c :=
      pow_le_pow_left₀ hrρ0 hrρ c
    have h2 : (N : ℝ) ≤ 8 ^ c := by
      calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
        _ ≤ Real.exp c := Real.exp_le_exp.2 (Nat.le_ceil _)
        _ = Real.exp 1 ^ c := (Real.exp_one_pow c).symm
        _ ≤ 8 ^ c := pow_le_pow_left₀ (Real.exp_pos 1).le
            (by have := Real.exp_one_lt_d9; linarith) c
    calc (N : ℝ) * ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ c ≤ 8 ^ c * (1 / 8) ^ c :=
          mul_le_mul h2 h1 (pow_nonneg hrρ0 _) (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hn₀ : faN0 p N + 2 = c + (2 * p + 2) := by rw [faN0]; omega
  calc 2 * rowNorm M L p (fun w => ∑ γ ∈ S, ∑ b ∈ Finset.univ.erase k,
        ((size_Rfac (𝕜 := 𝕜) L z k γ b).map (· w)).prod) x
      ≤ 2 * ((S.card : ℝ) * ((Finset.univ.erase k : Finset L).card * B)) := by gcongr
    _ = 2 * (((S.card : ℝ) * (Finset.univ.erase k : Finset L).card) * B) := by ring
    _ ≤ 2 * ((L.card : ℝ) ^ (faN0 p N + 2) * B) := by gcongr
    _ ≤ 2 * ((L.card : ℝ) ^ (faN0 p N + 2) *
        (N * (faTau ϑ⁻¹ p * phiL C₀ L z x) ^ (faN0 p N + 2) * 6 ^ (faN0 p N + 2))) := by
        rw [hB]; gcongr
        · norm_num
        · omega
    _ = 2 * (N * ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ (faN0 p N + 2)) := by
        rw [hρ, mul_pow, mul_pow]; ring
    _ = 2 * (N * ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ c *
        ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ (2 * p + 2)) := by
        rw [hn₀, pow_add]; ring
    _ ≤ 2 * (1 * ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ (2 * p + 2)) := by
        gcongr
    _ = 2 * ((L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x) ^ (2 * p + 2) := by ring

end Parts

/-- Lemma 6.11: size of the terms of the expansion on `Ξ_L`, (a)–(c). -/
theorem faSize {N : ℕ} (M : Ensemble 𝕜 N) {ϑ δm δp C₀ : ℝ}
    (hM : M.Assumptions ϑ δm δp C₀) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {p : ℕ} (hp : 2 ≤ p)
    (hpe : Even p) (hN : 8 ≤ N) (hlog : Real.log N ≤ p) {z : ℂ} (hη : 1 / N ≤ z.im)
    {L : Finset (Fin N)} (hL1 : 1 ≤ L.card) (hLp : L.card ≤ p) (hLN : L.card < N) (k : L)
    {x : Pair N → 𝕜} (hx : x ∈ faXiL M C₀ ϑ⁻¹ p L z) :
    p * faRho C₀ ϑ⁻¹ p L z x ≤ 1 / 8 ∧
    (∀ γ ∈ faPath k (faN0 p N),
      rowNorm M L p (fun w => faW L z k γ w - rowInt M {k.1} (faW L z k γ) w) x ≤
        2 * faRho C₀ ϑ⁻¹ p L z x ^ (γ.length + 1)) ∧
    rowNorm M L p (fun w => faR L z k (faN0 p N) w - rowInt M {k.1} (faR L z k (faN0 p N)) w) x ≤
      2 * (L.card * faRho C₀ ϑ⁻¹ p L z x) ^ (2 * p + 2) := by
  have _ := hL1
  have _ := hpe
  have hNpos : 0 < N := by omega
  have hz : 0 < z.im := lt_of_lt_of_le (by positivity) hη
  have ha1 : (1 : ℝ) ≤ ϑ⁻¹ := (one_le_inv₀ hϑ).2 hϑ1
  have hΦ := size_phiL_nonneg (size_C₀_nonneg M hM hNpos) L z x
  have hτ : 0 ≤ faTau ϑ⁻¹ p * phiL C₀ L z x :=
    mul_nonneg (mul_nonneg (by linarith [size_one_le_faCm ha1])
      (Real.rpow_nonneg (by positivity) _)) hΦ
  obtain ⟨hQ2, hQ9, hQ13⟩ := size_Q_bounds (N := N) hp hlog
  have hm1 := size_m1 M hM hϑ hϑ1 hz hLN hQ9 x
  have hm3 := size_m3 M hM hϑ hϑ1 hp hη hLN hQ2 hQ13 hx
  have hG := size_G M (C₀ := C₀) hNpos hη L k.1
  have ha := size_part_a ha1 hp hx.1
  have hrρ : (L.card : ℝ) * faRho C₀ ϑ⁻¹ p L z x ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hLp)
      (by unfold faRho; linarith)).trans ha
  refine ⟨ha, fun γ hγ => ?_,
    size_part_c M hM hϑ hp hNpos hz k x hm1 hm3 (fun u v q hq => hG u v hq x) hτ hrρ⟩
  rcases eq_or_ne γ [] with rfl | hne
  · exact size_part_b_nil M hM hϑ hϑ1 hp hlog hz hLN k x
  · exact size_part_b_cons M hM hϑ hp hz k le_rfl x hm1 hm3 hτ hγ hne

end Rigidity
