import Rigidity.Edge.EntryDet
import Rigidity.Edge.Resolvent

/-!
# Good sets of matrices and the removed-entry bound

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a pair `p = (a, b)` of indices, `goodSet η Ψ E₁ E₂ a b` is the set `𝒢_p` of Definition 11.14:
the hermitian matrices `Q` with `|G_Q(y + iη)_{kl} + δ_{kl}| ≤ Ψ` for `k, l ∈ {a, b}` and all
`y ∈ [E₁, E₂]`.  For `η > 0` it is closed.  The endpoint condition (11.25) is the same inequality
at `y ∈ {E₁, E₂}` and holds on `𝒢_p` when `E₁ ≤ E₂`.

Lemma 11.15 (a) says that removing the entry `h = H_{ab}` from a hermitian `H`, with
`|h| ≤ t ≤ Ψ / 40` and `0 < Ψ ≤ 1 / 8`, changes the four resolvent entries at the indices `a, b`
by at most `(4 / 3) |h|` (11.26), and so maps matrices whose shifted entries are bounded by `Ψ / 2`
on the window into `𝒢_p`.  The proof uses the closed `m × m` identity `R = S + S V R` on the
indices `{a, b}`, where `S = G_H(z)`, `R = G_{H - V}(z)` and `V` is the removed hermitian
one-entry matrix of Definition 11.3.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


section GoodSetC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Definition 11.14: `𝒢_p` for `p = (a, b)`, with general `η`, `Ψ`, `E₁`, `E₂`. -/
def goodSet (η Ψ E₁ E₂ : ℝ) (a b : n) : Set (Matrix n n ℂ) :=
  {Q | Q.IsHermitian ∧ ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n), ∀ y ∈ Set.Icc E₁ E₂,
    ‖(resolventMat Q ⟨y, η⟩ + 1) k l‖ ≤ Ψ}

/-- The endpoint condition (11.25). -/
def EndpointGood (η Ψ E₁ E₂ : ℝ) (a b : n) (Q : Matrix n n ℂ) : Prop :=
  ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n), ∀ y ∈ ({E₁, E₂} : Set ℝ),
    ‖(resolventMat Q ⟨y, η⟩ + 1) k l‖ ≤ Ψ

omit [Fintype n] [DecidableEq n] in
/-- The hermitian matrices form a closed set. -/
private lemma goodSet_isClosed_isHermitian :
    IsClosed {Q : Matrix n n ℂ | Q.IsHermitian} := by
  have h : {Q : Matrix n n ℂ | Q.IsHermitian} = (fun Q : Matrix n n ℂ => Qᴴ - Q) ⁻¹' {0} := by
    ext Q
    simp [Matrix.IsHermitian, sub_eq_zero]
  rw [h]
  exact isClosed_singleton.preimage (continuous_id.matrix_conjTranspose.sub continuous_id)

/-- The resolvent at a fixed `z` with `Im z ≠ 0` is continuous at every hermitian matrix. -/
private lemma goodSet_continuousAt_resolventMat {z : ℂ} (hz : z.im ≠ 0) {Q : Matrix n n ℂ}
    (hQ : Q.IsHermitian) : ContinuousAt (fun P : Matrix n n ℂ => resolventMat P z) Q := by
  have hdet : (Q - z • (1 : Matrix n n ℂ)).det ≠ 0 := det_sub_smul_ne_zero hQ hz
  have h1 : ContinuousAt (Inv.inv : Matrix n n ℂ → Matrix n n ℂ)
      ((fun P : Matrix n n ℂ => P - z • (1 : Matrix n n ℂ)) Q) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have h2 : ContinuousAt (fun P : Matrix n n ℂ => P - z • (1 : Matrix n n ℂ)) Q :=
    (continuous_id.sub continuous_const).continuousAt
  exact ContinuousAt.comp (g := (Inv.inv : Matrix n n ℂ → Matrix n n ℂ))
    (f := fun P : Matrix n n ℂ => P - z • (1 : Matrix n n ℂ)) (x := Q) h1 h2

/-- One entry condition of `goodSet` cuts out a closed subset of the hermitian matrices. -/
private lemma goodSet_isClosed_entry {η : ℝ} (hη : 0 < η) (Ψ y : ℝ) (k l : n) :
    IsClosed {Q : Matrix n n ℂ | Q.IsHermitian ∧
      ‖(resolventMat Q ⟨y, η⟩ + 1) k l‖ ≤ Ψ} := by
  have hcont : ContinuousOn
      (fun Q : Matrix n n ℂ => ‖(resolventMat Q ⟨y, η⟩ + 1) k l‖)
      {Q : Matrix n n ℂ | Q.IsHermitian} := by
    intro Q hQ
    have h1 := goodSet_continuousAt_resolventMat (z := ⟨y, η⟩) hη.ne' hQ
    have h2 : ContinuousAt (fun P : Matrix n n ℂ => (resolventMat P ⟨y, η⟩ + 1) k l) Q :=
      continuousAt_pi.1 (continuousAt_pi.1 (h1.add continuousAt_const) k) l
    exact (continuous_norm.continuousAt.comp h2).continuousWithinAt
  exact hcont.preimage_isClosed_of_isClosed goodSet_isClosed_isHermitian isClosed_Iic

theorem isClosed_goodSet {η : ℝ} (hη : 0 < η) (Ψ E₁ E₂ : ℝ) (a b : n) :
    IsClosed (goodSet η Ψ E₁ E₂ a b) := by
  have h : goodSet η Ψ E₁ E₂ a b = {Q : Matrix n n ℂ | Q.IsHermitian} ∩
      ⋂ k ∈ ({a, b} : Set n), ⋂ l ∈ ({a, b} : Set n), ⋂ y ∈ Set.Icc E₁ E₂,
        {Q : Matrix n n ℂ | Q.IsHermitian ∧ ‖(resolventMat Q ⟨y, η⟩ + 1) k l‖ ≤ Ψ} := by
    ext Q
    simp only [goodSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hQ, h⟩
      exact ⟨hQ, fun k hk l hl y hy => ⟨hQ, h k hk l hl y hy⟩⟩
    · rintro ⟨hQ, h⟩
      exact ⟨hQ, fun k hk l hl y hy => (h k hk l hl y hy).2⟩
  rw [h]
  refine goodSet_isClosed_isHermitian.inter ?_
  refine isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun l =>
    isClosed_iInter fun _ => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact goodSet_isClosed_entry hη Ψ y k l

theorem endpointGood_of_mem_goodSet {η Ψ E₁ E₂ : ℝ} (hE : E₁ ≤ E₂) {a b : n}
    {Q : Matrix n n ℂ} (hQ : Q ∈ goodSet η Ψ E₁ E₂ a b) : EndpointGood η Ψ E₁ E₂ a b Q := by
  intro k hk l hl y hy
  refine hQ.2 k hk l hl y ?_
  rcases hy with rfl | hy
  · exact ⟨le_rfl, hE⟩
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hE, le_rfl⟩

/-- The closed identity `R = S + S V R` for the resolvents of `H` and of `H` with the entry
`H a b` removed (proof of Lemma 11.15 (a)). -/
private lemma goodSet_removed_eq {H : Matrix n n ℂ} (hH : H.IsHermitian) {η : ℝ} (hη : 0 < η)
    (y : ℝ) (a b : n) :
    resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ =
      resolventMat H ⟨y, η⟩ + resolventMat H ⟨y, η⟩ * entryMat a b (H a b) *
        resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ := by
  have hQ := hH.sub (entryMat_isHermitian a b (H a b))
  have h := resolventMat_sub_resolventMat hH hQ (z := ⟨y, η⟩) hη.ne'
  rw [sub_sub_cancel_left, Matrix.mul_neg, Matrix.neg_mul] at h
  calc resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩
      = resolventMat H ⟨y, η⟩ - (resolventMat H ⟨y, η⟩ -
          resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩) := by abel
    _ = _ := by rw [h]; abel

/-- Entry of `S V R` for `V = entryMat a b v` with `a ≠ b`. -/
private lemma goodSet_prod_ne {a b : n} (hab : a ≠ b) (v : ℂ) (S R : Matrix n n ℂ) (k l : n) :
    (S * entryMat a b v * R) k l = S k a * v * R b l + S k b * star v * R a l := by
  simp only [entryMat, hab, ↓reduceIte]
  simp [Matrix.mul_add, Matrix.mul_apply, Matrix.single_apply, ite_and,
    Finset.sum_ite_eq, _root_.add_mul, Finset.sum_add_distrib, ite_mul]

/-- Entry of `S V R` for `V = entryMat a a v`. -/
private lemma goodSet_prod_eq (a : n) (v : ℂ) (S R : Matrix n n ℂ) (k l : n) :
    (S * entryMat a a v * R) k l = S k a * (v.re : ℂ) * R a l := by
  simp only [entryMat, ↓reduceIte]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

omit [Fintype n] in
/-- Entrywise bound for `S` from a bound for `S + 1`. -/
private lemma goodSet_norm_le_of_add_one {S : Matrix n n ℂ} {c : ℝ} {k l : n}
    (h : ‖(S + 1) k l‖ ≤ c) : ‖S k l‖ ≤ (if k = l then 1 else 0) + c := by
  have h1 : S k l = (S + 1) k l - (1 : Matrix n n ℂ) k l := by simp
  have h2 : ‖(1 : Matrix n n ℂ) k l‖ = if k = l then 1 else 0 := by
    by_cases hkl : k = l <;> simp [Matrix.one_apply, hkl]
  calc ‖S k l‖ = ‖(S + 1) k l - (1 : Matrix n n ℂ) k l‖ := by rw [← h1]
    _ ≤ ‖(S + 1) k l‖ + ‖(1 : Matrix n n ℂ) k l‖ := norm_sub_le _ _
    _ ≤ (if k = l then 1 else 0) + c := by rw [h2]; linarith

/-- The `{a, b} × {a, b}` bound of (11.26): if `R = S + S V R` with `V = entryMat a b h`,
`|h| ≤ Ψ / 40`, `0 < Ψ ≤ 1 / 8` and `|(S + 1)_{kl}| ≤ Ψ / 2` on `{a, b}`, then
`|R_{kl} - S_{kl}| ≤ (4 / 3) |h|` on `{a, b}`. -/
private lemma goodSet_removed_bound {S R : Matrix n n ℂ} {Ψ : ℝ} {a b : n} {h : ℂ}
    (hid : R = S + S * entryMat a b h * R) (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8)
    (hh : ‖h‖ ≤ Ψ / 40)
    (hS : ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n), ‖(S + 1) k l‖ ≤ Ψ / 2) :
    ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n), ‖R k l - S k l‖ ≤ 4 / 3 * ‖h‖ := by
  have hmem : ∀ j ∈ ({a, b} : Set n), j = a ∨ j = b := by
    intro j hj
    simpa using hj
  have ha : a ∈ ({a, b} : Set n) := Set.mem_insert _ _
  have hb : b ∈ ({a, b} : Set n) := Set.mem_insert_of_mem _ rfl
  have hS' := fun k hk l hl => goodSet_norm_le_of_add_one (hS k hk l hl)
  have hSc : ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n), ‖S k l‖ ≤ 1 + Ψ / 2 := by
    intro k hk l hl
    refine (hS' k hk l hl).trans ?_
    split_ifs <;> linarith
  have hrow : ∀ k ∈ ({a, b} : Set n), a ≠ b → ‖S k a‖ + ‖S k b‖ ≤ 1 + Ψ := by
    intro k hk hab
    rcases hmem k hk with h1 | h1
    · have e1 := hS' k hk a ha
      have e2 := hS' k hk b hb
      rw [h1] at e1 e2
      simp only [↓reduceIte, hab] at e1 e2
      rw [h1]
      linarith
    · have e1 := hS' k hk a ha
      have e2 := hS' k hk b hb
      rw [h1] at e1 e2
      simp only [↓reduceIte, Ne.symm hab] at e1 e2
      rw [h1]
      linarith
  set M : ℝ := max (max ‖R a a‖ ‖R a b‖) (max ‖R b a‖ ‖R b b‖) with hMdef
  have hM : ∀ j ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n), ‖R j l‖ ≤ M := by
    intro j hj l hl
    rcases hmem j hj with h1 | h1 <;> rcases hmem l hl with h2 | h2 <;> rw [h1, h2] <;>
      simp [hMdef]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ha a ha)
  have hdiff : ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n),
      ‖R k l - S k l‖ ≤ (1 + Ψ) * ‖h‖ * M := by
    intro k hk l hl
    have hRS : R k l - S k l = (S * entryMat a b h * R) k l := by
      have e := congrFun (congrFun hid k) l
      rw [Matrix.add_apply] at e
      rw [sub_eq_iff_eq_add']
      exact e
    by_cases hab : a = b
    · subst hab
      rw [hRS, goodSet_prod_eq]
      calc ‖S k a * (h.re : ℂ) * R a l‖ = ‖S k a‖ * |h.re| * ‖R a l‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (1 + Ψ) * ‖h‖ * M := by
            have e1 : ‖S k a‖ ≤ 1 + Ψ := by linarith [hSc k hk a ha]
            have e2 : |h.re| ≤ ‖h‖ := Complex.abs_re_le_norm h
            have e3 := hM a ha l hl
            gcongr
    · rw [hRS, goodSet_prod_ne hab]
      calc ‖S k a * h * R b l + S k b * star h * R a l‖
          ≤ ‖S k a * h * R b l‖ + ‖S k b * star h * R a l‖ := norm_add_le _ _
        _ ≤ ‖S k a‖ * ‖h‖ * M + ‖S k b‖ * ‖h‖ * M := by
            rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_star]
            have e1 := hM b hb l hl
            have e2 := hM a ha l hl
            gcongr
        _ = (‖S k a‖ + ‖S k b‖) * ‖h‖ * M := by ring
        _ ≤ (1 + Ψ) * ‖h‖ * M := by
            have e1 := hrow k hk hab
            gcongr
  have hhw : ‖h‖ ≤ 1 / 320 := by linarith
  have hRc : ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n),
      ‖R k l‖ ≤ (1 + Ψ / 2) + (1 + Ψ) * ‖h‖ * M := by
    intro k hk l hl
    calc ‖R k l‖ = ‖S k l + (R k l - S k l)‖ := by congr 1; ring
      _ ≤ ‖S k l‖ + ‖R k l - S k l‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hSc k hk l hl) (hdiff k hk l hl)
  have hMle : M ≤ (1 + Ψ / 2) + (1 + Ψ) * ‖h‖ * M :=
    max_le (max_le (hRc a ha a ha) (hRc a ha b hb)) (max_le (hRc b hb a ha) (hRc b hb b hb))
  have hτ : (1 + Ψ) * ‖h‖ ≤ 9 / 2560 := by nlinarith [norm_nonneg h]
  have hτM : (1 + Ψ) * ‖h‖ * M ≤ 9 / 2560 * M := by gcongr
  have hM1 : M ≤ 107 / 100 := by linarith
  have hfin : (1 + Ψ) * M ≤ 4 / 3 := by nlinarith [mul_nonneg hM0 (sub_nonneg.2 hΨ')]
  intro k hk l hl
  calc ‖R k l - S k l‖ ≤ (1 + Ψ) * ‖h‖ * M := hdiff k hk l hl
    _ = ‖h‖ * ((1 + Ψ) * M) := by ring
    _ ≤ ‖h‖ * (4 / 3) := by gcongr
    _ = 4 / 3 * ‖h‖ := by ring

/-- Lemma 11.15 (a), pointwise form (11.26). -/
theorem resolventMat_entryRemoved_le {H : Matrix n n ℂ} (hH : H.IsHermitian) {η Ψ t : ℝ}
    (hη : 0 < η) (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8) (ht : t ≤ Ψ / 40) {a b : n}
    (hab : ‖H a b‖ ≤ t) (y : ℝ)
    (hS : ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n),
      ‖(resolventMat H ⟨y, η⟩ + 1) k l‖ ≤ Ψ / 2) :
    ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n),
      ‖resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ k l - resolventMat H ⟨y, η⟩ k l‖ ≤
          4 / 3 * ‖H a b‖ ∧
        ‖(resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ + 1) k l‖ ≤ Ψ := by
  have hid := goodSet_removed_eq hH hη y a b
  have hdiff := goodSet_removed_bound hid hΨ hΨ' (hab.trans ht) hS
  intro k hk l hl
  have h1 := hdiff k hk l hl
  refine ⟨h1, ?_⟩
  have h2 : (resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ + 1) k l =
      (resolventMat H ⟨y, η⟩ + 1) k l +
        (resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ k l - resolventMat H ⟨y, η⟩ k l) := by
    simp only [Matrix.add_apply]
    ring
  rw [h2]
  have h3 := hab.trans ht
  calc _ ≤ ‖(resolventMat H ⟨y, η⟩ + 1) k l‖ +
        ‖resolventMat (H - entryMat a b (H a b)) ⟨y, η⟩ k l - resolventMat H ⟨y, η⟩ k l‖ :=
        norm_add_le _ _
    _ ≤ Ψ / 2 + 4 / 3 * ‖H a b‖ := add_le_add (hS k hk l hl) h1
    _ ≤ Ψ := by linarith

/-- Lemma 11.15 (a). -/
theorem mem_goodSet_entryRemoved {H : Matrix n n ℂ} (hH : H.IsHermitian) {η Ψ t E₁ E₂ : ℝ}
    (hη : 0 < η) (hΨ : 0 < Ψ) (hΨ' : Ψ ≤ 1 / 8) (ht : t ≤ Ψ / 40) {a b : n}
    (hab : ‖H a b‖ ≤ t)
    (hS : ∀ y ∈ Set.Icc E₁ E₂, ∀ k ∈ ({a, b} : Set n), ∀ l ∈ ({a, b} : Set n),
      ‖(resolventMat H ⟨y, η⟩ + 1) k l‖ ≤ Ψ / 2) :
    H - entryMat a b (H a b) ∈ goodSet η Ψ E₁ E₂ a b := by
  refine ⟨hH.sub (entryMat_isHermitian a b (H a b)), fun k hk l hl y hy => ?_⟩
  exact (resolventMat_entryRemoved_le hH hη hΨ hΨ' ht hab y (hS y hy) k hk l hl).2

end GoodSetC

end Rigidity
