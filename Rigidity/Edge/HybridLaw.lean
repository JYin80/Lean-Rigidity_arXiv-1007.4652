module

public import Rigidity.Ensemble.Basic
public import Rigidity.Ensemble.Moments

@[expose] public section

/-!
# Hybrid ensembles

Numbers refer to NP v1.1; the original is cited as [EYY, …].

Moment matching of two ensembles up to order two (Definition 11.3, (2.40)), the equality of
the variances it forces (Lemma 11.4 (i)), admissibility of an ensemble whose entry laws are
taken from two admissible, moment matching ensembles (Lemma 11.4 (ii)), the behaviour of moment
matching under `H ↦ -H` (Lemma 11.4 (iii)), and the hybrid sequence `M_0, …, M_Γ` of
Definition 11.3 that replaces the entry laws of `M^v` by those of `M^w` one pair at a time.
-/

open MeasureTheory Real Matrix Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace Rigidity

variable {𝕜 : Type*} [RCLike 𝕜]


namespace Ensemble

variable {N : ℕ}

/-- The second moment `∫ star y * y` is the real variance integral, cast to `𝕜`. -/
private lemma HybridLaw_integral_star_mul_self (μ : Measure 𝕜) :
    ∫ y, star y ^ 1 * y ^ 1 ∂μ = ((∫ y, ‖y‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
  rw [← integral_ofReal]
  congr 1
  ext y
  simp [RCLike.star_def, RCLike.conj_mul]

/-- Lemma 11.4 (i). -/
theorem MomentMatch2.varPair_eq {Mv Mw : Ensemble 𝕜 N} (h : MomentMatch2 Mv Mw) (p : Pair N) :
    Mv.varPair p = Mw.varPair p := by
  have h11 := h p 1 1 (by norm_num)
  rw [HybridLaw_integral_star_mul_self, HybridLaw_integral_star_mul_self] at h11
  exact_mod_cast h11

theorem MomentMatch2.symm {Mv Mw : Ensemble 𝕜 N} (h : MomentMatch2 Mv Mw) :
    MomentMatch2 Mw Mv := by
  intro p l u hlu
  exact (h p l u hlu).symm

/-- Lemma 11.4 (ii). -/
theorem Assumptions.of_law_mem {ϑ δm δp C₀ : ℝ} {Mv Mw : Ensemble 𝕜 N}
    (hv : Mv.Assumptions ϑ δm δp C₀) (hw : Mw.Assumptions ϑ δm δp C₀) (h : MomentMatch2 Mv Mw)
    (M : Ensemble 𝕜 N) (hM : ∀ p, M.law p = Mv.law p ∨ M.law p = Mw.law p) :
    M.Assumptions ϑ δm δp C₀ := by
  have hvar : ∀ p, M.varPair p = Mv.varPair p := by
    intro p
    rcases hM p with e | e
    · unfold Ensemble.varPair
      rw [e]
    · unfold Ensemble.varPair
      rw [e]
      exact (h.varPair_eq p).symm
  have hvar' : ∀ i j, M.var i j = Mv.var i j := fun i j => hvar _
  have hmat : M.varMatrix = Mv.varMatrix := by
    ext i j
    exact hvar' i j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rcases hM p with e | e
    · rw [e]
      exact hv.meanZero p
    · rw [e]
      exact hw.meanZero p
  · intro i
    rcases hM (Pair.mk' i i) with e | e
    · change ∀ᵐ y ∂M.law (Pair.mk' i i), RCLike.im y = 0
      rw [e]
      exact hv.diagReal i
    · change ∀ᵐ y ∂M.law (Pair.mk' i i), RCLike.im y = 0
      rw [e]
      exact hw.diagReal i
  · intro j
    simp only [hvar']
    exact hv.sumA j
  · intro v hv0
    simp only [hmat]
    exact hv.specB v hv0
  · intro i j
    rw [hvar']
    exact hv.boundC i j
  · intro p x hx
    rw [hvar p]
    rcases hM p with e | e
    · rw [e]
      exact hv.subexp p x hx
    · rw [e]
      have := hw.subexp p x hx
      rw [← h.varPair_eq p] at this
      exact this

/-- Lemma 11.4 (iii). -/
theorem MomentMatch2.smul_neg_one {Mv Mw : Ensemble 𝕜 N} (h : MomentMatch2 Mv Mw) :
    MomentMatch2 (Mv.smul (-1)) (Mw.smul (-1)) := by
  have key : ∀ (M : Ensemble 𝕜 N) (p : Pair N) (l u : ℕ),
      ∫ y, star y ^ l * y ^ u ∂(M.smul (-1)).law p =
        (-1 : 𝕜) ^ (l + u) * ∫ y, star y ^ l * y ^ u ∂M.law p := by
    intro M p l u
    change ∫ y, star y ^ l * y ^ u ∂(M.law p).map (fun y => (((-1 : ℝ) : ℝ) : 𝕜) * y) = _
    have hm : Measurable fun y : 𝕜 => (((-1 : ℝ) : ℝ) : 𝕜) * y := by fun_prop
    rw [integral_map hm.aemeasurable (by fun_prop), ← integral_const_mul]
    congr 1
    ext y
    have hc : (((-1 : ℝ) : ℝ) : 𝕜) = -1 := by simp
    rw [hc]
    simp only [neg_one_mul, star_neg]
    rw [neg_pow (star y) l, neg_pow y u, pow_add]
    ring
  intro p l u hlu
  rw [key, key, h p l u hlu]

/-- The hybrids `M_k` of Definition 11.3, for the enumeration `Fintype.equivFin (Pair N)`. -/
noncomputable def hybridSeq (Mv Mw : Ensemble 𝕜 N) (k : ℕ) : Ensemble 𝕜 N :=
  Mv.hybrid Mw {p | ((Fintype.equivFin (Pair N) p : Fin _) : ℕ) < k}

/-- Ensembles with the same entry laws are equal. -/
private lemma HybridLaw_ext {M M' : Ensemble 𝕜 N} (h : ∀ p, M.law p = M'.law p) : M = M' := by
  cases M
  cases M'
  have : (fun p => _) = _ := funext h
  subst this
  rfl

/-- The entry laws of `hybridSeq`. -/
private lemma HybridLaw_hybridSeq_law (Mv Mw : Ensemble 𝕜 N) (k : ℕ) (q : Pair N) :
    (hybridSeq Mv Mw k).law q =
      if ((Fintype.equivFin (Pair N) q : Fin _) : ℕ) < k then Mw.law q else Mv.law q := by
  unfold hybridSeq Ensemble.hybrid
  simp only [Set.mem_ofPred_eq]

theorem hybridSeq_zero (Mv Mw : Ensemble 𝕜 N) : hybridSeq Mv Mw 0 = Mv := by
  apply HybridLaw_ext
  intro q
  rw [HybridLaw_hybridSeq_law]
  simp

theorem hybridSeq_card (Mv Mw : Ensemble 𝕜 N) :
    hybridSeq Mv Mw (Fintype.card (Pair N)) = Mw := by
  apply HybridLaw_ext
  intro q
  rw [HybridLaw_hybridSeq_law]
  simp

/-- One step: `M_{k+1}` and `M_k` are `M_k` with the law at `p_{k+1}` set to `ν^w`, resp. `ν^v`. -/
theorem hybridSeq_succ (Mv Mw : Ensemble 𝕜 N) (k : ℕ) (hk : k < Fintype.card (Pair N)) :
    hybridSeq Mv Mw (k + 1) =
        (hybridSeq Mv Mw k).hybrid Mw {(Fintype.equivFin (Pair N)).symm ⟨k, hk⟩} ∧
      hybridSeq Mv Mw k =
        (hybridSeq Mv Mw k).hybrid Mv {(Fintype.equivFin (Pair N)).symm ⟨k, hk⟩} := by
  have hiff : ∀ q : Pair N, q = (Fintype.equivFin (Pair N)).symm ⟨k, hk⟩ ↔
      ((Fintype.equivFin (Pair N) q : Fin _) : ℕ) = k := by
    intro q
    rw [Equiv.eq_symm_apply]
    constructor
    · intro h; rw [h]
    · intro h; exact Fin.ext h
  constructor
  · apply HybridLaw_ext
    intro q
    rw [HybridLaw_hybridSeq_law]
    unfold Ensemble.hybrid
    simp only [Set.mem_singleton_iff]
    rw [HybridLaw_hybridSeq_law]
    by_cases hq : q = (Fintype.equivFin (Pair N)).symm ⟨k, hk⟩
    · have hn := (hiff q).mp hq
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hn : ((Fintype.equivFin (Pair N) q : Fin _) : ℕ) ≠ k := fun h => hq ((hiff q).mpr h)
      split_ifs <;> first | rfl | (exfalso; omega)
  · apply HybridLaw_ext
    intro q
    unfold Ensemble.hybrid
    simp only [Set.mem_singleton_iff]
    rw [HybridLaw_hybridSeq_law]
    by_cases hq : q = (Fintype.equivFin (Pair N)).symm ⟨k, hk⟩
    · have hn := (hiff q).mp hq
      split_ifs <;> first | rfl | (exfalso; omega)
    · have hn : ((Fintype.equivFin (Pair N) q : Fin _) : ℕ) ≠ k := fun h => hq ((hiff q).mpr h)
      split_ifs <;> rfl

theorem hybridSeq_law (Mv Mw : Ensemble 𝕜 N) (k : ℕ) (q : Pair N) :
    (hybridSeq Mv Mw k).law q = Mv.law q ∨ (hybridSeq Mv Mw k).law q = Mw.law q := by
  rw [HybridLaw_hybridSeq_law]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

end Ensemble

end Rigidity
