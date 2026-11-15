import Mathlib

/-!
# The exponent ledger

The explicit exponents `C₁, …, C₅`, `c₀`, `b` of (A.1) and the value of `φ` of Lemma A.2
(Appendix A of NP v1.1), written as affine functions of `a = 1/ϑ`.
The relations (L1)–(L12) of Lemma A.1 and the identification `φ = 1/(2 C₄)`, `A₀ = 3/φ` of
Lemma A.2 are proved for every `a ≥ 1`. Numbers in this file refer to the blueprint NP v1.1.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Rigidity

/-- `C₁ = 18a + 20` of (A.1); `a = 1/ϑ`. -/
noncomputable def ledgerC1 (a : ℝ) : ℝ := 18 * a + 20
/-- `C₂ = 12a + 19` of (A.1). -/
noncomputable def ledgerC2 (a : ℝ) : ℝ := 12 * a + 19
/-- `C₃ = 24a + 36` of (A.1). -/
noncomputable def ledgerC3 (a : ℝ) : ℝ := 24 * a + 36
/-- `C₄ = 30a + 44` of (A.1). -/
noncomputable def ledgerC4 (a : ℝ) : ℝ := 30 * a + 44
/-- `C₅ = 18a + 21` of (A.1). -/
noncomputable def ledgerC5 (a : ℝ) : ℝ := 18 * a + 21
/-- `c₀ = 1/(8 C₃)` of (A.1). -/
noncomputable def ledgerc0 (a : ℝ) : ℝ := 1 / (8 * ledgerC3 a)
/-- `b = 12a + 12` of (A.1). -/
noncomputable def ledgerB (a : ℝ) : ℝ := 12 * a + 12
/-- `φ = 1/(60a + 88)` of Lemma A.2. -/
noncomputable def ledgerPhi (a : ℝ) : ℝ := 1 / (60 * a + 88)
/-- `A₀ = 180a + 264` of Lemma A.2. -/
noncomputable def ledgerA0 (a : ℝ) : ℝ := 180 * a + 264

/-- `c₀` as an explicit reciprocal of an affine function. -/
private lemma ledgerc0_eq (a : ℝ) : ledgerc0 a = 1 / (192 * a + 288) := by
  unfold ledgerc0 ledgerC3
  congr 1
  ring

/-- Lemma A.1: the relations (L1)–(L12). -/
theorem ledger_closes {a : ℝ} (ha : 1 ≤ a) :
    12 * a + 18 ≤ ledgerC1 a - 1 ∧
    ledgerc0 a * (6 * a + 6) ≤ 1 / 32 ∧
    18 * a + 17 ≤ ledgerC1 a - 1 ∧
    ledgerc0 a < 2 / (3 * (40 * a + 40)) ∧
    12 * a + 12 ≤ ledgerB a ∧
    ledgerB a + 7 ≤ ledgerC2 a ∧
    2 * ledgerB a + 12 ≤ ledgerC3 a ∧
    ledgerc0 a * (ledgerC1 a - 1) ≤ 1 / 3 ∧
    max (ledgerC1 a) (ledgerC2 a + 1 / 3) + 1 ≤ ledgerC5 a ∧
    max (ledgerC5 a) (ledgerC3 a + ledgerC5 a / 3) + 1 ≤ ledgerC4 a ∧
    ledgerc0 a * max (ledgerC1 a) (max (ledgerC3 a) (ledgerC5 a)) ≤ 1 / 8 ∧
    1 ≤ ledgerC1 a ∧ 1 ≤ ledgerC2 a ∧ 1 ≤ ledgerC3 a ∧ 1 ≤ ledgerC4 a ∧ 1 ≤ ledgerC5 a ∧
    0 < ledgerc0 a := by
  have hd : 0 < 192 * a + 288 := by linarith
  have hd2 : 0 < 3 * (40 * a + 40) := by linarith
  have hmax : max (ledgerC1 a) (max (ledgerC3 a) (ledgerC5 a)) = ledgerC3 a := by
    unfold ledgerC1 ledgerC3 ledgerC5
    rw [max_eq_left (show 18 * a + 21 ≤ 24 * a + 36 by linarith),
      max_eq_right (show 18 * a + 20 ≤ 24 * a + 36 by linarith)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ledgerC1; linarith
  · rw [ledgerc0_eq, one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    linarith
  · unfold ledgerC1; linarith
  · rw [ledgerc0_eq, div_lt_div_iff₀ hd hd2]
    linarith
  · unfold ledgerB; linarith
  · unfold ledgerB ledgerC2; linarith
  · unfold ledgerB ledgerC3; linarith
  · rw [ledgerc0_eq]
    unfold ledgerC1
    rw [one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    linarith
  · unfold ledgerC1 ledgerC2 ledgerC5
    have h : max (18 * a + 20) (12 * a + 19 + 1 / 3) ≤ 18 * a + 21 - 1 :=
      max_le (by linarith) (by linarith)
    linarith
  · unfold ledgerC3 ledgerC4 ledgerC5
    have h : max (18 * a + 21) (24 * a + 36 + (18 * a + 21) / 3) ≤ 30 * a + 44 - 1 :=
      max_le (by linarith) (by linarith)
    linarith
  · rw [hmax, ledgerc0]
    have : 0 < ledgerC3 a := by unfold ledgerC3; linarith
    rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · unfold ledgerC1; linarith
  · unfold ledgerC2; linarith
  · unfold ledgerC3; linarith
  · unfold ledgerC4; linarith
  · unfold ledgerC5; linarith
  · rw [ledgerc0_eq]; positivity

/-- Lemma A.2: the value of `φ` in Proposition 2.7 and `A₀ = 3/φ`. -/
theorem ledgerPhi_eq {a : ℝ} (ha : 1 ≤ a) :
    min (min (10 / ledgerC1 a) (2 / ledgerC2 a))
        (min (min (4 / ledgerC3 a) (1 / (2 * ledgerC4 a)))
          (min (1 / (2 * ledgerC5 a)) (5 * ledgerc0 a))) = ledgerPhi a ∧
      ledgerA0 a = 3 / ledgerPhi a := by
  have hd : 0 < 60 * a + 88 := by linarith
  have h1 : 0 < ledgerC1 a := by unfold ledgerC1; linarith
  have h2 : 0 < ledgerC2 a := by unfold ledgerC2; linarith
  have h3 : 0 < ledgerC3 a := by unfold ledgerC3; linarith
  have h4 : 0 < ledgerC4 a := by unfold ledgerC4; linarith
  have h5 : 0 < ledgerC5 a := by unfold ledgerC5; linarith
  have hd0 : 0 < 192 * a + 288 := by linarith
  have e4 : 1 / (2 * ledgerC4 a) = ledgerPhi a := by
    unfold ledgerPhi ledgerC4
    congr 1
    ring
  have hmin : min (min (10 / ledgerC1 a) (2 / ledgerC2 a))
        (min (min (4 / ledgerC3 a) (1 / (2 * ledgerC4 a)))
          (min (1 / (2 * ledgerC5 a)) (5 * ledgerc0 a))) = ledgerPhi a := by
    apply le_antisymm
    · rw [← e4]
      exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    · refine le_min (le_min ?_ ?_) (le_min (le_min ?_ ?_) (le_min ?_ ?_))
      · rw [ledgerPhi, div_le_div_iff₀ hd h1]
        unfold ledgerC1; linarith
      · rw [ledgerPhi, div_le_div_iff₀ hd h2]
        unfold ledgerC2; linarith
      · rw [ledgerPhi, div_le_div_iff₀ hd h3]
        unfold ledgerC3; linarith
      · rw [e4]
      · rw [ledgerPhi, div_le_div_iff₀ hd (by positivity)]
        unfold ledgerC5; linarith
      · rw [ledgerc0_eq, mul_one_div, ledgerPhi, div_le_div_iff₀ hd hd0]
        linarith
  refine ⟨hmin, ?_⟩
  unfold ledgerA0 ledgerPhi
  field_simp
  ring

/-- The products `φ C_i` used in Step 2 of Proposition 2.7 and after Lemma A.2. -/
theorem ledgerPhi_mul {a : ℝ} (ha : 1 ≤ a) :
    ledgerPhi a * ledgerC1 a ≤ 1 / 2 ∧ ledgerPhi a * ledgerC2 a ≤ 2 / 5 ∧
    ledgerPhi a * ledgerC3 a ≤ 1 / 2 ∧ ledgerPhi a * ledgerC4 a = 1 / 2 ∧
    ledgerPhi a * ledgerC5 a ≤ 2 / 5 ∧ ledgerPhi a ≤ 5 * ledgerc0 a ∧
    0 < ledgerPhi a ∧ ledgerPhi a < 1 ∧ 1 < ledgerA0 a := by
  have hd : 0 < 60 * a + 88 := by linarith
  have hd0 : 0 < 192 * a + 288 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ledgerPhi ledgerC1
    rw [one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    linarith
  · unfold ledgerPhi ledgerC2
    rw [one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    linarith
  · unfold ledgerPhi ledgerC3
    rw [one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    linarith
  · unfold ledgerPhi ledgerC4
    field_simp
    ring
  · unfold ledgerPhi ledgerC5
    rw [one_div_mul_eq_div, div_le_div_iff₀ hd (by norm_num)]
    linarith
  · rw [ledgerc0_eq, mul_one_div, ledgerPhi, div_le_div_iff₀ hd hd0]
    linarith
  · unfold ledgerPhi; positivity
  · unfold ledgerPhi
    rw [div_lt_one hd]
    linarith
  · unfold ledgerA0; linarith

end Rigidity
