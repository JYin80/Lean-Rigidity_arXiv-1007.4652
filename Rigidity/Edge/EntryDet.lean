module

public import Rigidity.Edge.Resolvent

@[expose] public section

/-!
# The one-entry perturbation determinant

Numbers in this file refer to the blueprint NP v1.1; where the original paper
(Erdős–Yau–Yin, arXiv:1007.4652) has a counterpart, it is cited as [EYY, …].

For a hermitian `Q`, `z` in the upper half plane and a one-entry hermitian perturbation
`entryMat a b v` of Definition 11.3, `entryDet Q a b v z` is the `2 × 2` determinant of
Lemma 11.10 and `det (Q + entryMat a b v - z) = det (Q - z) * entryDet Q a b v z`.  The no-cut
statements (11.19) say that `entryDet` and `-G_aa` avoid the cut `(-∞, 0]`, so a branch of the
logarithm is available on the slit plane.
-/

open Real

namespace Rigidity

/-! ### `Rigidity/Edge/EntryDet.lean` — Lemma 11.10 -/

section EntryDetC
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `V_p(v)` of Definition 11.3: `v E^{(ab)} + v̄ E^{(ba)}` for `a ≠ b`, `(Re v) E^{(aa)}` for
`a = b`. -/
noncomputable def entryMat (a b : n) (v : ℂ) : Matrix n n ℂ :=
  if a = b then Matrix.single a a (v.re : ℂ) else Matrix.single a b v + Matrix.single b a (star v)

theorem entryMat_isHermitian (a b : n) (v : ℂ) : (entryMat a b v).IsHermitian := by
  unfold entryMat
  split_ifs with h
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

/-- `D_p(v; z)` of Lemma 11.10, with `R = G_Q(z)`. -/
noncomputable def entryDet (Q : Matrix n n ℂ) (a b : n) (v z : ℂ) : ℂ :=
  if a = b then 1 + (v.re : ℂ) * resolventMat Q z a a
  else 1 + (v * resolventMat Q z b a + star v * resolventMat Q z a b) -
    ((‖v‖ ^ 2 : ℝ) : ℂ) * (resolventMat Q z a a * resolventMat Q z b b -
      resolventMat Q z a b * resolventMat Q z b a)

/-- The `n × 2` matrix whose columns are the unit vectors at `p 0` and `p 1`. -/
private def entryDetFrame (p : Fin 2 → n) : Matrix n (Fin 2) ℂ :=
  Matrix.of fun i j => if i = p j then 1 else 0

open scoped Matrix in
private lemma entryDet_det_one_add (G : Matrix n n ℂ) (p : Fin 2 → n)
    (C : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 + G * (entryDetFrame p * C * (entryDetFrame p)ᵀ)).det =
      (1 + C * Matrix.of fun j k => G (p j) (p k)).det := by
  have h1 : G * (entryDetFrame p * C * (entryDetFrame p)ᵀ) =
      (G * entryDetFrame p) * (C * (entryDetFrame p)ᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.det_one_add_mul_comm]
  congr 2
  ext j k
  simp [Matrix.mul_apply, entryDetFrame, add_mul, Finset.sum_add_distrib, ite_mul]

private lemma entryDet_det_add {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (V : Matrix n n ℂ) :
    (Q + V - z • (1 : Matrix n n ℂ)).det =
      (Q - z • (1 : Matrix n n ℂ)).det * (1 + resolventMat Q z * V).det := by
  have h1 : Q + V - z • (1 : Matrix n n ℂ) =
      (Q - z • (1 : Matrix n n ℂ)) * (1 + resolventMat Q z * V) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc]
    have h2 : (Q - z • (1 : Matrix n n ℂ)) * resolventMat Q z = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hQ hz))
    rw [h2, Matrix.one_mul]
    abel
  rw [h1, Matrix.det_mul]

open scoped Matrix in
omit [Fintype n] in
private lemma entryDet_entryMat_eq_of_eq (a : n) (v : ℂ) :
    entryMat a a v = entryDetFrame ![a, a] * !![(v.re : ℂ), 0; 0, 0] *
      (entryDetFrame ![a, a])ᵀ := by
  ext i l
  simp [entryMat, entryDetFrame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : l = a <;> simp [h1, h2, eq_comm (a := a)]

open scoped Matrix in
omit [Fintype n] in
private lemma entryDet_entryMat_eq_of_ne {a b : n} (hab : a ≠ b) (v : ℂ) :
    entryMat a b v = entryDetFrame ![a, b] * !![0, v; star v, 0] *
      (entryDetFrame ![a, b])ᵀ := by
  ext i l
  simp [entryMat, hab, entryDetFrame, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : i = b <;> by_cases h3 : l = a <;> by_cases h4 : l = b <;>
    simp [h1, h2, h3, h4, hab, hab.symm, eq_comm (a := a), eq_comm (a := b)]

/-- Lemma 11.10, determinant identity. -/
theorem det_add_entryMat {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {z : ℂ} (hz : 0 < z.im)
    (a b : n) (v : ℂ) :
    (Q + entryMat a b v - z • (1 : Matrix n n ℂ)).det =
      (Q - z • (1 : Matrix n n ℂ)).det * entryDet Q a b v z := by
  rw [entryDet_det_add hQ hz.ne']
  congr 1
  by_cases hab : a = b
  · subst hab
    rw [entryDet_entryMat_eq_of_eq, entryDet_det_one_add, entryDet]
    rw [Matrix.det_fin_two]
    simp [Matrix.vecHead, Matrix.vecTail]
  · rw [entryDet_entryMat_eq_of_ne hab, entryDet_det_one_add, entryDet]
    rw [Matrix.det_fin_two]
    have hn : (‖v‖ : ℂ) ^ 2 = v * (starRingEnd ℂ) v := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    simp [hab, Matrix.vecHead, Matrix.vecTail, hn]
    ring

/-- Algebraic core of the no-cut argument (11.19): if the quadratic form of the `2 × 2` block
`[[p, r], [s, q]]` of a matrix has positive imaginary part on nonzero vectors and `Im q > 0`, then
`1 + (v s + v̄ r) - |v|² (p q - r s)` is not in `(-∞, 0]`. -/
private lemma entryDet_slit_aux (p q r s v : ℂ) (hv : v ≠ 0) (hq : 0 < q.im)
    (H : ∀ y₁ y₂ : ℂ, (y₁ ≠ 0 ∨ y₂ ≠ 0) →
      0 < (star y₁ * p * y₁ + star y₁ * r * y₂ + star y₂ * s * y₁ + star y₂ * q * y₂).im) :
    1 + (v * s + star v * r) - ((‖v‖ ^ 2 : ℝ) : ℂ) * (p * q - r * s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  set N : ℝ := ‖v‖ ^ 2 with hN
  have hNpos : 0 < N := by positivity
  have hNv : (N : ℂ) = v * star v := by
    rw [hN, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  set D : ℂ := 1 + (v * s + star v * r) - (N : ℂ) * (p * q - r * s) with hD
  have key := H ((N : ℂ) * q) (-((N : ℂ) * s + star v))
    (Or.inl (mul_ne_zero (by exact_mod_cast hNpos.ne') hq0))
  have hs1 : star ((N : ℂ) * q) = (N : ℂ) * star q := by simp
  have hs2 : star (-((N : ℂ) * s + star v)) = -((N : ℂ) * star s + v) := by
    simp
  rw [hs1, hs2] at key
  set F : ℂ := (N : ℂ) * star q * p * ((N : ℂ) * q) +
    (N : ℂ) * star q * r * -((N : ℂ) * s + star v) +
    -((N : ℂ) * star s + v) * s * ((N : ℂ) * q) +
    -((N : ℂ) * star s + v) * q * -((N : ℂ) * s + star v) with hF
  set x : ℂ := (N : ℂ) * star q * v * -((N : ℂ) * s + star v) with hx
  have hid : (N : ℂ) * F + (x + star x) = -(N : ℂ) ^ 2 * star q * D := by
    have hsx : star x = -((N : ℂ) * star s + v) * star v * ((N : ℂ) * q) := by
      simp [hx]
      ring
    rw [hsx, hx, hF, hD, hNv]
    ring
  have hDre : D = (D.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have him2 := congrArg Complex.im hid
  have hxs : (star x).im = -x.im := Complex.conj_im x
  have hL : ((N : ℂ) * F + (x + star x)).im = N * F.im := by
    rw [Complex.add_im, Complex.add_im, hxs]
    simp
  have hR : (-(N : ℂ) ^ 2 * star q * D).im = N ^ 2 * D.re * q.im := by
    rw [hDre]
    simp [Complex.mul_im, Complex.mul_re, pow_two]
    ring
  rw [hL, hR] at him2
  have h1 : 0 < N * F.im := mul_pos hNpos key
  have h2 : N ^ 2 * D.re * q.im ≤ 0 := by
    have : D.re * q.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hre hq.le
    nlinarith [sq_nonneg N]
  linarith

open scoped Matrix in
/-- The quadratic form of a matrix on `y₁ e_a + y₂ e_b` in terms of its entries. -/
private lemma entryDet_form_pair (G : Matrix n n ℂ) (a b : n) (y₁ y₂ : ℂ) :
    star (Pi.single a y₁ + Pi.single b y₂ : n → ℂ) ⬝ᵥ G *ᵥ (Pi.single a y₁ + Pi.single b y₂) =
      star y₁ * G a a * y₁ + star y₁ * G a b * y₂ + star y₂ * G b a * y₁ +
        star y₂ * G b b * y₂ := by
  simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-- (11.19), first part. -/
theorem entryDet_mem_slitPlane {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (a b : n) (v : ℂ) : entryDet Q a b v z ∈ Complex.slitPlane := by
  unfold entryDet
  split_ifs with hab
  · subst hab
    rw [Complex.mem_slitPlane_iff]
    by_cases hv : v.re = 0
    · left; simp [hv]
    · right
      have := im_resolventMat_diag_pos hQ hz a
      simp [hv, this.ne']
  · by_cases hv : v = 0
    · subst hv; simp
    · refine entryDet_slit_aux _ _ _ _ v hv (im_resolventMat_diag_pos hQ hz b) ?_
      intro y₁ y₂ hy
      have hw : (Pi.single a y₁ + Pi.single b y₂ : n → ℂ) ≠ 0 := by
        intro h0
        rcases hy with hy | hy
        · apply hy
          simpa [hab] using congrFun h0 a
        · apply hy
          simpa [Ne.symm hab] using congrFun h0 b
      have := Resolvent.im_form_pos hQ hz hw
      rwa [entryDet_form_pair] at this

/-- (11.19), second part. -/
theorem neg_resolventMat_mem_slitPlane {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (a : n) : -resolventMat Q z a a ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have := im_resolventMat_diag_pos hQ hz a
  rw [Complex.neg_im]
  exact neg_ne_zero.mpr this.ne'

end EntryDetC

end Rigidity
