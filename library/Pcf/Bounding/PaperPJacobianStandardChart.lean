/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianSchemeChart
public import Pcf.Bounding.PaperPJacobianOverlap
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The polynomial coordinates on a standard projective chart

This identifies the degree-zero localization at the last homogeneous
coordinate with the polynomial ring in the remaining affine coordinates.
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K
local notation "lastX" => (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K)

/-- Dehomogenization commutes with evaluation in an arbitrary coefficient
algebra, not only at ground-field rational points. -/
theorem paperPDehomogenize_aeval_algebra {L : Type v} [CommSemiring L] [Algebra K L]
    (P : MvPolynomial (Fin n ⊕ Unit) K) (x : Fin n → L) :
    aeval x (paperPDehomogenize P) = aeval (Sum.elim x (fun _ : Unit => 1)) P := by
  simp only [paperPDehomogenize, comp_aeval_apply]
  congr 1
  ext j
  cases j with
  | inl i => simp
  | inr j => cases j; simp

/-- The homogeneous scaling identity is valid after extending the
coefficient field, so it can also be used at generic coordinates. -/
theorem paperPHomogeneous_aeval_smul {L : Type v} [Field L] [Algebra K L]
    (P : MvPolynomial (Fin n ⊕ Unit) K) (d : ℕ) (hP : P.IsHomogeneous d)
    (x : Fin n ⊕ Unit → L) (t : L) :
    aeval (fun j => t * x j) P = t ^ d * aeval x P := by
  simpa only [eval_map, aeval_def] using
    paperPHomogeneous_eval_smul (map (algebraMap K L) P) d (hP.map _) x t

/-- Setting the last coordinate to one is injective on each fixed
homogeneous component, including over finite fields. -/
theorem paperPDehomogenize_eq_zero_of_isHomogeneous
    (P : MvPolynomial (Fin n ⊕ Unit) K) (d : ℕ) (hP : P.IsHomogeneous d)
    (hzero : paperPDehomogenize P = 0) : P = 0 := by
  let L := FractionRing (MvPolynomial (Fin n ⊕ Unit) K)
  let x : Fin n ⊕ Unit → L :=
    fun j => algebraMap (MvPolynomial (Fin n ⊕ Unit) K) L (X j)
  have hx : x (Sum.inr ()) ≠ 0 := by
    simpa only [x, map_zero] using
      (IsFractionRing.injective (MvPolynomial (Fin n ⊕ Unit) K) L).ne
        (X_ne_zero (Sum.inr ()))
  let t := (x (Sum.inr ()))⁻¹
  have ht : t ≠ 0 := inv_ne_zero hx
  have hn : Sum.elim (fun i : Fin n => t * x (Sum.inl i)) (fun _ : Unit => (1 : L)) =
      (fun j => t * x j) := by
    ext j
    cases j with
    | inl i => rfl
    | inr j => cases j; exact (inv_mul_cancel₀ hx).symm
  have hz : aeval (fun j => t * x j) P = 0 := by
    rw [← hn, ← paperPDehomogenize_aeval_algebra]
    simp [hzero]
  rw [paperPHomogeneous_aeval_smul P d hP x t] at hz
  have he : aeval x P = 0 := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero d ht)
  have heval : aeval x = IsScalarTower.toAlgHom K (MvPolynomial (Fin n ⊕ Unit) K) L := by
    ext j
    simp [x]
  rw [heval] at he
  exact (IsFractionRing.injective (MvPolynomial (Fin n ⊕ Unit) K) L)
    (by simpa using he)

/-- Restrict dehomogenization to the degree-zero localization at the last
coordinate. The last coordinate maps to one, so the localization lift exists. -/
noncomputable def paperPStandardChartDehomogenize :
    Away polyGrade lastX →+* MvPolynomial (Fin n) K := by
  let f : Localization.Away lastX →+* MvPolynomial (Fin n) K :=
    IsLocalization.Away.lift lastX (g := (paperPDehomogenize (K := K) (n := n)).toRingHom)
      (by simp [paperPDehomogenize])
  exact f.comp (algebraMap (Away polyGrade lastX) (Localization.Away lastX))

@[simp] theorem paperPStandardChartDehomogenize_mk
    (m : ℕ) (P : MvPolynomial (Fin n ⊕ Unit) K) (hP : P ∈ polyGrade m) :
    paperPStandardChartDehomogenize
      (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) m P (by simpa using hP)) =
      paperPDehomogenize P := by
  let f : Localization.Away lastX →+* MvPolynomial (Fin n) K :=
    IsLocalization.Away.lift lastX (g := (paperPDehomogenize (K := K) (n := n)).toRingHom)
      (by simp [paperPDehomogenize])
  change f (Localization.mk P ⟨lastX ^ m, by use m⟩) = paperPDehomogenize P
  rw [Localization.mk_eq_mk']
  have hs := congrArg f (IsLocalization.mk'_spec (M := Submonoid.powers lastX)
    (Localization.Away lastX) P
    ⟨lastX ^ m, by use m⟩)
  rw [map_mul] at hs
  simp only [f, IsLocalization.Away.lift_eq] at hs
  change f (IsLocalization.mk' (Localization.Away lastX) P
    ⟨lastX ^ m, by use m⟩) * paperPDehomogenize (lastX ^ m) = paperPDehomogenize P at hs
  have hden : paperPDehomogenize (K := K) (n := n) lastX = 1 := by
    simp [paperPDehomogenize]
  rw [map_pow, hden, one_pow, mul_one] at hs
  exact hs

/-- Dehomogenization is injective on degree-zero standard-chart fractions. -/
theorem paperPStandardChartDehomogenize_injective :
    Function.Injective (paperPStandardChartDehomogenize (K := K) (n := n)) := by
  have hker : ∀ z : Away polyGrade lastX, paperPStandardChartDehomogenize z = 0 → z = 0 := by
    intro z hz
    obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective polyGrade (isHomogeneous_X K (Sum.inr ())) z
    have hzero : paperPDehomogenize P = 0 :=
      (paperPStandardChartDehomogenize_mk m P (by simpa using hP)).symm.trans hz
    have hPzero : P = 0 :=
      paperPDehomogenize_eq_zero_of_isHomogeneous P m (by simpa using hP) hzero
    apply HomogeneousLocalization.mk_eq_zero_of_num
    exact Subtype.ext hPzero
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hab, sub_self]

/-- Every affine polynomial is the dehomogenization of a regular function
on the standard projective coordinate chart. -/
theorem paperPStandardChartDehomogenize_surjective :
    Function.Surjective (paperPStandardChartDehomogenize (K := K) (n := n)) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) 0 (C c)
      (by simp), ?_⟩
    simp [paperPDehomogenize]
  | add P Q hP hQ =>
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hQ
    exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | mul_X P i hP =>
    obtain ⟨p, hp⟩ := hP
    refine ⟨p * Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) 1 (X (Sum.inl i))
      (by simpa using isHomogeneous_X K (Sum.inl i)), ?_⟩
    rw [map_mul, hp]
    congr 1
    have h := paperPStandardChartDehomogenize_mk (K := K) (n := n) 1
      (X (Sum.inl i)) (isHomogeneous_X K (Sum.inl i))
    simpa [paperPDehomogenize] using h

/-- The standard degree-zero homogeneous localization is the actual
polynomial ring in the affine coordinate ratios. -/
noncomputable def paperPStandardChartRingEquiv :
    Away polyGrade lastX ≃+* MvPolynomial (Fin n) K :=
  RingEquiv.ofBijective paperPStandardChartDehomogenize
    ⟨paperPStandardChartDehomogenize_injective, paperPStandardChartDehomogenize_surjective⟩

/-- The actual standard projective open is affine `n`-space with its
usual polynomial coordinate ring.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
noncomputable def paperPStandardChartSchemeIso :
    (AlgebraicGeometry.Proj.basicOpen polyGrade lastX).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec polyGrade lastX
    (isHomogeneous_X K (Sum.inr ())) Nat.zero_lt_one ≪≫
    (Scheme.Spec.mapIso paperPStandardChartRingEquiv.toCommRingCatIso.op).symm

/-- The affine coordinate `x_i` corresponds to the homogeneous ratio
`x_i / x_N` in the standard chart ring. -/
theorem paperPStandardChartRingEquiv_symm_X (i : Fin n) :
    (paperPStandardChartRingEquiv (K := K) (n := n)).symm (X i) =
      Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) 1 (X (Sum.inl i))
        (by simpa using isHomogeneous_X K (Sum.inl i)) := by
  apply paperPStandardChartRingEquiv.injective
  rw [RingEquiv.apply_symm_apply]
  change X i = paperPStandardChartDehomogenize _
  have h := paperPStandardChartDehomogenize_mk (K := K) (n := n) 1
    (X (Sum.inl i)) (isHomogeneous_X K (Sum.inl i))
  simpa [paperPDehomogenize] using h.symm

/-- Constants correspond to degree-zero homogeneous fractions. -/
theorem paperPStandardChartRingEquiv_symm_C (c : K) :
    (paperPStandardChartRingEquiv (K := K) (n := n)).symm (C c) =
      Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) 0 (C c)
        (by simp) := by
  apply paperPStandardChartRingEquiv.injective
  rw [RingEquiv.apply_symm_apply]
  change C c = paperPStandardChartDehomogenize _
  simp [paperPDehomogenize]

#print axioms paperPStandardChartSchemeIso
#print axioms paperPStandardChartRingEquiv_symm_X
#print axioms paperPStandardChartRingEquiv_symm_C
#print axioms paperPStandardChartDehomogenize_injective
#print axioms paperPStandardChartDehomogenize_surjective
#print axioms paperPStandardChartRingEquiv
#print axioms paperPStandardChartDehomogenize
#print axioms paperPStandardChartDehomogenize_mk
#print axioms paperPDehomogenize_eq_zero_of_isHomogeneous
end Pcf
