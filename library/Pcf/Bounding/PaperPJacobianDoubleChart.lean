/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianStandardChart
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The polynomial model of a projective double chart

The actual homogeneous coordinate ring of `D₊(x_N F_N)` is isomorphic to the
polynomial affine chart localized at `F_N(x_0,…,x_{N-1},1)`.
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K
local notation "lastX" => (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K)

/-- Under standard dehomogenization, the element whose inversion opens
`F_N ≠ 0` is exactly the dehomogenized target denominator. -/
theorem paperPDoubleChart_localizationElement
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    paperPStandardChartRingEquiv (K := K) (n := n)
        (Away.isLocalizationElem (isHomogeneous_X K (Sum.inr ())) (hF (Sum.inr ()))) =
      paperPDehomogenize (F (Sum.inr ())) := by
  change paperPStandardChartDehomogenize
    (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) d (F (Sum.inr ()) ^ 1) _) = _
  have hp : (F (Sum.inr ()) ^ 1).IsHomogeneous d := by
    simpa only [pow_one] using hF (Sum.inr ())
  exact (paperPStandardChartDehomogenize_mk d (F (Sum.inr ()) ^ 1) hp).trans
    (congrArg paperPDehomogenize (pow_one (F (Sum.inr ()))))

/-- The degree-zero homogeneous localization of the actual projective
double chart is the polynomial localization used by the affine Jacobian proofs. -/
noncomputable def paperPDoubleChartRingEquiv
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    Away polyGrade (lastX * F (Sum.inr ())) ≃+* PaperPChartRing F := by
  let : Algebra (Away polyGrade lastX) (Away polyGrade (lastX * F (Sum.inr ()))) :=
    (awayMap polyGrade (hF (Sum.inr ())) rfl).toAlgebra
  let : IsLocalization.Away
      (Away.isLocalizationElem (isHomogeneous_X K (Sum.inr ())) (hF (Sum.inr ())))
      (Away polyGrade (lastX * F (Sum.inr ()))) :=
    Away.isLocalization_mul (isHomogeneous_X K (Sum.inr ())) (hF (Sum.inr ())) rfl
      Nat.one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (Away.isLocalizationElem (isHomogeneous_X K (Sum.inr ())) (hF (Sum.inr ()))))
    (T := Submonoid.powers (paperPDehomogenize (F (Sum.inr ()))))
    (Away polyGrade (lastX * F (Sum.inr ()))) (PaperPChartRing F)
    (paperPStandardChartRingEquiv (K := K) (n := n)) (by
    rw [Submonoid.map_powers]
    congr 1
    exact paperPDoubleChart_localizationElement F d hF)

/-- The actual projective double-chart open is the affine scheme of the
polynomial localization used in the Jacobian criterion.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
noncomputable def paperPDoubleChartSchemeIso
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    (AlgebraicGeometry.Proj.basicOpen polyGrade (lastX * F (Sum.inr ()))).toScheme ≅
      Spec (CommRingCat.of (PaperPChartRing F)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec polyGrade (lastX * F (Sum.inr ()))
    ((isHomogeneous_X K (Sum.inr ())).mul (hF (Sum.inr ()))) (by omega) ≪≫
    (Scheme.Spec.mapIso (paperPDoubleChartRingEquiv F d hF).toCommRingCatIso.op).symm

/-- The double-chart comparison extends ordinary standard-chart
dehomogenization. -/
theorem paperPDoubleChartRingEquiv_awayMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (a : Away polyGrade lastX) :
    paperPDoubleChartRingEquiv F d hF
        (awayMap polyGrade (hF (Sum.inr ())) rfl a) =
      algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)
        (paperPStandardChartRingEquiv a) := by
  let : Algebra (Away polyGrade lastX) (Away polyGrade (lastX * F (Sum.inr ()))) :=
    (awayMap polyGrade (hF (Sum.inr ())) rfl).toAlgebra
  let : IsLocalization.Away
      (Away.isLocalizationElem (isHomogeneous_X K (Sum.inr ())) (hF (Sum.inr ())))
      (Away polyGrade (lastX * F (Sum.inr ()))) :=
    Away.isLocalization_mul (isHomogeneous_X K (Sum.inr ())) (hF (Sum.inr ())) rfl
      Nat.one_ne_zero
  unfold paperPDoubleChartRingEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ a

#print axioms paperPDoubleChartSchemeIso
#print axioms paperPDoubleChartRingEquiv_awayMap
#print axioms paperPDoubleChart_localizationElement
#print axioms paperPDoubleChartRingEquiv
end Pcf
