/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianEtale
public import Pcf.Bounding.SchemeBridge

/-!
# Scheme-level étaleness of the polynomial double-chart morphism

This identifies the Jacobian criterion with the actual stalk map of
`projChartSchemeMap`, at every scheme point. The remaining projective
obligation is to transport this criterion through coordinate-chart
isomorphisms for the global Proj morphism.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- The actual affine scheme chart morphism is étale on the entire chart
exactly when its regular Jacobian determinant is a unit. -/
theorem projChartSchemeMap_etale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Etale (projChartSchemeMap F) ↔ IsUnit (projChartRegularJacobian F).det := by
  rw [projChartSchemeMap, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact projChart_etale_iff F

/-- At every arbitrary point of the actual affine source chart, the scheme
stalk map is formally étale exactly where the homogeneous determinant is nonzero. -/
theorem projChartSchemeMap_stalk_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : PrimeSpectrum (ProjFormsChartRing F)) :
    ((projChartSchemeMap F).stalkMap p).hom.FormallyEtale ↔
      algebraMap _ (ProjFormsChartRing F)
        (projDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p.asIdeal := by
  let φ := (projChartPullback F).toRingHom
  let q := (p.comap φ).asIdeal
  let C := Localization.AtPrime p.asIdeal
  let R := Localization.AtPrime q
  let : SMul (MvPolynomial (Fin n) K) C :=
    (projChartLocalPullback F p.asIdeal C).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) C :=
    (projChartLocalPullback F p.asIdeal C).toAlgebra
  let : Algebra R C := (Localization.localRingHom q p.asIdeal φ rfl).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) K) R C := by
    apply IsScalarTower.of_algebraMap_eq' (R := MvPolynomial (Fin n) K) (S := R) (A := C)
    apply RingHom.ext
    intro a
    exact (Localization.localRingHom_to_map q p.asIdeal φ rfl a).symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) K) R :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  trans (Localization.localRingHom q p.asIdeal φ rfl).FormallyEtale
  · exact formallyEtale_respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom φ) p)
  · change Algebra.FormallyEtale R C ↔ _
    refine (Algebra.FormallyEtale.iff_restrictScalars
      (R := MvPolynomial (Fin n) K) (A := R) (B := C)).symm.trans ?_
    exact projChartLocal_formallyEtale_iff F d hF hd p.asIdeal C

#print axioms projChartSchemeMap_etale_iff
#print axioms projChartSchemeMap_stalk_formallyEtale_iff
end Pcf.PaperCharZero
