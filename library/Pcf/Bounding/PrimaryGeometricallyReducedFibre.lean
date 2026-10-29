/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryReducedFiberLocal
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Geometrically reduced fibres and divisorial multiplicity

On an affine chart of the altered morphism in `paper-p.tex`, Lemma
`lem:primary-fibres`, a geometrically reduced fibre is reduced. At a
height-one source prime lying over a height-one base prime, this forces
the pullback of the base uniformizer to have valuation one. The argument
does not require the altered morphism to be finite.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- A geometrically reduced affine morphism has ramification index one
at a divisorial component of any height-one fibre. Here injectivity of
the coefficient map is the affine form of dominance. -/
theorem ramificationIdx_eq_one_of_geometricallyReduced_affineFiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    (hinj : Function.Injective (algebraMap R S))
    (p : Pcf.HeightOnePrime R) (Q : Pcf.HeightOnePrime S)
    [Q.1.asIdeal.LiesOver p.1.asIdeal]
    (hgeo : GeometricallyReduced
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    Q.1.asIdeal.ramificationIdx R = 1 := by
  letI : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  letI : GeometricallyReduced g := hgeo
  have hred : AlgebraicGeometry.IsReduced (g.fiber p.1) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  let e := Spec.fiberToSpecResidueFieldIso R S p.1
  have hspec : AlgebraicGeometry.IsReduced
      (Spec (.of (p.1.asIdeal.Fiber S))) :=
    @isReduced_of_isOpenImmersion _ _ e.inv.left inferInstance hred
  have hring : _root_.IsReduced (p.1.asIdeal.Fiber S) :=
    (affine_isReduced_iff _).mp hspec
  let P : p.1.asIdeal.primesOver S :=
    ⟨Q.1.asIdeal, ⟨inferInstance, inferInstance⟩⟩
  let q : PrimeSpectrum (p.1.asIdeal.Fiber S) :=
    PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal P
  have hq : q.asIdeal.comap Algebra.TensorProduct.includeRight = Q.1.asIdeal := by
    change ((PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm q).1 = P.1
    exact congrArg Subtype.val
      ((PrimeSpectrum.primesOverOrderIsoFiber R S p.1.asIdeal).symm_apply_apply P)
  exact ramificationIdx_eq_one_of_reduced_affineFiber_dominant
    p Q q.asIdeal hq hring

#print axioms ramificationIdx_eq_one_of_geometricallyReduced_affineFiber

end
end Pcf.Bounding.PrimaryFibres
