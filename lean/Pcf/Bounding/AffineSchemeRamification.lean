/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.InvariantDivisorGeometry

/-!
# Ramification on affine charts and actual scheme stalks

The chart and stalk definitions of divisorial ramification agree. The proof
uses the tower law twice: localizing the source or the target has ramification
index one. Flatness of the stalk extension follows from dominance and the DVR
property of the normal target at a codimension-one point.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- Localization of both rings preserves ramification when the resulting
local extension is flat. This applies in particular to dominant extensions
of codimension-one stalks with normal target. -/
theorem ramificationIdx_eq_of_localization_square
    {R S Rp Sq : Type*} [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sq]
    [Algebra R S] [Algebra R Rp] [Algebra S Sq] [Algebra R Sq] [Algebra Rp Sq]
    [IsScalarTower R S Sq] [IsScalarTower R Rp Sq]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [IsLocalization.AtPrime Rp p] [IsLocalization.AtPrime Sq q]
    [IsLocalRing Rp] [IsLocalRing Sq] [IsLocalHom (algebraMap Rp Sq)]
    [Module.Flat Rp Sq] :
    (IsLocalRing.maximalIdeal Sq).ramificationIdx Rp = q.ramificationIdx R := by
  letI : Module.Flat S Sq := IsLocalization.flat Sq q.primeCompl
  letI : Algebra.EssFiniteType S Sq := Algebra.EssFiniteType.of_isLocalization Sq q.primeCompl
  letI : Algebra.FormallyEtale S Sq := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  letI : Algebra.EssFiniteType R Rp := Algebra.EssFiniteType.of_isLocalization Rp p.primeCompl
  letI : Algebra.FormallyEtale R Rp := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have hs := Ideal.ramificationIdx_tower (R := R) q (IsLocalRing.maximalIdeal Sq)
  have ht := Ideal.ramificationIdx_tower (R := R)
    (IsLocalRing.maximalIdeal Rp) (IsLocalRing.maximalIdeal Sq)
  rw [Ideal.ramificationIdx_eq_one (IsLocalRing.maximalIdeal Sq) S, mul_one] at hs
  rw [Ideal.ramificationIdx_eq_one (IsLocalRing.maximalIdeal Rp) R, one_mul] at ht
  exact ht.symm.trans hs

set_option backward.isDefEq.respectTransparency false in
/-- The actual stalk ramification index equals the height-one ramification
index on any finite affine preimage chart. All algebra structures are the
ones induced by the actual morphism and section-to-stalk maps. -/
theorem schemeDivisorRamificationIdx_eq_heightOneRamificationIdx
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (U : Y.affineOpens)
    (Q : HeightOnePrime Γ(X, finitePreimageAffine f U)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    schemeDivisorRamificationIdx f (schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) Q) =
      heightOneRamificationIdx (R := Γ(Y, U)) Q := by
  let V := finitePreimageAffine f U
  let x := schemeDivisorPointOfAffinePrime V Q
  have hx : x.1 ∈ (V : X.Opens) := by
    exact (V.2.isoSpec.inv Q.1).2
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let Rp := Y.presheaf.stalk (f x.1)
  let Sq := X.presheaf.stalk x.1
  letI : Algebra R S := (f.app U).hom.toAlgebra
  letI : Algebra R Rp := Y.presheaf.algebra_section_stalk ⟨f x.1, hx⟩
  letI : Algebra S Sq := X.presheaf.algebra_section_stalk ⟨x.1, hx⟩
  letI : Algebra Rp Sq := (f.stalkMap x.1).hom.toAlgebra
  letI : Algebra R Sq :=
    ((X.presheaf.germ V x.1 hx).hom.comp (f.app U).hom).toAlgebra
  letI : IsScalarTower R S Sq := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Rp Sq := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.germ_stalkMap_apply U x.1 hx a).symm)
  let p := (U.2.primeIdealOf ⟨f x.1, hx⟩).asIdeal
  letI : IsLocalization.AtPrime Rp p := U.2.isLocalization_stalk ⟨f x.1, hx⟩
  letI : IsLocalization.AtPrime Sq Q.1.asIdeal := V.2.isLocalization_stalk' Q.1 hx
  letI : IsLocalHom (algebraMap Rp Sq) :=
    show IsLocalHom (f.stalkMap x.1).hom from inferInstance
  letI : IsDiscreteValuationRing Rp :=
    (x.mapFiniteDominantNormal f).stalk_isDiscreteValuationRing
  letI : FaithfulSMul Rp Sq := (faithfulSMul_iff_algebraMap_injective Rp Sq).mpr
    (stalkMap_injective_of_dominant_integral f x.1)
  letI : Module.Flat Rp Sq := inferInstance
  exact ramificationIdx_eq_of_localization_square p Q.1.asIdeal

#print axioms ramificationIdx_eq_of_localization_square
#print axioms schemeDivisorRamificationIdx_eq_heightOneRamificationIdx
#check @ramificationIdx_eq_of_localization_square
#check @schemeDivisorRamificationIdx_eq_heightOneRamificationIdx

end

end Pcf
