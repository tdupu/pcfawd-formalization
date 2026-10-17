/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.OuterInduction
public import Pcf.Stacks.Purity.RegularPairSections
public import Pcf.Stacks.Purity.Tag0BM9Equivalence
public import Pcf.Stacks.Purity.Tag0BMBAssembly
public import Mathlib.RingTheory.Regular.Flat

/-!
# The two clauses of Stacks Tag `0BMA`

This file proves the categorical implication from clause (1) of Tag `0BMA` to its corrected
affine clause (2), using the actual equivalence of Tag `0BM9`.

The section algebra of the finite etale extension need not first be shown normal. Its flatness
transports a length-two regular sequence from the base, and the same Hartogs calculation used in
Tag `0BM9` recovers it directly from the puncture.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing RingTheory.Sequence

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- The section algebra of a finite etale cover of an affine spectrum is finite etale over the
base ring.  The algebra structure is the canonical one induced by the structure morphism and
the `Gamma(Spec R) = R` isomorphism. -/
theorem finiteEtaleCover_sections_finite_etale
    (R : Type u) [CommRing R]
    (Y : FiniteEtaleCover (Spec (.of R))) :
    Module.Finite R
        ((algΓ (.of R)).obj ((FiniteEtaleCover.forget _).obj Y)).unop ∧
      Algebra.Etale R
        ((algΓ (.of R)).obj ((FiniteEtaleCover.forget _).obj Y)).unop := by
  letI : IsAffine ((Functor.fromPUnit (Spec (.of R))).obj Y.right) := by
    change IsAffine (Spec (.of R))
    infer_instance
  letI : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  letI : IsAffine ((Functor.id Scheme).obj Y.left) := by
    change IsAffine Y.left
    infer_instance
  have hfiniteTop : Y.hom.appTop.hom.Finite := Y.hom.finite_appTop
  have hetaleTop : Y.hom.appTop.hom.Etale :=
    HasRingHomProperty.appTop (@Etale) Y.hom Y.prop.2
  have hbaseFinite : (Scheme.ΓSpecIso (.of R)).inv.hom.Finite :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.finite
  have hbaseEtale : (Scheme.ΓSpecIso (.of R)).inv.hom.Etale :=
    RingHom.Etale.of_bijective
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  have hfinite :
      (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom).Finite :=
    hfiniteTop.comp hbaseFinite
  have hetale :
      (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom).Etale :=
    RingHom.Etale.stableUnderComposition _ _ hbaseEtale hetaleTop
  constructor
  · change (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom).Finite
    exact hfinite
  · exact hetale.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The relative `Gamma`-`Spec` unit is an isomorphism on a finite etale cover of an affine
base, since the source of the cover is affine. -/
theorem finiteEtaleCover_algGamma_unit_isIso
    (R : Type u) [CommRing R]
    (Y : FiniteEtaleCover (Spec (.of R))) :
    IsIso ((algΓAlgSpecAdjunction (.of R)).unit.app
      ((FiniteEtaleCover.forget _).obj Y)) := by
  letI : IsAffine ((Functor.fromPUnit (Spec (.of R))).obj Y.right) := by
    change IsAffine (Spec (.of R))
    infer_instance
  letI : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let A : (CommAlgCat R)ᵒᵖ := Opposite.op <|
    (commAlgCatEquivUnder (.of R)).inverse.obj <|
      .mk (Spec.fullyFaithful.preimage
        (Y.left.isoSpec.inv ≫ Y.hom)).unop
  let e : (FiniteEtaleCover.forget _).obj Y ≅
      (algSpec (.of R)).obj A :=
    Over.isoMk Y.left.isoSpec (by
      simp only [algSpec_obj_hom]
      dsimp only [A, commAlgCatEquivUnder]
      change Y.left.isoSpec.hom ≫
          Spec.map (Spec.fullyFaithful.preimage
            (Y.left.isoSpec.inv ≫ Y.hom)).unop = Y.hom
      rw [Spec.map_preimage_unop]
      simp)
  letI : (algSpec (.of R)).Full := algSpec.fullyFaithful.full
  letI : (algSpec (.of R)).Faithful := algSpec.fullyFaithful.faithful
  exact (algΓAlgSpecAdjunction (.of R)).isIso_unit_app_of_iso e

/-- A form of the punctured `Gamma`-`Spec` counit criterion which exposes exactly the
ring-theoretic Hartogs input. -/
theorem puncturedSectionsSpecAdjunction_counit_isIso_of_bijective
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (A : (CommAlgCat R)ᵒᵖ)
    (hcomp : Function.Bijective
      (((Scheme.ΓSpecIso (.of A.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj A).hom
          (puncturedSpectrum R).ι).appTop).hom)) :
    IsIso ((puncturedSectionsSpecAdjunction R).counit.app A) := by
  let p := ((algSpec (.of R)).obj A).hom
  let i := (puncturedSpectrum R).ι
  let j := pullback.fst p i
  haveI : IsIso
      ((Scheme.ΓSpecIso (.of A.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj A).hom
          (puncturedSpectrum R).ι).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hcomp
  haveI : IsIso
      (pullback.fst ((algSpec (.of R)).obj A).hom
        (puncturedSpectrum R).ι).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of A.unop)).inv _
  haveI : IsIso j.appTop := by
    change IsIso
      (pullback.fst ((algSpec (.of R)).obj A).hom
        (puncturedSpectrum R).ι).appTop
    infer_instance
  let c := (Over.mapPullbackAdj i).counit.app ((algSpec (.of R)).obj A)
  haveI : IsIso c.left.appTop := by
    change IsIso j.appTop
    infer_instance
  haveI : IsIso ((Scheme.Γ.rightOp).map c.left) := by
    change IsIso c.left.appTop.op
    infer_instance
  haveI : IsIso ((Over.post Scheme.Γ.rightOp).map c) := by
    let m := (Over.post Scheme.Γ.rightOp).map c
    haveI : IsIso m.left := by
      change IsIso ((Scheme.Γ.rightOp).map c.left)
      infer_instance
    let e := Over.isoMk (asIso m.left) m.w
    have he : e.hom = m := by
      ext
      rfl
    change IsIso m
    rw [← he]
    infer_instance
  haveI : IsIso ((algΓ (.of R)).map c) := by
    unfold algΓ
    dsimp only [Functor.comp_map]
    infer_instance
  simp only [puncturedSectionsSpecAdjunction, Adjunction.comp_counit_app]
  infer_instance

/-- A base regular pair on a finite étale algebra: flatness transports a length-two regular
sequence `x, y` of the base, in either order. -/
theorem finiteEtaleAlgebra_exists_regularPair
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ IsSMulRegular C.unop x ∧
      IsSMulRegular C.unop y ∧ IsSMulRegular (QuotSMulTop x C.unop) y := by
  obtain ⟨x, y, hxm, hym, hreg⟩ :=
    exists_regularSequence_two_of_isIntegrallyClosed R hdim
  have hweak : IsWeaklyRegular C.unop [x, y] := by
    rw [← isWeaklyRegular_map_algebraMap_iff (S := C.unop) (M := C.unop) [x, y]]
    exact hreg.toIsWeaklyRegular.of_flat
  obtain ⟨hx, htail⟩ := (isWeaklyRegular_cons_iff C.unop x [y]).mp hweak
  have hregYX : IsRegular R [y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x y []).symm
  have hweakYX : IsWeaklyRegular C.unop [y, x] := by
    rw [← isWeaklyRegular_map_algebraMap_iff (S := C.unop) (M := C.unop) [y, x]]
    exact hregYX.toIsWeaklyRegular.of_flat
  exact ⟨x, y, hxm, hym, hx, ((isWeaklyRegular_cons_iff C.unop y [x]).mp hweakYX).1,
    ((isWeaklyRegular_cons_iff (QuotSMulTop x C.unop) y []).mp htail).1⟩

/-- The restriction of the spectrum of an étale algebra to the punctured spectrum is étale. -/
theorem etale_puncturedRestriction_of_etale
    (R : CommRingCat.{u}) [IsLocalRing R] (C : (CommAlgCat R)ᵒᵖ) [Algebra.Etale R C.unop] :
    Etale (((Over.pullback (puncturedSpectrum R).ι).obj ((algSpec (.of R)).obj C)).hom) := by
  let p : Spec (.of C.unop) ⟶ Spec (.of R) := ((algSpec (.of R)).obj C).hom
  have : Etale p := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R C.unop)))
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  change Etale (pullback.snd p (puncturedSpectrum R).ι)
  infer_instance

/-- A finite etale algebra over the base is recovered from regular functions on the open image
of its restriction to the punctured spectrum. Flatness, rather than normality of the algebra,
transports the depth-two regular sequence needed in the Hartogs calculation. -/
theorem finiteEtaleAlgebra_openSections_bijective
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of C.unop)).inv ≫
        (Spec (.of C.unop)).presheaf.map
          (homOfLE (show (pullback.fst ((algSpec (.of R)).obj C).hom
            (puncturedSpectrum R).ι).opensRange ≤ ⊤ from le_top)).op).hom) := by
  obtain ⟨x, y, hxm, hym, hx, hyB, hy⟩ := finiteEtaleAlgebra_exists_regularPair R hdim C
  exact openSections_bijective_of_regularPair_of_puncturedEtale R (le_trans (by norm_num) hdim)
    C x y hxm hym hx hyB hy (etale_puncturedRestriction_of_etale R C)

/-- Hartogs recovery for a finite etale algebra, expressed on its actual pullback scheme over
the puncture. -/
theorem finiteEtaleAlgebra_pullbackSections_bijective
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of C.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj C).hom
          (puncturedSpectrum R).ι).appTop).hom) := by
  obtain ⟨x, y, hxm, hym, hx, hyB, hy⟩ := finiteEtaleAlgebra_exists_regularPair R hdim C
  exact pullbackSections_bijective_of_regularPair_of_puncturedEtale R
    (le_trans (by norm_num) hdim) C x y hxm hym hx hyB hy (etale_puncturedRestriction_of_etale R C)

/-- The punctured `Gamma`-`Spec` counit is an isomorphism on finite etale algebras. This is the
normality-free Hartogs input used to compare an extension supplied by clause (1) of Tag `0BMA`
with the algebra in clause (2). -/
theorem finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
    IsIso ((puncturedSectionsSpecAdjunction R).counit.app C) :=
  puncturedSectionsSpecAdjunction_counit_isIso_of_bijective R C
    (finiteEtaleAlgebra_pullbackSections_bijective R hdim C)

/-- Clause (1) of Stacks Tag `0BMA` implies its corrected affine clause (2).

Given a finite etale extension of the punctured cover, the proof compares its finite etale
section algebra with the original finite normal algebra. The comparison uses Hartogs recovery
twice: the flat regular-sequence argument above for the finite etale algebra, and the Tag `0BM9`
recovery theorem for the original normal algebra. No normality assertion for finite etale
algebras is needed. -/
theorem finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (hpurity : PuncturedSpectrumPurity R) :
    FiniteNormalPuncturedEtalePurity R := by
  intro B hB
  let B' : FiniteNormalPuncturedEtaleAlgebra R := ⟨B, hB⟩
  let V := (finiteNormalAlgebraToPuncturedCover R).obj B'
  rcases hpurity with ⟨hpurity⟩
  obtain ⟨Y, ⟨eY⟩⟩ := hpurity V
  let Y0 : Over (Spec (.of R)) := (FiniteEtaleCover.forget _).obj Y
  let C : (CommAlgCat R)ᵒᵖ := (algΓ (.of R)).obj Y0
  have hC := finiteEtaleCover_sections_finite_etale R Y
  letI : Module.Finite R C.unop := hC.1
  letI : Algebra.Etale R C.unop := hC.2
  let unitY := (algΓAlgSpecAdjunction (.of R)).unit.app Y0
  letI : IsIso unitY := finiteEtaleCover_algGamma_unit_isIso R Y
  let eU := (Over.pullback (puncturedSpectrum R).ι).mapIso (asIso unitY)
  let eR := (Over.map (puncturedSpectrum R).ι).mapIso eU
  let eUnitΓ := (algΓ (.of R)).mapIso eR
  letI : IsIso ((puncturedSectionsSpecAdjunction (.of R)).counit.app C) :=
    finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
      (.of R) hdim C
  let eΓ := (puncturedFiniteEtaleGlobalSections R).mapIso eY
  let eB := (finiteNormalPuncturedEtaleAlgebraProperty R).ι.mapIso
    ((puncturedFiniteEtaleCoverEquivalence_counitIso (.of R) hdim).app B')
  let eCB : C ≅ B :=
    (eUnitΓ ≪≫ asIso ((puncturedSectionsSpecAdjunction (.of R)).counit.app C)).symm ≪≫
      eΓ ≪≫ eB
  let eA : C.unop ≃ₐ[R] B.unop := CommAlgCat.algEquivOfIso eCB.symm.unop
  exact Algebra.Etale.of_equiv eA

#print axioms finiteEtaleCover_sections_finite_etale
#print axioms finiteEtaleCover_algGamma_unit_isIso
#print axioms puncturedSectionsSpecAdjunction_counit_isIso_of_bijective
#print axioms finiteEtaleAlgebra_openSections_bijective
#print axioms finiteEtaleAlgebra_pullbackSections_bijective
#print axioms finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
#print axioms finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity

end Pcf.Stacks
