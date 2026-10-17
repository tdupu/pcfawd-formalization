/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Pcf.Stacks.Purity.Tag0BM9
public import Pcf.Stacks.Purity.FiniteNormalAlgebraRecovery

/-!
# The categorical equivalence in Stacks Tag `0BM9`

This file packages the relative `Gamma`-`Spec` adjunction on the punctured spectrum and restricts
it to finite etale covers and finite torsion-free normal algebras.  The Hartogs recovery theorem
identifies the counit on the algebra side; normalization supplies essential surjectivity on the
cover side.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- The relative global-sections/affine-spectrum adjunction, after restriction of schemes from
`Spec R` to its punctured spectrum. -/
noncomputable def puncturedSectionsSpecAdjunction :
    (Over.map (puncturedSpectrum R).ι ⋙ algΓ (.of R)) ⊣
      (algSpec (.of R) ⋙ Over.pullback (puncturedSpectrum R).ι) :=
  (Over.mapPullbackAdj (puncturedSpectrum R).ι).comp
    (algΓAlgSpecAdjunction (.of R))

/-- The defining property of the algebra category in Tag `0BM9` is invariant under isomorphism.
In particular, finiteness, torsion-freeness, Stacks-normality, and punctured etaleness all
transport across an algebra isomorphism. -/
instance finiteNormalPuncturedEtaleAlgebraProperty_isClosedUnderIsomorphisms :
    (finiteNormalPuncturedEtaleAlgebraProperty R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let eA : Y.unop ≃ₐ[R] X.unop := CommAlgCat.algEquivOfIso e.unop
    letI : Module.Finite R X.unop := hX.1
    have hfin : Module.Finite R Y.unop := Module.Finite.equiv eA.symm.toLinearEquiv
    letI : Module.IsTorsionFree R X.unop := hX.2.1
    have htf : Module.IsTorsionFree R Y.unop :=
      Function.Injective.moduleIsTorsionFree eA eA.injective
        (fun r y ↦ by simp)
    have hnormal : IsStacksNormalRing Y.unop :=
      IsStacksNormalRing.of_ringEquiv eA.toRingEquiv hX.2.2.1
    let ep := (Over.pullback (puncturedSpectrum R).ι).mapIso
      ((algSpec (.of R)).mapIso e)
    have hetale : Etale (((Over.pullback (puncturedSpectrum R).ι).obj
        ((algSpec (.of R)).obj Y)).hom) := by
      letI : MorphismProperty.RespectsIso (@Etale) := by
        rw [HasRingHomProperty.eq_affineLocally (@Etale)]
        exact affineLocally_respectsIso _ RingHom.Etale.respectsIso
      letI : IsIso ep.inv.left := by
        change IsIso ((Over.forget _).map ep.inv)
        infer_instance
      rw [← ep.inv.w]
      apply (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).mpr
      exact hX.2.2.2
    exact ⟨hfin, htf, hnormal, hetale⟩

/-- Hartogs recovery expressed on the actual pullback scheme over the puncture.  The previously
proved open-image form is transported across the global-sections isomorphism of an open
immersion. -/
theorem finiteNormalAlgebra_pullbackSections_bijective
    (hdim : 2 ≤ ringKrullDim R)
    (A : FiniteNormalPuncturedEtaleAlgebra R) :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of A.obj.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj A.obj).hom
          (puncturedSpectrum R).ι).appTop).hom) := by
  let B : CommRingCat := .of A.obj.unop
  let p : Spec B ⟶ Spec (.of R) := ((algSpec (.of R)).obj A.obj).hom
  let i := (puncturedSpectrum R).ι
  let P := pullback p i
  let j : P ⟶ Spec B := pullback.fst p i
  let W : (Spec B).Opens := j.opensRange
  change Function.Bijective (((Scheme.ΓSpecIso B).inv ≫ j.appTop).hom)
  let e := IsOpenImmersion.ΓIsoTop j
  have hW := finiteNormalAlgebra_openSections_bijective R hdim A
  letI : Algebra B Γ(Spec B, W) :=
    (((Scheme.ΓSpecIso B).inv ≫
      (Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op).hom).toAlgebra
  have he (b : B) : e.inv (algebraMap B Γ(Spec B, W) b) =
      j.appTop ((Scheme.ΓSpecIso B).inv b) := by
    have etop : (⊤ : P.Opens) ≤ j ⁻¹ᵁ W := by
      change (⊤ : P.Opens) ≤ j ⁻¹ᵁ j.opensRange
      rw [← j.image_top_eq_opensRange, j.preimage_image_eq]
    have hcomp : (Spec B).presheaf.map
          (eqToHom j.image_top_eq_opensRange).op ≫
          (j.appIso ⊤).hom =
        j.appLE W ⊤ etop := by
      rw [j.appIso_hom']
      exact j.map_appLE' etop j.image_top_eq_opensRange
    simp only [e, IsOpenImmersion.ΓIsoTop, Iso.trans_inv,
      Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
      Iso.symm_inv]
    change ((Spec B).presheaf.map
          (eqToHom j.image_top_eq_opensRange).op ≫
        (j.appIso ⊤).hom).hom
        (((Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.map
            (homOfLE (show W ≤ ⊤ from le_top)).op).hom b) = _
    rw [← CommRingCat.comp_apply, hcomp]
    change ((Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op ≫
      j.appLE W ⊤ etop).hom ((Scheme.ΓSpecIso B).inv b) = _
    rw [j.map_appLE]
    have happ : j.appLE ⊤ ⊤ (by simp) = j.appTop := by
      simpa only [Scheme.Hom.preimage_top] using
        (j.appLE_eq_app (U := (⊤ : (Spec B).Opens)))
    change (j.appLE ⊤ ⊤ _).hom _ = j.appTop.hom _
    rw [happ]
  have heBij : Function.Bijective e.inv.hom :=
    (ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance
  have hcomp := heBij.comp hW
  change Function.Bijective
    (e.inv.hom ∘ (((Scheme.ΓSpecIso B).inv ≫
      (Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op).hom)) at hcomp
  have hefun : ((Scheme.ΓSpecIso B).inv ≫ j.appTop).hom =
      e.inv.hom ∘ (((Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.map
          (homOfLE (show W ≤ ⊤ from le_top)).op).hom) := by
    funext b
    exact (he b).symm
  rw [hefun]
  exact hcomp

/-- The counit of the punctured `Gamma`-`Spec` adjunction is an isomorphism on every finite
torsion-free normal algebra in the target of Tag `0BM9`. -/
theorem puncturedSectionsSpecAdjunction_counit_isIso
    (hdim : 2 ≤ ringKrullDim R)
    (A : FiniteNormalPuncturedEtaleAlgebra R) :
    IsIso ((puncturedSectionsSpecAdjunction R).counit.app A.obj) := by
  let p := ((algSpec (.of R)).obj A.obj).hom
  let i := (puncturedSpectrum R).ι
  let j := pullback.fst p i
  have hcomp := finiteNormalAlgebra_pullbackSections_bijective R hdim A
  haveI : IsIso
      ((Scheme.ΓSpecIso (.of A.obj.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj A.obj).hom
          (puncturedSpectrum R).ι).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hcomp
  haveI : IsIso
      (pullback.fst ((algSpec (.of R)).obj A.obj).hom
        (puncturedSpectrum R).ι).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of A.obj.unop)).inv _
  haveI : IsIso j.appTop := by
    change IsIso
      (pullback.fst ((algSpec (.of R)).obj A.obj).hom
        (puncturedSpectrum R).ι).appTop
    infer_instance
  let c := (Over.mapPullbackAdj i).counit.app ((algSpec (.of R)).obj A.obj)
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

/-- Global sections of a finite etale cover of the puncture lie in the exact finite,
torsion-free, Stacks-normal target category of Tag `0BM9`. -/
theorem puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty
    (hdim : 2 ≤ ringKrullDim R) :
    ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V) := by
  intro V
  have hdim1 : 1 ≤ ringKrullDim R := le_trans (by norm_num) hdim
  obtain ⟨A, ⟨e⟩⟩ :=
    puncturedCover_exists_finiteNormalPuncturedEtaleAlgebra R hdim1 V
  letI : IsIso ((puncturedSectionsSpecAdjunction R).counit.app A.obj) :=
    puncturedSectionsSpecAdjunction_counit_isIso R hdim A
  let eΓ := (puncturedFiniteEtaleGlobalSections R).mapIso e
  let eA : A.obj ≅ (puncturedFiniteEtaleGlobalSections R).obj V :=
    (asIso ((puncturedSectionsSpecAdjunction R).counit.app A.obj)).symm ≪≫ eΓ
  exact (finiteNormalPuncturedEtaleAlgebraProperty R).prop_of_iso eA A.property

/-- The relative `Gamma`-`Spec` adjunction restricted to finite etale covers of the puncture and
finite torsion-free normal algebras which are etale there. -/
noncomputable def puncturedFiniteEtaleSectionsAdjunction (hdim : 2 ≤ ringKrullDim R) :
    puncturedGlobalSectionsToFiniteNormalAlgebra R
        (puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty R hdim) ⊣
      finiteNormalAlgebraToPuncturedCover R :=
  (puncturedSectionsSpecAdjunction R).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (FiniteEtaleCover.forget _))
    (finiteNormalPuncturedEtaleAlgebraProperty R).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- The counit of the restricted Tag `0BM9` adjunction is an isomorphism.  This is the categorical
form of recovering a finite normal algebra from the global functions on its punctured
restriction. -/
theorem puncturedFiniteEtaleSectionsAdjunction_counit_isIso (hdim : 2 ≤ ringKrullDim R)
    (A : FiniteNormalPuncturedEtaleAlgebra R) :
    IsIso ((puncturedFiniteEtaleSectionsAdjunction R hdim).counit.app A) := by
  rw [← ObjectProperty.isIso_hom_iff]
  have hmap := (puncturedSectionsSpecAdjunction R).map_restrictFullyFaithful_counit_app
    (L := puncturedGlobalSectionsToFiniteNormalAlgebra R
      (puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty R hdim))
    (R := finiteNormalAlgebraToPuncturedCover R)
    (Functor.FullyFaithful.ofFullyFaithful (FiniteEtaleCover.forget _))
    (finiteNormalPuncturedEtaleAlgebraProperty R).fullyFaithfulι
    (Iso.refl _) (Iso.refl _) A
  dsimp only [puncturedFiniteEtaleSectionsAdjunction] at hmap
  change IsIso ((finiteNormalPuncturedEtaleAlgebraProperty R).ι.map
    ((puncturedFiniteEtaleSectionsAdjunction R hdim).counit.app A))
  dsimp only [puncturedFiniteEtaleSectionsAdjunction]
  rw [hmap]
  dsimp
  haveI : IsIso ((puncturedSectionsSpecAdjunction R).counit.app A.obj) :=
    puncturedSectionsSpecAdjunction_counit_isIso R hdim A
  simpa only [Category.id_comp]

/-- Restriction from the finite-normal algebra category to finite etale covers of the puncture is
fully faithful. -/
noncomputable def finiteNormalAlgebraToPuncturedCoverFullyFaithful
    (hdim : 2 ≤ ringKrullDim R) :
    (finiteNormalAlgebraToPuncturedCover R).FullyFaithful := by
  let adj := puncturedFiniteEtaleSectionsAdjunction R hdim
  haveI : ∀ A, IsIso (adj.counit.app A) := fun A ↦
    puncturedFiniteEtaleSectionsAdjunction_counit_isIso R hdim A
  letI : IsIso adj.counit := NatIso.isIso_of_isIso_app adj.counit
  exact adj.fullyFaithfulROfIsIsoCounit

/-- Every finite etale cover of the puncture is in the essential image of restriction from a
finite torsion-free normal algebra. -/
theorem finiteNormalAlgebraToPuncturedCover_essSurj
    (hdim : 2 ≤ ringKrullDim R) :
    (finiteNormalAlgebraToPuncturedCover R).EssSurj := by
  constructor
  intro V
  obtain ⟨A, e⟩ := puncturedCover_exists_finiteNormalPuncturedEtaleAlgebra R
    (le_trans (by norm_num) hdim) V
  exact ⟨A, e⟩

/-- The exact equivalence of categories in Stacks Tag `0BM9`: finite etale covers of the
punctured spectrum are equivalent, by global sections, to finite torsion-free Stacks-normal
`R`-algebras whose spectra are etale over the puncture. -/
noncomputable def puncturedFiniteEtaleCoverEquivalence (hdim : 2 ≤ ringKrullDim R) :
    FiniteEtaleCover (puncturedSpectrumScheme R) ≌
      FiniteNormalPuncturedEtaleAlgebra R := by
  let F := puncturedGlobalSectionsToFiniteNormalAlgebra R
    (puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty R hdim)
  let G := finiteNormalAlgebraToPuncturedCover R
  let adj : F ⊣ G := puncturedFiniteEtaleSectionsAdjunction R hdim
  let hFullyFaithful : G.FullyFaithful :=
    finiteNormalAlgebraToPuncturedCoverFullyFaithful R hdim
  letI : G.Full := hFullyFaithful.full
  letI : G.Faithful := hFullyFaithful.faithful
  letI : G.EssSurj := finiteNormalAlgebraToPuncturedCover_essSurj R hdim
  letI : G.IsEquivalence := {}
  exact adj.toEquivalence

/-- Canonical recovery of a punctured finite etale cover from the spectrum of its global
sections. -/
noncomputable def puncturedFiniteEtaleCoverEquivalence_unitIso
    (hdim : 2 ≤ ringKrullDim R) :
    𝟭 (FiniteEtaleCover (puncturedSpectrumScheme R)) ≅
      puncturedGlobalSectionsToFiniteNormalAlgebra R
          (puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty R hdim) ⋙
        finiteNormalAlgebraToPuncturedCover R :=
  (puncturedFiniteEtaleCoverEquivalence R hdim).unitIso

/-- Canonical recovery of a finite normal algebra from the global sections of its punctured
restriction. -/
noncomputable def puncturedFiniteEtaleCoverEquivalence_counitIso
    (hdim : 2 ≤ ringKrullDim R) :
    finiteNormalAlgebraToPuncturedCover R ⋙
        puncturedGlobalSectionsToFiniteNormalAlgebra R
          (puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty R hdim) ≅
      𝟭 (FiniteNormalPuncturedEtaleAlgebra R) :=
  (puncturedFiniteEtaleCoverEquivalence R hdim).counitIso

/-- Global sections on punctured finite etale covers are fully faithful. -/
noncomputable def puncturedGlobalSectionsFullyFaithfulOfTwoLeRingKrullDim
    (hdim : 2 ≤ ringKrullDim R) :
    (puncturedGlobalSectionsToFiniteNormalAlgebra R
      (puncturedGlobalSections_finiteNormalPuncturedEtaleAlgebraProperty R
        hdim)).FullyFaithful :=
  (puncturedFiniteEtaleCoverEquivalence R hdim).fullyFaithfulFunctor

end Pcf.Stacks
