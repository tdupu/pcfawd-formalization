/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.NormalRing
public import Pcf.Stacks.Purity.PuncturedSpectrum

/-!
# The finite-normal-algebra category in Stacks Tag `0BM9`

For a Noetherian local ring `R`, this file models the actual target of the functor in Tag `0BM9`:
finite Stacks-normal `R`-algebras whose spectra are étale over the punctured spectrum.  We use the
opposite category of algebras, so that contravariant global sections define a covariant functor
from finite étale covers.

The obvious quasi-inverse from the Stacks proof is constructed unconditionally on this target:
send `B` to `Spec B ×_(Spec R) U`.  The final equivalence is packaged only under explicit recovery
isomorphisms.  Establishing those isomorphisms is the depth-two/reflexive Hartogs content still
missing at the pinned Mathlib revision.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Pcf.Stacks

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The object property defining the algebra category in Tag `0BM9`.

An object is an `R`-algebra `B`, regarded oppositely, which is finite and torsion-free as an
`R`-module, normal in the literal Stacks sense, and whose affine spectrum becomes étale after
pullback to the punctured spectrum.

Divergence from Stacks (see `FiniteNormalPuncturedEtalePurity` and Tag `0BMA`, clause (2)): the
literal clause (2) is false for `B = A × κ(𝔪)` (finite, normal, étale over the punctured spectrum,
not flat), so `B` torsion-free over `A` is part of the property.

Torsion-freeness is essential here: without it one could add
a normal factor supported only at the closed point, which restriction to the punctured spectrum
would forget.  Equivalently, this condition forces every component relevant to this category to
dominate the base. -/
def finiteNormalPuncturedEtaleAlgebraProperty :
    ObjectProperty ((CommAlgCat R)ᵒᵖ) :=
  fun B ↦ Module.Finite R B.unop ∧
    Module.IsTorsionFree R B.unop ∧
      IsStacksNormalRing B.unop ∧
        Etale (((Over.pullback (puncturedSpectrum R).ι).obj
          ((algSpec (.of R)).obj B)).hom)

/-- The opposite category of finite normal `R`-algebras whose spectra are étale over the
punctured spectrum.  This is the target category of Tag `0BM9`, with arrows oriented so that
global sections are covariant. -/
abbrev FiniteNormalPuncturedEtaleAlgebra : Type (u + 1) :=
  (finiteNormalPuncturedEtaleAlgebraProperty R).FullSubcategory

namespace FiniteNormalPuncturedEtaleAlgebra

variable {R}

instance (B : FiniteNormalPuncturedEtaleAlgebra R) : Module.Finite R B.obj.unop :=
  B.property.1

omit [IsNoetherianRing R] in
/-- Objects in the Tag `0BM9` target have no vertical `R`-torsion. -/
instance (B : FiniteNormalPuncturedEtaleAlgebra R) :
    Module.IsTorsionFree R B.obj.unop :=
  B.property.2.1

omit [IsNoetherianRing R] in
theorem isStacksNormalRing (B : FiniteNormalPuncturedEtaleAlgebra R) :
    IsStacksNormalRing B.obj.unop :=
  B.property.2.2.1

instance (B : FiniteNormalPuncturedEtaleAlgebra R) :
    Etale (((Over.pullback (puncturedSpectrum R).ι).obj
      ((algSpec (.of R)).obj B.obj)).hom) :=
  B.property.2.2.2

set_option backward.isDefEq.respectTransparency.types false in
omit [IsNoetherianRing R] in
/-- The affine spectrum of an object in the target category is finite over `Spec R`. -/
theorem isFinite_algSpec (B : FiniteNormalPuncturedEtaleAlgebra R) :
    IsFinite ((algSpec (.of R)).obj B.obj).hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R B.obj.unop)))
  rw [IsFinite.SpecMap_iff]
  change (algebraMap R B.obj.unop).Finite
  exact RingHom.finite_algebraMap.mpr B.property.1

end FiniteNormalPuncturedEtaleAlgebra

/-- The underlying affine scheme over the punctured spectrum attached to a target algebra. -/
noncomputable abbrev finiteNormalAlgebraOverPuncturedSpectrum :
    FiniteNormalPuncturedEtaleAlgebra R ⥤ Over (puncturedSpectrumScheme R) :=
  (finiteNormalPuncturedEtaleAlgebraProperty R).ι ⋙
    algSpec (.of R) ⋙ Over.pullback (puncturedSpectrum R).ι

/-- The obvious quasi-inverse on objects in Tag `0BM9`: `B` is sent to
`Spec B ×_(Spec R) U`, which is finite étale over `U`. -/
noncomputable def finiteNormalAlgebraToPuncturedCover :
    FiniteNormalPuncturedEtaleAlgebra R ⥤ FiniteEtaleCover (puncturedSpectrumScheme R) where
  obj B := MorphismProperty.Over.mk ⊤
    ((finiteNormalAlgebraOverPuncturedSpectrum R).obj B).hom (by
      constructor
      · let _ : IsFinite ((algSpec (.of R)).obj B.obj).hom :=
          FiniteNormalPuncturedEtaleAlgebra.isFinite_algSpec B
        change IsFinite (Limits.pullback.snd
          ((algSpec (.of R)).obj B.obj).hom (puncturedSpectrum R).ι)
        infer_instance
      · exact B.property.2.2.2)
  map f := MorphismProperty.Over.Hom.mk
    ((finiteNormalAlgebraOverPuncturedSpectrum R).map f) trivial
  map_id B := by
    apply (FiniteEtaleCover.forget _).map_injective
    exact (finiteNormalAlgebraOverPuncturedSpectrum R).map_id B
  map_comp f g := by
    apply (FiniteEtaleCover.forget _).map_injective
    exact (finiteNormalAlgebraOverPuncturedSpectrum R).map_comp f g

/-- Once the algebraic part of Tag `0BM9` proves that global sections are finite and normal, the
global-sections functor lifts to the exact target category of the tag. -/
noncomputable def puncturedGlobalSectionsToFiniteNormalAlgebra
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V)) :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤
      FiniteNormalPuncturedEtaleAlgebra R :=
  (finiteNormalPuncturedEtaleAlgebraProperty R).lift
    (puncturedFiniteEtaleGlobalSections R) hTarget

/-- The canonical recovery transformation, lifted from schemes over `U` to finite étale covers,
after global sections have been shown to land in the finite-normal target category. -/
noncomputable def puncturedCoverRecovery
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V)) :
    𝟭 (FiniteEtaleCover (puncturedSpectrumScheme R)) ⟶
      puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget ⋙
        finiteNormalAlgebraToPuncturedCover R where
  app V := MorphismProperty.Over.Hom.mk
    ((puncturedFiniteEtaleRecovery R).app V) trivial
  naturality V W f := by
    apply (FiniteEtaleCover.forget _).map_injective
    exact (puncturedFiniteEtaleRecovery R).naturality f

/-- If the canonical recovery maps are isomorphisms, they form the unit isomorphism for the
candidate Tag `0BM9` equivalence. -/
noncomputable def puncturedCoverRecoveryIso
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V))
    (hRecovery : ∀ V, IsIso ((puncturedFiniteEtaleRecovery R).app V)) :
    𝟭 (FiniteEtaleCover (puncturedSpectrumScheme R)) ≅
      puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget ⋙
        finiteNormalAlgebraToPuncturedCover R :=
  NatIso.ofComponents
    (fun V ↦ MorphismProperty.Comma.isoFromComma
      (@asIso _ _ _ _ ((puncturedFiniteEtaleRecovery R).app V) (hRecovery V)))
    (fun f ↦ by
      apply (FiniteEtaleCover.forget _).map_injective
      exact (puncturedFiniteEtaleRecovery R).naturality f)

/-- The exact morphism-extension property in Tag `0BM9`: the global-sections functor, after
landing in the finite-normal target, induces a bijection on every hom-set. -/
def PuncturedGlobalSectionsMorphismsExtend
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V)) : Prop :=
  ∀ V W : FiniteEtaleCover (puncturedSpectrumScheme R),
    Function.Bijective (fun f : V ⟶ W ↦
      (puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget).map f)

/-- Unique extension of morphisms makes the Tag `0BM9` global-sections functor fully faithful. -/
noncomputable def puncturedGlobalSectionsFullyFaithful
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V))
    (hMorphisms : PuncturedGlobalSectionsMorphismsExtend R hTarget) :
    (puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget).FullyFaithful where
  preimage {V W} f := Classical.choose ((hMorphisms V W).2 f)
  map_preimage {V W} f := Classical.choose_spec ((hMorphisms V W).2 f)
  preimage_map {V W} f := (hMorphisms V W).1
    (Classical.choose_spec ((hMorphisms V W).2
      ((puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget).map f)))

omit [IsNoetherianRing R] in
/-- Algebra recovery makes the Tag `0BM9` global-sections functor essentially surjective. -/
theorem puncturedGlobalSections_essSurj
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V))
    (hAlgebraRecovery :
      finiteNormalAlgebraToPuncturedCover R ⋙
          puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget ≅
        𝟭 (FiniteNormalPuncturedEtaleAlgebra R)) :
    (puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget).EssSurj := by
  constructor
  intro B
  exact ⟨(finiteNormalAlgebraToPuncturedCover R).obj B,
    ⟨hAlgebraRecovery.app B⟩⟩

/-- The exact categorical conclusion of Tag `0BM9`, conditional on the three remaining algebraic
inputs: global sections land in the finite-normal target and algebra maps extend uniquely, while
restriction followed by global sections recovers every target algebra. -/
noncomputable def puncturedFiniteEtaleCoverEquivalenceOfMorphismExtension
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V))
    (hMorphisms : PuncturedGlobalSectionsMorphismsExtend R hTarget)
    (hAlgebraRecovery :
      finiteNormalAlgebraToPuncturedCover R ⋙
          puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget ≅
        𝟭 (FiniteNormalPuncturedEtaleAlgebra R)) :
    FiniteEtaleCover (puncturedSpectrumScheme R) ≌
      FiniteNormalPuncturedEtaleAlgebra R := by
  let F := puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget
  let hFullyFaithful : F.FullyFaithful :=
    puncturedGlobalSectionsFullyFaithful R hTarget hMorphisms
  let hEssSurj : F.EssSurj :=
    puncturedGlobalSections_essSurj R hTarget hAlgebraRecovery
  letI : F.Full := hFullyFaithful.full
  letI : F.Faithful := hFullyFaithful.faithful
  letI : F.EssSurj := hEssSurj
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- The exact categorical assembly of Tag `0BM9` once its two Hartogs recovery assertions have
been supplied: recovery of a cover from `Spec Γ`, and recovery of a finite normal algebra from the
global sections of its restriction to `U`.

The hypotheses are intentionally exposed.  This theorem packages, but does not prove, the missing
depth-two/reflexive algebra. -/
noncomputable def puncturedFiniteEtaleCoverEquivalenceOfRecovery
    (hTarget : ∀ V, finiteNormalPuncturedEtaleAlgebraProperty R
      ((puncturedFiniteEtaleGlobalSections R).obj V))
    (hRecovery : ∀ V, IsIso ((puncturedFiniteEtaleRecovery R).app V))
    (hAlgebraRecovery :
      finiteNormalAlgebraToPuncturedCover R ⋙
          puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget ≅
        𝟭 (FiniteNormalPuncturedEtaleAlgebra R)) :
    FiniteEtaleCover (puncturedSpectrumScheme R) ≌
      FiniteNormalPuncturedEtaleAlgebra R :=
  CategoryTheory.Equivalence.mk
    (puncturedGlobalSectionsToFiniteNormalAlgebra R hTarget)
    (finiteNormalAlgebraToPuncturedCover R)
    (puncturedCoverRecoveryIso R hTarget hRecovery)
    hAlgebraRecovery

end LocalRing

end Pcf.Stacks
