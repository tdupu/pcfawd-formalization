/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The punctured-spectrum functors in Stacks Tag `0BM9`

Let `R` be a Noetherian local ring, let `X = Spec R`, and let
`U = X \ {m}` be the complement of its closed point.  This file constructs the actual
categories and functors at the start of Stacks Tag `0BM9`:

* `FiniteEtaleCover X`, the category of finite étale schemes over a scheme `X`;
* restriction of finite étale covers from `X` to `U` by scheme-theoretic pullback;
* the global-sections functor from finite étale covers of `U` to `R`-algebras;
* the affine `Spec Γ` extension over `X` and its canonical recovery morphism over `U`.

The missing assertion in Tag `0BM9` is that the recovery morphism is an isomorphism when `R` is
normal of dimension at least two, and that its global-sections algebra is finite and normal over
`R`.  At the pinned Mathlib revision this cannot yet be proved faithfully: Mathlib has neither
the Stacks notion of a possibly disconnected normal ring nor the depth/reflexive-module Hartogs
theorems used in the proof.  No equivalence is asserted below.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Pcf.Stacks

/-- The open complement of the closed point in the spectrum of a local ring. -/
def puncturedSpectrum (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (.of R)).Opens :=
  show TopologicalSpace.Opens (PrimeSpectrum R) from
    { carrier := {IsLocalRing.closedPoint R}ᶜ
      is_open' := (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl }

@[simp]
theorem mem_puncturedSpectrum_iff
    (R : Type u) [CommRing R] [IsLocalRing R] (x : PrimeSpectrum R) :
    x ∈ puncturedSpectrum R ↔ x ≠ IsLocalRing.closedPoint R := by
  change x ∉ ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) ↔ _
  simp

@[simp]
theorem closedPoint_notMem_puncturedSpectrum
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalRing.closedPoint R ∉ puncturedSpectrum R := by
  simp

/-- The punctured spectrum as an actual open subscheme. -/
abbrev puncturedSpectrumScheme (R : Type u) [CommRing R] [IsLocalRing R] : Scheme :=
  (puncturedSpectrum R).toScheme

/-- The scheme-morphism property "finite and étale". -/
abbrev finiteEtaleMorphism : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

/-- The category of finite étale schemes over `X`.  This is the scheme-theoretic category
denoted `FÉt_X` in Stacks Tag `0BM9`. -/
abbrev FiniteEtaleCover (X : Scheme.{u}) : Type (u + 1) :=
  finiteEtaleMorphism.Over ⊤ X

namespace FiniteEtaleCover

variable (X : Scheme.{u})

/-- Forget a finite étale cover to its underlying scheme over `X`. -/
abbrev forget : FiniteEtaleCover X ⥤ Over X :=
  MorphismProperty.Over.forget finiteEtaleMorphism ⊤ X

instance (Y : FiniteEtaleCover X) : IsFinite Y.hom := Y.prop.1

instance (Y : FiniteEtaleCover X) : Etale Y.hom := Y.prop.2

/-- Restriction of finite étale covers along an arbitrary scheme morphism, implemented by
scheme-theoretic pullback. -/
noncomputable def pullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    FiniteEtaleCover X ⥤ FiniteEtaleCover Y := by
  letI : finiteEtaleMorphism.IsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.inf
  exact MorphismProperty.Over.pullback finiteEtaleMorphism ⊤ f

end FiniteEtaleCover

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Restriction of finite étale covers from `Spec R` to its punctured spectrum. -/
noncomputable abbrev restrictFiniteEtaleToPuncturedSpectrum :
    FiniteEtaleCover (Spec (.of R)) ⥤ FiniteEtaleCover (puncturedSpectrumScheme R) :=
  FiniteEtaleCover.pullback _ (puncturedSpectrum R).ι

/-- Regard a finite étale cover of the punctured spectrum as a scheme over `Spec R`. -/
abbrev puncturedFiniteEtaleOverSpec :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤ Over (Spec (.of R)) :=
  FiniteEtaleCover.forget _ ⋙ Over.map (puncturedSpectrum R).ι

/-- Global sections of a finite étale cover of the punctured spectrum, with their canonical
`R`-algebra structure.  The target is opposite because global sections are contravariant. -/
abbrev puncturedFiniteEtaleGlobalSections :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤ (CommAlgCat R)ᵒᵖ :=
  puncturedFiniteEtaleOverSpec R ⋙ algΓ (.of R)

/-- The affine scheme over `Spec R` obtained by applying `Spec` to the global sections of a
finite étale cover of the punctured spectrum. -/
abbrev puncturedFiniteEtaleExtension :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤ Over (Spec (.of R)) :=
  puncturedFiniteEtaleGlobalSections R ⋙ algSpec (.of R)

/-- The canonical map from a punctured finite étale cover, viewed over `Spec R`, to the affine
`Spec Γ` extension.  It is the unit of the relative `Γ ⊣ Spec` adjunction. -/
def puncturedFiniteEtaleToExtension :
    puncturedFiniteEtaleOverSpec R ⟶ puncturedFiniteEtaleExtension R :=
  (puncturedFiniteEtaleOverSpec R).whiskerLeft (algΓAlgSpecAdjunction (.of R)).unit

/-- Restrict the affine `Spec Γ` extension back to the punctured spectrum. -/
noncomputable abbrev restrictPuncturedFiniteEtaleExtension :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤ Over (puncturedSpectrumScheme R) :=
  puncturedFiniteEtaleExtension R ⋙ Over.pullback (puncturedSpectrum R).ι

/-- The canonical recovery morphism from a finite étale cover of the punctured spectrum to the
restriction of its affine `Spec Γ` extension.

Showing that every component of this natural transformation is an isomorphism is the first
geometric extension assertion still missing from the pinned library on the route to Tag `0BM9`.
-/
noncomputable def puncturedFiniteEtaleRecovery :
    FiniteEtaleCover.forget (puncturedSpectrumScheme R) ⟶
      restrictPuncturedFiniteEtaleExtension R where
  app V :=
    (Over.mapPullbackAdj (puncturedSpectrum R).ι).homEquiv _ _
      ((puncturedFiniteEtaleToExtension R).app V)
  naturality V W f := by
    change _ = _ ≫ (Over.pullback (puncturedSpectrum R).ι).map
      ((puncturedFiniteEtaleExtension R).map f)
    rw [← (Over.mapPullbackAdj (puncturedSpectrum R).ι).homEquiv_naturality_left,
      ← (Over.mapPullbackAdj (puncturedSpectrum R).ι).homEquiv_naturality_right]
    exact congrArg _ ((puncturedFiniteEtaleToExtension R).naturality f)

/-- Package the `Spec Γ` extension as a finite étale cover of `Spec R`, provided the missing
algebraic extension theorem supplies finite and étale morphisms objectwise.

This is a purely categorical reduction: the hypothesis is one of the substantive conclusions
of the depth/normality argument in Stacks Tag `0BM9`, not an implementation of that argument. -/
noncomputable def puncturedFiniteEtaleExtensionCover
    (hExtension : ∀ V, finiteEtaleMorphism ((puncturedFiniteEtaleExtension R).obj V).hom) :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤ FiniteEtaleCover (Spec (.of R)) where
  obj V := MorphismProperty.Over.mk ⊤ ((puncturedFiniteEtaleExtension R).obj V).hom
    (hExtension V)
  map f := MorphismProperty.Over.Hom.mk ((puncturedFiniteEtaleExtension R).map f) trivial
  map_id V := by
    apply (FiniteEtaleCover.forget _).map_injective
    exact (puncturedFiniteEtaleExtension R).map_id V
  map_comp f g := by
    apply (FiniteEtaleCover.forget _).map_injective
    exact (puncturedFiniteEtaleExtension R).map_comp f g

/-- Under the explicit Tag `0BM9` extension and recovery hypotheses, each punctured finite
étale cover is isomorphic to the restriction of its packaged `Spec Γ` extension. -/
noncomputable def puncturedFiniteEtaleRecoveryIso
    (hExtension : ∀ V, finiteEtaleMorphism ((puncturedFiniteEtaleExtension R).obj V).hom)
    (hRecovery : ∀ V, IsIso ((puncturedFiniteEtaleRecovery R).app V))
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    V ≅ (restrictFiniteEtaleToPuncturedSpectrum R).obj
      ((puncturedFiniteEtaleExtensionCover R hExtension).obj V) := by
  exact MorphismProperty.Comma.isoFromComma
    (@asIso _ _ _ _ ((puncturedFiniteEtaleRecovery R).app V) (hRecovery V))

omit [IsNoetherianRing R] in
/-- A useful special consequence of the missing Tag `0BM9` Hartogs/normality input: if every
`Spec Γ` extension in a chosen family is finite étale and every recovery map is an isomorphism,
then restriction to the punctured spectrum is essentially surjective.

Tag `0BM9` does not say that every punctured finite étale cover extends finite étale. Rather,
it identifies punctured finite étale covers with finite normal `R`-algebras étale away from the
closed point, and characterizes the covers whose corresponding algebra is finite étale. The
strong objectwise `hExtension` hypothesis below is therefore an explicit additional premise,
not the general conclusion of that tag. Full faithfulness of this restriction functor also
requires the corresponding extension theorem for morphisms and is not claimed here. -/
theorem restrictFiniteEtaleToPuncturedSpectrum_essSurj
    (hExtension : ∀ V, finiteEtaleMorphism ((puncturedFiniteEtaleExtension R).obj V).hom)
    (hRecovery : ∀ V, IsIso ((puncturedFiniteEtaleRecovery R).app V)) :
    (restrictFiniteEtaleToPuncturedSpectrum R).EssSurj := by
  constructor
  intro V
  refine ⟨(puncturedFiniteEtaleExtensionCover R hExtension).obj V, ?_⟩
  exact ⟨(puncturedFiniteEtaleRecoveryIso R hExtension hRecovery V).symm⟩

/-- The precise morphism-extension property for finite étale covers across the closed point:
restriction induces a bijection on every hom-set.

This isolates the morphism part of the stronger special case in which every finite étale cover of
the punctured spectrum extends as a finite étale cover of `Spec R`.  It is not itself part of the
conclusion of Tag `0BM9`, whose target is a category of finite normal algebras. -/
def PuncturedFiniteEtaleMorphismsExtend : Prop :=
  ∀ X Y : FiniteEtaleCover (Spec (.of R)),
    Function.Bijective (fun f : X ⟶ Y ↦
      (restrictFiniteEtaleToPuncturedSpectrum R).map f)

omit [IsNoetherianRing R] in
/-- The morphism-extension property is exactly sufficient to make restriction fully faithful. -/
noncomputable def restrictFiniteEtaleToPuncturedSpectrumFullyFaithful
    (hMorphisms : PuncturedFiniteEtaleMorphismsExtend R) :
    (restrictFiniteEtaleToPuncturedSpectrum R).FullyFaithful where
  preimage {X Y} f := Classical.choose ((hMorphisms X Y).2 f)
  map_preimage {X Y} f :=
    Classical.choose_spec ((hMorphisms X Y).2 f)
  preimage_map {X Y} f :=
    (hMorphisms X Y).1 (Classical.choose_spec ((hMorphisms X Y).2
      ((restrictFiniteEtaleToPuncturedSpectrum R).map f)))

omit [IsNoetherianRing R] in
/-- Under the strictly stronger hypotheses that every punctured finite étale cover extends as a
finite étale cover and morphisms extend uniquely, restriction is an equivalence.

This is a conditional special consequence and is deliberately not labelled as Tag `0BM9`. -/
noncomputable def restrictFiniteEtaleToPuncturedSpectrumEquivalence
    (hExtension : ∀ V, finiteEtaleMorphism ((puncturedFiniteEtaleExtension R).obj V).hom)
    (hRecovery : ∀ V, IsIso ((puncturedFiniteEtaleRecovery R).app V))
    (hMorphisms : PuncturedFiniteEtaleMorphismsExtend R) :
    FiniteEtaleCover (Spec (.of R)) ≌ FiniteEtaleCover (puncturedSpectrumScheme R) := by
  let F := restrictFiniteEtaleToPuncturedSpectrum R
  let hFullyFaithful : F.FullyFaithful :=
    restrictFiniteEtaleToPuncturedSpectrumFullyFaithful R hMorphisms
  let hEssSurj : F.EssSurj :=
    restrictFiniteEtaleToPuncturedSpectrum_essSurj R hExtension hRecovery
  letI : F.Full := hFullyFaithful.full
  letI : F.Faithful := hFullyFaithful.faithful
  letI : F.EssSurj := hEssSurj
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end LocalRing

end Pcf.Stacks
