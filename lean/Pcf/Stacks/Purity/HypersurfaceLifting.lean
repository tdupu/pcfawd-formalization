/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Pcf.Stacks.Purity.OuterInduction

/-!
# The categorical assembly in Stacks Tag `0BLM`

Stacks Tag `0BLM` deduces extension of a finite etale cover of a punctured spectrum from two
separate inputs used in Tag `0BLS`:

* finite etale covers of the hypersurface lift to the ambient spectrum (Tag `09ZL`, after
  passing to the complete henselian-pair case); and
* restriction from the punctured spectrum to the punctured hypersurface is fully faithful
  (Tag `0BM6`, obtained there from the local-cohomology vanishing).

This file proves the exact categorical assembly from those two inputs.  In particular, the
result has the literal target `HypersurfaceFiniteEtaleLifting`; it does not replace that target
by a newly named surrogate.  The two remaining hypotheses are the preceding Stacks results,
not the conclusion of `0BLM` in disguise.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

section Hypersurface

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (x : R)

local notation "Rbar" => R ⧸ Ideal.span (Set.singleton x)

/-- The closed immersion `Spec(R/(x)) → Spec R` in Situation `0BLF`. -/
noncomputable def hypersurfaceMap : Spec (.of Rbar) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span (Set.singleton x))))

/-- Base change of finite etale covers from `Spec R` to the hypersurface `Spec(R/(x))`.

Essential surjectivity of this functor is the finite-etale lifting supplied by Stacks Tag
`09ZL` for a henselian pair. -/
noncomputable def restrictFiniteEtaleToHypersurface :
    FiniteEtaleCover (Spec (.of R)) ⥤ FiniteEtaleCover (Spec (.of Rbar)) :=
  FiniteEtaleCover.pullback _ (hypersurfaceMap R x)

omit [IsNoetherianRing R] in
/-- The defining square of the punctured hypersurface is commutative. -/
theorem puncturedHypersurfaceMap_comp_ι
    [IsLocalRing Rbar] :
    puncturedHypersurfaceMap R x ≫ (puncturedSpectrum R).ι =
      (puncturedSpectrum Rbar).ι ≫ hypersurfaceMap R x := by
  simp only [puncturedHypersurfaceMap, hypersurfaceMap]
  exact IsOpenImmersion.lift_fac _ _ _

/-- Iterated base change around the punctured-hypersurface square commutes.

This is the scheme-theoretic identification implicitly used in Tags `0BLS` and `0BLM`: first
restricting an ambient cover to the hypersurface and then puncturing agrees with first
puncturing and then restricting to the punctured hypersurface. -/
noncomputable def restrictFiniteEtaleToHypersurfaceCompPunctureIso
    [IsLocalRing Rbar] [IsNoetherianRing Rbar] :
    restrictFiniteEtaleToHypersurface R x ⋙
        restrictFiniteEtaleToPuncturedSpectrum Rbar ≅
      restrictFiniteEtaleToPuncturedSpectrum R ⋙
        restrictFiniteEtaleToPuncturedHypersurface R x := by
  let i₀ := (puncturedSpectrum Rbar).ι
  let j := hypersurfaceMap R x
  let i := (puncturedSpectrum R).ι
  let h := puncturedHypersurfaceMap R x
  letI : finiteEtaleMorphism.IsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.inf
  exact
    (MorphismProperty.Over.pullbackComp i₀ j).symm ≪≫
      MorphismProperty.Over.pullbackCongr
        (puncturedHypersurfaceMap_comp_ι R x).symm ≪≫
      MorphismProperty.Over.pullbackComp h i

omit [IsNoetherianRing R] in
/-- The faithful categorical core of Stacks Tags `0BLS` and `0BLM`.

The first hypothesis is precisely the essential-surjectivity part of the henselian-pair
equivalence of Tag `09ZL`.  The second is precisely the fully-faithful restriction theorem of
Tag `0BM6`.  Given an extension `Y₀` on the hypersurface, the first input lifts it to `Y` on
`Spec R`; the base-change square identifies both restrictions to the punctured hypersurface;
and the second input uniquely lifts that isomorphism to the punctured spectrum.

Thus the conclusion is the exact `HypersurfaceFiniteEtaleLifting` proposition used by the
outer induction, while the still-unformalized local-cohomology and henselian-pair results remain
visible as their own mathematically faithful prerequisites. -/
theorem hypersurfaceFiniteEtaleLifting_of_essSurj_of_fullyFaithful
    [IsLocalRing Rbar] [IsNoetherianRing Rbar]
    (hLift : (restrictFiniteEtaleToHypersurface R x).EssSurj)
    (hDetect :
      (restrictFiniteEtaleToPuncturedHypersurface R x).FullyFaithful) :
    HypersurfaceFiniteEtaleLifting R x := by
  intro V hV
  obtain ⟨Y₀, ⟨e₀⟩⟩ := hV
  rcases hLift with ⟨hLift⟩
  obtain ⟨Y, ⟨eY⟩⟩ := hLift Y₀
  let square := restrictFiniteEtaleToHypersurfaceCompPunctureIso R x
  let e :
      (restrictFiniteEtaleToPuncturedHypersurface R x).obj
          ((restrictFiniteEtaleToPuncturedSpectrum R).obj Y) ≅
        (restrictFiniteEtaleToPuncturedHypersurface R x).obj V :=
    (square.app Y).symm ≪≫
      (restrictFiniteEtaleToPuncturedSpectrum Rbar).mapIso eY ≪≫ e₀
  exact ⟨Y, ⟨hDetect.preimageIso e⟩⟩

#print axioms puncturedHypersurfaceMap_comp_ι
#print axioms restrictFiniteEtaleToHypersurfaceCompPunctureIso
#print axioms hypersurfaceFiniteEtaleLifting_of_essSurj_of_fullyFaithful

end Hypersurface

end Pcf.Stacks
