/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeGluing
public import Pcf.Bounding.AllCodimBlowupFiniteBaseChange
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Finiteness of the Rees blow-up lift

The global relative closed immersion removes the remaining premise from the
finiteness argument for the lift of a finite affine map to Rees blow-ups.
We also factor this finite morphism through Mathlib's relative normalization
and show that the source identifies with that relative normalization.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

set_option linter.style.haveILetI false

/-- A finite map of affine bases induces a finite morphism of the actual
Rees Proj blow-ups of a center and its extended center. -/
theorem reesProjMap_isFinite {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) :
    IsFinite (reesProjMap f I) := by
  letI : Algebra R S := f.toAlgebra
  apply reesProjMap_isFinite_of_relativeClosedImmersion f I hf
  exact reesProjRelativeBaseChange_isClosedImmersion (S := S) I

/- The normalization here is Mathlib's relative normalization of the target
in the finite source. The absolute normalization of each blow-up in its own
function field is a separate construction. -/

/-- The relative normalization of the target Rees blow-up in the finite
source Rees blow-up, formed from Mathlib's actual normalization scheme. -/
noncomputable def reesProjFiniteRelativeNormalization
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) : Scheme := by
  haveI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hf
  haveI : IsSeparated (reesProjMap f I) :=
    IsSeparated.of_isAffineHom (reesProjMap f I)
  exact (reesProjMap f I).normalization

/-- The canonical map from the source Rees blow-up to the relative
normalization of its finite map to the target blow-up. -/
noncomputable def reesProjFiniteToRelativeNormalization
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) :
    reesProj (I.map f) ⟶ reesProjFiniteRelativeNormalization f I hf := by
  haveI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hf
  haveI : IsSeparated (reesProjMap f I) :=
    IsSeparated.of_isAffineHom (reesProjMap f I)
  exact (reesProjMap f I).toNormalization

/-- The map from the relative normalization to the target Rees blow-up. -/
noncomputable def reesProjFiniteFromRelativeNormalization
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) :
    reesProjFiniteRelativeNormalization f I hf ⟶ reesProj I := by
  haveI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hf
  haveI : IsSeparated (reesProjMap f I) :=
    IsSeparated.of_isAffineHom (reesProjMap f I)
  exact (reesProjMap f I).fromNormalization

/-- Finiteness forces the source Rees blow-up to be the relative
normalization of the target in that source. -/
theorem reesProjFiniteToRelativeNormalization_isIso
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) :
    IsIso (reesProjFiniteToRelativeNormalization f I hf) := by
  haveI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hf
  haveI : IsSeparated (reesProjMap f I) :=
    IsSeparated.of_isAffineHom (reesProjMap f I)
  change IsIso (reesProjMap f I).toNormalization
  infer_instance

/-- The canonical relative-normalization factorization of the finite
Rees Proj map. -/
theorem reesProjFinite_relativeNormalization_factorization
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) :
    reesProjFiniteToRelativeNormalization f I hf ≫
      reesProjFiniteFromRelativeNormalization f I hf = reesProjMap f I := by
  haveI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hf
  haveI : IsSeparated (reesProjMap f I) :=
    IsSeparated.of_isAffineHom (reesProjMap f I)
  change (reesProjMap f I).toNormalization ≫
    (reesProjMap f I).fromNormalization = reesProjMap f I
  exact Scheme.Hom.toNormalization_fromNormalization _

/-- The map from this relative normalization to the target blow-up is
finite, as it is identified with the finite Rees Proj map. -/
theorem reesProjFiniteFromRelativeNormalization_isFinite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite) :
    IsFinite (reesProjFiniteFromRelativeNormalization f I hf) := by
  haveI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hf
  haveI : IsSeparated (reesProjMap f I) :=
    IsSeparated.of_isAffineHom (reesProjMap f I)
  change IsFinite (reesProjMap f I).fromNormalization
  haveI : IsIso (reesProjMap f I).toNormalization := inferInstance
  have heq : (reesProjMap f I).fromNormalization =
      inv (reesProjMap f I).toNormalization ≫ reesProjMap f I := by
    calc
      (reesProjMap f I).fromNormalization =
          (inv (reesProjMap f I).toNormalization ≫
            (reesProjMap f I).toNormalization) ≫
              (reesProjMap f I).fromNormalization := by simp
      _ = inv (reesProjMap f I).toNormalization ≫
          ((reesProjMap f I).toNormalization ≫
            (reesProjMap f I).fromNormalization) := by simp
      _ = inv (reesProjMap f I).toNormalization ≫ reesProjMap f I := by
        rw [(reesProjMap f I).toNormalization_fromNormalization]
  rw [heq]
  infer_instance

#print axioms reesProjMap_isFinite
#print axioms reesProjFiniteRelativeNormalization
#print axioms reesProjFiniteToRelativeNormalization_isIso
#print axioms reesProjFinite_relativeNormalization_factorization
#print axioms reesProjFiniteFromRelativeNormalization_isFinite

end Pcf.Bounding.AllCodimBlowup
