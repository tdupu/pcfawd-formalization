/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalBaseChange

/-!
# Coherent transport of Rees maps to equal extended ideals

Ideal sheaf restriction gives an equality `I.map f = J`. The maps below use
that equality while retaining a coefficientwise formula, so identity and
composition hold without any unproved coherence of ideal transports.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The actual graded Rees map with a specified equal target ideal. -/
noncomputable def gradedReesMapTo (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map f = J) : reesGrade I →+*ᵍ reesGrade J := by
  subst J
  exact gradedReesMap f I

@[simp] theorem gradedReesMapTo_val (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map f = J) (P : reesAlgebra I) :
    (gradedReesMapTo f I J h P).1 = (Polynomial.mapRingHom f) P.1 := by
  subst J
  rfl

/-- Equality transports preserve the irrelevant-ideal condition for the actual Proj map. -/
theorem gradedReesMapTo_irrelevant_le (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map f = J) :
    HomogeneousIdeal.irrelevant (reesGrade J) ≤
      (HomogeneousIdeal.irrelevant (reesGrade I)).map (gradedReesMapTo f I J h) := by
  subst J
  exact gradedReesMap_irrelevant_le f I

/-- Composition is independent of the proofs witnessing the target ideal equalities. -/
theorem gradedReesMapTo_comp (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (hIJ : I.map f = J) (hJK : J.map g = K) (hIK : I.map (g.comp f) = K) :
    (gradedReesMapTo g J K hJK).comp (gradedReesMapTo f I J hIJ) =
      gradedReesMapTo (g.comp f) I K hIK := by
  ext P : 1
  apply Subtype.ext
  simp [Polynomial.map_map]

/-- Identity is independent of the ideal-equality proof. -/
theorem gradedReesMapTo_id (I : Ideal R) (h : I.map (RingHom.id R) = I) :
    gradedReesMapTo (RingHom.id R) I I h = GradedRingHom.id (reesGrade I) := by
  ext P : 1
  apply Subtype.ext
  simp

/-- The actual scheme map for a coefficient map and its specified extended ideal. -/
noncomputable def reesProjMapTo (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map f = J) : reesProj J ⟶ reesProj I :=
  Proj.map (gradedReesMapTo f I J h) (gradedReesMapTo_irrelevant_le f I J h)

theorem reesProjMapTo_comp (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T)
    (hIJ : I.map f = J) (hJK : J.map g = K) (hIK : I.map (g.comp f) = K) :
    reesProjMapTo g J K hJK ≫ reesProjMapTo f I J hIJ =
      reesProjMapTo (g.comp f) I K hIK := by
  unfold reesProjMapTo
  rw [← Proj.map_comp]
  congr 1
  exact gradedReesMapTo_comp f g I J K hIJ hJK hIK

theorem reesProjMapTo_id (I : Ideal R) (h : I.map (RingHom.id R) = I) :
    reesProjMapTo (RingHom.id R) I I h = 𝟙 (reesProj I) := by
  unfold reesProjMapTo
  simp only [gradedReesMapTo_id]
  exact Proj.map_id

/-- The actual structure maps commute after transport of the centre equality. -/
@[reassoc]
theorem reesProjMapTo_toSpec (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : I.map f = J) :
    reesProjMapTo f I J h ≫ reesProjToSpec I =
      reesProjToSpec J ≫ Spec.map (CommRingCat.ofHom f) := by
  subst J
  exact reesProjMap_toSpec f I

#print axioms gradedReesMapTo_comp
#print axioms gradedReesMapTo_id
#print axioms reesProjMapTo_comp
#print axioms reesProjMapTo_id
#print axioms reesProjMapTo_toSpec
end Pcf.Bounding.AllCodimBlowup
