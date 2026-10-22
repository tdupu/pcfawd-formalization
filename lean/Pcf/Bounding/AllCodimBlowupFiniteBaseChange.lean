/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeGlobalCharts
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finiteness of a Rees blow-up map from relative closed immersion

The source blow-up maps to the finite base change of the target
blow-up as a closed subscheme. This file isolates the formal geometric
deduction: the map of blow-ups is finite because a closed immersion
and the base change of a finite map are finite.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

set_option linter.style.haveILetI false

/-- Once the relative Rees Proj map is identified globally as a closed
immersion, a finite affine base map induces a finite map of blow-ups.
The closed-immersion premise is discharged by gluing the checked chart
closed immersions along their target cover. -/
theorem reesProjMap_isFinite_of_relativeClosedImmersion
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : f.Finite)
    (hclosed : IsClosedImmersion (reesProjRelativeBaseChange f I)) :
    IsFinite (reesProjMap f I) := by
  haveI : IsFinite (Spec.map (CommRingCat.ofHom f)) :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom f)).mpr hf
  haveI : IsClosedImmersion (reesProjRelativeBaseChange f I) := hclosed
  rw [← reesProjRelativeBaseChange_snd]
  infer_instance

#print axioms reesProjMap_isFinite_of_relativeClosedImmersion

end Pcf.Bounding.AllCodimBlowup
