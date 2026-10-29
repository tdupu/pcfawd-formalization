/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLine
public import Pcf.Unnormalized.PaperPRegularCodimOneLoci

/-!
# `PC(f) = PC₀(f) = PC₁(f)` for the pinched plane

For `paper-p.tex`, Example `ex:pinched` ("As `X` is regular in codimension one, the
three branch loci of `f` agree ... so `PC(f) = PC₀(f) = PC₁(f)`"):

* `stalk_isRegularLocalRing`: every codimension-one stalk of `X` is regular
  (from `PinchedLine.regularInCodimOne`).
* `pinched_postcritical_coincide`: the normalized (weighted) postcritical points of `f`
  and the generic points of `PC₀(f)`, `PC₁(f)` coincide, and PCF ↔ `0`-PCF ↔ `1`-PCF,
  by `Pcf.postcritical_coincide_of_regularInCodimOne`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedPostcritical

open AlgebraicGeometry CategoryTheory Pcf.Examples.PaperP.PinchedNormalization

set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k

/-- The structure morphism `X → Spec k`. -/
noncomputable def structureMap : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

instance structureMap_locallyOfFiniteType : LocallyOfFiniteType (structureMap k) := by
  unfold structureMap
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **`X` is regular in codimension one**, stalk form. -/
theorem stalk_isRegularLocalRing (P : Pcf.SchemeDivisorPoint (Spec (.of R))) :
    IsRegularLocalRing ((Spec (.of R)).presheaf.stalk P.1) := by
  have hh : P.1.asIdeal.height ≤ 1 := by
    rw [idealHeight_eq_coheight (.of R) P.1, P.2]
  haveI := PinchedLine.regularInCodimOne k P.1.asIdeal hh
  exact IsRegularLocalRing.of_ringEquiv (R' := (Spec (.of R)).presheaf.stalk P.1)
    (StructureSheaf.stalkIso R P.1).toRingEquiv

/-- **`PC(f) = PC₀(f) = PC₁(f)`** (as generic points) and PCF ↔ `0`-PCF ↔ `1`-PCF for the
actual pinched map `f`. -/
theorem pinched_postcritical_coincide :
    letI : IsFinite (Palomar.normalizationMap (Spec (.of R))) :=
      Pcf.schemeGlobalNormalizationMap_isFinite _ k (structureMap k)
    (Pcf.weightedPostcriticalPointSet (PinchedAmbient.fScheme k) =
        Subtype.val '' Pcf.schemeUnnormalizedPostcriticalSet false k (structureMap k)
          (PinchedAmbient.fScheme k) ∧
      Subtype.val '' Pcf.schemeUnnormalizedPostcriticalSet false k (structureMap k)
          (PinchedAmbient.fScheme k) =
        Subtype.val '' Pcf.schemeUnnormalizedPostcriticalSet true k (structureMap k)
          (PinchedAmbient.fScheme k)) ∧
    (Pcf.IsWeightedNormalizedPCFDownstairs k (structureMap k) (PinchedAmbient.fScheme k) ↔
      Pcf.IsSchemeUnnormalizedPCF false k (structureMap k) (PinchedAmbient.fScheme k)) ∧
    (Pcf.IsSchemeUnnormalizedPCF false k (structureMap k) (PinchedAmbient.fScheme k) ↔
      Pcf.IsSchemeUnnormalizedPCF true k (structureMap k) (PinchedAmbient.fScheme k)) :=
  Pcf.postcritical_coincide_of_regularInCodimOne k (structureMap k) (PinchedAmbient.fScheme k)
    (stalk_isRegularLocalRing k)

#print axioms stalk_isRegularLocalRing
#print axioms pinched_postcritical_coincide

end Pcf.Examples.PaperP.PinchedPostcritical
