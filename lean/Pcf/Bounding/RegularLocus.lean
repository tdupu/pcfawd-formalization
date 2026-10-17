/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeExtraction
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Pcf.Palomar.Statement

/-!
# Generic regularity and normal codimension-one stalks

The reduced closed subscheme of an irreducible closed set is integral. In
particular, every reduced point closure has a regular generic stalk, so its
pointwise singular locus is proper. Normal locally Noetherian integral schemes
have regular stalks at every codimension-one point.

These statements concern `IsRegularLocalRing` on actual scheme stalks. They do
not assert openness of the regular locus: that additional theorem for schemes
locally of finite type over a field is not supplied by the pinned Mathlib.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

/-- An irreducible closed subset with its reduced induced scheme structure is integral. -/
theorem isIntegral_vanishingIdeal_subscheme {X : Scheme.{u}} (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Palomar.isReduced_vanishingIdeal_subscheme Z
  let : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Subtype.irreducibleSpace hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Every reduced point closure is integral, including the closure of a divisor point. -/
instance pointClosureSubscheme_isIntegral {X : Scheme.{u}} (x : X) :
    IsIntegral (pointClosureIdealSheaf x).subscheme :=
  isIntegral_vanishingIdeal_subscheme
    ⟨closure ({x} : Set X), isClosed_closure⟩ (isIrreducible_singleton.closure)

/-- The generic point of a reduced point closure maps to the point defining that closure. -/
@[simp]
theorem pointClosureSubschemeι_genericPoint {X : Scheme.{u}} (x : X) :
    (pointClosureIdealSheaf x).subschemeι
      (genericPoint (pointClosureIdealSheaf x).subscheme) = x := by
  have h := (genericPoint_spec (pointClosureIdealSheaf x).subscheme).image
    (pointClosureIdealSheaf x).subschemeι.continuous
  rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
  change IsGenericPoint _ (closure (closure ({x} : Set X))) at h
  rw [closure_closure] at h
  exact h.eq (by rfl)

/-- The generic stalk of an integral scheme is a field and hence regular. -/
theorem isRegularLocalRing_stalk_genericPoint {X : Scheme.{u}} [IsIntegral X] :
    IsRegularLocalRing (X.presheaf.stalk (genericPoint X)) := by
  change IsRegularLocalRing X.functionField
  infer_instance

/-- The singular locus of an integral scheme omits its generic point. -/
theorem genericPoint_notMem_stalkSingularLocus {X : Scheme.{u}} [IsIntegral X] :
    genericPoint X ∉ stalkSingularLocus X :=
  fun h ↦ h isRegularLocalRing_stalk_genericPoint

/-- Properness of the pointwise singular locus requires neither finite type nor Noetherianity. -/
theorem stalkSingularLocus_ne_univ {X : Scheme.{u}} [IsIntegral X] :
    stalkSingularLocus X ≠ Set.univ := by
  intro h
  exact genericPoint_notMem_stalkSingularLocus
    (h.symm ▸ Set.mem_univ (genericPoint X))

/-- The pointwise singular locus of the reduced closure of any point is proper. -/
theorem stalkSingularLocus_pointClosureSubscheme_ne_univ {X : Scheme.{u}} (x : X) :
    stalkSingularLocus (pointClosureIdealSheaf x).subscheme ≠ Set.univ :=
  stalkSingularLocus_ne_univ

/-- The actual stalk at a divisor point of a normal locally Noetherian integral
scheme is regular, by the height-one DVR theorem on an affine neighborhood. -/
theorem SchemeDivisorPoint.isRegularLocalRing_stalk
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (x : SchemeDivisorPoint X) :
    IsRegularLocalRing (X.presheaf.stalk x.1) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.1) isOpen_univ
  let V : X.affineOpens := ⟨U, hU⟩
  let y : U := ⟨x.1, hxU⟩
  let : Nonempty U := ⟨y⟩
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian V
  let : IsIntegrallyClosed Γ(X, U) := IsNormalScheme.component_integrallyClosed V
  let p := (hU.primeIdealOf y).asIdeal
  have hp : p.height = 1 := by
    simpa only [pointClosureIdealSheaf_ideal x.1 V hxU] using
      pointClosureIdealSheaf_ideal_height x V hxU
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hp
  let : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := hU.isLocalization_stalk y
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime p) (X.presheaf.stalk x.1)).toRingEquiv

/-- A normal locally Noetherian integral scheme has no singular divisor points. -/
theorem SchemeDivisorPoint.notMem_stalkSingularLocus
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (x : SchemeDivisorPoint X) : x.1 ∉ stalkSingularLocus X :=
  fun h ↦ h x.isRegularLocalRing_stalk

/-- The singular codimension-one locus of a normal locally Noetherian integral
scheme is empty, without an assumption that the full singular locus is closed. -/
theorem schemeDivisorPoint_stalkSingularLocus_eq_empty
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] :
    {x : SchemeDivisorPoint X | x.1 ∈ stalkSingularLocus X} = ∅ := by
  exact Set.eq_empty_iff_forall_notMem.mpr fun x ↦ x.notMem_stalkSingularLocus

/-- In particular the singular codimension-one locus is finite. -/
theorem finite_schemeDivisorPoint_stalkSingularLocus
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] :
    {x : SchemeDivisorPoint X | x.1 ∈ stalkSingularLocus X}.Finite := by
  rw [schemeDivisorPoint_stalkSingularLocus_eq_empty]
  exact Set.finite_empty

/-- On a divisor of a normal scheme, the generic point avoids the ambient singular locus. -/
theorem genericPoint_notMem_ambient_stalkSingularLocus
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (x : SchemeDivisorPoint X) :
    genericPoint (pointClosureIdealSheaf x.1).subscheme ∉
      (pointClosureIdealSheaf x.1).subschemeι ⁻¹' stalkSingularLocus X := by
  simpa only [Set.mem_preimage, pointClosureSubschemeι_genericPoint] using
    x.notMem_stalkSingularLocus

/-- The union of the ambient and intrinsic singular loci on a reduced divisor is
proper. Closedness of this union remains a separate regular-locus theorem. -/
theorem stalkSingularLoci_pointClosureSubscheme_ne_univ
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (x : SchemeDivisorPoint X) :
    ((pointClosureIdealSheaf x.1).subschemeι ⁻¹' stalkSingularLocus X ∪
      stalkSingularLocus (pointClosureIdealSheaf x.1).subscheme) ≠ Set.univ := by
  intro h
  have hmem := h.symm ▸ Set.mem_univ
    (genericPoint (pointClosureIdealSheaf x.1).subscheme)
  exact hmem.elim (genericPoint_notMem_ambient_stalkSingularLocus x)
    genericPoint_notMem_stalkSingularLocus

end Pcf
