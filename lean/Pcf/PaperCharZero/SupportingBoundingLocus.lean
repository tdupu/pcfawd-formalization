/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingTower
public import Pcf.PaperCharZero.SupportingDictionary
public import Pcf.Bounding.FiniteSingularCorrection
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# The literal exceptional locus of the bounding theorem

The exceptional set is exactly `(B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B`, as a subset
of the actual reduced divisor `B`, where `Z` is the union of the actual branch
divisors other than `B`. This module does not replace singular loci by larger
closed corrections. Full closedness still needs finite-type regular-locus
openness; properness and finiteness of divisor points do not require that bridge.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf.PaperCharZero

/-- The literal exceptional subset in `paper.tex`, `thm:bounding`, formed using
actual nonreduced divisor fibers and actual singular stalks. For the theorem,
the distinguished divisor is the reduced image of the source divisor. -/
def boundingExceptionalSet {X Y : Scheme.{u}} (f : X ⟶ Y) (B : SchemeDivisorPoint Y) :
    Set (pointClosureIdealSheaf B.1).subscheme :=
  (pointClosureIdealSheaf B.1).subschemeι ⁻¹'
      divisorSupport (schemeReducedFiberBranch f \ {B}) ∪
    (pointClosureIdealSheaf B.1).subschemeι ⁻¹' stalkSingularLocus Y ∪
    stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme

/-- Step 0's generic-point exclusion for the exact exceptional set. Normality
of the ambient target makes its divisor stalk regular; the divisor's generic
stalk is a field. No closedness or branch-finiteness premise is needed. -/
theorem genericPoint_notMem_boundingExceptionalSet
    {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (f : X ⟶ Y) (B : SchemeDivisorPoint Y) :
    genericPoint (pointClosureIdealSheaf B.1).subscheme ∉ boundingExceptionalSet f B := by
  rintro ((hbranch | hambient) | hdivisor)
  · have hB : B.1 ∈ divisorSupport (schemeReducedFiberBranch f \ {B}) := by
      simpa only [Set.mem_preimage, pointClosureSubscheme_genericPoint] using hbranch
    exact ((mem_divisorSupport_iff B _).mp hB).2 (Set.mem_singleton B)
  · apply B.notMem_stalkSingularLocus
    simpa only [Set.mem_preimage, pointClosureSubscheme_genericPoint] using hambient
  · exact genericPoint_notMem_stalkSingularLocus hdivisor

/-- The literal exceptional set in `thm:bounding` is proper, without assuming
either singular locus closed. -/
theorem boundingExceptionalSet_ne_univ
    {X Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (f : X ⟶ Y) (B : SchemeDivisorPoint Y) :
    boundingExceptionalSet f B ≠ Set.univ := by
  intro heq
  exact genericPoint_notMem_boundingExceptionalSet f B (heq.symm ▸ Set.mem_univ _)

/-- Finite dominant maps of normal varieties in characteristic zero have
finitely many actual nonreduced-fiber branch divisors. -/
theorem reducedFiberBranch_finite_charZero
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    (schemeReducedFiberBranch f).Finite := by
  let := charZero_stalk_of_field k s (genericPoint Y)
  apply ((schemeDivisorNonEtaleLocus_finite_of_cover_charZero f).image
    (fun Q => Q.mapFiniteDominantNormal f)).subset
  intro E hE
  obtain ⟨Q, hQE, hQ⟩ := (mem_schemeReducedFiberBranch_iff f E).mp hE
  exact ⟨Q, mem_schemeDivisorNonEtaleLocus_of_one_lt_ramificationIdx f Q hQ,
    Subtype.ext hQE⟩

/-- The other-branch term `B ∩ Z` of the literal exceptional set is closed.
Thus the unresolved closedness issue concerns the two actual singular terms. -/
theorem isClosed_otherBranch_on_divisor
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y) :
    IsClosed ((pointClosureIdealSheaf B.1).subschemeι ⁻¹'
      divisorSupport (schemeReducedFiberBranch f \ {B})) :=
  (isClosed_divisorSupport _ ((reducedFiberBranch_finite_charZero k s f).subset
    Set.sdiff_subset)).preimage (pointClosureIdealSheaf B.1).subschemeι.continuous

/-- The literal exceptional set contains only finitely many divisor points,
without assuming it closed or enlarging it in the conclusion. -/
theorem finite_divisorPoints_boundingExceptionalSet
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] (B : SchemeDivisorPoint Y) :
    {Q : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
      Q.1 ∈ boundingExceptionalSet f B}.Finite := by
  have hbranch : (schemeReducedFiberBranch f \ {B}).Finite :=
    (reducedFiberBranch_finite_charZero k s f).subset Set.sdiff_subset
  have hmeets : (⋃ E ∈ schemeReducedFiberBranch f \ {B}, invariantDivisorMeets B E).Finite :=
    hbranch.biUnion fun E hE => invariantDivisorMeets_finite B E (by simpa using hE.2)
  apply (hmeets.union (invariantDivisorSing_finite_of_perfectField k s B)).subset
  intro Q hQ
  rcases hQ with ((hbranch | hambient) | hdivisor)
  · left
    obtain ⟨E, hx⟩ := Set.mem_iUnion.mp hbranch
    obtain ⟨hE, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨E, Set.mem_iUnion.mpr ⟨hE, hx⟩⟩
  · exact Or.inr (Or.inl hambient)
  · exact Or.inr (Or.inr hdivisor)

section EtaleOutside

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormalScheme X] [IsNormalScheme Y]

attribute [local instance] finitePreimageAlgebra IsLocallyNoetherian.component_noetherian
  finitePreimageAffine_moduleFinite finitePreimageSourceNoetherian
  finitePreimageAffine_faithfulSMul

/-- An affine branch component on an actual finite preimage chart is a branch
divisor of the original two-scheme morphism. -/
theorem affineBranch_mem_reducedFiberBranch
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (E : HeightOnePrime Γ(Y, U))
    (hE : E ∈ heightOneBranch (R := Γ(Y, U))
      (S := Γ(X, finitePreimageAffine f U))) :
    schemeDivisorPointOfAffinePrime U E ∈ schemeReducedFiberBranch f := by
  obtain ⟨F, hF, rfl⟩ := hE
  apply (mem_schemeReducedFiberBranch_iff f _).mpr
  refine ⟨schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) F,
    schemeDivisorPointOfAffinePrime_map f U F, ?_⟩
  rw [schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U F]
  exact hF

/-- Avoidance of the literal exceptional set implies the actual local
other-branch avoidance condition, for arbitrary source and target schemes. -/
theorem notMem_affineOtherBranch_of_notMem_boundingExceptionalSet
    (B : SchemeDivisorPoint Y) (z : (pointClosureIdealSheaf B.1).subscheme)
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (hzU : (pointClosureIdealSheaf B.1).subschemeι z ∈ (U : Y.Opens))
    (hz : z ∉ boundingExceptionalSet f B) :
    (⟨(pointClosureIdealSheaf B.1).subschemeι z, hzU⟩ : (U : Y.Opens)) ∉
      finiteAffineOtherBranchLocus (f := f) U
        (affinePrimeOfSchemeDivisorPoint B U
          (B.mem_affine_of_pointClosurePoint_mem U z hzU)) := by
  rintro ⟨E, hE, hEB, hinc⟩
  apply hz
  left; left
  apply Set.mem_iUnion.mpr
  refine ⟨schemeDivisorPointOfAffinePrime U E, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · refine ⟨affineBranch_mem_reducedFiberBranch f U E hE, ?_⟩
    intro heq
    apply hEB
    apply schemeDivisorPointOfAffinePrime_injective U
    exact (Set.mem_singleton_iff.mp heq).trans
      (schemeDivisorPointOfAffinePrime_affinePrime B U _).symm
  · exact schemeDivisorPointOfAffinePrime_mem_closure U E _ hinc

set_option backward.isDefEq.respectTransparency false in
/-- The étaleness assertion of `thm:bounding`, over every divisor point of the
target divisor outside the literal exceptional set. The source point is
arbitrary in that fiber. All local Cartier, purity, and Abhyankar chart inputs
are derived; none is a theorem hypothesis. Closedness of the exceptional set
is not needed for this conclusion. -/
theorem etale_over_divisor_outside_boundingExceptionalSet
    (k : Type u) [Field k] [CharZero k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X)
    (z : SchemeDivisorPoint (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hz : z.1 ∉ boundingExceptionalSet f (A.mapFiniteDominantNormal f))
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hxz : A.closureMapFiniteDominantNormal f x = z.1) :
    ∃ V : (pointClosureIdealSheaf A.1).subscheme.Opens,
      x ∈ V ∧ Etale (V.ι ≫ A.closureMapFiniteDominantNormal f) := by
  let B := A.mapFiniteDominantNormal f
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (pointClosureIdealSheaf B.1).subschemeι z.1 ∈ (⊤ : Y.Opens) by trivial)
  let U : Y.affineOpens := ⟨W, hW⟩
  have hzU : (pointClosureIdealSheaf B.1).subschemeι z.1 ∈ (U : Y.Opens) := hzW
  have hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens) := by
    change f ((pointClosureIdealSheaf A.1).subschemeι x) ∈ (U : Y.Opens)
    have hsquare := congrArg (fun h => h x)
      (pointClosureSubschemeMap_subschemeι f A.1 B.1 (by rfl))
    change (pointClosureIdealSheaf B.1).subschemeι
        (A.closureMapFiniteDominantNormal f x) =
      f ((pointClosureIdealSheaf A.1).subschemeι x) at hsquare
    rw [← hsquare, hxz]
    exact hzU
  let : Nonempty (U : Y.Opens) := ⟨⟨_, hzU⟩⟩
  let : Nonempty (finitePreimageAffine f U : X.Opens) := ⟨⟨_, hx⟩⟩
  let : Algebra ℚ Γ(Y, U) := schemeAffineRationalAlgebraOfField k s U
  have hambient : (pointClosureIdealSheaf B.1).subschemeι z.1 ∉ stalkSingularLocus Y :=
    fun h => hz (Or.inl (Or.inr h))
  have hdivisor : z.1 ∉ stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme :=
    fun h => hz (Or.inr h)
  have hp := A.closureStalkBoundingLocalizationOfCorrectionRegularDimTwoAt f U x hx z hzU hxz
    (B.closureDivisor_coheight_of_finiteType k s z) hambient hdivisor
    (notMem_affineOtherBranch_of_notMem_boundingExceptionalSet f B z.1 U hzU hz)
    (Stacks.zariskiNagataPurity _ _) (Stacks.abhyankarLemma _ _ _)
  let : IsFinite (A.closureMapFiniteDominantNormal f) :=
    pointClosureSubschemeMap_isFinite f A.1 B.1 (by rfl)
  exact (formallyEtale_stalkMap_iff_etale_neighborhood _ x).mp hp.formallyEtale

/-- The restriction is étale at every source divisor point whose image point
is outside the literal exceptional set. The image's codimension-one property
is derived from the actual finite dominant restriction and finite-type geometry.
The statement does not assume it as an extra hypothesis. -/
theorem etale_at_divisor_outside_boundingExceptionalSet
    (k : Type u) [Field k] [CharZero k]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hQ : A.closureMapFiniteDominantNormal f Q.1 ∉
      boundingExceptionalSet f (A.mapFiniteDominantNormal f)) :
    ∃ V : (pointClosureIdealSheaf A.1).subscheme.Opens,
      Q.1 ∈ V ∧ Etale (V.ι ≫ A.closureMapFiniteDominantNormal f) := by
  let B := A.mapFiniteDominantNormal f
  let g := A.closureMapFiniteDominantNormal f
  let : IsFinite g := pointClosureSubschemeMap_isFinite f A.1 B.1 rfl
  let : IsDominant g := pointClosureSubschemeMap_isDominant f A.1 B.1 rfl
  let sB := (pointClosureIdealSheaf B.1).subschemeι ≫ s
  let φ (U : (pointClosureIdealSheaf B.1).subscheme.affineOpens) :
      k →+* Γ((pointClosureIdealSheaf B.1).subscheme, U) :=
    (sB.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  let (U : (pointClosureIdealSheaf B.1).subscheme.affineOpens) :
      Algebra k Γ((pointClosureIdealSheaf B.1).subscheme, U) :=
    (φ U).toAlgebra
  have (U : (pointClosureIdealSheaf B.1).subscheme.affineOpens) :
      Algebra.FiniteType k Γ((pointClosureIdealSheaf B.1).subscheme, U) := by
    apply RingHom.finiteType_algebraMap.mp
    exact (sB.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  let E : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme :=
    ⟨g Q.1, coheight_apply_eq_one_of_finiteType g k Q⟩
  exact etale_over_divisor_outside_boundingExceptionalSet f k s A E hQ Q.1 rfl

end EtaleOutside

end Pcf.PaperCharZero
