/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.GlobalNormalizationDynamics
import Pcf.Bounding.DivisorFlagCodimension
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Exceptional sets on an actual invariant divisor

This file constructs the geometric exceptional sets on the reduced closure of a
divisor point. Incidence means membership in the closure of the other ambient
divisor. The singular correction uses the actual ambient and divisor stalks.

This file supplies the geometric exceptional-set layer; later files complete the
constructor of `InvariantDivisorStep0LocalData`.  In particular,
`AffineSchemeRamification.lean` proves the affine-to-stalk ramification comparison,
and `FiniteSingularCorrection.lean` obtains the finite singular correction directly
from generic smoothness and local principal generation, without assuming that the
entire regular locus is open.  No branch-avoidance, PCF, or étaleness conclusion is
assumed in either construction.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

attribute [local instance] specializationOrder

/-- The reduced closure of a point is irreducible. -/
instance pointClosureSubscheme_irreducible {X : Scheme.{u}} (x : X) :
    IrreducibleSpace (pointClosureIdealSheaf x).subscheme := by
  change IrreducibleSpace (closure ({x} : Set X))
  exact isIrreducible_iff_irreducibleSpace.mp (isIrreducible_singleton.closure)

/-- The point-closure construction uses a radical ideal on every affine chart. -/
instance pointClosureSubscheme_reduced {X : Scheme.{u}} (x : X) :
    AlgebraicGeometry.IsReduced (pointClosureIdealSheaf x).subscheme := by
  let I := pointClosureIdealSheaf x
  let (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover I.subscheme
    I.subschemeCover.openCover).mpr
  intro U
  let V : X.affineOpens := U
  exact inferInstanceAs
    (AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, V) ⧸ I.ideal V))))

/-- A reduced point closure is an integral scheme, including in a nonnormal ambient. -/
instance pointClosureSubscheme_integral {X : Scheme.{u}} (x : X) :
    IsIntegral (pointClosureIdealSheaf x).subscheme :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The point closure inherits local Noetherianity from the ambient scheme. -/
instance pointClosureSubscheme_locallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] (x : X) :
    IsLocallyNoetherian (pointClosureIdealSheaf x).subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian (pointClosureIdealSheaf x).subschemeι

/-- The point closure inherits topological Noetherianity from the ambient scheme. -/
instance pointClosureSubscheme_noetherian {X : Scheme.{u}}
    [NoetherianSpace X] (x : X) :
    NoetherianSpace (pointClosureIdealSheaf x).subscheme :=
  (pointClosureIdealSheaf x).subschemeι.isEmbedding.isInducing.noetherianSpace

/-- The actual generic point of the reduced closure maps to the original point. -/
theorem pointClosureSubscheme_genericPoint {X : Scheme.{u}} (x : X) :
    (pointClosureIdealSheaf x).subschemeι
      (genericPoint (pointClosureIdealSheaf x).subscheme) = x := by
  symm
  apply (isGenericPoint_closure (x := x)).eq
  have h := (genericPoint_spec (pointClosureIdealSheaf x).subscheme).image
    (pointClosureIdealSheaf x).subschemeι.continuous
  rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
  change IsGenericPoint _ (closure (closure ({x} : Set X))) at h
  simpa only [closure_closure] using h

/-- Actual incidence of a divisor of `A` with the closure of an ambient divisor. -/
def invariantDivisorMeets {X : Scheme.{u}} (A E : SchemeDivisorPoint X) :
    Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme) :=
  {Q | (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ closure ({E.1} : Set X)}

/-- Two distinct divisor points do not specialize to one another. -/
theorem SchemeDivisorPoint.not_mem_closure_of_ne {X : Scheme.{u}}
    (A E : SchemeDivisorPoint X) (h : E ≠ A) :
    A.1 ∉ closure ({E.1} : Set X) := by
  intro hAE
  have hle : A.1 ≤ E.1 := specializes_iff_mem_closure.mpr hAE
  have hne : A.1 ≠ E.1 := fun he ↦ h (Subtype.ext he.symm)
  have hlt := Order.coheight_strictAnti (lt_of_le_of_ne hle hne)
    (show Order.coheight E.1 < ⊤ by rw [E.2]; exact ENat.natCast_lt_top 1)
  rw [A.2, E.2] at hlt
  exact (lt_irrefl _ hlt)

/-- Every divisor flag has ambient codimension at least two. This direction is
purely topological; the reverse inequality requires the dimension formula. -/
theorem SchemeDivisorPoint.two_le_coheight_closureDivisor {X : Scheme.{u}}
    (A : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme) :
    2 ≤ Order.coheight ((pointClosureIdealSheaf A.1).subschemeι Q.1) := by
  have hle : (pointClosureIdealSheaf A.1).subschemeι Q.1 ≤ A.1 :=
    specializes_iff_mem_closure.mpr (pointClosureSubschemeι_mem A.1 Q.1)
  have hne : (pointClosureIdealSheaf A.1).subschemeι Q.1 ≠ A.1 := by
    intro he
    have hq : Q.1 = genericPoint (pointClosureIdealSheaf A.1).subscheme :=
      (pointClosureIdealSheaf A.1).subschemeι.isEmbedding.injective
        (he.trans (pointClosureSubscheme_genericPoint A.1).symm)
    have hmax : IsMax (genericPoint (pointClosureIdealSheaf A.1).subscheme) :=
      fun _ _ ↦ genericPoint_specializes _
    have hzero := Order.coheight_eq_zero.mpr hmax
    rw [← hq, Q.2] at hzero
    exact one_ne_zero hzero
  simpa only [A.2, one_add_one_eq_two] using
    Order.coheight_add_one_le (lt_of_le_of_ne hle hne)

/-- A height-one prime on an affine open gives the same divisor in the ambient
scheme by its canonical open immersion. -/
def schemeDivisorPointOfAffinePrime {X : Scheme.{u}} (U : X.affineOpens)
    (E : HeightOnePrime Γ(X, U)) : SchemeDivisorPoint X := by
  let hU : IsAffineOpen (U : X.Opens) := U.2
  exact ⟨hU.fromSpec E.1, (AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    hU.fromSpec).trans ((AlgebraicGeometry.idealHeight_eq_coheight
      Γ(X, U) E.1).symm.trans E.2)⟩

/-- Inclusion of an affine divisor into the ambient scheme is injective. -/
theorem schemeDivisorPointOfAffinePrime_injective {X : Scheme.{u}} (U : X.affineOpens) :
    Function.Injective (schemeDivisorPointOfAffinePrime U) := by
  intro E F h
  let hU : IsAffineOpen (U : X.Opens) := U.2
  have hval : hU.fromSpec E.1 = hU.fromSpec F.1 :=
    congrArg (fun D : SchemeDivisorPoint X ↦ D.1) h
  exact Subtype.ext (hU.fromSpec.isEmbedding.injective hval)

/-- Passing an ambient divisor to an affine chart and back recovers it. -/
theorem schemeDivisorPointOfAffinePrime_affinePrime {X : Scheme.{u}}
    (A : SchemeDivisorPoint X) (U : X.affineOpens) (hA : A.1 ∈ (U : X.Opens)) :
    schemeDivisorPointOfAffinePrime U (affinePrimeOfSchemeDivisorPoint A U hA) = A := by
  apply Subtype.ext
  have hprime : (affinePrimeOfSchemeDivisorPoint A U hA).1 =
      U.2.primeIdealOf ⟨A.1, hA⟩ :=
    PrimeSpectrum.ext (pointClosureIdealSheaf_ideal A.1 U hA)
  change U.2.fromSpec (affinePrimeOfSchemeDivisorPoint A U hA).1 = A.1
  rw [hprime, U.2.fromSpec_primeIdealOf]

/-- The prime-ideal incidence used on affine charts implies the actual closed
point-closure incidence defining `invariantDivisorMeets`. -/
theorem schemeDivisorPointOfAffinePrime_mem_closure {X : Scheme.{u}}
    (U : X.affineOpens) (E : HeightOnePrime Γ(X, U)) (y : (U : X.Opens))
    (hle : E.1.asIdeal ≤ (U.2.primeIdealOf y).asIdeal) :
    y.1 ∈ closure ({(schemeDivisorPointOfAffinePrime U E).1} : Set X) := by
  have hsp := (PrimeSpectrum.le_iff_specializes E.1 (U.2.primeIdealOf y)).mp hle
  have hmap := hsp.map U.2.fromSpec.continuous
  rw [U.2.fromSpec_primeIdealOf] at hmap
  exact specializes_iff_mem_closure.mp hmap

/-- The finite affine coordinate map and the actual scheme map send the same
height-one prime to the same ambient point. -/
theorem schemeDivisorPointOfAffinePrime_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (Q : HeightOnePrime Γ(X, finitePreimageAffine f U)) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    letI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian U
    letI : Module.Finite Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      finitePreimageModuleFinite f U
    letI : IsNoetherianRing Γ(X, finitePreimageAffine f U) :=
      IsNoetherianRing.of_finite Γ(Y, U) Γ(X, finitePreimageAffine f U)
    letI : FaithfulSMul Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
      finitePreimageFaithfulSMul f U
    f (schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) Q).1 =
      (schemeDivisorPointOfAffinePrime U (heightOneUnder (R := Γ(Y, U)) Q)).1 := by
  dsimp only
  have h := congrArg (fun g : Spec Γ(X, finitePreimageAffine f U) ⟶ Y ↦ g Q.1)
    (IsAffineOpen.SpecMap_appLE_fromSpec f U.2
      (finitePreimageAffine f U).2 le_rfl)
  change U.2.fromSpec
    (PrimeSpectrum.comap (f.appLE U (finitePreimageAffine f U) le_rfl).hom Q.1) =
      f ((finitePreimageAffine f U).2.fromSpec Q.1) at h
  have happ : f.appLE U (finitePreimageAffine f U) le_rfl = f.app U :=
    f.appLE_eq_app
  rw [happ] at h
  exact h.symm

/-- A proper intersection with another ambient divisor has only finitely many
codimension-one points on the reduced divisor. -/
theorem invariantDivisorMeets_finite {X : Scheme.{u}} [NoetherianSpace X]
    (A E : SchemeDivisorPoint X) (h : E ≠ A) :
    (invariantDivisorMeets A E).Finite := by
  apply finite_schemeDivisorPoint_mem_of_isClosed
    (isClosed_closure.preimage (pointClosureIdealSheaf A.1).subschemeι.continuous)
  intro heq
  have hmem : genericPoint (pointClosureIdealSheaf A.1).subscheme ∈
      (pointClosureIdealSheaf A.1).subschemeι ⁻¹' closure ({E.1} : Set X) :=
    heq.symm ▸ Set.mem_univ _
  exact A.not_mem_closure_of_ne E h (by
    simpa only [Set.mem_preimage, pointClosureSubscheme_genericPoint] using hmem)

/-- The two actual stalk singular loci excluded by Step 0. -/
def invariantDivisorSing {X : Scheme.{u}} (A : SchemeDivisorPoint X) :
    Set (SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme) :=
  {Q | (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ stalkSingularLocus X ∨
    Q.1 ∈ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme}

/-- Exclusion from the singular correction supplies the two regularity fields
of the literal Step-0 data. -/
theorem invariantDivisorSing_regular {X : Scheme.{u}} (A : SchemeDivisorPoint X)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (h : Q ∉ invariantDivisorSing A) :
    (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉ stalkSingularLocus X ∧
      Q.1 ∉ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme := by
  exact not_or.mp h

/-- Closedness of the two genuine singular loci is enough for the singular
correction to be finite: normality makes the ambient generic divisor stalk a
DVR, and the divisor's own generic stalk is a field. -/
theorem invariantDivisorSing_finite_of_isClosed {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] (A : SchemeDivisorPoint X)
    (hX : IsClosed (stalkSingularLocus X))
    (hA : IsClosed (stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme)) :
    (invariantDivisorSing A).Finite := by
  have h₁ : {Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme |
      (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ stalkSingularLocus X}.Finite := by
    apply finite_schemeDivisorPoint_mem_of_isClosed
      (hX.preimage (pointClosureIdealSheaf A.1).subschemeι.continuous)
    intro heq
    have hmem : genericPoint (pointClosureIdealSheaf A.1).subscheme ∈
        (pointClosureIdealSheaf A.1).subschemeι ⁻¹' stalkSingularLocus X :=
      heq.symm ▸ Set.mem_univ _
    have hsing : A.1 ∈ stalkSingularLocus X := by
      simpa only [Set.mem_preimage, pointClosureSubscheme_genericPoint] using hmem
    let : IsDiscreteValuationRing (X.presheaf.stalk A.1) :=
      A.stalk_isDiscreteValuationRing
    exact hsing inferInstance
  have h₂ : {Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme |
      Q.1 ∈ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme}.Finite := by
    apply finite_schemeDivisorPoint_mem_of_isClosed hA
    intro heq
    have hsing : genericPoint (pointClosureIdealSheaf A.1).subscheme ∈
        stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme :=
      heq.symm ▸ Set.mem_univ _
    exact hsing inferInstance
  exact h₁.union h₂

/-- The structure morphism over a field makes each actual stalk a field algebra. -/
@[instance_reducible]
def schemeStalkAlgebraOfField (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x (by trivial)).hom.comp
    ((s.appLE ⊤ ⊤ (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra

/-- Characteristic zero of the ground field passes to each scheme stalk. -/
theorem schemeStalkCharZeroOfField (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (x : X) :
    CharZero (X.presheaf.stalk x) := by
  let := schemeStalkAlgebraOfField k s x
  exact charZero_of_injective_ringHom (algebraMap k (X.presheaf.stalk x)).injective

/-- Every affine coordinate ring of a scheme over a characteristic-zero field
has the rational algebra structure required by Step 0. -/
@[instance_reducible]
def schemeAffineRationalAlgebraOfField (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (U : X.affineOpens) :
    Algebra ℚ Γ(X, U) :=
  (((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).comp
    (algebraMap ℚ k)).toAlgebra

/-- The canonical invariant restriction is dominant. -/
instance SchemeDivisorPoint.invariantClosureMap_dominant
    {X : Scheme.{u}} (f : X ⟶ X) (A : SchemeDivisorPoint X)
    (hA : f A.1 = A.1) : IsDominant (A.invariantClosureMap f hA) :=
  pointClosureSubschemeMap_isDominant f A.1 A.1 hA

/-- The actual canonical normalization dynamics of the invariant reduced divisor.
Its finiteness and characteristic-zero inputs come from the ambient geometry. -/
def invariantDivisorNormalization (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsLocallyNoetherian X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    SchemeNormalizationUnnormDyn (pointClosureIdealSheaf A.1).subscheme
      (SchemeDivisorPoint (schemeGlobalNormalization
        (pointClosureIdealSheaf A.1).subscheme)) := by
  let sA := (pointClosureIdealSheaf A.1).subschemeι ≫ s
  let : LocallyOfFiniteType sA := inferInstance
  let : CharZero ((pointClosureIdealSheaf A.1).subscheme.presheaf.stalk
      (genericPoint (pointClosureIdealSheaf A.1).subscheme)) :=
    schemeStalkCharZeroOfField k sA _
  exact schemeGlobalNormalizationUnnormDynOfFiniteType k sA
    (A.invariantClosureMap f hA)

/-- The stored unnormalized map is exactly the canonical restriction. -/
theorem invariantDivisorNormalization_g (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsLocallyNoetherian X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    (invariantDivisorNormalization k s f A hA).g = A.invariantClosureMap f hA := rfl

/-- The actual restriction and the unnormalized step stored in the canonical
normalization package have the same iterated point maps. -/
theorem invariantDivisorNormalization_iterate_step_val
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsLocallyNoetherian X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) (m : ℕ)
    (Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme) :
    (((invariantDivisorNormalization k s f A hA).toNormalizationUnnormDyn.step)^[m] Q).1 =
      (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base Q.1 := by
  exact schemeDivisorMap_iterate_val _
    (invariantDivisorNormalization k s f A hA).g_preserves_divisors m Q

/-- A specified inverse image on the restriction lies in the finite affine
preimage of every affine chart containing its target. -/
theorem SchemeDivisorPoint.invariantClosureIterate_source_mem
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) (m : ℕ)
    (U : X.affineOpens)
    (Q Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hQ : (pointClosureIdealSheaf A.1).subschemeι Q.1 ∈ (U : X.Opens))
    (hQQ : (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base Q'.1 = Q.1) :
    Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens) := by
  have hsquare := congrArg (fun g : (pointClosureIdealSheaf A.1).subscheme ⟶ X ↦ g Q'.1)
    (pointClosureSubschemeMap_iterate_subschemeι f A.1 hA m)
  change (pointClosureIdealSheaf A.1).subschemeι
      ((CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base Q'.1) =
    (CategoryTheory.End.of f ^ m).asHom.base ((pointClosureIdealSheaf A.1).subschemeι Q'.1)
    at hsquare
  change (CategoryTheory.End.of f ^ m).asHom.base
    ((pointClosureIdealSheaf A.1).subschemeι Q'.1) ∈ (U : X.Opens)
  rw [← hsquare, hQQ]
  exact hQ

#print axioms pointClosureSubscheme_irreducible
#print axioms pointClosureSubscheme_reduced
#print axioms pointClosureSubscheme_integral
#print axioms pointClosureSubscheme_locallyNoetherian
#print axioms pointClosureSubscheme_noetherian
#print axioms pointClosureSubscheme_genericPoint
#print axioms SchemeDivisorPoint.not_mem_closure_of_ne
#print axioms SchemeDivisorPoint.two_le_coheight_closureDivisor
#print axioms schemeDivisorPointOfAffinePrime
#print axioms schemeDivisorPointOfAffinePrime_injective
#print axioms schemeDivisorPointOfAffinePrime_affinePrime
#print axioms schemeDivisorPointOfAffinePrime_mem_closure
#print axioms schemeDivisorPointOfAffinePrime_map
#print axioms invariantDivisorMeets
#print axioms invariantDivisorMeets_finite
#print axioms invariantDivisorSing
#print axioms invariantDivisorSing_regular
#print axioms invariantDivisorSing_finite_of_isClosed
#print axioms schemeStalkAlgebraOfField
#print axioms schemeStalkCharZeroOfField
#print axioms schemeAffineRationalAlgebraOfField
#print axioms SchemeDivisorPoint.invariantClosureMap_dominant
#print axioms invariantDivisorNormalization
#print axioms invariantDivisorNormalization_g
#print axioms invariantDivisorNormalization_iterate_step_val
#print axioms SchemeDivisorPoint.invariantClosureIterate_source_mem

#check @invariantDivisorMeets
#check @invariantDivisorMeets_finite
#check @invariantDivisorSing
#check @invariantDivisorSing_finite_of_isClosed
#check @SchemeDivisorPoint.two_le_coheight_closureDivisor
#check @schemeDivisorPointOfAffinePrime_map
#check @invariantDivisorNormalization
#check @invariantDivisorNormalization_g
#check @invariantDivisorNormalization_iterate_step_val
#check @SchemeDivisorPoint.invariantClosureIterate_source_mem

end

end Pcf
