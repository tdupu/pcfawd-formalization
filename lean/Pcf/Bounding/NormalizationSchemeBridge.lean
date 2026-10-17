/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NormalizationRamification
public import Pcf.Bounding.SchemeDynamics

/-!
# The local normalization square

The tensor-image branch of a commuting local square is constructed in this
file. Its localization has the same fraction field as the upper source ring
when the source vertical map is birational. Thus no choice of a quotient or
of a normalized base-change component is part of the ramification comparison.
-/

@[expose] public section

universe u

open IsLocalRing
open scoped TensorProduct

namespace Pcf

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

section LocalSquare

variable (A B R N K : Type*)
    [CommRing A] [CommRing B] [CommRing R] [CommRing N] [Field K]
    [Algebra A B] [Algebra A R] [Algebra A N]
    [Algebra B N] [Algebra R N]
    [IsScalarTower A B N] [IsScalarTower A R N]
    [IsDedekindDomain R] [IsLocalRing R]
    [IsDomain N] [IsLocalRing N] [IsLocalHom (algebraMap R N)]
    [Algebra B K] [Algebra N K] [IsScalarTower B N K]
    [IsFractionRing B K] [IsFractionRing N K]
    [Algebra.EssFiniteType A B]

include K

/-- Unramifiedness in the lower row of a commuting local square forces every
ramification index in the upper row to be one, provided the upper target is
local Dedekind and the source vertical map is birational. -/
theorem ramificationIdx_eq_one_of_local_birational_square
    [Algebra.FormallyUnramified A B] (q : Ideal N) [q.IsPrime] :
    q.ramificationIdx R = 1 := by
  let f : R ⊗[A] B →ₐ[R] N :=
    AlgHom.liftEquiv A R B N (IsScalarTower.toAlgHom A B N)
  let D := f.range
  let p : Ideal D := (maximalIdeal N).comap (algebraMap D N)
  let C := Localization.AtPrime p
  have hunits : ∀ y : p.primeCompl, IsUnit (algebraMap D N y) := by
    intro y
    exact notMem_maximalIdeal.mp y.2
  let j : C →ₐ[R] N := IsLocalization.liftAlgHom (f := D.val) hunits
  letI : Algebra C N := j.toRingHom.toAlgebra
  letI : IsScalarTower R C N := IsScalarTower.of_algebraMap_eq (fun r ↦ (j.commutes r).symm)
  have hj : Function.Injective j := by
    change Function.Injective (IsLocalization.lift hunits : C → N)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      simpa [j, IsLocalization.liftAlgHom_apply, Subalgebra.algebraMap_apply]
        using congrArg j h
    · intro h
      exact congrArg (algebraMap D C) (Subtype.ext h)
  letI : IsLocalHom (algebraMap C N) := ⟨fun x hx ↦ by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    apply (IsLocalization.AtPrime.isUnit_mk'_iff C p a s).mpr
    have ha : IsUnit (algebraMap D N a) := by
      have heq : algebraMap D N a = algebraMap D N s *
          algebraMap C N (IsLocalization.mk' C a s) :=
        (IsLocalization.lift_mk'_spec hunits a _ s).mp rfl
      rw [heq]
      exact (hunits s).mul hx
    exact notMem_maximalIdeal.mpr ha⟩
  letI : IsLocalHom (algebraMap R C) := by
    have hcomp : (algebraMap C N).comp (algebraMap R C) = algebraMap R N :=
      (IsScalarTower.algebraMap_eq R C N).symm
    haveI : IsLocalHom ((algebraMap C N).comp (algebraMap R C)) := hcomp ▸ inferInstance
    exact isLocalHom_of_comp (algebraMap R C) (algebraMap C N)
  letI : Algebra C K := ((algebraMap N K).comp (algebraMap C N)).toAlgebra
  letI : IsScalarTower C N K := IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul C K :=
    (faithfulSMul_iff_algebraMap_injective C K).mpr
      ((IsFractionRing.injective N K).comp hj)
  have hB (b : B) : algebraMap B N b ∈ D := by
    exact ⟨1 ⊗ₜ[A] b, by simp [f]⟩
  letI : IsFractionRing C K := IsFractionRing.of_field C K fun z ↦ by
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective B z
    refine ⟨algebraMap D C ⟨algebraMap B N a, hB a⟩,
      algebraMap D C ⟨algebraMap B N b, hB b⟩, ?_⟩
    change z = algebraMap N K (j (algebraMap D C _)) /
      algebraMap N K (j (algebraMap D C _))
    simp only [j, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change z = algebraMap N K (algebraMap B N a) / algebraMap N K (algebraMap B N b)
    simpa only [← IsScalarTower.algebraMap_apply B N K] using hab.symm
  exact ramificationIdx_eq_one_of_localized_birational_baseChange
    A B R D C N K f.rangeRestrict f.rangeRestrict_surjective p.primeCompl q

end LocalSquare

open CategoryTheory _root_.AlgebraicGeometry

/-- A pointwise birationality condition on the actual normalization stalk map.
The algebra structure on the function field is the composite of that map with
the canonical inclusion of the upper stalk. This condition says nothing about
ramification or either critical locus. -/
def IsStalkBirationalAt {A N : Scheme.{u}} [IsIntegral N]
    (nu : N ⟶ A) (x : N) : Prop :=
  letI : Algebra (A.presheaf.stalk (nu x)) N.functionField :=
    ((algebraMap (N.presheaf.stalk x) N.functionField).comp
      (nu.stalkMap x).hom).toAlgebra
  IsFractionRing (A.presheaf.stalk (nu x)) N.functionField

/-- Birationality at the generic point supplies the shared fraction field for
every actual stalk map. No finiteness or normality hypothesis is needed here. -/
theorem isStalkBirationalAt_of_isIso_generic_stalkMap
    {A N : Scheme.{u}} [IsIntegral A] [IsIntegral N]
    (nu : N ⟶ A) [IsDominant nu]
    [IsIso (nu.stalkMap (genericPoint N))] (x : N) :
    IsStalkBirationalAt nu x := by
  let B := A.presheaf.stalk (nu x)
  letI : Algebra B N.functionField :=
    ((algebraMap (N.presheaf.stalk x) N.functionField).comp
      (nu.stalkMap x).hom).toAlgebra
  have hη : nu (genericPoint N) = genericPoint A :=
    map_genericPoint_eq_of_isDominant nu
  let e := ((A.presheaf.stalkCongr (.of_eq hη)).symm ≪≫
    asIso (nu.stalkMap (genericPoint N))).commRingCatIsoToRingEquiv
  let eB : A.functionField ≃ₐ[B] N.functionField := {
    __ := e
    commutes' := fun b ↦ by
      have hgen := (genericPoint_spec N).specializes (Set.mem_univ x)
      have h := nu.stalkSpecializes_stalkMap (genericPoint N) x hgen
      change ((A.presheaf.stalkSpecializes
        ((genericPoint_spec A).specializes (Set.mem_univ (nu x))) ≫
        (A.presheaf.stalkCongr (.of_eq hη)).inv ≫
        nu.stalkMap (genericPoint N)).hom b) =
          ((nu.stalkMap x ≫ N.presheaf.stalkSpecializes hgen).hom b)
      rw [← Category.assoc]
      change ((A.presheaf.stalkSpecializes
        ((genericPoint_spec A).specializes (Set.mem_univ (nu x))) ≫
        A.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
        nu.stalkMap (genericPoint N)).hom b) = _
      rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
      exact congrArg (fun f : B ⟶ N.functionField ↦ f.hom b) h }
  exact IsFractionRing.of_algEquiv eB

/-- A ramified divisor upstairs lies in the non-unramified locus downstairs.
The only normalization-specific input is the common fraction field of the
actual source stalk map; the base-change branch is constructed in the proof. -/
theorem not_formallyUnramified_stalkMap_of_one_lt_schemeDivisorRamificationIdx
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [LocallyOfFiniteType g] [IsFinite gN] [IsDominant gN]
    [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    (hsquare : gN ≫ nu = nu ≫ g) (Q : SchemeDivisorPoint N)
    (hbirational : IsStalkBirationalAt nu Q.1)
    (hQ : 1 < schemeDivisorRamificationIdx gN Q) :
    ¬ (g.stalkMap (nu Q.1)).hom.FormallyUnramified := by
  let R₀ := A.presheaf.stalk (g (nu Q.1))
  let B := A.presheaf.stalk (nu Q.1)
  let R := N.presheaf.stalk (gN Q.1)
  let S := N.presheaf.stalk Q.1
  let K := N.functionField
  have hpoint : g (nu Q.1) = nu (gN Q.1) :=
    congrArg (fun f : N ⟶ A ↦ f Q.1) hsquare.symm
  let v : R₀ →+* R :=
    ((A.presheaf.stalkCongr (.of_eq hpoint)).hom ≫ nu.stalkMap (gN Q.1)).hom
  letI : Algebra R₀ B := (g.stalkMap (nu Q.1)).hom.toAlgebra
  letI : Algebra B S := (nu.stalkMap Q.1).hom.toAlgebra
  letI : Algebra R S := (gN.stalkMap Q.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (gN.stalkMap Q.1).hom)
  letI : Algebra R₀ R := v.toAlgebra
  letI : Algebra R₀ S :=
    ((nu.stalkMap Q.1).hom.comp (g.stalkMap (nu Q.1)).hom).toAlgebra
  letI : IsScalarTower R₀ B S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' (by
    change ((g.stalkMap (nu Q.1)) ≫ nu.stalkMap Q.1).hom =
      ((gN.stalkMap Q.1).hom.comp v)
    have h := Scheme.Hom.stalkMap_congr_hom (nu ≫ g) (gN ≫ nu) hsquare.symm Q.1
    simp only [Scheme.Hom.stalkMap_comp] at h
    exact congrArg CommRingCat.Hom.hom h)
  letI : Algebra B K := ((algebraMap S K).comp (algebraMap B S)).toAlgebra
  letI : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing B K := hbirational
  letI : IsDiscreteValuationRing R :=
    (schemeDivisorMap gN (coheight_apply_eq_one gN) Q).stalk_isDiscreteValuationRing
  letI : Algebra.EssFiniteType R₀ B := LocallyOfFiniteType.stalkMap g (nu Q.1)
  intro hu
  letI : Algebra.FormallyUnramified R₀ B := hu
  have he := ramificationIdx_eq_one_of_local_birational_square R₀ B R S K
    (maximalIdeal S)
  exact (Nat.lt_irrefl 1) (he ▸ hQ)

/-- A commuting normalization square commutes after every iterate. -/
theorem normalization_square_pow
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    (hsquare : gN ≫ nu = nu ≫ g) (m : ℕ) :
    (CategoryTheory.End.of gN ^ m).asHom ≫ nu = nu ≫ (CategoryTheory.End.of g ^ m).asHom := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, pow_succ]
      change (gN ≫ (CategoryTheory.End.of gN ^ m).asHom) ≫ nu =
        nu ≫ (g ≫ (CategoryTheory.End.of g ^ m).asHom)
      rw [Category.assoc, ih, ← Category.assoc, hsquare, Category.assoc]

/-- U1 for actual finite scheme maps and an actual birational normalization
map. The hypothesis at the generic stalk is the usual function-field meaning
of birationality, and is independent of every critical locus and iterate. -/
theorem mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx_of_birational
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsFinite gN] [IsDominant gN]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [IsDominant nu] [IsIso (nu.stalkMap (genericPoint N))]
    (hsquare : gN ≫ nu = nu ≫ g)
    (hcodim : ∀ Q : SchemeDivisorPoint N, Order.coheight (nu Q.1) = 1)
    (m : ℕ) (Q : SchemeDivisorPoint N)
    (hQ : 1 < schemeDivisorRamificationIdx (CategoryTheory.End.of gN ^ m).asHom Q) :
    schemeDivisorMap nu hcodim Q ∈
      schemeDivisorNonUnramifiedLocus (CategoryTheory.End.of g ^ m).asHom := by
  exact not_formallyUnramified_stalkMap_of_one_lt_schemeDivisorRamificationIdx
    (CategoryTheory.End.of g ^ m).asHom (CategoryTheory.End.of gN ^ m).asHom nu
    (normalization_square_pow g gN nu hsquare m) Q
    (isStalkBirationalAt_of_isIso_generic_stalkMap nu Q.1) hQ

/-- Construct the actual normalization dynamics without a U1 assumption.
The generic stalk isomorphism records that the finite dominant map `nu` is
birational. Together with normality of `N`, these are the structural properties
of a finite normalization needed by the construction. -/
noncomputable def schemeNormalizationUnnormalizedDynamicsOfFiniteBirational
    (k : Type*) [Field k]
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [TopologicalSpace.NoetherianSpace A]
    [CharZero (A.presheaf.stalk (genericPoint A))]
    [IsIso (nu.stalkMap (genericPoint N))]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]
    (hsquare : gN ≫ nu = nu ≫ g) :
    SchemeNormalizationUnnormalizedDynamics A (SchemeDivisorPoint N) :=
  schemeNormalizationUnnormalizedDynamicsOfFiniteType k g gN nu hsquare fun m Q hQ ↦
    mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx_of_birational g gN nu hsquare
      (coheight_apply_eq_one_of_finiteType nu k) m Q
      ((divisorDynamicsOfFiniteNormalization_iterateRamificationIdx gN nu m Q) ▸ hQ)

#print axioms ramificationIdx_eq_one_of_local_birational_square
#print axioms isStalkBirationalAt_of_isIso_generic_stalkMap
#print axioms not_formallyUnramified_stalkMap_of_one_lt_schemeDivisorRamificationIdx
#print axioms normalization_square_pow
#print axioms mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx_of_birational
#print axioms schemeNormalizationUnnormalizedDynamicsOfFiniteBirational

end Pcf
