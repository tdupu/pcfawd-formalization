/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeIteration
public import Pcf.Unnormalized

/-!
# Non-étale divisor dynamics in arbitrary characteristic

The critical set here is the failure of formal étaleness of the *actual*
stalk map of each iterate.  In characteristic `p` it detects both a nontrivial
ramification index and an inseparable residue extension, as required by
`paper-p.tex`.  Generic separability and Noetherianity make these sets finite.
This file does not assert that their orbits are finite.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

/-- Formal unramifiedness at a divisor stalk forces its local ramification
index to be one, in every characteristic. -/
theorem schemeDivisorRamificationIdx_eq_one_of_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : SchemeDivisorPoint X)
    (hx : (f.stalkMap x.1).hom.FormallyUnramified) :
    schemeDivisorRamificationIdx f x = 1 := by
  letI := (f.stalkMap x.1).hom.toAlgebra
  letI : Algebra.EssFiniteType (Y.presheaf.stalk (f x.1))
      (X.presheaf.stalk x.1) := LocallyOfFiniteType.stalkMap f x.1
  letI : Algebra.FormallyUnramified (Y.presheaf.stalk (f x.1))
      (X.presheaf.stalk x.1) := hx
  let q := IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)
  letI : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  letI : Algebra.IsUnramifiedAt (Y.presheaf.stalk (f x.1)) q :=
    (Algebra.formallyUnramified_iff_forall.mp hx) ⟨q, inferInstance⟩
  exact Ideal.ramificationIdx_eq_one q (Y.presheaf.stalk (f x.1))

/-- Index ramification on an actual divisor implies failure of formal
unramifiedness of the stalk map. -/
theorem mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : SchemeDivisorPoint X) (hx : 1 < schemeDivisorRamificationIdx f x) :
    x ∈ schemeDivisorNonUnramifiedLocus f := by
  intro hu
  have h := schemeDivisorRamificationIdx_eq_one_of_formallyUnramified f x hu
  omega

/-- The actual normalized divisor dynamics together with both stalk-defined
critical loci for every iterate. The model is valid in characteristic `p`
under generic separability; no prime-to-`p` degree condition is required
to construct it. -/
noncomputable def unnormalizedDynamicsOfFiniteDominantNormalSeparable
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] (hsep : IsGenericallySeparable f) :
    UnnormalizedDynamics (SchemeDivisorPoint X) where
  toDivisorDynamics := divisorDynamicsOfFiniteDominantNormalSeparable f hsep
  nonUnramifiedLocus := fun m =>
    schemeDivisorNonUnramifiedLocus (End.of f ^ m).asHom
  nonEtaleLocus := fun m =>
    schemeDivisorNonEtaleLocus (End.of f ^ m).asHom
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx := by
    intro m Q hidx
    have hidx' : 1 < schemeDivisorRamificationIdx (End.of f ^ m).asHom Q := by
      rw [← divisorDynamicsOfFiniteDominantNormal_iterateRamificationIdx
        f (schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale f
          ⟨genericPoint X,
            formallyEtale_stalkMap_genericPoint_of_finite_dominant_separable f hsep⟩)]
      exact hidx
    exact mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx
      (End.of f ^ m).asHom Q hidx'
  nonUnramifiedLocus_subset_nonEtaleLocus := fun m =>
    schemeDivisorNonUnramifiedLocus_subset_nonEtaleLocus (End.of f ^ m).asHom
  nonEtaleLocus_finite := by
    intro m
    exact schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale
      (End.of f ^ m).asHom
        ⟨genericPoint X,
          formallyEtale_stalkMap_genericPoint_of_finite_dominant_separable
            (End.of f ^ m).asHom (isGenericallySeparable_pow f hsep m)⟩
  nonUnramifiedLocus_tower := schemeDivisorNonUnramifiedLocus_tower f
  nonEtaleLocus_tower := by
    intro n Q hQ
    exact schemeDivisorNonEtaleLocus_tower f (coheight_apply_eq_one f) n Q hQ

/-- PCF on an integral normal scheme using the images of its actual
non-étale divisor stalks. This is the branch convention of `paper-p.tex`
for a normal variety in arbitrary characteristic. -/
def IsNormalNonEtalePCF
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] (hsep : IsGenericallySeparable f) : Prop :=
  (unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep).IsNonEtaleBranchPCF

/-- A fixed finite set containing the images of the actual non-étale
critical divisors of every positive iterate makes the normal map PCF,
in any characteristic. The geometric construction of that finite set is
the remaining content of the bounding or normalized blow-up argument. -/
theorem isNormalNonEtalePCF_of_uniform_iterate_support
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X] (hsep : IsGenericallySeparable f)
    (T : Set (SchemeDivisorPoint X)) (hT : T.Finite)
    (hbound : ∀ (m : ℕ), 1 ≤ m →
      ∀ Q ∈ schemeDivisorNonEtaleLocus (End.of f ^ m).asHom,
        ((unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep).step^[m] Q) ∈ T) :
    IsNormalNonEtalePCF f hsep := by
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep
  change D.IsNonEtaleBranchPCF
  apply D.isNonEtaleBranchPCF_of_nonEtaleBranch_subset hT
  intro m hm R hR
  obtain ⟨Q, hQ, rfl⟩ := hR
  exact hbound m hm Q hQ

#print axioms schemeDivisorRamificationIdx_eq_one_of_formallyUnramified
#print axioms mem_schemeDivisorNonUnramifiedLocus_of_one_lt_ramificationIdx
#print axioms unnormalizedDynamicsOfFiniteDominantNormalSeparable
#print axioms IsNormalNonEtalePCF
#print axioms isNormalNonEtalePCF_of_uniform_iterate_support

end Pcf
