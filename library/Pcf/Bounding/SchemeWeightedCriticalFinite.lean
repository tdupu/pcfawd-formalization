/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeFiniteResidueDelta
public import Mathlib.RingTheory.Unramified.LocalRing

/-! # Finiteness of the actual weighted critical divisor locus -/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

noncomputable section

theorem schemeResidue_isSeparable_of_formallyEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : (f.stalkMap x).hom.FormallyEtale) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  letI := (f.stalkMap x).hom.toAlgebra
  letI : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  letI : Algebra.FormallyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hx
  letI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    show IsLocalHom (f.stalkMap x).hom from inferInstance
  let Acan : Algebra (Y.residueField (f x)) (X.residueField x) :=
    inferInstanceAs (Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)))
  letI := Acan
  have hfu : Algebra.FormallyUnramified (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) := inferInstance
  have hsep : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) :=
    inferInstanceAs (Algebra.IsSeparable
      (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)))
  have heq : Acan = (f.residueFieldMap x).hom.toAlgebra := by
    apply Algebra.algebra_ext
    intro a
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    exact IsLocalRing.ResidueField.algebraMap_residue r
  rw [← heq]
  exact hsep

/-- A formally étale stalk has weighted local degree one: both its
ramification index and residue-field inseparable degree equal one. -/
theorem schemeDivisorDelta_eq_one_of_formallyEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (d : SchemeDivisorPoint X)
    (hd : (f.stalkMap d.1).hom.FormallyEtale) :
    schemeDivisorDelta f d = 1 := by
  letI := (f.residueFieldMap d.1).hom.toAlgebra
  letI : FiniteDimensional (Y.residueField (f d.1)) (X.residueField d.1) :=
    finiteResidueField_of_isFinite f d.1
  letI : Algebra.IsSeparable (Y.residueField (f d.1)) (X.residueField d.1) :=
    schemeResidue_isSeparable_of_formallyEtale f d.1 hd
  unfold schemeDivisorDelta
  rw [schemeDivisorRamificationIdx_eq_one_of_formallyEtale f d hd,
    Algebra.IsSeparable.finInsepDegree_eq]

/-- Every divisor critical for the paper's weighted degree lies in the
actual non-formally-étale stalk locus. -/
theorem schemeDivisorWeightedCritical_subset_nonEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d} ⊆
      schemeDivisorNonEtaleLocus f := by
  intro d hd hetale
  have heq := schemeDivisorDelta_eq_one_of_formallyEtale f d hetale
  simp only [Set.mem_ofPred_eq] at hd
  omega

/-- Finiteness of the non-étale divisor locus implies finiteness of
the actual weighted critical set. -/
theorem schemeDivisorWeightedCritical_finite_of_nonEtale_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (hfinite : (schemeDivisorNonEtaleLocus f).Finite) :
    {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d}.Finite :=
  hfinite.subset (schemeDivisorWeightedCritical_subset_nonEtale f)

/-- Generic formal étaleness and global Noetherianity give finitely
many divisors critical for the actual weighted degree. -/
theorem schemeDivisorWeightedCritical_finite_of_genericFormallyEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [IrreducibleSpace X] [NoetherianSpace X] [IsLocallyNoetherian Y]
    (hgeneric : (f.stalkMap (genericPoint X)).hom.FormallyEtale) :
    {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d}.Finite := by
  apply schemeDivisorWeightedCritical_finite_of_nonEtale_finite f
  exact schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale f
    ⟨genericPoint X, hgeneric⟩

/-- Separability of the actual extension of generic stalk fields for a
dominant map between two integral schemes. -/
def IsGenericallySeparableSchemeMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    [IsIntegral X] [IsIntegral Y] : Prop := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  exact Algebra.IsSeparable (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))

/-- For endomorphisms, the two-carrier generic separability predicate is
the existing characteristic-free self-map predicate. -/
theorem isGenericallySeparableSchemeMap_iff
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsDominant f] [IsIntegral X] :
    IsGenericallySeparableSchemeMap f ↔ IsGenericallySeparable f := Iff.rfl

/-- A finite dominant generically separable map between integral
schemes is formally étale at its generic point. -/
theorem formallyEtale_genericPoint_of_isGenericallySeparableSchemeMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    (hsep : IsGenericallySeparableSchemeMap f) :
    (f.stalkMap (genericPoint X)).hom.FormallyEtale := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : Algebra.IsSeparable (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) := hsep
  rw [RingHom.FormallyEtale]
  exact Algebra.FormallyEtale.of_isSeparable
    (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))

/-- A generically separable finite dominant map of integral schemes
has finitely many weighted critical divisors. -/
theorem schemeDivisorWeightedCritical_finite_of_genericallySeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsLocallyNoetherian Y]
    (hsep : IsGenericallySeparableSchemeMap f) :
    {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d}.Finite :=
  schemeDivisorWeightedCritical_finite_of_genericFormallyEtale f
    (formallyEtale_genericPoint_of_isGenericallySeparableSchemeMap f hsep)

/-- In a finite comparison square with separable comparison map,
the weighted comparison critical set is finite automatically. The
downstairs weighted branch finiteness remains an explicit input. -/
theorem schemeDeltaDynamics_isPCF_of_genericallySeparable_comparison
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [NoetherianSpace Y]
    (hcomm : g ≫ π = π ≫ f)
    (hsepπ : IsGenericallySeparableSchemeMap π)
    (hDbranch : (schemeDeltaDynamicsOfFiniteDominantNormal f).branch.Finite)
    (hE : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF :=
  schemeDeltaDynamics_isPCF_of_separable_comparison_of_isFinite f g π hcomm hDbranch
    (schemeDivisorWeightedCritical_finite_of_genericallySeparable π hsepπ) hE

/-- Generic separability of an actual finite normal self-map gives a
finite weighted branch set. -/
theorem schemeDeltaDynamics_branch_finite_of_genericallySeparable
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparableSchemeMap f) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).branch.Finite := by
  let D := schemeDeltaDynamicsOfFiniteDominantNormal f
  have hcrit : D.critical.Finite := by
    simpa only [D, DeltaDynamics.critical, schemeDeltaDynamics_delta] using
      (schemeDivisorWeightedCritical_finite_of_genericallySeparable f hsep)
  exact hcrit.image D.step

/-- The separable-comparison part of `lem:pcf-transfer-charp` at the
level of actual normal scheme divisor dynamics. Generic separability of
the downstairs map and comparison map supplies all geometric finiteness
and weighted local-degree conditions. -/
theorem schemeDeltaDynamics_isPCF_of_genericallySeparable_square
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (hcomm : g ≫ π = π ≫ f)
    (hsep_f : IsGenericallySeparableSchemeMap f)
    (hsep_π : IsGenericallySeparableSchemeMap π)
    (hE : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF :=
  schemeDeltaDynamics_isPCF_of_genericallySeparable_comparison f g π hcomm hsep_π
    (schemeDeltaDynamics_branch_finite_of_genericallySeparable f hsep_f) hE

#print axioms schemeResidue_isSeparable_of_formallyEtale
#print axioms schemeDivisorDelta_eq_one_of_formallyEtale
#print axioms schemeDivisorWeightedCritical_subset_nonEtale
#print axioms schemeDivisorWeightedCritical_finite_of_nonEtale_finite
#print axioms schemeDivisorWeightedCritical_finite_of_genericFormallyEtale
#print axioms IsGenericallySeparableSchemeMap
#print axioms isGenericallySeparableSchemeMap_iff
#print axioms formallyEtale_genericPoint_of_isGenericallySeparableSchemeMap
#print axioms schemeDivisorWeightedCritical_finite_of_genericallySeparable
#print axioms schemeDeltaDynamics_isPCF_of_genericallySeparable_comparison
#print axioms schemeDeltaDynamics_branch_finite_of_genericallySeparable
#print axioms schemeDeltaDynamics_isPCF_of_genericallySeparable_square

end

end Pcf
