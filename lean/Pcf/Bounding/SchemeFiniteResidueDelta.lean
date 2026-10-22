/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaDynamics
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Finite residue extensions and weighted divisor degree -/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace Pcf

set_option linter.style.haveILetI false

/-- The residue field extension at a point of a finite scheme morphism is finite. -/
theorem finiteResidueField_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (Y.residueField (f x)) (X.residueField x) := by
  letI := (f.stalkMap x).hom.toAlgebra
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.quasiFiniteAt x)
  letI : Algebra (Y.presheaf.stalk (f x)) (X.residueField x) :=
    IsLocalRing.ResidueField.algebra _
  letI : Algebra (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    IsLocalRing.ResidueField.algebra _
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    IsLocalRing.ResidueField.algebra _
  letI : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.QuasiFinite (X.presheaf.stalk x) (X.residueField x) := by
    haveI : Module.Finite (X.presheaf.stalk x) (X.residueField x) :=
      Module.Finite.of_surjective
        (Algebra.linearMap (X.presheaf.stalk x) (X.residueField x))
        IsLocalRing.residue_surjective
    infer_instance
  letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hq : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.residueField x) :=
    Algebra.QuasiFinite.trans _ (X.presheaf.stalk x) _
  letI : IsScalarTower (Y.presheaf.stalk (f x)) (Y.residueField (f x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' (by
    change (IsLocalRing.residue (X.presheaf.stalk x)).comp (f.stalkMap x).hom =
      (IsLocalRing.ResidueField.map (f.stalkMap x).hom).comp
        (IsLocalRing.residue (Y.presheaf.stalk (f x)))
    exact (IsLocalRing.ResidueField.map_comp_residue (f.stalkMap x).hom).symm)
  haveI : Algebra.QuasiFinite (Y.residueField (f x)) (X.residueField x) :=
    Algebra.QuasiFinite.of_restrictScalars (Y.presheaf.stalk (f x)) _ _
  exact Module.Finite.of_quasiFinite

/-- Weighted divisor degree of a finite map is positive without a
separate residue-field finiteness premise. -/
theorem schemeDivisorDelta_pos_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (d : SchemeDivisorPoint X) :
    0 < schemeDivisorDelta f d :=
  schemeDivisorDelta_pos f d (finiteResidueField_of_isFinite f d.1)

/-- The weighted degree tower law for finite scheme morphisms, with
the intermediate residue-field algebraicity obtained from finiteness. -/
theorem schemeDivisorDelta_comp_of_isFinite
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X) :
    schemeDivisorDelta (f ≫ g) d =
      schemeDivisorDelta g (d.mapFiniteDominantNormal f) *
        schemeDivisorDelta f d := by
  apply schemeDivisorDelta_comp f g d
  letI := (g.residueFieldMap (f d.1)).hom.toAlgebra
  letI : FiniteDimensional (Z.residueField (g (f d.1)))
      (Y.residueField (f d.1)) := finiteResidueField_of_isFinite g (f d.1)
  infer_instance

/-- The weighted local-degree identity in an actual commuting square of
finite dominant normal scheme maps now has no residue-field hypotheses. -/
theorem schemeDeltaDynamics_comparison_tower_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y) :
    schemeDivisorDelta f (d.mapFiniteDominantNormal π) * schemeDivisorDelta π d =
      schemeDivisorDelta π (d.mapFiniteDominantNormal g) * schemeDivisorDelta g d := by
  have hleft := schemeDivisorDelta_comp_of_isFinite π f d
  have hright := schemeDivisorDelta_comp_of_isFinite g π d
  rw [hcomm] at hright
  exact hleft.symm.trans hright

/-- Scheme-level PCF descent for a finite comparison square: residue
extensions, local-degree positivity, divisor surjectivity, finite fibers,
and the weighted tower law follow from finite morphisms. Only finiteness
of the weighted branch and comparison critical sets remains explicit. -/
theorem schemeDeltaDynamics_isPCF_of_separable_comparison_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f)
    (hDbranch : (schemeDeltaDynamicsOfFiniteDominantNormal f).branch.Finite)
    (hπcritical : {d : SchemeDivisorPoint Y | 1 < schemeDivisorDelta π d}.Finite)
    (hE : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  apply schemeDeltaDynamics_isPCF_of_separable_comparison f g π hcomm
  · intro d
    letI := (f.residueFieldMap (π d.1)).hom.toAlgebra
    letI : FiniteDimensional (X.residueField (f (π d.1)))
        (X.residueField (π d.1)) := finiteResidueField_of_isFinite f (π d.1)
    infer_instance
  · intro d
    letI := (π.residueFieldMap (g d.1)).hom.toAlgebra
    letI : FiniteDimensional (X.residueField (π (g d.1)))
        (Y.residueField (g d.1)) := finiteResidueField_of_isFinite π (g d.1)
    infer_instance
  · exact schemeDivisorDelta_pos_of_isFinite f
  · exact schemeDivisorDelta_pos_of_isFinite g
  · exact schemeDivisorDelta_pos_of_isFinite π
  · exact hDbranch
  · exact hπcritical
  · exact hE

#print axioms finiteResidueField_of_isFinite
#print axioms schemeDivisorDelta_pos_of_isFinite
#print axioms schemeDivisorDelta_comp_of_isFinite
#print axioms schemeDeltaDynamics_comparison_tower_of_isFinite
#print axioms schemeDeltaDynamics_isPCF_of_separable_comparison_of_isFinite

end Pcf
