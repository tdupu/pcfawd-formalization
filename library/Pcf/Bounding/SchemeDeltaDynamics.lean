/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.CharPCoverDescent
public import Pcf.Bounding.SchemeDynamics
public import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Weighted divisor dynamics from actual scheme maps

The positive-characteristic local weight is the ramification index of
the actual stalk map times the inseparable degree of the actual residue
field map. This connects the scheme normalization square to the weighted
`DeltaDynamics` used in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

/-- The paper's `δ_f(D)=e_f(D)[κ(D):κ(fD)]_insep`, constructed from the
actual stalk and residue-field maps of a scheme morphism.

`paper-p.tex` correspondence: Remark 2.3 (`rem:why-normalized`). -/
noncomputable def schemeDivisorDelta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : SchemeDivisorPoint X) : ℕ :=
  letI := (f.residueFieldMap d.1).hom.toAlgebra
  schemeDivisorRamificationIdx f d *
    Field.finInsepDegree (Y.residueField (f d.1)) (X.residueField d.1)

/-- The actual weighted local degree is positive when the residue
extension is finite. This hypothesis is automatic for finite-type
quasi-finite morphisms, but is kept explicit here. -/
theorem schemeDivisorDelta_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (d : SchemeDivisorPoint X)
    (hfinite : letI := (f.residueFieldMap d.1).hom.toAlgebra
      FiniteDimensional (Y.residueField (f d.1)) (X.residueField d.1)) :
    0 < schemeDivisorDelta f d := by
  letI := (f.residueFieldMap d.1).hom.toAlgebra
  letI : FiniteDimensional (Y.residueField (f d.1)) (X.residueField d.1) :=
    hfinite
  unfold schemeDivisorDelta
  exact Nat.mul_pos (schemeDivisorRamificationIdx_pos f d)
    (Nat.pos_of_ne_zero (NeZero.ne _))

set_option backward.isDefEq.respectTransparency false in
/-- The weighted local degrees of actual scheme maps satisfy the tower
law. Algebraicity of the intermediate residue extension is the exact
hypothesis of Mathlib's inseparable-degree tower theorem. -/
theorem schemeDivisorDelta_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (d : SchemeDivisorPoint X)
    (hAlg : letI := (g.residueFieldMap (f d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (Z.residueField (g (f d.1)))
        (Y.residueField (f d.1))) :
    schemeDivisorDelta (f ≫ g) d =
      schemeDivisorDelta g (d.mapFiniteDominantNormal f) *
        schemeDivisorDelta f d := by
  let K := Z.residueField (g (f d.1))
  let M := Y.residueField (f d.1)
  let L := X.residueField d.1
  letI : Algebra K M := (g.residueFieldMap (f d.1)).hom.toAlgebra
  letI : Algebra M L := (f.residueFieldMap d.1).hom.toAlgebra
  letI : Algebra K L := ((f ≫ g).residueFieldMap d.1).hom.toAlgebra
  letI : IsScalarTower K M L := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ g).residueFieldMap d.1).hom =
      (f.residueFieldMap d.1).hom.comp (g.residueFieldMap (f d.1)).hom
    rw [Scheme.residueFieldMap_comp]
    rfl)
  letI : Algebra.IsAlgebraic K M := hAlg
  have hres : Field.finInsepDegree K M * Field.finInsepDegree M L =
      Field.finInsepDegree K L :=
    Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K M L
  unfold schemeDivisorDelta
  rw [schemeDivisorRamificationIdx_comp f g d]
  change schemeDivisorRamificationIdx g (d.mapFiniteDominantNormal f) *
      schemeDivisorRamificationIdx f d * Field.finInsepDegree K L =
    schemeDivisorRamificationIdx g (d.mapFiniteDominantNormal f) *
      Field.finInsepDegree K M *
        (schemeDivisorRamificationIdx f d * Field.finInsepDegree M L)
  rw [← hres]
  ring

/-- A finite dominant normal self-map supplies a weighted divisor
dynamical system with the actual pushforward on divisors. -/
noncomputable def schemeDeltaDynamicsOfFiniteDominantNormal
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] :
    DeltaDynamics (SchemeDivisorPoint X) where
  step := fun d => d.mapFiniteDominantNormal f
  delta := schemeDivisorDelta f

@[simp] theorem schemeDeltaDynamics_step_val
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (d : SchemeDivisorPoint X) :
    ((schemeDeltaDynamicsOfFiniteDominantNormal f).step d).1 = f d.1 := rfl

@[simp] theorem schemeDeltaDynamics_delta
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (d : SchemeDivisorPoint X) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).delta d =
      schemeDivisorDelta f d := rfl

/-- A commuting square of finite dominant maps gives a commuting square
on codimension-one points, with the actual divisor pushforward maps. -/
theorem schemeDeltaDynamics_comparison_comm
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y) :
    (d.mapFiniteDominantNormal g).mapFiniteDominantNormal π =
      (d.mapFiniteDominantNormal π).mapFiniteDominantNormal f := by
  apply Subtype.ext
  exact congrArg (fun h : Y ⟶ X => h d.1) hcomm

/-- The paper's weighted equality `δ_f(πD) δ_π(D) =
δ_π(gD) δ_g(D)` follows from the actual commuting scheme square and
the stalk and residue-field tower laws. -/
theorem schemeDeltaDynamics_comparison_tower
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y)
    (hAlg_f : letI := (f.residueFieldMap (π d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (X.residueField (f (π d.1)))
        (X.residueField (π d.1)))
    (hAlg_π : letI := (π.residueFieldMap (g d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (X.residueField (π (g d.1)))
        (Y.residueField (g d.1))) :
    schemeDivisorDelta f (d.mapFiniteDominantNormal π) * schemeDivisorDelta π d =
      schemeDivisorDelta π (d.mapFiniteDominantNormal g) * schemeDivisorDelta g d := by
  have hleft := schemeDivisorDelta_comp π f d hAlg_f
  have hright := schemeDivisorDelta_comp g π d hAlg_π
  rw [hcomm] at hright
  exact hleft.symm.trans hright

/-- The divisor-step hypothesis of `DeltaDynamics` descent is supplied by
the genuine finite scheme square. -/
theorem schemeDeltaDynamics_step_comparison
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y) :
    (d.mapFiniteDominantNormal g).mapFiniteDominantNormal π =
      (schemeDeltaDynamicsOfFiniteDominantNormal f).step
        (d.mapFiniteDominantNormal π) :=
  schemeDeltaDynamics_comparison_comm f g π hcomm d

/-- The weighted-degree hypothesis of `DeltaDynamics` descent is
supplied by the genuine finite scheme square. -/
theorem schemeDeltaDynamics_delta_comparison
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f) (d : SchemeDivisorPoint Y)
    (hAlg_f : letI := (f.residueFieldMap (π d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (X.residueField (f (π d.1)))
        (X.residueField (π d.1)))
    (hAlg_π : letI := (π.residueFieldMap (g d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (X.residueField (π (g d.1)))
        (Y.residueField (g d.1))) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).delta
        (d.mapFiniteDominantNormal π) * schemeDivisorDelta π d =
      schemeDivisorDelta π ((schemeDeltaDynamicsOfFiniteDominantNormal g).step d) *
        (schemeDeltaDynamicsOfFiniteDominantNormal g).delta d :=
  schemeDeltaDynamics_comparison_tower f g π hcomm d hAlg_f hAlg_π

/-- The separable-comparison descent theorem applied to actual finite
scheme maps. The remaining inputs are geometric finiteness and positivity
conditions on their codimension-one ramification and residue data. -/
theorem schemeDeltaDynamics_isPCF_of_separable_comparison
    {X Y : Scheme.{u}} (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    (hcomm : g ≫ π = π ≫ f)
    (hAlg_f : ∀ d : SchemeDivisorPoint Y,
      letI := (f.residueFieldMap (π d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (X.residueField (f (π d.1)))
        (X.residueField (π d.1)))
    (hAlg_π : ∀ d : SchemeDivisorPoint Y,
      letI := (π.residueFieldMap (g d.1)).hom.toAlgebra
      Algebra.IsAlgebraic (X.residueField (π (g d.1)))
        (Y.residueField (g d.1)))
    (hDpos : ∀ d, 0 < schemeDivisorDelta f d)
    (hEpos : ∀ d, 0 < schemeDivisorDelta g d)
    (hπpos : ∀ d, 0 < schemeDivisorDelta π d)
    (hDbranch : (schemeDeltaDynamicsOfFiniteDominantNormal f).branch.Finite)
    (hπcritical : {d : SchemeDivisorPoint Y | 1 < schemeDivisorDelta π d}.Finite)
    (hE : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  let D := schemeDeltaDynamicsOfFiniteDominantNormal f
  let E := schemeDeltaDynamicsOfFiniteDominantNormal g
  let ρ : SchemeDivisorPoint Y → SchemeDivisorPoint X :=
    fun d => d.mapFiniteDominantNormal π
  refine D.isPCF_of_separable_comparison E ρ
    (SchemeDivisorPoint.mapFiniteDominantNormal_surjective π)
    (SchemeDivisorPoint.mapFiniteDominantNormal_finite_fiber π)
    ?_ (schemeDivisorDelta π) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro d
    exact schemeDeltaDynamics_step_comparison f g π hcomm d
  · exact hDpos
  · exact hEpos
  · exact hπpos
  · exact SchemeDivisorPoint.mapFiniteDominantNormal_surjective f
  · exact SchemeDivisorPoint.mapFiniteDominantNormal_surjective g
  · exact hDbranch
  · exact hπcritical
  · intro d
    exact schemeDeltaDynamics_delta_comparison f g π hcomm d (hAlg_f d) (hAlg_π d)
  · exact hE

#print axioms schemeDivisorDelta
#print axioms schemeDivisorDelta_pos
#print axioms schemeDivisorDelta_comp
#print axioms schemeDeltaDynamicsOfFiniteDominantNormal
#print axioms schemeDeltaDynamics_comparison_comm
#print axioms schemeDeltaDynamics_comparison_tower
#print axioms schemeDeltaDynamics_step_comparison
#print axioms schemeDeltaDynamics_delta_comparison
#print axioms schemeDeltaDynamics_isPCF_of_separable_comparison

end Pcf
