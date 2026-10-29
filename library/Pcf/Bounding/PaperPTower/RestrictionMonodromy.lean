/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPTower.Normalized
public import Pcf.Bounding.AllCentrePointClosureSeparable
public import Pcf.Bounding.FieldExtensionNormalizationFieldEquiv

/-!
# Restricting composites of a tower to integral closed subvarieties

This proves the monodromy and generic-separability part of
`paper-p.tex`, Theorem `thm:tower-restrict`, for the actual maps between
the reduced point-closure subschemes. The uniform branch support of these
restrictions is a separate geometric obligation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace Pcf.PaperPTower
universe u
noncomputable section
set_option linter.style.haveILetI false

/-- Prime-to-characteristic monodromy for the restriction to two
specified reduced point closures, when the ambient map carries one
generic point to the other. -/
theorem pointClosureMap_primeToPMonodromy_of_apply_eq
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) (y : Y) (hxy : f x = y) :
    let g := pointClosureSubschemeMap f x y hxy
    letI : IsFinite g := pointClosureSubschemeMap_isFinite f x y hxy
    letI : IsDominant g := pointClosureSubschemeMap_isDominant f x y hxy
    IsPrimeToPMonodromyMap p g := by
  subst y
  exact finiteType_pointClosureMap_primeToPMonodromy
    p hp k f s hmono x

/-- A generically separable composite has generically separable first
factor: separability descends along the intermediate function field. -/
theorem genericallySeparable_left_of_comp
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g]
    (hsep : IsGenericallySeparableSchemeMap (f ≫ g)) :
    IsGenericallySeparableSchemeMap f := by
  letI : Algebra Z.functionField Y.functionField :=
    (schemeGenericFieldHom g).toAlgebra
  letI : Algebra Y.functionField X.functionField :=
    (schemeGenericFieldHom f).toAlgebra
  letI : Algebra Z.functionField X.functionField :=
    (schemeGenericFieldHom (f ≫ g)).toAlgebra
  letI : IsScalarTower Z.functionField Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq' (by
      change schemeGenericFieldHom (f ≫ g) =
        (schemeGenericFieldHom f).comp (schemeGenericFieldHom g)
      exact schemeGenericFieldHom_comp f g)
  letI : Algebra.IsSeparable Z.functionField X.functionField :=
    (schemeGenericFieldHom_isSeparable_iff (f ≫ g)).mpr hsep
  exact (schemeGenericFieldHom_isSeparable_iff f).mp
    (Algebra.isSeparable_tower_top_of_isSeparable
      Z.functionField Y.functionField X.functionField)

/-- Weighted branch support is invariant under equality of the actual
scheme morphism, independently of the particular finiteness witnesses. -/
theorem weightedBranchPointSet_congr
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f g : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsFinite g] [IsDominant g] (h : f = g) :
    weightedBranchPointSet f = weightedBranchPointSet g := by
  subst g
  rfl

/-- A finite dominant morphism of integral schemes over a
characteristic-zero field is generically separable. -/
theorem genericallySeparable_of_finite_charZero
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] :
    IsGenericallySeparableSchemeMap f := by
  letI : CharZero Y.functionField :=
    charZero_stalk_of_field k s (genericPoint Y)
  letI : Algebra Y.functionField X.functionField :=
    (schemeGenericFieldHom f).toAlgebra
  letI : FiniteDimensional Y.functionField X.functionField :=
    schemeGenericFieldHom_finite f
  exact (schemeGenericFieldHom_isSeparable_iff f).mp inferInstance

/-- Compatible generic points of the integral closed subvarieties
`Aₙ ⊆ Xₙ` in Theorem `thm:tower-restrict`. -/
structure CompatibleCentres {k : Type u} [Field k] (T : Tower k) where
  point : ∀ n, T.X n
  step : ∀ n, T.h n (point (n + 1)) = point n

namespace CompatibleCentres
variable {k : Type u} [Field k] {T : Tower k} (C : CompatibleCentres T)

/-- The composite `fₙ` sends the generic point of `Aₙ` to that of `A₀`. -/
theorem composite_point (n : ℕ) : T.composite n (C.point n) = C.point 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change T.composite n (T.h n (C.point (n + 1))) = C.point 0
      rw [C.step n]
      exact ih

/-- The actual reduced integral closed subvariety `Aₙ`. -/
abbrev level (n : ℕ) : Scheme.{u} := (pointClosureIdealSheaf (C.point n)).subscheme

instance level_integral (n : ℕ) : IsIntegral (C.level n) :=
  Palomar.pointClosure_isIntegral (C.point n)

instance level_normalization_finite (n : ℕ) :
    IsFinite (Palomar.normalizationMap (C.level n)) := by
  let s : C.level n ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf (C.point n)).subschemeι ≫ T.base n
  letI : LocallyOfFiniteType s := by infer_instance
  exact schemeGlobalNormalizationMap_isFinite (C.level n) k s

/-- Restriction of the transition `hₙ` to `Aₙ₊₁ → Aₙ`. -/
def restrictedStep (n : ℕ) : C.level (n + 1) ⟶ C.level n :=
  pointClosureSubschemeMap (T.h n) (C.point (n + 1)) (C.point n) (C.step n)

/-- Restriction of `fₙ` to `Aₙ → A₀`. -/
def restrictedComposite (n : ℕ) : C.level n ⟶ C.level 0 :=
  pointClosureSubschemeMap (T.composite n) (C.point n) (C.point 0)
    (C.composite_point n)

instance restrictedStep_finite (n : ℕ) : IsFinite (C.restrictedStep n) :=
  pointClosureSubschemeMap_isFinite (T.h n) (C.point (n + 1))
    (C.point n) (C.step n)

instance restrictedStep_dominant (n : ℕ) : IsDominant (C.restrictedStep n) :=
  pointClosureSubschemeMap_isDominant (T.h n) (C.point (n + 1))
    (C.point n) (C.step n)

theorem restrictedStep_surjective (n : ℕ) :
    Function.Surjective (C.restrictedStep n) :=
  pointClosureSubschemeMap_surjective (T.h n) (C.point (n + 1))
    (C.point n) (C.step n)

instance restrictedComposite_finite (n : ℕ) :
    IsFinite (C.restrictedComposite n) :=
  pointClosureSubschemeMap_isFinite (T.composite n) (C.point n)
    (C.point 0) (C.composite_point n)

instance restrictedComposite_dominant (n : ℕ) :
    IsDominant (C.restrictedComposite n) :=
  pointClosureSubschemeMap_isDominant (T.composite n) (C.point n)
    (C.point 0) (C.composite_point n)

/-- The actual restriction of each composite is the composite of the
restricted transitions. -/
theorem restrictedComposite_succ (n : ℕ) :
    C.restrictedComposite (n + 1) =
      C.restrictedStep n ≫ C.restrictedComposite n := by
  unfold restrictedComposite restrictedStep level
  simpa only [Tower.composite_succ] using
    (pointClosureSubschemeMap_comp (T.h n) (T.composite n)
      (C.point (n + 1)) (C.point n) (C.point 0)
      (C.step n) (C.composite_point n)
      (by simpa only [Tower.composite_succ] using C.composite_point (n + 1))).symm

theorem restrictedComposite_zero : C.restrictedComposite 0 = 𝟙 (C.level 0) := by
  exact pointClosureSubschemeMap_id (C.point 0) (C.composite_point 0)

/-- The prime-to-characteristic monodromy hypothesis on every ambient
composite passes to its actual integral closed-subvariety restriction. -/
theorem restrictedComposite_primeToPMonodromy
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p) (n : ℕ) :
    IsPrimeToPMonodromyMap p (C.restrictedComposite (n + 1)) := by
  have hmono' : ∀ m, IsPrimeToPMonodromyMap p (T.composite (m + 1)) := by
    simpa [Tower.MonodromyNotDivisibleBy, hp.ne_zero] using hmono
  exact pointClosureMap_primeToPMonodromy_of_apply_eq
    p hp k (T.composite (n + 1)) (T.base 0)
    (hmono' n) (C.point (n + 1)) (C.point 0) (C.composite_point (n + 1))

/-- The restricted composites are generically separable; this follows
from their inherited prime-to-characteristic monodromy. -/
theorem restrictedComposite_genericallySeparable
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p) (n : ℕ) :
    IsGenericallySeparableSchemeMap (C.restrictedComposite (n + 1)) :=
  isGenericallySeparableSchemeMap_of_primeToPMonodromyMap p
    (C.restrictedComposite (n + 1))
    (C.restrictedComposite_primeToPMonodromy p hp hmono n)

/-- Every transition of the restricted tower is separable in positive
characteristic, because it is the first factor of a separable restricted
composite. -/
theorem restrictedStep_genericallySeparable
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p) (n : ℕ) :
    IsGenericallySeparableSchemeMap (C.restrictedStep n) := by
  have hsep : IsGenericallySeparableSchemeMap
      (C.restrictedStep n ≫ C.restrictedComposite n) := by
    simpa only [← C.restrictedComposite_succ n] using
      C.restrictedComposite_genericallySeparable p hp hmono n
  exact genericallySeparable_left_of_comp (C.restrictedStep n)
    (C.restrictedComposite n) hsep

/-- The compatible integral closed subvarieties form an actual tower of
finite surjective separable morphisms in positive characteristic. The PCF
clause of Theorem `thm:tower-restrict` remains the uniform branch bound. -/
abbrev restrictedTower
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p) : Tower k where
  X := C.level
  integral := C.level_integral
  base n := (pointClosureIdealSheaf (C.point n)).subschemeι ≫ T.base n
  finiteType n := by infer_instance
  compact n := by
    letI : CompactSpace (T.X n) := T.compact n
    exact QuasiCompact.compactSpace_of_compactSpace
      (pointClosureIdealSheaf (C.point n)).subschemeι
  separated n := by infer_instance
  h := C.restrictedStep
  over n := by
    rw [← Category.assoc, restrictedStep, pointClosureSubschemeMap_subschemeι]
    rw [Category.assoc, T.over n]
  finite := C.restrictedStep_finite
  surjective := C.restrictedStep_surjective
  dominant := C.restrictedStep_dominant
  separable n := C.restrictedStep_genericallySeparable p hp hmono n

/-- The same restricted tower in characteristic zero, where every finite
extension of function fields is separable and no monodromy input is needed. -/
abbrev restrictedTowerCharZero [CharZero k] : Tower k where
  X := C.level
  integral := C.level_integral
  base n := (pointClosureIdealSheaf (C.point n)).subschemeι ≫ T.base n
  finiteType n := by infer_instance
  compact n := by
    letI : CompactSpace (T.X n) := T.compact n
    exact QuasiCompact.compactSpace_of_compactSpace
      (pointClosureIdealSheaf (C.point n)).subschemeι
  separated n := by infer_instance
  h := C.restrictedStep
  over n := by
    rw [← Category.assoc, restrictedStep, pointClosureSubschemeMap_subschemeι]
    rw [Category.assoc, T.over n]
  finite := C.restrictedStep_finite
  surjective := C.restrictedStep_surjective
  dominant := C.restrictedStep_dominant
  separable n := genericallySeparable_of_finite_charZero k
    ((pointClosureIdealSheaf (C.point n)).subschemeι ≫ T.base n)
    (C.restrictedStep n)

/-- The restricted tower's composite is the actual restriction of the
original ambient composite. -/
theorem restrictedTower_composite_eq
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p) (n : ℕ) :
    (C.restrictedTower p hp hmono).composite n = C.restrictedComposite n := by
  induction n with
  | zero =>
      simpa only [Tower.composite_zero] using C.restrictedComposite_zero.symm
  | succ n ih =>
      change C.restrictedStep n ≫
        (C.restrictedTower p hp hmono).composite n = C.restrictedComposite (n + 1)
      rw [ih]
      exact (C.restrictedComposite_succ n).symm

theorem restrictedTowerCharZero_composite_eq [CharZero k] (n : ℕ) :
    C.restrictedTowerCharZero.composite n = C.restrictedComposite n := by
  induction n with
  | zero =>
      simpa only [Tower.composite_zero] using C.restrictedComposite_zero.symm
  | succ n ih =>
      change C.restrictedStep n ≫ C.restrictedTowerCharZero.composite n =
        C.restrictedComposite (n + 1)
      rw [ih]
      exact (C.restrictedComposite_succ n).symm

/-- The restricted tower retains the manuscript's prime-to-characteristic
monodromy condition for every positive composite. -/
theorem restrictedTower_monodromyNotDivisibleBy
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p) :
    (C.restrictedTower p hp hmono).MonodromyNotDivisibleBy p := by
  simp only [Tower.MonodromyNotDivisibleBy, hp.ne_zero, ↓reduceIte]
  intro n
  simpa only [C.restrictedTower_composite_eq p hp hmono] using
    C.restrictedComposite_primeToPMonodromy p hp hmono n

/-- Source-facing reduction of the PCF clause of `thm:tower-restrict` to
the uniform branch bound for the actual restricted composites. That
bound is the separate normalized blow-up argument in the manuscript. -/
theorem restrictedTower_isNormalizedPCF_of_uniform_branch_bound
    (p : ℕ) (hp : p.Prime) [CharP k p]
    [IsNormalScheme (T.X 0)]
    (hmono : T.MonodromyNotDivisibleBy p)
    (hbound : ∃ S : Set (C.level 0), S.Finite ∧
      ∀ n, weightedBranchPointSet (C.restrictedComposite (n + 1)) ⊆ S) :
    (C.restrictedTower p hp hmono).IsNormalizedPCF := by
  apply (Tower.isNormalizedPCF_iff_uniform_support _).mpr
  obtain ⟨S, hS, hbound⟩ := hbound
  refine ⟨S, hS, ?_⟩
  intro n
  have heq : weightedBranchPointSet
      ((C.restrictedTower p hp hmono).composite (n + 1)) =
        weightedBranchPointSet (C.restrictedComposite (n + 1)) :=
    weightedBranchPointSet_congr _ _
      (C.restrictedTower_composite_eq p hp hmono (n + 1))
  simpa only [Tower.normalizedBranchGenericPoints_eq_weighted, heq] using hbound n

/-- Characteristic-zero form of the same exact PCF reduction for
unrelated restricted composites. -/
theorem restrictedTowerCharZero_isNormalizedPCF_of_uniform_branch_bound
    [CharZero k]
    (hbound : ∃ S : Set (C.level 0), S.Finite ∧
      ∀ n, weightedBranchPointSet (C.restrictedComposite (n + 1)) ⊆ S) :
    C.restrictedTowerCharZero.IsNormalizedPCF := by
  apply (Tower.isNormalizedPCF_iff_uniform_support _).mpr
  obtain ⟨S, hS, hbound⟩ := hbound
  refine ⟨S, hS, ?_⟩
  intro n
  have heq : weightedBranchPointSet (C.restrictedTowerCharZero.composite (n + 1)) =
      weightedBranchPointSet (C.restrictedComposite (n + 1)) :=
    weightedBranchPointSet_congr _ _ (C.restrictedTowerCharZero_composite_eq (n + 1))
  simpa only [Tower.normalizedBranchGenericPoints_eq_weighted, heq] using hbound n

/-- The finite exceptional-component assembly in the last paragraph of
`thm:tower-restrict`: if each blow-up component `j` supplies a finite bad
set and each restricted composite is controlled by one such component,
then one finite set controls all unrelated composites. The geometric
construction of the bad sets is a separate obligation. -/
theorem restrictedComposite_uniform_bound_of_finite_exceptional_family
    (J : Type*) [Finite J]
    (bad : J → Set (C.level 0)) (hbadFinite : ∀ j, (bad j).Finite)
    (j : ℕ → J)
    (hbound : ∀ n, weightedBranchPointSet (C.restrictedComposite (n + 1)) ⊆
      bad (j n)) :
    ∃ S : Set (C.level 0), S.Finite ∧
      ∀ n, weightedBranchPointSet (C.restrictedComposite (n + 1)) ⊆ S := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  refine ⟨⋃ j, bad j, Set.finite_iUnion hbadFinite, ?_⟩
  intro n
  exact (hbound n).trans (Set.subset_iUnion bad (j n))

#print axioms restrictedComposite_succ
#print axioms restrictedComposite_primeToPMonodromy
#print axioms restrictedComposite_genericallySeparable
#print axioms restrictedStep_genericallySeparable
#print axioms restrictedTower
#print axioms restrictedTower_composite_eq
#print axioms restrictedTower_monodromyNotDivisibleBy
#print axioms restrictedTower_isNormalizedPCF_of_uniform_branch_bound
#print axioms restrictedTowerCharZero
#print axioms restrictedTowerCharZero_isNormalizedPCF_of_uniform_branch_bound
#print axioms restrictedComposite_uniform_bound_of_finite_exceptional_family

end CompatibleCentres
end
end Pcf.PaperPTower
