/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPTower.Normalized
public import Pcf.Bounding.PaperPIteration
public import Pcf.Bounding.SchemePrimeToPIteration

/-!
# The tower of iterates (`paper-p.tex`, l. 1773–1780)

The iterates of a finite surjective separable `k`-morphism `f : X → X` form
the tower with `X_n = X` and `h_n = f`. This file constructs that tower as an
actual `PaperPTower.Tower`, identifies its composites with the categorical
iterates, and proves the two claims of l. 1773–1780: the tower is PCF exactly
when `f` is, and it has monodromy not divisible by `p` when `f` has.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The tower of iterates of a finite surjective separable `k`-morphism. -/
def iterateTower (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [CompactSpace X] [IsSeparated s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hfs : f ≫ s = s) (hsurj : Function.Surjective f)
    (hsep : IsGenericallySeparable f) : PaperPTower.Tower k where
  X := fun _ => X
  integral := fun _ => inferInstance
  base := fun _ => s
  finiteType := fun _ => inferInstance
  compact := fun _ => inferInstance
  separated := fun _ => inferInstance
  h := fun _ => f
  over := fun _ => hfs
  finite := fun _ => inferInstance
  surjective := fun _ => hsurj
  dominant := fun _ => inferInstance
  separable := fun _ => hsep

section
variable (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [CompactSpace X] [IsSeparated s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hfs : f ≫ s = s) (hsurj : Function.Surjective f)
    (hsep : IsGenericallySeparable f)

/-- The composites `fₙ` of the tower of iterates are the iterates `fⁿ`. -/
theorem iterateTower_composite (n : ℕ) :
    (iterateTower k s f hfs hsurj hsep).composite n = (End.of f ^ n).asHom := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [PaperPTower.Tower.composite_succ, ih, pow_succ, End.mul_asHom]
      rfl

private theorem weightedBranchPointSet_congr {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap Y)] [IsFinite (Palomar.normalizationMap Z)]
    (a b : Y ⟶ Z) (h : a = b) {_ : IsFinite a} {_ : IsDominant a}
    {_ : IsFinite b} {_ : IsDominant b} :
    weightedBranchPointSet a = weightedBranchPointSet b := by
  subst h
  rfl

private theorem isPrimeToPMonodromyMap_congr (p : ℕ) {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z]
    (a b : Y ⟶ Z) (h : a = b) {_ : IsFinite a} {_ : IsDominant a}
    {_ : IsFinite b} {_ : IsDominant b} :
    IsPrimeToPMonodromyMap p a ↔ IsPrimeToPMonodromyMap p b := by
  subst h
  rfl

/-- **`paper-p.tex`, l. 1773–1778.** The tower of iterates of `f` is PCF
(normalized weighted branch divisors counted on the base) exactly when `f`
is separable normalized PCF. -/
theorem iterateTower_isNormalizedPCF_iff [IsLocallyNoetherian X] [NoetherianSpace X] :
    (iterateTower k s f hfs hsurj hsep).IsNormalizedPCF ↔
      IsSeparableNormalizedPCF k s f := by
  letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
  have hunion : (⋃ n, (iterateTower k s f hfs hsurj hsep).normalizedBranchGenericPoints
      (n + 1)) = weightedPostcriticalPointSet f := by
    have hn : ∀ n, (iterateTower k s f hfs hsurj hsep).normalizedBranchGenericPoints (n + 1) =
        ⋃ i ∈ Set.Iio (n + 1), (f : X → X)^[i] '' weightedBranchPointSet f := by
      intro n
      haveI := isFinite_end_pow f (n + 1)
      haveI := isDominant_end_pow f (n + 1)
      rw [PaperPTower.Tower.normalizedBranchGenericPoints_eq_weighted]
      rw [← weightedBranchPointSet_pow_eq_iUnion f (n + 1)]
      exact weightedBranchPointSet_congr _ _ (iterateTower_composite k s f hfs hsurj hsep _)
    rw [Set.iUnion_congr hn]
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun n => Set.iUnion₂_subset fun i _ =>
        Set.subset_iUnion (fun j => (f : X → X)^[j] '' weightedBranchPointSet f) i
    · exact Set.iUnion_subset fun i =>
        (Set.subset_biUnion_of_mem (u := fun j => (f : X → X)^[j] '' weightedBranchPointSet f)
          (show i ∈ Set.Iio (i + 1) from Nat.lt_succ_self i)).trans
          (Set.subset_iUnion (fun n => ⋃ j ∈ Set.Iio (n + 1),
            (f : X → X)^[j] '' weightedBranchPointSet f) i)
  rw [isSeparableNormalizedPCF_iff_downstairs,
    isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite]
  change (⋃ n, (iterateTower k s f hfs hsurj hsep).normalizedBranchGenericPoints
      (n + 1)).Finite ↔ _
  rw [hunion]
  exact ⟨fun h => ⟨hsep, h⟩, fun h => h.2⟩

/-- **`paper-p.tex`, l. 1778–1779.** The tower of iterates has monodromy not
divisible by `p` when `f` has prime-to-`p` monodromy. -/
theorem iterateTower_monodromyNotDivisibleBy (p : ℕ)
    (hmono : IsPrimeToPMonodromyMap p f) :
    (iterateTower k s f hfs hsurj hsep).MonodromyNotDivisibleBy p := by
  unfold PaperPTower.Tower.MonodromyNotDivisibleBy
  split_ifs
  intro n
  haveI := isFinite_end_pow f (n + 1)
  haveI := isDominant_end_pow f (n + 1)
  exact (isPrimeToPMonodromyMap_congr p _ _
      (iterateTower_composite k s f hfs hsurj hsep (n + 1))).mpr
      (isPrimeToPMonodromyMap_pow_succ p f hmono n)

end

#print axioms iterateTower
#print axioms iterateTower_composite
#print axioms iterateTower_isNormalizedPCF_iff
#print axioms iterateTower_monodromyNotDivisibleBy

end

end Pcf
