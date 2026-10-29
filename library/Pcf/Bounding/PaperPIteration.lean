/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Pcf.Bounding.SeparableNormalizedPCFIteration

/-!
# Iteration of the `paper-p.tex` postcritical condition

This states clause (4) of Proposition `prop:iterates` for the manuscript's
weighted normalized postcritical divisors counted on the original scheme.
The map is generically separable, as required by the source proposition.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- `paper-p.tex`, Proposition `prop:iterates`(4): for every positive `m`,
postcritical finiteness of a finite surjective separable map is equivalent to
postcritical finiteness of its `m`-th iterate. Both sides count weighted
normalized branch divisors on the original scheme.

`paper-p.tex` correspondence: Proposition 5.3 (`prop:iterates`), item (4) of Proposition 5.3
(`item:pcf-iterate`). -/
theorem isWeightedNormalizedPCFDownstairs_pow_iff_of_genericallySeparable
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparable f) (m : ℕ) (hm : 1 ≤ m) :
    IsWeightedNormalizedPCFDownstairs k s (End.of f ^ m).asHom ↔
      IsWeightedNormalizedPCFDownstairs k s f := by
  have hsepPow : IsGenericallySeparable (End.of f ^ m).asHom :=
    isGenericallySeparable_pow f hsep m
  have h := isSeparableNormalizedPCF_pow_iff k s f m hm
  rw [isSeparableNormalizedPCF_iff_downstairs k s (End.of f ^ m).asHom,
    isSeparableNormalizedPCF_iff_downstairs k s f] at h
  exact ⟨fun hpcf => (h.mp ⟨hsepPow, hpcf⟩).2,
    fun hpcf => (h.mpr ⟨hsep, hpcf⟩).2⟩

/-- `paper-p.tex`, Proposition `prop:iterates`(1), induction step for the
underlying closed weighted branch locus. The corresponding finite-union
formula follows by iterating this identity. -/
theorem weightedBranchLocus_pow_succ
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (m : ℕ) :
    weightedBranchLocus (End.of f ^ (m + 1)).asHom =
      weightedBranchLocus f ∪ f '' weightedBranchLocus (End.of f ^ m).asHom := by
  calc
    weightedBranchLocus (End.of f ^ (m + 1)).asHom =
        weightedBranchLocus ((End.of f ^ m).asHom ≫ f) := by
          congr 1
          simp only [pow_succ', End.mul_asHom]
    _ = _ := weightedBranchLocus_comp (End.of f ^ m).asHom f

/-- The same induction step for the generic points of the branch divisors. -/
theorem weightedBranchPointSet_pow_succ
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (m : ℕ) :
    weightedBranchPointSet (End.of f ^ (m + 1)).asHom =
      weightedBranchPointSet f ∪ f '' weightedBranchPointSet (End.of f ^ m).asHom := by
  calc
    weightedBranchPointSet (End.of f ^ (m + 1)).asHom =
        weightedBranchPointSet ((End.of f ^ m).asHom ≫ f) := by
          congr 1
          simp only [pow_succ', End.mul_asHom]
    _ = _ := weightedBranchPointSet_comp (End.of f ^ m).asHom f

/-- The identity morphism has no weighted branch generic points. -/
theorem weightedBranchPointSet_id
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)] :
    weightedBranchPointSet (𝟙 X) = ∅ := by
  simp [weightedBranchPointSet, schemeDivisorDelta_id]

private theorem image_iterate_iUnion_succ {α : Type*} (f : α → α)
    (S : Set α) (m : ℕ) :
    (⋃ i ∈ Set.Iio (m + 1), f^[i] '' S) =
      S ∪ f '' (⋃ i ∈ Set.Iio m, f^[i] '' S) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨i, hi, y, hy, hxy⟩
    cases i with
    | zero =>
        left
        simpa using hxy ▸ hy
    | succ j =>
        right
        refine ⟨f^[j] y, ⟨j, by omega, y, hy, rfl⟩, ?_⟩
        simpa only [Function.iterate_succ_apply'] using hxy
  · rintro (hx | ⟨z, ⟨j, hj, y, hy, hzy⟩, hzx⟩)
    · exact ⟨0, by omega, x, hx, rfl⟩
    · refine ⟨j + 1, by omega, y, hy, ?_⟩
      rw [Function.iterate_succ_apply', hzy]
      exact hzx

/-- Proposition `prop:iterates`(1) at the level of generic points of the
manuscript's weighted normalized branch divisors on the original scheme. -/
theorem weightedBranchPointSet_pow_eq_iUnion
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] (m : ℕ) :
    weightedBranchPointSet (End.of f ^ m).asHom =
      ⋃ i ∈ Set.Iio m, (f : X → X)^[i] '' weightedBranchPointSet f := by
  induction m with
  | zero =>
      simpa using
        (show weightedBranchPointSet (End.of f ^ 0).asHom = ∅ from by
          calc
            weightedBranchPointSet (End.of f ^ 0).asHom =
                weightedBranchPointSet (𝟙 X) := by
                  congr 1
            _ = ∅ := weightedBranchPointSet_id)
  | succ m ih =>
      rw [weightedBranchPointSet_pow_succ, ih]
      exact (image_iterate_iUnion_succ (f : X → X) (weightedBranchPointSet f) m).symm

/-- Proposition `prop:iterates`(1) for the closed underlying branch loci on
the original scheme, including possibly nonnormal varieties. A finite-type
variety has a finite normalization, supplying the instance used here.

`paper-p.tex` correspondence: Proposition 5.3 (`prop:iterates`), item (1) of Proposition 5.3
(`item:branch-iterate`). -/
theorem weightedBranchLocus_pow_eq_iUnion
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] (m : ℕ) :
    weightedBranchLocus (End.of f ^ m).asHom =
      ⋃ i ∈ Set.Iio m, (f : X → X)^[i] '' weightedBranchLocus f := by
  induction m with
  | zero =>
      have hpoint := weightedBranchPointSet_pow_eq_iUnion f 0
      change closure (weightedBranchPointSet (End.of f ^ 0).asHom) =
        ⋃ i ∈ Set.Iio 0, (f : X → X)^[i] '' weightedBranchLocus f
      rw [hpoint]
      simp
  | succ m ih =>
      rw [weightedBranchLocus_pow_succ, ih]
      exact (image_iterate_iUnion_succ (f : X → X) (weightedBranchLocus f) m).symm

/-- Proposition `prop:iterates`(2) for the generic points of weighted branch
divisors on the original scheme. -/
theorem weightedBranchPointSet_orbit_mem_pow
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (n : ℕ) {x : X} (hx : x ∈ weightedBranchPointSet f) :
    (f : X → X)^[n] x ∈ weightedBranchPointSet (End.of f ^ (n + 1)).asHom := by
  rw [weightedBranchPointSet_pow_eq_iUnion]
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
    ⟨Nat.lt_succ_self n, Set.mem_image_of_mem _ hx⟩⟩

private theorem scheme_end_pow_apply_eq_iterate
    {X : Scheme.{u}} (f : X ⟶ X) (m : ℕ) (x : X) :
    (End.of f ^ m).asHom x = (f : X → X)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [pow_succ', End.mul_asHom, Scheme.Hom.comp_apply,
        Function.iterate_succ_apply', ih]

private theorem postcritical_set_iterate_generic {α : Type*} (f : α → α)
    (B : Set α) (m : ℕ) (hm : 0 < m) :
    (⋃ n : ℕ, (f^[m])^[n] '' (⋃ i ∈ Set.Iio m, f^[i] '' B)) =
      ⋃ n : ℕ, f^[n] '' B := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_image]
  constructor
  · rintro ⟨n, y, ⟨i, hi, z, hz, hzy⟩, hxy⟩
    refine ⟨m * n + i, z, hz, ?_⟩
    rw [Function.iterate_add_apply, hzy]
    simpa [Function.iterate_mul] using hxy
  · rintro ⟨N, z, hz, hzx⟩
    refine ⟨N / m, f^[N % m] z,
      ⟨N % m, Nat.mod_lt _ hm, z, hz, rfl⟩, ?_⟩
    have hN : m * (N / m) + N % m = N := Nat.div_add_mod N m
    rw [← hN, Function.iterate_add_apply] at hzx
    simpa [Function.iterate_mul] using hzx

/-- Generic points of the weighted postcritical divisors of `paper-p.tex`,
Definition `def:pcf`, counted on the original scheme.

`paper-p.tex` correspondence: Definition 3.1 (`def:pcf`). -/
noncomputable def weightedPostcriticalPointSet
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] : Set X :=
  ⋃ n : ℕ, (f : X → X)^[n] '' weightedBranchPointSet f

/-- Proposition `prop:iterates`(3), equality of the weighted postcritical
generic-point sets on the original scheme, for any positive iterate. -/
theorem weightedPostcriticalPointSet_pow_eq
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (m : ℕ) (hm : 0 < m) :
    weightedPostcriticalPointSet (End.of f ^ m).asHom =
      weightedPostcriticalPointSet f := by
  have hfun : ((End.of f ^ m).asHom : X → X) = (f : X → X)^[m] :=
    funext (scheme_end_pow_apply_eq_iterate f m)
  simp only [weightedPostcriticalPointSet, hfun,
    weightedBranchPointSet_pow_eq_iUnion]
  exact postcritical_set_iterate_generic (f : X → X) (weightedBranchPointSet f) m hm

/-- The second assertion of Proposition `prop:iterates`(3): every branch
generic point of an iterate is postcritical for the original map. -/
theorem weightedBranchPointSet_pow_subset_postcritical
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] (m : ℕ) :
    weightedBranchPointSet (End.of f ^ m).asHom ⊆
      weightedPostcriticalPointSet f := by
  rw [weightedBranchPointSet_pow_eq_iUnion]
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hi, hx⟩
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

/-- The original-scheme weighted branch generic points are the projections
of the branch divisor points in the actual normalization lift. -/
theorem weightedBranchPointSet_eq_normalization_image
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    weightedBranchPointSet f =
      (fun q : SchemeDivisorPoint (Palomar.normalization X) =>
        Palomar.normalizationMap X q.1) ''
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).branch := by
  ext x
  simp only [weightedBranchPointSet, DeltaDynamics.branch,
    DeltaDynamics.critical, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, ⟨p, hpq, hp⟩, hqx⟩
    exact ⟨q, ⟨p, hp, hpq⟩, hqx⟩
  · rintro ⟨q, ⟨p, hp, hpq⟩, hqx⟩
    exact ⟨q, ⟨p, hpq, hp⟩, hqx⟩

private theorem weighted_normalization_step_comm
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (q : SchemeDivisorPoint (Palomar.normalization X)) :
    Palomar.normalizationMap X
      ((schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).step q).1 =
      f (Palomar.normalizationMap X q.1) := by
  have h := congrArg (fun g : Palomar.normalization X ⟶ X => g q.1)
    (schemeGlobalNormalizationMorphism_comp f)
  rw [schemeGlobalNormalizationMorphism_eq_lift] at h
  simpa only [Scheme.Hom.comp_apply, schemeDeltaDynamics_step_val] using h

private theorem weighted_normalization_iterate_comm
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (n : ℕ) (q : SchemeDivisorPoint (Palomar.normalization X)) :
    Palomar.normalizationMap X
      (((schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).step)^[n] q).1 =
      (f : X → X)^[n] (Palomar.normalizationMap X q.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [weighted_normalization_step_comm f, ih]

/-- The weighted postcritical generic points computed by original-scheme
orbits are exactly the projection of the actual normalization lift's
postcritical divisor points. This links `def:pcf` to the predicate used in
Theorem A for every characteristic. -/
theorem weightedPostcriticalPointSet_eq_normalization_image
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    weightedPostcriticalPointSet f =
      (fun q : SchemeDivisorPoint (Palomar.normalization X) =>
        Palomar.normalizationMap X q.1) ''
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).postcriticalSet := by
  let D := schemeDeltaDynamicsOfFiniteDominantNormal
    (schemeGlobalNormalizationLift f)
  let π : SchemeDivisorPoint (Palomar.normalization X) → X :=
    fun q => Palomar.normalizationMap X q.1
  change (⋃ n, (f : X → X)^[n] '' weightedBranchPointSet f) =
    π '' D.postcriticalSet
  rw [weightedBranchPointSet_eq_normalization_image f]
  change (⋃ n, (f : X → X)^[n] '' (π '' D.branch)) =
    π '' (⋃ n, D.step^[n] '' D.branch)
  rw [Set.image_iUnion]
  congr 1
  funext n
  rw [Set.image_image, Set.image_image]
  congr 1
  funext q
  exact (weighted_normalization_iterate_comm f n q).symm

/-- Definition `def:pcf`: the theorem-facing downstairs PCF predicate is
exactly finiteness of the original-scheme orbit of the weighted branch
generic points. The normalization map is finite for a finite-type variety.

`paper-p.tex` correspondence: Definition 3.1 (`def:pcf`). -/
theorem isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsWeightedNormalizedPCFDownstairs k s f ↔
      (letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k s
      (weightedPostcriticalPointSet f).Finite) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  change ((fun q : SchemeDivisorPoint (Palomar.normalization X) =>
      Palomar.normalizationMap X q.1) ''
    (schemeDeltaDynamicsOfFiniteDominantNormal
      (schemeGlobalNormalizationLift f)).postcriticalSet).Finite ↔
    (weightedPostcriticalPointSet f).Finite
  rw [weightedPostcriticalPointSet_eq_normalization_image]

/-- `paper-p.tex`, Lemma `lem:normalization`, PCF equivalence in any
characteristic for the actual normalization lift. The manuscript's PCF
predicate also requires generic separability, supplied by its hypothesis;
this theorem isolates the postcritical finiteness assertion. -/
theorem weightedPostcriticalPointSet_finite_iff_normalization
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    (weightedPostcriticalPointSet f).Finite ↔
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).IsPCF := by
  exact (isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k s f).symm.trans
    (isWeightedNormalizedPCFDownstairs_iff k s f)

#print axioms isWeightedNormalizedPCFDownstairs_pow_iff_of_genericallySeparable
#print axioms weightedBranchLocus_pow_succ
#print axioms weightedBranchPointSet_pow_succ
#print axioms weightedBranchPointSet_id
#print axioms weightedBranchPointSet_pow_eq_iUnion
#print axioms weightedBranchLocus_pow_eq_iUnion
#print axioms weightedBranchPointSet_orbit_mem_pow
#print axioms weightedPostcriticalPointSet_pow_eq
#print axioms weightedBranchPointSet_pow_subset_postcritical
#print axioms weightedBranchPointSet_eq_normalization_image
#print axioms weightedPostcriticalPointSet_eq_normalization_image
#print axioms isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
#print axioms weightedPostcriticalPointSet_finite_iff_normalization

end Pcf
