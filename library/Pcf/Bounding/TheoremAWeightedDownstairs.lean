/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremACharZero
public import Pcf.Bounding.TheoremACharPWeighted
import Pcf.Bounding.SchemeFiniteResidueDelta
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Set.Finite.Powerset

/-!
# Theorem A with postcritical divisors on the original scheme

In `latex/paper-p.tex`, Definitions `def:crit-branch` and `def:pcf`, the
normalized critical divisors are measured on `Xᵛ`, while their postcritical
images are divisors on `X`. This file records those downstairs points and
proves that their finiteness is equivalent to finiteness of the weighted
postcritical set upstairs. The reverse direction uses finite fibres of the
actual finite normalization map.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Finiteness of the paper's postcritical divisor points on the original
scheme, obtained by projecting the weighted postcritical divisors of the
actual normalization lift. The normalization square identifies these points
with the forward orbits in `def:pcf`.

`paper-p.tex` correspondence: Definition 3.1 (`def:pcf`). -/
def IsWeightedNormalizedPCFDownstairs
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] : Prop := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  exact ((fun Q : SchemeDivisorPoint (Palomar.normalization X) =>
      Palomar.normalizationMap X Q.1) ''
    (schemeDeltaDynamicsOfFiniteDominantNormal
      (schemeGlobalNormalizationLift f)).postcriticalSet).Finite

/-- Downstairs weighted normalized PCF is equivalent to weighted PCF of
the normalization lift. -/
theorem isWeightedNormalizedPCFDownstairs_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsWeightedNormalizedPCFDownstairs k s f ↔
      (letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k s
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).IsPCF) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  let ν : Palomar.normalization X ⟶ X := Palomar.normalizationMap X
  let D := schemeDeltaDynamicsOfFiniteDominantNormal (schemeGlobalNormalizationLift f)
  let π : SchemeDivisorPoint (Palomar.normalization X) → X := fun Q => ν Q.1
  change (π '' D.postcriticalSet).Finite ↔ D.postcriticalSet.Finite
  constructor
  · intro h
    have hpre : (ν ⁻¹' (π '' D.postcriticalSet)).Finite := ν.finite_preimage h
    have hpre' : (π ⁻¹' (π '' D.postcriticalSet)).Finite := by
      change (Subtype.val ⁻¹' (ν ⁻¹' (π '' D.postcriticalSet))).Finite
      exact hpre.preimage Subtype.val_injective.injOn
    exact hpre'.subset (by
      intro Q hQ
      exact ⟨Q, hQ, rfl⟩)
  · exact Set.Finite.image π

/-- **Theorem A, characteristic zero**, from finiteness of postcritical
divisors on the original scheme in the paper's normalized weighted sense.

`paper-p.tex` correspondence: Theorem 1.2 (`thm:A`). -/
theorem isPCFAllSubvarieties_charZero_of_downstairsPCF
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_charZero_of_weightedPCF k s f
    ((isWeightedNormalizedPCFDownstairs_iff k s f).mp hpcf)

/-- **Theorem A, positive characteristic**, with the paper's downstairs
normalized PCF condition and prime-to-`p` monodromy.

`paper-p.tex` correspondence: Theorem 1.2 (`thm:A`). -/
theorem isPCFAllSubvarieties_charP_of_downstairsPCF
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_charP_of_weightedPCF p hp k s f
    ((isWeightedNormalizedPCFDownstairs_iff k s f).mp hpcf) hmono

/-- The PCF predicate at every node of `IsPCFAllSubvarieties` is the paper's
`def:pcf`: generic separability together with finiteness of the weighted
normalized postcritical divisors counted on `X` itself.

`paper-p.tex` correspondence: Definition 3.1 (`def:pcf`). -/
theorem isSeparableNormalizedPCF_iff_downstairs
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsSeparableNormalizedPCF k s f ↔
      IsGenericallySeparable f ∧ IsWeightedNormalizedPCFDownstairs k s f := by
  rw [isSeparableNormalizedPCF_iff_weightedNormalLift, isWeightedNormalizedPCFDownstairs_iff]
  exact ⟨fun ⟨hsep, hpcf⟩ => ⟨hsep, hpcf⟩, fun ⟨hsep, hpcf⟩ => ⟨hsep, hpcf⟩⟩

#print axioms isSeparableNormalizedPCF_iff_downstairs
#print axioms isWeightedNormalizedPCFDownstairs_iff
#print axioms isPCFAllSubvarieties_charZero_of_downstairsPCF
#print axioms isPCFAllSubvarieties_charP_of_downstairsPCF

private theorem orbit_finite_iff_eventuallyPeriodic {α : Type u} (f : α → α) (x : α) :
    (Set.range (fun n : ℕ => f^[n] x)).Finite ↔
      ∃ r s : ℕ, 0 < s ∧ f^[r+s] x = f^[r] x := by
  constructor
  · intro h
    obtain ⟨r, n, hrn, heq⟩ :=
      h.exists_lt_map_eq_of_forall_mem
        (fun i : ℕ => Set.mem_range_self i)
    refine ⟨r, n - r, by omega, ?_⟩
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hrn)] using heq.symm
  · rintro ⟨r, s, hs, heq⟩
    let y := f^[r] x
    have hperiod : Function.IsPeriodicPt f s y := by
      change f^[s] y = y
      simpa only [y, ← Function.iterate_add_apply, Nat.add_comm] using heq
    let T : Set α := Set.range (fun i : Fin (r+s) => f^[i.val] x)
    have hT : T.Finite := Set.finite_range _
    apply hT.subset
    rintro z ⟨n, rfl⟩
    by_cases hn : n < r
    · exact ⟨⟨n, by omega⟩, rfl⟩
    · let m := n-r
      have hn' : n = r + m := by omega
      have hmod : f^[n] x = f^[r + (m % s)] x := by
        rw [hn', Nat.add_comm r m, Function.iterate_add_apply]
        rw [← hperiod.iterate_mod_apply m]
        rw [Nat.add_comm r (m % s), Function.iterate_add_apply]
      have hms : m % s < s := Nat.mod_lt _ hs
      exact ⟨⟨r + m % s, by omega⟩, hmod.symm⟩

private theorem orbit_finite_iff_tail_finite {α : Type u} (f : α → α) (x : α) :
    (Set.range (fun n : ℕ => f^[n] x)).Finite ↔
      (Set.range (fun n : ℕ => f^[n] (f x))).Finite := by
  have hdecomp :
      Set.range (fun n : ℕ => f^[n] x) =
        {x} ∪ Set.range (fun n : ℕ => f^[n] (f x)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Set.mem_union_left _ (Set.mem_singleton x)
      | succ n =>
          apply Set.mem_union_right
          exact ⟨n, by
            change f^[n] (f x) = f^[n+1] x
            exact (Function.iterate_succ_apply f n x).symm⟩
    · intro h
      rcases h with h | ⟨n, rfl⟩
      · exact ⟨0, Set.mem_singleton_iff.mp h |>.symm⟩
      · exact ⟨n+1, by
          change f^[n+1] x = f^[n] (f x)
          exact Function.iterate_succ_apply f n x⟩
  rw [hdecomp]
  exact ⟨fun h => h.subset (Set.subset_union_right), fun h => Set.finite_singleton x |>.union h⟩

private theorem iterate_image {α : Type u} (f : α → α) (S : Set α) (n : ℕ) :
    (fun T : Set α => f '' T)^[n] S = f^[n] '' S := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Set.image_image]
      congr 1
      funext x
      exact (Function.iterate_succ_apply' f n x).symm

namespace DivisorDynamics

variable {P : Type u} (D : DivisorDynamics P)

/-- The normalized critical divisors of the abstract divisorial system. -/
def criticalSet : Set P := {Q | 1 < D.ramificationIdx Q}

/-- The branch divisors are the image of the critical divisors. -/
theorem branch_eq_image_criticalSet : D.branch = D.step '' D.criticalSet := by
  ext Q
  simp only [branch, criticalSet, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨R, hR, hram⟩
    exact ⟨R, hram, hR⟩
  · rintro ⟨R, hram, hR⟩
    exact ⟨R, hR, hram⟩

/-- Proposition `prop:pcf-equiv`, clauses (1) and (2), on normalized divisors. -/
theorem isPCF_iff_branchPointPreperiodic :
    D.IsPCF ↔
      ∀ Q ∈ D.branch, ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] Q = D.step^[r] Q := by
  constructor
  · intro h Q hQ
    exact (orbit_finite_iff_eventuallyPeriodic D.step Q).mp
      ((D.isPCF_iff_forall_orbit_finite).mp h Q hQ)
  · intro h
    apply (D.isPCF_iff_forall_orbit_finite).mpr
    intro Q hQ
    exact (orbit_finite_iff_eventuallyPeriodic D.step Q).mpr (h Q hQ)

/-- Finiteness of the orbit of the set of branch divisors is equivalent to PCF. -/
theorem isPCF_iff_finite_branch_set_orbit :
    D.IsPCF ↔ (Set.range (fun n : ℕ => D.step^[n] '' D.branch)).Finite := by
  constructor
  · intro h
    apply h.powerset.subset
    rintro S ⟨n, rfl⟩
    change D.step^[n] '' D.branch ⊆ D.postcriticalSet
    intro Q hQ
    exact Set.mem_iUnion.mpr ⟨n, hQ⟩
  · intro h
    have hpart : ∀ S ∈ Set.range (fun n : ℕ => D.step^[n] '' D.branch), S.Finite := by
      rintro S ⟨n, rfl⟩
      exact D.step_image_ramified_finite.image _
    have hU := h.biUnion hpart
    have heq : (⋃ S ∈ Set.range (fun n : ℕ => D.step^[n] '' D.branch), S) =
        D.postcriticalSet := by
      ext Q
      simp only [postcriticalSet, Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨S, ⟨n, rfl⟩, hQ⟩
        exact ⟨n, hQ⟩
      · rintro ⟨n, hQ⟩
        exact ⟨_, ⟨n, rfl⟩, hQ⟩
    change D.postcriticalSet.Finite
    rw [← heq]
    exact hU

/-- The paper's set-level preperiodicity of the critical divisor locus. -/
def IsCriticalSetPreperiodic : Prop :=
  ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] '' D.criticalSet = D.step^[r] '' D.criticalSet

/-- Proposition `prop:pcf-equiv`, clauses (1) and (3), on normalized divisors. -/
theorem isPCF_iff_criticalSetPreperiodic : D.IsPCF ↔ D.IsCriticalSetPreperiodic := by
  let F : Set P → Set P := fun S => D.step '' S
  have hbranch : F D.criticalSet = D.branch := D.branch_eq_image_criticalSet.symm
  rw [D.isPCF_iff_finite_branch_set_orbit]
  change (Set.range (fun n : ℕ => D.step^[n] '' D.branch)).Finite ↔ _
  simpa only [IsCriticalSetPreperiodic, ← iterate_image, ← hbranch] using
    ((orbit_finite_iff_tail_finite F D.criticalSet).symm.trans
      (orbit_finite_iff_eventuallyPeriodic F D.criticalSet))

/-- The three conditions of `paper-p.tex`, Proposition `prop:pcf-equiv`,
as an equivalence of PCF, preperiodic branch divisors, and preperiodic
critical divisor set in an abstract divisorial system. -/
theorem pcf_equiv :
    (D.IsPCF ↔
      ∀ Q ∈ D.branch, ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] Q = D.step^[r] Q) ∧
    (D.IsPCF ↔ D.IsCriticalSetPreperiodic) :=
  ⟨D.isPCF_iff_branchPointPreperiodic, D.isPCF_iff_criticalSetPreperiodic⟩

end DivisorDynamics

#print axioms DivisorDynamics.pcf_equiv

namespace DeltaDynamics

variable {P : Type u} (D : DeltaDynamics P)

/-- Proposition `prop:pcf-equiv` for weighted divisor dynamics. The finite
branch condition is the geometric finiteness input for a separable map. -/
theorem pcf_equiv_weighted
    (hpos : ∀ d, 0 < D.delta d)
    (hsurj : Function.Surjective D.step)
    (hbranch : D.branch.Finite) :
    (D.IsPCF ↔
      ∀ Q ∈ D.branch, ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] Q = D.step^[r] Q) ∧
    (D.IsPCF ↔
      ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] '' D.critical =
        D.step^[r] '' D.critical) := by
  have h := (D.toDivisorDynamics hpos hsurj hbranch).pcf_equiv
  simp only [DivisorDynamics.IsPCF, DivisorDynamics.IsCriticalSetPreperiodic] at h
  rw [D.toDivisorDynamics_postcriticalSet hpos hsurj hbranch,
    D.toDivisorDynamics_branch hpos hsurj hbranch] at h
  exact h

end DeltaDynamics

/-- Proposition `prop:pcf-equiv` on actual normalized divisors of a finite
generically separable normal scheme self-map, with `δ` from stalk and residue
fields. The final critical-set condition concerns divisor points. -/
theorem schemeDeltaDynamics_pcf_equiv_of_genericallySeparable
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparableSchemeMap f) :
    let D := schemeDeltaDynamicsOfFiniteDominantNormal f
    (D.IsPCF ↔
      ∀ Q ∈ D.branch, ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] Q = D.step^[r] Q) ∧
    (D.IsPCF ↔
      ∃ r s : ℕ, 0 < s ∧ D.step^[r+s] '' D.critical =
        D.step^[r] '' D.critical) := by
  let D := schemeDeltaDynamicsOfFiniteDominantNormal f
  have hpos : ∀ d, 0 < D.delta d := schemeDivisorDelta_pos_of_isFinite f
  have hsurj : Function.Surjective D.step :=
    SchemeDivisorPoint.mapFiniteDominantNormal_surjective f
  have hbranch : D.branch.Finite :=
    schemeDeltaDynamics_branch_finite_of_genericallySeparable f hsep
  exact D.pcf_equiv_weighted hpos hsurj hbranch

/-- The generic points of the manuscript's normalized weighted branch
divisors on the original target scheme. The critical divisors and their
weights are computed on the canonical normalizations. -/
noncomputable def weightedBranchPointSet
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] : Set Y :=
  let F := schemeGlobalNormalizationMorphism f
  (fun q : SchemeDivisorPoint (Palomar.normalization Y) =>
    Palomar.normalizationMap Y q.1) ''
    {q | ∃ p : SchemeDivisorPoint (Palomar.normalization X),
      p.mapFiniteDominantNormal F = q ∧ 1 < schemeDivisorDelta F p}

/-- Lemma `lem:tower` for the generic points of normalized weighted branch
divisors on possibly nonnormal original schemes. The equality of the
associated closed unions of integral effective divisors is a separate
geometric correspondence. -/
theorem weightedBranchPointSet_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap Z)] :
    weightedBranchPointSet (f ≫ g) =
      weightedBranchPointSet g ∪ g '' weightedBranchPointSet f := by
  let F := schemeGlobalNormalizationMorphism f
  let G := schemeGlobalNormalizationMorphism g
  have hcomp : schemeGlobalNormalizationMorphism (f ≫ g) = F ≫ G :=
    (schemeGlobalNormalizationMorphism_comp_morphism f g).symm
  simp only [weightedBranchPointSet, hcomp]
  rw [schemeDelta_branch_comp F G]
  rw [Set.image_union]
  congr 1
  have hmap :
      (fun q : SchemeDivisorPoint (Palomar.normalization Y) =>
        Palomar.normalizationMap Z
          (SchemeDivisorPoint.mapFiniteDominantNormal G q).1) =
      (fun q : SchemeDivisorPoint (Palomar.normalization Y) =>
        g (Palomar.normalizationMap Y q.1)) := by
    funext q
    have h := congrArg (fun m : Palomar.normalization Y ⟶ Z => m q.1)
      (schemeGlobalNormalizationMorphism_comp g)
    simpa only [Scheme.Hom.comp_apply, G, SchemeDivisorPoint.mapFiniteDominantNormal] using h
  rw [Set.image_image, Set.image_image, hmap]

/-- Original-scheme generic points supporting weighted critical divisors on
the canonical normalization. -/
noncomputable def weightedCriticalPointSet
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] : Set X :=
  let F := schemeGlobalNormalizationMorphism f
  (fun p : SchemeDivisorPoint (Palomar.normalization X) =>
    Palomar.normalizationMap X p.1) ''
    {p | 1 < schemeDivisorDelta F p}

/-- Definition `def:crit-branch` at the level of generic points: branch
points are the images of critical points. -/
theorem weightedBranchPointSet_eq_image_criticalPointSet
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    weightedBranchPointSet f = f '' weightedCriticalPointSet f := by
  let F := schemeGlobalNormalizationMorphism f
  have hbranch :
      {q : SchemeDivisorPoint (Palomar.normalization Y) |
        ∃ p : SchemeDivisorPoint (Palomar.normalization X),
        p.mapFiniteDominantNormal F = q ∧ 1 < schemeDivisorDelta F p} =
      (fun p : SchemeDivisorPoint (Palomar.normalization X) => p.mapFiniteDominantNormal F) ''
        {p | 1 < schemeDivisorDelta F p} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨p, rfl, hp⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, rfl, hp⟩
  have hmap :
      (fun p : SchemeDivisorPoint (Palomar.normalization X) =>
        Palomar.normalizationMap Y (p.mapFiniteDominantNormal F).1) =
      (fun p : SchemeDivisorPoint (Palomar.normalization X) =>
        f (Palomar.normalizationMap X p.1)) := by
    funext p
    have h := congrArg (fun m : Palomar.normalization X ⟶ Y => m p.1)
      (schemeGlobalNormalizationMorphism_comp f)
    simpa only [Scheme.Hom.comp_apply, F, SchemeDivisorPoint.mapFiniteDominantNormal] using h
  change (fun q : SchemeDivisorPoint (Palomar.normalization Y) =>
    Palomar.normalizationMap Y q.1) ''
      {q | ∃ p : SchemeDivisorPoint (Palomar.normalization X),
        p.mapFiniteDominantNormal F = q ∧ 1 < schemeDivisorDelta F p} =
      f '' ((fun p : SchemeDivisorPoint (Palomar.normalization X) =>
        Palomar.normalizationMap X p.1) '' {p | 1 < schemeDivisorDelta F p})
  rw [hbranch, Set.image_image, Set.image_image, hmap]

/-- The closed original-scheme locus generated by the projected weighted
critical divisor points.

`paper-p.tex` correspondence: Definition 2.2 (`def:crit-branch`). -/
noncomputable def weightedCriticalLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] : Set X :=
  closure (weightedCriticalPointSet f)


/-- The closed original-scheme locus generated by the weighted branch
divisor points. For a separable map the generating set is finite.

`paper-p.tex` correspondence: Definition 2.2 (`def:crit-branch`). -/
noncomputable def weightedBranchLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] : Set Y :=
  closure (weightedBranchPointSet f)

/-- Definition `def:crit-branch` for the closed loci: a finite scheme map
takes the weighted critical locus onto the weighted branch locus.

`paper-p.tex` correspondence: Definition 2.2 (`def:crit-branch`), equation (1) (`eq:branch-
normalization`). -/
theorem weightedBranchLocus_eq_image_criticalLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    weightedBranchLocus f = f '' weightedCriticalLocus f := by
  simp only [weightedBranchLocus, weightedCriticalLocus,
    weightedBranchPointSet_eq_image_criticalPointSet,
    f.isClosedMap.closure_image_eq_of_continuous f.continuous]

/-- Lemma `lem:tower` for the closed weighted branch loci on possibly
nonnormal original schemes.

`paper-p.tex` correspondence: Remark 2.3 (`rem:why-normalized`), Lemma 5.2 (`lem:tower`). -/
theorem weightedBranchLocus_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap Z)] :
    weightedBranchLocus (f ≫ g) =
      weightedBranchLocus g ∪ g '' weightedBranchLocus f := by
  simp only [weightedBranchLocus, weightedBranchPointSet_comp,
    closure_union, g.isClosedMap.closure_image_eq_of_continuous g.continuous]


private theorem finite_closure_eq_union {Y : Type*} [TopologicalSpace Y]
    (S : Set Y) (hS : S.Finite) :
    closure S = ⋃ y ∈ S, closure ({y} : Set Y) := by
  calc
    closure S = closure (⋃ x ∈ S, ({x} : Set Y)) := by rw [Set.biUnion_of_singleton]
    _ = ⋃ x ∈ S, closure ({x} : Set Y) := hS.closure_biUnion _

/-- A generically separable normalization lift has finitely many projected
weighted critical divisor points. -/
theorem weightedCriticalPointSet_finite_of_lift_genericallySeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (hsep : IsGenericallySeparableSchemeMap (schemeGlobalNormalizationMorphism f)) :
    (weightedCriticalPointSet f).Finite := by
  let F := schemeGlobalNormalizationMorphism f
  have hcrit :
      {p : SchemeDivisorPoint (Palomar.normalization X) | 1 < schemeDivisorDelta F p}.Finite :=
    schemeDivisorWeightedCritical_finite_of_genericallySeparable F hsep
  exact hcrit.image _


/-- For a generically separable normalization lift, the closed critical
locus is exactly the finite union of closures of its divisor points. -/
theorem weightedCriticalLocus_eq_union_of_lift_genericallySeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (hsep : IsGenericallySeparableSchemeMap (schemeGlobalNormalizationMorphism f)) :
    weightedCriticalLocus f =
      ⋃ x ∈ weightedCriticalPointSet f, closure ({x} : Set X) :=
  finite_closure_eq_union _ (weightedCriticalPointSet_finite_of_lift_genericallySeparable f hsep)

/-- For a generically separable normalization lift, the closed branch locus
is exactly the finite union of closures of its divisor points. -/
theorem weightedBranchLocus_eq_union_of_lift_genericallySeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (hsep : IsGenericallySeparableSchemeMap (schemeGlobalNormalizationMorphism f)) :
    weightedBranchLocus f =
      ⋃ y ∈ weightedBranchPointSet f, closure ({y} : Set Y) := by
  have hfin : (weightedBranchPointSet f).Finite := by
    rw [weightedBranchPointSet_eq_image_criticalPointSet]
    exact (weightedCriticalPointSet_finite_of_lift_genericallySeparable f hsep).image f
  exact finite_closure_eq_union _ hfin

/-- Definition `def:crit-branch` for a finite generically separable map:
the closed critical locus is the finite union of projected normalized
critical divisors. -/
theorem weightedCriticalLocus_eq_union_of_genericallySeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (hsep : IsGenericallySeparableSchemeMap f) :
    weightedCriticalLocus f =
      ⋃ x ∈ weightedCriticalPointSet f, closure ({x} : Set X) :=
  weightedCriticalLocus_eq_union_of_lift_genericallySeparable f
    (isGenericallySeparable_schemeGlobalNormalizationMorphism f hsep)

/-- The normalized weighted branch locus is likewise the finite union of
its projected divisor components under generic separability. -/
theorem weightedBranchLocus_eq_union_of_genericallySeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (hsep : IsGenericallySeparableSchemeMap f) :
    weightedBranchLocus f =
      ⋃ y ∈ weightedBranchPointSet f, closure ({y} : Set Y) :=
  weightedBranchLocus_eq_union_of_lift_genericallySeparable f
    (isGenericallySeparable_schemeGlobalNormalizationMorphism f hsep)


/-- The image of a normalized integral effective divisor has the same
underlying closed set as the closure of its projected generic point. -/
theorem normalization_image_divisor_closure
    {X : Scheme.{u}} [IsIntegral X] [IsFinite (Palomar.normalizationMap X)]
    (p : SchemeDivisorPoint (Palomar.normalization X)) :
    (Palomar.normalizationMap X) ''
      closure ({p.1} : Set (Palomar.normalization X)) =
    closure ({Palomar.normalizationMap X p.1} : Set X) := by
  simpa only [Set.image_singleton] using
    ((Palomar.normalizationMap X).isClosedMap.closure_image_eq_of_continuous
      (Palomar.normalizationMap X).continuous ({p.1} : Set (Palomar.normalization X))).symm


/-- The source definition `def:crit-branch`: for a separable map the
critical locus is the finite union of the actual images of normalized
critical divisors, represented by their closed underlying sets.

`paper-p.tex` correspondence: Definition 2.2 (`def:crit-branch`), Lemma 5.2 (`lem:tower`). -/
theorem weightedCriticalLocus_eq_union_normalized_divisor_images
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (hsep : IsGenericallySeparableSchemeMap f) :
    let F := schemeGlobalNormalizationMorphism f
    weightedCriticalLocus f =
      ⋃ p ∈ ({p : SchemeDivisorPoint (Palomar.normalization X) |
        1 < schemeDivisorDelta F p} : Set _),
        (Palomar.normalizationMap X) ''
          closure ({p.1} : Set (Palomar.normalization X)) := by
  let F := schemeGlobalNormalizationMorphism f
  rw [weightedCriticalLocus_eq_union_of_genericallySeparable f hsep]
  change (⋃ x ∈ ((fun p : SchemeDivisorPoint (Palomar.normalization X) =>
    Palomar.normalizationMap X p.1) ''
      {p | 1 < schemeDivisorDelta F p}), closure ({x} : Set X)) = _
  ext y
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨p, hp, rfl⟩, hy⟩
    exact ⟨p, hp, (normalization_image_divisor_closure p).symm ▸ hy⟩
  · rintro ⟨p, hp, hy⟩
    exact ⟨_, ⟨p, hp, rfl⟩, (normalization_image_divisor_closure p) ▸ hy⟩


/-- On a finite-type target, every projected normalized divisor in the
preceding union remains codimension one on the original variety. -/
theorem normalization_divisor_image_coheight_one
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    [∀ U : X.affineOpens, Algebra k Γ(X, U)]
    [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)]
    (p : SchemeDivisorPoint (Palomar.normalization X)) :
    Order.coheight (Palomar.normalizationMap X p.1) = 1 :=
  coheight_apply_eq_one_of_finiteType (Palomar.normalizationMap X) k p


#print axioms DeltaDynamics.pcf_equiv_weighted
#print axioms weightedCriticalLocus_eq_union_normalized_divisor_images
#print axioms normalization_divisor_image_coheight_one
#print axioms weightedCriticalLocus_eq_union_of_lift_genericallySeparable
#print axioms weightedBranchLocus_eq_union_of_lift_genericallySeparable
#print axioms weightedCriticalLocus_eq_union_of_genericallySeparable
#print axioms weightedBranchLocus_eq_union_of_genericallySeparable
#print axioms weightedBranchLocus_eq_image_criticalLocus
#print axioms weightedBranchLocus_comp
#print axioms schemeDeltaDynamics_pcf_equiv_of_genericallySeparable
#print axioms weightedBranchPointSet_comp


end
end Pcf
