/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Geometry
public import Pcf.Wiring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Irreducible

/-!
# A concrete, genuinely ramified witness for `Pcf.PCFGeometry`

`Pcf/Geometry.lean` derives Theorem `thm:normal-invariant` (`Pcf.PCFGeometry.restriction_isPCF`)
from a structure `Pcf.PCFGeometry PX B` together with the bounding conclusion `key` as an explicit
argument. A reader is entitled to ask whether that structure is inhabited at all, and — more sharply
— whether it is inhabited by anything in which the *restricted* system actually ramifies. If the
only models had `res.branch = ∅`, Theorem `thm:normal-invariant` would be true but empty on this
route.

This file answers both questions with a single compiling instance.

## The space

The base space is `Pcf.Examples.CofiniteNat`, namely `ℕ` carried by `CofiniteTopology`: a set
is open iff it is empty or has finite complement. Mathlib supplies its closed-set
description (`CofiniteTopology.isClosed_iff`) and its Noetherianness
(`instNoetherianSpaceCofiniteTopology`), and this file supplies the identification of
`Pcf.IsProperIrreducibleClosed`.

## What is established

* `Pcf.Examples.isClosed_cofiniteNat_iff` — the closed sets are exactly the finite sets and
  the whole space.
* `Pcf.Examples.isProperIrreducibleClosed_iff_singleton` —
  `Pcf.IsProperIrreducibleClosed s ↔ ∃ x, s = {x}`. So the primes of
  this toy "variety" are its points, and there are plenty of them.
* `Pcf.Examples.noetherianSpace_cofiniteNat` — the space is Noetherian, which is the hypothesis
  `Pcf.PCFGeometry.restriction_isPCF` needs.
* `Pcf.Examples.cofiniteGeometry` — a `Pcf.PCFGeometry Unit CofiniteNat`. The ambient system is
  trivial (identity step, no ramification, hence PCF); the restricted system has identity
  step and ramification index `2` at the prime `{0}` and `1` elsewhere; the correction
  locus `singAmbient` is `{0}`, so the ramified prime sits inside it, exactly as
  Theorem `thm:bounding` permits.
* `Pcf.Examples.restrictionDynamics_branch` — the restricted branch divisor is `{{0}}`, in
  particular
  **nonempty** (`Pcf.Examples.restrictionDynamics_branch_nonempty`). The witness is therefore not
  ramification-free.
* `Pcf.Examples.restrictionDynamics_isPCF` — `res.PCF`, obtained by *applying*
  `Pcf.PCFGeometry.restriction_isPCF`
  to the instance, not by reproving it.

## What is **not** established

This is a toy topological space, not a variety. `CofiniteNat` is one-dimensional in the crude
sense that its proper closed subsets are finite, and its "primes" are points; there is no
scheme, no cover, no ring of functions, and nothing here is a model of an actual finite
separable self-map. The bounding conclusion `key` is discharged cheaply, because away from
`{0}` the restricted ramification index is literally `1`. No purity or Abhyankar input is
exercised: the index is known to be `1` by construction.

What the file does show is precisely this: `Pcf.PCFGeometry` is consistent, its fields can
be satisfied simultaneously, and they can be satisfied with `res.branch ≠ ∅`. That is the
non-vacuity claim, and no more.
-/

@[expose] public section

namespace Pcf.Examples

open Set TopologicalSpace

/-! ### The space: `ℕ` with the cofinite topology -/

/-- The toy base space: the natural numbers carried by the cofinite topology. -/
abbrev CofiniteNat : Type := CofiniteTopology ℕ

instance : Infinite CofiniteNat :=
  Infinite.of_injective CofiniteTopology.of CofiniteTopology.of.injective

/-- **Step 1.** The closed subsets of `CofiniteNat` are exactly the finite sets together with
the whole space. This is Mathlib's `CofiniteTopology.isClosed_iff`, recorded here because
every argument below is an application of it. -/
theorem isClosed_cofiniteNat_iff {s : Set CofiniteNat} : IsClosed s ↔ s = univ ∨ s.Finite :=
  CofiniteTopology.isClosed_iff

/-- A finite subset of `CofiniteNat` is a proper subset, since `CofiniteNat` is infinite. -/
theorem ne_univ_of_finite {s : Set CofiniteNat} (hs : s.Finite) : s ≠ univ := fun h =>
  Set.infinite_univ (h ▸ hs)

/-- A proper closed subset of `CofiniteNat` is finite. -/
theorem finite_of_isClosed_of_ne_univ {s : Set CofiniteNat} (hcl : IsClosed s) (hne : s ≠ univ) :
    s.Finite :=
  (isClosed_cofiniteNat_iff.mp hcl).resolve_left hne

/-- In the cofinite topology a finite irreducible set has at most one point: if it had two,
`x` and `y`, it would be the union of the two proper closed subsets `{x}` and `s \ {x}`. -/
theorem subsingleton_of_isIrreducible_of_finite {s : Set CofiniteNat} (hirr : IsIrreducible s)
    (hfin : s.Finite) : s.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hu : IsOpen ({x}ᶜ : Set CofiniteNat) :=
    CofiniteTopology.isOpen_iff'.mpr (Or.inr (by simp))
  have hv : IsOpen ((s \ {x})ᶜ : Set CofiniteNat) :=
    CofiniteTopology.isOpen_iff'.mpr (Or.inr (by simpa using hfin.sdiff))
  obtain ⟨z, hzs, hzu, hzv⟩ :=
    hirr.2 _ _ hu hv ⟨y, hy, fun h => hxy h.symm⟩ ⟨x, hx, fun h => h.2 rfl⟩
  exact hzv ⟨hzs, hzu⟩

/-! ### Step 2: the primes are the points -/

/-- **Step 2, one direction.** Every singleton is a prime of `CofiniteNat`. -/
theorem isProperIrreducibleClosed_singleton (x : CofiniteNat) : Pcf.IsProperIrreducibleClosed
    ({x} : Set CofiniteNat) where
  irreducible := isIrreducible_singleton
  isClosed := isClosed_cofiniteNat_iff.mpr (Or.inr (Set.finite_singleton x))
  ne_univ := ne_univ_of_finite (Set.finite_singleton x)
  maximal := by
    intro Q hQirr hQcl hQne hsub
    refine hsub.antisymm fun y hy => ?_
    have hfin := finite_of_isClosed_of_ne_univ hQcl hQne
    have := subsingleton_of_isIrreducible_of_finite hQirr hfin hy (hsub rfl)
    simpa using this

/-- **Step 2, the other direction.** Every prime of `CofiniteNat` is a singleton: it is closed
and proper, hence finite, and finite irreducible sets are subsingletons. -/
theorem eq_singleton_of_isProperIrreducibleClosed {s : Set CofiniteNat}
    (hs : Pcf.IsProperIrreducibleClosed s) : ∃ x, s = {x} := by
  obtain ⟨x, hx⟩ := hs.nonempty
  refine ⟨x, ?_⟩
  have hfin := finite_of_isClosed_of_ne_univ hs.isClosed hs.ne_univ
  exact (subsingleton_of_isIrreducible_of_finite hs.irreducible hfin).eq_singleton_of_mem hx

/-- **Step 2.** The primes of `CofiniteNat`, in the sense of `Pcf.IsProperIrreducibleClosed`, are
exactly its points. In particular there are infinitely many of them. -/
theorem isProperIrreducibleClosed_iff_singleton {s : Set CofiniteNat} :
    Pcf.IsProperIrreducibleClosed s ↔ ∃ x, s = {x} :=
  ⟨eq_singleton_of_isProperIrreducibleClosed,
      by rintro ⟨x, rfl⟩; exact isProperIrreducibleClosed_singleton x⟩

/-! ### Step 3: Noetherianness -/

/-- **Step 3.** `CofiniteNat` is a Noetherian space — the hypothesis under which
`Pcf.PCFGeometry.restriction_isPCF` is stated. Descending chains of closed sets are eventually
chains of finite sets, so they stabilize; Mathlib already knows this for the cofinite
topology. -/
theorem noetherianSpace_cofiniteNat : NoetherianSpace CofiniteNat := inferInstance

/-! ### Step 4: the geometry -/

/-- The point `0`, whose prime `{0}` is where the restricted system will ramify. -/
def zeroPoint : CofiniteNat := CofiniteTopology.of 0

/-- The prime `{0}` of `CofiniteNat`. -/
def zeroPrime : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s} :=
    ⟨{zeroPoint}, isProperIrreducibleClosed_singleton zeroPoint⟩

@[simp] theorem zeroPrime_coe : (zeroPrime : Set CofiniteNat) = {zeroPoint} := rfl

/-- The ambient system: one prime, identity step, no ramification. -/
def ambientDynamics : DivisorDynamics Unit where
  step := id
  ramificationIdx := fun _ => 1
  ramificationIdx_pos := fun _ => Nat.one_pos
  step_surjective := Function.surjective_id
  step_image_ramified_finite := Set.toFinite _

/-- The ambient system is unramified. -/
theorem ambientDynamics_branch : ambientDynamics.branch = ∅ := by
  ext Q
  simp [DivisorDynamics.branch, ambientDynamics]

/-- The ambient system is post-critically finite — trivially, since it has one prime. -/
theorem ambientDynamics_isPCF : ambientDynamics.IsPCF := Set.toFinite _

/-- The ramification index of the restricted system: `2` at the prime `{0}`, `1`
elsewhere. -/
noncomputable def restrictionRamificationIdx
    (Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}) : ℕ :=
  letI := Classical.propDecidable ((Q : Set CofiniteNat) = {zeroPoint})
  if (Q : Set CofiniteNat) = {zeroPoint} then 2 else 1

theorem restrictionRamificationIdx_of_eq
    {Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}}
        (h : (Q : Set CofiniteNat) = {zeroPoint}) :
    restrictionRamificationIdx Q = 2 := by
  simp [restrictionRamificationIdx, h]

theorem restrictionRamificationIdx_of_ne
    {Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}}
        (h : (Q : Set CofiniteNat) ≠ {zeroPoint}) :
    restrictionRamificationIdx Q = 1 := by
  simp [restrictionRamificationIdx, h]

theorem restrictionRamificationIdx_pos
    (Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}) : 0 < restrictionRamificationIdx
        Q := by
  by_cases h : (Q : Set CofiniteNat) = {zeroPoint}
  · simp [restrictionRamificationIdx_of_eq h]
  · simp [restrictionRamificationIdx_of_ne h]

theorem eq_zeroPrime_of_one_lt_restrictionRamificationIdx
    {Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}}
    (h : 1 < restrictionRamificationIdx Q) : Q = zeroPrime := by
  by_cases hQ : (Q : Set CofiniteNat) = {zeroPoint}
  · exact Subtype.ext hQ
  · rw [restrictionRamificationIdx_of_ne hQ] at h
    exact absurd h (by omega)

/-- The restricted system `g = f|_A`: identity step on the primes of `CofiniteNat`, with
ramification index `2` at `{0}`. The branch set is the singleton `{{0}}`, so
`step_image_ramified_finite` holds; here it is proved by hand.  A second construction of the same
system, with `step_image_ramified_finite` derived from a purity datum, is
`restrictionDynamicsOfPurity`; the two are kept because the second one exercises the purity
wiring of `Pcf/Wiring.lean`. -/
noncomputable def restrictionDynamics : DivisorDynamics
    {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s} where
  step := id
  ramificationIdx := restrictionRamificationIdx
  ramificationIdx_pos := restrictionRamificationIdx_pos
  step_surjective := Function.surjective_id
  step_image_ramified_finite := by
    refine (Set.finite_singleton zeroPrime).subset ?_
    rintro Q ⟨Q', hQ', hram⟩
    have : Q' = zeroPrime := eq_zeroPrime_of_one_lt_restrictionRamificationIdx hram
    simp only [Set.mem_singleton_iff, ← hQ', this, id_eq]

@[simp] theorem restrictionDynamics_step : restrictionDynamics.step = id := rfl

@[simp] theorem restrictionDynamics_ramificationIdx : restrictionDynamics.ramificationIdx =
    restrictionRamificationIdx := rfl

/-- Away from `{0}` the restricted system is unramified, in every iterate: the step map is
the identity, so the tower product is a product of copies of `1`. -/
theorem restrictionDynamics_iterateRamificationIdx_eq_one (m : ℕ)
    {Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}}
    (h : (Q : Set CofiniteNat) ≠ {zeroPoint}) : restrictionDynamics.iterateRamificationIdx m Q =
        1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [restrictionDynamics_step, Function.iterate_id, id_eq, restrictionDynamics_ramificationIdx,
      restrictionRamificationIdx_of_ne h]

/-- The bounding conclusion for the witness: away from the prime `{0}` (which lies in
`singAmbient`) every iterate of the restricted system is unramified, so no good prime is a
branch prime. -/
theorem notMem_branch_iterate_restrictionDynamics (m : ℕ)
    (Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s})
    (hsa : ¬ ((Q : Set CofiniteNat) ⊆ ({zeroPoint} : Set CofiniteNat))) :
    Q ∉ (restrictionDynamics.iterate m).branch := by
  rintro ⟨Q', hQ', hram⟩
  have hQeq : Q' = Q := by
    rw [DivisorDynamics.iterate_step, restrictionDynamics_step, Function.iterate_id, id_eq] at hQ'
    exact hQ'
  have hne : (Q' : Set CofiniteNat) ≠ {zeroPoint} := by
    rw [hQeq]
    exact fun h => hsa (le_of_eq h)
  rw [DivisorDynamics.iterate_ramificationIdx, restrictionDynamics_iterateRamificationIdx_eq_one m
      hne] at hram
  exact absurd hram (by omega)

/-- **The witness.** A `Pcf.PCFGeometry` on the cofinite space, with a trivial ambient
system and a restricted system that genuinely ramifies at the prime `{0}`.

The ramified prime lies in the correction locus `singAmbient = {0}`, which is exactly the
configuration Theorem `thm:bounding` allows: the proposition bounds ramification *away* from the
three loci, and says nothing inside them. -/
noncomputable def cofiniteGeometry : PCFGeometry Unit CofiniteNat where
  ambient := ambientDynamics
  fixedPrime := ()
  fixed := rfl
  restriction := restrictionDynamics
  singAmbient := {zeroPoint}
  singSelf := ∅
  otherBranchIntersection := fun _ => ∅
  singAmbient_isClosed := isClosed_cofiniteNat_iff.mpr (Or.inr (Set.finite_singleton zeroPoint))
  singAmbient_ne_univ := ne_univ_of_finite (Set.finite_singleton zeroPoint)
  singSelf_isClosed := isClosed_empty
  singSelf_ne_univ := ne_univ_of_finite Set.finite_empty
  otherBranchIntersection_isClosed := fun _ _ => isClosed_empty
  otherBranchIntersection_ne_univ := fun _ _ => ne_univ_of_finite Set.finite_empty

/-! ### Step 5: the payoff -/

/-- The restricted branch divisor is exactly `{{0}}`. -/
theorem restrictionDynamics_branch : restrictionDynamics.branch = {zeroPrime} := by
  ext Q
  constructor
  · rintro ⟨Q', hQ', hram⟩
    have h : Q' = zeroPrime := eq_zeroPrime_of_one_lt_restrictionRamificationIdx hram
    rw [Set.mem_singleton_iff, ← hQ', h, restrictionDynamics_step, id_eq]
  · rintro rfl
    exact ⟨zeroPrime, rfl,
        by rw [restrictionDynamics_ramificationIdx, restrictionRamificationIdx_of_eq rfl]; omega⟩

/-- **The restricted system really ramifies.** This is what makes the witness
non-vacuous. -/
theorem restrictionDynamics_branch_nonempty : restrictionDynamics.branch.Nonempty :=
  ⟨zeroPrime, by rw [restrictionDynamics_branch]; rfl⟩

/-- **The payoff.** The restricted system is post-critically finite, obtained by *applying*
Theorem `thm:normal-invariant` (`Pcf.PCFGeometry.restriction_isPCF`) to the witness — not by
reproving it.

Together with `Pcf.Examples.restrictionDynamics_branch_nonempty` this says: `Pcf.PCFGeometry` is
inhabited, the inhabitant has a nonempty restricted branch divisor, and Theorem
`thm:normal-invariant` fires on
it.  A second proof, through the purity wiring, is `restrictionDynamicsOfPurity_isPCF`. -/
theorem restrictionDynamics_isPCF : restrictionDynamics.IsPCF :=
  cofiniteGeometry.restriction_isPCF
      (fun m Q hs _ => notMem_branch_iterate_restrictionDynamics m Q fun h => hs (Or.inl h))
          ambientDynamics_isPCF

#print axioms isProperIrreducibleClosed_iff_singleton
#print axioms noetherianSpace_cofiniteNat
#print axioms cofiniteGeometry
#print axioms restrictionDynamics_branch
#print axioms restrictionDynamics_branch_nonempty
#print axioms restrictionDynamics_isPCF

/-! ### The same witness, with `step_image_ramified_finite` derived from purity

`Pcf/Wiring.lean` routes the geometric input to Theorem `thm:normal-invariant` through a
`Pcf.PurityData`, so
that `Pcf.DivisorDynamics.step_image_ramified_finite` for the restricted system is *proved* rather
than supplied. This section exhibits an inhabitant of that route, so the wiring is not vacuous.

`restrictionDynamics` above supplies `step_image_ramified_finite` by hand.
`restrictionDynamicsOfPurity` below does not: it is built by
`Pcf.restrictionDivisorDynamicsOfPurity`, whose `step_image_ramified_finite` comes from the
non-étale locus being a proper closed subset of a Noetherian space. -/

/-- A purity datum on `CofiniteNat` with non-étale locus `{0}`.

Every point has codimension one here, so `Pcf.localPurity_of_codim_le_one` supplies the
`localPurity` field with no purity input at all — which is exactly the phenomenon that
lemma records. Nothing about Zariski–Nagata is exercised; what is exercised is the
*finiteness* half of the wiring. -/
noncomputable def cofinitePurityData : PurityData CofiniteNat :=
  PurityData.ofCodimLeOne (fun _ => 1) {zeroPoint}
    (isClosed_cofiniteNat_iff.mpr (Or.inr (Set.finite_singleton zeroPoint)))
    (ne_univ_of_finite (Set.finite_singleton zeroPoint))
    (fun _ h => absurd h (by omega))
    (fun _ _ => le_refl 1)

@[simp] theorem cofinitePurityData_nonEtale : cofinitePurityData.nonEtale = {zeroPoint} := rfl

/-- Ramified primes of the restricted system land in the non-étale locus. -/
theorem restrictionRamificationIdx_branch_subset
    (Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s})
        (h : 1 < restrictionRamificationIdx Q) :
    ((id Q : {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s}) : Set CofiniteNat) ⊆
        cofinitePurityData.nonEtale := by
  rw [cofinitePurityData_nonEtale, id_eq, eq_zeroPrime_of_one_lt_restrictionRamificationIdx h]
  exact le_of_eq zeroPrime_coe

/-- The restricted system with `step_image_ramified_finite` **proved** from the purity datum: a
second construction of `restrictionDynamics` (same data; the proof field comes from
`Pcf.restrictionDivisorDynamicsOfPurity` instead of being supplied by hand). -/
noncomputable def restrictionDynamicsOfPurity : DivisorDynamics
    {s : Set CofiniteNat // Pcf.IsProperIrreducibleClosed s} :=
  restrictionDivisorDynamicsOfPurity id restrictionRamificationIdx restrictionRamificationIdx_pos
      Function.surjective_id cofinitePurityData
    restrictionRamificationIdx_branch_subset

@[simp] theorem restrictionDynamicsOfPurity_step : restrictionDynamicsOfPurity.step = id := rfl

@[simp] theorem restrictionDynamicsOfPurity_ramificationIdx :
    restrictionDynamicsOfPurity.ramificationIdx = restrictionRamificationIdx := rfl

/-- It is the same system as `restrictionDynamics`: only the *provenance* of
`step_image_ramified_finite` differs, and `DivisorDynamics` is a structure whose proof fields are
propositions. -/
theorem restrictionDynamicsOfPurity_branch : restrictionDynamicsOfPurity.branch = {zeroPrime} := by
  rw [show restrictionDynamicsOfPurity.branch = restrictionDynamics.branch from rfl]
  exact restrictionDynamics_branch

/-- **The payoff.** The restricted system is post-critically finite: a second proof of
`restrictionDynamics_isPCF`, obtained by applying
`Pcf.PCFGeometry.restriction_isPCF` to a `Pcf.PCFGeometry` whose restricted system's
branch-finiteness was derived from purity rather than assumed. -/
theorem restrictionDynamicsOfPurity_isPCF : restrictionDynamicsOfPurity.IsPCF := by
  refine PCFGeometry.restriction_isPCF_of_purityData ambientDynamics () rfl id
      restrictionRamificationIdx restrictionRamificationIdx_pos
    Function.surjective_id cofinitePurityData restrictionRamificationIdx_branch_subset {zeroPoint} ∅
    (fun _ => ∅)
    (isClosed_cofiniteNat_iff.mpr (Or.inr (Set.finite_singleton zeroPoint)))
    (ne_univ_of_finite (Set.finite_singleton zeroPoint))
    isClosed_empty (ne_univ_of_finite Set.finite_empty)
    (fun _ _ => isClosed_empty) (fun _ _ => ne_univ_of_finite Set.finite_empty)
    ?_ ambientDynamics_isPCF
  intro m Q hs _
  exact notMem_branch_iterate_restrictionDynamics m Q fun h => hs (Or.inl h)

end Pcf.Examples
