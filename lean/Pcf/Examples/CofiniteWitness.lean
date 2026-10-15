/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Geometry
public import Pcf.Wiring
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Irreducible

/-!
# A concrete, genuinely ramified witness for `Pcf.PcfGeometry`

`Pcf/Geometry.lean` derives Theorem `thm:normal-invariant` (`Pcf.PcfGeometry.res_pcf`) from a
structure `Pcf.PcfGeometry PX B` together with the bounding conclusion `key` as an explicit
argument. A reader is entitled to ask whether that structure is inhabited at all, and — more
sharply — whether it is inhabited by anything in which the *restricted* system actually
ramifies. If the only models had `res.branch = ∅`, Theorem `thm:normal-invariant` would be
true but empty on this route.

This file answers both questions with a single compiling instance.

## The space

The base space is `Pcf.Examples.CofNat`, namely `ℕ` carried by `CofiniteTopology`: a set
is open iff it is empty or has finite complement. Mathlib supplies its closed-set
description (`CofiniteTopology.isClosed_iff`) and its Noetherianness
(`instNoetherianSpaceCofiniteTopology`), and this file supplies the identification of
`Pcf.IsPrime`.

## What is established

* `Pcf.Examples.isClosed_cofNat_iff` — the closed sets are exactly the finite sets and
  the whole space.
* `Pcf.Examples.isPrime_iff_singleton` — `Pcf.IsPrime s ↔ ∃ x, s = {x}`. So the primes of
  this toy "variety" are its points, and there are plenty of them.
* `Pcf.Examples.noetherianSpace_cofNat` — the space is Noetherian, which is the hypothesis
  `Pcf.PcfGeometry.res_pcf` needs.
* `Pcf.Examples.cofiniteGeometry` — a `Pcf.PcfGeometry Unit CofNat`. The ambient system is
  trivial (identity step, no ramification, hence PCF); the restricted system has identity
  step and ramification index `2` at the prime `{0}` and `1` elsewhere; the correction
  locus `singAmbient` is `{0}`, so the ramified prime sits inside it, exactly as
  Theorem `thm:bounding` permits.
* `Pcf.Examples.resDyn_branch` — the restricted branch divisor is `{{0}}`, in particular
  **nonempty** (`Pcf.Examples.resDyn_branch_nonempty`). The witness is therefore not
  ramification-free.
* `Pcf.Examples.resDyn_pcf` — `res.PCF`, obtained by *applying* `Pcf.PcfGeometry.res_pcf`
  to the instance, not by reproving it.

## What is **not** established

This is a toy topological space, not a variety. `CofNat` is one-dimensional in the crude
sense that its proper closed subsets are finite, and its "primes" are points; there is no
scheme, no cover, no ring of functions, and nothing here is a model of an actual finite
separable self-map. The bounding conclusion `key` is discharged cheaply, because away from
`{0}` the restricted ramification index is literally `1`. No purity or Abhyankar input is
exercised: the index is known to be `1` by construction.

What the file does show is precisely this: `Pcf.PcfGeometry` is consistent, its fields can
be satisfied simultaneously, and they can be satisfied with `res.branch ≠ ∅`. That is the
non-vacuity claim, and no more.
-/

@[expose] public section

namespace Pcf.Examples

open Set TopologicalSpace

/-! ### The space: `ℕ` with the cofinite topology -/

/-- The toy base space: the natural numbers carried by the cofinite topology. -/
abbrev CofNat : Type := CofiniteTopology ℕ

instance : Infinite CofNat :=
  Infinite.of_injective CofiniteTopology.of CofiniteTopology.of.injective

/-- **Step 1.** The closed subsets of `CofNat` are exactly the finite sets together with
the whole space. This is Mathlib's `CofiniteTopology.isClosed_iff`, recorded here because
every argument below is an application of it. -/
theorem isClosed_cofNat_iff {s : Set CofNat} : IsClosed s ↔ s = univ ∨ s.Finite :=
  CofiniteTopology.isClosed_iff

/-- A finite subset of `CofNat` is a proper subset, since `CofNat` is infinite. -/
theorem ne_univ_of_finite {s : Set CofNat} (hs : s.Finite) : s ≠ univ := fun h =>
  Set.infinite_univ (h ▸ hs)

/-- A proper closed subset of `CofNat` is finite. -/
theorem finite_of_isClosed_of_ne_univ {s : Set CofNat} (hcl : IsClosed s) (hne : s ≠ univ) :
    s.Finite :=
  (isClosed_cofNat_iff.mp hcl).resolve_left hne

/-- In the cofinite topology a finite irreducible set has at most one point: if it had two,
`x` and `y`, it would be the union of the two proper closed subsets `{x}` and `s \ {x}`. -/
theorem subsingleton_of_isIrreducible_of_finite {s : Set CofNat} (hirr : IsIrreducible s)
    (hfin : s.Finite) : s.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hu : IsOpen ({x}ᶜ : Set CofNat) :=
    CofiniteTopology.isOpen_iff'.mpr (Or.inr (by simp))
  have hv : IsOpen ((s \ {x})ᶜ : Set CofNat) :=
    CofiniteTopology.isOpen_iff'.mpr (Or.inr (by simpa using hfin.sdiff))
  obtain ⟨z, hzs, hzu, hzv⟩ :=
    hirr.2 _ _ hu hv ⟨y, hy, fun h => hxy h.symm⟩ ⟨x, hx, fun h => h.2 rfl⟩
  exact hzv ⟨hzs, hzu⟩

/-! ### Step 2: the primes are the points -/

/-- **Step 2, one direction.** Every singleton is a prime of `CofNat`. -/
theorem isPrime_singleton (x : CofNat) : Pcf.IsPrime ({x} : Set CofNat) where
  irreducible := isIrreducible_singleton
  isClosed := isClosed_cofNat_iff.mpr (Or.inr (Set.finite_singleton x))
  ne_univ := ne_univ_of_finite (Set.finite_singleton x)
  maximal := by
    intro Q hQirr hQcl hQne hsub
    refine hsub.antisymm fun y hy => ?_
    have hfin := finite_of_isClosed_of_ne_univ hQcl hQne
    have := subsingleton_of_isIrreducible_of_finite hQirr hfin hy (hsub rfl)
    simpa using this

/-- **Step 2, the other direction.** Every prime of `CofNat` is a singleton: it is closed
and proper, hence finite, and finite irreducible sets are subsingletons. -/
theorem eq_singleton_of_isPrime {s : Set CofNat} (hs : Pcf.IsPrime s) : ∃ x, s = {x} := by
  obtain ⟨x, hx⟩ := hs.nonempty
  refine ⟨x, ?_⟩
  have hfin := finite_of_isClosed_of_ne_univ hs.isClosed hs.ne_univ
  exact (subsingleton_of_isIrreducible_of_finite hs.irreducible hfin).eq_singleton_of_mem hx

/-- **Step 2.** The primes of `CofNat`, in the sense of `Pcf.IsPrime`, are exactly its
points. In particular there are infinitely many of them. -/
theorem isPrime_iff_singleton {s : Set CofNat} : Pcf.IsPrime s ↔ ∃ x, s = {x} :=
  ⟨eq_singleton_of_isPrime, by rintro ⟨x, rfl⟩; exact isPrime_singleton x⟩

/-! ### Step 3: Noetherianness -/

/-- **Step 3.** `CofNat` is a Noetherian space — the hypothesis under which
`Pcf.PcfGeometry.res_pcf` is stated. Descending chains of closed sets are eventually
chains of finite sets, so they stabilize; Mathlib already knows this for the cofinite
topology. -/
theorem noetherianSpace_cofNat : NoetherianSpace CofNat := inferInstance

/-! ### Step 4: the geometry -/

/-- The point `0`, whose prime `{0}` is where the restricted system will ramify. -/
def pt : CofNat := CofiniteTopology.of 0

/-- The prime `{0}` of `CofNat`. -/
def zeroPrime : {s : Set CofNat // Pcf.IsPrime s} := ⟨{pt}, isPrime_singleton pt⟩

@[simp] theorem zeroPrime_coe : (zeroPrime : Set CofNat) = {pt} := rfl

/-- The ambient system: one prime, identity step, no ramification. -/
def ambDyn : DivDyn Unit where
  step := id
  ram := fun _ => 1
  ram_pos := fun _ => Nat.one_pos
  step_surjective := Function.surjective_id
  branch_finite' := Set.toFinite _

/-- The ambient system is unramified. -/
theorem ambDyn_branch : ambDyn.branch = ∅ := by
  ext Q
  simp [DivDyn.branch, ambDyn]

/-- The ambient system is post-critically finite — trivially, since it has one prime. -/
theorem ambDyn_pcf : ambDyn.PCF := Set.toFinite _

/-- The ramification index of the restricted system: `2` at the prime `{0}`, `1`
elsewhere. -/
noncomputable def resRam (Q : {s : Set CofNat // Pcf.IsPrime s}) : ℕ :=
  letI := Classical.propDecidable ((Q : Set CofNat) = {pt})
  if (Q : Set CofNat) = {pt} then 2 else 1

theorem resRam_of_eq {Q : {s : Set CofNat // Pcf.IsPrime s}} (h : (Q : Set CofNat) = {pt}) :
    resRam Q = 2 := by
  simp [resRam, h]

theorem resRam_of_ne {Q : {s : Set CofNat // Pcf.IsPrime s}} (h : (Q : Set CofNat) ≠ {pt}) :
    resRam Q = 1 := by
  simp [resRam, h]

theorem resRam_pos (Q : {s : Set CofNat // Pcf.IsPrime s}) : 0 < resRam Q := by
  by_cases h : (Q : Set CofNat) = {pt}
  · simp [resRam_of_eq h]
  · simp [resRam_of_ne h]

theorem eq_zeroPrime_of_one_lt_resRam {Q : {s : Set CofNat // Pcf.IsPrime s}}
    (h : 1 < resRam Q) : Q = zeroPrime := by
  by_cases hQ : (Q : Set CofNat) = {pt}
  · exact Subtype.ext hQ
  · rw [resRam_of_ne hQ] at h
    exact absurd h (by omega)

/-- The restricted system `g = f|_A`: identity step on the primes of `CofNat`, with
ramification index `2` at `{0}`. The branch set is the singleton `{{0}}`, so
`branch_finite'` holds. -/
noncomputable def resDyn : DivDyn {s : Set CofNat // Pcf.IsPrime s} where
  step := id
  ram := resRam
  ram_pos := resRam_pos
  step_surjective := Function.surjective_id
  branch_finite' := by
    refine (Set.finite_singleton zeroPrime).subset ?_
    rintro Q ⟨Q', hQ', hram⟩
    have : Q' = zeroPrime := eq_zeroPrime_of_one_lt_resRam hram
    simp only [Set.mem_singleton_iff, ← hQ', this, id_eq]

@[simp] theorem resDyn_step : resDyn.step = id := rfl

@[simp] theorem resDyn_ram : resDyn.ram = resRam := rfl

/-- Away from `{0}` the restricted system is unramified, in every iterate: the step map is
the identity, so the tower product is a product of copies of `1`. -/
theorem resDyn_iterRam_eq_one (m : ℕ) {Q : {s : Set CofNat // Pcf.IsPrime s}}
    (h : (Q : Set CofNat) ≠ {pt}) : resDyn.iterRam m Q = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [resDyn_step, Function.iterate_id, id_eq, resDyn_ram, resRam_of_ne h]

/-- The bounding conclusion for the witness: away from the prime `{0}` (which lies in
`singAmbient`) every iterate of the restricted system is unramified, so no good prime is a
branch prime. -/
theorem resDyn_key (m : ℕ) (Q : {s : Set CofNat // Pcf.IsPrime s})
    (hsa : ¬ ((Q : Set CofNat) ⊆ ({pt} : Set CofNat))) :
    Q ∉ (resDyn.iter m).branch := by
  rintro ⟨Q', hQ', hram⟩
  have hQeq : Q' = Q := by
    rw [DivDyn.iter_step, resDyn_step, Function.iterate_id, id_eq] at hQ'
    exact hQ'
  have hne : (Q' : Set CofNat) ≠ {pt} := by
    rw [hQeq]
    exact fun h => hsa (le_of_eq h)
  rw [DivDyn.iter_ram, resDyn_iterRam_eq_one m hne] at hram
  exact absurd hram (by omega)

/-- **The witness.** A `Pcf.PcfGeometry` on the cofinite space, with a trivial ambient
system and a restricted system that genuinely ramifies at the prime `{0}`.

The ramified prime lies in the correction locus `singAmbient = {0}`, which is exactly the
configuration Theorem `thm:bounding` allows: the proposition bounds ramification *away* from the
three loci, and says nothing inside them. -/
noncomputable def cofiniteGeometry : PcfGeometry Unit CofNat where
  amb := ambDyn
  fixedPrime := ()
  fixed := rfl
  res := resDyn
  singAmbient := {pt}
  singSelf := ∅
  meetsSet := fun _ => ∅
  singAmbient_isClosed := isClosed_cofNat_iff.mpr (Or.inr (Set.finite_singleton pt))
  singAmbient_ne_univ := ne_univ_of_finite (Set.finite_singleton pt)
  singSelf_isClosed := isClosed_empty
  singSelf_ne_univ := ne_univ_of_finite Set.finite_empty
  meetsSet_isClosed := fun _ _ => isClosed_empty
  meetsSet_ne_univ := fun _ _ => ne_univ_of_finite Set.finite_empty

/-! ### Step 5: the payoff -/

/-- The restricted branch divisor is exactly `{{0}}`. -/
theorem resDyn_branch : resDyn.branch = {zeroPrime} := by
  ext Q
  constructor
  · rintro ⟨Q', hQ', hram⟩
    have h : Q' = zeroPrime := eq_zeroPrime_of_one_lt_resRam hram
    rw [Set.mem_singleton_iff, ← hQ', h, resDyn_step, id_eq]
  · rintro rfl
    exact ⟨zeroPrime, rfl, by rw [resDyn_ram, resRam_of_eq rfl]; omega⟩

/-- **The restricted system really ramifies.** This is what makes the witness
non-vacuous. -/
theorem resDyn_branch_nonempty : resDyn.branch.Nonempty :=
  ⟨zeroPrime, by rw [resDyn_branch]; rfl⟩

/-- **The payoff.** The restricted system is post-critically finite, obtained by *applying*
Theorem `thm:normal-invariant` (`Pcf.PcfGeometry.res_pcf`) to the witness — not by reproving it.

Together with `Pcf.Examples.resDyn_branch_nonempty` this says: `Pcf.PcfGeometry` is
inhabited, the inhabitant has a nonempty restricted branch divisor, and Theorem
`thm:normal-invariant` fires on
it. -/
theorem resDyn_pcf : resDyn.PCF :=
  cofiniteGeometry.res_pcf (fun m Q hs _ => resDyn_key m Q fun h => hs (Or.inl h)) ambDyn_pcf

#print axioms isPrime_iff_singleton
#print axioms noetherianSpace_cofNat
#print axioms cofiniteGeometry
#print axioms resDyn_branch
#print axioms resDyn_branch_nonempty
#print axioms resDyn_pcf

/-! ### The same witness, with `branch_finite'` derived from purity

`Pcf/Wiring.lean` routes the geometric input to Theorem `thm:normal-invariant` through a
`Pcf.PurityData`, so
that `Pcf.DivDyn.branch_finite'` for the restricted system is *proved* rather than supplied.
This section exhibits an inhabitant of that route, so the wiring is not vacuous.

`resDyn` above supplies `branch_finite'` by hand. `resDynOfPurity` below does not: it is
built by `Pcf.resDivDynOfPurity`, whose `branch_finite'` comes from the non-étale locus
being a proper closed subset of a Noetherian space. -/

/-- A purity datum on `CofNat` with non-étale locus `{0}`.

Every point has codimension one here, so `Pcf.localPurity_of_codim_le_one` supplies the
`localPurity` field with no purity input at all — which is exactly the phenomenon that
lemma records. Nothing about Zariski–Nagata is exercised; what is exercised is the
*finiteness* half of the wiring. -/
noncomputable def cofinitePurityData : PurityData CofNat :=
  PurityData.ofCodimLeOne (fun _ => 1) {pt}
    (isClosed_cofNat_iff.mpr (Or.inr (Set.finite_singleton pt)))
    (ne_univ_of_finite (Set.finite_singleton pt))
    (fun _ h => absurd h (by omega))
    (fun _ _ => le_refl 1)

@[simp] theorem cofinitePurityData_nonEtale : cofinitePurityData.nonEtale = {pt} := rfl

/-- Ramified primes of the restricted system land in the non-étale locus. -/
theorem resRam_branch_subset (Q : {s : Set CofNat // Pcf.IsPrime s}) (h : 1 < resRam Q) :
    ((id Q : {s : Set CofNat // Pcf.IsPrime s}) : Set CofNat) ⊆ cofinitePurityData.nonEtale := by
  rw [cofinitePurityData_nonEtale, id_eq, eq_zeroPrime_of_one_lt_resRam h]
  exact le_of_eq zeroPrime_coe

/-- The restricted system with `branch_finite'` **proved** from the purity datum. -/
noncomputable def resDynOfPurity : DivDyn {s : Set CofNat // Pcf.IsPrime s} :=
  resDivDynOfPurity id resRam resRam_pos Function.surjective_id cofinitePurityData
    resRam_branch_subset

@[simp] theorem resDynOfPurity_step : resDynOfPurity.step = id := rfl

@[simp] theorem resDynOfPurity_ram : resDynOfPurity.ram = resRam := rfl

/-- It is the same system as `resDyn`: only the *provenance* of `branch_finite'` differs,
and `DivDyn` is a structure whose proof fields are propositions. -/
theorem resDynOfPurity_branch : resDynOfPurity.branch = {zeroPrime} := by
  rw [show resDynOfPurity.branch = resDyn.branch from rfl]
  exact resDyn_branch

/-- **The payoff.** The restricted system is post-critically finite, obtained by applying
`Pcf.PcfGeometry.res_pcf` to a `Pcf.PcfGeometry` whose restricted system's branch-finiteness
was derived from purity rather than assumed. -/
theorem resDynOfPurity_pcf : resDynOfPurity.PCF := by
  refine PcfGeometry.res_pcf_of_purityData ambDyn () rfl id resRam resRam_pos
    Function.surjective_id cofinitePurityData resRam_branch_subset {pt} ∅
    (fun _ => ∅)
    (isClosed_cofNat_iff.mpr (Or.inr (Set.finite_singleton pt)))
    (ne_univ_of_finite (Set.finite_singleton pt))
    isClosed_empty (ne_univ_of_finite Set.finite_empty)
    (fun _ _ => isClosed_empty) (fun _ _ => ne_univ_of_finite Set.finite_empty)
    ?_ ambDyn_pcf
  intro m Q hs _
  exact resDyn_key m Q fun h => hs (Or.inl h)

end Pcf.Examples
