/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Wiring
import Mathlib.Topology.Sober

/-!
# A divisorial system on `Spec S`, with `branch_finite'` and `hbranch` both discharged

`Pcf/Wiring.lean` derives `Pcf.DivDyn.branch_finite'` for the restricted system from a
`Pcf.PurityData`, but it still *assumes* `ramified_subset_nonEtale`: that a prime over
which the system ramifies lies in the non-étale locus. That hypothesis is Definition 2.3 of
`latex/pcf.tex` read in the direction the argument needs, and in the abstract layer there
is nothing to prove it from.

Over an honest algebra there is. This file instantiates the dynamics at `Spec S` with the
ramification index taken to be Mathlib's `Ideal.ramificationIdx` at the generic point, and
then **both** hypotheses become theorems:

* `ramified ⟹ non-étale` is `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx`, which comes
  from `Ideal.ramificationIdx_eq_one` together with "étale implies unramified";
* `branch_finite'` follows, because the ramified primes then lie in a proper closed subset
  of a Noetherian space, which contains only finitely many primes, and the branch set is
  their image.

What the caller must still supply is the dynamics itself — a self-map `step` of the primes
and its surjectivity (lying over) — and **generic étaleness**, `nonEtaleLocus R S ≠ univ`,
which is the separability hypothesis of §2 and is a genuine condition on `S`.

## Why generic points

`Pcf.IsPrime` is a property of *closed subsets*, while `Ideal.ramificationIdx` is attached
to a *point* of `Spec S`. `PrimeSpectrum` is a sober space, so an irreducible closed subset
has a generic point and is the closure of it; `Pcf.specRam` uses that to read an index off
a prime, and `Pcf.subset_nonEtaleLocus_of_one_lt_specRam` transports membership back from
the point to the whole subset using closedness of the locus.

## What this does *not* do

It does not prove Zariski–Nagata purity, and it does not touch Proposition 4.1(2). It
removes one hypothesis — the definitional compatibility between ramification and
non-étaleness — from the list a caller must supply on this route, and nothing else. See
`lean/AXIOMS.md` §B.7.
-/

namespace Pcf

open Set TopologicalSpace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-! ### Reading a ramification index off a prime -/

/-- The ramification index of a prime of `Spec S`, in the sense of Definition 2.2's
divisorial bookkeeping: `Ideal.ramificationIdx` at the generic point of the prime. -/
noncomputable def specRam (R : Type*) [CommRing R] [Algebra R S]
    (Q : {s : Set (PrimeSpectrum S) // IsPrime s}) : ℕ :=
  Ideal.ramificationIdx (Q.2.irreducible.genericPoint).asIdeal R

theorem specRam_pos [Module.Finite R S]
    (Q : {s : Set (PrimeSpectrum S) // IsPrime s}) : 0 < specRam R Q := by
  have := (Q.2.irreducible.genericPoint (α := PrimeSpectrum S)).isPrime
  exact Ideal.ramificationIdx_pos _ R

/-- **`hbranch`, discharged.** A prime of `Spec S` over which the system ramifies is
contained in the non-étale locus.

The generic point is non-étale by `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx`, the
locus is closed, and the prime is the closure of its generic point. -/
theorem subset_nonEtaleLocus_of_one_lt_specRam [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] (Q : {s : Set (PrimeSpectrum S) // IsPrime s})
    (h : 1 < specRam R Q) : (Q : Set (PrimeSpectrum S)) ⊆ nonEtaleLocus R S := by
  have hclosure : closure ({Q.2.irreducible.genericPoint} : Set (PrimeSpectrum S))
      = (Q : Set (PrimeSpectrum S)) :=
    Q.2.irreducible.closure_genericPoint Q.2.isClosed
  rw [← hclosure]
  refine (isClosed_nonEtaleLocus R S).closure_subset_iff.mpr ?_
  exact singleton_subset_iff.mpr (mem_nonEtaleLocus_of_one_lt_ramificationIdx R S _ h)

/-! ### The system -/

/-- The ramified primes are finitely many: they lie in the non-étale locus, a proper closed
subset of a Noetherian space. -/
theorem finite_ramified [Algebra.EssFiniteType R S] [Algebra.FinitePresentation R S]
    [NoetherianSpace (PrimeSpectrum S)] (hgen : nonEtaleLocus R S ≠ univ) :
    {Q : {s : Set (PrimeSpectrum S) // IsPrime s} | 1 < specRam R Q}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine (finite_isPrime_subset (isClosed_nonEtaleLocus R S) hgen).subset ?_
  rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
  exact ⟨hQ, subset_nonEtaleLocus_of_one_lt_specRam ⟨Q, hQ⟩ h⟩

/-- **The divisorial system on `Spec S`, with both `branch_finite'` and the
ramified-implies-non-étale compatibility proved.**

The caller supplies the dynamics (`step`, and lying over) and generic étaleness. Compare
`Pcf.resDivDynOfPurity`, which additionally demands `ramified_subset_nonEtale`. -/
noncomputable def divDynOfSpectrum [Module.Finite R S] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (step : {s : Set (PrimeSpectrum S) // IsPrime s} → {s : Set (PrimeSpectrum S) // IsPrime s})
    (step_surjective : Function.Surjective step)
    (hgen : nonEtaleLocus R S ≠ univ) :
    DivDyn {s : Set (PrimeSpectrum S) // IsPrime s} where
  step := step
  ram := specRam R
  ram_pos := specRam_pos
  step_surjective := step_surjective
  branch_finite' := by
    refine ((finite_ramified hgen).image step).subset ?_
    rintro Q ⟨Q', rfl, hram⟩
    exact ⟨Q', hram, rfl⟩

@[simp] theorem divDynOfSpectrum_step [Module.Finite R S] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (step) (step_surjective) (hgen : nonEtaleLocus R S ≠ univ) :
    (divDynOfSpectrum step step_surjective hgen).step = step := rfl

@[simp] theorem divDynOfSpectrum_ram [Module.Finite R S] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (step) (step_surjective) (hgen : nonEtaleLocus R S ≠ univ) :
    (divDynOfSpectrum step step_surjective hgen).ram = specRam R := rfl

end Pcf
