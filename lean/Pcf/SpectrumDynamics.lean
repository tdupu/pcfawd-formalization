/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Wiring
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Ring

/-!
# A divisorial system on `Spec S`, with `step_image_ramified_finite` and `hbranch` both discharged

`Pcf/Wiring.lean` derives `Pcf.DivisorDynamics.step_image_ramified_finite` for the restricted system
from a `Pcf.PurityData`, but it still *assumes* `ramified_subset_nonEtale`: that a prime over which
the system ramifies lies in the non-étale locus. That hypothesis is Definition `def:crit-branch` of
`latex/paper.tex` read in the direction the argument needs, and in the abstract layer there is
nothing to prove it from.

Over an honest algebra there is. This file instantiates the dynamics at `Spec S` with the
ramification index taken to be Mathlib's `Ideal.ramificationIdx` at the generic point, and
then **both** hypotheses become theorems:

* `ramified ⟹ non-étale` is `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx`, which comes
  from `Ideal.ramificationIdx_eq_one` together with "étale implies unramified";
* `step_image_ramified_finite` follows, because the ramified primes then lie in a proper closed
  subset
  of a Noetherian space, which contains only finitely many primes, and the branch set is
  their image.

What the caller must still supply is the dynamics itself — a self-map `step` of the primes
and its surjectivity (lying over) — and **generic étaleness**, `nonEtaleLocus R S ≠ univ`,
which is the separability hypothesis of §`sec:defs` and is a genuine condition on `S`.

## Why generic points

`Pcf.IsProperIrreducibleClosed` is a property of *closed subsets*, while `Ideal.ramificationIdx` is
attached to a *point* of `Spec S`. `PrimeSpectrum` is a sober space, so an irreducible closed subset
has a generic point and is the closure of it; `Pcf.primeSpectrumRamificationIdx` uses that to read
an index off a prime, and `Pcf.subset_nonEtaleLocus_of_one_lt_primeSpectrumRamificationIdx`
transports membership back from the point to the whole subset using closedness of the locus.

## What this does *not* do

It does not prove Zariski–Nagata purity, and it does not touch Theorem `thm:bounding` (per-divisor
form). It
removes one hypothesis — the definitional compatibility between ramification and
non-étaleness — from the list a caller must supply on this route, and nothing else. See
`lean/AXIOMS.md` §B.7.
-/

@[expose] public section

namespace Pcf

open Set TopologicalSpace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-! ### Reading a ramification index off a prime -/

/-- The ramification index of a prime of `Spec S`, in the sense of the ramification paragraph before
Definition `def:crit-branch`'s
divisorial bookkeeping: `Ideal.ramificationIdx` at the generic point of the prime. -/
noncomputable def primeSpectrumRamificationIdx (R : Type*) [CommRing R] [Algebra R S]
    (Q : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s}) : ℕ :=
  Ideal.ramificationIdx (Q.2.irreducible.genericPoint).asIdeal R

theorem primeSpectrumRamificationIdx_pos [Module.Finite R S]
    (Q : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s}) : 0 <
        primeSpectrumRamificationIdx R Q := by
  have := (Q.2.irreducible.genericPoint (α := PrimeSpectrum S)).isPrime
  exact Ideal.ramificationIdx_pos (R := R) _

/-- **`hbranch`, discharged.** A prime of `Spec S` over which the system ramifies is
contained in the non-étale locus.

The generic point is non-étale by `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx`, the
locus is closed, and the prime is the closure of its generic point. -/
theorem subset_nonEtaleLocus_of_one_lt_primeSpectrumRamificationIdx [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S]
        (Q : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s})
    (h : 1 < primeSpectrumRamificationIdx R Q) : (Q : Set (PrimeSpectrum S)) ⊆ nonEtaleLocus R S :=
        by
  have hclosure : closure ({Q.2.irreducible.genericPoint} : Set (PrimeSpectrum S))
      = (Q : Set (PrimeSpectrum S)) :=
    Q.2.irreducible.closure_genericPoint Q.2.isClosed
  rw [← hclosure]
  refine (isClosed_nonEtaleLocus R S).closure_subset_iff.mpr ?_
  exact singleton_subset_iff.mpr (mem_nonEtaleLocus_of_one_lt_ramificationIdx R S _ h)

/-! ### Lying over

`Pcf.DivisorDynamics.step_surjective` is census entry **B1** — "every prime is the image of a
prime", the lying-over/going-down step isolated inside the proof of Lemma `lem:lift`, and cited to
Stacks Tags 00HS / 00H8. Mathlib proves it, for an injective integral ring map. -/

omit [Algebra R S] in
/-- **Lying over** (Stacks Tag 00HS). For an injective integral ring map, the induced map
on prime spectra is surjective.

This is the mathematical content of `Pcf.DivisorDynamics.step_surjective`, which is assumed on every
route in this development. See the caveat on `Pcf.primeSpectrumSelfMap_surjective` for why proving
it here does not yet remove the field. -/
theorem comap_surjective_of_isIntegral_of_injective {φ : R →+* S}
    (hint : φ.IsIntegral) (hinj : Function.Injective φ) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  let := φ.toAlgebra
  have : Algebra.IsIntegral R S := ⟨fun x => hint x⟩
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  intro p
  have := p.isPrime
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver p.asIdeal S))
  exact ⟨⟨Q, hQp⟩, PrimeSpectrum.ext hQl.over.symm⟩

/-- The pushforward of points of `Spec S` along a ring endomorphism — the manuscript's
`P' ↦ g(P')` on points. -/
noncomputable def primeSpectrumSelfMap (φ : S →+* S) : PrimeSpectrum S → PrimeSpectrum S :=
  PrimeSpectrum.comap φ

/-- **`step_surjective` on points, proved.** A finite injective self-map of `Spec S` is
surjective on points.

**This does not yet discharge the field `Pcf.DivisorDynamics.step_surjective`.** That field is about
a self-map of *divisors* — elements of
`{s : Set (PrimeSpectrum S) // Pcf.IsProperIrreducibleClosed s}` — and transporting this statement
there needs two things this development does not have: that the image of a closed set under a finite
morphism is closed, and that such a morphism preserves codimension. The second is dimension theory
that Mathlib's Krull-dimension API does not currently reach. So B1 stands as an assumption, with its
content now identified and proved at the level where Mathlib can express it. -/
theorem primeSpectrumSelfMap_surjective (φ : S →+* S) (hint : φ.IsIntegral)
    (hinj : Function.Injective φ) :
    Function.Surjective (primeSpectrumSelfMap φ) :=
  comap_surjective_of_isIntegral_of_injective hint hinj

/-! ### The system -/

/-- The ramified primes are finitely many: they lie in the non-étale locus, a proper closed
subset of a Noetherian space. -/
theorem finite_ramified [Algebra.EssFiniteType R S] [Algebra.FinitePresentation R S]
    [NoetherianSpace (PrimeSpectrum S)] (hgen : nonEtaleLocus R S ≠ univ) :
    {Q : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s} | 1 <
        primeSpectrumRamificationIdx R Q}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine (finite_isProperIrreducibleClosed_subset (isClosed_nonEtaleLocus R S) hgen).subset ?_
  rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
  exact ⟨hQ, subset_nonEtaleLocus_of_one_lt_primeSpectrumRamificationIdx ⟨Q, hQ⟩ h⟩

/-- **The divisorial system on `Spec S`, with both `step_image_ramified_finite` and the
ramified-implies-non-étale compatibility proved.**

The caller supplies the dynamics (`step`, and lying over) and generic étaleness. Compare
`Pcf.restrictionDivisorDynamicsOfPurity`, which additionally demands `ramified_subset_nonEtale`. -/
noncomputable def divisorDynamicsOfSpectrum [Module.Finite R S] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (step : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s} →
        {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s})
    (step_surjective : Function.Surjective step)
    (hgen : nonEtaleLocus R S ≠ univ) :
    DivisorDynamics {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s} where
  step := step
  ramificationIdx := primeSpectrumRamificationIdx R
  ramificationIdx_pos := primeSpectrumRamificationIdx_pos
  step_surjective := step_surjective
  step_image_ramified_finite := by
    refine ((finite_ramified hgen).image step).subset ?_
    rintro Q ⟨Q', rfl, hram⟩
    exact ⟨Q', hram, rfl⟩

@[simp] theorem divisorDynamicsOfSpectrum_step [Module.Finite R S] [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (step) (step_surjective) (hgen : nonEtaleLocus R S ≠ univ) :
    (divisorDynamicsOfSpectrum step step_surjective hgen).step = step := rfl

@[simp] theorem divisorDynamicsOfSpectrum_ramificationIdx [Module.Finite R S]
    [Algebra.EssFiniteType R S]
    [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (step) (step_surjective) (hgen : nonEtaleLocus R S ≠ univ) :
    (divisorDynamicsOfSpectrum step step_surjective hgen).ramificationIdx =
        primeSpectrumRamificationIdx R := rfl

end Pcf
