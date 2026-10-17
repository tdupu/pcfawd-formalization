/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Purity
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The non-étale locus of an actual algebra, and two fields of `PurityData` discharged

`Pcf/Purity.lean` states the manuscript's purity argument over an abstract topological
space, with the ramification locus `E`, its closedness, its properness and the dimension
bookkeeping all carried as *fields* of `Pcf.PurityData`. That is enough to prove the
manuscript's local-to-global deduction, but it leaves a reader unable to tell whether the
fields are satisfiable by anything geometric.

This file instantiates the abstraction at `Spec S` for an honest `R`-algebra `S`, and in
doing so **discharges two of the four assumed fields**:

* `nonEtale_isClosed` — because Mathlib proves the étale locus is *open*
  (`Algebra.isOpen_etaleLocus`). This is the field `Pcf.PurityData.notMem_nonEtale_of_specializes`
  actually consumes, so the discharge is load-bearing rather than decorative.
* `closure_eq_univ_of_codim_eq_zero` — because over a domain a prime of height zero is
  `⊥`, whose closure is all of `Spec S`.

The remaining two stay assumptions, and they are the mathematically substantial ones:

* `nonEtale_ne_univ` — that the morphism is *generically* étale. In the manuscript this is
  the separability of the function-field extension; it is a real hypothesis about `S`, not
  a formality.
* `localPurity` — **Zariski–Nagata purity itself** (Stacks Tag 0BMB). Mathlib does not
  have it. See `Pcf/ZariskiNagata.lean` for the statement in its faithful form.

## Main results

* `Pcf.isClosed_nonEtaleLocus` — the non-étale locus is closed. **Proved.**
* `Pcf.closure_eq_univ_of_primeSpectrumCodimension_eq_zero` — height-zero primes are generic.
  **Proved.**
* `Pcf.purityDataOfAlgebra` — the assembled `Pcf.PurityData (PrimeSpectrum S)`.
* `Pcf.codim_eq_one_of_algebra` — global purity on `Spec S`, i.e. `E` is pure of
  codimension one, from Tag 0BMB and generic étaleness and nothing else.
-/

@[expose] public section

namespace Pcf

open Algebra TopologicalSpace

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-! ### The locus -/

/-- The **non-étale locus** of `R → S`: the manuscript's ramification locus `E`, as a
subset of `Spec S`. -/
def nonEtaleLocus : Set (PrimeSpectrum S) := (Algebra.etaleLocus R S)ᶜ

theorem mem_nonEtaleLocus_iff {p : PrimeSpectrum S} :
    p ∈ nonEtaleLocus R S ↔ ¬ Algebra.IsEtaleAt R p.asIdeal := Iff.rfl

/-- **`PurityData.nonEtale_isClosed`, discharged.**

The manuscript says `E` is closed "because the étale locus is open". Mathlib proves that
— `Algebra.isOpen_etaleLocus`, via the étale locus being the complement of the supports of
`Ω` and `H¹` of the cotangent complex — so here it is a theorem rather than a hypothesis. -/
theorem isClosed_nonEtaleLocus [Algebra.FinitePresentation R S] :
    IsClosed (nonEtaleLocus R S) :=
  Algebra.isOpen_etaleLocus.isClosed_compl

/-! ### Ramified points are non-étale

Definition `def:crit-branch` of `latex/paper.tex` says the branch divisor is where the cover
ramifies, and
§`sec:bounding` uses that a ramified point is a non-étale point. In the abstract layer that
implication
is a *hypothesis* (`hbranch` in `Pcf.divisorDynamicsOfGeometry`, `ramified_subset_nonEtale` in
`Pcf/Wiring.lean`). Over an honest algebra it is a **theorem**, because Mathlib's
`Ideal.ramificationIdx_eq_one` derives index `1` from unramifiedness and étale implies
unramified. -/

/-- **Ramified implies non-étale.** A prime of `Spec S` whose ramification index over `R`
exceeds `1` lies in the non-étale locus.

This is the content of the `hbranch` hypothesis, proved rather than assumed. -/
theorem mem_nonEtaleLocus_of_one_lt_ramificationIdx [Algebra.EssFiniteType R S]
    (q : PrimeSpectrum S) (h : 1 < Ideal.ramificationIdx q.asIdeal R) :
    q ∈ nonEtaleLocus R S := by
  have := q.isPrime
  intro hq
  have hetale : Algebra.IsEtaleAt R q.asIdeal := hq
  have : Algebra.IsUnramifiedAt R q.asIdeal := inferInstance
  have h1 := Ideal.ramificationIdx_eq_one q.asIdeal R
  omega

/-- The converse: an étale point is unramified in the sense of `Ideal.ramificationIdx`. -/
theorem ramificationIdx_eq_one_of_notMem_nonEtaleLocus [Algebra.EssFiniteType R S]
    (q : PrimeSpectrum S) (h : q ∉ nonEtaleLocus R S) :
    Ideal.ramificationIdx q.asIdeal R = 1 := by
  have := q.isPrime
  have hetale : Algebra.IsEtaleAt R q.asIdeal := not_not.mp h
  have : Algebra.IsUnramifiedAt R q.asIdeal := inferInstance
  exact Ideal.ramificationIdx_eq_one q.asIdeal R

/-! ### Codimension -/

/-- Codimension of a point of `Spec S`: the height of the corresponding prime.

`Ideal.height` takes values in `ℕ∞`; `Pcf.PurityData.codim` is `ℕ`-valued, so this
truncates. The truncation is harmless exactly when heights are finite, which is why
`Pcf.purityDataOfAlgebra` takes that as a hypothesis rather than hiding it: without it a
prime of infinite height would masquerade as one of codimension zero. -/
noncomputable def primeSpectrumCodimension (p : PrimeSpectrum S) : ℕ := (p.asIdeal.height).toNat

variable {S}

/-- **`PurityData.closure_eq_univ_of_codim_eq_zero`, discharged.**

Over a domain, a prime of height zero is `⊥`, and `V(⊥)` is everything: a codimension-zero
point of `Spec S` is the generic point. -/
theorem closure_eq_univ_of_primeSpectrumCodimension_eq_zero [IsDomain S] (p : PrimeSpectrum S)
    (hfin : p.asIdeal.height ≠ ⊤) (h : primeSpectrumCodimension S p = 0) :
    closure ({p} : Set (PrimeSpectrum S)) = Set.univ := by
  have h0 : p.asIdeal.height = 0 := by
    have := (ENat.toNat_eq_zero).mp h
    tauto
  have hbot : p.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h0
  rw [PrimeSpectrum.closure_singleton, hbot, PrimeSpectrum.zeroLocus_bot]

variable (S)

/-! ### The assembled datum -/

/-- The purity datum of `Pcf/Purity.lean`, instantiated at `Spec S` for an honest algebra.

Two fields are proved (`nonEtale_isClosed`, `closure_eq_univ_of_codim_eq_zero`); two are
supplied by the caller and are the substantial ones — generic étaleness, and
Zariski–Nagata purity itself. -/
noncomputable def purityDataOfAlgebra [IsDomain S] [Algebra.FinitePresentation R S]
    (hfin : ∀ p : PrimeSpectrum S, p.asIdeal.height ≠ ⊤)
    (hgen : nonEtaleLocus R S ≠ Set.univ)
    (hloc : ∀ x : PrimeSpectrum S, 1 ≤ primeSpectrumCodimension S x →
      (∀ x', x' ⤳ x → primeSpectrumCodimension S x' = 1 → x' ∉ nonEtaleLocus R S) → x ∉
          nonEtaleLocus R S) :
    PurityData (PrimeSpectrum S) where
  codim := primeSpectrumCodimension S
  nonEtale := nonEtaleLocus R S
  nonEtale_isClosed := isClosed_nonEtaleLocus R S
  nonEtale_ne_univ := hgen
  closure_eq_univ_of_codim_eq_zero := fun x hx =>
    closure_eq_univ_of_primeSpectrumCodimension_eq_zero x (hfin x) hx
  localPurity := hloc

/-- The non-étale locus is empty exactly when the algebra is étale. -/
theorem nonEtaleLocus_eq_empty_iff [Algebra.FinitePresentation R S] :
    nonEtaleLocus R S = ∅ ↔ Algebra.Etale R S := by
  rw [nonEtaleLocus, Set.compl_empty_iff, Algebra.etaleLocus_eq_univ_iff_etale]

/-- **The datum is inhabited — degenerately.**

For an étale algebra the non-étale locus is empty, so all four fields hold and
`Pcf.purityDataOfAlgebra` is not unsatisfiable-by-construction.

That is *all* this shows. With `E = ∅` there are no irreducible components of `E`, so
`Pcf.codim_eq_one_of_algebra` has no instances and says nothing. **No example with
`E ≠ ∅` is provided in this development**, so the global purity statement is not exercised
non-trivially on any concrete algebra. Producing one would require a generically étale but
genuinely ramified extension together with a computation of its non-étale locus, which is
not done here. -/
noncomputable def purityDataOfEtale [IsDomain S]
    [Algebra.FinitePresentation R S] [Algebra.Etale R S]
    (hfin : ∀ p : PrimeSpectrum S, p.asIdeal.height ≠ ⊤) :
    PurityData (PrimeSpectrum S) :=
  have hempty : nonEtaleLocus R S = ∅ := (nonEtaleLocus_eq_empty_iff R S).mpr inferInstance
  purityDataOfAlgebra R S hfin (by rw [hempty]; exact Set.empty_ne_univ)
    (fun _ _ _ => by rw [hempty]; exact Set.notMem_empty _)

/-- **Zariski–Nagata purity, global form, on the spectrum of an actual algebra.**

Every irreducible component of the non-étale locus has a codimension-one generic point.
The only inputs are the local form of purity (Stacks Tag 0BMB) and generic étaleness;
closedness of `E` and the identification of codimension-zero points are now theorems. -/
theorem codim_eq_one_of_algebra [IsDomain S] [Algebra.FinitePresentation R S]
    (hfin : ∀ p : PrimeSpectrum S, p.asIdeal.height ≠ ⊤)
    (hgen : nonEtaleLocus R S ≠ Set.univ)
    (hloc : ∀ x : PrimeSpectrum S, 1 ≤ primeSpectrumCodimension S x →
      (∀ x', x' ⤳ x → primeSpectrumCodimension S x' = 1 → x' ∉ nonEtaleLocus R S) → x ∉
          nonEtaleLocus R S)
    {E₀ : Set (PrimeSpectrum S)}
    (hE₀ : (purityDataOfAlgebra R S hfin hgen hloc).IsComponent E₀)
    {η : PrimeSpectrum S} (hη : closure ({η} : Set (PrimeSpectrum S)) = E₀) :
    primeSpectrumCodimension S η = 1 :=
  PurityData.codim_eq_one hE₀ hη

/-- **Finiteness of the branch divisor on `Spec S`.** For `S` Noetherian the non-étale
locus, being a proper closed subset, contains only finitely many primes in the sense of
`Pcf.IsProperIrreducibleClosed`. -/
theorem finite_isProperIrreducibleClosed_subset_nonEtaleLocus [IsNoetherianRing S]
    [Algebra.FinitePresentation R S] (hgen : nonEtaleLocus R S ≠ Set.univ) :
    {P : Set (PrimeSpectrum S) | IsProperIrreducibleClosed P ∧ P ⊆ nonEtaleLocus R S}.Finite :=
  Pcf.finite_isProperIrreducibleClosed_subset (isClosed_nonEtaleLocus R S) hgen

end Pcf
