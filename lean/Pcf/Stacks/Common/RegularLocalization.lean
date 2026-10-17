/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Vendor.RegularLocalization.Localization

/-!
# Localizations of regular local rings (Stacks Tag 0AFS)

Stacks Project Lemma 10.110.6 (Tag `0AFS`): a Noetherian local ring is regular if and only if it
has finite global dimension; in that case every localization at a prime is regular.

The proofs are the Auslander–Buchsbaum–Serre theory of mathlib4 PR #29802 (Nailin Guan), vendored
under `Pcf.Vendor.RegularLocalization`. This file restates the pcf-facing consequences:

* `Pcf.Stacks.isRegularLocalRing_iff_globalDimension_lt_top` : the first sentence of `0AFS`;
* `Pcf.Stacks.isRegularLocalRing_localization_atPrime` : the second sentence of `0AFS`;
* `Pcf.Stacks.IsRegularLocalRing.of_isLocalization_atPrime` : the same for any
  `IsLocalization.AtPrime`;
* `Pcf.Stacks.isRegularRing_of_isRegularLocalRing` : a regular local ring is a regular ring in
  Mathlib's sense (every localization at a prime is regular local).

None of these is a global instance (instance hygiene: Mathlib already has the low-priority
instance `IsRegularRing → IsRegularLocalRing (Localization.AtPrime p)`). Downstream files can opt
in with the scoped instances in the namespace `Pcf.Stacks.RegularLocalization`.

## Global instances from the vendored code

Importing this file brings the global (not scoped) instances of the vendored PR #29802 into
scope; the vendored copy keeps them as the PR declares them:

* `IsRegularLocalRing R → IsDomain R` (`Pcf.Vendor.RegularLocalization.RegularLocalRingBasic`,
  priority lowered to `low` by pcf), so every importer finds `IsDomain` for a regular local ring
  by instance search; the explicit `isDomain_of_isRegularLocalRing` still works;
* `Nontrivial M` for a maximal Cohen–Macaulay module `M`, priority `low`
  (`Pcf.Vendor.RegularLocalization.MaximalCohenMacaulay`);
* `ModuleCat.IsCohenMacaulay (ModuleCat.of R R)` for a Cohen–Macaulay local ring `R`
  (`Pcf.Vendor.RegularLocalization.CohenMacaulay`).

All three conclude a proposition, so they cannot create data diamonds with Mathlib; they
disappear when the PR lands and the vendored copy is removed.
-/

@[expose] public section

universe u v

namespace Pcf.Stacks

/-- **Stacks Project Tag 0AFS, first sentence.** A Noetherian local ring is a regular local ring
if and only if it has finite global dimension.

Divergence from Stacks: the global dimension is computed in `ModuleCat.{v} R` for an auxiliary
universe `v` with `Small.{v} R`; the statement holds for every such `v`. -/
@[stacks 0AFS "first sentence"]
theorem isRegularLocalRing_iff_globalDimension_lt_top (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Small.{v} R] :
    IsRegularLocalRing R ↔ Pcf.Vendor.globalDimension.{v} R < ⊤ :=
  Pcf.Vendor.Auslander_Buchsbaum_Serre R

/-- **Stacks Project Tag 0AFS, second sentence.** The localization of a regular local ring at a
prime ideal is a regular local ring. -/
@[stacks 0AFS "second sentence"]
theorem isRegularLocalRing_localization_atPrime (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) :=
  Pcf.Vendor.isRegularLocalRing_localization R p

/-- **Stacks Project Tag 0AFS, second sentence**, for an arbitrary localization at a prime. -/
@[stacks 0AFS "second sentence, any `IsLocalization.AtPrime`"]
theorem IsRegularLocalRing.of_isLocalization_atPrime (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p] : IsRegularLocalRing S :=
  Pcf.Vendor.IsRegularLocalRing.of_isLocalization R p S

/-- A regular local ring is a regular ring in Mathlib's sense: all its localizations at primes
are regular local rings. This is a restatement of the second sentence of Stacks Tag 0AFS in
terms of Mathlib's `IsRegularRing`. -/
@[stacks 0AFS "second sentence, as `IsRegularRing`"]
theorem isRegularRing_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R :=
  Pcf.Vendor.isRegularRing_of_isRegularLocalRing R

namespace RegularLocalization

/-- Opt-in instance: `open scoped Pcf.Stacks.RegularLocalization`. -/
scoped instance (priority := low) instIsRegularLocalRingLocalizationAtPrime (R : Type u)
    [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_localization_atPrime R p

/-- Opt-in instance: `open scoped Pcf.Stacks.RegularLocalization`. -/
scoped instance (priority := low) instIsRegularRingOfIsRegularLocalRing (R : Type u)
    [CommRing R] [IsRegularLocalRing R] : IsRegularRing R :=
  isRegularRing_of_isRegularLocalRing R

end RegularLocalization

end Pcf.Stacks
