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
under `Pcf.Vendor.RegularLocalization`; pcf uses the vendored statements directly, which carry
the Stacks tags (a pcf addition to the vendored copy).  This module re-exports them:

* `Pcf.Vendor.Auslander_Buchsbaum_Serre` : the first sentence of `0AFS` (the global dimension is
  computed in `ModuleCat.{v} R` for an auxiliary universe `v` with `Small.{v} R`; the statement
  holds for every such `v`);
* `Pcf.Vendor.isRegularLocalRing_localization` : the second sentence of `0AFS` (finite global
  dimension localizes, Algebra, Lemma 10.109.13, and Auslander–Buchsbaum–Serre converts back to
  regularity, as in Stacks);
* `Pcf.Vendor.IsRegularLocalRing.of_isLocalization` : the same for any `IsLocalization.AtPrime`;
* `Pcf.Vendor.isRegularRing_of_isRegularLocalRing` : a regular local ring is a regular ring in
  Mathlib's sense (every localization at a prime is regular local);
* `Pcf.Vendor.isDomain_of_isRegularLocalRing` : Stacks Tag `00NP`, a regular local ring is a
  domain.

None of the `0AFS` consequences is a global instance (instance hygiene: Mathlib already has the
low-priority instance `IsRegularRing → IsRegularLocalRing (Localization.AtPrime p)`).

## Global instances from the vendored code

Importing this file brings the global (not scoped) instances of the vendored PR #29802 into
scope; the vendored copy keeps them as the PR declares them:

* `IsRegularLocalRing R → IsDomain R` (`Pcf.Vendor.RegularLocalization.RegularLocalRingBasic`,
  priority lowered to `low` by pcf), so every importer finds `IsDomain` for a regular local ring
  by instance search; the explicit `Pcf.Vendor.isDomain_of_isRegularLocalRing` still works;
* `Nontrivial M` for a maximal Cohen–Macaulay module `M`, priority `low`
  (`Pcf.Vendor.RegularLocalization.MaximalCohenMacaulay`);
* `ModuleCat.IsCohenMacaulay (ModuleCat.of R R)` for a Cohen–Macaulay local ring `R`
  (`Pcf.Vendor.RegularLocalization.CohenMacaulay`).

All three conclude a proposition, so they cannot create data diamonds with Mathlib; they
disappear when the PR lands and the vendored copy is removed.
-/
