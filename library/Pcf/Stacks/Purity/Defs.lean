/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Zariski--Nagata purity: affine pointwise definitions

This file contains the stable statement layer for the affine specialization of Stacks Tag `0BMB`.
The proof components and their assembly live under `Pcf.Stacks.Purity`.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

/-- The pointwise hypotheses of Stacks Tag `0BMB` for `Spec S → Spec R` at `w`.

The source local ring is a normal domain, the target local ring is regular, the map is
quasi-finite, the positive local dimensions agree, and the map is unramified at every
codimension-one generization of `w`. -/
structure ZariskiNagataPurityHypothesesAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop where
  source_isDomain : IsDomain (Localization.AtPrime w.asIdeal)
  source_isIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime w.asIdeal)
  target_isRegular : IsRegularLocalRing (Localization.AtPrime (w.asIdeal.under R))
  quasiFinite : Algebra.QuasiFiniteAt R w.asIdeal
  equalDimension : w.asIdeal.height = (w.asIdeal.under R).height
  positiveDimension : 1 ≤ w.asIdeal.height
  unramifiedCodimensionOne :
    ∀ w' : PrimeSpectrum S, w' ⤳ w → w'.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w'.asIdeal

/-- The affine pointwise conclusion of Stacks Tag `0BMB`. -/
def HasZariskiNagataPurityAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop :=
  ZariskiNagataPurityHypothesesAt R S w → Algebra.IsEtaleAt R w.asIdeal

/-- **Zariski--Nagata purity, Stacks Tag `0BMB`**, specialized to affine schemes.

The explicit finite-type premise reflects the Stacks meaning of quasi-finite. Local normality,
regularity, dimension, unramifiedness, and étaleness are represented by the corresponding
Mathlib predicates on the localizations. This statement is faithful. -/
def ZariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
  ∀ w : PrimeSpectrum S, HasZariskiNagataPurityAt R S w

/-- An étale algebra satisfies the affine purity conclusion at every point. -/
theorem ZariskiNagataPurity.of_etale
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : ZariskiNagataPurity R S :=
  fun _ _ _ w _ ↦
    inferInstanceAs (Algebra.FormallyEtale R (Localization.AtPrime w.asIdeal))

end Pcf.Stacks
