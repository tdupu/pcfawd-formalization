/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Zariski--Nagata purity: TauCeti-facing statement

This module isolates the affine statement consumed by the PCFAWD development.  It is the
target to replace by a proof when the material is admitted to TauCeti; downstream files should
not manufacture a substitute interface.

## Stacks proof spine

The intended proof follows the Stacks Project literally, with one declaration (or a documented
Mathlib reuse) per tag.

* `0BMB`: the target, purity of the branch locus;
* `00PD`: the dimension-one regular-local/DVR case;
* `02VN`, `036W`: étale locality on the base and source;
* `02LK`: étale localization of a quasi-finite morphism;
* `00H8`, `0567`, `0AFS`, `00ON`: going down, regular implies normal, regularity under
  localization, and the local-dimension comparison;
* `0BMA`: purity for a punctured spectrum, the deep induction endpoint;
* `0BM9`, `031S`, `00R4`, `00HT`, `0BJH`, `0BJF`, `00NQ`, `0BLM`: the finite-étale,
  depth/Cohen--Macaulay, flatness, discriminant, and hyperplane-section inputs used by `0BMA`.

The pointwise `Prop` below is faithful to the affine specialization of `0BMB`, but it remains
an input: this file does not claim that the proof spine is implemented.  In particular,
Mathlib at the project pin does not yet expose the punctured-spectrum finite-étale machinery
used by `0BMA`.
-/

universe u

namespace Pcf.Stacks

/-- The pointwise hypotheses of Stacks Tag 0BMB for `Spec S → Spec R` at `w`.

The source local ring is a normal domain, the target local ring is regular, the map is
quasi-finite, the positive local dimensions agree, and the map is unramified at every
codimension-one generization of `w`. -/
structure ZariskiNagataPurityInputsAt
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

/-- The affine pointwise conclusion of Stacks Tag 0BMB. -/
def HasZariskiNagataPurityAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop :=
  ZariskiNagataPurityInputsAt R S w → Algebra.IsEtaleAt R w.asIdeal

/-- **Zariski--Nagata purity, Stacks Tag 0BMB**, specialized to affine schemes.

The explicit finite-type premise reflects the Stacks meaning of quasi-finite.  Local
normality, regularity, dimension, unramifiedness, and étaleness are represented by the
corresponding Mathlib predicates on the localizations.  This statement is faithful; it is
not yet proved in this repository. -/
def ZariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
  ∀ w : PrimeSpectrum S, HasZariskiNagataPurityAt R S w

/-- An étale algebra satisfies the affine purity conclusion at every point.  This sanity
check shows that the input is about the ambient cover and contains no divisor-specific PCF
conclusion. -/
theorem ZariskiNagataPurity.of_etale
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : ZariskiNagataPurity R S :=
  fun _ _ _ w _ =>
    inferInstanceAs (Algebra.FormallyEtale R (Localization.AtPrime w.asIdeal))

end Pcf.Stacks
