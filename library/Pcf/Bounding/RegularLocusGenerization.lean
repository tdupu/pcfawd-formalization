/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FiniteTypeRegularLocus
public import Pcf.Vendor.RegularLocalization.Localization

/-!
# Regular loci are stable under generalization

This is the localization input to the J-2 theorem used in `paper-p.tex`,
Theorem `thm:bounding`, Step 0. It does not by itself prove that the regular
locus of a finite-type scheme is open. The latter is Stacks Project Tag
`07R5`, and requires a principal regular neighborhood at each regular point.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- If `p ⊆ q` and `R_q` is regular, then `R_p` is regular. This is
Stacks Project Tag `0AFS`, second sentence, applied to the localization
of `R_q` at the prime above `p`. -/
@[stacks 0AFS "regularity under generalization"]
theorem isRegularLocalRing_atPrime_of_le
    {R : Type u} [CommRing R] (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q)
    (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let S := Localization.AtPrime q
  let P := p.map (algebraMap R S)
  letI : P.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime q hpq
  letI : IsRegularLocalRing S := hq
  have hP : IsRegularLocalRing (Localization.AtPrime P) :=
    Pcf.Vendor.isRegularLocalRing_localization S P
  have hunder : P.comap (algebraMap R S) = p := by
    simpa only [Ideal.under_def] using
      (Ideal.under_map_of_isLocalizationAtPrime q hpq)
  have h := (isRegularLocalRing_localizationAtPrime_iff q.primeCompl S P).mp hP
  let p' : PrimeSpectrum R := ⟨P.comap (algebraMap R S), inferInstance⟩
  have hp' : p' = ⟨p, inferInstance⟩ := PrimeSpectrum.ext hunder
  let regularAt (r : PrimeSpectrum R) : Prop :=
    IsRegularLocalRing (Localization.AtPrime r.asIdeal)
  have ht : regularAt p' := h
  have ht2 : regularAt ⟨p, inferInstance⟩ := hp' ▸ ht
  exact ht2

/-- If a point of `Spec R` is regular, every generalization is regular.
The finite-type J-2 theorem still needs openness, a stronger statement. -/
theorem primeRegularLocus_generization_closed
    (R : Type u) [CommRing R]
    (p q : PrimeSpectrum R) (hpq : p.asIdeal ≤ q.asIdeal)
    (hq : q ∈ primeRegularLocus R) :
    p ∈ primeRegularLocus R := by
  exact isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq

/-- The affine singular locus is stable under specialization. This is one
topological half of closedness; a specialization-stable subset of a
Noetherian spectrum need not itself be closed. -/
theorem primeSingularLocus_specialization_closed
    (R : Type u) [CommRing R]
    (p q : PrimeSpectrum R) (hpq : p.asIdeal ≤ q.asIdeal)
    (hp : p ∈ (primeRegularLocus R)ᶜ) :
    q ∈ (primeRegularLocus R)ᶜ :=
  fun hq => hp (primeRegularLocus_generization_closed R p q hpq hq)

/-- A regular stalk stays regular under generization on any scheme. This
is the scheme-level form of the localization argument. -/
theorem isRegularLocalRing_stalk_of_specializes
    {X : Scheme.{u}} {d E : X} (h : d ⤳ E)
    (hE : IsRegularLocalRing (X.presheaf.stalk E)) :
    IsRegularLocalRing (X.presheaf.stalk d) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hEU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ E) isOpen_univ
  have hdU : d ∈ U := h.mem_open U.isOpen hEU
  let pD := (hU.primeIdealOf ⟨d, hdU⟩).asIdeal
  let pE := (hU.primeIdealOf ⟨E, hEU⟩).asIdeal
  have hDE : pD ≤ pE := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mpr
    exact ((subtype_specializes_iff _ _).mpr h).map hU.isoSpec.hom.continuous
  have hregE : IsRegularLocalRing (Localization.AtPrime pE) := by
    letI : Algebra Γ(X, U) (X.presheaf.stalk E) :=
      X.presheaf.algebra_section_stalk ⟨E, hEU⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk E) pE :=
      hU.isLocalization_stalk ⟨E, hEU⟩
    exact (isRegularLocalRing_iff_of_ringEquiv
      (IsLocalization.algEquiv pE.primeCompl
        (Localization.AtPrime pE) (X.presheaf.stalk E)).toRingEquiv).mpr hE
  have hregD : IsRegularLocalRing (Localization.AtPrime pD) :=
    isRegularLocalRing_atPrime_of_le pD pE hDE hregE
  letI : Algebra Γ(X, U) (X.presheaf.stalk d) :=
    X.presheaf.algebra_section_stalk ⟨d, hdU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk d) pD :=
    hU.isLocalization_stalk ⟨d, hdU⟩
  exact (isRegularLocalRing_iff_of_ringEquiv
    (IsLocalization.algEquiv pD.primeCompl
      (Localization.AtPrime pD) (X.presheaf.stalk d)).toRingEquiv).mp hregD

/-- On every scheme, the actual pointwise singular locus is stable under
specialization. Closedness for finite-type schemes over a field still
requires the J-2 theorem (Stacks Project Tag `07R5`). -/
theorem stalkSingularLocus_specialization_closed (X : Scheme.{u}) :
    StableUnderSpecialization (stalkSingularLocus X) := by
  intro d E h hd hregE
  exact hd (isRegularLocalRing_stalk_of_specializes h hregE)

#print axioms isRegularLocalRing_atPrime_of_le
#print axioms primeRegularLocus_generization_closed
#print axioms primeSingularLocus_specialization_closed
#print axioms isRegularLocalRing_stalk_of_specializes
#print axioms stalkSingularLocus_specialization_closed

end Pcf
