/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.SchemeBridge

/-!
# Comparing divisor charts with actual affine stalk maps

Let `R → S` be the coordinate-ring map of an affine finite cover.  Suppose `D ⊆ q`
are prime ideals of `R`, while `P ⊆ Q` are prime ideals of `S`, with `Q` lying over
`q` and the pullback of `D` contained in `P`.  The local bounding chart is constructed
from `R_q`, the simultaneous localization `S_q`, and the extension of `P` to `S_q`.

This file proves the missing comparison with geometry: the local-ring map of the actual
affine quotient morphism

`Spec(S/P) → Spec(R/D)`

at the point `Q/P` is isomorphic, as an arrow of commutative rings, to the local-ring map
of the bounding chart at `(Q S_q)/(P S_q)`.  The proof uses only contraction of primes,
quotients of localizations, and the universal property of localization.  In particular,
it does not assume formal étaleness or any bounding conclusion.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Pcf

set_option linter.style.haveILetI false

private abbrev simultaneousLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime] :=
  Localization (Algebra.algebraMapSubmonoid S q.primeCompl)

private theorem disjoint_simultaneousLocalization_prime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) (Q : Ideal S) [q.IsPrime]
    (hQq : Q.under R = q) :
    Disjoint (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (Q : Set S) := by
  rw [Set.disjoint_left]
  rintro x ⟨r, hr, rfl⟩ hxQ
  exact hr (hQq ▸ hxQ)

/-- If `D ⊆ q` and `P ⊆ Q` are compatible with a ring map, then the prime `Q/P`
contracts to `q/D` under the induced quotient-ring map. -/
private theorem quotientPrime_comap_quotientMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q D : Ideal R) (P Q : Ideal S)
    (hDq : D ≤ q) (hPQ : P ≤ Q) (hQq : Q.under R = q)
    (hDP : D.map (algebraMap R S) ≤ P) :
    let f : (R ⧸ D) →+* (S ⧸ P) :=
      Ideal.quotientMap P (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hDP)
    let Qbar : Ideal (S ⧸ P) := Q.map (Ideal.Quotient.mk P)
    let qbar : Ideal (R ⧸ D) := q.map (Ideal.Quotient.mk D)
    Qbar.comap f = qbar := by
  dsimp
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.comap_comap]
  rw [show
      (Ideal.quotientMap P (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hDP)).comp
          (Ideal.Quotient.mk D) =
        (Ideal.Quotient.mk P).comp (algebraMap R S) by
    ext r
    rfl]
  rw [← Ideal.comap_comap]
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [sup_eq_left.mpr hPQ]
  rw [show Q.comap (algebraMap R S) = q by exact hQq]
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hDq]

/-- Extending `Q` to the simultaneous localization and contracting recovers `Q`. -/
private theorem localizedPrime_under
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) (Q : Ideal S) [q.IsPrime] [Q.IsPrime]
    (hQq : Q.under R = q) :
    let Sq := simultaneousLocalization q (S := S)
    let W : Ideal Sq := Q.map (algebraMap S Sq)
    W.under S = Q := by
  dsimp
  exact IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid S q.primeCompl) _ inferInstance
      (disjoint_simultaneousLocalization_prime q Q hQq)

/-- The point `(Q S_q)/(P S_q)` on the localized quotient contracts to `Q/P`. -/
private theorem localizedQuotientPrime_comap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) (P Q : Ideal S)
    [q.IsPrime] [P.IsPrime] [Q.IsPrime]
    (hPQ : P ≤ Q) (hQq : Q.under R = q) :
    let Sq := simultaneousLocalization q (S := S)
    let p : Ideal Sq := P.map (algebraMap S Sq)
    let W : Ideal Sq := Q.map (algebraMap S Sq)
    let f : (S ⧸ P) →+* (Sq ⧸ p) :=
      Ideal.quotientMap p (algebraMap S Sq) Ideal.le_comap_map
    let xiIdeal : Ideal (Sq ⧸ p) := W.map (Ideal.Quotient.mk p)
    let Qbar : Ideal (S ⧸ P) := Q.map (Ideal.Quotient.mk P)
    xiIdeal.comap f = Qbar := by
  dsimp
  have hdisjointQ : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (Q : Set S) :=
    disjoint_simultaneousLocalization_prime q Q hQq
  have hdisjointP : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (P : Set S) :=
    hdisjointQ.mono_right hPQ
  letI : (P.map (algebraMap S (simultaneousLocalization q (S := S)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl)
        (simultaneousLocalization q (S := S)) P inferInstance hdisjointP
  letI : (Q.map (algebraMap S (simultaneousLocalization q (S := S)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl)
        (simultaneousLocalization q (S := S)) Q inferInstance hdisjointQ
  apply quotientPrime_comap_quotientMap Q P
      (P.map (algebraMap S (simultaneousLocalization q (S := S))))
      (Q.map (algebraMap S (simultaneousLocalization q (S := S))))
  · exact hPQ
  · exact Ideal.map_mono hPQ
  · exact localizedPrime_under q Q hQq
  · exact le_rfl

/-- The point of the local target quotient below `(Q S_q)/(P S_q)` contracts to `q/D`
on the global target quotient. -/
private theorem restrictionPoint_comap_globalQuotientMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q D : Ideal R) (P Q : Ideal S)
    [q.IsPrime] [D.IsPrime] [P.IsPrime] [Q.IsPrime]
    (hDq : D ≤ q) (hPQ : P ≤ Q) (hQq : Q.under R = q)
    (hDP : D.map (algebraMap R S) ≤ P)
    (a : Localization.AtPrime q)
    (ha : D.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a})
    (hchart :
      let Sq := simultaneousLocalization q (S := S)
      let p : Ideal Sq := P.map (algebraMap S Sq)
      LocalBoundingChart (Localization.AtPrime q) Sq a p) :
    let Sq := simultaneousLocalization q (S := S)
    let p : Ideal Sq := P.map (algebraMap S Sq)
    let W : Ideal Sq := Q.map (algebraMap S Sq)
    let fAC : (R ⧸ D) →+*
        (Localization.AtPrime q ⧸ Ideal.span {a}) :=
      Ideal.quotientMap (Ideal.span {a})
        (algebraMap R (Localization.AtPrime q))
        (Ideal.map_le_iff_le_comap.mp ha.le)
    let xiIdeal : Ideal (Sq ⧸ p) := W.map (Ideal.Quotient.mk p)
    let xi : PrimeSpectrum (Sq ⧸ p) := by
      have hdisjointQ : Disjoint
          (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (Q : Set S) :=
        disjoint_simultaneousLocalization_prime q Q hQq
      have hdisjointP : Disjoint
          (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (P : Set S) :=
        hdisjointQ.mono_right hPQ
      letI : (P.map (algebraMap S Sq)).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint
          (Algebra.algebraMapSubmonoid S q.primeCompl) Sq P inferInstance hdisjointP
      letI : (Q.map (algebraMap S Sq)).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint
          (Algebra.algebraMapSubmonoid S q.primeCompl) Sq Q inferInstance hdisjointQ
      exact ⟨xiIdeal, Ideal.map_isPrime_of_surjective
        Ideal.Quotient.mk_surjective (by
          rw [Ideal.mk_ker]
          exact Ideal.map_mono hPQ)⟩
    (hchart.restrictionPoint xi).asIdeal.comap fAC =
      q.map (Ideal.Quotient.mk D) := by
  dsimp only
  let Sq := simultaneousLocalization q (S := S)
  let p : Ideal Sq := P.map (algebraMap S Sq)
  let W : Ideal Sq := Q.map (algebraMap S Sq)
  have hdisjointQ : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (Q : Set S) :=
    disjoint_simultaneousLocalization_prime q Q hQq
  have hdisjointP : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (P : Set S) :=
    hdisjointQ.mono_right hPQ
  letI : (P.map (algebraMap S Sq)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl) Sq P inferInstance hdisjointP
  letI : (Q.map (algebraMap S Sq)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl) Sq Q inferInstance hdisjointQ
  let fAB : (R ⧸ D) →+* (S ⧸ P) :=
    Ideal.quotientMap P (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hDP)
  let fAC : (R ⧸ D) →+*
      (Localization.AtPrime q ⧸ Ideal.span {a}) :=
    Ideal.quotientMap (Ideal.span {a})
      (algebraMap R (Localization.AtPrime q))
      (Ideal.map_le_iff_le_comap.mp ha.le)
  let fBE : (S ⧸ P) →+* (Sq ⧸ p) :=
    Ideal.quotientMap p (algebraMap S Sq) Ideal.le_comap_map
  let xiIdeal : Ideal (Sq ⧸ p) := W.map (Ideal.Quotient.mk p)
  letI : xiIdeal.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.map_mono hPQ)
  let xi : PrimeSpectrum (Sq ⧸ p) := ⟨xiIdeal, inferInstance⟩
  have hxiB : xi.asIdeal.comap fBE = Q.map (Ideal.Quotient.mk P) := by
    exact localizedQuotientPrime_comap q P Q hPQ hQq
  have hQbarA :
      (Q.map (Ideal.Quotient.mk P)).comap fAB =
        q.map (Ideal.Quotient.mk D) :=
    quotientPrime_comap_quotientMap q D P Q hDq hPQ hQq hDP
  have hsquare : hchart.restrictionRingHom.comp fAC = fBE.comp fAB := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply, fAB, fAC, fBE, Ideal.quotientMap_mk]
    change
      Ideal.Quotient.mk p
          (algebraMap (Localization.AtPrime q) Sq
            (algebraMap R (Localization.AtPrime q) r)) =
        Ideal.Quotient.mk p (algebraMap S Sq (algebraMap R S r))
    rw [Ideal.Quotient.eq]
    change
      algebraMap (Localization.AtPrime q) Sq (algebraMap R (Localization.AtPrime q) r) -
        algebraMap S Sq (algebraMap R S r) ∈ p
    have hroute :
        algebraMap (Localization.AtPrime q) Sq
            (algebraMap R (Localization.AtPrime q) r) =
          algebraMap S Sq (algebraMap R S r) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply,
        ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) Sq,
        ← IsScalarTower.algebraMap_eq R S Sq]
    rw [hroute, sub_self]
    exact p.zero_mem
  change (xi.asIdeal.comap hchart.restrictionRingHom).comap fAC = _
  rw [Ideal.comap_comap, hsquare, ← Ideal.comap_comap, hxiB, hQbarA]

/-- Quotienting `R_q` by the extension of `D` (presented by its local equation `a`)
is a localization of `R/D`. -/
private theorem targetQuotient_isLocalization
    {R : Type u} [CommRing R] (q D : Ideal R) [q.IsPrime]
    (a : Localization.AtPrime q)
    (ha : D.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a}) :
    let C := Localization.AtPrime q ⧸ Ideal.span {a}
    letI : Algebra (R ⧸ D) C :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Ideal.map_le_iff_le_comap.mp ha.le)
    IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ D) q.primeCompl) C := by
  dsimp only
  letI : Algebra (R ⧸ D)
      (Localization.AtPrime q ⧸ Ideal.span {a}) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp ha.le)
  apply IsLocalization.of_surjective q.primeCompl (Localization.AtPrime q)
    (Ideal.Quotient.mk D) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (Ideal.span {a})) Ideal.Quotient.mk_surjective
  · rfl
  · rw [Ideal.mk_ker, Ideal.mk_ker]
    exact ha.symm.le

namespace LocalBoundingChart

set_option backward.isDefEq.respectTransparency false in
/-- Identify the stalk map of the actual affine quotient morphism with the local bounding
chart obtained by simultaneous localization.

The hypotheses contain only incidence and contraction statements for four honest prime
ideals and the already-constructed local chart.  The arrow isomorphism is derived from
the universal properties of quotient rings and localizations. -/
noncomputable def toGlobalQuotientSchemeStalkBoundingChart
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q D : Ideal R) (P Q : Ideal S)
    [q.IsPrime] [D.IsPrime] [P.IsPrime] [Q.IsPrime]
    (hDq : D ≤ q) (hPQ : P ≤ Q) (hQq : Q.under R = q)
    (hDP : D.map (algebraMap R S) ≤ P)
    (a : Localization.AtPrime q)
    (ha : D.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a})
    (hchart :
      let Sq := simultaneousLocalization q (S := S)
      let p : Ideal Sq := P.map (algebraMap S Sq)
      LocalBoundingChart (Localization.AtPrime q) Sq a p) :
    let fAB : (R ⧸ D) →+* (S ⧸ P) :=
      Ideal.quotientMap P (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hDP)
    let Qbar : Ideal (S ⧸ P) := Q.map (Ideal.Quotient.mk P)
    let x : PrimeSpectrum (S ⧸ P) :=
      ⟨Qbar, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact hPQ)⟩
    SchemeStalkBoundingChart
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom fAB)) x := by
  let Sq := simultaneousLocalization q (S := S)
  let Rq := Localization.AtPrime q
  let p : Ideal Sq := P.map (algebraMap S Sq)
  let W : Ideal Sq := Q.map (algebraMap S Sq)
  let A := R ⧸ D
  let B := S ⧸ P
  let C := Rq ⧸ Ideal.span {a}
  let E := Sq ⧸ p
  let fAB : A →+* B :=
    Ideal.quotientMap P (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hDP)
  let fAC : A →+* C :=
    Ideal.quotientMap (Ideal.span {a}) (algebraMap R Rq)
      (Ideal.map_le_iff_le_comap.mp ha.le)
  let fBE : B →+* E :=
    Ideal.quotientMap p (algebraMap S Sq) Ideal.le_comap_map
  let Qbar : Ideal B := Q.map (Ideal.Quotient.mk P)
  let qbar : Ideal A := q.map (Ideal.Quotient.mk D)
  letI : Qbar.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact hPQ)
  letI : qbar.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact hDq)
  let x : PrimeSpectrum B := ⟨Qbar, inferInstance⟩
  have hdisjointQ : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (Q : Set S) :=
    disjoint_simultaneousLocalization_prime q Q hQq
  have hdisjointP : Disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl : Set S) (P : Set S) :=
    hdisjointQ.mono_right hPQ
  letI : (P.map (algebraMap S Sq)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl) Sq P inferInstance hdisjointP
  letI : (Q.map (algebraMap S Sq)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S q.primeCompl) Sq Q inferInstance hdisjointQ
  let xiIdeal : Ideal E := W.map (Ideal.Quotient.mk p)
  letI : xiIdeal.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.map_mono hPQ)
  let xi : PrimeSpectrum E := ⟨xiIdeal, inferInstance⟩
  let eta := hchart.restrictionPoint xi
  let target := PrimeSpectrum.comap fAB x
  letI algAC : Algebra A C :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp ha.le)
  haveI locAC : IsLocalization
      (Algebra.algebraMapSubmonoid A q.primeCompl) C :=
    targetQuotient_isLocalization q D a ha
  letI algBE : Algebra B E :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  haveI locBE : IsLocalization
      (Algebra.algebraMapSubmonoid B
        (Algebra.algebraMapSubmonoid S q.primeCompl)) E := by
    infer_instance
  let TC := Localization.AtPrime eta.asIdeal
  let TE := Localization.AtPrime xi.asIdeal
  haveI locAT0 : IsLocalization.AtPrime TC
      (eta.asIdeal.comap (algebraMap A C)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid A q.primeCompl) TC eta.asIdeal
  have hetaA : eta.asIdeal.comap (algebraMap A C) = qbar := by
    exact restrictionPoint_comap_globalQuotientMap
      q D P Q hDq hPQ hQq hDP a ha hchart
  haveI locAT : IsLocalization.AtPrime TC qbar := by
    change IsLocalization qbar.primeCompl TC
    change IsLocalization
      (eta.asIdeal.comap (algebraMap A C)).primeCompl TC at locAT0
    have hprimeCompl : qbar.primeCompl =
        (eta.asIdeal.comap (algebraMap A C)).primeCompl := by
      ext z
      simp only [Ideal.mem_primeCompl_iff, hetaA]
    rw [hprimeCompl]
    exact locAT0
  haveI locBT0 : IsLocalization.AtPrime TE
      (xi.asIdeal.comap (algebraMap B E)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid B
        (Algebra.algebraMapSubmonoid S q.primeCompl)) TE xi.asIdeal
  have hxiB : xi.asIdeal.comap (algebraMap B E) = Qbar := by
    exact localizedQuotientPrime_comap q P Q hPQ hQq
  haveI locBT : IsLocalization.AtPrime TE Qbar := by
    change IsLocalization Qbar.primeCompl TE
    change IsLocalization
      (xi.asIdeal.comap (algebraMap B E)).primeCompl TE at locBT0
    have hprimeCompl : Qbar.primeCompl =
        (xi.asIdeal.comap (algebraMap B E)).primeCompl := by
      ext z
      simp only [Ideal.mem_primeCompl_iff, hxiB]
    rw [hprimeCompl]
    exact locBT0
  have htarget : target.asIdeal = qbar := by
    exact quotientPrime_comap_quotientMap q D P Q hDq hPQ hQq hDP
  haveI locATtarget : IsLocalization.AtPrime TC target.asIdeal := by
    change IsLocalization target.asIdeal.primeCompl TC
    change IsLocalization qbar.primeCompl TC at locAT
    have hprimeCompl : target.asIdeal.primeCompl = qbar.primeCompl := by
      ext z
      simp only [Ideal.mem_primeCompl_iff, htarget]
    rw [hprimeCompl]
    exact locAT
  have hsquare : hchart.restrictionRingHom.comp fAC = fBE.comp fAB := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply, fAB, fAC, fBE, Ideal.quotientMap_mk]
    change
      Ideal.Quotient.mk p (algebraMap Rq Sq (algebraMap R Rq r)) =
        Ideal.Quotient.mk p (algebraMap S Sq (algebraMap R S r))
    rw [Ideal.Quotient.eq]
    change
      algebraMap Rq Sq (algebraMap R Rq r) -
        algebraMap S Sq (algebraMap R S r) ∈ p
    have hroute :
        algebraMap Rq Sq (algebraMap R Rq r) =
          algebraMap S Sq (algebraMap R S r) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply,
        ← IsScalarTower.algebraMap_eq R Rq Sq,
        ← IsScalarTower.algebraMap_eq R S Sq]
    rw [hroute, sub_self]
    exact p.zero_mem
  let globalHom := Localization.localRingHom target.asIdeal x.asIdeal fAB rfl
  let chartHom := hchart.restrictionLocalRingHom xi
  let eBase : Localization.AtPrime target.asIdeal ≃ₐ[A] TC :=
    IsLocalization.algEquiv target.asIdeal.primeCompl _ _
  let eCover : Localization.AtPrime x.asIdeal ≃ₐ[B] TE :=
    IsLocalization.algEquiv x.asIdeal.primeCompl _ _
  refine
    { R := Rq
      S := Sq
      a := a
      p := p
      xi := xi
      chart := hchart
      stalkIso := ?_ }
  refine (AlgebraicGeometry.Scheme.arrowStalkMapSpecIso
    (CommRingCat.ofHom fAB) x).trans ?_
  refine Arrow.isoMk eBase.toRingEquiv.toCommRingCatIso
    eCover.toRingEquiv.toCommRingCatIso ?_
  apply CommRingCat.hom_ext
  change chartHom.comp eBase.toRingEquiv.toRingHom =
    eCover.toRingEquiv.toRingHom.comp globalHom
  apply IsLocalization.ringHom_ext target.asIdeal.primeCompl
  ext r
  simp only [RingHom.comp_apply]
  change
    chartHom (eBase (algebraMap A (Localization.AtPrime target.asIdeal)
      (Ideal.Quotient.mk D r))) =
      eCover (globalHom (algebraMap A (Localization.AtPrime target.asIdeal)
        (Ideal.Quotient.mk D r)))
  rw [eBase.commutes]
  rw [Localization.localRingHom_to_map target.asIdeal x.asIdeal fAB rfl
    (Ideal.Quotient.mk D r)]
  rw [eCover.commutes]
  change
    chartHom (algebraMap C TC (algebraMap A C (Ideal.Quotient.mk D r))) =
      algebraMap E TE (algebraMap B E (fAB (Ideal.Quotient.mk D r)))
  have hlocal :
      chartHom (algebraMap C TC (algebraMap A C (Ideal.Quotient.mk D r))) =
        algebraMap E TE
          (hchart.restrictionRingHom
            (algebraMap A C (Ideal.Quotient.mk D r))) := by
    simpa only [chartHom, TC, TE, eta,
      LocalBoundingChart.restrictionLocalRingHom,
      LocalBoundingChart.restrictionRingHom] using
        (Localization.localRingHom_to_map
          (hchart.restrictionPoint xi).asIdeal xi.asIdeal
          hchart.restrictionRingHom
          (by simp [LocalBoundingChart.restrictionPoint,
            LocalBoundingChart.restrictionRingHom, Ideal.under_def])
          (algebraMap A C (Ideal.Quotient.mk D r)))
  rw [hlocal]
  congr 1
  exact DFunLike.congr_fun hsquare (Ideal.Quotient.mk D r)

/-- Construct the stalk-level bounding chart of the actual affine divisor morphism
directly from a finite normal cover, its target and source divisors, and the purity and
Abhyankar inputs.

Unlike `toGlobalQuotientSchemeStalkBoundingChart`, this definition does not take an
already-constructed `LocalBoundingChart`.  It first builds that chart from the canonical
simultaneous localization by `ofFiniteNormalLocalizationOfDivisors`, then applies the
affine stalk comparison above.  Thus neither formal étaleness nor the conclusion of the
bounding argument occurs among its hypotheses. -/
noncomputable def
    toGlobalQuotientSchemeStalkBoundingChartOfFiniteNormalLocalizationOfDivisors
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q D : Ideal R) (P Q : Ideal S)
    [q.IsPrime] [D.IsPrime] [P.IsPrime] [Q.IsPrime]
    (hDq : D ≤ q) (hPQ : P ≤ Q) (hQq : Q.under R = q)
    (hDP : D.map (algebraMap R S) ≤ P)
    (hPheight : P.height = 1)
    (a : Localization.AtPrime q)
    (ha : D.map (algebraMap R (Localization.AtPrime q)) = Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (branch_subset_divisor : heightOneBranchIdeal (R := R) (S := S) ⊆ {D})
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (simultaneousLocalization q (S := S)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (simultaneousLocalization q (S := S)) a) :
    let fAB : (R ⧸ D) →+* (S ⧸ P) :=
      Ideal.quotientMap P (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hDP)
    let Qbar : Ideal (S ⧸ P) := Q.map (Ideal.Quotient.mk P)
    let x : PrimeSpectrum (S ⧸ P) :=
      ⟨Qbar, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact hPQ)⟩
    SchemeStalkBoundingChart
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom fAB)) x := by
  have hunder : P.under R ≤ q := by
    rw [← hQq]
    exact Ideal.comap_mono hPQ
  let hchart := ofFiniteNormalLocalizationOfDivisors
    q D P hunder hDP hPheight a ha regular_base dim_base regular_divisor
      dim_divisor branch_subset_divisor purity abhyankar
  exact toGlobalQuotientSchemeStalkBoundingChart
    q D P Q hDq hPQ hQq hDP a ha hchart

/-- Dynamics-facing bundled-divisor form of the global affine stalk bridge.

The target and selected source divisors are honest height-one primes, and branch support
is stated using `heightOneBranch`.  The result is already converted to the
`SchemeStalkBoundingLocalizationPresentation` consumed by
`SchemeNormalizationPcfSetupChart.chart`.  Thus the auxiliary contracted-ideal support
set, the local chart, the stalk-arrow isomorphism, and the localization presentation are
all derived. -/
noncomputable def
    toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisors
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q : Ideal R) (D : HeightOnePrime R) (P : HeightOnePrime S) (Q : Ideal S)
    [q.IsPrime] [Q.IsPrime]
    (hDq : D.1.asIdeal ≤ q) (hPQ : P.1.asIdeal ≤ Q)
    (hQq : Q.under R = q)
    (hDP : D.1.asIdeal.map (algebraMap R S) ≤ P.1.asIdeal)
    (a : Localization.AtPrime q)
    (ha : D.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (branch_subset_divisor : heightOneBranch (R := R) (S := S) ⊆ {D})
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (simultaneousLocalization q (S := S)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (simultaneousLocalization q (S := S)) a) :
    let fAB : (R ⧸ D.1.asIdeal) →+* (S ⧸ P.1.asIdeal) :=
      Ideal.quotientMap P.1.asIdeal (algebraMap R S)
        (Ideal.map_le_iff_le_comap.mp hDP)
    let Qbar : Ideal (S ⧸ P.1.asIdeal) :=
      Q.map (Ideal.Quotient.mk P.1.asIdeal)
    let x : PrimeSpectrum (S ⧸ P.1.asIdeal) :=
      ⟨Qbar, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact hPQ)⟩
    SchemeStalkBoundingLocalizationPresentation
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom fAB)) x := by
  let hchart :=
    toGlobalQuotientSchemeStalkBoundingChartOfFiniteNormalLocalizationOfDivisors
      q D.1.asIdeal P.1.asIdeal Q hDq hPQ hQq hDP P.2 a ha regular_base
        dim_base regular_divisor dim_divisor
        (heightOneBranchIdeal_subset_singleton_of_heightOneBranch_subset_singleton
          D branch_subset_divisor)
        purity abhyankar
  exact hchart.toSchemeStalkBoundingLocalizationPresentation

/-- Step 0 form of the dynamics-facing affine stalk bridge.

Instead of requiring the whole affine branch set to be supported on `D`, this constructor
assumes only that the selected point `q` lies on no other branch divisor.  It produces the
same localization presentation of the actual quotient morphism, so this is the form that
matches the manuscript's open-avoidance argument. -/
noncomputable def
    toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra ℚ R]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q : Ideal R) (D : HeightOnePrime R) (P : HeightOnePrime S) (Q : Ideal S)
    [q.IsPrime] [Q.IsPrime]
    (hDq : D.1.asIdeal ≤ q) (hPQ : P.1.asIdeal ≤ Q)
    (hQq : Q.under R = q)
    (hDP : D.1.asIdeal.map (algebraMap R S) ≤ P.1.asIdeal)
    (a : Localization.AtPrime q)
    (ha : D.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (havoid : ∀ E ∈ heightOneBranch (R := R) (S := S), E ≠ D →
      ¬ E.1.asIdeal ≤ q)
    (purity : Stacks.ZariskiNagataPurity (Localization.AtPrime q)
      (simultaneousLocalization q (S := S)))
    (abhyankar : Stacks.AbhyankarLemma (Localization.AtPrime q)
      (simultaneousLocalization q (S := S)) a) :
    let fAB : (R ⧸ D.1.asIdeal) →+* (S ⧸ P.1.asIdeal) :=
      Ideal.quotientMap P.1.asIdeal (algebraMap R S)
        (Ideal.map_le_iff_le_comap.mp hDP)
    let Qbar : Ideal (S ⧸ P.1.asIdeal) :=
      Q.map (Ideal.Quotient.mk P.1.asIdeal)
    let x : PrimeSpectrum (S ⧸ P.1.asIdeal) :=
      ⟨Qbar, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]
        exact hPQ)⟩
    SchemeStalkBoundingLocalizationPresentation
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom fAB)) x := by
  have hunder : P.1.asIdeal.under R ≤ q := by
    rw [← hQq]
    exact Ideal.comap_mono hPQ
  let hlocal := ofFiniteNormalLocalizationOfHeightOneDivisorsAt
    q D P hunder hDP a ha regular_base dim_base regular_divisor dim_divisor
      havoid purity abhyankar
  let hchart := toGlobalQuotientSchemeStalkBoundingChart
    q D.1.asIdeal P.1.asIdeal Q hDq hPQ hQq hDP a ha hlocal
  exact hchart.toSchemeStalkBoundingLocalizationPresentation

end LocalBoundingChart

end Pcf
