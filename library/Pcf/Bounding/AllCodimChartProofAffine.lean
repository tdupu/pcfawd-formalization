/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimChartStatement
public import Pcf.Bounding.SchemeBridge

/-!
# Affine dictionary for the étale restriction chart

On an affine open `W` of a scheme, points of `W` correspond to primes of
`Γ(W)`, stalks are localizations at these primes, and specialization is
inclusion of primes. This file records the facts used to pass between the
scheme-level statement `AllCodimChartProperty` and the affine local tame
bounding chart: the prime of a generization inside a stalk is the extension
of the corresponding prime of `Γ(W)`, and formal étaleness of a stalk map
is formal étaleness of the corresponding local ring map of sections.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)

/-- The germ map at a point of an affine open contracts the maximal ideal of
the stalk to the prime of the point. -/
theorem affineOpen_comap_germ_maximalIdeal (x : X) (hx : x ∈ W) :
    (maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ W x hx).hom =
      (hW.primeIdealOf ⟨x, hx⟩).asIdeal := by
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x) _

/-- The prime of a generization inside a stalk contracts to the prime of the
generization on sections of an affine neighbourhood. -/
theorem affineOpen_comap_germ_stalkGenerizationPrime {d E : X} (h : d ⤳ E)
    (hE : E ∈ W) :
    (stalkGenerizationPrime X h).comap (X.presheaf.germ W E hE).hom =
      (hW.primeIdealOf ⟨d, h.mem_open W.isOpen hE⟩).asIdeal := by
  rw [stalkGenerizationPrime, Ideal.comap_comap, ← CommRingCat.hom_comp,
    X.presheaf.germ_stalkSpecializes]
  exact affineOpen_comap_germ_maximalIdeal hW d _

/-- Specialization inside an affine open is inclusion of primes. -/
theorem affineOpen_primeIdealOf_le_of_specializes {d E : X} (h : d ⤳ E)
    (hE : E ∈ W) :
    (hW.primeIdealOf ⟨d, h.mem_open W.isOpen hE⟩).asIdeal ≤
      (hW.primeIdealOf ⟨E, hE⟩).asIdeal := by
  rw [← affineOpen_comap_germ_stalkGenerizationPrime hW h hE,
    ← affineOpen_comap_germ_maximalIdeal hW E hE]
  exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))

/-- The prime of a generization inside the stalk is the extension of the
prime of sections. -/
theorem affineOpen_stalkGenerizationPrime_eq_map {d E : X} (h : d ⤳ E)
    (hE : E ∈ W) :
    stalkGenerizationPrime X h =
      (hW.primeIdealOf ⟨d, h.mem_open W.isOpen hE⟩).asIdeal.map
        (X.presheaf.germ W E hE).hom := by
  letI := X.presheaf.algebra_section_stalk ⟨E, hE⟩
  haveI := hW.isLocalization_stalk ⟨E, hE⟩
  rw [← affineOpen_comap_germ_stalkGenerizationPrime hW h hE]
  exact (IsLocalization.map_under (hW.primeIdealOf ⟨E, hE⟩).asIdeal.primeCompl
    (X.presheaf.stalk E) _).symm

/-- A prime of sections contained in the prime of a point is the prime of a
generization of that point. -/
theorem affineOpen_specializes_fromSpec_of_le (P : PrimeSpectrum Γ(X, W)) (E : X)
    (hE : E ∈ W) (hP : P.asIdeal ≤ (hW.primeIdealOf ⟨E, hE⟩).asIdeal) :
    hW.fromSpec P ⤳ E := by
  have h := (PrimeSpectrum.le_iff_specializes P (hW.primeIdealOf ⟨E, hE⟩)).mp hP
  have h' := h.map hW.fromSpec.continuous
  rwa [hW.fromSpec_primeIdealOf] at h'

/-- The height of the prime of a point of an affine open is its codimension. -/
theorem affineOpen_primeIdealOf_height (x : X) (hx : x ∈ W) :
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal.height = Order.coheight x := by
  let P : AlgebraicGeometry.Spec Γ(X, W) := hW.primeIdealOf ⟨x, hx⟩
  change P.asIdeal.height = _
  have hcoheight : Order.coheight P = Order.coheight x := by
    symm
    have h := AlgebraicGeometry.coheight_eq_of_isOpenImmersion (x := P) hW.fromSpec
    simpa only [P, hW.fromSpec_primeIdealOf] using h
  exact (AlgebraicGeometry.idealHeight_eq_coheight Γ(X, W) P).trans hcoheight

/-- The point of an affine open with a prescribed prime of sections. -/
theorem affineOpen_exists_point_of_prime (P : PrimeSpectrum Γ(X, W)) :
    ∃ (x : X) (hx : x ∈ W), hW.primeIdealOf ⟨x, hx⟩ = P := by
  have hx : hW.fromSpec P ∈ W := by
    have h : hW.fromSpec P ∈ Set.range hW.fromSpec := ⟨P, rfl⟩
    rwa [hW.range_fromSpec] at h
  refine ⟨hW.fromSpec P, hx, ?_⟩
  apply hW.fromSpec.isOpenEmbedding.injective
  exact hW.fromSpec_primeIdealOf ⟨_, hx⟩

/-- Points of an affine open are determined by their primes. -/
theorem affineOpen_primeIdealOf_injective {x y : X} (hx : x ∈ W) (hy : y ∈ W)
    (h : hW.primeIdealOf ⟨x, hx⟩ = hW.primeIdealOf ⟨y, hy⟩) : x = y := by
  have h1 := hW.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 := hW.fromSpec_primeIdealOf ⟨y, hy⟩
  rw [h] at h1
  exact h1.symm.trans h2

/-- On an integral scheme the prime of the generic point is zero. -/
theorem affineOpen_primeIdealOf_genericPoint [IsIntegral X] (hη : genericPoint X ∈ W) :
    (hW.primeIdealOf ⟨genericPoint X, hη⟩).asIdeal = ⊥ := by
  rw [← affineOpen_comap_germ_maximalIdeal hW _ hη]
  have hfield : IsField (X.presheaf.stalk (genericPoint X)) :=
    Field.toIsField X.functionField
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield]
  exact Ideal.comap_bot_of_injective _ (germ_injective_of_isIntegral X _ hη)

/-- Formal étaleness of local maps does not depend on the presentation of
equal data. -/
theorem formallyEtale_localRingHom_congr {R S : Type u} [CommRing R] [CommRing S]
    {f g : R →+* S} (hfg : f = g) {I I' : Ideal S} [I.IsPrime] [I'.IsPrime] (hI : I = I')
    {J J' : Ideal R} [J.IsPrime] [J'.IsPrime] (hJ : J = J') (h1 : J = I.comap f)
    (h2 : J' = I'.comap g) :
    (Localization.localRingHom J I f h1).FormallyEtale →
      (Localization.localRingHom J' I' g h2).FormallyEtale := by
  subst hfg hI hJ
  exact id

/-- Formal étaleness of a stalk map is formal étaleness of the local map of
sections over affine opens. -/
theorem formallyEtale_stalkMap_iff_localRingHom {Y : Scheme.{u}} (f : X ⟶ Y)
    {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    (f.stalkMap x).hom.FormallyEtale ↔
      (Localization.localRingHom _ _ (f.appLE U V hVU).hom
        congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm).FormallyEtale :=
  formallyEtale_respectsIso.arrow_mk_iso_iff (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)

/-- If the local map of sections at the contraction of a prime of the
simultaneous localization is formally étale, the localized base is étale at
that prime. -/
theorem isEtaleAt_of_formallyEtale_localRingHom {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal R) [q.IsPrime]
    (w : Ideal (Localization (Algebra.algebraMapSubmonoid S q.primeCompl))) [w.IsPrime]
    (h : (Localization.localRingHom
      ((w.comap (algebraMap S _)).comap (algebraMap R S)) (w.comap (algebraMap S _))
      (algebraMap R S) rfl).FormallyEtale) :
    Algebra.IsEtaleAt (Localization.AtPrime q) w := by
  let Sq := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  let P : Ideal S := w.comap (algebraMap S Sq)
  let p : Ideal R := P.comap (algebraMap R S)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap R S) rfl).toAlgebra
  haveI : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime P) := h
  haveI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (Localization.localRingHom_to_map p P (algebraMap R S) rfl x).symm
  haveI : Algebra.FormallyEtale R (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  haveI : Algebra.FormallyEtale R (Localization.AtPrime P) :=
    Algebra.FormallyEtale.comp R (Localization.AtPrime p) (Localization.AtPrime P)
  let e : Localization.AtPrime P ≃ₐ[S] Localization.AtPrime w :=
    IsLocalization.algEquiv P.primeCompl _ _
  haveI : Algebra.FormallyEtale R (Localization.AtPrime w) :=
    Algebra.FormallyEtale.of_equiv (e.restrictScalars R)
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

#print axioms affineOpen_comap_germ_maximalIdeal
#print axioms affineOpen_comap_germ_stalkGenerizationPrime
#print axioms affineOpen_primeIdealOf_le_of_specializes
#print axioms affineOpen_stalkGenerizationPrime_eq_map
#print axioms affineOpen_specializes_fromSpec_of_le
#print axioms affineOpen_primeIdealOf_height
#print axioms affineOpen_exists_point_of_prime
#print axioms affineOpen_primeIdealOf_injective
#print axioms affineOpen_primeIdealOf_genericPoint
#print axioms formallyEtale_localRingHom_congr
#print axioms formallyEtale_stalkMap_iff_localRingHom
#print axioms isEtaleAt_of_formallyEtale_localRingHom

end
end Pcf
