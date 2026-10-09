/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Regularity from a one-dimensional principal quotient

If a local ring surjects onto a local ring with principal maximal ideal and
the kernel is principal, then its maximal ideal has at most two generators.
In dimension at least two, a Noetherian local ring with such a quotient is
therefore regular.
-/

universe u v

open IsLocalRing

namespace Pcf

/-- A principal kernel and a principal maximal ideal downstairs give two
generators of the maximal ideal upstairs. -/
theorem spanFinrank_maximalIdeal_le_two_of_principal_kernel
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : (RingHom.ker f).IsPrincipal)
    (hmax : (maximalIdeal S).IsPrincipal) :
    (maximalIdeal R).spanFinrank ≤ 2 := by
  classical
  let : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨a, ha⟩ := hker
  obtain ⟨b, hb⟩ := hmax
  obtain ⟨c, hc⟩ := hf b
  change RingHom.ker f = Ideal.span ({a} : Set R) at ha
  have hmap : (Ideal.span ({c} : Set R)).map f = maximalIdeal S := by
    rw [Ideal.map_span, Set.image_singleton, hc]
    exact hb.symm
  have hspan : Ideal.span ({c, a} : Set R) = maximalIdeal R := by
    rw [Ideal.span_insert, ← ha, RingHom.ker_eq_comap_bot,
      ← Ideal.comap_map_of_surjective f hf, hmap, maximalIdeal_comap]
  rw [← hspan]
  exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
    (by simpa using Set.ncard_insert_le c ({a} : Set R))

/-- A Noetherian local ring of dimension at least two is regular if it has
a principal kernel quotient which is regular of dimension one. -/
theorem isRegularLocalRing_of_principal_kernel_of_dim_one
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : (RingHom.ker f).IsPrincipal)
    (hdimS : ringKrullDim S = 1) (hdimR : 2 ≤ ringKrullDim R) :
    IsRegularLocalRing R := by
  have hmax : (maximalIdeal S).IsPrincipal := by
    apply ((Submodule.spanFinrank_eq_one_iff _).mp ?_).1
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
    rw [hdimS] at h
    exact_mod_cast h
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 2 := by
      exact_mod_cast spanFinrank_maximalIdeal_le_two_of_principal_kernel f hf hker hmax
    _ ≤ ringKrullDim R := hdimR

/-- The quotient-ring formulation of the principal-kernel regularity criterion. -/
theorem isRegularLocalRing_of_principal_quotient_of_dim_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) [I.IsPrincipal] [IsRegularLocalRing (R ⧸ I)]
    (hdimI : ringKrullDim (R ⧸ I) = 1) (hdimR : 2 ≤ ringKrullDim R) :
    IsRegularLocalRing R := by
  apply isRegularLocalRing_of_principal_kernel_of_dim_one (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  · simpa only [Ideal.mk_ker] using (inferInstance : I.IsPrincipal)
  · exact hdimI
  · exact hdimR

#print axioms spanFinrank_maximalIdeal_le_two_of_principal_kernel
#print axioms isRegularLocalRing_of_principal_kernel_of_dim_one
#print axioms isRegularLocalRing_of_principal_quotient_of_dim_one

end Pcf
