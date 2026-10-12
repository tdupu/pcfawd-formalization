/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.KrullDimension.Regular

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

/-- A surjective local map with principal kernel increases the minimal number of
generators of the maximal ideal by at most one.  This is the generator-lifting step in
Stacks Tag `00NU`. -/
theorem spanFinrank_maximalIdeal_le_add_one_of_principal_kernel
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : (RingHom.ker f).IsPrincipal) :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal S).spanFinrank + 1 := by
  classical
  let : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨a, ha⟩ := hker
  change RingHom.ker f = Ideal.span ({a} : Set R) at ha
  have hfg : Submodule.FG (maximalIdeal S) := IsNoetherian.noetherian _
  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  let g : S → R := Function.surjInv hf
  have hg : Function.RightInverse g f := Function.rightInverse_surjInv hf
  let t : Finset R := s.image g
  have hmap : (Ideal.span (↑t : Set R)).map f = maximalIdeal S := by
    rw [Ideal.map_span, ← hs]
    congr 1
    ext y
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image, t]
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hg z] using hz
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, hg y⟩
  have hspan : Ideal.span (Set.insert a (↑t : Set R)) = maximalIdeal R := by
    rw [show Ideal.span (Set.insert a (↑t : Set R)) =
        Ideal.span ({a} : Set R) ⊔ Ideal.span (↑t : Set R) from
      Ideal.span_insert a (↑t : Set R),
      ← ha, RingHom.ker_eq_comap_bot, sup_comm,
      ← Ideal.comap_map_of_surjective f hf (Ideal.span (↑t : Set R)),
      hmap, maximalIdeal_comap]
  rw [← hspan]
  calc
    (Ideal.span (Set.insert a (↑t : Set R))).spanFinrank ≤
        (Set.insert a (↑t : Set R)).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite
        ((Finset.finite_toSet t).insert a)
    _ ≤ (↑t : Set R).ncard + 1 := Set.ncard_insert_le _ _
    _ = t.card + 1 := by simp
    _ ≤ s.card + 1 := Nat.add_le_add_right (Finset.card_image_le) 1
    _ = (maximalIdeal S).spanFinrank + 1 := by rw [hcard]

/-- **Stacks Tag `00NU`, principal-element case.**

If a nonzerodivisor in the maximal ideal of a Noetherian local ring has regular local
quotient, then the original ring is regular local.  This is the form used in the proof
of Abhyankar's lemma. -/
@[stacks 00NU "the principal-element case"]
theorem isRegularLocalRing_of_quotient_nonZeroDivisor
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : x ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    IsRegularLocalRing R := by
  let I : Ideal R := Ideal.span {x}
  have hbound : (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ I)).spanFinrank + 1 := by
    apply spanFinrank_maximalIdeal_le_add_one_of_principal_kernel
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    simpa only [Ideal.mk_ker] using (inferInstance : I.IsPrincipal)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) + 1 := by
      exact_mod_cast hbound
    _ = ringKrullDim (R ⧸ I) + 1 := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    _ = ringKrullDim R := by
      dsimp only [I]
      exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
        (Module.Flat.isSMulRegular_of_nonZeroDivisors hreg) hx

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
#print axioms spanFinrank_maximalIdeal_le_add_one_of_principal_kernel
#print axioms isRegularLocalRing_of_quotient_nonZeroDivisor
#print axioms isRegularLocalRing_of_principal_kernel_of_dim_one
#print axioms isRegularLocalRing_of_principal_quotient_of_dim_one

end Pcf
