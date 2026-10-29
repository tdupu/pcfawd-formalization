/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StandardCoverGeometry

/-!
# Geometry of the normalization in the standard-cover presentation

This file transports the finite-free and regular reduced-divisor conclusions for the
standard models across the normalization equivalence proved from the generic presentation.
It is the affine geometric conclusion of Stacks Project Tag `0EYH` after Tag `0EYG` has
supplied the product of localized standard root algebras.
-/

@[expose] public section

universe u

open Polynomial

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- An arbitrary normalization with the generic standard-cover presentation is finite
over the base. -/
theorem normalizationOfLocalizedPresentation_finite
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Finite ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (u i) a (e i)))) :
    Module.Finite R N := by
  let _ := Fintype.ofFinite ι
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))
  let E : N ≃ₐ[R] C :=
    normalizationEquivStandardCoversOfLocalizedPresentation u a e he ha g
  let _ : Module.Finite R C := standardCovers_finite u a e he
  exact Module.Finite.equiv E.symm.toLinearEquiv

/-- An arbitrary normalization with the generic standard-cover presentation is free over
the base.  Together with `normalizationOfLocalizedPresentation_finite`, this is the affine
finite-locally-free assertion of Tag `0EYH`. -/
theorem normalizationOfLocalizedPresentation_free
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Finite ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (u i) a (e i)))) :
    Module.Free R N := by
  let _ := Fintype.ofFinite ι
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))
  let E : N ≃ₐ[R] C :=
    normalizationEquivStandardCoversOfLocalizedPresentation u a e he ha g
  let _ : Module.Free R C := standardCovers_free u a e he
  exact Module.Free.of_equiv E.symm.toLinearEquiv

/-- The reduced inverse-image ideal on an arbitrary normalization, transported from the
root ideals in its standard-cover presentation. -/
noncomputable def normalizationReducedDivisorIdealOfLocalizedPresentation
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Fintype ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (u i) a (e i)))) : Ideal N :=
  (standardCoversReducedDivisorIdeal u a e).map
    (normalizationEquivStandardCoversOfLocalizedPresentation
      u a e he ha g).symm.toRingEquiv.toRingHom

/-- The transported root ideal is exactly the radical of the pullback of the base
divisor, so it defines the reduced inverse image rather than an auxiliary divisor. -/
theorem normalization_radical_span_algebraMap_eq_reducedDivisorIdeal
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Fintype ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (u i) a (e i)))) :
    (Ideal.span ({algebraMap R N a} : Set N)).radical =
      normalizationReducedDivisorIdealOfLocalizedPresentation u a e he ha g := by
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))
  let E : N ≃ₐ[R] C :=
    normalizationEquivStandardCoversOfLocalizedPresentation u a e he ha g
  let J : Ideal C := standardCoversReducedDivisorIdeal u a e
  let _ : IsReduced (R ⧸ Ideal.span ({a} : Set R)) :=
    isReduced_of_isRegularRing
  have hC : (Ideal.span ({algebraMap R C a} : Set C)).radical = J :=
    standardCovers_radical_span_algebraMap_eq_reducedDivisorIdeal u a e he
  have hspan : (Ideal.span ({algebraMap R C a} : Set C)).map
      E.symm.toRingEquiv.toRingHom = Ideal.span ({algebraMap R N a} : Set N) := by
    rw [Ideal.map_span]
    simp [E]
  change (Ideal.span ({algebraMap R N a} : Set N)).radical =
    J.map E.symm.toRingEquiv.toRingHom
  rw [← hspan, ← hC]
  symm
  exact Ideal.map_radical_of_surjective
    (f := E.symm.toRingEquiv.toRingHom)
    (I := Ideal.span ({algebraMap R C a} : Set C))
    E.symm.surjective
      (((RingHom.injective_iff_ker_eq_bot E.symm.toRingEquiv.toRingHom).mp
        E.symm.injective).le.trans bot_le)

/-- The reduced divisor on the normalization is a finite product of copies of the base
divisor. -/
noncomputable def normalizationReducedDivisorQuotientEquiv
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Fintype ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (u i) a (e i)))) :
    (N ⧸ normalizationReducedDivisorIdealOfLocalizedPresentation u a e he ha g) ≃+*
      (∀ _i : ι, R ⧸ Ideal.span ({a} : Set R)) := by
  let C := ∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (u i) a (e i))
  let E : N ≃ₐ[R] C :=
    normalizationEquivStandardCoversOfLocalizedPresentation u a e he ha g
  let J : Ideal C := standardCoversReducedDivisorIdeal u a e
  let K : Ideal N :=
    normalizationReducedDivisorIdealOfLocalizedPresentation u a e he ha g
  have hmap : J = K.map E.toRingEquiv.toRingHom := by
    change J = Ideal.map E.toRingEquiv.toRingHom
      (Ideal.map E.symm.toRingEquiv.toRingHom J)
    rw [Ideal.map_map]
    have hcomp : E.toRingEquiv.toRingHom.comp E.symm.toRingEquiv.toRingHom =
        RingHom.id C := by
      ext x
      simp
    rw [hcomp, Ideal.map_id]
  exact (Ideal.quotientEquiv K J E.toRingEquiv hmap).trans
    (standardCoversReducedDivisorQuotientEquiv u a e he)

/-- The reduced inverse image of the divisor on the arbitrary normalization is regular,
the final regularity assertion of Tag `0EYH`. -/
theorem normalizationReducedDivisor_isRegularRing
    {N : Type u} [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Fintype ι]
    (u : ι → Rˣ) (a : R) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [IsIntegralClosure N R (Localization.Away (algebraMap R N a))]
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (u i) a (e i)))) :
    IsRegularRing
      (N ⧸ normalizationReducedDivisorIdealOfLocalizedPresentation u a e he ha g) := by
  let _ : IsRegularRing (∀ _i : ι, R ⧸ Ideal.span ({a} : Set R)) :=
    isRegularRing_pi_of_finite _
  exact IsRegularRing.of_ringEquiv
    (normalizationReducedDivisorQuotientEquiv u a e he ha g).symm

#print axioms normalizationOfLocalizedPresentation_finite
#print axioms normalizationOfLocalizedPresentation_free
#print axioms normalization_radical_span_algebraMap_eq_reducedDivisorIdeal
#print axioms normalizationReducedDivisorQuotientEquiv
#print axioms normalizationReducedDivisor_isRegularRing

end Pcf.Stacks
