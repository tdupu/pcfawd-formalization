/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Regularity under etale base change

This file records the affine regularity ascent used when a regular Cartier divisor is pulled
back to a pointed etale neighbourhood.  It is the regularity input in the descent paragraph of
Stacks Tag `0EYG`.
-/

@[expose] public section

universe u v

open IsLocalRing
open scoped TensorProduct

namespace Pcf.Stacks

/-- Regularity ascends along a flat, formally unramified local map of Noetherian local rings
essentially of finite type. -/
theorem isRegularLocalRing_of_flat_of_formallyUnramified
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Module.Flat R S]
    [Algebra.FormallyUnramified R S] : IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hspan : (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R)]
    exact Ideal.spanFinrank_map_le_of_fg _ (Ideal.fg_of_isNoetherianRing _)
  have hlo : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  have hdim : ringKrullDim R ≤ ringKrullDim S := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr (by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
        (maximalIdeal S)]
      exact le_self_add)
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast hspan
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := hdim

/-- An etale algebra over a regular ring is regular. -/
theorem isRegularRing_of_etale
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsRegularRing R] [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by
  let _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.under R
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq]
    infer_instance
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.comp R S _
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R _ _
  exact isRegularLocalRing_of_flat_of_formallyUnramified
    (Localization.AtPrime p) (Localization.AtPrime q)

/-- Pulling back a regular principal quotient along an etale algebra keeps the quotient regular.
This is the affine regular-divisor clause needed at a descended pointed-etale stage. -/
theorem quotient_span_isRegularRing_of_etale
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] (a : R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))] :
    IsRegularRing (S ⧸ Ideal.span ({algebraMap R S a} : Set S)) := by
  let I : Ideal R := Ideal.span {a}
  let T := (R ⧸ I) ⊗[R] S
  let _ : Algebra (R ⧸ I) T := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra.Etale (R ⧸ I) T := Algebra.Etale.baseChange R S (R ⧸ I)
  let _ : IsRegularRing T := isRegularRing_of_etale (R ⧸ I) T
  have hregular : IsRegularRing (S ⧸ I.map (algebraMap R S)) :=
    IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toRingEquiv
  have hI : I.map (algebraMap R S) =
      Ideal.span ({algebraMap R S a} : Set S) := by
    rw [Ideal.map_span]
    simp
  rw [← hI]
  exact hregular

#print axioms isRegularLocalRing_of_flat_of_formallyUnramified
#print axioms isRegularRing_of_etale
#print axioms quotient_span_isRegularRing_of_etale

end Pcf.Stacks
