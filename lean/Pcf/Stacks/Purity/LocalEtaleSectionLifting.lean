/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Pcf.Stacks.Purity.StandardEtaleSectionLifting

/-!
# Lifting etale sections over a local henselian pair

Let `(R, I)` be a henselian pair with `R` local.  An `R`-algebra map from an etale algebra
`S` to `R ⧸ I` lifts to `R`.  Composing the given map with the residue map of the local ring
`R ⧸ I` selects a prime of `S`.  Stacks Tag `00UE` supplies a principal neighbourhood of that
prime on which `S` is standard etale.  Its denominator maps to a unit in the local ring `R ⧸ I`,
so the section extends to the localization and the standard-etale lifting theorem applies.

This is the local-base specialization of condition (2) in Stacks Project Tag `09XI`.  It is not
the fully general pair theorem: without a local base, one must globalize the local standard-etale
neighbourhoods, as in the integral-closure and clopen assembly in the proof of `09XI`.
-/

noncomputable section

universe u v

namespace Pcf.Stacks

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [IsLocalRing R] [Algebra R S]

/-- Over a local henselian pair, a section modulo the henselian ideal of an arbitrary etale
algebra lifts to the base ring.

This is the local-base case of Stacks Project Tag `09XI`, condition (2). -/
theorem exists_algHom_lift_of_etale_of_isLocalRing
    (I : Ideal R) [HenselianRing R I] [Algebra.Etale R S]
    (σ : S →ₐ[R] R ⧸ I) :
    ∃ τ : S →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp τ = σ := by
  have hIle : I ≤ IsLocalRing.maximalIdeal R := by
    simpa [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top] using
      (HenselianRing.jac (R := R) (I := I))
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let ρ : S →+* IsLocalRing.ResidueField (R ⧸ I) :=
    (IsLocalRing.residue (R ⧸ I)).comp σ.toRingHom
  let Q : Ideal S := RingHom.ker ρ
  let _ : Q.IsPrime := RingHom.ker_isPrime ρ
  let _ : Algebra.IsEtaleAt R Q := inferInstance
  obtain ⟨f, hfQ, hfstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := S) Q
  let L := Localization.Away f
  let _ : Algebra.IsStandardEtale R L := hfstd
  have hresidue : IsUnit (IsLocalRing.residue (R ⧸ I) (σ f)) := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    exact hfQ (RingHom.mem_ker.mpr hzero)
  have hσf : IsUnit (σ f) :=
    IsUnit.of_map (IsLocalRing.residue (R ⧸ I)) (σ f) hresidue
  let σL : L →ₐ[R] R ⧸ I :=
    IsLocalization.Away.liftAlgHom f (f := σ) hσf
  obtain ⟨τL, hτL⟩ := exists_algHom_lift_of_isStandardEtale I σL
  let toL : S →ₐ[R] L := IsScalarTower.toAlgHom R S L
  refine ⟨τL.comp toL, ?_⟩
  apply AlgHom.ext
  intro s
  have hs := DFunLike.congr_fun hτL (toL s)
  simpa [σL, toL] using hs

#print axioms exists_algHom_lift_of_etale_of_isLocalRing

end Pcf.Stacks
