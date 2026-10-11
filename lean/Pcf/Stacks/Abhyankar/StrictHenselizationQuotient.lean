/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.Quotient
import Pcf.Stacks.Abhyankar.StrictHenselization

/-!
# Quotients of strictly henselian local rings

This module proves the intrinsic algebraic core of Stacks Tag `05WS`: a quotient by an ideal
contained in the maximal ideal of a strictly henselian local ring is again strictly henselian.
The full tag additionally identifies that quotient with a strict henselization of the quotient of
the original base ring; that comparison requires a universal-property interface for strict
henselizations, which is not present in the pinned Mathlib.
-/

open Polynomial

universe u

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- A quotient of a henselian local ring by an ideal in its maximal ideal is henselian. -/
theorem HenselianLocalRing.quotient_of_le_maximalIdeal [HenselianLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    HenselianLocalRing (R ⧸ I) := by
  have hIne : I ≠ ⊤ := by
    intro h
    have hm : IsLocalRing.maximalIdeal R = ⊤ :=
      eq_top_iff.mpr (h ▸ hI)
    exact (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).ne_top hm
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  apply ((HenselianLocalRing.TFAE (R ⧸ I)).out 3 1).mp
  intro K _ φ hφ f hf a₀ ha₀ hda₀
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hlifts : f ∈ Polynomial.lifts q :=
    Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective f
  obtain ⟨F, hF, -, hFmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  let ψ : R →+* K := φ.comp q
  have hψ : Function.Surjective ψ := hφ.comp Ideal.Quotient.mk_surjective
  have hroot : F.eval₂ ψ a₀ = 0 := by
    rw [← Polynomial.eval₂_map, hF]
    exact ha₀
  have hderiv : F.derivative.eval₂ ψ a₀ ≠ 0 := by
    rw [← Polynomial.eval₂_map, ← Polynomial.derivative_map, hF]
    exact hda₀
  have hhens := ((HenselianLocalRing.TFAE R).out 1 3).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, ha, hφa⟩ :=
    hhens (K := K) ψ hψ F hFmonic a₀ hroot hderiv
  refine ⟨q a, ?_, hφa⟩
  change f.eval (q a) = 0
  rw [← hF, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha.eq_zero, map_zero]

/-- A surjective local map induces a bijection on residue fields. -/
theorem residueFieldMap_bijective_of_surjective
    {S : Type u} [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Bijective (IsLocalRing.ResidueField.map f) := by
  constructor
  · exact RingHom.injective _
  · intro y
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := hf s
    exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.map_residue f r⟩

/-- Separable closedness is invariant under a ring equivalence of fields. -/
theorem isSepClosed_of_ringEquiv {K L : Type u} [Field K] [Field L]
    [IsSepClosed K] (e : K ≃+* L) : IsSepClosed L := by
  constructor
  intro p hp
  have hs : (p.map e.symm.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp.map
  have hs' := hs.map e.toRingHom
  have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
    apply RingHom.ext
    intro x
    exact e.apply_symm_apply x
  rw [Polynomial.map_map, hcomp, Polynomial.map_id] at hs'
  exact hs'

/-- A quotient of a strictly henselian local ring by an ideal in its maximal ideal is strictly
henselian.  This is the intrinsic strictly-henselian part of Stacks Tag `05WS`. -/
theorem StrictlyHenselianLocalRing.quotient_of_le_maximalIdeal
    [StrictlyHenselianLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    StrictlyHenselianLocalRing (R ⧸ I) := by
  have hIne : I ≠ ⊤ := by
    intro h
    have hm : IsLocalRing.maximalIdeal R = ⊤ :=
      eq_top_iff.mpr (h ▸ hI)
    exact (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).ne_top hm
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let e : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField (R ⧸ I) :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map (Ideal.Quotient.mk I))
      (residueFieldMap_bijective_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)
  exact
    { toHenselianLocalRing :=
        HenselianLocalRing.quotient_of_le_maximalIdeal I hI
      isSepClosed_residueField := isSepClosed_of_ringEquiv e }

end Pcf.Stacks
