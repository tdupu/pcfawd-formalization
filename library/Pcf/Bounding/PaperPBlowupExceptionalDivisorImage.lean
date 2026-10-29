/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupDominatingDivisor
public import Pcf.Bounding.AllCodimBlowupMonodromyTransport
public import Pcf.Bounding.AllCodimBlowupExceptionalNaturality

/-!
# The actual finite lift maps exceptional divisors to exceptional divisors

This supplies the divisor-point part of the component diagram in
`paper-p.tex`, Proposition `prop:bound-blowup`, for affine varieties.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- Over a chosen minimal component of the scheme-theoretic inverse image
of the centre, there is an actual exceptional divisor of the source
normalized blow-up. The finite normalized lift sends it to an exceptional
divisor of the target normalized blow-up, and the two base maps commute
on their generic points. -/
theorem exists_normalizedRees_exceptional_divisor_image
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (P' : Ideal S) (hP' : P' ∈ (I.map f).minimalPrimes) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
    let X' := Palomar.normalization (reesProj (I.map f))
    let Y' := Palomar.normalization (reesProj I)
    let g : X' ⟶ Y' := normalizedReesProjMap f hf hfin I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    let β := normalizedReesProjToSpec I a ha
    ∃ dX : SchemeDivisorPoint X', ∃ dY : SchemeDivisorPoint Y',
      dY.1 = g dX.1 ∧
      α dX.1 = (⟨P', hP'.1.1⟩ : Spec (.of S)) ∧
      dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support ∧
      β dY.1 = (Spec.map (CommRingCat.ofHom f))
        (⟨P', hP'.1.1⟩ : Spec (.of S)) := by
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  have hFT : (f.comp (algebraMap k R)).FiniteType :=
    hfin.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType k S := RingHom.finiteType_algebraMap.mp hFT
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let X' := Palomar.normalization (reesProj (I.map f))
  let Y' := Palomar.normalization (reesProj I)
  let g : X' ⟶ Y' := normalizedReesProjMap f hf hfin I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a ha
  letI : IsFinite g := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsDominant g := normalizedReesProjMap_isDominant f hf hfin I a ha
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpecField (k := k) I)
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsLocallyNoetherian Y' := inferInstance
  obtain ⟨dX, hdX⟩ := exists_normalizedRees_divisorPoint_over_minimalPrime
    k (I.map f) (Ideal.FG.map hI f) b hb P' hP'
  let dY : SchemeDivisorPoint Y' := dX.mapFiniteDominantNormal g
  have hα : α dX.1 = (⟨P', hP'.1.1⟩ : Spec (.of S)) := hdX
  have hsrc : dX.1 ∈ (normalizedReesExceptionalIdealSheaf (I.map f) b hb).support := by
    have h := Set.ext_iff.mp
      (normalizedReesExceptionalIdealSheaf_support (I.map f) b hb) dX.1
    apply h.mpr
    have hzero : (⟨P', hP'.1.1⟩ : Spec (.of S)) ∈
        PrimeSpectrum.zeroLocus ((I.map f) : Set S) :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr hP'.1.2
    change α dX.1 ∈ PrimeSpectrum.zeroLocus ((I.map f) : Set S)
    exact hα ▸ hzero
  have htgt : dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support := by
    have h := Set.ext_iff.mp
      (normalizedReesExceptional_support_preimage f hf hfin I a ha) dX.1
    exact h.mpr hsrc
  refine ⟨dX, dY, rfl, hα, htgt, ?_⟩
  have hcomm := normalizedReesProjToSpec_comm f hf hfin I a ha
  have hpoint := congrArg (fun m => m dX.1) hcomm
  change β (g dX.1) = (Spec.map (CommRingCat.ofHom f)) (α dX.1) at hpoint
  change β (g dX.1) =
    (Spec.map (CommRingCat.ofHom f)) (⟨P', hP'.1.1⟩ : Spec (.of S))
  rw [hα] at hpoint
  exact hpoint

#print axioms exists_normalizedRees_exceptional_divisor_image

end
end Pcf.Bounding.AllCodimBlowup
