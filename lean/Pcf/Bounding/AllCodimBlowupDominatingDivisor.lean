/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupNormalizedExceptionalChart
public import Pcf.Bounding.AllCodimBlowupExceptionalSurjectivity
public import Pcf.Bounding.AllCodimBlowupExceptionalComponents

/-!
# A codimension-one exceptional point over a minimal centre prime

On a locally Noetherian integral scheme, every point of the support of an
effective Cartier divisor is a specialization of a codimension-one point of
that support (Krull's principal ideal theorem on an affine chart where the
divisor is principal). Applied to the normalized Rees blow-up of a possibly
non-prime centre `I`, this gives a codimension-one exceptional point lying
over any prime minimal over `I`. In `latex/paper-p.tex`, proof of Theorem
`thm:allcodim-normal`, it supplies the component `D'_m` of `α_m⁻¹(A)`
dominating `A`, where `A` is an irreducible component of `V(J_m)`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Every point of the support of an effective Cartier divisor on a locally
Noetherian integral scheme specializes from a codimension-one point of the
support. -/
theorem exists_coheight_one_specializes_of_isEffectiveCartier
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : Pcf.Stacks.SchemeLevel.IsEffectiveCartier D)
    (x : X) (hx : x ∈ D.support) :
    ∃ η : X, Order.coheight η = 1 ∧ η ∈ D.support ∧ η ⤳ x := by
  obtain ⟨U, hxU, s, hs, hDs⟩ := hD x
  let hU : IsAffineOpen (U : X.Opens) := U.2
  let φ := hU.fromSpec
  haveI : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : φ p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hsp : Ideal.span {s} ≤ p.asIdeal := by
    have h1 : x ∈ X.zeroLocus (U := U.1) (D.ideal U) :=
      (Scheme.IdealSheafData.mem_support_iff_of_mem hxU).mp hx
    rw [hDs, ← hpx] at h1
    have h2 : p ∈ φ ⁻¹' X.zeroLocus (U := U.1) ((Ideal.span {s} : Ideal Γ(X, U)) :
        Set Γ(X, U)) := h1
    rw [hU.fromSpec_preimage_zeroLocus] at h2
    exact h2
  obtain ⟨q, hqmin, hqp⟩ := Ideal.exists_minimalPrimes_le hsp
  haveI : q.IsPrime := hqmin.1.1
  let Q : PrimeSpectrum Γ(X, U) := ⟨q, hqmin.1.1⟩
  have hsq : s ∈ q := hqmin.1.2 (Ideal.subset_span rfl)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hheight : q.height = 1 := by
    apply le_antisymm
    · haveI : (Ideal.span {s} : Ideal Γ(X, U)).IsPrincipal := ⟨⟨s, rfl⟩⟩
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hqmin
    · have hbot : (⊥ : Ideal Γ(X, U)) < q := by
        refine lt_of_le_of_ne bot_le ?_
        intro h
        apply hs0
        have : s ∈ (⊥ : Ideal Γ(X, U)) := h ▸ hsq
        simpa using this
      have := Ideal.height_add_one_le_of_lt_of_isPrime hbot
      simpa using this
  refine ⟨φ Q, ?_, ?_, ?_⟩
  · have h := AlgebraicGeometry.coheight_eq_of_isOpenImmersion (x := Q) φ
    rw [h, ← AlgebraicGeometry.idealHeight_eq_coheight Γ(X, U) Q]
    exact hheight
  · have hQU : φ Q ∈ (U : X.Opens) := by
      have : φ Q ∈ Set.range φ := ⟨Q, rfl⟩
      rwa [hU.range_fromSpec] at this
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hQU, hDs]
    change Q ∈ φ ⁻¹' X.zeroLocus (U := U.1) ((Ideal.span {s} : Ideal Γ(X, U)) :
      Set Γ(X, U))
    rw [hU.fromSpec_preimage_zeroLocus]
    exact hqmin.1.2
  · rw [← hpx]
    exact ((PrimeSpectrum.le_iff_specializes Q p).mp hqp).map φ.continuous

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

/-- **A codimension-one exceptional point over a minimal centre prime.** -/
theorem exists_normalizedRees_divisorPoint_over_minimalPrime
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (P' : Ideal R) (hP' : P' ∈ I.minimalPrimes) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    ∃ d : SchemeDivisorPoint (Palomar.normalization (reesProj I)),
      (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) d.1 =
        (⟨P', hP'.1.1⟩ : Spec (.of R)) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let N := Palomar.normalization (reesProj I)
  let q : N ⟶ Spec (.of R) := Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I
  let D := normalizedReesExceptionalIdealSheaf I a ha
  letI : NoetherianSpace (reesProj I) := reesProj_noetherianSpace k I hI
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpecField (k := k) I)
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsLocallyNoetherian N :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
  let y : Spec (.of R) := ⟨P', hP'.1.1⟩
  have hyI : y ∈ PrimeSpectrum.zeroLocus (I : Set R) := hP'.1.2
  have hsupp (z : N) : z ∈ D.support ↔ q z ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
    have h := Set.ext_iff.mp (normalizedReesExceptionalIdealSheaf_support I a ha) z
    exact h
  obtain ⟨x, hx⟩ := normalizedReesProjToSpec_surjective k I hI a ha y
  have hxD : x ∈ D.support := (hsupp x).mpr (hx ▸ hyI)
  obtain ⟨η, hη1, hηD, hηx⟩ := exists_coheight_one_specializes_of_isEffectiveCartier D
    (normalizedReesExceptionalIdealSheaf_isEffectiveCartier I a ha) x hxD
  refine ⟨⟨η, hη1⟩, ?_⟩
  have hqη : q η ⤳ y := hx ▸ hηx.map q.continuous
  have hle : (q η).asIdeal ≤ P' := (PrimeSpectrum.le_iff_specializes _ y).mpr hqη
  have hIle : I ≤ (q η).asIdeal := (hsupp η).mp hηD
  have hge : P' ≤ (q η).asIdeal := hP'.2 ⟨(q η).isPrime, hIle⟩ hle
  exact PrimeSpectrum.ext (le_antisymm hle hge)

#print axioms exists_coheight_one_specializes_of_isEffectiveCartier
#print axioms exists_normalizedRees_divisorPoint_over_minimalPrime

end
end Pcf.Bounding.AllCodimBlowup
