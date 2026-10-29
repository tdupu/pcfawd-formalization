/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localizing a hypersurface ring at a prime

For `R = A ⧸ (f)` and a prime `𝔮` of `R` with preimage `Q` in `A`,
`R_𝔮 ≅ A_Q ⧸ (f)`. Used for the singular locus and the Cohen–Macaulay property of the
hypersurface in `ex:charp-exceptional-fibre-paper`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalLocal

variable {A : Type*} [CommRing A] (f : A) (𝔮 : Ideal (A ⧸ Ideal.span {f})) [𝔮.IsPrime]

/-- The preimage of `𝔮` in `A`. -/
abbrev liftPrime : Ideal A := 𝔮.comap (Ideal.Quotient.mk _)

instance : (liftPrime f 𝔮).IsPrime := Ideal.comap_isPrime _ _

theorem algebraMapSubmonoid_primeCompl :
    Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {f}) (liftPrime f 𝔮).primeCompl =
      𝔮.primeCompl := by
  ext r
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hr
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨a, hr, rfl⟩

theorem map_span_singleton_localization :
    (Ideal.span {f}).map (algebraMap A (Localization.AtPrime (liftPrime f 𝔮))) =
      Ideal.span {algebraMap A (Localization.AtPrime (liftPrime f 𝔮)) f} := by
  rw [Ideal.map_span, Set.image_singleton]

instance isLocalization_quotient :
    IsLocalization.AtPrime
      (Localization.AtPrime (liftPrime f 𝔮) ⧸
        (Ideal.span {f}).map (algebraMap A (Localization.AtPrime (liftPrime f 𝔮)))) 𝔮 := by
  have h := (inferInstance : IsLocalization
    (Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {f}) (liftPrime f 𝔮).primeCompl)
    (Localization.AtPrime (liftPrime f 𝔮) ⧸
        (Ideal.span {f}).map (algebraMap A (Localization.AtPrime (liftPrime f 𝔮)))))
  rwa [algebraMapSubmonoid_primeCompl] at h

/-- **`R_𝔮 ≅ A_Q ⧸ (f)`.** -/
noncomputable def localizationQuotientEquiv :
    Localization.AtPrime 𝔮 ≃+*
      Localization.AtPrime (liftPrime f 𝔮) ⧸
        Ideal.span {algebraMap A (Localization.AtPrime (liftPrime f 𝔮)) f} :=
  ((IsLocalization.algEquiv 𝔮.primeCompl (Localization.AtPrime 𝔮)
    (Localization.AtPrime (liftPrime f 𝔮) ⧸
        (Ideal.span {f}).map
          (algebraMap A (Localization.AtPrime (liftPrime f 𝔮))))).toRingEquiv).trans
    (Ideal.quotEquivOfEq (map_span_singleton_localization f 𝔮))

end Pcf.Examples.PaperP.CharPExceptionalLocal
