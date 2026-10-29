/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryNormalizationHomeomorph

/-!
# Descent of a good dense open through purely inseparable normalization

In `paper-p.tex`, Lemma `lem:primary-fibres`, a good dense open on the
purely inseparable normalized base is descended to the original base by
removing the image of its closed complement. The normalization is a
homeomorphism on underlying prime spectra, so this descent is exact.

The existence of the good open with geometrically reduced fibres is the
separate Stacks Tag 0578 step and is not asserted here.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open TopologicalSpace

/-- Every dense open of the actual purely inseparable integral closure is
the inverse image of a dense open of the normal base. This is the
dense-open descent step of `paper-p.tex`, Lemma `lem:primary-fibres`. -/
theorem integralClosure_denseOpen_descends
    (R K L : Type*) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsPurelyInseparable K L]
    (p : ℕ) [ExpChar K p]
    (V : Opens (PrimeSpectrum (integralClosure R L)))
    (hV : Dense (V : Set (PrimeSpectrum (integralClosure R L)))) :
    ∃ U : Opens (PrimeSpectrum R),
      Dense (U : Set (PrimeSpectrum R)) ∧
      (PrimeSpectrum.comap (algebraMap R (integralClosure R L))) ⁻¹'
        (U : Set (PrimeSpectrum R)) =
          (V : Set (PrimeSpectrum (integralClosure R L))) := by
  let f := PrimeSpectrum.comap (algebraMap R (integralClosure R L))
  have hf : IsHomeomorph f := integralClosure_isHomeomorph_comap R K L p
  let U : Opens (PrimeSpectrum R) :=
    ⟨f '' (V : Set (PrimeSpectrum (integralClosure R L))),
      hf.isOpenMap _ V.isOpen⟩
  refine ⟨U, ?_, ?_⟩
  · change Dense (f '' (V : Set (PrimeSpectrum (integralClosure R L))))
    rw [dense_iff_closure_eq, ← hf.image_closure, hV.closure_eq]
    exact Set.image_univ_of_surjective hf.surjective
  · exact Set.preimage_image_eq _ hf.injective

#print axioms integralClosure_denseOpen_descends

end Pcf.Bounding.PrimaryFibres
