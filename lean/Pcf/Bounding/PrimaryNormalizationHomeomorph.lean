/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFibres
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Topology of purely inseparable normalization

The root property for the integral closure in `PrimaryFibres` shows more
than uniqueness of primes. It identifies the underlying topological
spaces of the normalization and its normal base. This is the topological
part of the radicial morphism used in `paper-p.tex`, Lemma
`lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

/-- The map on prime spectra of the actual integral closure in a purely
inseparable function-field extension is a homeomorphism. -/
theorem integralClosure_isHomeomorph_comap
    (R K L : Type*) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsPurelyInseparable K L]
    (p : ℕ) [ExpChar K p] :
    IsHomeomorph
      (PrimeSpectrum.comap (algebraMap R (integralClosure R L))) := by
  apply PrimeSpectrum.isHomeomorph_comap
  · intro x
    obtain ⟨n, r, hr⟩ :=
      integralClosure_pow_mem_base (R := R) (K := K) (L := L) p x
    refine ⟨p ^ n, expChar_pow_pos K p n, ⟨r, ?_⟩⟩
    apply Subtype.val_injective
    simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hr.symm
  · have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
      intro a b h
      have hL := congrArg (fun z : integralClosure R L => (z : L)) h
      have hKL : algebraMap R L a = algebraMap R L b := by
        simpa only [Subalgebra.coe_algebraMap] using hL
      apply IsFractionRing.injective R K
      apply FaithfulSMul.algebraMap_injective K L
      simpa only [← IsScalarTower.algebraMap_apply R K L] using hKL
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le

#print axioms integralClosure_isHomeomorph_comap

end Pcf.Bounding.PrimaryFibres
