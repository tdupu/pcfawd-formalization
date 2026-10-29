/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryPureTensorReduction
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Integral reduction after purely inseparable base change

The proof of `paper-p.tex`, Lemma `lem:primary-fibres`, forms a finite purely
inseparable base change of an integral generic fibre and then reduces it.
The resulting affine schemes remain integral: a purely inseparable field
extension gives a universal homeomorphism on spectra, preserving the unique
generic point. This is the affine algebra component of that step, independent
of finite generation or the later geometric-reducedness alteration.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open AlgebraicGeometry
open scoped TensorProduct

universe u

variable (K L A : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [CommRing A] [IsDomain A] [Algebra K A]

/-- The nilradical of an integral affine algebra after purely inseparable
field base change is prime. Equivalently, the reduction of the base change
has one irreducible component. -/
theorem purelyInseparable_baseChange_nilradical_isPrime :
    (nilradical (A ⊗[K] L)).IsPrime := by
  let T := A ⊗[K] L
  have hhome : IsHomeomorph
      (PrimeSpectrum.comap (algebraMap A T)) :=
    PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K L A
  have hirr : IrreducibleSpace (PrimeSpectrum T) :=
    (IsHomeomorph.homeomorph _ hhome).irreducibleSpace_iff.mpr inferInstance
  exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr

/-- The reduction of an integral affine scheme remains integral after any
purely inseparable field base change. This is the universal-homeomorphism
assertion used before normalizing the altered fibre in
`paper-p.tex`, Lemma `lem:primary-fibres`. -/
theorem purelyInseparable_reduced_baseChange_isDomain :
    IsDomain ((A ⊗[K] L) ⧸ nilradical (A ⊗[K] L)) := by
  have : (nilradical (A ⊗[K] L)).IsPrime :=
    purelyInseparable_baseChange_nilradical_isPrime K L A
  infer_instance

/-- The reduced base change of an integral affine scheme by a purely
inseparable field extension is an integral scheme, in the literal scheme
language used in the primary-fibres argument. -/
theorem purelyInseparable_reduced_baseChange_isIntegralSpec :
    IsIntegral
      (Spec (CommRingCat.of
        ((A ⊗[K] L) ⧸ nilradical (A ⊗[K] L)))) := by
  have : IsDomain ((A ⊗[K] L) ⧸ nilradical (A ⊗[K] L)) :=
    purelyInseparable_reduced_baseChange_isDomain K L A
  infer_instance

#print axioms purelyInseparable_baseChange_nilradical_isPrime
#print axioms purelyInseparable_reduced_baseChange_isDomain
#print axioms purelyInseparable_reduced_baseChange_isIntegralSpec

end Pcf.Bounding.PrimaryFibres
