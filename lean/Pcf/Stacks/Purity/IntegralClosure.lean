/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Pcf.Stacks.Purity.NormalRing

/-!
# The finite-separable integral-closure input of Tag 0BM9

In the proof of Stacks Tag `0BM9`, a connected finite étale cover of the punctured spectrum
has a finite separable function-field extension.  Its affine extension is obtained from the
integral closure of the base in that field extension.

This file records the part of that construction already supported by the pinned Mathlib
revision: the integral closure is module-finite and is a normal domain, hence normal in the
possibly-disconnected Stacks sense used by the target category in `FiniteNormalAlgebra.lean`.
It does not assert the depth-two/reflexive Hartogs recovery needed to identify its restriction
with the original punctured cover.
-/

@[expose] public section

noncomputable section

namespace Pcf.Stacks

variable (A L C : Type*) [CommRing A] [Field L] [CommRing C]
variable [Algebra A L]
variable [Algebra C L] [IsIntegralClosure C A L]
variable [Algebra A C] [IsScalarTower A C L]
include L

/-- Any chosen integral closure in a finite field extension of the fraction field is a domain.
This is the domain component of the normal-algebra construction in Tag `0BM9`. -/
theorem IsIntegralClosure.isDomain_of_isIntegralClosureInField [IsDomain A] : IsDomain C :=
  (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain
    (integralClosure A L)

variable (K : Type*) [Field K]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [IsScalarTower A K L]
variable [FiniteDimensional K L]
include K L

/-- Any chosen integral closure in a finite field extension of the fraction field is integrally
closed.  This transports Mathlib's theorem for the canonical integral closure across the
canonical algebra equivalence. -/
theorem IsIntegralClosure.isIntegrallyClosed_of_finiteExtension [IsDomain A] :
    IsIntegrallyClosed C := by
  let _ : IsIntegrallyClosed (integralClosure A L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  exact IsIntegrallyClosed.of_equiv
    (IsIntegralClosure.equiv A C L (integralClosure A L)).symm.toRingEquiv

/-- The integral closure used in the connected component of Tag `0BM9` is normal in the literal
Stacks sense. -/
theorem IsIntegralClosure.isStacksNormalRing_of_finiteExtension [IsDomain A] :
    IsStacksNormalRing C := by
  let _ : IsDomain C :=
    IsIntegralClosure.isDomain_of_isIntegralClosureInField (A := A) (L := L) (C := C)
  let _ : IsIntegrallyClosed C :=
    IsIntegralClosure.isIntegrallyClosed_of_finiteExtension
      (A := A) (K := K) (L := L) (C := C)
  exact IsStacksNormalRing.of_isDomain

/-- The integral closure of a Noetherian normal domain in a finite separable extension of its
fraction field is module-finite.  This is the finiteness input in the integral-closure
construction of Tag `0BM9`; the remaining recovery step is a separate Hartogs theorem. -/
theorem IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
    [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [Algebra.IsSeparable K L] :
    Module.Finite A C :=
  IsIntegralClosure.finite A K L C

end Pcf.Stacks
