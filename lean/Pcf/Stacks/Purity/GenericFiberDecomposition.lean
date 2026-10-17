/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
public import Pcf.Stacks.Purity.NormalRing

/-!
# Generic fibre of a finite normal algebra

The target algebra in Stacks Tag `0BM9` need not be a domain.  Its generic fibre over a normal
local domain is nevertheless a finite product of fields.  This decomposition makes the
disconnected case explicit before applying integral-closure arguments componentwise.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R B K : Type u) [CommRing R] [IsDomain R] [CommRing B] [Field K]
  [Algebra R B] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsFractionRing R K] in
/-- A module-finite algebra has an Artinian generic fibre. -/
theorem genericFiber_isArtinian [Module.Finite R B] :
    IsArtinianRing (K ⊗[R] B) := by
  have : Module.Finite K (K ⊗[R] B) := inferInstance
  exact IsArtinianRing.of_finite K _

omit [IsDomain R] [IsFractionRing R K] in
/-- A finite generic fibre has only finitely many field components. -/
theorem genericFiber_maximalSpectrum_finite [Module.Finite R B] :
    Finite (MaximalSpectrum (K ⊗[R] B)) := by
  letI : IsArtinianRing (K ⊗[R] B) := genericFiber_isArtinian R B K
  infer_instance

omit [IsDomain R] [IsFractionRing R K] in
/-- Every maximal-ideal quotient occurring in the generic-fibre decomposition is a field. -/
theorem genericFiber_component_isField (q : MaximalSpectrum (K ⊗[R] B)) :
    IsField ((K ⊗[R] B) ⧸ q.asIdeal) :=
  (Ideal.Quotient.field q.asIdeal).toIsField

omit [IsDomain R] in
/-- The generic fibre of a Stacks-normal algebra is reduced.  This uses the fact that scalar
extension from a domain to its fraction field is a localization, not a general field extension. -/
theorem genericFiber_isReduced (hB : IsStacksNormalRing B) :
    IsReduced (K ⊗[R] B) := by
  letI : Algebra B (K ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
      (K ⊗[R] B) := inferInstance
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (K ⊗[R] B) hB.isReduced

/-- The disconnected generic fibre of a finite Stacks-normal algebra is canonically a finite
product of its residue fields at maximal ideals. -/
noncomputable def genericFiberEquivPi [Module.Finite R B]
    (hB : IsStacksNormalRing B) :
    (K ⊗[R] B) ≃+* ∀ q : MaximalSpectrum (K ⊗[R] B),
      (K ⊗[R] B) ⧸ q.asIdeal := by
  letI : IsArtinianRing (K ⊗[R] B) := genericFiber_isArtinian R B K
  letI : IsReduced (K ⊗[R] B) := genericFiber_isReduced R B K hB
  exact (IsArtinianRing.equivPi (K ⊗[R] B)).toRingEquiv

end Pcf.Stacks
