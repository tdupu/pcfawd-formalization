/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFibres
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Flat.Basic

/-!
# A finite purely inseparable case of the altered generic fibre

For a purely inseparable field extension `L/K`, the multiplication map
`L ⊗[K] L → L` has nilpotent kernel. Thus the reduction of the base change
of `Spec L` from `K` to `L` is `Spec L`. When `L/K` is finite, this is a
concrete special case of the finite purely inseparable alteration in
`paper-p.tex`, Lemma `lem:primary-fibres` (Stacks Tag 04KT). It does not
give the general finite-type alteration used there.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open Algebra
open scoped TensorProduct

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L]

/-- The multiplication map of the purely inseparable tensor square has
exactly the nilradical as its kernel. -/
theorem purelyInseparable_tensor_mul_ker_eq_nilradical :
    RingHom.ker (Algebra.TensorProduct.lmul'' K (S := L)).toRingHom =
      nilradical (L ⊗[K] L) := by
  let m := Algebra.TensorProduct.lmul'' K (S := L)
  ext x
  rw [RingHom.mem_ker, mem_nilradical]
  constructor
  · intro hx
    change m x = 0 at hx
    obtain ⟨n, hn, a, ha⟩ :=
      IsPurelyInseparable.exists_pow_mem_range_tensorProduct (k := K) (K := L) x
    have hma : a = 0 := by
      have hm : (m x) ^ n = a := by
        calc
          (m x) ^ n = m (x ^ n) := (map_pow m x n).symm
          _ = m (algebraMap L (L ⊗[K] L) a) := congrArg m ha.symm
          _ = a := m.commutes a
      have hzero : (0 : L) = a := by
        simpa [hx, zero_pow (Nat.ne_of_gt hn)] using hm
      exact hzero.symm
    exact ⟨n, by simpa [hma] using ha.symm⟩
  · rintro ⟨n, hn⟩
    have hmn : (m x) ^ n = 0 := by simpa only [map_pow, map_zero] using congrArg m hn
    exact eq_zero_of_pow_eq_zero hmn

/-- The reduction of the base change of `Spec L` from `K` to `L` has
coordinate ring `L`; the equivalence respects the new `L`-algebra
structure. -/
noncomputable def purelyInseparable_reduced_tensor_equiv :
    ((L ⊗[K] L) ⧸ nilradical (L ⊗[K] L)) ≃ₐ[L] L := by
  let m := Algebra.TensorProduct.lmul'' K (S := L)
  have hs : Function.Surjective m := by
    intro a
    exact ⟨algebraMap L (L ⊗[K] L) a, m.commutes a⟩
  have hker : RingHom.ker m.toRingHom = nilradical (L ⊗[K] L) :=
    purelyInseparable_tensor_mul_ker_eq_nilradical K L
  have hker' : RingHom.ker m = nilradical (L ⊗[K] L) := hker
  let e := Ideal.quotientKerAlgEquivOfSurjective hs
  exact hker' ▸ e

/-- A field is geometrically reduced over itself. -/
theorem field_geometricallyReduced_self (F : Type u) [Field F] :
    Algebra.IsGeometricallyReduced F F := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_injective
    (Algebra.TensorProduct.rid F F (AlgebraicClosure F)).toRingHom
    (Algebra.TensorProduct.rid F F (AlgebraicClosure F)).injective

/-- In the finite purely inseparable field case of Stacks Tag 04KT, one
may take the altering field to be `L` itself. The reduction of the
base-changed generic fibre is geometrically reduced over `L`. -/
@[stacks 04KT "finite purely inseparable field case"]
theorem finitePurelyInseparable_reduced_tensor_geometricallyReduced
    [FiniteDimensional K L] :
    Algebra.IsGeometricallyReduced L
      ((L ⊗[K] L) ⧸ nilradical (L ⊗[K] L)) := by
  have : Algebra.IsGeometricallyReduced L L :=
    field_geometricallyReduced_self L
  exact Algebra.IsGeometricallyReduced.of_injective
    (purelyInseparable_reduced_tensor_equiv K L).toAlgHom
    (purelyInseparable_reduced_tensor_equiv K L).injective

/-- Purely inseparable base change of an arbitrary field extension has a
single reduced field factor. This is the compositum step in the proof of
Stacks Tag 030R, used by Tag 04KT. The field need not be finitely generated
over the original base. -/
theorem purelyInseparable_reduced_tensor_isField
    (E : Type u) [Field E] [Algebra K E] :
    IsField ((E ⊗[K] L) ⧸ nilradical (E ⊗[K] L)) := by
  let T := E ⊗[K] L
  have hhome : IsHomeomorph
      (PrimeSpectrum.comap (algebraMap E T)) :=
    PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K L E
  have : Subsingleton (PrimeSpectrum T) := hhome.injective.subsingleton
  have hquot : Function.Bijective
      (PrimeSpectrum.comap (Ideal.Quotient.mk (nilradical T))) :=
    PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl
  have : Subsingleton (PrimeSpectrum (T ⧸ nilradical T)) :=
    hquot.injective.subsingleton
  have : IsReduced (T ⧸ nilradical T) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (Ideal.radical_isRadical (0 : Ideal T))
  have hproper : nilradical T ≠ ⊤ := by
    intro h
    have hm : (1 : T) ∈ nilradical T := by rw [h]; trivial
    obtain ⟨n, hn⟩ := (mem_nilradical.mp hm)
    have hmap : Function.Injective (algebraMap E T) :=
      Algebra.TensorProduct.includeLeft_injective (S := E) (algebraMap K L).injective
    have h10 : (1 : T) = 0 := by simpa using hn
    exact one_ne_zero (hmap (by simpa only [map_one, map_zero] using h10))
  have : Nontrivial (T ⧸ nilradical T) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp inferInstance

#print axioms purelyInseparable_tensor_mul_ker_eq_nilradical
#print axioms purelyInseparable_reduced_tensor_equiv
#print axioms finitePurelyInseparable_reduced_tensor_geometricallyReduced
#print axioms purelyInseparable_reduced_tensor_isField

end Pcf.Bounding.PrimaryFibres
