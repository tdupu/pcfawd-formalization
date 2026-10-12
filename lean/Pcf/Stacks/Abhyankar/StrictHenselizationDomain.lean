/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Flat.TorsionFree
import Pcf.Stacks.Abhyankar.StrictHenselizationDimension

/-!
# Domain lemmas for the strict local colimit

These are bypass lemmas for the terminal application.  They are separate from Stacks Tag `06LN`:
in particular, they do not assert that the strict local colimit is Noetherian.
-/

open CategoryTheory Limits

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]

/-- A pointed etale stage which is a domain embeds in the strict local colimit. -/
theorem toLocalColimitAlgHom_injective_of_isDomain
    (N : PointedEtaleNeighborhood R Ω) [IsDomain N] :
    Function.Injective (toLocalColimitAlgHom (R := R) (Ω := Ω) N) := by
  intro x y hxy
  let z := x - y
  have hz : toLocalColimitAlgHom (R := R) (Ω := Ω) N z = 0 := by
    rw [show z = x - y from rfl, map_sub]
    exact sub_eq_zero.mpr hxy
  obtain ⟨Y, f, hf⟩ :=
    exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero
      (R := R) (Ω := Ω) N z hz
  let _ : Algebra N Y := f.hom.toAlgebra
  let _ : IsScalarTower R N Y :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := N) (A := Y) fun r => by
    change algebraMap R Y r = f.hom (algebraMap R N r)
    exact (f.hom.commutes r).symm
  let _ : Algebra.Etale N Y := Algebra.Etale.of_restrictScalars R N Y
  let _ : Nontrivial Y := Y.point.toRingHom.domain_nontrivial
  have hfinj : Function.Injective f.hom := by
    intro a b hab
    apply sub_eq_zero.mp
    by_contra hne
    have hreg : IsRegular (a - b) := (isRegular_iff_ne_zero).mpr hne
    have hsmul : IsSMulRegular Y (a - b) :=
      Module.Flat.isSMulRegular_of_isRegular (M := Y) hreg
    have hab' : algebraMap N Y a = algebraMap N Y b := hab
    have honezero : (1 : Y) = 0 := hsmul (by
      simp only [Algebra.smul_def, map_sub, hab', sub_self, zero_mul, mul_zero])
    exact one_ne_zero honezero
  apply sub_eq_zero.mp
  apply hfinj
  simpa only [map_zero] using hf

#print axioms toLocalColimitAlgHom_injective_of_isDomain

end Pcf.Stacks.PointedEtaleNeighborhood
