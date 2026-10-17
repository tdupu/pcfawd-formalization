/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Pcf.Bounding.RegularLocalDomain
public import Pcf.Bounding.SmoothRegularLocal
public import Pcf.Stacks.Abhyankar.StrictHenselizationDimension

/-!
# Domain lemmas for the strict local colimit

These are bypass lemmas for the terminal application.  They are separate from Stacks Tag `06LN`:
in particular, they do not assert that the strict local colimit is Noetherian.
-/

@[expose] public section

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

/-- The strict local colimit of a regular local ring is a domain.  A product relation descends to
a pointed etale stage.  Localizing that stage and a zero-killing refinement at their point kernels
gives a flat map from a regular local domain, hence an injection.  One factor therefore vanishes
in the first localization, and the single denominator witnessing this maps to a unit in the strict
local colimit. -/
theorem localColimit_isDomain [IsRegularLocalRing R]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsScalarTower R (IsLocalRing.ResidueField R) Ω]
    [IsSepClosure (IsLocalRing.ResidueField R) Ω] :
    IsDomain (LocalColimit R Ω) := by
  let _ : NoZeroDivisors (LocalColimit R Ω) := ⟨by
    intro a b hab
    let s : Set (LocalColimit R Ω) := {a, b}
    obtain ⟨X, hX⟩ := exists_stage_containing_finite_localColimit_set
      (R := R) (Ω := Ω) s (Set.toFinite s)
    obtain ⟨x, hx⟩ := hX (show a ∈ s by simp [s])
    obtain ⟨y, hy⟩ := hX (show b ∈ s by simp [s])
    have hprod : toLocalColimitAlgHom (R := R) (Ω := Ω) X (x * y) = 0 := by
      rw [map_mul, hx, hy]
      exact hab
    obtain ⟨Y, f, hf⟩ :=
      exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero
        (R := R) (Ω := Ω) X (x * y) hprod
    let _ : Algebra X Y := f.hom.toAlgebra
    let _ : IsScalarTower R X Y :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := X) (A := Y) fun r => by
        change algebraMap R Y r = f.hom (algebraMap R X r)
        exact (f.hom.commutes r).symm
    let _ : Algebra.Etale X Y := Algebra.Etale.of_restrictScalars R X Y
    let QX : Ideal X := RingHom.ker X.point.toRingHom
    let QY : Ideal Y := RingHom.ker Y.point.toRingHom
    let _ : QX.IsPrime := RingHom.ker_isPrime _
    let _ : QY.IsPrime := RingHom.ker_isPrime _
    have hQ : QX = QY.comap f.hom.toRingHom := by
      ext z
      change X.point z = 0 ↔ Y.point (f.hom z) = 0
      change X.point z = 0 ↔ (Y.point.comp f.hom) z = 0
      rw [f.point_comp]
    let L := Localization.AtPrime QX
    let T := Localization.AtPrime QY
    let _ : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L QX
    let _ : IsLocalHom (algebraMap R L) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap R L)).out 4 1).mp
      intro r hr
      rw [Ideal.mem_comap]
      rw [IsScalarTower.algebraMap_apply R X L,
        IsLocalization.AtPrime.to_map_mem_maximal_iff L QX]
      rw [← Ideal.mem_under, point_ker_under (R := R) (Ω := Ω) X]
      exact hr
    let _ : IsRegularLocalRing L :=
      Pcf.Stacks.isRegularLocalRing_of_flat_of_formallyUnramified R L
    let _ : IsDomain L := Pcf.Stacks.isDomain_of_isRegularLocalRing L
    let g : L →ₐ[R] T := Localization.localAlgHom QX QY f.hom hQ
    let _ : Algebra L T := g.toAlgebra
    let _ : IsScalarTower R L T :=
      IsScalarTower.of_algebraMap_eq (R := R) (S := L) (A := T) fun r => by
        exact (g.commutes r).symm
    let _ : IsScalarTower X L T :=
      IsScalarTower.of_algebraMap_eq (R := X) (S := L) (A := T) fun z => by
        change algebraMap Y T (f.hom z) = g (algebraMap X L z)
        exact (Localization.localRingHom_to_map QX QY f.hom.toRingHom hQ z).symm
    let _ : Module.Flat L T := inferInstance
    let _ : Nontrivial T := inferInstance
    have hginj : Function.Injective g := by
      intro c d hcd
      apply sub_eq_zero.mp
      by_contra hne
      have hreg : IsRegular (c - d) := (isRegular_iff_ne_zero).mpr hne
      have hsmul : IsSMulRegular T (c - d) :=
        Module.Flat.isSMulRegular_of_isRegular (M := T) hreg
      have hcd' : algebraMap L T c = algebraMap L T d := hcd
      have honezero : (1 : T) = 0 := hsmul (by
        simp only [Algebra.smul_def, map_sub, hcd', sub_self, zero_mul, mul_zero])
      exact one_ne_zero honezero
    have hxyL : algebraMap X L (x * y) = 0 := by
      apply hginj
      calc
        g (algebraMap X L (x * y)) = algebraMap Y T (f.hom (x * y)) :=
          Localization.localRingHom_to_map QX QY f.hom.toRingHom hQ (x * y)
        _ = 0 := by rw [hf, map_zero]
        _ = g 0 := (map_zero g).symm
    rw [map_mul] at hxyL
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hxyL with hxL | hyL
    · left
      rw [← hx]
      obtain ⟨m, hm⟩ :=
        (IsLocalization.map_eq_zero_iff QX.primeCompl L x).mp hxL
      have hpointm : X.point (m : X) ≠ 0 := by
        intro hzero
        apply m.property
        exact hzero
      let mc : (colimitPointPrime (R := R) (Ω := Ω)).primeCompl :=
        ⟨toColimit (R := R) (Ω := Ω) X m, by
          rw [Ideal.mem_primeCompl_iff]
          change colimitPoint (R := R) (Ω := Ω)
            (toColimit (R := R) (Ω := Ω) X m) ≠ 0
          intro hzero
          apply hpointm
          exact (DFunLike.congr_fun
            (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) (m : X)).symm.trans hzero⟩
      have hunit : IsUnit (toLocalColimitAlgHom (R := R) (Ω := Ω) X m) := by
        exact IsLocalization.map_units (LocalColimit R Ω) mc
      apply hunit.mul_left_cancel
      have hm' := congrArg (toLocalColimitAlgHom (R := R) (Ω := Ω) X) hm
      simpa only [map_mul, map_zero, mul_zero] using hm'
    · right
      rw [← hy]
      obtain ⟨m, hm⟩ :=
        (IsLocalization.map_eq_zero_iff QX.primeCompl L y).mp hyL
      have hpointm : X.point (m : X) ≠ 0 := by
        intro hzero
        apply m.property
        exact hzero
      let mc : (colimitPointPrime (R := R) (Ω := Ω)).primeCompl :=
        ⟨toColimit (R := R) (Ω := Ω) X m, by
          rw [Ideal.mem_primeCompl_iff]
          change colimitPoint (R := R) (Ω := Ω)
            (toColimit (R := R) (Ω := Ω) X m) ≠ 0
          intro hzero
          apply hpointm
          exact (DFunLike.congr_fun
            (colimitPoint_comp_toColimit (R := R) (Ω := Ω) X) (m : X)).symm.trans hzero⟩
      have hunit : IsUnit (toLocalColimitAlgHom (R := R) (Ω := Ω) X m) := by
        exact IsLocalization.map_units (LocalColimit R Ω) mc
      apply hunit.mul_left_cancel
      have hm' := congrArg (toLocalColimitAlgHom (R := R) (Ω := Ω) X) hm
      simpa only [map_mul, map_zero, mul_zero] using hm'
  ⟩
  exact NoZeroDivisors.to_isDomain (LocalColimit R Ω)

#print axioms toLocalColimitAlgHom_injective_of_isDomain
#print axioms localColimit_isDomain

end Pcf.Stacks.PointedEtaleNeighborhood
