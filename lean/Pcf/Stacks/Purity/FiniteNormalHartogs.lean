/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Pcf.Stacks.Purity.FiniteModuleHartogs

/-!
# Hartogs recovery for finite normal algebras

This file transfers the module intersection theorem to regular functions on an open of an affine
scheme.  The only geometric input is injectivity of restriction to one of the two basic opens.
For the punctured restriction of a finite normal algebra this injectivity comes from its generic
fibre.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

set_option backward.isDefEq.respectTransparency false in
/-- Restriction between opens of an affine spectrum commutes with the canonical algebra maps
from its coordinate ring. -/
theorem spec_algebraMap_res {B : CommRingCat.{u}} {U V : (Spec B).Opens}
    (hVU : V ≤ U) (b : B) :
    (Spec B).presheaf.map (homOfLE hVU).op (algebraMap B Γ(Spec B, U) b) =
      algebraMap B Γ(Spec B, V) b := by
  rw [IsAffineOpen.algebraMap_Spec_obj, IsAffineOpen.algebraMap_Spec_obj]
  have hmorph : (Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
          (Spec B).presheaf.map (homOfLE hVU).op =
      (Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op := by
    rw [← Functor.map_comp, ← op_comp, homOfLE_comp]
  exact congrArg (fun f : B ⟶ Γ(Spec B, V) => f.hom b) hmorph

variable {R : Type u} [CommRing R]
variable {B : CommRingCat.{u}} [Algebra R B]

set_option backward.isDefEq.respectTransparency false in
/-- If an open of an affine spectrum contains the basic opens of a module-regular pair and
restriction to the first one is injective, every regular function on the open comes from the
coordinate ring. -/
theorem openSections_algebraMap_surjective_of_module_regularPair
    {W : (Spec B).Opens} {x y : R}
    (hx : IsSMulRegular B x)
    (hyB : IsSMulRegular B y)
    (hy : IsSMulRegular (QuotSMulTop x B) y)
    (hDx : PrimeSpectrum.basicOpen (algebraMap R B x) ≤ W)
    (hDy : PrimeSpectrum.basicOpen (algebraMap R B y) ≤ W)
    (hinj : Function.Injective
      ((Spec B).presheaf.map (homOfLE hDx).op).hom) :
    Function.Surjective (algebraMap B Γ(Spec B, W)) := by
  let xb : B := algebraMap R B x
  let yb : B := algebraMap R B y
  let Dx : (Spec B).Opens := PrimeSpectrum.basicOpen xb
  let Dy : (Spec B).Opens := PrimeSpectrum.basicOpen yb
  let Dxy : (Spec B).Opens := PrimeSpectrum.basicOpen (xb * yb)
  letI : Algebra B Γ(Spec B, Dx) := inferInstance
  letI : Algebra B Γ(Spec B, Dy) := inferInstance
  letI : Algebra B Γ(Spec B, Dxy) := inferInstance
  intro s
  let sx : Γ(Spec B, Dx) := (Spec B).presheaf.map (homOfLE hDx).op s
  let sy : Γ(Spec B, Dy) := (Spec B).presheaf.map (homOfLE hDy).op s
  let dx := IsLocalization.Away.sec xb sx
  let dy := IsLocalization.Away.sec yb sy
  have hsx := IsLocalization.Away.sec_spec xb sx
  have hsy := IsLocalization.Away.sec_spec yb sy
  have hDxyDx : Dxy ≤ Dx := PrimeSpectrum.basicOpen_mul_le_left xb yb
  have hDxyDy : Dxy ≤ Dy := PrimeSpectrum.basicOpen_mul_le_right xb yb
  have hsxy : (Spec B).presheaf.map (homOfLE hDxyDx).op sx =
      (Spec B).presheaf.map (homOfLE hDxyDy).op sy := by
    have hmorph : (Spec B).presheaf.map (homOfLE hDx).op ≫
        (Spec B).presheaf.map (homOfLE hDxyDx).op =
        (Spec B).presheaf.map (homOfLE hDy).op ≫
          (Spec B).presheaf.map (homOfLE hDxyDy).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        homOfLE_comp, homOfLE_comp]
    exact congrArg (fun f : Γ(Spec B, W) ⟶ Γ(Spec B, Dxy) => f.hom s) hmorph
  have hsx' := congrArg
    (fun z : Γ(Spec B, Dx) => (Spec B).presheaf.map (homOfLE hDxyDx).op z) hsx
  have hsy' := congrArg
    (fun z : Γ(Spec B, Dy) => (Spec B).presheaf.map (homOfLE hDxyDy).op z) hsy
  have hsx'' :
      (Spec B).presheaf.map (homOfLE hDxyDx).op sx *
          algebraMap B Γ(Spec B, Dxy) (xb ^ dx.2) =
        algebraMap B Γ(Spec B, Dxy) dx.1 := by
    simpa only [map_mul, spec_algebraMap_res] using hsx'
  have hsy'' :
      (Spec B).presheaf.map (homOfLE hDxyDy).op sy *
          algebraMap B Γ(Spec B, Dxy) (yb ^ dy.2) =
        algebraMap B Γ(Spec B, Dxy) dy.1 := by
    simpa only [map_mul, spec_algebraMap_res] using hsy'
  have hxb : IsRegular xb := by
    constructor
    · intro a b hab
      apply hx
      simpa only [Algebra.smul_def] using hab
    · intro a b hab
      apply hx
      simpa only [Algebra.smul_def, mul_comm] using hab
  have hyb : IsRegular yb := by
    constructor
    · intro a b hab
      apply hyB
      simpa only [Algebra.smul_def] using hab
    · intro a b hab
      apply hyB
      simpa only [Algebra.smul_def, mul_comm] using hab
  have hxy : IsRegular (xb * yb) := hxb.mul hyb
  have hmapinj : Function.Injective
      (algebraMap B Γ(Spec B, Dxy)) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply (IsLocalization.to_map_eq_zero_iff
      (S := Γ(Spec B, Dxy)) (M := Submonoid.powers (xb * yb)) ?_).mp
    · rw [map_sub, hab, sub_self]
    · intro z hz
      obtain ⟨n, rfl⟩ := hz
      exact (hxy.pow n).mem_nonZeroDivisors
  have hcross : y ^ dy.2 • dx.1 = x ^ dx.2 • dy.1 := by
    apply hmapinj
    dsimp only [xb, yb] at hsx'' hsy'' ⊢
    simp only [Algebra.smul_def, map_pow]
    rw [map_mul, map_mul, ← hsx'', ← hsy'', hsxy]
    ac_rfl
  obtain ⟨c, hcx, -⟩ :=
    exists_common_value_of_module_regular_pair hx hy dy.2 dx.2 hcross
  refine ⟨c, ?_⟩
  apply hinj
  change (Spec B).presheaf.map (homOfLE hDx).op
      (algebraMap B Γ(Spec B, W) c) = sx
  rw [spec_algebraMap_res]
  have hu : IsUnit (algebraMap B Γ(Spec B, Dx) (xb ^ dx.2)) :=
    IsLocalization.map_units Γ(Spec B, Dx)
      ⟨xb ^ dx.2, Submonoid.pow_mem _ (Submonoid.mem_powers xb) _⟩
  apply hu.mul_right_cancel
  rw [hsx, ← map_mul]
  apply congrArg (algebraMap B Γ(Spec B, Dx))
  rw [mul_comm]
  dsimp only [xb]
  rw [← map_pow, ← Algebra.smul_def]
  exact hcx.symm

set_option backward.isDefEq.respectTransparency false in
/-- Under the same hypotheses, the coordinate ring is recovered bijectively from regular
functions on the open. -/
theorem openSections_algebraMap_bijective_of_module_regularPair
    {W : (Spec B).Opens} {x y : R}
    (hx : IsSMulRegular B x)
    (hyB : IsSMulRegular B y)
    (hy : IsSMulRegular (QuotSMulTop x B) y)
    (hDx : PrimeSpectrum.basicOpen (algebraMap R B x) ≤ W)
    (hDy : PrimeSpectrum.basicOpen (algebraMap R B y) ≤ W)
    (hinj : Function.Injective
      ((Spec B).presheaf.map (homOfLE hDx).op).hom) :
    Function.Bijective (algebraMap B Γ(Spec B, W)) := by
  refine ⟨?_, openSections_algebraMap_surjective_of_module_regularPair
    hx hyB hy hDx hDy hinj⟩
  let xb : B := algebraMap R B x
  let Dx : (Spec B).Opens := PrimeSpectrum.basicOpen xb
  letI : Algebra B Γ(Spec B, Dx) := inferInstance
  have hxb : IsRegular xb := by
    constructor
    · intro a b hab
      apply hx
      simpa only [Algebra.smul_def] using hab
    · intro a b hab
      apply hx
      simpa only [Algebra.smul_def, mul_comm] using hab
  have hmapinj : Function.Injective (algebraMap B Γ(Spec B, Dx)) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply (IsLocalization.to_map_eq_zero_iff
      (S := Γ(Spec B, Dx)) (M := Submonoid.powers xb) ?_).mp
    · rw [map_sub, hab, sub_self]
    · intro z hz
      obtain ⟨n, rfl⟩ := hz
      exact (hxb.pow n).mem_nonZeroDivisors
  intro a b hab
  apply hmapinj
  rw [← spec_algebraMap_res hDx a, ← spec_algebraMap_res hDx b, hab]

end Pcf.Stacks
