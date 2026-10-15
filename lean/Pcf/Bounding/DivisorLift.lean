/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeExtraction

/-!
# Lifting divisors through finite dominant morphisms

This file packages the scheme-level form of `lem:lift`.  For a finite dominant morphism
of integral schemes, every point above a codimension-one point is again codimension one.
Consequently, when the target is of finite type over a field, the canonical pushforward
on divisor points is surjective and has finite fibres.

The codimension argument uses only lying over and incomparability for the finite affine
extension over an affine neighbourhood of the target point.  No normality hypothesis is
needed on either scheme.
-/

@[expose] public section

open TopologicalSpace
open AlgebraicGeometry

namespace Pcf

universe u

set_option linter.style.haveILetI false

/-- A point above a codimension-one point under a finite dominant morphism of integral
schemes is codimension one.  This is the scheme-global form of the existence direction
in `height_eq_one_of_liesOver_heightOne`. -/
theorem coheight_eq_one_of_finite_preimage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    (x : X) (hx : Order.coheight (f x) = 1) :
    Order.coheight x = 1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hfxW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
  let U : Y.affineOpens := ⟨W, hW⟩
  let V := finitePreimageAffine f U
  have hxV : x ∈ (V : X.Opens) := hfxW
  letI : Nonempty (U : Y.Opens) := ⟨⟨f x, hfxW⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨x, hxV⟩⟩
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, V) := finitePreimageModuleFinite f U
  letI : FaithfulSMul Γ(Y, U) Γ(X, V) := finitePreimageFaithfulSMul f U
  let Q : Ideal Γ(X, V) := (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  let q : Ideal Γ(Y, U) := (U.2.primeIdealOf ⟨f x, hfxW⟩).asIdeal
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : q.IsPrime := by
    dsimp only [q]
    infer_instance
  have hAlg : algebraMap Γ(Y, U) Γ(X, V) =
      (f.appLE U V le_rfl).hom := by
    change (f.app U).hom = (f.appLE U V le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hcontract : Q.under Γ(Y, U) = q := by
    change Q.comap (algebraMap Γ(Y, U) Γ(X, V)) = q
    rw [hAlg]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hxV)
  let hU : IsAffineOpen (U : Y.Opens) := U.2
  let p : AlgebraicGeometry.Spec Γ(Y, U) :=
    hU.primeIdealOf ⟨f x, hfxW⟩
  have htarget := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (x := p) hU.fromSpec
  rw [hU.fromSpec_primeIdealOf] at htarget
  have hpcoheight : Order.coheight p = 1 := htarget.symm.trans hx
  have hqheight : q.height = 1 :=
    (AlgebraicGeometry.idealHeight_eq_coheight Γ(Y, U) p).trans hpcoheight
  have hQheight : Q.height = 1 :=
    height_eq_one_of_liesOver_heightOne Q q ⟨hcontract.symm⟩ hqheight
  let hV : IsAffineOpen (V : X.Opens) := V.2
  let P : AlgebraicGeometry.Spec Γ(X, V) :=
    hV.primeIdealOf ⟨x, hxV⟩
  have hsource := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (x := P) hV.fromSpec
  rw [hV.fromSpec_primeIdealOf] at hsource
  exact hsource.trans <|
    (AlgebraicGeometry.idealHeight_eq_coheight Γ(X, V) P).symm.trans <| by
      simpa only [Q, P] using hQheight

section FiniteType

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y]
variable (k : Type*) [Field k]
  [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
  [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)]

/-- Every divisor downstairs has a divisor above it under a finite dominant morphism
whose target is of finite type over a field. -/
theorem SchemeDivisorPoint.mapFiniteDominantFiniteType_surjective :
    Function.Surjective (fun x : SchemeDivisorPoint X ↦
      x.mapFiniteDominantFiniteType f k) := by
  intro y
  obtain ⟨x, hx⟩ := f.surjective y.1
  have hcodim : Order.coheight x = 1 :=
    coheight_eq_one_of_finite_preimage f x (by simpa [hx] using y.2)
  exact ⟨⟨x, hcodim⟩, Subtype.ext hx⟩

/-- The canonical divisor map has finite fibres. -/
theorem SchemeDivisorPoint.mapFiniteDominantFiniteType_finite_fiber
    (y : SchemeDivisorPoint Y) :
    ((fun x : SchemeDivisorPoint X ↦ x.mapFiniteDominantFiniteType f k) ⁻¹' {y}).Finite := by
  exact Scheme.Hom.finite_divisorPoint_subtype_fiber f
    (coheight_apply_eq_one_of_finiteType f k) y

/-- Scheme-level `lem:lift`: the canonical divisor pushforward is surjective and has
finite fibres.  This simultaneously records existence of a divisor above every target
divisor and finiteness of all such divisors. -/
theorem finiteDominantFiniteType_divisor_lift :
    Function.Surjective (fun x : SchemeDivisorPoint X ↦
      x.mapFiniteDominantFiniteType f k) ∧
      ∀ y : SchemeDivisorPoint Y,
        ((fun x : SchemeDivisorPoint X ↦ x.mapFiniteDominantFiniteType f k) ⁻¹' {y}).Finite :=
  ⟨SchemeDivisorPoint.mapFiniteDominantFiniteType_surjective f k,
    SchemeDivisorPoint.mapFiniteDominantFiniteType_finite_fiber f k⟩

end FiniteType

#print axioms coheight_eq_one_of_finite_preimage
#print axioms SchemeDivisorPoint.mapFiniteDominantFiniteType_surjective
#print axioms SchemeDivisorPoint.mapFiniteDominantFiniteType_finite_fiber
#print axioms finiteDominantFiniteType_divisor_lift

end Pcf
