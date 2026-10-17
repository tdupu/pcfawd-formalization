/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.DivisorRootLocalization
public import Pcf.Stacks.Abhyankar.NormalizationBaseChange

/-!
# Localizing an actual normalization

This file records the normalization-localization comparison used at a divisor point in
Stacks Tag `0EYG`.  Starting with an actual integral-closure model `N` of `R` in `D`, it
constructs the canonical map between their localizations at a multiplicative system of
`R` and proves that the localized model is the integral closure of the localized base in
the localized generic algebra.  Uniqueness of integral closure then gives the comparison
with the literal canonical normalization.

The construction uses the localization base-change theorem for integral closure; no
normalization equivalence is assumed.
-/

@[expose] public section

universe u

open TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

noncomputable section

attribute [local instance] normalizationBaseChangeAlgebra

/-- The integral-closure comparison for an arbitrary localization.  Unlike the smooth
base-change comparison, this applies to a localization at an arbitrary submonoid. -/
noncomputable def localizationBaseChangeIntegralClosureEquiv
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) :
    Localization M ⊗[R] N ≃ₐ[Localization M]
      integralClosure (Localization M) (Localization M ⊗[R] D) :=
  (Algebra.TensorProduct.congr (.refl (R := Localization M) (A₁ := Localization M))
    (IsIntegralClosure.equiv R N D (integralClosure R D))).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R (Localization M) D)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization M))

/-- The arbitrary-localization comparison agrees with the base-changed embedding into
the localized generic algebra. -/
theorem localizationBaseChangeIntegralClosureEquiv_val
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) (x : Localization M ⊗[R] N) :
    ((localizationBaseChangeIntegralClosureEquiv R N D M x :
        integralClosure (Localization M) (Localization M ⊗[R] D)) :
      Localization M ⊗[R] D) =
      algebraMap (Localization M ⊗[R] N) (Localization M ⊗[R] D) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      change x ⊗ₜ[R] ((IsIntegralClosure.equiv R N D (integralClosure R D) y :
          integralClosure R D) : D) =
        (Algebra.TensorProduct.map (AlgHom.id (Localization M) (Localization M))
          (IsScalarTower.toAlgHom R N D)) (x ⊗ₜ[R] y)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun z : D => x ⊗ₜ[R] z)
        (IsIntegralClosure.algebraMap_equiv R N D (integralClosure R D) y)

/-- Integral closure commutes with arbitrary localization, in the exact
`IsIntegralClosure` form used for a localized normalization component. -/
theorem localizationBaseChange_isIntegralClosure
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) :
    IsIntegralClosure (Localization M ⊗[R] N) (Localization M)
      (Localization M ⊗[R] D) := by
  let e := localizationBaseChangeIntegralClosureEquiv R N D M
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    rw [localizationBaseChangeIntegralClosureEquiv_val,
      localizationBaseChangeIntegralClosureEquiv_val, hxy]
  · intro x
    constructor
    · intro hx
      let z : integralClosure (Localization M) (Localization M ⊗[R] D) := ⟨x, hx⟩
      refine ⟨e.symm z, ?_⟩
      rw [← localizationBaseChangeIntegralClosureEquiv_val]
      simp [e, z]
    · rintro ⟨y, rfl⟩
      rw [← localizationBaseChangeIntegralClosureEquiv_val]
      exact (e y).2

/-- Transport an integral-closure structure across an equivalence of its integral models,
provided the two embeddings in the common ambient algebra agree. -/
theorem isIntegralClosure_of_modelEquiv
    (R A A' B : Type u)
    [CommRing R] [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B]
    [Algebra A B] [Algebra A' B]
    [IsScalarTower R A B] [IsScalarTower R A' B]
    [IsIntegralClosure A R B]
    (e : A ≃ₐ[R] A')
    (hmap : ∀ x : A, algebraMap A' B (e x) = algebraMap A B x) :
    IsIntegralClosure A' R B := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    apply congrArg e
    apply IsIntegralClosure.algebraMap_injective A R B
    rw [← hmap, ← hmap, hxy]
  · intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A)).mp hx
      exact ⟨e a, hmap a |>.trans ha⟩
    · rintro ⟨a', rfl⟩
      obtain ⟨a, rfl⟩ := e.surjective a'
      rw [hmap]
      exact (IsIntegralClosure.isIntegral_iff (A := A)).mpr ⟨a, rfl⟩

/-- The canonical map from the localization of an integral-closure model to the
localization of its generic ambient algebra. -/
@[instance_reducible]
noncomputable def localizedNormalizationAlgebra
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    (M : Submonoid R) :
    Algebra
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
  (IsLocalization.mapₐ M (Localization M)
    (Localization (Algebra.algebraMapSubmonoid N M))
    (Localization (Algebra.algebraMapSubmonoid D M))
    (IsScalarTower.toAlgHom R N D)).toRingHom.toAlgebra

/-- The canonical localized normalization map is linear over the localized base. -/
theorem localizedNormalization_isScalarTower
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    (M : Submonoid R) :
    let _ : Algebra
        (Localization (Algebra.algebraMapSubmonoid N M))
        (Localization (Algebra.algebraMapSubmonoid D M)) :=
      localizedNormalizationAlgebra R N D M
    IsScalarTower
      (Localization M)
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) := by
  letI : Algebra
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalizationAlgebra R N D M
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact ((IsLocalization.mapₐ M (Localization M)
    (Localization (Algebra.algebraMapSubmonoid N M))
    (Localization (Algebra.algebraMapSubmonoid D M))
    (IsScalarTower.toAlgHom R N D)).commutes x).symm

/-- On elements of the original normalization, the localized normalization map is the
localization of the original embedding into the generic algebra. -/
theorem localizedNormalizationAlgebra_algebraMap
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    (M : Submonoid R) (x : N) :
    let _ : Algebra
        (Localization (Algebra.algebraMapSubmonoid N M))
        (Localization (Algebra.algebraMapSubmonoid D M)) :=
      localizedNormalizationAlgebra R N D M
    algebraMap
        (Localization (Algebra.algebraMapSubmonoid N M))
        (Localization (Algebra.algebraMapSubmonoid D M))
        (algebraMap N (Localization (Algebra.algebraMapSubmonoid N M)) x) =
      algebraMap D (Localization (Algebra.algebraMapSubmonoid D M))
        (algebraMap N D x) := by
  dsimp only
  change
    IsLocalization.mapₐ M (Localization M)
        (Localization (Algebra.algebraMapSubmonoid N M))
        (Localization (Algebra.algebraMapSubmonoid D M))
        (IsScalarTower.toAlgHom R N D)
        (algebraMap N (Localization (Algebra.algebraMapSubmonoid N M)) x) = _
  rw [IsLocalization.mapₐ_coe, IsLocalization.map_eq]
  rfl

/-- Localization of an actual integral-closure model is again the integral closure in the
localized generic algebra.

The proof applies the arbitrary-localization integral-closure comparison to
`R → M⁻¹R`, then transports both tensor products across the canonical
tensor/localization equivalences. -/
theorem localizedNormalization_isIntegralClosure
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) :
    let Rm := Localization M
    let Nm := Localization (Algebra.algebraMapSubmonoid N M)
    let Dm := Localization (Algebra.algebraMapSubmonoid D M)
    let _ : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
    let _ : IsScalarTower Rm Nm Dm :=
      localizedNormalization_isScalarTower R N D M
    IsIntegralClosure Nm Rm Dm := by
  dsimp only
  let Rm := Localization M
  let Nm := Localization (Algebra.algebraMapSubmonoid N M)
  let Dm := Localization (Algebra.algebraMapSubmonoid D M)
  let TN : Type u := Rm ⊗[R] N
  let TD : Type u := Rm ⊗[R] D
  letI : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
  letI : IsScalarTower Rm Nm Dm :=
    localizedNormalization_isScalarTower R N D M
  letI : Algebra TN TD :=
    normalizationBaseChangeAlgebra (R := R) (R' := Rm) (N := N) (B := D)
  let hTN : IsIntegralClosure TN Rm TD :=
    localizationBaseChange_isIntegralClosure R N D M
  letI : IsIntegralClosure TN Rm TD := hTN
  let eD : TD ≃ₐ[Rm] Dm := Localization.tensorRightAlgEquiv M D
  letI : Algebra TN Dm :=
    normalizationAlgebraOfGenericEquiv Rm TN TD Dm eD
  letI : IsScalarTower Rm TN Dm :=
    normalizationAlgebraOfGenericEquiv_isScalarTower Rm TN TD Dm eD
  letI : IsIntegralClosure TN Rm Dm :=
    isIntegralClosure_of_genericEquiv Rm TN TD Dm eD
  let eN : TN ≃ₐ[Rm] Nm := Localization.tensorRightAlgEquiv M N
  apply isIntegralClosure_of_modelEquiv Rm TN Nm Dm eN
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      change algebraMap Nm Dm
          (Localization.tensorRightAlgEquiv M N (x ⊗ₜ[R] y)) =
        Localization.tensorRightAlgEquiv M D
          ((Algebra.TensorProduct.map (AlgHom.id Rm Rm)
            (IsScalarTower.toAlgHom R N D)) (x ⊗ₜ[R] y))
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change algebraMap Nm Dm
          (Localization.tensorRightAlgEquiv M N (x ⊗ₜ[R] y)) =
        Localization.tensorRightAlgEquiv M D (x ⊗ₜ[R] algebraMap N D y)
      rw [show x ⊗ₜ[R] y = (x ⊗ₜ[R] (1 : N)) *
        ((1 : Rm) ⊗ₜ[R] y) by simp]
      rw [show x ⊗ₜ[R] algebraMap N D y =
        (x ⊗ₜ[R] (1 : D)) * ((1 : Rm) ⊗ₜ[R] algebraMap N D y) by simp]
      have hxN : Localization.tensorRightAlgEquiv M N (x ⊗ₜ[R] (1 : N)) =
          algebraMap Rm Nm x :=
        Localization.tensorRightAlgEquiv_apply_tmul_one (R := R) M N x
      have hyN : Localization.tensorRightAlgEquiv M N ((1 : Rm) ⊗ₜ[R] y) =
          algebraMap N Nm y :=
        Localization.tensorRightAlgEquiv_apply_one_tmul (R := R) (S := N) M y
      have hxD : Localization.tensorRightAlgEquiv M D (x ⊗ₜ[R] (1 : D)) =
          algebraMap Rm Dm x :=
        Localization.tensorRightAlgEquiv_apply_tmul_one (R := R) M D x
      have hyD : Localization.tensorRightAlgEquiv M D
          ((1 : Rm) ⊗ₜ[R] algebraMap N D y) =
          algebraMap D Dm (algebraMap N D y) :=
        Localization.tensorRightAlgEquiv_apply_one_tmul
          (R := R) (S := D) M (algebraMap N D y)
      simp only [map_mul]
      rw [hxN, hyN, hxD, hyD]
      rw [IsScalarTower.algebraMap_apply Rm Nm Dm,
        localizedNormalizationAlgebra_algebraMap R N D M]

/-- The canonical comparison with the literal integral closure after localization. -/
noncomputable def localizedNormalizationEquivIntegralClosure
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) :
    let Rm := Localization M
    let Nm := Localization (Algebra.algebraMapSubmonoid N M)
    let Dm := Localization (Algebra.algebraMapSubmonoid D M)
    let _ : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
    let _ : IsScalarTower Rm Nm Dm :=
      localizedNormalization_isScalarTower R N D M
    Nm ≃ₐ[Rm] integralClosure Rm Dm := by
  dsimp only
  letI : Algebra
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalizationAlgebra R N D M
  letI : IsScalarTower
      (Localization M)
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalization_isScalarTower R N D M
  letI : IsIntegralClosure
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization M)
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalization_isIntegralClosure R N D M
  exact IsIntegralClosure.equiv (Localization M)
    (Localization (Algebra.algebraMapSubmonoid N M))
    (Localization (Algebra.algebraMapSubmonoid D M)) _

/-- The localized normalization comparison commutes with the two canonical embeddings in
the localized generic algebra. -/
theorem localizedNormalizationEquivIntegralClosure_algebraMap
    (R N D : Type u) [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R)
    (x : Localization (Algebra.algebraMapSubmonoid N M)) :
    let Rm := Localization M
    let Nm := Localization (Algebra.algebraMapSubmonoid N M)
    let Dm := Localization (Algebra.algebraMapSubmonoid D M)
    let _ : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
    let _ : IsScalarTower Rm Nm Dm :=
      localizedNormalization_isScalarTower R N D M
    algebraMap (integralClosure Rm Dm) Dm
        (localizedNormalizationEquivIntegralClosure R N D M x) =
      algebraMap Nm Dm x := by
  dsimp only
  letI : Algebra
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalizationAlgebra R N D M
  letI : IsScalarTower
      (Localization M)
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalization_isScalarTower R N D M
  letI : IsIntegralClosure
      (Localization (Algebra.algebraMapSubmonoid N M))
      (Localization M)
      (Localization (Algebra.algebraMapSubmonoid D M)) :=
    localizedNormalization_isIntegralClosure R N D M
  exact IsIntegralClosure.algebraMap_equiv (Localization M)
    (Localization (Algebra.algebraMapSubmonoid N M))
    (Localization (Algebra.algebraMapSubmonoid D M)) _ x

#print axioms localizationBaseChangeIntegralClosureEquiv
#print axioms localizationBaseChangeIntegralClosureEquiv_val
#print axioms localizationBaseChange_isIntegralClosure
#print axioms isIntegralClosure_of_modelEquiv
#print axioms localizedNormalization_isScalarTower
#print axioms localizedNormalizationAlgebra_algebraMap
#print axioms localizedNormalization_isIntegralClosure
#print axioms localizedNormalizationEquivIntegralClosure
#print axioms localizedNormalizationEquivIntegralClosure_algebraMap

end

end Pcf.Stacks
