/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryDeltaTransfer

/-!
# Ramification indices along isomorphic squares

The ramification index of a prime is unchanged when both the base and the top
ring of the extension are replaced by isomorphic rings compatibly with the
structure maps.
-/

@[expose] public section

namespace Pcf

universe u v w x

set_option linter.style.haveILetI false

/-- Replacing the base ring by an isomorphic one with the composite structure
map does not change the ramification index. -/
theorem ramificationIdx_eq_of_base_ringEquiv_aux {A₁ : Type u} {A₂ : Type v} {B : Type w}
    [CommRing A₁] [CommRing A₂] [CommRing B]
    (f₂ : A₂ →+* B) (eA : A₁ ≃+* A₂) (q : Ideal B) [q.IsPrime] :
    (@Ideal.ramificationIdx B _ q A₁ _ (f₂.comp (eA : A₁ →+* A₂)).toAlgebra) =
      (@Ideal.ramificationIdx B _ q A₂ _ f₂.toAlgebra) := by
  letI alg₁ : Algebra A₁ B := (f₂.comp (eA : A₁ →+* A₂)).toAlgebra
  letI alg₂ : Algebra A₂ B := f₂.toAlgebra
  rw [@Ideal.ramificationIdx_def B _ q A₁ _ alg₁, @Ideal.ramificationIdx_def B _ q A₂ _ alg₂]
  have h1 : algebraMap A₁ (Localization.AtPrime q) =
      (algebraMap A₂ (Localization.AtPrime q)).comp (eA : A₁ →+* A₂) := by
    rw [IsScalarTower.algebraMap_eq A₁ B, IsScalarTower.algebraMap_eq A₂ B]
    rfl
  have h2 : Ideal.under A₁ q = (Ideal.under A₂ q).comap (eA : A₁ →+* A₂) := by
    change q.comap (f₂.comp (eA : A₁ →+* A₂)) = (q.comap f₂).comap _
    rw [Ideal.comap_comap]
  have key : Ideal.map (algebraMap A₁ (Localization.AtPrime q)) (Ideal.under A₁ q) =
      Ideal.map (algebraMap A₂ (Localization.AtPrime q)) (Ideal.under A₂ q) := by
    rw [h1, h2, ← Ideal.map_map, Ideal.map_comap_of_surjective (eA : A₁ →+* A₂) eA.surjective]
  rw [key]

/-- Ramification indices of maximal ideals agree for an isomorphic commuting
square of local ring extensions. -/
theorem ramificationIdx_maximalIdeal_eq_of_square {A₁ : Type u} {B₁ : Type v}
    {A₂ : Type w} {B₂ : Type x} [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂]
    [IsLocalRing B₁] [IsLocalRing B₂]
    (f₁ : A₁ →+* B₁) (f₂ : A₂ →+* B₂) (eA : A₁ ≃+* A₂) (eB : B₁ ≃+* B₂)
    (h : ∀ a, eB (f₁ a) = f₂ (eA a)) :
    @Ideal.ramificationIdx B₁ _ (IsLocalRing.maximalIdeal B₁) A₁ _ f₁.toAlgebra =
      @Ideal.ramificationIdx B₂ _ (IsLocalRing.maximalIdeal B₂) A₂ _ f₂.toAlgebra := by
  rw [← ramificationIdx_eq_of_base_ringEquiv_aux f₂ eA]
  letI : Algebra A₁ B₁ := f₁.toAlgebra
  letI : Algebra A₁ B₂ := (f₂.comp (eA : A₁ →+* A₂)).toAlgebra
  let e : B₁ ≃ₐ[A₁] B₂ := { eB with commutes' := fun a => h a }
  have hmax : (IsLocalRing.maximalIdeal B₁).map e = IsLocalRing.maximalIdeal B₂ := by
    haveI : ((IsLocalRing.maximalIdeal B₁).map e).IsMaximal :=
      Ideal.map_isMaximal_of_equiv e
    exact IsLocalRing.eq_maximalIdeal this
  rw [← hmax]
  exact (ramificationIdx_map_algEquiv e (IsLocalRing.maximalIdeal B₁)).symm

end Pcf
