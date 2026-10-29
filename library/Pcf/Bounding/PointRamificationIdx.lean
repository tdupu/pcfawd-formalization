/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDynamics
public import Pcf.Bounding.SchemePrimaryDeltaTransfer

/-!
# Ramification indices of stalk maps at arbitrary points

`pointRamificationIdx f x` is the ramification index of the maximal ideal of
the stalk at `x` over the stalk at `f x`. Unlike `schemeDivisorRamificationIdx`
it is stated for every point, with no normality assumption on the schemes.
It is multiplicative along a composite as soon as the middle stalk is a
discrete valuation ring and the stalk map into the source is injective, it is
one for stalk isomorphisms, and it is invariant under compatible ring
equivalences. These are the bookkeeping facts behind the valuation equality
`μ = e · v` in `latex/paper-p.tex`, proof of Theorem `thm:allcodim-normal`,
where the exceptional divisors and the periodic subvariety need not be normal.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The ramification index of the stalk map of `f` at `x`. -/
def pointRamificationIdx {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.stalkMap x).hom.toAlgebra
  (maximalIdeal (X.presheaf.stalk x)).ramificationIdx (Y.presheaf.stalk (f x))

/-- Multiplicativity of stalk ramification indices along a composite. -/
theorem pointRamificationIdx_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDomain (Y.presheaf.stalk (f x))]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    (hinj : Function.Injective (f.stalkMap x).hom) :
    pointRamificationIdx (f ≫ g) x = pointRamificationIdx g (f x) * pointRamificationIdx f x := by
  let R := Z.presheaf.stalk (g (f x))
  let S := Y.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  letI : Algebra R S := (g.stalkMap (f x)).hom.toAlgebra
  letI : Algebra S T := (f.stalkMap x).hom.toAlgebra
  letI : Algebra R T := ((f ≫ g).stalkMap x).hom.toAlgebra
  letI : IsLocalHom (algebraMap S T) := show IsLocalHom (f.stalkMap x).hom from inferInstance
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom
    rw [Scheme.Hom.stalkMap_comp]
    rfl)
  letI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr hinj
  letI : Module.Flat S T := inferInstance
  exact Ideal.ramificationIdx_tower (R := R) (maximalIdeal S) (maximalIdeal T)

/-- A stalk isomorphism has ramification index one. -/
theorem pointRamificationIdx_eq_one_of_bijective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hbij : Function.Bijective (f.stalkMap x).hom) : pointRamificationIdx f x = 1 := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  letI : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap R S) := hbij.2
  letI : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) hsurj
  letI : Algebra.FiniteType R S := Algebra.FiniteType.of_surjective (Algebra.ofId R S) hsurj
  letI : Algebra.IsUnramifiedAt R (maximalIdeal S) := inferInstance
  exact Ideal.ramificationIdx_eq_one (maximalIdeal S) R

/-- The ramification index does not change under an isomorphism of the base
ring compatible with the structure maps. -/
theorem ramificationIdx_eq_of_base_ringEquiv {R₁ R₂ S : Type*} [CommRing R₁] [CommRing R₂]
    [CommRing S] [Algebra R₁ S] [Algebra R₂ S] (e : R₁ ≃+* R₂)
    (he : (algebraMap R₂ S).comp e.toRingHom = algebraMap R₁ S)
    (q : Ideal S) [q.IsPrime] :
    q.ramificationIdx R₁ = q.ramificationIdx R₂ := by
  have hmap : (q.under R₁).map (algebraMap R₁ (Localization.AtPrime q)) =
      (q.under R₂).map (algebraMap R₂ (Localization.AtPrime q)) := by
    have h1 : q.under R₁ = (q.under R₂).comap e.toRingHom := by
      ext r
      simp only [Ideal.mem_comap, Ideal.under_def]
      rw [← he]
      rfl
    have h2 : algebraMap R₁ (Localization.AtPrime q) =
        (algebraMap R₂ (Localization.AtPrime q)).comp e.toRingHom := by
      rw [IsScalarTower.algebraMap_eq R₁ S, IsScalarTower.algebraMap_eq R₂ S, ← he]
      rfl
    rw [h1, h2, ← Ideal.map_map]
    congr 1
    exact Ideal.map_comap_of_surjective e.toRingHom e.surjective _
  rw [Ideal.ramificationIdx_eq (q.under R₁) q, Ideal.ramificationIdx_eq (q.under R₂) q, hmap]

/-- Ramification indices of maximal ideals agree for local maps identified by
ring equivalences on both sides. -/
theorem ramificationIdx_maximalIdeal_eq_of_ringEquiv {A₁ A₂ B₁ B₂ : Type*}
    [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [IsLocalRing A₂] [IsLocalRing B₂]
    (φ : A₁ →+* A₂) (ψ : B₁ →+* B₂) (e₁ : A₁ ≃+* B₁) (e₂ : A₂ ≃+* B₂)
    (hcomm : ψ.comp e₁.toRingHom = e₂.toRingHom.comp φ) :
    (letI := φ.toAlgebra; (maximalIdeal A₂).ramificationIdx A₁) =
      (letI := ψ.toAlgebra; (maximalIdeal B₂).ramificationIdx B₁) := by
  letI : Algebra A₁ A₂ := φ.toAlgebra
  letI : Algebra B₁ B₂ := ψ.toAlgebra
  letI : Algebra A₁ B₂ := (e₂.toRingHom.comp φ).toAlgebra
  let E : A₂ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun r => rfl }
  have hmax : (maximalIdeal A₂).map E = maximalIdeal B₂ :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv E.toRingEquiv)
  have h1 := ramificationIdx_map_algEquiv E (maximalIdeal A₂)
  rw [hmax] at h1
  rw [← h1]
  exact ramificationIdx_eq_of_base_ringEquiv e₁ hcomm (maximalIdeal B₂)

#print axioms ramificationIdx_eq_of_base_ringEquiv
#print axioms ramificationIdx_maximalIdeal_eq_of_ringEquiv
#print axioms pointRamificationIdx_comp
#print axioms pointRamificationIdx_eq_one_of_bijective

end
end Pcf
