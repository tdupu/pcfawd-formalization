/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GenericStalkMonodromyTransport

/-!
# Monodromy across a square with stalk-isomorphic sides

Prime-to-`p` monodromy of a finite dominant morphism transfers across a
commutative square whose vertical maps are isomorphisms on the relevant
generic stalks, for instance open immersions. In `latex/paper-p.tex`, proof
of Theorem `thm:allcodim-normal`, this moves the monodromy hypothesis from the
ambient self-map to its affine chart `Spec S ⟶ Spec R`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- Pointwise comparison data for a commuting square with bijective vertical
stalk maps. -/
theorem exists_stalkEquivs_of_square {X' Y X₀ Y₀ : Scheme.{u}}
    (F : X' ⟶ Y) (α : X' ⟶ X₀) (β : Y ⟶ Y₀) (g : X₀ ⟶ Y₀)
    (h : F ≫ β = α ≫ g) (x' : X') {z₀ : X₀} (hz : α x' = z₀)
    (hα : Function.Bijective (α.stalkMap x').hom)
    (hβ : Function.Bijective (β.stalkMap (F x')).hom) :
    ∃ (eE : X₀.presheaf.stalk z₀ ≃+* X'.presheaf.stalk x')
      (eK : Y₀.presheaf.stalk (g z₀) ≃+* Y.presheaf.stalk (F x')),
      (F.stalkMap x').hom.comp eK.toRingHom = eE.toRingHom.comp (g.stalkMap z₀).hom := by
  subst hz
  have hpt : (α ≫ g) x' = (F ≫ β) x' := by rw [h]
  let c := Y₀.presheaf.stalkCongr (Inseparable.of_eq hpt)
  refine ⟨RingEquiv.ofBijective _ hα,
    c.commRingCatIsoToRingEquiv.trans (RingEquiv.ofBijective _ hβ), ?_⟩
  have hsq := Scheme.Hom.stalkMap_congr_hom (α ≫ g) (F ≫ β) h.symm x'
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hsq
  apply RingHom.ext
  intro r
  have := congrArg (fun φ => φ.hom r) hsq
  exact this.symm

/-- **Monodromy across a square.** -/
theorem isPrimeToPMonodromyMap_of_square (p : ℕ) {X' Y X₀ Y₀ : Scheme.{u}}
    [IsIntegral X'] [IsIntegral Y] [IsIntegral X₀] [IsIntegral Y₀]
    (F : X' ⟶ Y) (α : X' ⟶ X₀) (β : Y ⟶ Y₀) (g : X₀ ⟶ Y₀)
    [IsFinite F] [IsDominant F] [IsFinite g] [IsDominant g] [IsDominant α]
    (h : F ≫ β = α ≫ g)
    (hα : Function.Bijective (α.stalkMap (genericPoint X')).hom)
    (hβ : Function.Bijective (β.stalkMap (F (genericPoint X'))).hom)
    (hmono : IsPrimeToPMonodromyMap p g) : IsPrimeToPMonodromyMap p F := by
  obtain ⟨eE, eK, hcomm⟩ := exists_stalkEquivs_of_square F α β g h (genericPoint X')
    (map_genericPoint_eq_of_isDominant α) hα hβ
  exact isPrimeToPMonodromyMap_of_genericStalkEquivs p g F eK eE hcomm hmono

/-- The open-immersion case. -/
theorem isPrimeToPMonodromyMap_of_openImmersion_square (p : ℕ) {X' Y X₀ Y₀ : Scheme.{u}}
    [IsIntegral X'] [IsIntegral Y] [IsIntegral X₀] [IsIntegral Y₀]
    (F : X' ⟶ Y) (α : X' ⟶ X₀) (β : Y ⟶ Y₀) (g : X₀ ⟶ Y₀)
    [IsFinite F] [IsDominant F] [IsFinite g] [IsDominant g]
    [IsOpenImmersion α] [IsOpenImmersion β]
    (h : F ≫ β = α ≫ g) (hmono : IsPrimeToPMonodromyMap p g) :
    IsPrimeToPMonodromyMap p F := by
  haveI : IsDominant α := by
    constructor
    have hne : (Set.range α).Nonempty := ⟨α (genericPoint X'), genericPoint X', rfl⟩
    exact (α.isOpenEmbedding.isOpenMap.isOpen_range).dense hne
  exact isPrimeToPMonodromyMap_of_square p F α β g h
    (ConcreteCategory.bijective_of_isIso _) (ConcreteCategory.bijective_of_isIso _) hmono

#print axioms exists_stalkEquivs_of_square
#print axioms isPrimeToPMonodromyMap_of_square
#print axioms isPrimeToPMonodromyMap_of_openImmersion_square

end Pcf
