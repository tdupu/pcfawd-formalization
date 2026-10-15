/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Finite-presentation descent along filtered colimits

This file records the two proved filtered-colimit mechanisms needed when descending an
Abhyankar standard presentation from a strict henselization:

* a homomorphism out of a finitely presented algebra factors through a finite stage;
* equality of two homomorphisms out of an essentially finite type algebra holds at a later stage.

These are the homomorphism and relation parts underlying Stacks Tag `05N9`, parts (2) and (3).
They are wrappers around Mathlib's finitely-presentable-object theorem, with all structure maps
kept explicit for later use by the Abhyankar assembly.

This module does **not** carry `@[stacks 05N9]`: Tag `05N9` also asserts effectivity of objects
(every finitely presented algebra over the colimit descends to a finite stage), which is not yet
proved in the pinned library.
-/

@[expose] public section

open CategoryTheory Limits

universe vJ uJ u

namespace Pcf.Stacks.EtaleDescent

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u})
variable (α : (Functor.const J).obj R ⟶ F)
variable {S : CommRingCat.{u}} (f : R ⟶ S)
variable (c : Cocone F) (hc : IsColimit c)
variable [PreservesColimit F (forget CommRingCat)]

include hc

/-- A map from a finitely presented `R`-algebra into a filtered colimit factors through one
stage, compatibly with the `R`-algebra structures.

This is the map-existence mechanism used in Tag `05N9`(2). -/
theorem exists_factorization_of_finitePresentation
    (hf : f.hom.FinitePresentation) (g : S ⟶ c.pt)
    (hg : ∀ i, f ≫ g = α.app i ≫ c.ι.app i) :
    ∃ (i : J) (g' : S ⟶ F.obj i),
      f ≫ g' = α.app i ∧ g = g' ≫ c.ι.app i := by
  exact RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    R F α f c hc hf g hg

/-- If two maps out of an essentially finite type `R`-algebra agree in a filtered colimit,
then they agree after passing to a common later stage.

For finitely presented source algebras this is the equality mechanism used in Tag `05N9`(3),
and it is what eventually verifies the two inverse identities of a descended isomorphism. -/
theorem exists_eventual_eq_of_essFiniteType
    (hf : f.hom.EssFiniteType)
    {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i)
    {j : J} (b : S ⟶ F.obj j) (hb : f ≫ b = α.app j)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    ∃ (k : J) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ F.map hik = b ≫ F.map hjk := by
  exact RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
    R F α f c hc hf a ha b hb hab

/-- The equality part of filtered-colimit descent specialized to a finitely presented source. -/
theorem exists_eventual_eq_of_finitePresentation
    (hf : f.hom.FinitePresentation)
    {i : J} (a : S ⟶ F.obj i) (ha : f ≫ a = α.app i)
    {j : J} (b : S ⟶ F.obj j) (hb : f ≫ b = α.app j)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    ∃ (k : J) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ F.map hik = b ≫ F.map hjk := by
  exact exists_eventual_eq_of_essFiniteType R F α f c hc
    (RingHom.FiniteType.of_finitePresentation hf).essFiniteType a ha b hb hab

end Pcf.Stacks.EtaleDescent
