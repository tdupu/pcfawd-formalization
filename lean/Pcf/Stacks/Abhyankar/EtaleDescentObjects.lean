/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Pcf.Stacks.Abhyankar.EtaleDescent

/-!
# Object effectivity for finitely presented algebras over filtered colimits

This module proves the object-effectivity part of Stacks Tag `05N9`: a finitely presented algebra
over a filtered colimit of rings is obtained by base change from a finitely presented algebra at
one finite stage.  The construction chooses a finite polynomial presentation, moves its finite
set of coefficients to a common stage, and uses `Algebra.Presentation.ModelOfHasCoeffs`.

The final section combines the map and equality clauses of Tag `05N9` for two diagrams over the
same filtered category.  It puts two descended maps, or two eventual equalities, over one common
stage.  This is the categorical bookkeeping needed for the two maps and two inverse identities of
a descended isomorphism.  Constructing the varying-base-change diagrams to which these lemmas are
applied is deliberately kept separate from the object-effectivity statement.
-/

@[expose] public section

open CategoryTheory Limits

universe vJ uJ u

namespace Pcf.Stacks.EtaleDescent

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]
variable (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
variable [PreservesColimit F (forget CommRingCat)]

include hc

/-- Every finite set of elements of a filtered colimit of commutative rings is contained in the
range of the structure map from one common stage. -/
theorem exists_stage_containing_finite_set (s : Set c.pt) (hs : s.Finite) :
    ∃ i : J, s ⊆ Set.range (c.ι.app i).hom := by
  classical
  let _ : Fintype s := hs.fintype
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  choose j x hx using fun a : s ↦ Types.jointly_surjective_of_isColimit hc' a.1
  obtain ⟨i, hi⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  have hj (a : s) : j a ∈ Finset.univ.image j :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  let f (a : s) : j a ⟶ i := (hi (hj a)).some
  refine ⟨i, fun a ha ↦ ?_⟩
  let a' : s := ⟨a, ha⟩
  refine ⟨F.map (f a') (x a'), ?_⟩
  change (c.ι.app i).hom (F.map (f a') (x a')) = (a' : c.pt)
  rw [← hx a']
  exact congr($(c.w (f a')).hom (x a'))

/-- **Stacks Tag 05N9, object-effectivity part.**

If `R = colim Rᵢ` and `S` is a finitely presented `R`-algebra, then `S` is the base change of a
finitely presented `Rᵢ`-algebra for some stage `i`.  The algebra structure on `c.pt` in the
conclusion is the canonical structure map `Rᵢ → colim Rᵢ`. -/
theorem exists_finitePresentation_model_of_isColimit
    (S : Type u) [CommRing S] [Algebra c.pt S] [Algebra.FinitePresentation c.pt S] :
    ∃ i : J,
      letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
      ∃ (Sᵢ : Type u) (_ : CommRing Sᵢ) (_ : Algebra (F.obj i) Sᵢ)
        (_ : Algebra.FinitePresentation (F.obj i) Sᵢ),
        Nonempty (TensorProduct (F.obj i) c.pt Sᵢ ≃ₐ[c.pt] S) := by
  let P := Algebra.Presentation.ofFinitePresentation c.pt S
  obtain ⟨i, hi⟩ := exists_stage_containing_finite_set F c hc P.coeffs P.finite_coeffs
  refine ⟨i, ?_⟩
  let _ : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let _ : Algebra (F.obj i) S :=
    ((algebraMap c.pt S).comp (c.ι.app i).hom).toAlgebra
  let _ : IsScalarTower (F.obj i) c.pt S := .of_algebraMap_eq' rfl
  let _ : P.HasCoeffs (F.obj i) := ⟨hi⟩
  exact ⟨P.ModelOfHasCoeffs (F.obj i), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj i)⟩⟩

section SimultaneousMaps

variable (R : CommRingCat.{u}) (G : J ⥤ CommRingCat.{u})
variable (α : (Functor.const J).obj R ⟶ F) (β : (Functor.const J).obj R ⟶ G)
variable (d : Cocone G) (hd : IsColimit d)
variable [PreservesColimit G (forget CommRingCat)]

include hd

/-- Two maps out of finitely presented algebras and into two filtered colimits can be descended
over one common index.  This is the simultaneous form of the map clause of Tag `05N9` used for
the forward and inverse maps of an isomorphism after the two base-change diagrams have been
constructed. -/
theorem exists_common_factorizations_of_finitePresentation
    {S T : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (hf : f.hom.FinitePresentation) (hg : g.hom.FinitePresentation)
    (a : S ⟶ c.pt) (b : T ⟶ d.pt)
    (ha : ∀ i, f ≫ a = α.app i ≫ c.ι.app i)
    (hb : ∀ i, g ≫ b = β.app i ≫ d.ι.app i) :
    ∃ (k : J) (aₖ : S ⟶ F.obj k) (bₖ : T ⟶ G.obj k),
      f ≫ aₖ = α.app k ∧ a = aₖ ≫ c.ι.app k ∧
      g ≫ bₖ = β.app k ∧ b = bₖ ≫ d.ι.app k := by
  obtain ⟨i, aᵢ, hfaᵢ, haᵢ⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R F α f c hc hf a ha
  obtain ⟨j, bⱼ, hgbⱼ, hbⱼ⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R G β g d hd hg b hb
  let k := IsFiltered.max i j
  let hik : i ⟶ k := IsFiltered.leftToMax i j
  let hjk : j ⟶ k := IsFiltered.rightToMax i j
  refine ⟨k, aᵢ ≫ F.map hik, bⱼ ≫ G.map hjk, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hfaᵢ]
    simpa using (α.naturality hik).symm
  · rw [haᵢ]
    simp only [Category.assoc, c.w]
  · rw [← Category.assoc, hgbⱼ]
    simpa using (β.naturality hjk).symm
  · rw [hbⱼ]
    simp only [Category.assoc, d.w]

/-- Two applications of the equality clause of Tag `05N9`, possibly in different filtered
diagrams and with different finitely presented sources, can be realized at one common index.
In the isomorphism application these are the two inverse identities. -/
theorem exists_common_stage_for_two_eventual_eq_of_finitePresentation
    {S T : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (hf : f.hom.FinitePresentation) (hg : g.hom.FinitePresentation)
    {i₁ i₂ j₁ j₂ : J}
    (a₁ : S ⟶ F.obj i₁) (ha₁ : f ≫ a₁ = α.app i₁)
    (a₂ : S ⟶ F.obj i₂) (ha₂ : f ≫ a₂ = α.app i₂)
    (b₁ : T ⟶ G.obj j₁) (hb₁ : g ≫ b₁ = β.app j₁)
    (b₂ : T ⟶ G.obj j₂) (hb₂ : g ≫ b₂ = β.app j₂)
    (ha : a₁ ≫ c.ι.app i₁ = a₂ ≫ c.ι.app i₂)
    (hb : b₁ ≫ d.ι.app j₁ = b₂ ≫ d.ι.app j₂) :
    ∃ (m : J) (hi₁m : i₁ ⟶ m) (hi₂m : i₂ ⟶ m)
      (hj₁m : j₁ ⟶ m) (hj₂m : j₂ ⟶ m),
      a₁ ≫ F.map hi₁m = a₂ ≫ F.map hi₂m ∧
      b₁ ≫ G.map hj₁m = b₂ ≫ G.map hj₂m := by
  obtain ⟨k, hi₁k, hi₂k, hak⟩ :=
    exists_eventual_eq_of_finitePresentation R F α f c hc hf a₁ ha₁ a₂ ha₂ ha
  obtain ⟨l, hj₁l, hj₂l, hbl⟩ :=
    exists_eventual_eq_of_finitePresentation R G β g d hd hg b₁ hb₁ b₂ hb₂ hb
  let m := IsFiltered.max k l
  let hkm : k ⟶ m := IsFiltered.leftToMax k l
  let hlm : l ⟶ m := IsFiltered.rightToMax k l
  refine ⟨m, hi₁k ≫ hkm, hi₂k ≫ hkm, hj₁l ≫ hlm, hj₂l ≫ hlm, ?_, ?_⟩
  · simpa only [F.map_comp, Category.assoc] using congrArg (fun q ↦ q ≫ F.map hkm) hak
  · simpa only [G.map_comp, Category.assoc] using congrArg (fun q ↦ q ≫ G.map hlm) hbl

end SimultaneousMaps

end Pcf.Stacks.EtaleDescent
