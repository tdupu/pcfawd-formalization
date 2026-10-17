/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Checking finiteness and flatness on an affine open cover of the target

For an affine morphism `π : Z → X` and a family of affine opens `V_i` covering `X`, `π` is finite
(resp. flat) as soon as each `Γ(X, V_i) → Γ(Z, π⁻¹V_i)` is.  These are the local-to-global steps
for "finite locally free" in Stacks Tag `0EYH` (with Morphisms, Lemma 29.49.2, Tag `02KB`).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace Pcf.Stacks.SchemeLevel

variable {X Z : Scheme.{u}}

/-- Restriction along an equality of opens is bijective. -/
theorem bijective_presheaf_map_eqToHom {S : Scheme.{u}} {U V : S.Opens} (h : U = V) :
    Function.Bijective (S.presheaf.map (eqToHom h).op).hom := by
  subst h
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism whose ring maps over a family of affine opens covering the target are finite, and
whose preimages of these opens are affine, is finite. -/
theorem isFinite_of_iSup_eq_top (π : Z ⟶ X) {ι : Type*} (V : ι → X.affineOpens)
    (hV : ⨆ i, (V i : X.Opens) = ⊤) (hpre : ∀ i, IsAffineOpen (π ⁻¹ᵁ (V i : X.Opens)))
    (h : ∀ i, (π.app (V i)).hom.Finite) : IsFinite π := by
  refine (HasAffineProperty.iff_of_iSup_eq_top (P := @IsFinite)
    V hV).mpr fun i ↦ ?_
  refine ⟨hpre i, ?_⟩
  have h' : (π.app ((V i : X.Opens).ι ''ᵁ ⊤)).hom.Finite := by
    rw [Scheme.Opens.ι_image_top]; exact h i
  rw [morphismRestrict_appTop]
  exact (RingHom.Finite.of_surjective _ (bijective_presheaf_map_eqToHom _).2).comp h'

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism whose ring maps over a family of affine opens covering the target are flat, and
whose preimages of these opens are affine, is flat. -/
theorem flat_of_iSup_eq_top (π : Z ⟶ X) {ι : Type*} (V : ι → X.affineOpens)
    (hV : ⨆ i, (V i : X.Opens) = ⊤) (hpre : ∀ i, IsAffineOpen (π ⁻¹ᵁ (V i : X.Opens)))
    (h : ∀ i, (π.app (V i)).hom.Flat) : Flat π := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat.{u})
    (fun i ↦ (V i : X.Opens)) hV).mpr fun i ↦ ?_
  have : IsAffine (π ⁻¹ᵁ (V i : X.Opens)) := hpre i
  have : IsAffine (V i : X.Opens) := (V i).2
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat.{u})]
  have h' : (π.app ((V i : X.Opens).ι ''ᵁ ⊤)).hom.Flat := by
    rw [Scheme.Opens.ι_image_top]; exact h i
  rw [morphismRestrict_appTop]
  exact RingHom.Flat.respectsIso.1 _ (RingEquiv.ofBijective _
    (bijective_presheaf_map_eqToHom (image_morphismRestrict_preimage π (V i : X.Opens) ⊤))) h'

#print axioms bijective_presheaf_map_eqToHom
#print axioms isFinite_of_iSup_eq_top
#print axioms flat_of_iSup_eq_top

end Pcf.Stacks.SchemeLevel
