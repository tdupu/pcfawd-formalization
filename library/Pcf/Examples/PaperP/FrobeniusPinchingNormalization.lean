/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingGenerators
public import Pcf.Examples.PaperP.BirationalAffineNormalization
public import Pcf.Examples.PaperP.CoordinateSquareEtale

/-!
# Normalization and canonical lift in `ex:frobenius-pinching`

`paper-p.tex`, Example `ex:frobenius-pinching`: the absolute normalization of
`X = Spec R`, `R = k[x^p] + y k[x,y]`, is `A² = Spec k[x,y]`, and the canonical lift of the
descended map `f` to normalizations is `H(x,y) = (x², y²)` transported through this
identification. When `2 ≠ 0` in `k`, `H` is étale at every point off the axes `xy = 0`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingNormalization

open AlgebraicGeometry CategoryTheory
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators
open Pcf.Examples.PaperP.BirationalAffineNormalization (normalizationIsoCover genericToCover)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]

theorem p_pos : 0 < p := (Fact.out : p.Prime).pos

instance planeFinite : Module.Finite (ring k p) (Plane k) := moduleFinite_plane k p (p_pos p)

instance planeFaithful : FaithfulSMul (ring k p) (Plane k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective

/-- `isFractionRing_plane`, restated for the localization algebra structure
`R → k[x,y] → Frac k[x,y]` that the generic normalization lemmas use. -/
instance planeFraction :
    @IsFractionRing (ring k p) _ (FractionRing (Plane k)) _ OreLocalization.instAlgebra := by
  convert isFractionRing_plane k p (p_pos p) using 1
  exact Algebra.algebra_ext _ _ fun _ => rfl

instance ringNoetherian : IsNoetherianRing (ring k p) := by
  haveI := ring_finiteType k p
  exact Algebra.FiniteType.isNoetherianRing k (ring k p)

/-- The pinched scheme `X`. -/
noncomputable abbrev Xs := Spec (.of (ring k p))

/-- The identification of the absolute normalization of `X` with `A²`.

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
noncomputable def normIso : Pcf.Palomar.normalization (Xs k p) ≅ Spec (.of (Plane k)) :=
  normalizationIsoCover (ring k p) (Plane k)

/-- The normalization map `A² → X`. -/
noncomputable abbrev nu : Spec (.of (Plane k)) ⟶ Xs k p :=
  BirationalAffineNormalization.schemeMap (ring k p) (Plane k)

theorem normIso_hom_nu :
    (normIso k p).hom ≫ nu k p = Pcf.Palomar.normalizationMap (Xs k p) :=
  BirationalAffineNormalization.normalizationIsoCover_hom_comp _ _

/-- `H(x,y) = (x², y²)` on `A²`. -/
noncomputable def Hs : Spec (.of (Plane k)) ⟶ Spec (.of (Plane k)) :=
  Spec.map (CommRingCat.ofHom (square k).toRingHom)

theorem Hs_nu : Hs k ≫ nu k p = nu k p ≫ descendedSchemeMap k p := by
  unfold Hs nu BirationalAffineNormalization.schemeMap descendedSchemeMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

instance fFinite : IsFinite (descendedSchemeMap k p) := descendedSchemeMap_finite k p

instance fSurjective : Surjective (descendedSchemeMap k p) := descendedSchemeMap_surjective k p

instance fDominant : IsDominant (descendedSchemeMap k p) := inferInstance

/-- The candidate lift `normIso⁻¹ ∘ H ∘ normIso`. -/
noncomputable def lift : Pcf.Palomar.normalization (Xs k p) ⟶
    Pcf.Palomar.normalization (Xs k p) :=
  (normIso k p).hom ≫ Hs k ≫ (normIso k p).inv

theorem lift_comp_normalizationMap :
    lift k p ≫ Pcf.Palomar.normalizationMap (Xs k p) =
      Pcf.Palomar.normalizationMap (Xs k p) ≫ descendedSchemeMap k p := by
  rw [← normIso_hom_nu, lift]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Hs_nu]


/-- Maps from the spectrum of a field into `A²` are determined by their composite to `X`
when that composite is injective on rings (birationality of `ν`). -/
theorem spec_ext {L : CommRingCat} (hL : IsField L) (u v : Spec L ⟶ Spec (.of (Plane k)))
    (c : ring k p →+* L) (hc : Function.Injective c)
    (hu : u ≫ nu k p = Spec.map (CommRingCat.ofHom c))
    (hv : v ≫ nu k p = Spec.map (CommRingCat.ofHom c)) : u = v := by
  letI : Field L := hL.toField
  obtain ⟨a, rfl⟩ := Spec.map_surjective (R := .of (Plane k)) (S := L) u
  obtain ⟨b, rfl⟩ := Spec.map_surjective (R := .of (Plane k)) (S := L) v
  unfold nu BirationalAffineNormalization.schemeMap at hu hv
  rw [← Spec.map_comp] at hu hv
  have ha := congrArg CommRingCat.Hom.hom (Spec.map_injective hu)
  have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective hv)
  congr 1
  apply CommRingCat.hom_ext
  apply BirationalAffineNormalization.ringHom_ext_of_birational (ring k p) (Plane k)
  · exact ha.trans hb.symm
  · change Function.Injective ((CommRingCat.ofHom (algebraMap (ring k p) (Plane k)) ≫ a).hom)
    rw [Spec.map_injective hu]
    exact hc

/-- The generic inclusion of `X` composed with `f`, as a ring map. -/
noncomputable def genericRing : ring k p →+* (Xs k p).functionField :=
  ((Scheme.ΓSpecIso (.of (ring k p))).inv ≫
    (Xs k p).presheaf.germ ⊤ (genericPoint (Xs k p)) trivial).hom.comp
      (descendedSquare k p).toRingHom

theorem genericRing_injective : Function.Injective (genericRing k p) := by
  intro a b h
  apply descendedSquare_injective k p
  have hg := germ_injective_of_isIntegral (Xs k p) (U := ⊤) (genericPoint (Xs k p)) trivial
  have h' := hg h
  exact (Scheme.ΓSpecIso (.of (ring k p))).commRingCatIsoToRingEquiv.symm.injective h'

theorem genericIncl_f :
    Pcf.schemeGenericInclusion (Xs k p) ≫ descendedSchemeMap k p =
      Spec.map (CommRingCat.ofHom (genericRing k p)) := by
  unfold Pcf.schemeGenericInclusion descendedSchemeMap genericRing
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

/-- The generic condition characterizing the canonical lift. -/
theorem lift_generic :
    Pcf.Palomar.genericToNormalization (Xs k p) ≫ lift k p =
      Pcf.schemeGenericMorphism (descendedSchemeMap k p) ≫
        Pcf.Palomar.genericToNormalization (Xs k p) := by
  apply (cancel_mono (normIso k p).hom).mp
  have hG : Pcf.Palomar.genericToNormalization (Xs k p) ≫ (normIso k p).hom =
      genericToCover (ring k p) (Plane k) :=
    BirationalAffineNormalization.genericToNormalization_normalizationToCover _ _
  simp only [lift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hG]
  have hgc := BirationalAffineNormalization.genericToCover_comp (ring k p) (Plane k)
  apply spec_ext k p (Field.toIsField _) _ _ (genericRing k p) (genericRing_injective k p)
  · rw [Category.assoc, Hs_nu, ← Category.assoc, hgc, genericIncl_f]
  · rw [Category.assoc, hgc, Pcf.schemeGenericMorphism_comp, genericIncl_f]

/-- **The canonical lift of `f` to the normalization is `H(x,y) = (x², y²)`.**

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem lift_eq_canonical :
    lift k p = Pcf.schemeGlobalNormalizationMorphism (descendedSchemeMap k p) :=
  Pcf.schemeGlobalNormalizationMorphism_unique _ _ (lift_comp_normalizationMap k p)
    (lift_generic k p)

#print axioms lift_eq_canonical

end Pcf.Examples.PaperP.FrobeniusPinchingNormalization
