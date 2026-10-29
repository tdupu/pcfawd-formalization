/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.Bounding.PaperPProjectiveDominant

/-!
# Uniqueness of the normalization lift (`paper-p.tex`, l. 303–311)

A finite surjective morphism `g : A → B` of integral schemes has at most one
lift `g̃ : Ã → B̃` with `ν_B ∘ g̃ = g ∘ ν_A`; the canonical lift
`schemeGlobalNormalizationMorphism g` is one. Unlike
`schemeGlobalNormalizationMorphism_unique`, no agreement on generic points is
assumed: it follows because `ν_B` is finite (so its generic fibre is the
generic point) and birational.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

attribute [local instance] specializationOrder in
/-- For a finite dominant map of integral schemes, only the generic point
maps to the generic point. -/
theorem eq_genericPoint_of_map_eq_genericPoint_of_isFinite
    {N A : Scheme.{u}} [IsIntegral N] [IsIntegral A] (ν : N ⟶ A) [IsFinite ν] [IsDominant ν]
    (x : N) (hx : ν x = genericPoint A) : x = genericPoint N := by
  by_contra hne
  have hlt : x < genericPoint N := lt_of_le_of_ne (genericPoint_specializes x) hne
  have := schemeHom_strictMono_of_locallyQuasiFinite ν hlt
  rw [hx, map_genericPoint_eq_of_isDominant ν] at this
  exact lt_irrefl _ this

/-- A dominant morphism from the spectrum of a field hits the generic point. -/
theorem specField_closedPoint_eq_genericPoint {K : Type u} [Field K] {N : Scheme.{u}}
    [IsIntegral N] (a : Spec (.of K) ⟶ N) [IsDominant a] :
    a (IsLocalRing.closedPoint K) = genericPoint N := by
  have h := map_genericPoint_eq_of_isDominant a
  have hc : genericPoint (Spec (.of K)) = IsLocalRing.closedPoint K := by
    apply PrimeSpectrum.ext
    have := (genericPoint (Spec (.of K))).isPrime
    exact (Ideal.eq_bot_of_prime _).trans (IsLocalRing.maximalIdeal_eq_bot (R := K)).symm
  rw [← hc]
  exact h

private theorem sigma_eq_of_residue {K : Type u} [Field K] {N A : Scheme.{u}} (ν : N ⟶ A)
    (x y : N) (φ : N.residueField x ⟶ CommRingCat.of K) (ψ : N.residueField y ⟶ CommRingCat.of K)
    (e : x = y) (e' : ν x = ν y)
    (h : ν.residueFieldMap x ≫ φ = (A.residueFieldCongr e').hom ≫ ν.residueFieldMap y ≫ ψ)
    (hsurj : Function.Surjective (ν.residueFieldMap x)) :
    (⟨x, φ⟩ : Σ z : N, N.residueField z ⟶ CommRingCat.of K) = ⟨y, ψ⟩ := by
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at h
  congr
  ext t
  obtain ⟨s, rfl⟩ := hsurj t
  exact congrArg (fun F => F.hom s) h

/-- The residue-field map at the generic point of a morphism that is an
isomorphism on generic stalks is surjective. -/
theorem residueFieldMap_genericPoint_surjective {N A : Scheme.{u}} [IsIntegral N]
    (ν : N ⟶ A) [IsIso (ν.stalkMap (genericPoint N))] :
    Function.Surjective (ν.residueFieldMap (genericPoint N)) := by
  intro t
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective (R := N.presheaf.stalk (genericPoint N)) t
  obtain ⟨r, rfl⟩ := ((ConcreteCategory.bijective_of_isIso
    (ν.stalkMap (genericPoint N))).2) s
  refine ⟨A.residue _ r, ?_⟩
  have h := Scheme.residue_residueFieldMap (f := ν) (genericPoint N)
  exact congrArg (fun F => F.hom r) h

/-- Two morphisms from the spectrum of a field into `N`, both hitting the
generic point, agree once composed with a morphism `ν` that is an isomorphism
on generic stalks. -/
theorem specField_hom_ext_of_genericPoint {K : Type u} [Field K] {N A : Scheme.{u}}
    [IsIntegral N] (ν : N ⟶ A) [IsIso (ν.stalkMap (genericPoint N))]
    (a b : Spec (.of K) ⟶ N)
    (ha : a (IsLocalRing.closedPoint K) = genericPoint N)
    (hb : b (IsLocalRing.closedPoint K) = genericPoint N)
    (hab : a ≫ ν = b ≫ ν) : a = b := by
  apply (Scheme.SpecToEquivOfField K N).injective
  have himg := congrArg (Scheme.SpecToEquivOfField K A) hab
  rw [Scheme.SpecToEquivOfField_eq_iff] at himg
  obtain ⟨e', hres⟩ := himg
  change (⟨a (IsLocalRing.closedPoint K), N.descResidueField (Scheme.stalkClosedPointTo a)⟩ :
      Σ x : N, N.residueField x ⟶ CommRingCat.of K) =
    ⟨b (IsLocalRing.closedPoint K), N.descResidueField (Scheme.stalkClosedPointTo b)⟩
  change ν (a _) = ν (b _) at e'
  have hsurj : Function.Surjective (ν.residueFieldMap (a (IsLocalRing.closedPoint K))) := by
    rw [ha]; exact residueFieldMap_genericPoint_surjective ν
  refine sigma_eq_of_residue ν _ _ _ _ (ha.trans hb.symm) e' ?_ hsurj
  have e1 := Scheme.descResidueField_stalkClosedPointTo_comp (f := ν) a
  have e2 := Scheme.descResidueField_stalkClosedPointTo_comp (f := ν) b
  rw [← e1, ← e2]
  exact hres

/-- **`paper-p.tex`, l. 303–311.** Any two lifts `l₁ l₂ : Ã → B̃` of a finite
dominant `π : A → B` of integral schemes with `ν_B ∘ lᵢ = π ∘ ν_A` coincide.
The target normalization map is assumed finite, as it is for varieties. -/
theorem normalization_lift_unique {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsFinite (Palomar.normalizationMap X)]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (l₁ l₂ : Palomar.normalization Y ⟶ Palomar.normalization X)
    (h₁ : l₁ ≫ Palomar.normalizationMap X = Palomar.normalizationMap Y ≫ π)
    (h₂ : l₂ ≫ Palomar.normalizationMap X = Palomar.normalizationMap Y ≫ π) :
    l₁ = l₂ := by
  let νX := Palomar.normalizationMap X
  let G := Palomar.genericToNormalization Y
  apply ext_of_isDominant_of_isSeparated νX (h₁.trans h₂.symm) G
  let K := Y.functionField
  let G' : Spec (.of K) ⟶ Palomar.normalization Y := G
  have hGcp : G' (IsLocalRing.closedPoint K) = genericPoint (Palomar.normalization Y) := by
    have : IsDominant G' := inferInstanceAs (IsDominant G)
    exact specField_closedPoint_eq_genericPoint G'
  have hpt (l : Palomar.normalization Y ⟶ Palomar.normalization X)
      (h : l ≫ νX = Palomar.normalizationMap Y ≫ π) :
      (G' ≫ l) (IsLocalRing.closedPoint K) = genericPoint (Palomar.normalization X) := by
    apply eq_genericPoint_of_map_eq_genericPoint_of_isFinite νX
    have : νX ((G' ≫ l) (IsLocalRing.closedPoint K)) =
        π (Palomar.normalizationMap Y (G' (IsLocalRing.closedPoint K))) := by
      change (l ≫ νX) (G' _) = _
      rw [h]; rfl
    rw [this, hGcp, map_genericPoint_eq_of_isDominant, map_genericPoint_eq_of_isDominant]
  exact specField_hom_ext_of_genericPoint (K := K) νX (G' ≫ l₁) (G' ≫ l₂)
    (hpt l₁ h₁) (hpt l₂ h₂) (by rw [Category.assoc, Category.assoc, h₁, h₂])

/-- The canonical lift is the unique lift. -/
theorem eq_schemeGlobalNormalizationMorphism_of_comp {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsFinite (Palomar.normalizationMap X)]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (l : Palomar.normalization Y ⟶ Palomar.normalization X)
    (h : l ≫ Palomar.normalizationMap X = Palomar.normalizationMap Y ≫ π) :
    l = schemeGlobalNormalizationMorphism π :=
  normalization_lift_unique π _ _ h (schemeGlobalNormalizationMorphism_comp π)

#print axioms normalization_lift_unique
#print axioms eq_schemeGlobalNormalizationMorphism_of_comp

end

end Pcf
