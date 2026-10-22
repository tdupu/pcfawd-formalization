/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyFiniteCoverInductionCharZero

/-!
# Intrinsic PCF and the ambient-base all-codimension input

The normalized non-étale PCF predicate only uses a structure map to a field
to establish finite normalization. Its assertion is independent of that
choice. This makes the all-codimension input in the finite-cover induction
equivalent to the source's assertion with the inherited ambient structure
map on each original reduced point closure.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Normalized non-étale PCF is intrinsic to a finite dominant self-map;
the finite-type morphism to the field is used only for normalization
finiteness. -/
theorem isSeparableNormalizedPCF_base_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [NoetherianSpace X]
    (s t : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [LocallyOfFiniteType t]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsSeparableNormalizedPCF k s f ↔ IsSeparableNormalizedPCF k t f := by
  rfl

/-- Source-form positive-characteristic all-codimension input, where the
normalized return is measured using the base map inherited from the ambient
normal system. -/
def AllCodimNormalizedReturnPCFAtAmbientBase
    (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g],
    IsSeparableNormalizedPCF k t g → IsPrimeToPMonodromyMap p g →
    ∀ (y : Y) (n : ℕ) (_ : 0 < n)
      (hy : schemePointIterate g n y = y),
      let A := (pointClosureIdealSheaf y).subscheme
      let a := (pointClosureIdealSheaf y).subschemeι ≫ t
      let ν := Palomar.normalizationMap A
      letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
      IsSeparableNormalizedPCF k (ν ≫ a)
        (schemeGlobalNormalizationLift
          (pointClosureReturnMap (End.of g ^ n).asHom y hy))

/-- The inherited-base all-codimension theorem gives exactly the input
needed in the finite-cover induction. -/
theorem allCodimNormalizedReturnPCF_of_ambientBase
    (p : ℕ) (k : Type u) [Field k] [CharP k p]
    (h : AllCodimNormalizedReturnPCFAtAmbientBase p k) :
    AllCodimNormalizedReturnPCF p k := by
  intro Y _ _ _ _ t _ g _ _ hpcf hmono y n hn hy a _
  let A := (pointClosureIdealSheaf y).subscheme
  let b := (pointClosureIdealSheaf y).subschemeι ≫ t
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k b
  have hb := h t g hpcf hmono y n hn hy
  exact (isSeparableNormalizedPCF_base_iff k
    (Palomar.normalizationMap (pointClosureIdealSheaf y).subscheme ≫ b)
    (Palomar.normalizationMap (pointClosureIdealSheaf y).subscheme ≫ a)
    (schemeGlobalNormalizationLift
      (pointClosureReturnMap (End.of g ^ n).asHom y hy))).1 hb

/-- Source-form characteristic-zero input with the inherited ambient base
map on every periodic original reduced point closure. -/
def AllCodimNormalizedReturnPCFCharZeroAtAmbientBase
    (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g],
    IsSeparableNormalizedPCF k t g →
    ∀ (y : Y) (n : ℕ) (_ : 0 < n)
      (hy : schemePointIterate g n y = y),
      let A := (pointClosureIdealSheaf y).subscheme
      let a := (pointClosureIdealSheaf y).subschemeι ≫ t
      let ν := Palomar.normalizationMap A
      letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
      IsSeparableNormalizedPCF k (ν ≫ a)
        (schemeGlobalNormalizationLift
          (pointClosureReturnMap (End.of g ^ n).asHom y hy))

theorem allCodimNormalizedReturnPCFCharZero_of_ambientBase
    (k : Type u) [Field k] [CharZero k]
    (h : AllCodimNormalizedReturnPCFCharZeroAtAmbientBase k) :
    AllCodimNormalizedReturnPCFCharZero k := by
  intro Y _ _ _ _ t _ g _ _ hpcf y n hn hy a _
  let A := (pointClosureIdealSheaf y).subscheme
  let b := (pointClosureIdealSheaf y).subschemeι ≫ t
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k b
  have hb := h t g hpcf y n hn hy
  exact (isSeparableNormalizedPCF_base_iff k
    (Palomar.normalizationMap (pointClosureIdealSheaf y).subscheme ≫ b)
    (Palomar.normalizationMap (pointClosureIdealSheaf y).subscheme ≫ a)
    (schemeGlobalNormalizationLift
      (pointClosureReturnMap (End.of g ^ n).asHom y hy))).1 hb

/-- The source-form positive-characteristic inputs imply full recursive
PCF for every finite semiconjugate image of a normal system. -/
theorem isPCFAllSubvarieties_of_normal_finite_cover_charp_of_ambientBase
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (htransfer : FiniteSemiconjugacyPCFTransfer k)
    (hcodim : AllCodimNormalizedReturnPCFAtAmbientBase p k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g)
    (hmono : IsPrimeToPMonodromyMap p g) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_of_normal_finite_cover_charp p hp k htransfer
    (allCodimNormalizedReturnPCF_of_ambientBase p k hcodim)
    s f g π hcomm hpcf hmono

/-- The source-form characteristic-zero inputs imply full recursive PCF
for every finite semiconjugate image of a normal system. -/
theorem isPCFAllSubvarieties_of_normal_finite_cover_charZero_of_ambientBase
    (k : Type u) [Field k] [CharZero k]
    (htransfer : FiniteSemiconjugacyPCFTransfer k)
    (hcodim : AllCodimNormalizedReturnPCFCharZeroAtAmbientBase k)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y] [IsNormalScheme Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsSeparableNormalizedPCF k (π ≫ s) g) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_of_normal_finite_cover_charZero k htransfer
    (allCodimNormalizedReturnPCFCharZero_of_ambientBase k hcodim)
    s f g π hcomm hpcf

#print axioms isSeparableNormalizedPCF_base_iff
#print axioms allCodimNormalizedReturnPCF_of_ambientBase
#print axioms allCodimNormalizedReturnPCFCharZero_of_ambientBase
#print axioms isPCFAllSubvarieties_of_normal_finite_cover_charp_of_ambientBase
#print axioms isPCFAllSubvarieties_of_normal_finite_cover_charZero_of_ambientBase

end Pcf
