/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeCharPTransfer

/-!
# Reducing the all-codimension return to a uniform branch support

`AllCodimNormalizedReturnPCF` asks that the normalized return on every
periodic point closure be separable and PCF. Separability follows from
prime-to-`p` monodromy of that return. PCF follows once one finite set of
divisors of the normalization contains the images of the non-étale divisors
of every iterate. That uniform support is the content of the normalized
blow-up argument in `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The uniform branch-support assertion of `thm:allcodim-normal`: for the
normalized return on an actual periodic point closure, one finite set of
divisors contains the images of the non-étale divisors of every iterate. -/
def AllCodimUniformReturnSupport
    (p : ℕ) (k : Type u) [Field k] [CharP k p] : Prop :=
  ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace Y] [IsNormalScheme Y]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t]
    (g : Y ⟶ Y) [IsFinite g] [IsDominant g],
    IsSeparableNormalizedPCF k t g → IsPrimeToPMonodromyMap p g →
    ∀ (y : Y) (n : ℕ) (_ : 0 < n)
      (hy : schemePointIterate g n y = y)
      (a : (pointClosureIdealSheaf y).subscheme ⟶ Spec (.of k))
      [LocallyOfFiniteType a],
      let q := pointClosureReturnMap (End.of g ^ n).asHom y hy
      let A := (pointClosureIdealSheaf y).subscheme
      let ν := Palomar.normalizationMap A
      letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
      let F := schemeGlobalNormalizationLift q
      ∃ T : Set (SchemeDivisorPoint (Palomar.normalization A)), T.Finite ∧
        ∀ (m : ℕ), 1 ≤ m → ∀ Q ∈ schemeDivisorNonEtaleLocus (End.of F ^ m).asHom,
          (fun d : SchemeDivisorPoint (Palomar.normalization A) =>
            d.mapFiniteDominantNormal F)^[m] Q ∈ T

/-- The uniform branch support gives the all-codimension normalized return
hypothesis of the all-subvariety induction. -/
theorem allCodimNormalizedReturnPCF_of_uniformReturnSupport
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (h : AllCodimUniformReturnSupport p k) : AllCodimNormalizedReturnPCF p k := by
  intro Y _ _ _ _ t _ g _ _ hpcf hmono y n hn hy a _
  obtain ⟨T, hT, hbound⟩ := h t g hpcf hmono y n hn hy a
  let q := pointClosureReturnMap (End.of g ^ n).asHom y hy
  let A := (pointClosureIdealSheaf y).subscheme
  let ν := Palomar.normalizationMap A
  letI : IsFinite ν := schemeGlobalNormalizationMap_isFinite A k a
  let F := schemeGlobalNormalizationLift q
  have hmonoF : IsPrimeToPMonodromyMap p F :=
    finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy p hp k g t hmono
      n hn y hy
  have hsep : IsGenericallySeparable F :=
    isGenericallySeparable_of_isPrimeToPMonodromyMap p F hmonoF
  haveI : IsLocallyNoetherian (Palomar.normalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  haveI : CompactSpace (Palomar.normalization A) :=
    QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Palomar.normalization A) := ⟨⟩
  rw [normalScheme_isSeparableNormalizedPCF_iff k (ν ≫ a) F]
  exact ⟨hsep, isNormalNonEtalePCF_of_uniform_iterate_support F hsep T hT hbound⟩

#print axioms allCodimNormalizedReturnPCF_of_uniformReturnSupport

/-- The characteristic-`p` all-subvariety theorem for every finite
semiconjugate image of a normal system, conditional only on the uniform
branch support of `thm:allcodim-normal`. The PCF transfer input is
`finiteSemiconjugacyPCFTransfer`. -/
theorem isPCFAllSubvarieties_of_uniformReturnSupport
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    (h : AllCodimUniformReturnSupport p k)
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
  isPCFAllSubvarieties_of_normal_finite_cover_charp p hp k (finiteSemiconjugacyPCFTransfer k)
    (allCodimNormalizedReturnPCF_of_uniformReturnSupport p hp k h) s f g π hcomm hpcf hmono

#print axioms isPCFAllSubvarieties_of_uniformReturnSupport

end
end Pcf
