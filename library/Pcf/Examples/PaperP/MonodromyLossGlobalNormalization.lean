/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossProductNormal
public import Pcf.Examples.PaperP.MonodromyLossProductDegree
public import Pcf.Palomar.Bridge
public import Pcf.Bounding.PrimeToPMonodromyOpenSquare

/-!
# The normalization of `X` is `E ×ₖ ℙ¹`, and the normalization of `f` is `F`

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "The map `F` descends to a finite map
`f` of the resulting nonnormal variety `X`. Its normalization is `F`, which is PCF with prime-to-3
monodromy" (the transfer to `f`).

* **`normalizationIso : X̃ ≅ E ×ₖ ℙ¹`** over `X` (`normalizationIso_hom_nu`): `ν` is finite,
  birational, and `E ×ₖ ℙ¹` is normal;
* `normalizationMap_isFinite`;
* `fX_isDominant`;
* **`isNormalizationLift_F`**: the conjugate `F̃ = e ∘ F ∘ e⁻¹` of `F` is a normalization lift of
  `f`, and **`normalizationLift_eq`**: it is *the* canonical normalization lift of `f`;
* `ramificationIndexAt_eq_one_of_etale`, `isPCF_of_etale` (general): an étale endomorphism is PCF;
* **`fX_isNormalizedPCF`**: `f` is PCF on the normalization (its normalization `F` is étale);
* **`fX_isPrimeToThreeMonodromy`**: `f` has prime-to-3 monodromy (transported from `F` along the
  birational square `ν ∘ F = f ∘ ν`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

universe u

set_option linter.style.haveILetI false

/-- An étale morphism is unramified at every point: `e_f(x) = 1`. -/
theorem ramificationIndexAt_eq_one_of_etale {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g] (x : X) :
    Pcf.Palomar.ramificationIndexAt g x = 1 := by
  unfold Pcf.Palomar.ramificationIndexAt
  letI := (g.stalkMap x).hom.toAlgebra
  haveI : Algebra.FormallyUnramified (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    FormallyUnramified.stalkMap g x
  haveI : Algebra.EssFiniteType (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap g x
  haveI : Algebra.IsUnramifiedAt (Y.presheaf.stalk (g x))
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    Algebra.FormallyUnramified.comp _ (X.presheaf.stalk x) _
  exact Ideal.ramificationIdx_eq_one _ _

/-- **An étale endomorphism is PCF** (its post-critical set is empty). -/
theorem isPCF_of_etale {X : Scheme.{u}} (g : X ⟶ X) [Etale g] : Pcf.Palomar.IsPCF g := by
  have : Pcf.Palomar.postcriticalSet g = ∅ := by
    ext y
    simp only [Pcf.Palomar.postcriticalSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, -, hram, -⟩
    rw [ramificationIndexAt_eq_one_of_etale] at hram
    exact lt_irrefl _ hram
  unfold Pcf.Palomar.IsPCF
  rw [this]
  exact Set.finite_empty

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.NormalizationOfBirationalCover

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- **The normalization of `X` is `E ×ₖ ℙ¹`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
noncomputable def normalizationIso : Pcf.Palomar.normalization (X k i hi) ≅ EP1 k :=
  normalizationIsoOfBirational (nu k i hi)

/-- **The isomorphism is over `X`:** under it, the normalization map of `X` is `ν`. -/
@[reassoc (attr := simp)]
theorem normalizationIso_hom_nu :
    (normalizationIso k i hi).hom ≫ nu k i hi = Pcf.Palomar.normalizationMap (X k i hi) :=
  normalizationIsoOfBirational_hom_comp _

@[reassoc (attr := simp)]
theorem normalizationIso_inv_normalizationMap :
    (normalizationIso k i hi).inv ≫ Pcf.Palomar.normalizationMap (X k i hi) = nu k i hi :=
  normalizationIsoOfBirational_inv_comp _

instance normalizationMap_isFinite : IsFinite (Pcf.Palomar.normalizationMap (X k i hi)) :=
  normalizationMap_isFinite_of_birational (nu k i hi)

instance fX_isDominant : IsDominant (fX k i hi) := by
  haveI : IsDominant (nu k i hi ≫ fX k i hi) := by rw [nu_fX]; infer_instance
  exact IsDominant.of_comp (nu k i hi) (fX k i hi)

/-- `F` transported to the normalization of `X`. -/
noncomputable def Ftilde : Pcf.Palomar.normalization (X k i hi) ⟶
    Pcf.Palomar.normalization (X k i hi) :=
  (normalizationIso k i hi).hom ≫ bigF k i hi ≫ (normalizationIso k i hi).inv

theorem genericToNormalization_iso :
    Pcf.Palomar.genericToNormalization (X k i hi) ≫ (normalizationIso k i hi).hom =
      genericLift (nu k i hi) :=
  (Pcf.schemeGenericInclusion (X k i hi)).toNormalization_normalizationDesc _ _
    (genericLift_comp _)

/-- **`F` is the normalization lift of `f`.** -/
theorem isNormalizationLift_F : Pcf.Palomar.IsNormalizationLift (fX k i hi) (Ftilde k i hi) := by
  have h1 : Pcf.schemeGenericInclusion (EP1 k) ≫ (normalizationIso k i hi).inv =
      Pcf.schemeGenericMorphism (nu k i hi) ≫ Pcf.Palomar.genericToNormalization (X k i hi) := by
    rw [Iso.comp_inv_eq, Category.assoc, genericToNormalization_iso, genericLift,
      IsIso.hom_inv_id_assoc]
  refine ⟨?_, inv (Pcf.schemeGenericMorphism (nu k i hi)) ≫
    Pcf.schemeGenericMorphism (bigF k i hi) ≫ Pcf.schemeGenericMorphism (nu k i hi), ?_⟩
  · rw [Ftilde, Category.assoc, Category.assoc, normalizationIso_inv_normalizationMap,
      ← normalizationIso_hom_nu, Category.assoc, nu_fX]
  · rw [Ftilde, ← Category.assoc, genericToNormalization_iso, genericLift, Category.assoc,
      ← Pcf.schemeGenericMorphism_comp_assoc, h1]
    simp only [Category.assoc]

/-- **`F` is the canonical normalization lift of `f`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem normalizationLift_eq :
    Pcf.schemeGlobalNormalizationLift (fX k i hi) = Ftilde k i hi :=
  Pcf.Palomar.isNormalizationLift_unique _ (Pcf.Palomar.isNormalizationLift_lift _)
    (isNormalizationLift_F k i hi)

instance Ftilde_etale : Etale (Ftilde k i hi) := by unfold Ftilde; infer_instance

/-- **`f` is PCF on the normalization:** its normalization lift is `F`, which is étale. -/
theorem fX_isNormalizedPCF : Pcf.Palomar.IsNormalizedPCF (fX k i hi) := by
  rw [Pcf.Palomar.isNormalizedPCF_iff_lift, normalizationLift_eq]
  exact isPCF_of_etale _

/-- **`f` has prime-to-3 monodromy**, transported from `F` along `ν ∘ F = f ∘ ν`.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem fX_isPrimeToThreeMonodromy : Pcf.IsPrimeToPMonodromyMap 3 (fX k i hi) := by
  have hF : (bigF k i hi) (genericPoint (EP1 k)) = genericPoint (EP1 k) :=
    Pcf.map_genericPoint_eq_of_isDominant _
  obtain ⟨eE, eK, hcomm⟩ := Pcf.exists_stalkEquivs_of_square (bigF k i hi) (nu k i hi)
    (nu k i hi) (fX k i hi) (nu_fX k i hi).symm (genericPoint _)
    (Pcf.map_genericPoint_eq_of_isDominant (nu k i hi))
    (ConcreteCategory.bijective_of_isIso _)
    (by rw [hF]; exact ConcreteCategory.bijective_of_isIso _)
  refine Pcf.isPrimeToPMonodromyMap_of_genericStalkEquivs 3 (bigF k i hi) (fX k i hi)
    eK.symm eE.symm ?_ (MonodromyLossProductDegree.bigF_isPrimeToThreeMonodromy k i hi)
  apply RingHom.ext
  intro y
  have := congrArg (fun φ => φ (eK.symm y)) hcomm
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply] at this
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [this, RingEquiv.symm_apply_apply]

#print axioms normalizationIso
#print axioms normalizationLift_eq
#print axioms fX_isNormalizedPCF
#print axioms fX_isPrimeToThreeMonodromy

end Pcf.Examples.PaperP.MonodromyLossGlobal
