/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingUniformFamilySigma
public import Pcf.Bounding.PaperPBoundingUpperEtaBridge

/-!
# Upper étaleness outside a fixed finite tower correction

For a finite family of branch divisors on a fixed normal target, the exact
bounding corrections for every cover in the family lie in one finite set on
each fixed target divisor. The pointwise bounding theorem then gives the
universal upper étaleness condition used in `prop:bound-blowup`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- Characteristic-`p` upper étaleness outside the fixed finite correction
from a common branch-divisor family. -/
theorem paperPBoundingCharP_upperEtale_of_fixedFamily
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X)
    (W : Set Y) (hW : W.Finite)
    (hcodim : ∀ y ∈ W, Order.coheight y = 1)
    (hbranch :
      letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
      letI : IsFinite (Palomar.normalizationMap Y) :=
        schemeGlobalNormalizationMap_isFinite Y k s
      weightedBranchPointSet f ⊆ W) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    let B := A.mapFiniteDominantNormal f
    {D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
      D.1 ∈ paperPBoundingFixedSigma W B}.Finite ∧
      ∀ D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme,
        D.1 ∉ paperPBoundingFixedSigma W B →
        ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
          A.closureMapFiniteDominantNormal f E.1 = D.1 →
          ((A.closureMapFiniteDominantNormal f).stalkMap E.1).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  let B := A.mapFiniteDominantNormal f
  refine ⟨paperPBoundingFixedSigma_badDivisors_finite k s B W hW hcodim, ?_⟩
  intro D hD E hE
  have hnotSigma : D.1 ∉ paperPBoundingSigma f B := by
    intro h
    exact hD (paperPBoundingSigma_subset_fixedSigma f B W hbranch h)
  exact paperPBoundingCharP_at_formallyEtale p hp k s f hmono A E.1 D hE hnotSigma

/-- Characteristic-zero upper étaleness outside the same fixed correction. -/
theorem paperPBoundingCharZero_upperEtale_of_fixedFamily
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X)
    (W : Set Y) (hW : W.Finite)
    (hcodim : ∀ y ∈ W, Order.coheight y = 1)
    (hbranch :
      letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
      letI : IsFinite (Palomar.normalizationMap Y) :=
        schemeGlobalNormalizationMap_isFinite Y k s
      weightedBranchPointSet f ⊆ W) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    let B := A.mapFiniteDominantNormal f
    {D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
      D.1 ∈ paperPBoundingFixedSigma W B}.Finite ∧
      ∀ D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme,
        D.1 ∉ paperPBoundingFixedSigma W B →
        ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
          A.closureMapFiniteDominantNormal f E.1 = D.1 →
          ((A.closureMapFiniteDominantNormal f).stalkMap E.1).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  let B := A.mapFiniteDominantNormal f
  refine ⟨paperPBoundingFixedSigma_badDivisors_finite k s B W hW hcodim, ?_⟩
  intro D hD E hE
  have hnotSigma : D.1 ∉ paperPBoundingSigma f B := by
    intro h
    exact hD (paperPBoundingSigma_subset_fixedSigma f B W hbranch h)
  exact paperPBoundingCharZero_at_formallyEtale k s f A E.1 D hE hnotSigma

#print axioms paperPBoundingCharP_upperEtale_of_fixedFamily
#print axioms paperPBoundingCharZero_upperEtale_of_fixedFamily

end
end Pcf
