/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingCharPPointwise
public import Pcf.Bounding.PaperPBoundingCharZeroPointwise

/-!
# Bounding theorem as the upper-component étaleness premise

The pointwise bounding theorem gives the precise universal upper étaleness
premise used in `prop:bound-blowup`: every source divisor above a target
divisor outside the manuscript's exceptional set `Σ` has an étale stalk.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The positive-characteristic bounding theorem supplies upper étaleness
at every source divisor lying above a target divisor outside `Σ`.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharP_upperEtale_of_notSigma
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X)
    (D : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    D.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
      ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
        A.closureMapFiniteDominantNormal f E.1 = D.1 →
        ((A.closureMapFiniteDominantNormal f).stalkMap E.1).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  intro hD E hE
  exact paperPBoundingCharP_at_formallyEtale p hp k s f hmono A E.1 D hE hD

/-- Characteristic-zero form of the universal upper étaleness premise.

`paper-p.tex` correspondence: Theorem 7.5 (`thm:bounding`). -/
theorem paperPBoundingCharZero_upperEtale_of_notSigma
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (A : SchemeDivisorPoint X)
    (D : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    D.1 ∉ paperPBoundingSigma f (A.mapFiniteDominantNormal f) →
      ∀ E : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
        A.closureMapFiniteDominantNormal f E.1 = D.1 →
        ((A.closureMapFiniteDominantNormal f).stalkMap E.1).hom.FormallyEtale := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  intro hD E hE
  exact paperPBoundingCharZero_at_formallyEtale k s f A E.1 D hE hD

#print axioms paperPBoundingCharP_upperEtale_of_notSigma
#print axioms paperPBoundingCharZero_upperEtale_of_notSigma

end
end Pcf
