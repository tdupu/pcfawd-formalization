/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GenericStalkMonodromyTransport
public import Pcf.Bounding.NormalizationSeparable

/-!
# Prime-to-characteristic monodromy of the canonical normalization lift

The generic stalk maps of an integral scheme and its normalization are
isomorphisms. The commuting normalization square therefore identifies the
field extension of a finite dominant endomorphism with that of its lift.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- The canonical normalization lift has the same prime-to-`p` generic
monodromy as the original finite dominant endomorphism. -/
theorem isPrimeToPMonodromyMap_schemeGlobalNormalizationLift
    (p : ℕ) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsFinite (Palomar.normalizationMap X)]
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPrimeToPMonodromyMap p (schemeGlobalNormalizationLift f) := by
  let N := Palomar.normalization X
  let n := Palomar.normalizationMap X
  let l := schemeGlobalNormalizationLift f
  let η := genericPoint N
  have hη : n η = genericPoint X := map_genericPoint_eq_of_isDominant n
  have hlη : l η = η := map_genericPoint_eq_of_isDominant l
  have hfl : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  have hpoint : f (genericPoint X) = n (l η) := by
    have h := congrArg (fun m : N ⟶ X => m η)
      (schemeGlobalNormalizationLift_comp f)
    change n (l η) = f (n η) at h
    rw [hη] at h
    exact h.symm
  have hiso : IsIso (n.stalkMap η) := by
    change IsIso ((Palomar.normalizationMap X).stalkMap
      (genericPoint (Palomar.normalization X)))
    infer_instance
  have hiso' : IsIso (n.stalkMap (l η)) := by
    rw [hlη]
    exact hiso
  let eE : X.presheaf.stalk (genericPoint X) ≃+* N.presheaf.stalk η :=
    ((X.presheaf.stalkCongr (.of_eq hη.symm)) ≪≫
      asIso (n.stalkMap η)).commRingCatIsoToRingEquiv
  let eK : X.presheaf.stalk (f (genericPoint X)) ≃+*
      N.presheaf.stalk (l η) :=
    ((X.presheaf.stalkCongr (.of_eq hpoint)) ≪≫
      asIso (n.stalkMap (l η))).commRingCatIsoToRingEquiv
  have hcomm : (l.stalkMap η).hom.comp eK.toRingHom =
      eE.toRingHom.comp (f.stalkMap (genericPoint X)).hom := by
    have hsqpoint : n (l η) = f (n η) := by
      have h := congrArg (fun m : N ⟶ X => m η)
        (schemeGlobalNormalizationLift_comp f)
      simpa only [Scheme.Hom.comp_apply] using h
    have himage : f (genericPoint X) = f (n η) :=
      congrArg f hη.symm
    have hcompCongr :
        (X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
          (X.presheaf.stalkCongr (.of_eq hsqpoint)).hom =
        (X.presheaf.stalkCongr (.of_eq himage)).hom := by
      change X.presheaf.stalkSpecializes (Inseparable.of_eq hpoint).ge ≫
        X.presheaf.stalkSpecializes (Inseparable.of_eq hsqpoint).ge =
        X.presheaf.stalkSpecializes (Inseparable.of_eq himage).ge
      exact TopCat.Presheaf.stalkSpecializes_comp _ _ _
    have hsquare := Scheme.Hom.stalkMap_congr_hom (l ≫ n) (n ≫ f)
      (schemeGlobalNormalizationLift_comp f) η
    simp only [Scheme.Hom.stalkMap_comp] at hsquare
    let cE : X.presheaf.stalk (genericPoint X) ⟶ N.presheaf.stalk η :=
      (X.presheaf.stalkCongr (.of_eq hη.symm)).hom ≫ n.stalkMap η
    let cK : X.presheaf.stalk (f (genericPoint X)) ⟶
        N.presheaf.stalk (l η) :=
      (X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫ n.stalkMap (l η)
    have hcat : cK ≫ l.stalkMap η =
        f.stalkMap (genericPoint X) ≫ cE := by
      dsimp only [cK, cE]
      have hnat := Scheme.Hom.stalkMap_congr_point f
        (genericPoint X) (n η) hη.symm
      calc
        ((X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            n.stalkMap (l η)) ≫ l.stalkMap η =
          (X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            (n.stalkMap (l η) ≫ l.stalkMap η) := Category.assoc _ _ _
        _ = (X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            ((X.presheaf.stalkCongr (.of_eq hsqpoint)).hom ≫
              f.stalkMap (n η) ≫ n.stalkMap η) := by
          rw [hsquare]
          rfl
        _ = ((X.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            (X.presheaf.stalkCongr (.of_eq hsqpoint)).hom) ≫
              f.stalkMap (n η) ≫ n.stalkMap η := by
          simp only [Category.assoc]
        _ = (X.presheaf.stalkCongr (.of_eq himage)).hom ≫
              f.stalkMap (n η) ≫ n.stalkMap η := by rw [hcompCongr]
        _ = (f.stalkMap (genericPoint X) ≫
              (X.presheaf.stalkCongr (.of_eq hη.symm)).hom) ≫
                n.stalkMap η := by
          rw [hnat]
          exact (Category.assoc _ _ _).symm
        _ = f.stalkMap (genericPoint X) ≫
            ((X.presheaf.stalkCongr (.of_eq hη.symm)).hom ≫
              n.stalkMap η) := by
          exact Category.assoc _ _ _
    change (l.stalkMap η).hom.comp cK.hom =
      cE.hom.comp (f.stalkMap (genericPoint X)).hom
    exact congrArg CommRingCat.Hom.hom hcat
  exact isPrimeToPMonodromyMap_of_genericStalkEquivs p f l
    eK eE hcomm hmono

#print axioms isPrimeToPMonodromyMap_schemeGlobalNormalizationLift

end Pcf
