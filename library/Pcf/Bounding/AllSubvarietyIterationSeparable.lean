/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyIteration

/-!
# Generic separability descends from a positive iterate

The separability clause in `paper-p.tex`, Lemma `lem:allsubvar-iterate`,
descends from an iterate because the field embedding of the iterate
factors through the field embedding of one step. The result uses the
actual generic stalk maps of scheme morphisms.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- If one field embedding factors through another and the larger
extension is separable, then the intermediate extension is separable. -/
private theorem isSeparable_of_factor
    (F : Type u) [Field F] (a b c : F →+* F)
    (hc : c = b.comp a)
    (hsep : @Algebra.IsSeparable F F _ _ c.toAlgebra) :
    @Algebra.IsSeparable F F _ _ a.toAlgebra := by
  let β : @AlgHom F F F _ _ _ a.toAlgebra c.toAlgebra :=
    @AlgHom.mk F F F _ _ _ a.toAlgebra c.toAlgebra b (by
      intro x
      exact congrArg (fun h : F →+* F => h x) hc.symm)
  exact @Algebra.IsSeparable.of_algHom F _ F F _ _
    a.toAlgebra c.toAlgebra hsep β

/-- Generic separability of a positive categorical iterate of a finite
dominant endomorphism implies generic separability of the original map. -/
theorem isGenericallySeparable_of_pow
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X]
    (m : ℕ) (hm : 0 < m)
    (hsep : IsGenericallySeparable (End.of f ^ m).asHom) :
    IsGenericallySeparable f := by
  cases m with
  | zero => cases hm
  | succ n =>
    let η := genericPoint X
    let g := (End.of f ^ n).asHom
    have hgf : (End.of f ^ (n + 1)).asHom = g ≫ f := by
      simp only [g, pow_succ', End.mul_asHom]
    have hfη : f η = η := map_genericPoint_eq_of_isDominant f
    have hgη : g η = η := by
      letI : IsDominant g := isDominant_end_pow f n
      exact map_genericPoint_eq_of_isDominant g
    let a : X.presheaf.stalk η →+* X.presheaf.stalk η :=
      ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫ f.stalkMap η).hom
    let b : X.presheaf.stalk η →+* X.presheaf.stalk η :=
      ((X.presheaf.stalkCongr (.of_eq hgη.symm)).hom ≫ g.stalkMap η).hom
    have hgfη : (g ≫ f) η = η := by
      change f (g η) = η
      rw [hgη, hfη]
    let c : X.presheaf.stalk η →+* X.presheaf.stalk η :=
      ((X.presheaf.stalkCongr (.of_eq hgfη.symm)).hom ≫
        (g ≫ f).stalkMap η).hom
    have hc : c = b.comp a := by
      have hnat := Scheme.Hom.stalkMap_congr_point f η (g η) hgη.symm
      have hF : f η = f (g η) := congrArg f hgη.symm
      have hcongr :
          (X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫
            (X.presheaf.stalkCongr (.of_eq hF)).hom =
          (X.presheaf.stalkCongr (.of_eq hgfη.symm)).hom := by
        change X.presheaf.stalkSpecializes (Inseparable.of_eq hfη.symm).ge ≫
          X.presheaf.stalkSpecializes
            (Inseparable.of_eq hF).ge =
          X.presheaf.stalkSpecializes (Inseparable.of_eq hgfη.symm).ge
        exact TopCat.Presheaf.stalkSpecializes_comp _ _ _
      have hcat :
          ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫ f.stalkMap η) ≫
            ((X.presheaf.stalkCongr (.of_eq hgη.symm)).hom ≫ g.stalkMap η) =
          (X.presheaf.stalkCongr (.of_eq hgfη.symm)).hom ≫
            (g ≫ f).stalkMap η := by
        calc
          ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫ f.stalkMap η) ≫
              ((X.presheaf.stalkCongr (.of_eq hgη.symm)).hom ≫ g.stalkMap η) =
            ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫
              (f.stalkMap η ≫
                (X.presheaf.stalkCongr (.of_eq hgη.symm)).hom)) ≫
              g.stalkMap η := by simp only [Category.assoc]
          _ = ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫
              ((X.presheaf.stalkCongr (.of_eq hF)).hom ≫
                f.stalkMap (g η))) ≫ g.stalkMap η := by rw [hnat]
          _ = ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫
              (X.presheaf.stalkCongr (.of_eq hF)).hom) ≫
              (f.stalkMap (g η) ≫ g.stalkMap η) := by
                simp only [Category.assoc]
          _ = (X.presheaf.stalkCongr (.of_eq hgfη.symm)).hom ≫
              (g ≫ f).stalkMap η := by rw [hcongr, Scheme.Hom.stalkMap_comp]
      change ((X.presheaf.stalkCongr (.of_eq hgfη.symm)).hom ≫
        (g ≫ f).stalkMap η).hom =
          ((X.presheaf.stalkCongr (.of_eq hgη.symm)).hom ≫
            g.stalkMap η).hom.comp
            ((X.presheaf.stalkCongr (.of_eq hfη.symm)).hom ≫
              f.stalkMap η).hom
      exact congrArg CommRingCat.Hom.hom hcat.symm
    have hsepC : @Algebra.IsSeparable (X.presheaf.stalk η)
        (X.presheaf.stalk η) _ _ c.toAlgebra := by
      let F := X.presheaf.stalk η
      let F₀ := X.presheaf.stalk ((g ≫ f) η)
      let e : F ≃+* F₀ :=
        (X.presheaf.stalkCongr (.of_eq hgfη.symm)).commRingCatIsoToRingEquiv
      letI : Field F₀ :=
        (e.symm.toMulEquiv.isField (Field.toIsField _)).toField
      letI : Algebra F₀ F := ((g ≫ f).stalkMap η).hom.toAlgebra
      have hsepGF : IsGenericallySeparable (g ≫ f) := by
        simpa only [hgf] using hsep
      have hsep₀ : Algebra.IsSeparable F₀ F := hsepGF
      letI : Algebra.IsSeparable F₀ F := hsep₀
      letI : Algebra F F := c.toAlgebra
      have he : (algebraMap F F).comp e.symm.toRingHom =
          (RingEquiv.refl F).toRingHom.comp (algebraMap F₀ F) := by
        ext z
        change ((g ≫ f).stalkMap η).hom (e (e.symm z)) =
          ((g ≫ f).stalkMap η).hom z
        rw [e.apply_symm_apply]
      exact Algebra.IsSeparable.of_equiv_equiv e.symm
        (RingEquiv.refl F) he
    have hsepA := isSeparable_of_factor (X.presheaf.stalk η) a b c hc hsepC
    let F := X.presheaf.stalk η
    let F₀ := X.presheaf.stalk (f η)
    let e : F ≃+* F₀ :=
      (X.presheaf.stalkCongr (.of_eq hfη.symm)).commRingCatIsoToRingEquiv
    letI : Field F₀ :=
      (e.symm.toMulEquiv.isField (Field.toIsField _)).toField
    letI : Algebra F₀ F := (f.stalkMap η).hom.toAlgebra
    letI : Algebra F F := a.toAlgebra
    letI : Algebra.IsSeparable F F := hsepA
    have he : (algebraMap F₀ F).comp e.toRingHom =
        (RingEquiv.refl F).toRingHom.comp (algebraMap F F) := by
      ext z
      rfl
    exact Algebra.IsSeparable.of_equiv_equiv e
      (RingEquiv.refl F) he

#print axioms isSeparable_of_factor
#print axioms isGenericallySeparable_of_pow

end Pcf
