/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PointClosureStalkAtImage

/-!
# Quotient and generic-stalk compatibility for reduced point closures
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

@[instance_reducible] private noncomputable def centreFieldAlgebra_at_equal_ideal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] (P : Ideal R) [P.IsPrime]
    (h : Q.under R = P) :
    Algebra (FractionRing (R ⧸ P)) (FractionRing (S ⧸ Q)) := by
  subst P
  exact centreFieldAlgebra Q

private theorem primeToPMonodromy_at_equal_ideal
    (p : ℕ) {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (Q : Ideal S) [Q.IsPrime]
    (P : Ideal R) [P.IsPrime] (h : Q.under R = P)
    (hm : @IsPrimeToPMonodromy.{u, u, u} p
      (FractionRing (R ⧸ Q.under R)) (FractionRing (S ⧸ Q))
      _ _ (centreFieldAlgebra Q)) :
    @IsPrimeToPMonodromy.{u, u, u} p
      (FractionRing (R ⧸ P)) (FractionRing (S ⧸ Q))
      _ _ (centreFieldAlgebra_at_equal_ideal Q P h) := by
  subst P
  exact hm

private theorem centreFieldAlgebra_at_equal_ideal_algebraMap_quotient
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] (P : Ideal R) [P.IsPrime]
    (h : Q.under R = P) (a : R ⧸ P) :
    letI : Q.LiesOver P := ⟨h.symm⟩
    letI : Algebra (R ⧸ P) (S ⧸ Q) := inferInstance
    letI : Algebra (FractionRing (R ⧸ P)) (FractionRing (S ⧸ Q)) :=
      centreFieldAlgebra_at_equal_ideal Q P h
    algebraMap (FractionRing (R ⧸ P)) (FractionRing (S ⧸ Q))
        (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) a) =
      algebraMap (S ⧸ Q) (FractionRing (S ⧸ Q))
        (algebraMap (R ⧸ P) (S ⧸ Q) a) := by
  subst P
  exact centreFieldAlgebra_algebraMap_quotient Q a

/-- The restriction of a finite map with prime-to-`p` monodromy to
the reduced closures of any point and its image has literal
prime-to-`p` monodromy on its generic stalk map. -/
theorem pointClosureSubschemeMap_primeToPMonodromy
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (U : Y.affineOpens)
    [Algebra k Γ(Y, U)] [Algebra.FiniteType k Γ(Y, U)]
    [CharP Γ(Y, U) p]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) (hx : x ∈ (finitePreimageAffine f U : X.Opens)) :
    let g := pointClosureSubschemeMap f x (f x) rfl
    letI : IsFinite g := pointClosureSubschemeMap_isFinite f x (f x) rfl
    letI : IsDominant g := pointClosureSubschemeMap_isDominant f x (f x) rfl
    IsPrimeToPMonodromyMap p g := by
  let V := finitePreimageAffine f U
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf (f x)
  let g := I.subschemeMap J f
    (pointClosureIdealSheaf_le_map_of_apply_eq f x (f x) rfl)
  letI : IsFinite g := pointClosureSubschemeMap_isFinite f x (f x) rfl
  letI : IsDominant g := pointClosureSubschemeMap_isDominant f x (f x) rfl
  have hmap : g (genericPoint I.subscheme) = genericPoint J.subscheme :=
    pointClosureSubschemeMap_map_genericPoint f x
  let R := Γ(Y, U)
  let S := Γ(X, V)
  letI : Algebra R S := (f.app U).hom.toAlgebra
  let Q : Ideal S := I.ideal V
  letI : Q.IsPrime := pointClosureIdealSheaf_ideal_isPrime x V hx
  obtain ⟨hcontract, hmonoCentre⟩ :=
    finiteNormalAffinePreimage_pointClosure_primeToPMonodromy
      p hp k f U hmono x hx
  let P : Ideal R := J.ideal U
  letI : P.IsPrime := pointClosureIdealSheaf_ideal_isPrime (f x) U hx
  letI : Q.LiesOver P := ⟨hcontract.symm⟩
  letI : Algebra (R ⧸ P) (S ⧸ Q) := inferInstance
  let F := FractionRing (R ⧸ P)
  let E := FractionRing (S ⧸ Q)
  letI : Algebra F E := centreFieldAlgebra_at_equal_ideal Q P hcontract
  have hX : genericPoint I.subscheme ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens) := by
    change I.subschemeι (genericPoint I.subscheme) ∈ (V : X.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  have hY : genericPoint J.subscheme ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := by
    change J.subschemeι (genericPoint J.subscheme) ∈ (U : Y.Opens)
    rw [pointClosureSubschemeι_genericPoint]
    exact hx
  let y := g (genericPoint I.subscheme)
  have hy : y = genericPoint J.subscheme := hmap
  let eJ := (J.subscheme.presheaf.stalkCongr
    (Inseparable.of_eq hy)).commRingCatIsoToRingEquiv
  letI : Field (J.subscheme.presheaf.stalk y) :=
    (eJ.toMulEquiv.isField (Field.toIsField _)).toField
  letI : Algebra (S ⧸ Q) I.subscheme.functionField :=
    I.quotientStalkAlgebra V (genericPoint I.subscheme) hX
  have hYim : y ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := by
    rw [hy]
    exact hY
  letI : Algebra (R ⧸ P) (J.subscheme.presheaf.stalk y) :=
    J.quotientStalkAlgebra U y hYim
  letI : IsFractionRing (S ⧸ Q) I.subscheme.functionField :=
    pointClosure_functionField_isFractionRing x V hx
  letI : IsFractionRing (R ⧸ P) (J.subscheme.presheaf.stalk y) :=
    pointClosure_stalk_isFractionRing_of_eq_generic (f x) U hx y hy
  letI : Algebra (J.subscheme.presheaf.stalk y) I.subscheme.functionField :=
    (g.stalkMap (genericPoint I.subscheme)).hom.toAlgebra
  let eF : F ≃ₐ[R ⧸ P] (J.subscheme.presheaf.stalk y) :=
    FractionRing.algEquiv (A := R ⧸ P) (J.subscheme.presheaf.stalk y)
  let eE : E ≃ₐ[S ⧸ Q] I.subscheme.functionField :=
    FractionRing.algEquiv (A := S ⧸ Q) I.subscheme.functionField
  letI : Q.LiesOver (J.ideal U) := ⟨hcontract.symm⟩
  letI : Algebra (R ⧸ J.ideal U) (S ⧸ Q) := inferInstance
  have hAlg : algebraMap R S = (f.appLE U V le_rfl).hom := by
    change (f.app U).hom = (f.appLE U V le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hQmap : Ideal.quotientMap Q (f.appLE U V le_rfl).hom
        (I.subschemeMap_ideal_le J f
          (pointClosureIdealSheaf_le_map_of_apply_eq f x (f x) rfl)
          U V le_rfl) = algebraMap (R ⧸ J.ideal U) (S ⧸ Q) := by
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext r
    simp only [RingHom.comp_apply]
    rw [← hAlg]
    exact (Ideal.Quotient.algebraMap_mk_of_liesOver
      (P := Q) (p := J.ideal U) r).symm
  have hring : (algebraMap (J.subscheme.presheaf.stalk y)
        I.subscheme.functionField).comp (algebraMap (R ⧸ P)
          (J.subscheme.presheaf.stalk y)) =
      (algebraMap (S ⧸ Q) I.subscheme.functionField).comp
        (algebraMap (R ⧸ P) (S ⧸ Q)) := by
    have hstalkMap (z : J.subscheme.presheaf.stalk y) :
        algebraMap (J.subscheme.presheaf.stalk y)
          I.subscheme.functionField z =
        (g.stalkMap (genericPoint I.subscheme)).hom z := rfl
    have hsquare := pointClosure_genericStalk_quotient_square f U x hx
    dsimp only at hsquare
    rw [hQmap] at hsquare
    ext a
    have ha := congrArg (fun h => h a) hsquare
    simp only [RingHom.comp_apply, hstalkMap] at ⊢
    simpa only [RingHom.comp_apply, y, g, I, J, V, R, S, P, Q]
      using ha
  have hfield : (algebraMap (J.subscheme.presheaf.stalk y)
        I.subscheme.functionField).comp eF.toRingEquiv.toRingHom =
      eE.toRingEquiv.toRingHom.comp (algebraMap F E) := by
    apply IsFractionRing.ringHom_ext (A := R ⧸ P)
    intro a
    simp only [RingHom.comp_apply]
    change (algebraMap (J.subscheme.presheaf.stalk y) I.subscheme.functionField)
        (eF (algebraMap (R ⧸ P) F a)) =
      eE (algebraMap F E (algebraMap (R ⧸ P) F a))
    rw [eF.commutes,
      centreFieldAlgebra_at_equal_ideal_algebraMap_quotient Q P hcontract,
      eE.commutes]
    exact congrArg (fun h : (R ⧸ P) →+* I.subscheme.functionField => h a)
      hring
  change IsPrimeToPMonodromy.{u, u, u} p
    (J.subscheme.presheaf.stalk y) I.subscheme.functionField
  exact isPrimeToPMonodromy_of_equiv_equiv p F E
    (J.subscheme.presheaf.stalk y) I.subscheme.functionField
    eF.toRingEquiv eE.toRingEquiv hfield
      (primeToPMonodromy_at_equal_ideal p Q P hcontract hmonoCentre)


#print axioms pointClosureSubschemeMap_primeToPMonodromy

end Pcf
