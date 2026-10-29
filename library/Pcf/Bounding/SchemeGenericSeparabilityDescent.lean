/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeWeightedCriticalFinite

/-!
# Generic separability descent in a field diamond

This four-field formulation of the first paragraph of
`paper-p.tex`, Lemma `lem:pcf-transfer-charp`, is adapted to the four
generic stalk images of a finite commuting scheme square. It avoids
requiring all field images to be represented as intermediate fields of
one ambient type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Pcf

set_option linter.style.haveILetI false

universe u

/-- The actual commuting finite comparison square also commutes on
the spectra of its generic stalk fields. -/
theorem schemeGenericMorphism_commuting_square
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [AlgebraicGeometry.IsDominant f] [AlgebraicGeometry.IsDominant g]
    [AlgebraicGeometry.IsDominant π]
    (hcomm : g ≫ π = π ≫ f) :
    schemeGenericMorphism g ≫ schemeGenericMorphism π =
      schemeGenericMorphism π ≫ schemeGenericMorphism f := by
  rw [schemeGenericMorphism_comp_morphism,
    schemeGenericMorphism_comp_morphism]
  simp only [hcomm]

/-- Inseparable degree is invariant under an isomorphism of both the
base and extension fields in a commuting square. -/
theorem finInsepDegree_eq_of_equiv_equiv
    {F A B E : Type*} [Field F] [Field A] [Field B] [Field E]
    [Algebra F A] [Algebra B E]
    (e₁ : F ≃+* B) (e₂ : A ≃+* E)
    (he : (algebraMap B E).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap F A)) :
    Field.finInsepDegree F A = Field.finInsepDegree B E := by
  have he' : (algebraMap F A).comp e₁.symm.toRingHom =
      e₂.symm.toRingHom.comp (algebraMap B E) := by
    ext x
    simpa [RingEquiv.eq_symm_apply] using
      (RingHom.ext_iff.mp he (e₁.symm x)).symm
  let eSep : separableClosure F A ≃+* separableClosure B E := {
    toFun := fun x => ⟨e₂ x.1, mem_separableClosure_iff.mpr <|
      IsSeparable.of_equiv_equiv e₁ e₂ he
        (mem_separableClosure_iff.mp x.2)⟩
    invFun := fun x => ⟨e₂.symm x.1, mem_separableClosure_iff.mpr <|
      IsSeparable.of_equiv_equiv e₁.symm e₂.symm he'
        (mem_separableClosure_iff.mp x.2)⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp
    map_mul' := by intro x y; apply Subtype.ext; exact e₂.map_mul _ _
    map_add' := by intro x y; apply Subtype.ext; exact e₂.map_add _ _
  }
  unfold Field.finInsepDegree
  exact Algebra.finrank_eq_of_equiv_equiv eSep e₂ (by
    ext x
    rfl)

/-- Inseparable-degree cancellation in a commuting field diamond.
The equality of the two comparison degrees is the consequence of the
upstairs pullback isomorphism that remains to be supplied by the scheme
square. -/
theorem isSeparable_of_insepDegree_fieldDiamond
    (F A B E : Type*) [Field F] [Field A] [Field B] [Field E]
    [Algebra F A] [Algebra A E] [Algebra F B] [Algebra B E]
    [Algebra F E] [IsScalarTower F A E] [IsScalarTower F B E]
    [FiniteDimensional F A] [FiniteDimensional F B] [FiniteDimensional B E]
    (hsep : Algebra.IsSeparable A E)
    (hcomparison : Field.finInsepDegree F A = Field.finInsepDegree B E) :
    Algebra.IsSeparable F B := by
  letI : Algebra.IsSeparable A E := hsep
  have hA := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic F A E
  have hB := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic F B E
  rw [Algebra.IsSeparable.finInsepDegree_eq A E, mul_one] at hA
  have hprod : Field.finInsepDegree F B * Field.finInsepDegree B E =
      1 * Field.finInsepDegree B E := by
    calc
      _ = Field.finInsepDegree F E := hB
      _ = Field.finInsepDegree B E := hA.symm.trans hcomparison
      _ = 1 * Field.finInsepDegree B E := (one_mul _).symm
  have hpositive : 0 < Field.finInsepDegree B E := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdegree : Field.finInsepDegree F B = 1 :=
    Nat.mul_right_cancel hpositive hprod
  exact (isSeparable_iff_finInsepDegree_eq_one F B).mpr hdegree

/-- Separability descends across a commuting finite field diamond when
the two comparison extensions are identified by the upstairs field
pullback. This is the field-theoretic core of the first paragraph of
`lem:pcf-transfer-charp`, with no numerical degree premise. -/
theorem isSeparable_of_commuting_fieldDiamond
    (F A B E : Type*) [Field F] [Field A] [Field B] [Field E]
    [Algebra F A] [Algebra A E] [Algebra F B] [Algebra B E]
    [Algebra F E] [IsScalarTower F A E] [IsScalarTower F B E]
    [FiniteDimensional F A] [FiniteDimensional F B] [FiniteDimensional B E]
    (e₁ : F ≃+* B) (e₂ : A ≃+* E)
    (hcomm : (algebraMap B E).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap F A))
    (hsep : Algebra.IsSeparable A E) :
    Algebra.IsSeparable F B :=
  isSeparable_of_insepDegree_fieldDiamond F A B E hsep
    (finInsepDegree_eq_of_equiv_equiv e₁ e₂ hcomm)

#print axioms finInsepDegree_eq_of_equiv_equiv
#print axioms isSeparable_of_insepDegree_fieldDiamond
#print axioms isSeparable_of_commuting_fieldDiamond
#print axioms schemeGenericMorphism_commuting_square

end Pcf
