/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLinePCF
public import Pcf.Examples.PaperP.FrobeniusLineFunctionField

/-!
# The actual affine-line return is not generically separable

The generic stalk map of the actual restriction is identified with the
rational-function pullback `t ↦ t^p`. Thus the failure of separability is a
property of the scheme restriction, as well as of its explicit field model.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable def lineGenericLocalEquiv (I : Ideal (Polynomial k)) [I.IsPrime]
    (hI : I = ⊥) : Localization.AtPrime I ≃ₐ[Polynomial k] RatFunc k := by
  subst I
  haveI : IsFractionRing (Polynomial k) (Localization.AtPrime (⊥ : Ideal (Polynomial k))) := by
    change IsLocalization (nonZeroDivisors (Polynomial k))
      (Localization.AtPrime (⊥ : Ideal (Polynomial k)))
    rw [← Ideal.primeCompl_bot]
    infer_instance
  exact IsLocalization.algEquiv (nonZeroDivisors (Polynomial k)) _ _

local instance returnFinite : IsFinite (lineSchemeMap k p) :=
  lineSchemeMap_finite k p (Fact.out : p.Prime).two_le
local instance returnSurjective : Surjective (lineSchemeMap k p) :=
  lineSchemeMap_surjective k p (Fact.out : p.Prime).two_le

/-- The actual affine-line scheme restriction is not generically separable.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineSchemeMap_not_isGenericallySeparable :
    ¬ Pcf.IsGenericallySeparableSchemeMap (lineSchemeMap k p) := by
  intro hsep
  let g := lineSchemeMap k p
  let q := genericPoint (Spec (.of (Polynomial k)))
  let f := (lineCoordinateMap k p).toRingHom
  have hq : q.asIdeal = ⊥ := by
    dsimp [q]
    rw [genericPoint_eq_bot_of_affine]
    rfl
  have hI : q.asIdeal.comap f = ⊥ := by
    rw [hq]
    exact (RingHom.injective_iff_ker_eq_bot f).mp
      (lineCoordinateMap_injective k p (Fact.out : p.Prime).pos)
  let e := Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) q
  let E₁ := (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv.trans
    (lineGenericLocalEquiv k _ hI).toRingEquiv
  let E₂ := (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv.trans
    (lineGenericLocalEquiv k _ hq).toRingEquiv
  have hloc : (lineFunctionFieldMap k p).toRingHom.comp
      (lineGenericLocalEquiv k _ hI).toRingEquiv.toRingHom =
      (lineGenericLocalEquiv k _ hq).toRingEquiv.toRingHom.comp
        (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl) := by
    apply IsLocalization.ringHom_ext (q.asIdeal.comap f).primeCompl
    apply RingHom.ext
    intro a
    change lineFunctionFieldMap k p ((lineGenericLocalEquiv k _ hI)
      (algebraMap (Polynomial k) (Localization.AtPrime _) a)) =
      (lineGenericLocalEquiv k _ hq) (Localization.localRingHom
        (q.asIdeal.comap f) q.asIdeal f rfl
          (algebraMap (Polynomial k) (Localization.AtPrime _) a))
    rw [AlgEquiv.commutes, lineFunctionFieldMap_on_polynomial,
      Localization.localRingHom_to_map, AlgEquiv.commutes]
    rfl
  have hgp : g q = genericPoint (Spec (.of (Polynomial k))) :=
    map_genericPoint_eq_of_isDominant g
  let epoint := ((Spec (.of (Polynomial k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field ((Spec (.of (Polynomial k))).presheaf.stalk (g q)) :=
    (epoint.toMulEquiv.isField (Field.toIsField _)).toField
  letI := (g.stalkMap q).hom.toAlgebra
  haveI : Algebra.IsSeparable ((Spec (.of (Polynomial k))).presheaf.stalk (g q))
      ((Spec (.of (Polynomial k))).presheaf.stalk q) := hsep
  apply lineFunctionFieldMap_not_isSeparable k p
  letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
  apply Algebra.IsSeparable.of_equiv_equiv
    (A₁ := (Spec (.of (Polynomial k))).presheaf.stalk (g q))
    (B₁ := (Spec (.of (Polynomial k))).presheaf.stalk q) E₁ E₂
  have hw : (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).comp
      (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv.toRingHom =
      (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv.toRingHom.comp
        (g.stalkMap q).hom := congrArg CommRingCat.Hom.hom e.hom.w
  change (lineFunctionFieldMap k p).toRingHom.comp
      ((lineGenericLocalEquiv k _ hI).toRingEquiv.toRingHom.comp
        (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv.toRingHom) =
    (lineGenericLocalEquiv k _ hq).toRingEquiv.toRingHom.comp
      ((Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv.toRingHom.comp
        (g.stalkMap q).hom)
  rw [← RingHom.comp_assoc, hloc, RingHom.comp_assoc, hw]

#print axioms lineSchemeMap_not_isGenericallySeparable

end Pcf.Examples.PaperP.FrobeniusLine
