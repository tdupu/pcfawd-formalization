/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.GenericCoverFiber
import Pcf.Stacks.Purity.FiniteNormalAlgebra
import Pcf.Stacks.Purity.FiniteNormalHartogs

/-!
# Hartogs recovery for the algebras in Stacks Tag `0BM9`

For a finite torsion-free Stacks-normal algebra over a normal Noetherian local domain of
dimension at least two, restriction to the punctured spectrum does not create new global
functions.  This is the algebra-recovery half of the categorical equivalence in Tag `0BM9`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate ring of a finite torsion-free Stacks-normal algebra is recovered from the
regular functions on its restriction to the punctured spectrum. -/
theorem finiteNormalAlgebra_openSections_bijective (hdim : 2 ≤ ringKrullDim R)
    (A : FiniteNormalPuncturedEtaleAlgebra R) :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of A.obj.unop)).inv ≫
        (Spec (.of A.obj.unop)).presheaf.map
          (homOfLE (show (pullback.fst ((algSpec (.of R)).obj A.obj).hom
            (puncturedSpectrum R).ι).opensRange ≤ ⊤ from le_top)).op).hom) := by
  let B : CommRingCat := .of A.obj.unop
  let p : Spec B ⟶ Spec (.of R) := ((algSpec (.of R)).obj A.obj).hom
  let i := (puncturedSpectrum R).ι
  let P := pullback p i
  let j : pullback p i ⟶ Spec B := pullback.fst p i
  let W : (Spec B).Opens := j.opensRange
  letI : Algebra R B := inferInstance
  letI : Module.Finite R B := A.property.1
  letI : Module.IsTorsionFree R B := A.property.2.1
  have hnormal : IsStacksNormalRing B :=
    FiniteNormalPuncturedEtaleAlgebra.isStacksNormalRing A
  obtain ⟨x, y, hxm, hym, hx, hyB, hy⟩ :=
    exists_module_permutable_regular_pair_of_finite_stacksNormal hnormal hdim
  have hW : W = p ⁻¹ᵁ puncturedSpectrum R := by
    dsimp only [W, j]
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
  have hDx : PrimeSpectrum.basicOpen (algebraMap R B x) ≤ W := by
    rw [hW]
    intro q hq
    change p.base q ∈ puncturedSpectrum R
    rw [mem_puncturedSpectrum_iff]
    intro heq
    have hxnot : algebraMap R B x ∉ q.asIdeal :=
      (PrimeSpectrum.mem_basicOpen (algebraMap R B x) q).mp hq
    apply hxnot
    change x ∈ (p.base q).asIdeal
    rw [heq]
    exact hxm
  have hDy : PrimeSpectrum.basicOpen (algebraMap R B y) ≤ W := by
    rw [hW]
    intro q hq
    change p.base q ∈ puncturedSpectrum R
    rw [mem_puncturedSpectrum_iff]
    intro heq
    have hynot : algebraMap R B y ∉ q.asIdeal :=
      (PrimeSpectrum.mem_basicOpen (algebraMap R B y) q).mp hq
    apply hynot
    change y ∈ (p.base q).asIdeal
    rw [heq]
    exact hym
  have hinj : Function.Injective
      ((Spec B).presheaf.map (homOfLE hDx).op).hom := by
    letI : Algebra B Γ(Spec B, W) :=
      (((Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op).hom).toAlgebra
    let xb : B := algebraMap R B x
    let r : Γ(Spec B, W) := algebraMap B Γ(Spec B, W) xb
    have hWcompact : IsCompact W.1 := by
      rw [hW]
      haveI : IsFinite p := FiniteNormalPuncturedEtaleAlgebra.isFinite_algSpec A
      exact p.isCompact_preimage (isCompact_puncturedSpectrum R)
    have hD : (Spec B).basicOpen r = PrimeSpectrum.basicOpen xb := by
      dsimp only [r]
      change (Spec B).basicOpen ((Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op ((Scheme.ΓSpecIso B).inv xb)) = _
      rw [Scheme.basicOpen_res, basicOpen_eq_of_affine,
        inf_eq_right.mpr hDx]
    have hr : IsRegular r := by
      let e := IsOpenImmersion.ΓIsoTop j
      have he (b : B) : e.inv (algebraMap B Γ(Spec B, W) b) =
          j.appTop ((Scheme.ΓSpecIso B).inv b) := by
        have etop : (⊤ : P.Opens) ≤ j ⁻¹ᵁ W := by
          change (⊤ : P.Opens) ≤ j ⁻¹ᵁ j.opensRange
          rw [← j.image_top_eq_opensRange, j.preimage_image_eq]
        have hcomp : (Spec B).presheaf.map
              (eqToHom j.image_top_eq_opensRange).op ≫
              (j.appIso ⊤).hom =
            j.appLE W ⊤ etop := by
          rw [j.appIso_hom']
          exact j.map_appLE' etop j.image_top_eq_opensRange
        simp only [e, IsOpenImmersion.ΓIsoTop, Iso.trans_inv,
          Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, eqToHom_op,
          Iso.symm_inv]
        change ((Spec B).presheaf.map
              (eqToHom j.image_top_eq_opensRange).op ≫
            (j.appIso ⊤).hom).hom
            (((Scheme.ΓSpecIso B).inv ≫
              (Spec B).presheaf.map
                (homOfLE (show W ≤ ⊤ from le_top)).op).hom b) = _
        rw [← CommRingCat.comp_apply, hcomp]
        change ((Spec B).presheaf.map
            (homOfLE (show W ≤ ⊤ from le_top)).op ≫
          j.appLE W ⊤ etop).hom ((Scheme.ΓSpecIso B).inv b) = _
        rw [j.map_appLE]
        simp [Scheme.Hom.appLE]
      cases subsingleton_or_nontrivial B with
      | inl hB =>
          letI : Subsingleton B := hB
          letI : IsEmpty (Spec B) := by
            change IsEmpty (PrimeSpectrum B)
            exact PrimeSpectrum.isEmpty_iff_subsingleton.mpr hB
          letI : Subsingleton Γ(Spec B, W) := inferInstance
          exact ⟨Function.injective_of_subsingleton _,
            Function.injective_of_subsingleton _⟩
      | inr hB =>
          letI : Nontrivial B := hB
          have hx0 : x ≠ 0 := by
            intro hx0
            have h10 : (1 : B) = 0 := hx (by simp [hx0])
            exact one_ne_zero h10
          have hxR : IsRegular x := IsRegular.of_ne_zero hx0
          have hdim1 : 1 ≤ ringKrullDim R := le_trans (by norm_num) hdim
          let q := pullback.snd p i
          letI : Algebra R Γ(P, ⊤) :=
            (((Scheme.ΓSpecIso (.of R)).inv ≫ (q ≫ i).appTop).hom).toAlgebra
          let V := (finiteNormalAlgebraToPuncturedCover R).obj A
          let K := (Spec R).functionField
          let E := puncturedCoverGenericFiberAlgebra R hdim1 V
          letI : Algebra K E := inferInstance
          letI : Algebra R E := Algebra.compHom E (algebraMap R K)
          letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
          haveI : Module.IsTorsionFree K E := inferInstance
          haveI : Module.IsTorsionFree R K := inferInstance
          haveI : Module.IsTorsionFree R E :=
            Module.IsTorsionFree.trans (M := E) K
          let f := puncturedCoverGenericFiber_sectionAlgHom R hdim1 V
          letI : Module.IsTorsionFree R Γ(P, ⊤) :=
            Function.Injective.moduleIsTorsionFree f
              (puncturedCoverGenericFiber_sectionAlgHom_injective R hdim1 V)
              (fun a b ↦ by simp)
          have hxP : IsSMulRegular Γ(P, ⊤) x := by
            exact hxR.isSMulRegular
          have hp : CommRingCat.ofHom (algebraMap R B) ≫
                (Scheme.ΓSpecIso B).inv =
              (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop := by
            simpa only [p, B, algSpec_obj_hom] using Scheme.ΓSpecIso_inv_naturality
              (CommRingCat.ofHom (algebraMap R B))
          have hpx : (Scheme.ΓSpecIso B).inv (algebraMap R B x) =
              p.appTop ((Scheme.ΓSpecIso (.of R)).inv x) := by
            exact congrArg (fun q : R ⟶ Γ(Spec B, ⊤) ↦ q.hom x) hp
          have hjp : j ≫ p = q ≫ i := by
            exact pullback.condition
          have her : e.inv r = algebraMap R Γ(P, ⊤) x := by
            rw [he, hpx]
            rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hjp,
              Scheme.Hom.comp_appTop]
            rfl
          have heinj : Function.Injective e.inv.hom :=
            ((ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance).injective
          constructor
          · intro a b hab
            apply heinj
            have hab' := congrArg e.inv.hom hab
            rw [map_mul, map_mul, her] at hab'
            apply hxP
            simpa only [Algebra.smul_def] using hab'
          · intro a b hab
            apply heinj
            have hab' := congrArg e.inv.hom hab
            rw [map_mul, map_mul, her] at hab'
            have hab'' : algebraMap R Γ(P, ⊤) x * e.inv a =
                algebraMap R Γ(P, ⊤) x * e.inv b := by
              rw [mul_comm (algebraMap R Γ(P, ⊤) x) (e.inv a),
                mul_comm (algebraMap R Γ(P, ⊤) x) (e.inv b)]
              exact hab'
            apply hxP
            simpa only [Algebra.smul_def] using hab''
    intro s t hst
    have hz : (Spec B).presheaf.map (homOfLE hDx).op (s - t) = 0 := by
      rw [map_sub, hst, sub_self]
    have hz' : (s - t) |_ ((Spec B).basicOpen r) = 0 := by
      have hzcast := congrArg
        (fun z : Γ(Spec B, PrimeSpectrum.basicOpen xb) =>
          (Spec B).presheaf.map (eqToHom hD).op z) hz
      rw [map_zero, ← (Spec B).presheaf.map_comp_apply,
        ← op_comp, eqToHom_comp_homOfLE] at hzcast
      exact hzcast
    obtain ⟨n, hn⟩ :=
      exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        (Spec B) hWcompact (s - t) r hz'
    apply sub_eq_zero.mp
    apply (hr.pow n).1
    change r ^ n * (s - t) = r ^ n * 0
    simpa only [mul_zero] using hn
  exact openSections_algebraMap_bijective_of_module_regularPair
    hx hyB hy hDx hDy hinj

end Pcf.Stacks
