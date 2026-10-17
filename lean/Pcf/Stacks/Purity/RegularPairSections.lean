/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.FiniteNormalHartogs
public import Pcf.Stacks.Purity.Tag0BM9Equivalence

/-!
# Hartogs recovery for algebras étale over the punctured spectrum

Let `R` be a Noetherian local normal domain with punctured spectrum `U`, and let `C` be a finite
`R`-algebra which is étale over `U` and on which a base pair `x, y ∈ 𝔪` is regular (with `y`
also regular on `C`).  Then `C` is recovered from the regular functions on the preimage of `U`
in `Spec C`:

* `openSections_bijective_of_regularPair_of_puncturedEtale`: on the open image of the
  restriction of `Spec C` to `U`;
* `pullbackSections_bijective_of_regularPair_of_puncturedEtale`: on the pullback scheme itself.

These are the common Hartogs input of the clause (1) ⇒ (2) comparison for Stacks Tag `0BMA`
(`Tag0BMAClauses`, where `C` is finite étale and the pair comes from flatness) and of the
completion descent (`CompletionDescent`, where the pair comes from normality).
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing RingTheory.Sequence

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

set_option backward.isDefEq.respectTransparency false in
/-- Hartogs recovery for a finite algebra which is étale over the punctured spectrum and carries
a base regular pair, on the open image of its punctured restriction.

Only a base regular pair (given explicitly) and étaleness over the punctured spectrum are used;
`finiteEtaleAlgebra_openSections_bijective` is the case of a finite étale algebra. -/
theorem openSections_bijective_of_regularPair_of_puncturedEtale
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim1 : 1 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop]
    (x y : R) (hxm : x ∈ maximalIdeal R) (hym : y ∈ maximalIdeal R)
    (hx : IsSMulRegular C.unop x) (hyB : IsSMulRegular C.unop y)
    (hy : IsSMulRegular (QuotSMulTop x C.unop) y)
    (hetale : Etale (((Over.pullback (puncturedSpectrum R).ι).obj
      ((algSpec (.of R)).obj C)).hom)) :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of C.unop)).inv ≫
        (Spec (.of C.unop)).presheaf.map
          (homOfLE (show (pullback.fst ((algSpec (.of R)).obj C).hom
            (puncturedSpectrum R).ι).opensRange ≤ ⊤ from le_top)).op).hom) := by
  let B : CommRingCat := .of C.unop
  let p : Spec B ⟶ Spec (.of R) := ((algSpec (.of R)).obj C).hom
  let i := (puncturedSpectrum R).ι
  let P := pullback p i
  let j : pullback p i ⟶ Spec B := pullback.fst p i
  let W : (Spec B).Opens := j.opensRange
  letI : Algebra R B := inferInstance
  letI : Module.Finite R B := inferInstance
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
    have hpFinite : IsFinite p := by
      change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    have hWcompact : IsCompact W.1 := by
      rw [hW]
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
          let q := pullback.snd p i
          letI : Algebra R Γ(P, ⊤) :=
            (((Scheme.ΓSpecIso (.of R)).inv ≫ (q ≫ i).appTop).hom).toAlgebra
          let V : FiniteEtaleCover (puncturedSpectrumScheme R) :=
            MorphismProperty.Over.mk ⊤
              ((Over.pullback i).obj ((algSpec (.of R)).obj C)).hom (by
                constructor
                · let _ : IsFinite p := hpFinite
                  change IsFinite (pullback.snd p i)
                  infer_instance
                · exact hetale)
          let K := (Spec R).functionField
          let E := puncturedCoverGenericFiberAlgebra R hdim1 V
          letI : Algebra K E := inferInstance
          letI : Algebra R E := Algebra.compHom E (algebraMap R K)
          letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
          haveI : Module.IsTorsionFree K E := inferInstance
          haveI : Module.IsTorsionFree R K := inferInstance
          haveI : Module.IsTorsionFree R E :=
            Module.IsTorsionFree.trans (M := E) K
          let f : Γ(P, ⊤) →ₐ[R] E := puncturedCoverGenericFiberSectionAlgHom R hdim1 V
          letI : Module.IsTorsionFree R Γ(P, ⊤) :=
            Function.Injective.moduleIsTorsionFree f
              (puncturedCoverGenericFiber_sectionMap_injective R hdim1 V)
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
        (fun z : Γ(Spec B, PrimeSpectrum.basicOpen xb) ↦
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

/-- The form of `openSections_bijective_of_regularPair_of_puncturedEtale` on the actual pullback
scheme over the puncture. -/
theorem pullbackSections_bijective_of_regularPair_of_puncturedEtale
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim1 : 1 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop]
    (x y : R) (hxm : x ∈ maximalIdeal R) (hym : y ∈ maximalIdeal R)
    (hx : IsSMulRegular C.unop x) (hyB : IsSMulRegular C.unop y)
    (hy : IsSMulRegular (QuotSMulTop x C.unop) y)
    (hetale : Etale (((Over.pullback (puncturedSpectrum R).ι).obj
      ((algSpec (.of R)).obj C)).hom)) :
    Function.Bijective
      (((Scheme.ΓSpecIso (.of C.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj C).hom
          (puncturedSpectrum R).ι).appTop).hom) := by
  let B : CommRingCat := .of C.unop
  let p : Spec B ⟶ Spec (.of R) := ((algSpec (.of R)).obj C).hom
  let i := (puncturedSpectrum R).ι
  let P := pullback p i
  let j : P ⟶ Spec B := pullback.fst p i
  let W : (Spec B).Opens := j.opensRange
  change Function.Bijective (((Scheme.ΓSpecIso B).inv ≫ j.appTop).hom)
  let e := IsOpenImmersion.ΓIsoTop j
  have hW := openSections_bijective_of_regularPair_of_puncturedEtale R hdim1 C x y hxm hym
    hx hyB hy hetale
  letI : Algebra B Γ(Spec B, W) :=
    (((Scheme.ΓSpecIso B).inv ≫
      (Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op).hom).toAlgebra
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
    have happ : j.appLE ⊤ ⊤ (by simp) = j.appTop := by
      simpa only [Scheme.Hom.preimage_top] using
        (j.appLE_eq_app (U := (⊤ : (Spec B).Opens)))
    change (j.appLE ⊤ ⊤ _).hom _ = j.appTop.hom _
    rw [happ]
  have heBij : Function.Bijective e.inv.hom :=
    (ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance
  have hcomp := heBij.comp hW
  change Function.Bijective
    (e.inv.hom ∘ (((Scheme.ΓSpecIso B).inv ≫
      (Spec B).presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op).hom)) at hcomp
  have hefun : ((Scheme.ΓSpecIso B).inv ≫ j.appTop).hom =
      e.inv.hom ∘ (((Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.map
          (homOfLE (show W ≤ ⊤ from le_top)).op).hom) := by
    funext b
    exact (he b).symm
  rw [hefun]
  exact hcomp

#print axioms openSections_bijective_of_regularPair_of_puncturedEtale
#print axioms pullbackSections_bijective_of_regularPair_of_puncturedEtale

end Pcf.Stacks
