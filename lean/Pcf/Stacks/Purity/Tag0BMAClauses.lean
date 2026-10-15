/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.OuterInduction
public import Pcf.Stacks.Purity.Tag0BM9Equivalence
public import Pcf.Stacks.Purity.Tag0BMBAssembly
public import Mathlib.RingTheory.Regular.Flat

/-!
# The two clauses of Stacks Tag `0BMA`

This file proves the categorical implication from clause (1) of Tag `0BMA` to its corrected
affine clause (2), using the actual equivalence of Tag `0BM9`.

The section algebra of the finite etale extension need not first be shown normal. Its flatness
transports a length-two regular sequence from the base, and the same Hartogs calculation used in
Tag `0BM9` recovers it directly from the puncture.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing RingTheory.Sequence

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- The section algebra of a finite etale cover of an affine spectrum is finite etale over the
base ring.  The algebra structure is the canonical one induced by the structure morphism and
the `Gamma(Spec R) = R` isomorphism. -/
theorem finiteEtaleCover_sections_finite_etale
    (R : Type u) [CommRing R]
    (Y : FiniteEtaleCover (Spec (.of R))) :
    Module.Finite R
        ((algΓ (.of R)).obj ((FiniteEtaleCover.forget _).obj Y)).unop ∧
      Algebra.Etale R
        ((algΓ (.of R)).obj ((FiniteEtaleCover.forget _).obj Y)).unop := by
  letI : IsAffine ((Functor.fromPUnit (Spec (.of R))).obj Y.right) := by
    change IsAffine (Spec (.of R))
    infer_instance
  letI : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  letI : IsAffine ((Functor.id Scheme).obj Y.left) := by
    change IsAffine Y.left
    infer_instance
  have hfiniteTop : Y.hom.appTop.hom.Finite := Y.hom.finite_appTop
  have hetaleTop : Y.hom.appTop.hom.Etale :=
    HasRingHomProperty.appTop (@Etale) Y.hom Y.prop.2
  have hbaseFinite : (Scheme.ΓSpecIso (.of R)).inv.hom.Finite :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.finite
  have hbaseEtale : (Scheme.ΓSpecIso (.of R)).inv.hom.Etale :=
    RingHom.Etale.of_bijective
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  have hfinite :
      (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom).Finite :=
    hfiniteTop.comp hbaseFinite
  have hetale :
      (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom).Etale :=
    RingHom.Etale.stableUnderComposition _ _ hbaseEtale hetaleTop
  constructor
  · change (((Scheme.ΓSpecIso (.of R)).inv ≫ Y.hom.appTop).hom).Finite
    exact hfinite
  · exact hetale.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The relative `Gamma`-`Spec` unit is an isomorphism on a finite etale cover of an affine
base, since the source of the cover is affine. -/
theorem finiteEtaleCover_algGamma_unit_isIso
    (R : Type u) [CommRing R]
    (Y : FiniteEtaleCover (Spec (.of R))) :
    IsIso ((algΓAlgSpecAdjunction (.of R)).unit.app
      ((FiniteEtaleCover.forget _).obj Y)) := by
  letI : IsAffine ((Functor.fromPUnit (Spec (.of R))).obj Y.right) := by
    change IsAffine (Spec (.of R))
    infer_instance
  letI : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  let A : (CommAlgCat R)ᵒᵖ := Opposite.op <|
    (commAlgCatEquivUnder (.of R)).inverse.obj <|
      .mk (Spec.fullyFaithful.preimage
        (Y.left.isoSpec.inv ≫ Y.hom)).unop
  let e : (FiniteEtaleCover.forget _).obj Y ≅
      (algSpec (.of R)).obj A :=
    Over.isoMk Y.left.isoSpec (by
      simp only [algSpec_obj_hom]
      dsimp only [A, commAlgCatEquivUnder]
      change Y.left.isoSpec.hom ≫
          Spec.map (Spec.fullyFaithful.preimage
            (Y.left.isoSpec.inv ≫ Y.hom)).unop = Y.hom
      rw [Spec.map_preimage_unop]
      simp)
  letI : (algSpec (.of R)).Full := algSpec.fullyFaithful.full
  letI : (algSpec (.of R)).Faithful := algSpec.fullyFaithful.faithful
  exact (algΓAlgSpecAdjunction (.of R)).isIso_unit_app_of_iso e

/-- A form of the punctured `Gamma`-`Spec` counit criterion which exposes exactly the
ring-theoretic Hartogs input. -/
theorem puncturedSectionsSpecAdjunction_counit_isIso_of_bijective
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (A : (CommAlgCat R)ᵒᵖ)
    (hcomp : Function.Bijective
      (((Scheme.ΓSpecIso (.of A.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj A).hom
          (puncturedSpectrum R).ι).appTop).hom)) :
    IsIso ((puncturedSectionsSpecAdjunction R).counit.app A) := by
  let p := ((algSpec (.of R)).obj A).hom
  let i := (puncturedSpectrum R).ι
  let j := pullback.fst p i
  haveI : IsIso
      ((Scheme.ΓSpecIso (.of A.unop)).inv ≫
        (pullback.fst ((algSpec (.of R)).obj A).hom
          (puncturedSpectrum R).ι).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hcomp
  haveI : IsIso
      (pullback.fst ((algSpec (.of R)).obj A).hom
        (puncturedSpectrum R).ι).appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of A.unop)).inv _
  haveI : IsIso j.appTop := by
    change IsIso
      (pullback.fst ((algSpec (.of R)).obj A).hom
        (puncturedSpectrum R).ι).appTop
    infer_instance
  let c := (Over.mapPullbackAdj i).counit.app ((algSpec (.of R)).obj A)
  haveI : IsIso c.left.appTop := by
    change IsIso j.appTop
    infer_instance
  haveI : IsIso ((Scheme.Γ.rightOp).map c.left) := by
    change IsIso c.left.appTop.op
    infer_instance
  haveI : IsIso ((Over.post Scheme.Γ.rightOp).map c) := by
    let m := (Over.post Scheme.Γ.rightOp).map c
    haveI : IsIso m.left := by
      change IsIso ((Scheme.Γ.rightOp).map c.left)
      infer_instance
    let e := Over.isoMk (asIso m.left) m.w
    have he : e.hom = m := by
      ext
      rfl
    change IsIso m
    rw [← he]
    infer_instance
  haveI : IsIso ((algΓ (.of R)).map c) := by
    unfold algΓ
    dsimp only [Functor.comp_map]
    infer_instance
  simp only [puncturedSectionsSpecAdjunction, Adjunction.comp_counit_app]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A finite etale algebra over the base is recovered from regular functions on the open image
of its restriction to the punctured spectrum. Flatness, rather than normality of the algebra,
transports the depth-two regular sequence needed in the Hartogs calculation. -/
theorem finiteEtaleAlgebra_openSections_bijective
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
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
  letI : Algebra.Etale R B := inferInstance
  obtain ⟨x, y, hxm, hym, hreg⟩ :=
    exists_regularSequence_two_of_isIntegrallyClosed R hdim
  have hweak : IsWeaklyRegular B [x, y] := by
    rw [← isWeaklyRegular_map_algebraMap_iff (S := B) (M := B) [x, y]]
    exact hreg.toIsWeaklyRegular.of_flat
  obtain ⟨hx, htail⟩ := (isWeaklyRegular_cons_iff B x [y]).mp hweak
  have hy : IsSMulRegular (QuotSMulTop x B) y :=
    ((isWeaklyRegular_cons_iff (QuotSMulTop x B) y []).mp htail).1
  have hregYX : IsRegular R [y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x y []).symm
  have hweakYX : IsWeaklyRegular B [y, x] := by
    rw [← isWeaklyRegular_map_algebraMap_iff (S := B) (M := B) [y, x]]
    exact hregYX.toIsWeaklyRegular.of_flat
  have hyB : IsSMulRegular B y :=
    ((isWeaklyRegular_cons_iff B y [x]).mp hweakYX).1
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
      haveI : IsFinite p := by
        change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        rw [IsFinite.SpecMap_iff]
        exact RingHom.finite_algebraMap.mpr inferInstance
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
          have hpFinite : IsFinite p := by
            change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B)))
            rw [IsFinite.SpecMap_iff]
            exact RingHom.finite_algebraMap.mpr inferInstance
          have hpEtale : Etale p := by
            change Etale (Spec.map (CommRingCat.ofHom (algebraMap R B)))
            exact HasRingHomProperty.Spec_iff.mpr
              (RingHom.etale_algebraMap.mpr inferInstance)
          let V : FiniteEtaleCover (puncturedSpectrumScheme R) :=
            MorphismProperty.Over.mk ⊤
              ((Over.pullback i).obj ((algSpec (.of R)).obj C)).hom (by
                constructor
                · let _ : IsFinite p := hpFinite
                  change IsFinite (pullback.snd p i)
                  infer_instance
                · let _ : Etale p := hpEtale
                  change Etale (pullback.snd p i)
                  infer_instance)
          let K := (Spec R).functionField
          let E := puncturedCoverGenericFiberAlgebra R hdim1 V
          letI : Algebra K E := inferInstance
          letI : Algebra R E := Algebra.compHom E (algebraMap R K)
          letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
          haveI : Module.IsTorsionFree K E := inferInstance
          haveI : Module.IsTorsionFree R K := inferInstance
          haveI : Module.IsTorsionFree R E :=
            Module.IsTorsionFree.trans (M := E) K
          let f : Γ(P, ⊤) →ₐ[R] E := puncturedCoverGenericFiber_sectionAlgHom R hdim1 V
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

/-- Hartogs recovery for a finite etale algebra, expressed on its actual pullback scheme over
the puncture. -/
theorem finiteEtaleAlgebra_pullbackSections_bijective
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
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
  have hW := finiteEtaleAlgebra_openSections_bijective R hdim C
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

/-- The punctured `Gamma`-`Spec` counit is an isomorphism on finite etale algebras. This is the
normality-free Hartogs input used to compare an extension supplied by clause (1) of Tag `0BMA`
with the algebra in clause (2). -/
theorem finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (C : (CommAlgCat R)ᵒᵖ)
    [Module.Finite R C.unop] [Algebra.Etale R C.unop] :
    IsIso ((puncturedSectionsSpecAdjunction R).counit.app C) :=
  puncturedSectionsSpecAdjunction_counit_isIso_of_bijective R C
    (finiteEtaleAlgebra_pullbackSections_bijective R hdim C)

/-- Clause (1) of Stacks Tag `0BMA` implies its corrected affine clause (2).

Given a finite etale extension of the punctured cover, the proof compares its finite etale
section algebra with the original finite normal algebra. The comparison uses Hartogs recovery
twice: the flat regular-sequence argument above for the finite etale algebra, and the Tag `0BM9`
recovery theorem for the original normal algebra. No normality assertion for finite etale
algebras is needed. -/
theorem finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R)
    (hpurity : PuncturedSpectrumPurity R) :
    FiniteNormalPuncturedEtalePurity R := by
  intro B hB
  let B' : FiniteNormalPuncturedEtaleAlgebra R := ⟨B, hB⟩
  let V := (finiteNormalAlgebraToPuncturedCover R).obj B'
  rcases hpurity with ⟨hpurity⟩
  obtain ⟨Y, ⟨eY⟩⟩ := hpurity V
  let Y0 : Over (Spec (.of R)) := (FiniteEtaleCover.forget _).obj Y
  let C : (CommAlgCat R)ᵒᵖ := (algΓ (.of R)).obj Y0
  have hC := finiteEtaleCover_sections_finite_etale R Y
  letI : Module.Finite R C.unop := hC.1
  letI : Algebra.Etale R C.unop := hC.2
  let unitY := (algΓAlgSpecAdjunction (.of R)).unit.app Y0
  letI : IsIso unitY := finiteEtaleCover_algGamma_unit_isIso R Y
  let eU := (Over.pullback (puncturedSpectrum R).ι).mapIso (asIso unitY)
  let eR := (Over.map (puncturedSpectrum R).ι).mapIso eU
  let eUnitΓ := (algΓ (.of R)).mapIso eR
  letI : IsIso ((puncturedSectionsSpecAdjunction (.of R)).counit.app C) :=
    finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
      (.of R) hdim C
  let eΓ := (puncturedFiniteEtaleGlobalSections R).mapIso eY
  let eB := (finiteNormalPuncturedEtaleAlgebraProperty R).ι.mapIso
    ((tag0BM9_finiteNormalAlgebraRecoveryIso (.of R) hdim).app B')
  let eCB : C ≅ B :=
    (eUnitΓ ≪≫ asIso ((puncturedSectionsSpecAdjunction (.of R)).counit.app C)).symm ≪≫
      eΓ ≪≫ eB
  let eA : C.unop ≃ₐ[R] B.unop := CommAlgCat.algEquivOfIso eCB.symm.unop
  exact Algebra.Etale.of_equiv eA

#print axioms finiteEtaleCover_sections_finite_etale
#print axioms finiteEtaleCover_algGamma_unit_isIso
#print axioms puncturedSectionsSpecAdjunction_counit_isIso_of_bijective
#print axioms finiteEtaleAlgebra_openSections_bijective
#print axioms finiteEtaleAlgebra_pullbackSections_bijective
#print axioms finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
#print axioms finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity

end Pcf.Stacks
