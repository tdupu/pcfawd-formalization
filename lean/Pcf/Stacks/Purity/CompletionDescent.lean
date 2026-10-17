/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.Tag0BMAClauses
public import Pcf.Stacks.Purity.FiniteModuleHartogs
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Regular.Flat
public import Pcf.Stacks.Purity.Completion
public import Pcf.Bounding.RegularLocalDomain
public import Pcf.Stacks.Common.RegularNormal

/-!
# Descent of punctured-spectrum purity along a faithfully flat local extension

Let `A → A'` be a faithfully flat map of Noetherian local normal domains with
`m_A A' = m_{A'}`; the case of interest is the `m`-adic completion `A' = A^∧` of a regular
local ring `A` of dimension at least two.  This file proves that clause (1) of Stacks Tag
`0BMA` for `A'` (every finite étale cover of the punctured spectrum of `A'` extends) implies the
corrected affine clause (2) for `A` (`FiniteNormalPuncturedEtalePurity A`).

## Proof

Let `B` be a finite torsion-free Stacks-normal `A`-algebra which is étale over the punctured
spectrum `U` of `A`, and let `B' = A' ⊗[A] B`.

1. The preimage of `U` in `Spec A'` is the punctured spectrum `U'` of `A'`, and `Spec B'` is the
   fibre product `Spec B ×_{Spec A} Spec A'`.  Pasting pullback squares shows that the restriction
   of `Spec B'` to `U'` is a base change of the restriction of `Spec B` to `U`, hence it is a
   finite étale cover `V'` of `U'`.
2. A base regular pair `x, y ∈ m_A` on `B`
   (`exists_module_permutable_regular_pair_of_finite_stacksNormal`) stays regular on `B'` by
   flatness.  The Hartogs lemma for module-regular pairs then recovers `B'` from its sections
   over `U'`.
3. Purity for `A'` extends `V'` to a finite étale `Y'`.  Comparing sections over `U'` exactly as
   in `finiteNormalPuncturedEtalePurity_of_puncturedSpectrumPurity` identifies `Γ(Y')` with `B'`,
   so `B'` is étale over `A'`.
4. Étaleness descends along the faithfully flat map `A → A'`
   (`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`, the ring form of Stacks `02VN`).

## Divergence from Stacks

Stacks deduces the corresponding statement from Tag `0BLL` (Lemma 58.20.4), whose proof uses
Tag `0BLH` (finite modules over the punctured completion) and, in Tag `0BLS`, descent of the
extension `Y'` itself.  This file proves only what the `0BMA` induction needs: purity for the
completion gives clause (2) for `A`.  It avoids `0BLH` by using normality of `B` (a depth-two
regular pair) together with the Hartogs lemma and fpqc descent of étaleness.  No Stacks tag is
attached to the declarations below, since none of them is the statement of `0BLL`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing RingTheory.Sequence TensorProduct

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

set_option backward.isDefEq.respectTransparency false in
/-- Hartogs recovery for a finite algebra which is étale over the punctured spectrum and carries
a base regular pair, on the open image of its punctured restriction.

This is `finiteEtaleAlgebra_openSections_bijective` with étaleness of the whole algebra replaced
by its two consequences used in the proof: a base regular pair (given explicitly) and étaleness
over the punctured spectrum. -/
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

/-- Under `m_A A' = m_{A'}`, the preimage of the punctured spectrum of `A` in `Spec A'` is the
punctured spectrum of `A'`. -/
theorem preimage_puncturedSpectrum_eq_of_map_maximalIdeal_eq
    (A A' : Type u) [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    [Algebra A A']
    (hmax : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A') :
    Spec.map (CommRingCat.ofHom (algebraMap A A')) ⁻¹ᵁ puncturedSpectrum A =
      puncturedSpectrum A' := by
  ext q
  let q0 : PrimeSpectrum A' := q
  change PrimeSpectrum.comap (algebraMap A A') q0 ∈ puncturedSpectrum A ↔
    q0 ∈ puncturedSpectrum A'
  rw [mem_puncturedSpectrum_iff A, mem_puncturedSpectrum_iff A']
  apply not_congr
  constructor
  · intro h
    apply PrimeSpectrum.ext
    apply le_antisymm (le_maximalIdeal q.isPrime.ne_top)
    rw [← hmax, Ideal.map_le_iff_le_comap]
    have h' := congrArg PrimeSpectrum.asIdeal h
    change q.asIdeal.comap (algebraMap A A') = maximalIdeal A at h'
    rw [h']
  · rintro rfl
    apply PrimeSpectrum.ext
    change (maximalIdeal A').comap (algebraMap A A') = maximalIdeal A
    symm
    apply (maximalIdeal.isMaximal A).eq_of_le
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [← Ideal.map_le_iff_le_comap, hmax]

/-- The restriction to the punctured spectrum of `A'` of the spectrum of `A' ⊗[A] B` is étale
when the restriction of `Spec B` to the punctured spectrum of `A` is étale.  It is a base change
of the latter, by pasting pullback squares. -/
theorem puncturedEtale_tensorProduct_of_map_maximalIdeal_eq
    (A A' : Type u) [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
    [Algebra A A']
    (hmax : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A')
    (B : (CommAlgCat A)ᵒᵖ)
    (hB : Etale (((Over.pullback (puncturedSpectrum A).ι).obj
      ((algSpec (.of A)).obj B)).hom)) :
    Etale (((Over.pullback (puncturedSpectrum A').ι).obj
      ((algSpec (.of A')).obj (Opposite.op (CommAlgCat.of A' (A' ⊗[A] B.unop))))).hom) := by
  let g : Spec (.of A') ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let p : Spec (.of B.unop) ⟶ Spec (.of A) := ((algSpec (.of A)).obj B).hom
  let p' : Spec (.of (A' ⊗[A] B.unop)) ⟶ Spec (.of A') :=
    Spec.map (CommRingCat.ofHom (S := A' ⊗[A] B.unop)
      Algebra.TensorProduct.includeLeftRingHom)
  let h : Spec (.of (A' ⊗[A] B.unop)) ⟶ Spec (.of B.unop) :=
    Spec.map (CommRingCat.ofHom (S := A' ⊗[A] B.unop)
      Algebra.TensorProduct.includeRight.toRingHom)
  let U := puncturedSpectrum A
  change Etale (pullback.snd p' (puncturedSpectrum A').ι)
  change Etale (pullback.snd p U.ι) at hB
  rw [← preimage_puncturedSpectrum_eq_of_map_maximalIdeal_eq A A' hmax]
  let U'' := g ⁻¹ᵁ U
  have hsq : IsPullback h p' p g := by
    have := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct A A' B.unop)
    exact this.flip
  let gU : (U'' : Scheme) ⟶ U := g ∣_ U
  have hgU : gU ≫ U.ι = U''.ι ≫ g := (isPullback_morphismRestrict g U).w
  let q' := pullback.snd p' U''.ι
  let j' := pullback.fst p' U''.ι
  let q := pullback.snd p U.ι
  let j := pullback.fst p U.ι
  have hrect : IsPullback (j' ≫ h) q' p (U''.ι ≫ g) :=
    (IsPullback.of_hasPullback p' U''.ι).paste_horiz hsq
  let k : pullback p' U''.ι ⟶ pullback p U.ι :=
    pullback.lift (j' ≫ h) (q' ≫ gU) (by
      calc (j' ≫ h) ≫ p = j' ≫ p' ≫ g := by rw [Category.assoc, hsq.w]
        _ = (j' ≫ p') ≫ g := by rw [Category.assoc]
        _ = (q' ≫ U''.ι) ≫ g := by rw [pullback.condition]
        _ = (q' ≫ gU) ≫ U.ι := by simp only [Category.assoc, hgU])
  have hkj : k ≫ j = j' ≫ h := pullback.lift_fst _ _ _
  have hkq : k ≫ q = q' ≫ gU := pullback.lift_snd _ _ _
  have hrect' : IsPullback (k ≫ j) q' p (gU ≫ U.ι) := by
    rw [hkj, hgU]
    exact hrect
  have hsmall : IsPullback k q' q gU :=
    IsPullback.of_right hrect' hkq (IsPullback.of_hasPullback p U.ι)
  exact MorphismProperty.of_isPullback hsmall hB

/-- **Completion descent for clause (2) of Stacks Tag `0BMA`.**

Let `A → A'` be a faithfully flat map of Noetherian local normal domains with
`m_A A' = m_{A'}` (for instance `A' = A^∧` for regular local `A`), and let `dim A ≥ 2`. If every
finite étale cover of the punctured spectrum of `A'` extends over `Spec A'` (clause (1) of
`0BMA` for `A'`), then every finite torsion-free Stacks-normal `A`-algebra which is étale over
the punctured spectrum of `A` is étale (clause (2) of `0BMA` for `A`).

Proof route diverges from Stacks: Stacks uses Tag `0BLL` (via `0BLH`); here the base change
`A' ⊗[A] B` is recovered from its punctured sections by the regular-pair Hartogs lemma, compared
with the extension supplied by purity for `A'`, and étaleness descends along `A → A'`
(the ring form of Tag `02VN`). -/
theorem finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity
    (A A' : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    [Algebra A A'] [Module.FaithfullyFlat A A']
    (hmax : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A')
    (hdim : 2 ≤ ringKrullDim A) (hdim' : 2 ≤ ringKrullDim A')
    (hpurity : PuncturedSpectrumPurity A') :
    FiniteNormalPuncturedEtalePurity A := by
  intro B hB
  obtain ⟨hfin, htf, hnormal, hetale⟩ := hB
  letI : Module.Finite A B.unop := hfin
  letI : Module.IsTorsionFree A B.unop := htf
  obtain ⟨x, y, hxm, hym, hx, hyB, hy⟩ :=
    exists_module_permutable_regular_pair_of_finite_stacksNormal
      (R := A) (B := B.unop) hnormal hdim
  -- The base change `B' = A' ⊗[A] B`.
  let B'c : CommAlgCat A' := CommAlgCat.of A' (A' ⊗[A] B.unop)
  let B' : (CommAlgCat (CommRingCat.of A'))ᵒᵖ := Opposite.op B'c
  letI : Module.Finite A' B'.unop := by
    change Module.Finite A' (A' ⊗[A] B.unop)
    infer_instance
  -- Regularity of the image of the pair on `B'`.
  have hbc : IsBaseChange A' (TensorProduct.mk A A' B.unop 1) :=
    TensorProduct.isBaseChange A B.unop A'
  have hxy : IsWeaklyRegular (A' ⊗[A] B.unop)
      ([x, y].map (algebraMap A A')) := by
    apply IsWeaklyRegular.of_flat_of_isBaseChange hbc
    rw [isWeaklyRegular_cons_iff]
    refine ⟨hx, ?_⟩
    rw [isWeaklyRegular_cons_iff]
    exact ⟨hy, IsWeaklyRegular.nil _ _⟩
  have hyy : IsWeaklyRegular (A' ⊗[A] B.unop) ([y].map (algebraMap A A')) := by
    apply IsWeaklyRegular.of_flat_of_isBaseChange hbc
    rw [isWeaklyRegular_cons_iff]
    exact ⟨hyB, IsWeaklyRegular.nil _ _⟩
  simp only [List.map_cons, List.map_nil, isWeaklyRegular_cons_iff] at hxy hyy
  have hxm' : algebraMap A A' x ∈ maximalIdeal A' := by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hxm
  have hym' : algebraMap A A' y ∈ maximalIdeal A' := by
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hym
  -- Étaleness over the punctured spectrum of `A'`.
  have hetale' := puncturedEtale_tensorProduct_of_map_maximalIdeal_eq A A' hmax B hetale
  -- Hartogs recovery of `B'`.
  have hbij := pullbackSections_bijective_of_regularPair_of_puncturedEtale (.of A')
    (le_trans (by norm_num) hdim')
    B' (algebraMap A A' x) (algebraMap A A' y) hxm' hym' hxy.1 hyy.1 hxy.2.1 hetale'
  have hisoB : IsIso ((puncturedSectionsSpecAdjunction (.of A')).counit.app B') :=
    puncturedSectionsSpecAdjunction_counit_isIso_of_bijective (.of A') B' hbij
  -- The punctured cover `V'` and its extension.
  have hpFinite : IsFinite ((algSpec (.of A')).obj B').hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A' B'.unop)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let V' : FiniteEtaleCover (puncturedSpectrumScheme A') :=
    MorphismProperty.Over.mk ⊤
      ((Over.pullback (puncturedSpectrum A').ι).obj ((algSpec (.of A')).obj B')).hom (by
        constructor
        · change IsFinite (pullback.snd ((algSpec (.of A')).obj B').hom
            (puncturedSpectrum A').ι)
          infer_instance
        · exact hetale')
  rcases hpurity with ⟨hpurity⟩
  obtain ⟨Y, ⟨eY⟩⟩ := hpurity V'
  let Y0 : Over (Spec (.of A')) := (FiniteEtaleCover.forget _).obj Y
  let C : (CommAlgCat A')ᵒᵖ := (algΓ (.of A')).obj Y0
  have hC := finiteEtaleCover_sections_finite_etale A' Y
  letI : Module.Finite A' C.unop := hC.1
  letI : Algebra.Etale A' C.unop := hC.2
  let unitY := (algΓAlgSpecAdjunction (.of A')).unit.app Y0
  letI : IsIso unitY := finiteEtaleCover_algGamma_unit_isIso A' Y
  let eU := (Over.pullback (puncturedSpectrum A').ι).mapIso (asIso unitY)
  let eR := (Over.map (puncturedSpectrum A').ι).mapIso eU
  let eUnitΓ := (algΓ (.of A')).mapIso eR
  letI : IsIso ((puncturedSectionsSpecAdjunction (.of A')).counit.app C) :=
    finiteEtaleAlgebra_puncturedSectionsSpecAdjunction_counit_isIso
      (.of A') hdim' C
  let eΓ := (puncturedFiniteEtaleGlobalSections A').mapIso eY
  let eB : (puncturedFiniteEtaleGlobalSections A').obj V' ≅ B' :=
    @asIso _ _ _ _ ((puncturedSectionsSpecAdjunction (.of A')).counit.app B') hisoB
  let eCB : C ≅ B' :=
    (eUnitΓ ≪≫ asIso ((puncturedSectionsSpecAdjunction (.of A')).counit.app C)).symm ≪≫
      eΓ ≪≫ eB
  let eA : C.unop ≃ₐ[A'] B'.unop := CommAlgCat.algEquivOfIso eCB.symm.unop
  haveI : Algebra.Etale A' (A' ⊗[A] B.unop) := Algebra.Etale.of_equiv eA
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A'

/-- **Completion descent, regular local form.**

For a regular local ring `A` of dimension at least two, purity for the punctured spectrum of the
`m`-adic completion `A^∧` implies clause (2) of Stacks Tag `0BMA` for `A`.

The completion facts (regularity, faithful flatness `00MC`, `m_A A^∧ = m_{A^∧}`, equal dimension
`07NV`) come from `Pcf.Stacks.Purity.Completion`; normality of `A` and `A^∧` is Stacks `0567`
(`isIntegrallyClosed_of_isRegularLocalRing`).

Proof route diverges from Stacks (which uses Tag `0BLL`); see
`finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity`. -/
theorem finiteNormalPuncturedEtalePurity_of_completion_puncturedSpectrumPurity
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : 2 ≤ ringKrullDim A)
    (hpurity : PuncturedSpectrumPurity (AdicCompletion (maximalIdeal A) A)) :
    FiniteNormalPuncturedEtalePurity A := by
  letI : IsDomain A := isDomain_of_isRegularLocalRing A
  letI : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  letI : IsDomain (AdicCompletion (maximalIdeal A) A) :=
    isDomain_of_isRegularLocalRing _
  letI : IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) :=
    isIntegrallyClosed_of_isRegularLocalRing _
  letI : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    faithfullyFlat_adicCompletion A
  exact finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity
    A (AdicCompletion (maximalIdeal A) A) (map_maximalIdeal_adicCompletion A) hdim
    ((ringKrullDim_adicCompletion A).symm ▸ hdim) hpurity

#print axioms openSections_bijective_of_regularPair_of_puncturedEtale
#print axioms pullbackSections_bijective_of_regularPair_of_puncturedEtale
#print axioms preimage_puncturedSpectrum_eq_of_map_maximalIdeal_eq
#print axioms puncturedEtale_tensorProduct_of_map_maximalIdeal_eq
#print axioms finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity
#print axioms finiteNormalPuncturedEtalePurity_of_completion_puncturedSpectrumPurity

end Pcf.Stacks
