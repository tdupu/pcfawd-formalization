/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.RegularPairSections
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
  letI : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  letI : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  letI : IsDomain (AdicCompletion (maximalIdeal A) A) :=
    Pcf.Vendor.isDomain_of_isRegularLocalRing _
  letI : IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) :=
    isIntegrallyClosed_of_isRegularLocalRing _
  letI : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    faithfullyFlat_adicCompletion A
  exact finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity
    A (AdicCompletion (maximalIdeal A) A) (map_maximalIdeal_adicCompletion A) hdim
    ((ringKrullDim_adicCompletion A).symm ▸ hdim) hpurity

#print axioms preimage_puncturedSpectrum_eq_of_map_maximalIdeal_eq
#print axioms puncturedEtale_tensorProduct_of_map_maximalIdeal_eq
#print axioms finiteNormalPuncturedEtalePurity_of_faithfullyFlat_puncturedSpectrumPurity
#print axioms finiteNormalPuncturedEtalePurity_of_completion_puncturedSpectrumPurity

end Pcf.Stacks
