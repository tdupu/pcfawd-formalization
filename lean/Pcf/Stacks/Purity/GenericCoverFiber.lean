/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Localization
import Pcf.Stacks.Purity.Hartogs

/-!
# Generic fibre of a finite étale punctured cover

The first geometric step in Stacks Tag `0BM9` pulls a finite étale cover of the punctured
spectrum back to the generic point.  This fibre is an affine finite étale scheme over the
function field.  Its connected components are the field extensions used in the integral-closure
construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsDomain R] in
/-- A finite étale cover of a punctured Noetherian local spectrum is itself Noetherian. In
particular it is quasi-compact and quasi-separated for flat base change of global sections. -/
theorem puncturedCover_isNoetherian
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) : IsNoetherian V.left := by
  letI : IsFinite V.hom := V.prop.1
  letI : IsLocallyNoetherian
      ((Functor.fromPUnit (puncturedSpectrumScheme R)).obj V.right) := by
    change IsLocallyNoetherian (puncturedSpectrumScheme R)
    exact isLocallyNoetherian_of_isOpenImmersion (puncturedSpectrum R).ι
  letI : CompactSpace
      ((Functor.fromPUnit (puncturedSpectrumScheme R)).obj V.right) := by
    change CompactSpace (puncturedSpectrumScheme R)
    exact isCompact_iff_compactSpace.mp (isCompact_puncturedSpectrum R)
  letI : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian V.hom }

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The generic point of an integral affine scheme is flat over the scheme, since its
function field is a localization of the coordinate ring. -/
theorem genericPoint_fromSpecStalk_flat :
    Flat ((Spec R).fromSpecStalk (genericPoint (Spec R))) := by
  rw [Spec.fromSpecStalk_eq']
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R (Spec R).functionField).Flat
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Spec R).functionField (nonZeroDivisors R))

/-- Flat base change of global sections from the affine base `Spec R` to its generic point is an
isomorphism for every finite étale punctured cover. The cover is Noetherian, hence qcqs, which is
the substantive hypothesis in Mathlib's base-change theorem. -/
theorem puncturedCover_genericBaseChange_isIso
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let iX := V.hom ≫ (puncturedSpectrum R).ι
    IsIso (pushoutSection (IsPullback.of_hasPullback iX f)
      (show (⊤ : (Spec (Spec R).functionField).Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec R).Opens) from by simp)
      (show (⊤ : V.left.Opens) ≤ iX ⁻¹ᵁ (⊤ : (Spec R).Opens) from by simp)
      (show (⊤ : (Limits.pullback iX f).Opens) =
        Limits.pullback.fst iX f ⁻¹ᵁ (⊤ : V.left.Opens) ⊓
          Limits.pullback.snd iX f ⁻¹ᵁ
            (⊤ : (Spec (Spec R).functionField).Opens) from by simp)) := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let iX := V.hom ≫ (puncturedSpectrum R).ι
  letI : Flat f := genericPoint_fromSpecStalk_flat R
  letI : IsNoetherian ((𝟭 Scheme).obj V.left) := by
    change IsNoetherian V.left
    exact puncturedCover_isNoetherian R V
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback iX f) (by simp) (by simp) (by simp)
    (isAffineOpen_top (Spec R))
    (isAffineOpen_top (Spec (Spec R).functionField))
    CompactSpace.isCompact_univ isQuasiSeparated_univ

omit [IsNoetherianRing R] in
/-- The generic point of a positive-dimensional local domain lies in its punctured spectrum. -/
theorem genericPoint_mem_puncturedSpectrum (hdim : 1 ≤ ringKrullDim R) :
    genericPoint (Spec R) ∈ puncturedSpectrum R := by
  have hnon : Nonempty (puncturedSpectrum R) :=
    puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hdim
  exact ((genericPoint_spec (Spec R)).mem_open_set_iff
    (puncturedSpectrum R).isOpen).mpr (by simpa using hnon)

/-- Pull a finite étale punctured cover back along the generic point. -/
noncomputable def puncturedCoverGenericFiber (hdim : 1 ≤ ringKrullDim R) :
    FiniteEtaleCover (puncturedSpectrumScheme R) ⥤
      FiniteEtaleCover (Spec (Spec R).functionField) :=
  FiniteEtaleCover.pullback _
    ((puncturedSpectrum R).fromSpecStalkOfMem
      (genericPoint (Spec R)) (genericPoint_mem_puncturedSpectrum R hdim))

/-- The generic fibre formed over the puncture is the same scheme as base change over
`Spec R` along its generic point. -/
noncomputable def puncturedCoverGenericFiber_iso_basePullback
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    ((puncturedCoverGenericFiber R hdim).obj V).left ≅
      Limits.pullback (V.hom ≫ (puncturedSpectrum R).ι)
        ((Spec R).fromSpecStalk (genericPoint (Spec R))) := by
  let i := (puncturedSpectrum R).ι
  let g := (puncturedSpectrum R).fromSpecStalkOfMem
    (genericPoint (Spec R)) (genericPoint_mem_puncturedSpectrum R hdim)
  let h : IsPullback (Limits.pullback.fst V.hom g) (Limits.pullback.snd V.hom g)
      (V.hom ≫ i) (g ≫ i) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono V.hom g i)
  have hg : g ≫ i = (Spec R).fromSpecStalk (genericPoint (Spec R)) :=
    (puncturedSpectrum R).fromSpecStalkOfMem_ι _ _
  rw [← hg]
  exact h.isoPullback

omit [IsNoetherianRing R] in
/-- The generic fibre of any finite étale punctured cover is affine. -/
theorem puncturedCoverGenericFiber_isAffine (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    IsAffine ((puncturedCoverGenericFiber R hdim).obj V).left := by
  let W := (puncturedCoverGenericFiber R hdim).obj V
  letI : IsFinite W.hom := W.prop.1
  letI : IsAffine ((Functor.fromPUnit (Spec (Spec R).functionField)).obj W.right) := by
    change IsAffine (Spec (Spec R).functionField)
    infer_instance
  exact isAffine_of_isAffineHom W.hom

omit [IsNoetherianRing R] in
/-- The affine generic fibre is finite over the function-field scheme on global sections. -/
theorem puncturedCoverGenericFiber_finite_appTop (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    (((puncturedCoverGenericFiber R hdim).obj V).hom.appTop).hom.Finite := by
  let W := (puncturedCoverGenericFiber R hdim).obj V
  letI : IsFinite W.hom := W.prop.1
  letI : IsAffine ((Functor.fromPUnit (Spec (Spec R).functionField)).obj W.right) := by
    change IsAffine (Spec (Spec R).functionField)
    infer_instance
  exact W.hom.finite_appTop

omit [IsNoetherianRing R] in
/-- The ring map on global sections of an arbitrary punctured cover's generic fibre is étale. -/
theorem puncturedCoverGenericFiber_etale_appTop (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    (((puncturedCoverGenericFiber R hdim).obj V).hom.appTop).hom.Etale := by
  let W := (puncturedCoverGenericFiber R hdim).obj V
  letI : Etale W.hom := W.prop.2
  letI : IsAffine W.left := puncturedCoverGenericFiber_isAffine R hdim V
  letI : IsAffine ((𝟭 Scheme).obj W.left) := by
    change IsAffine W.left
    infer_instance
  letI : IsAffine ((Functor.fromPUnit (Spec (Spec R).functionField)).obj W.right) := by
    change IsAffine (Spec (Spec R).functionField)
    infer_instance
  exact HasRingHomProperty.appTop (@Etale) W.hom W.prop.2

/-- The finite étale algebra map of the generic fibre, with its source identified with the
function field rather than the global sections of its affine spectrum. -/
noncomputable def puncturedCoverGenericFiber_ringHom (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    (Spec R).functionField →+*
      Γ(((puncturedCoverGenericFiber R hdim).obj V).left, ⊤) :=
  ((Scheme.ΓSpecIso (Spec R).functionField).inv ≫
    ((puncturedCoverGenericFiber R hdim).obj V).hom.appTop).hom

omit [IsNoetherianRing R] in
/-- The generic-fibre algebra of any finite étale punctured cover is module-finite over the
function field. -/
theorem puncturedCoverGenericFiber_ringHom_finite (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    (puncturedCoverGenericFiber_ringHom R hdim V).Finite := by
  have h₁ := puncturedCoverGenericFiber_finite_appTop R hdim V
  have h₂ : ((Scheme.ΓSpecIso (Spec R).functionField).inv.hom).Finite :=
    RingHom.Finite.of_surjective _
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective
  exact h₁.comp h₂

omit [IsNoetherianRing R] in
/-- The same generic-fibre algebra map is étale over the function field. -/
theorem puncturedCoverGenericFiber_ringHom_etale (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    (puncturedCoverGenericFiber_ringHom R hdim V).Etale := by
  have h₁ := puncturedCoverGenericFiber_etale_appTop R hdim V
  have h₂ : ((Scheme.ΓSpecIso (Spec R).functionField).inv.hom).Etale :=
    RingHom.Etale.of_bijective
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  exact RingHom.Etale.stableUnderComposition _ _ h₂ h₁

/-- The commutative algebra over the function field carried by the generic fibre. -/
noncomputable def puncturedCoverGenericFiberAlgebra (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    CommAlgCat (Spec R).functionField := by
  let W := (puncturedCoverGenericFiber R hdim).obj V
  letI : Algebra (Spec R).functionField Γ(W.left, ⊤) :=
    (puncturedCoverGenericFiber_ringHom R hdim V).toAlgebra
  exact .of (Spec R).functionField Γ(W.left, ⊤)

omit [IsNoetherianRing R] in
/-- The generic fibre of any finite étale cover of the punctured spectrum is a finite product of
finite separable field extensions of the base function field, including the empty product. -/
theorem puncturedCoverGenericFiber_exists_separableFields (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    ∃ (I : Type u) (_ : Finite I) (L : I → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra (Spec R).functionField (L i))
      (_ : (puncturedCoverGenericFiberAlgebra R hdim V) ≃ₐ[(Spec R).functionField]
        (∀ i, L i)),
      ∀ i, Module.Finite (Spec R).functionField (L i) ∧
        Algebra.IsSeparable (Spec R).functionField (L i) := by
  let W := (puncturedCoverGenericFiber R hdim).obj V
  let E := puncturedCoverGenericFiberAlgebra R hdim V
  have hEtale : Algebra.Etale (Spec R).functionField E := by
    exact (puncturedCoverGenericFiber_ringHom_etale R hdim V).toAlgebra
  exact (Algebra.Etale.iff_exists_algEquiv_prod (Spec R).functionField E).mp hEtale

end Pcf.Stacks
