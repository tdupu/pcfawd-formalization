/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Stalk
import Pcf.Stacks.Purity.Hartogs

/-!
# Generic fibre of a finite étale punctured cover

The first geometric step in Stacks Tag `0BM9` pulls a finite étale cover of the punctured
spectrum back to the generic point.  This fibre is an affine finite étale scheme over the
function field.  Its connected components are the field extensions used in the integral-closure
construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

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

end Pcf.Stacks
