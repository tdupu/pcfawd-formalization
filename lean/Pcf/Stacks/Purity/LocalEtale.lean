/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# A local flatness criterion for formal étaleness

This file packages the local form of the flat-plus-unramified criterion needed in the
dimension-one case of purity.  Unlike `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, it assumes
flatness only after passing to the two local rings.  The finite-presentation datum is supplied by
an algebra of finite presentation whose localization is the target local ring.
-/

@[expose] public section

namespace Pcf.Stacks

open TensorProduct IsLocalRing

universe u v

/-- A flat, formally unramified local map which is essentially of finite presentation is formally
étale.  The presentation is made explicit because Mathlib does not yet have an
`EssentiallyFinitePresentation` typeclass.

This is the local algebra step used in the dimension-one case of Stacks Tag `0BMB`; it is also a
local counterpart of Mathlib's `Algebra.Etale.of_formallyUnramified_of_flat` (Tag `08WD`). -/
theorem formallyEtale_of_flat_of_formallyUnramified_of_isLocalization
    (R S P : Type*) [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] [Algebra.FormallyUnramified R S]
    (M : Submonoid P) [IsLocalization M S] [Algebra.FinitePresentation R P] :
    Algebra.FormallyEtale R S := by
  let _ : Algebra.EssFiniteType P S := Algebra.EssFiniteType.of_isLocalization S M
  let _ : Algebra.EssFiniteType R S := Algebra.EssFiniteType.comp R P S
  let _ : Algebra.FormallyEtale (ResidueField R) (ResidueField R ⊗[R] S) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  let _ : Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] S) := inferInstance
  let _ : Algebra.FormallySmooth R S :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (P := P) M
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

end Pcf.Stacks
