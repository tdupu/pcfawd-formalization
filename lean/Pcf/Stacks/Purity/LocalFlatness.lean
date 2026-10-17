/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.RingHom.Flat

/-!
# Local detection of flatness in Stacks Tag 00HT

This file records the algebra specialization of part (6) of Stacks Tag `00HT` used in the
finite-normal-algebra argument for purity. Flatness of an algebra is equivalent to flatness of
all its maps on local rings at primes of the target. Mathlib contains both directions as the
locality theorem for `RingHom.Flat`; the result below fixes the exact localization maps used by
the Stacks proof.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- **Stacks Tag `00HT`, part (6), for the module `A` over `R`.**

The algebra `A` is flat over `R` exactly when every target-prime localization is flat over the
corresponding source-prime localization. -/
@[stacks 00HT "part (6), specialized to an algebra"]
theorem algebraMap_flat_iff_localRingHom_flat :
    Module.Flat R A ↔
      ∀ (q : Ideal A) (hq : q.IsPrime),
        letI := hq
        (Localization.localRingHom (q.under R) q (algebraMap R A) rfl).Flat := by
  constructor
  · intro h q hq
    letI := hq
    exact (RingHom.flat_algebraMap_iff.mpr h).localRingHom q (q.under R) rfl
  · intro h
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.ofLocalizationPrime (algebraMap R A) h

end Pcf.Stacks
