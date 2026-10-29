/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupNormalizedLift
public import Mathlib.RingTheory.Localization.AsSubring

/-!
# The function field on a Rees blow-up chart

For a nonzero chart coordinate `a`, the chart ring `R[I/a]` is an
intermediate ring between `R` and its fraction field. Its fraction field is
the fraction field of `R`. This is the affine algebraic input for comparing
the generic extensions of normalized blow-up maps with the original finite
map in `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry

universe u

set_option linter.style.haveILetI false

noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The chart ring embeds into the fraction field of the affine base. -/
def affineBlowupChartToFractionRing (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) : affineBlowupChart I a →ₐ[R] FractionRing R :=
  (Localization.mapToFractionRing (FractionRing R) (Submonoid.powers (a : R))
    (Localization.Away (a : R))
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).comp
      (Subalgebra.val (affineBlowupChart I a))

theorem affineBlowupChartToFractionRing_injective (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    Function.Injective (affineBlowupChartToFractionRing I a ha) := by
  have hinj : Function.Injective
      (Localization.mapToFractionRing (FractionRing R) (Submonoid.powers (a : R))
        (Localization.Away (a : R))
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha)) := by
    apply (IsLocalization.lift_injective_iff _).mpr
    intro x y
    constructor
    · intro h
      exact congrArg (algebraMap R (FractionRing R))
        ((IsLocalization.injective (Localization.Away (a : R))
          (powers_le_nonZeroDivisors_of_noZeroDivisors ha)) h)
    · intro h
      exact congrArg (algebraMap R (Localization.Away (a : R)))
        ((IsFractionRing.injective R (FractionRing R)) h)
  exact hinj.comp Subtype.val_injective

/-- The actual fraction field of an affine Rees chart is the fraction field
of the original integral affine base. -/
theorem affineBlowupChart_isFractionRing (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : Algebra (affineBlowupChart I a) (FractionRing R) :=
      (affineBlowupChartToFractionRing I a ha).toRingHom.toAlgebra
    IsFractionRing (affineBlowupChart I a) (FractionRing R) := by
  letI : Algebra (affineBlowupChart I a) (FractionRing R) :=
    (affineBlowupChartToFractionRing I a ha).toRingHom.toAlgebra
  letI : FaithfulSMul (affineBlowupChart I a) (FractionRing R) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (affineBlowupChartToFractionRing_injective I a ha)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, _, hz⟩ := IsFractionRing.div_surjective R z
  exact ⟨algebraMap R (affineBlowupChart I a) x,
    algebraMap R (affineBlowupChart I a) y, by
      change z = (affineBlowupChartToFractionRing I a ha)
          (algebraMap R (affineBlowupChart I a) x) /
        (affineBlowupChartToFractionRing I a ha)
          (algebraMap R (affineBlowupChart I a) y)
      simpa only [AlgHom.commutes] using hz.symm⟩

#print axioms affineBlowupChartToFractionRing
#print axioms affineBlowupChartToFractionRing_injective
#print axioms affineBlowupChart_isFractionRing

end

end Pcf.Bounding.AllCodimBlowup
