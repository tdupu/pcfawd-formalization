/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLocalStructure
public import Pcf.Examples.PaperP.FrobeniusPinchingGalois

/-!
# The pinched map `f` has degree `4`

For `paper-p.tex`, Example `ex:pinched` (the Singular remark): "… while `f` has degree `4`".

The degree of the finite dominant map `f : X → X` is the field degree
`[K(X) : f^* K(X)]`. `K(X) = Frac R = Frac k[z, w]`, because `R ⊆ k[z, w]` is birational
(conductor `w - 1`). Under that identification `f^*` becomes the squaring map
`(z, w) ↦ (z², w²)`, whose function-field extension has degree `4`
(`FrobeniusPinchingGalois.galois_of_squareFractionData`).

* `finrank_eq_four`: for any fields `F`, `E` that are fraction fields of `R`, and any
  `F → E` restricting to `f^* : R → R`, `[E : F] = 4`. The extension is also Galois with group
  `(ℤ/2)²` (`isGalois_and_finrank`).
* `finrank_fracMap`: the instance `F = E = Frac R` with `F → E` the extension of `f^*`.

Not formalized: the deduction "finite flat over a local ring ⇒ free of the generic rank, so the
fibre length would be `4`". Non-flatness of `f` at `o` is proved by a different route in
`PinchedNotFlat` (a depth argument), so the manuscript's "fibre length `5` ≠ degree `4`" is
now supported by both numbers (`PinchedFibreLength.finrank_fibre` and this file) but the
implication between them is not.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedGenericDegree

open MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedLocalStructure
open Pcf.Examples.PaperP.PinchedAmbient Pcf.Examples.PaperP.FrobeniusPinchingGalois
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators

set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

instance isFractionRing_fractionRing_plane :
    IsFractionRing (PinchedRing k) (FractionRing (PlaneRing k)) :=
  isFractionRing_of_conductor (wSubOne k) (wSubOne_ne_zero k)
    (conductor k (wSubOne k) (wSubOne_mem_oIdeal k))

section Field

variable (K : Type*) [Field K] [Algebra (PinchedRing k) K] [IsFractionRing (PinchedRing k) K]

/-- The identification `Frac k[z, w] ≅ K` over `R`. -/
noncomputable def fracEquiv : FractionRing (PlaneRing k) ≃ₐ[PinchedRing k] K :=
  IsLocalization.algEquiv (nonZeroDivisors (PinchedRing k)) _ _

/-- `k[z, w] → K`. -/
noncomputable def planeToFrac : PlaneRing k →+* K :=
  (fracEquiv k K).toRingEquiv.toRingHom.comp (algebraMap (PlaneRing k) _)

theorem planeToFrac_algebraMap (r : PinchedRing k) :
    planeToFrac k K (algebraMap (PinchedRing k) (PlaneRing k) r) =
      algebraMap (PinchedRing k) K r := by
  change fracEquiv k K (algebraMap (PlaneRing k) (FractionRing (PlaneRing k))
    (algebraMap (PinchedRing k) (PlaneRing k) r)) = _
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]

theorem isFractionRing_planeToFrac :
    @IsFractionRing (PlaneRing k) _ K _ (planeToFrac k K).toAlgebra := by
  let _ : Algebra (PlaneRing k) K := (planeToFrac k K).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (PlaneRing k))
    (AlgEquiv.ofRingEquiv (f := (fracEquiv k K).toRingEquiv) fun _ => rfl)

theorem planeToFrac_injective : Function.Injective (planeToFrac k K) :=
  (fracEquiv k K).injective.comp (IsFractionRing.injective _ _)

end Field

variable {k}

/-- **`[E : F] = 4`, Galois with group `(ℤ/2)²`**: for fraction fields `F`, `E` of `R` and
`F → E` restricting to `f^*`. -/
theorem isGalois_and_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra (PinchedRing k) F] [IsFractionRing (PinchedRing k) F]
    [Algebra (PinchedRing k) E] [IsFractionRing (PinchedRing k) E]
    (hcomm : ∀ r : PinchedRing k,
      algebraMap F E (algebraMap (PinchedRing k) F r) = algebraMap (PinchedRing k) E (fStar k r)) :
    IsGalois F E ∧ Module.finrank F E = 4 ∧ Nonempty ((E ≃ₐ[F] E) ≃* SignGroup) := by
  refine galois_of_squareFractionData (i := planeToFrac k F) (j := planeToFrac k E)
    (two_ne_zero : (2 : k) ≠ 0)
    ⟨isFractionRing_planeToFrac k F, isFractionRing_planeToFrac k E, ?_⟩
  refine RingHom.ext fun s => ?_
  obtain ⟨a, ha⟩ := PinchedLocalStructure.conductor k (wSubOne k) (wSubOne_mem_oIdeal k) s
  set c := algebraMap (PinchedRing k) (PlaneRing k) (wSubOne k)
  have hsq : ∀ r : PinchedRing k, (square k) (algebraMap (PinchedRing k) (PlaneRing k) r) =
      algebraMap (PinchedRing k) (PlaneRing k) (fStar k r) := fun _ => rfl
  have hc : algebraMap F E (planeToFrac k F c) = planeToFrac k E (square k c) := by
    rw [planeToFrac_algebraMap, hcomm, hsq, planeToFrac_algebraMap]
  have hne : planeToFrac k E (square k c) ≠ 0 := by
    rw [map_ne_zero_iff _ (planeToFrac_injective k E)]
    intro h0
    have : c = 0 := squaringMap_injective k
      (show squaringMap k c = squaringMap k 0 by rw [map_zero]; exact h0)
    exact wSubOne_ne_zero k (algebraMap_injective k (by rw [map_zero]; exact this))
  apply mul_right_cancel₀ hne
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  calc algebraMap F E (planeToFrac k F s) * planeToFrac k E (square k c)
      = algebraMap F E (planeToFrac k F (c * s)) := by rw [← hc, ← map_mul, ← map_mul, mul_comm]
    _ = algebraMap (PinchedRing k) E (fStar k a) := by
        rw [← ha, planeToFrac_algebraMap, hcomm]
    _ = planeToFrac k E (square k (c * s)) := by
        rw [← ha, hsq, planeToFrac_algebraMap]
    _ = planeToFrac k E (square k s) * planeToFrac k E (square k c) := by
        rw [map_mul, map_mul, mul_comm]

/-- `paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem finrank_eq_four {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Algebra (PinchedRing k) F] [IsFractionRing (PinchedRing k) F]
    [Algebra (PinchedRing k) E] [IsFractionRing (PinchedRing k) E]
    (hcomm : ∀ r : PinchedRing k,
      algebraMap F E (algebraMap (PinchedRing k) F r) = algebraMap (PinchedRing k) E (fStar k r)) :
    Module.finrank F E = 4 :=
  (isGalois_and_finrank hcomm).2.1

variable (k)

theorem fStar_injective : Function.Injective (fStar k) := fun _ _ h =>
  Subtype.val_injective (squaringMap_injective k (congrArg (PinchedRing.val k) h))

/-- `f^* : Frac R → Frac R`. -/
noncomputable def fracMap : FractionRing (PinchedRing k) →+* FractionRing (PinchedRing k) :=
  IsFractionRing.map (fStar_injective k)

/-- **`deg f = [Frac R : f^* Frac R] = 4`.** -/
theorem finrank_fracMap :
    @Module.finrank (FractionRing (PinchedRing k)) (FractionRing (PinchedRing k)) _ _
      (fracMap k).toAlgebra.toModule = 4 :=
  @finrank_eq_four k _ _ (FractionRing (PinchedRing k)) (FractionRing (PinchedRing k)) _ _
    (fracMap k).toAlgebra _ _ _ _ fun r =>
      IsLocalization.map_eq (T := nonZeroDivisors (PinchedRing k))
        (hy := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (fStar_injective k)) r

#print axioms isGalois_and_finrank
#print axioms finrank_fracMap

end Pcf.Examples.PaperP.PinchedGenericDegree
