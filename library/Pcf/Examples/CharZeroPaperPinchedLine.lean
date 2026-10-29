/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperPinchedNode
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The invariant nodal line `B ⊂ X` of `paper.tex`, Example `ex:pinched`

The image `B` of `V(w-1)` in the pinched plane `X`:

* `restrB : R → k[B]`, `h ↦ h(z, 1)` read in the presentation
  `k[B] = k[b,d]/(d² - b(b-4)²)`, is surjective (`restrB_surjective`); its kernel is
  the prime `bPoint = ν(V(w-1))` of height one (`bDivisor`);
* `curveImmersion : B → X` is a closed immersion with image the closure of
  `bPoint` (`range_curveImmersion`), and `g ≫ ι = ι ≫ f` (`gScheme_curveImmersion`):
  `g` is the actual restriction of `f` to `B`;
* `f(B) = B` (`ambientMap_bPoint`).
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperPinched

open CategoryTheory AlgebraicGeometry Pcf.PaperCharZero Polynomial

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- `h ↦ h(z, 1)`. -/
def planeToLine : PlaneRing k →ₐ[k] Polynomial k := MvPolynomial.aeval ![X, 1]

theorem eval_planeToLine (a : k) (h : PlaneRing k) :
    (planeToLine k h).eval a = MvPolynomial.aeval ![a, 1] h := by
  change Polynomial.aeval a (MvPolynomial.aeval _ h) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp

theorem planeToLine_mem_range (h : PinchedRing k) :
    planeToLine k (val k h) ∈ (nodalParam k).range := by
  rw [mem_range_nodalParam_iff, eval_planeToLine, eval_planeToLine]
  exact val_mem k h

/-- The restriction `R → k[B]`. -/
def restrB : PinchedRing k →+* NodalRing k :=
  (AlgEquiv.ofInjective (nodalParam k) (nodalParam_injective k)).symm.toRingEquiv.toRingHom.comp
    (((planeToLine k : PlaneRing k →+* Polynomial k).comp
      (algebraMap (PinchedRing k) (PlaneRing k))).codRestrict (nodalParam k).range
        (planeToLine_mem_range k))

theorem nodalParam_restrB (h : PinchedRing k) :
    nodalParam k (restrB k h) = planeToLine k (val k h) := by
  have := (AlgEquiv.ofInjective (nodalParam k) (nodalParam_injective k)).apply_symm_apply
    ⟨planeToLine k (val k h), planeToLine_mem_range k h⟩
  exact congrArg Subtype.val this

theorem restrB_surjective : Function.Surjective (restrB k) := by
  intro n
  let p := nodalParam k n
  have hp : MvPolynomial.aeval ![(2 : k), 1]
      (Polynomial.aeval (MvPolynomial.X 0 : PlaneRing k) p) =
      MvPolynomial.aeval ![(-2 : k), 1] (Polynomial.aeval (MvPolynomial.X 0 : PlaneRing k) p) := by
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    simpa using nodalParam_eval_two k n
  refine ⟨mk k (Polynomial.aeval (MvPolynomial.X 0 : PlaneRing k) p) hp, nodalParam_injective k ?_⟩
  rw [nodalParam_restrB]
  change planeToLine k (Polynomial.aeval (MvPolynomial.X 0 : PlaneRing k) p) = p
  rw [← Polynomial.aeval_algHom_apply]
  simp [planeToLine]

theorem restrB_fStar (h : PinchedRing k) : restrB k (fStar k h) = gStar k (restrB k h) := by
  apply nodalParam_injective k
  rw [nodalParam_restrB, nodalParam_gStar, nodalParam_restrB, val_fStar, comp_eq_aeval]
  change MvPolynomial.aeval _ (MvPolynomial.aeval _ (val k h)) =
    Polynomial.aeval _ (MvPolynomial.aeval _ (val k h))
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The closed immersion `B → X`. -/
def curveImmersion : nodalCurve k ⟶ pinchedPlane k := Spec.map (CommRingCat.ofHom (restrB k))

instance curveImmersion_isClosedImmersion : IsClosedImmersion (curveImmersion k) :=
  IsClosedImmersion.spec_of_surjective _ (restrB_surjective k)

/-- **`g` is the restriction of `f` to `B`**: `g ≫ ι = ι ≫ f`. -/
theorem gScheme_curveImmersion :
    gScheme k ≫ curveImmersion k = curveImmersion k ≫ ambientMap k := by
  unfold gScheme curveImmersion ambientMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro h
  exact (restrB_fStar k h).symm

/-- The generic point of `B` in `X`. -/
def bPoint : pinchedPlane k := ⟨RingHom.ker (restrB k), RingHom.ker_isPrime _⟩

theorem mem_bPoint_iff (h : PinchedRing k) :
    h ∈ (bPoint k).asIdeal ↔ planeToLine k (val k h) = 0 := by
  change restrB k h = 0 ↔ _
  rw [← nodalParam_restrB, map_eq_zero_iff _ (nodalParam_injective k)]

theorem range_curveImmersion :
    Set.range (curveImmersion k) = closure {bPoint k} := by
  change Set.range (PrimeSpectrum.comap (restrB k)) = _
  rw [range_comap_of_surjective _ _ (restrB_surjective k)]
  change _ = closure ({(show PrimeSpectrum (PinchedRing k) from bPoint k)} :
    Set (PrimeSpectrum (PinchedRing k)))
  rw [PrimeSpectrum.closure_singleton]
  rfl

/-- **`f(B) = B`.** -/
theorem ambientMap_bPoint : ambientMap k (bPoint k) = bPoint k := by
  apply PrimeSpectrum.ext
  ext h
  change restrB k (fStar k h) = 0 ↔ restrB k h = 0
  rw [restrB_fStar, map_eq_zero_iff _ (gStar_injective k)]

/-- The line `V(w - 1)` of `𝔸²`. -/
def planeLine : plane k := ⟨RingHom.ker (planeToLine k), RingHom.ker_isPrime _⟩

/-- `B = ν(V(w - 1))`. -/
theorem nu_planeLine : nu k (planeLine k) = bPoint k := by
  apply PrimeSpectrum.ext
  ext h
  rw [mem_bPoint_iff]
  rfl

theorem sub_mem_span_w (h : PlaneRing k) :
    h - Polynomial.aeval (MvPolynomial.X 0) (planeToLine k h) ∈
      Ideal.span {(MvPolynomial.X 1 - 1 : PlaneRing k)} := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [planeToLine]
  | add p q hp hq =>
    convert Ideal.add_mem _ hp hq using 1
    simp only [map_add]; ring
  | mul_X p i hp =>
    have h1 := Ideal.mul_mem_right (MvPolynomial.X i) _ hp
    fin_cases i
    · convert h1 using 1
      simp [planeToLine]; ring
    · have h2 : Polynomial.aeval (MvPolynomial.X 0) (planeToLine k p) *
          (MvPolynomial.X 1 - 1 : PlaneRing k) ∈ Ideal.span {(MvPolynomial.X 1 - 1 : PlaneRing k)} :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      convert Ideal.add_mem _ h1 h2 using 1
      simp [planeToLine]; ring

theorem planeLine_eq_span :
    (planeLine k).asIdeal = Ideal.span {(MvPolynomial.X 1 - 1 : PlaneRing k)} := by
  apply le_antisymm
  · intro h hh
    have := sub_mem_span_w k h
    change planeToLine k h = 0 at hh
    rwa [hh, map_zero, sub_zero] at this
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change planeToLine k _ = 0
    simp [planeToLine]

theorem planeLine_height : (planeLine k).asIdeal.height = 1 := by
  rw [planeLine_eq_span]
  apply Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
  · apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h0
    have := congrArg (MvPolynomial.aeval ![(0 : k), 0]) h0
    simp at this
  · intro hu
    have := (hu.map (MvPolynomial.aeval ![(0 : k), 1]))
    simp at this

/-- `B` as an integral effective divisor of `X`. -/
def bDivisor : SchemeDivisorPoint (pinchedPlane k) :=
  ⟨bPoint k, by
    let x : PrimeSpectrum (PlaneRing k) := planeLine k
    rw [← idealHeight_eq_coheight, ← nu_planeLine]
    change (x.asIdeal.under (PinchedRing k)).height = 1
    rw [height_under_eq_of_finite_of_finiteType k]
    exact planeLine_height k⟩

end Pcf.Examples.CharZeroPaperPinched

#print axioms Pcf.Examples.CharZeroPaperPinched.restrB_surjective
#print axioms Pcf.Examples.CharZeroPaperPinched.restrB_fStar
#print axioms Pcf.Examples.CharZeroPaperPinched.gScheme_curveImmersion
#print axioms Pcf.Examples.CharZeroPaperPinched.range_curveImmersion
#print axioms Pcf.Examples.CharZeroPaperPinched.ambientMap_bPoint
#print axioms Pcf.Examples.CharZeroPaperPinched.nu_planeLine
#print axioms Pcf.Examples.CharZeroPaperPinched.bDivisor
