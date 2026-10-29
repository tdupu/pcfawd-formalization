/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNormalization
public import Mathlib.Algebra.MvPolynomial.Expand

/-!
# The ambient map `f : X → X` of the pinched plane

For `paper-p.tex`, Example `ex:pinched` ("`f̃` descends to a morphism
`f : X → X` with `f ∘ ν = ν ∘ f̃`"; "`f` is finite, and surjective"):

* `fStar : R →+* R`, the restriction of `f̃* : h ↦ h(z², w²)`.
* `fScheme_comp_nu`: `f ∘ ν = ν ∘ f̃` as actual scheme maps.
* `fStar_finite`, `fScheme_isFinite`, `fScheme_surjective`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedAmbient

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

omit [CharZero k] in
theorem squaringMap_eq_expand : squaringMap k = expand 2 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [squaringMap, expand]

omit [CharZero k] in
theorem squaringMap_injective : Function.Injective (squaringMap k) := by
  rw [squaringMap_eq_expand]
  exact expand_injective (by norm_num)

/-- `f* : R → R`, the restriction of `f̃*`. -/
noncomputable def fStar : PinchedRing k →+* PinchedRing k where
  toFun r := PinchedRing.mk k (squaringMap k (PinchedRing.val k r)) (squaringMap_mem k _)
  map_one' := by
    apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
    exact map_one (squaringMap k)
  map_mul' a b := by
    apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
    exact map_mul (squaringMap k) _ _
  map_zero' := by
    apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
    exact map_zero (squaringMap k)
  map_add' a b := by
    apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
    exact map_add (squaringMap k) _ _

omit [CharZero k] in
theorem val_fStar (r : PinchedRing k) :
    PinchedRing.val k (fStar k r) = squaringMap k (PinchedRing.val k r) := rfl

/-- The actual scheme map `f : X → X`. -/
noncomputable def fScheme : Spec (.of (PinchedRing k)) ⟶ Spec (.of (PinchedRing k)) :=
  Spec.map (CommRingCat.ofHom (fStar k))

/-- `ν : 𝔸² → X`. -/
noncomputable abbrev nu : Spec (.of (PlaneRing k)) ⟶ Spec (.of (PinchedRing k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PinchedRing k) (PlaneRing k)))

/-- `f̃ : 𝔸² → 𝔸²`, `(z, w) ↦ (z², w²)`. -/
noncomputable def fTilde : Spec (.of (PlaneRing k)) ⟶ Spec (.of (PlaneRing k)) :=
  Spec.map (CommRingCat.ofHom (squaringMap k).toRingHom)

omit [CharZero k] in
/-- `f ∘ ν = ν ∘ f̃`. -/
theorem fScheme_comp_nu : fTilde k ≫ nu k = nu k ≫ fScheme k := by
  unfold fTilde fScheme
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

omit [CharZero k] in
theorem fStar_injective : Function.Injective (fStar k) := by
  intro a b h
  apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
  exact squaringMap_injective k (congrArg (PinchedRing.val k) h)

omit [CharZero k] in
theorem fStar_comp_algebraMap :
    (fStar k).comp (algebraMap k (PinchedRing k)) = algebraMap k (PinchedRing k) := by
  ext c
  apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
  exact (squaringMap k).commutes c

omit [CharZero k] in
theorem z_sq_mem' : (X 0 ^ 2 : PlaneRing k) ∈ pinchedAlg k := z_sq_mem k
omit [CharZero k] in
theorem w_mem' : (X 1 : PlaneRing k) ∈ pinchedAlg k := w_mem k

/-- `k[z, w]` is integral over `R` through `f*`: `z⁴ = f*(z²)`, `w² = f*(w)`. -/
theorem plane_isIntegralElem_over_f (p : PlaneRing k) :
    ((algebraMap (PinchedRing k) (PlaneRing k)).comp (fStar k)).IsIntegralElem p := by
  let φ := (algebraMap (PinchedRing k) (PlaneRing k)).comp (fStar k)
  have hX0 : φ.IsIntegralElem (X 0 : PlaneRing k) := by
    refine ⟨Polynomial.X ^ 4 - Polynomial.C (PinchedRing.mk k (X 0 ^ 2) (z_sq_mem' k)),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    change (X 0 : PlaneRing k) ^ 4 - squaringMap k (X 0 ^ 2) = 0
    simp [squaringMap]
    ring
  have hX1 : φ.IsIntegralElem (X 1 : PlaneRing k) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (PinchedRing.mk k (X 1) (w_mem' k)),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    change (X 1 : PlaneRing k) ^ 2 - squaringMap k (X 1) = 0
    simp [squaringMap]
  have hC (a : k) : φ.IsIntegralElem (C a) := by
    have h := RingHom.isIntegralElem_map φ (x := algebraMap k (PinchedRing k) a)
    have hφ : φ (algebraMap k (PinchedRing k) a) = C a := by
      change PinchedRing.val k (fStar k (algebraMap k (PinchedRing k) a)) = C a
      rw [← RingHom.comp_apply, fStar_comp_algebraMap]
      rfl
    rwa [hφ] at h
  induction p using MvPolynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact RingHom.IsIntegralElem.add φ hp hq
  | mul_X p i hp =>
      fin_cases i
      · exact RingHom.IsIntegralElem.mul φ hp hX0
      · exact RingHom.IsIntegralElem.mul φ hp hX1

/-- `f* : R → R` is finite ("`R` is finite over `f*R`"). -/
theorem fStar_finite : (fStar k).Finite := by
  refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨?_, ?_⟩
  · intro r
    obtain ⟨P, hP, hev⟩ := plane_isIntegralElem_over_f k (PinchedRing.val k r)
    refine ⟨P, hP, ?_⟩
    apply (Subtype.val_injective (p := fun h => h ∈ pinchedAlg k))
    change algebraMap (PinchedRing k) (PlaneRing k) (P.eval₂ (fStar k) r) =
      algebraMap (PinchedRing k) (PlaneRing k) 0
    rw [Polynomial.hom_eval₂, map_zero]
    exact hev
  · apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (PinchedRing k))
    rw [fStar_comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- `f` is finite.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
instance fScheme_isFinite : IsFinite (fScheme k) :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom (fStar k))).mpr (fStar_finite k)

/-- `f` is surjective.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
instance fScheme_surjective : Surjective (fScheme k) := by
  constructor
  exact (fStar_finite k).to_isIntegral.comap_surjective (fStar_injective k)

instance fScheme_isDominant : IsDominant (fScheme k) := inferInstance

#print axioms fScheme_comp_nu
#print axioms fStar_finite
#print axioms fScheme_isFinite
#print axioms fScheme_surjective

end Pcf.Examples.PaperP.PinchedAmbient
