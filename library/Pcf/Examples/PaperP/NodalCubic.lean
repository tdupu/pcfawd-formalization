/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CuspFiber
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The nodal cubic in `paper-p.tex`

The curve is `N = V(y² - x²(x+1))`; the parametrization is
`x = t² - 1`, `y = t³ - t`. The projection to the `x`-axis has
nonreduced fibre over zero. These are the algebraic calculations used by
`ex:loci-compared` and the reverse-inclusion counterexample of
`lem:tower-unnormalized`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.NodalCubic

open Polynomial
open AlgebraicGeometry CategoryTheory

set_option linter.style.haveILetI false

variable (k : Type*) [Field k]

abbrev Plane := MvPolynomial (Fin 2) k

noncomputable def equation : Plane k :=
  MvPolynomial.X 1 ^ 2 -
    MvPolynomial.X 0 ^ 2 * (MvPolynomial.X 0 + 1)

noncomputable def ideal : Ideal (Plane k) := Ideal.span {equation k}

abbrev CoordinateRing := Plane k ⧸ ideal k

/-- The candidate normalization parametrization on coordinate rings. Its
normalization property is a separate, currently unproved claim. -/
noncomputable def parametrization : CoordinateRing k →ₐ[k] k[X] :=
  Ideal.Quotient.liftₐ _
    (MvPolynomial.aeval ![(X : k[X]) ^ 2 - 1,
      (X : k[X]) ^ 3 - X]) <| by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      have hz : MvPolynomial.aeval ![(X : k[X]) ^ 2 - 1,
          (X : k[X]) ^ 3 - X] (equation k) = 0 := by
        simp [equation]
        ring
      simp [hz]

@[simp] theorem parametrization_x :
    parametrization k (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
      (X : k[X]) ^ 2 - 1 := by
  change MvPolynomial.aeval ![(X : k[X]) ^ 2 - 1, X ^ 3 - X] _ = _
  simp

@[simp] theorem parametrization_y :
    parametrization k (Ideal.Quotient.mk _ (MvPolynomial.X 1)) =
      (X : k[X]) ^ 3 - X := by
  change MvPolynomial.aeval ![(X : k[X]) ^ 2 - 1, X ^ 3 - X] _ = _
  simp

/-- The coordinate map of the projection `N → A¹`, sending the affine-line
coordinate to `x` on the nodal cubic. -/
noncomputable def projection : k[X] →ₐ[k] CoordinateRing k :=
  Polynomial.aeval (Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0))

@[simp] theorem projection_X :
    projection k (X : k[X]) =
      Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0) := by
  simp [projection]

/-- The composite of parametrization and projection is `t ↦ t² - 1`,
as stated in the nodal-cubic counterexample. -/
theorem parametrization_comp_projection :
    (parametrization k).comp (projection k) =
      Polynomial.aeval ((X : k[X]) ^ 2 - 1) := by
  ext
  simp

/-- The affine scheme map `A¹ → N` induced by the nodal parametrization. -/
noncomputable def normalizationSchemeMap :
    Spec (.of k[X]) ⟶ Spec (.of (CoordinateRing k)) :=
  Spec.map (CommRingCat.ofHom (parametrization k).toRingHom)

/-- The affine projection `N → A¹`. -/
noncomputable def projectionSchemeMap :
    Spec (.of (CoordinateRing k)) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (projection k).toRingHom)

/-- The corresponding composite scheme map is the one induced by
`x ↦ t² - 1` on affine coordinates. -/
theorem normalizationSchemeMap_comp_projectionSchemeMap :
    normalizationSchemeMap k ≫ projectionSchemeMap k =
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval ((X : k[X]) ^ 2 - 1)).toRingHom) := by
  unfold normalizationSchemeMap projectionSchemeMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : k[X] →+* k[X] => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (parametrization_comp_projection k))

/-- The fibre of the projection `N → A¹` over the origin has equations
`x = 0` and `y² - x²(x+1) = 0`. -/
noncomputable def originFiberIdeal : Ideal (Plane k) :=
  Ideal.span {equation k, MvPolynomial.X 0}

abbrev OriginFiber := Plane k ⧸ originFiberIdeal k

/-- The same fibre as a quotient of the nodal cubic's coordinate ring by
the pullback of the origin ideal `(x)` on the target affine line. -/
abbrev ProjectionOriginFiber := CoordinateRing k ⧸
  (Ideal.span {MvPolynomial.X 0} : Ideal (Plane k)).map
    (Ideal.Quotient.mk (ideal k))

theorem ideal_sup_x_eq_origin :
    ideal k ⊔ (Ideal.span {MvPolynomial.X 0} : Ideal (Plane k)) =
      originFiberIdeal k := by
  simp [ideal, originFiberIdeal, Ideal.span_insert]

/-- The direct equations for the projection fibre agree with the actual
quotient of the coordinate ring by the target's origin ideal. -/
noncomputable def projectionOriginFiberEquiv :
    ProjectionOriginFiber k ≃+* OriginFiber k :=
  (DoubleQuot.quotQuotEquivQuotSup (ideal k)
    (Ideal.span {MvPolynomial.X 0} : Ideal (Plane k))).trans
      (Ideal.quotEquivOfEq (ideal_sup_x_eq_origin k))

noncomputable def fiberY : OriginFiber k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

theorem fiberY_sq_zero : fiberY k ^ 2 = 0 := by
  have hrel : Ideal.Quotient.mk (originFiberIdeal k) (equation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hx : Ideal.Quotient.mk (originFiberIdeal k) (MvPolynomial.X 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  unfold equation at hrel
  simp only [map_sub, map_mul, map_pow, map_add, map_one] at hrel
  simpa [fiberY, hx] using hrel

/-- Evaluation at `x = 0`, `y = ε` maps the nodal projection fibre to
the dual numbers `k[ε]/(ε²)`. -/
noncomputable def originFiberToDual : OriginFiber k →ₐ[k] CuspFiber.Fiber k := by
  let u : CuspFiber.Fiber k :=
    Ideal.Quotient.mk (CuspFiber.fiberIdeal k) (X : k[X])
  let φ : Plane k →ₐ[k] CuspFiber.Fiber k := MvPolynomial.aeval ![0, u]
  apply Ideal.Quotient.liftₐ _ φ
  intro a ha
  have hrel : φ (equation k) = 0 := by
    simp [φ, equation, u, CuspFiber.coordinate_sq_zero]
  have hx : φ (MvPolynomial.X 0) = 0 := by simp [φ]
  have hspan : originFiberIdeal k ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.mpr
    intro b hb
    rcases hb with rfl | rfl
    · exact hrel
    · exact hx
  exact hspan ha

@[simp] theorem originFiberToDual_y :
    originFiberToDual k (fiberY k) =
      Ideal.Quotient.mk (CuspFiber.fiberIdeal k) (X : k[X]) := by
  change MvPolynomial.aeval
    ![0, Ideal.Quotient.mk (CuspFiber.fiberIdeal k) (X : k[X])]
      (MvPolynomial.X 1) = _
  simp

/-- The fibre coordinate `y` survives despite being square zero. -/
theorem fiberY_ne_zero : fiberY k ≠ 0 := by
  intro h
  have hh := congrArg (originFiberToDual k) h
  simp only [originFiberToDual_y, map_zero] at hh
  exact CuspFiber.coordinate_ne_zero k hh

/-- The projection's fibre over `x = 0` is nonreduced. -/
theorem originFiber_not_isReduced : ¬ IsReduced (OriginFiber k) := by
  intro h
  let := h
  exact fiberY_ne_zero k (IsReduced.eq_zero _ ⟨2, fiberY_sq_zero k⟩)

/-- The actual quotient of the nodal coordinate ring by the projection
origin ideal is nonreduced. -/
theorem projectionOriginFiber_not_isReduced :
    ¬ IsReduced (ProjectionOriginFiber k) := by
  intro h
  letI : IsReduced (ProjectionOriginFiber k) := h
  letI : IsReduced (OriginFiber k) :=
    isReduced_of_injective (projectionOriginFiberEquiv k).symm.toRingHom
      (projectionOriginFiberEquiv k).symm.injective
  exact originFiber_not_isReduced k ‹_›

/-- Pulling back the node's ideal through the parametrization gives the
fibre equations `t² - 1 = 0` and `t³ - t = 0`. -/
noncomputable def normalizationOriginFiberIdeal : Ideal k[X] :=
  Ideal.span {(X : k[X]) ^ 2 - 1, X ^ 3 - X}

noncomputable def nodeIdeal : Ideal (CoordinateRing k) :=
  Ideal.span {Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0),
    Ideal.Quotient.mk (ideal k) (MvPolynomial.X 1)}

theorem nodeIdeal_map :
    Ideal.map (parametrization k).toRingHom (nodeIdeal k) =
      normalizationOriginFiberIdeal k := by
  simp [Ideal.map_span, nodeIdeal, normalizationOriginFiberIdeal]

theorem normalizationOriginFiberIdeal_eq :
    normalizationOriginFiberIdeal k =
      Ideal.span {(X : k[X]) ^ 2 - 1} := by
  unfold normalizationOriginFiberIdeal
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.mem_span_singleton.mpr
      refine ⟨X, ?_⟩
      ring
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact Ideal.subset_span (by simp)

abbrev NormalizationOriginFiber := k[X] ⧸ normalizationOriginFiberIdeal k

/-- The normalization fibre over the node is reduced in characteristic
zero, unlike the projection fibre on the nodal cubic. -/
theorem normalizationOriginFiber_isReduced [CharZero k] :
    IsReduced (NormalizationOriginFiber k) := by
  change IsReduced (k[X] ⧸ normalizationOriginFiberIdeal k)
  rw [normalizationOriginFiberIdeal_eq]
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  apply (isRadical_iff_span_singleton).mp
  apply (isRadical_iff_squarefree_or_zero).mpr
  left
  simpa using (Polynomial.separable_X_pow_sub_C (1 : k)
    (by norm_num : (2 : k) ≠ 0) one_ne_zero).squarefree

#print axioms parametrization_x
#print axioms parametrization_y
#print axioms parametrization_comp_projection
#print axioms normalizationSchemeMap_comp_projectionSchemeMap
#print axioms fiberY_sq_zero
#print axioms fiberY_ne_zero
#print axioms originFiber_not_isReduced
#print axioms projectionOriginFiber_not_isReduced
#print axioms normalizationOriginFiberIdeal_eq
#print axioms nodeIdeal_map
#print axioms normalizationOriginFiber_isReduced

end Pcf.Examples.PaperP.NodalCubic
