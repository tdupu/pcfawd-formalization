/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeRestriction
/-!
# The affine basilica scheme map

For `latex/paper-p.tex`, Example `ex:basilica`, this module constructs the
actual affine scheme map with coordinate pullback `t ↦ t²-1`, proves it is
finite and surjective, and checks its `0 ↔ -1` orbit at scheme points.
The nonreduced fibre at `-1` is the quotient `k[t]/(t²)`.

This is the finite affine chart of the projective map. It does not construct
its projective extension or identify the projective critical/branch loci.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
namespace Pcf.Examples.PaperP.BasilicaAffine
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
variable (k : Type*) [Field k]
/-- Coordinate pullback for the finite affine basilica chart. -/
noncomputable def coordinateMap : k[X] →ₐ[k] k[X] := aeval (X ^ 2 - 1)
@[simp] theorem coordinateMap_X : coordinateMap k X = (X : k[X]) ^ 2 - 1 := by
  simp [coordinateMap]

/-- The pullback factors as squaring after a target translation. -/
theorem coordinateMap_eq_square_comp_translation :
    coordinateMap k = (QuadricConeRestriction.coordinateMap k).comp
      (algEquivAevalXAddC (-1 : k)).toAlgHom := by
  ext
  simp [coordinateMap, algEquivAevalXAddC_apply, sub_eq_add_neg]

/-- The affine coordinate-ring map is finite. -/
theorem coordinateMap_finite : (coordinateMap k).toRingHom.Finite := by
  rw [coordinateMap_eq_square_comp_translation]
  exact (QuadricConeRestriction.coordinateMap_finite k).comp
    (RingHom.Finite.of_surjective _ (algEquivAevalXAddC (-1 : k)).surjective)

/-- The affine coordinate-ring map is injective. -/
theorem coordinateMap_injective : Function.Injective (coordinateMap k) := by
  rw [coordinateMap_eq_square_comp_translation]
  exact (QuadricConeRestriction.coordinateMap_injective k).comp
    (algEquivAevalXAddC (-1 : k)).injective

/-- The actual affine-line scheme morphism. -/
noncomputable def schemeMap : Spec (.of k[X]) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (coordinateMap k).toRingHom)
/-- The actual affine-line scheme morphism is finite.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem schemeMap_finite : IsFinite (schemeMap k) :=
  (IsFinite.SpecMap_iff _).mpr (coordinateMap_finite k)
/-- Every scheme point of the target has a preimage.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem schemeMap_surjective : Surjective (schemeMap k) := by
  rw [surjective_iff]
  exact (coordinateMap_finite k).to_isIntegral.comap_surjective (coordinateMap_injective k)

/-- The rational closed point with parameter value `a`. -/
noncomputable def closedPoint (a : k) : Spec (.of k[X]) :=
  ⟨RingHom.ker (evalRingHom a),
    (RingHom.ker_isMaximal_of_surjective (evalRingHom a)
      (fun b => ⟨C b, by simp⟩)).isPrime⟩

/-- The scheme map evaluates rational closed points by `a ↦ a²-1`. -/
theorem schemeMap_closedPoint (a : k) :
    schemeMap k (closedPoint k a) = closedPoint k (a ^ 2 - 1) := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro p
  change (coordinateMap k p).eval a = 0 ↔ p.eval (a ^ 2 - 1) = 0
  rw [coordinateMap, ← comp_eq_aeval, eval_comp]
  simp

/-- The source origin maps to the target point `-1`. -/
theorem zero_to_minusOne : schemeMap k (closedPoint k 0) = closedPoint k (-1) := by
  simpa using schemeMap_closedPoint k 0

/-- The scheme point `-1` returns to the origin. -/
theorem minusOne_to_zero : schemeMap k (closedPoint k (-1)) = closedPoint k 0 := by
  simpa using schemeMap_closedPoint k (-1)

/-- Different parameter values define different scheme points. -/
theorem closedPoint_injective : Function.Injective (closedPoint k) := by
  intro a b h
  have ha : X - C a ∈ (closedPoint k a).asIdeal := by
    change (X - C a).eval a = 0
    simp
  rw [h] at ha
  change (X - C a).eval b = 0 at ha
  have hh : b - a = 0 := by simpa using ha
  exact (sub_eq_zero.mp hh).symm

/-- The scheme point `0` has exact period two.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem zero_exact_period_two :
    (schemeMap k)^[2] (closedPoint k 0) = closedPoint k 0 ∧
    schemeMap k (closedPoint k 0) ≠ closedPoint k 0 := by
  constructor
  · simp [Function.iterate_succ_apply, zero_to_minusOne, minusOne_to_zero]
  · rw [zero_to_minusOne]
    exact fun h => neg_ne_zero.mpr one_ne_zero (closedPoint_injective k h)

/-- The extended ideal of the target point `-1` is `(t²)`. -/
theorem minusOne_fiberIdeal :
    Ideal.map (coordinateMap k).toRingHom (RingHom.ker (evalRingHom (-1 : k))) =
      CuspFiber.fiberIdeal k := by
  rw [ker_evalRingHom, CuspFiber.fiberIdeal_eq, Ideal.map_span]
  simp [coordinateMap_X, Set.image_singleton]

/-- The original fibre over `-1` is nonreduced. -/
theorem minusOne_fiber_not_isReduced :
    ¬ IsReduced (k[X] ⧸ Ideal.map (coordinateMap k).toRingHom
      (RingHom.ker (evalRingHom (-1 : k)))) := by
  rw [minusOne_fiberIdeal]
  exact CuspFiber.fiber_not_isReduced k
#print axioms coordinateMap_finite
#print axioms coordinateMap_injective
#print axioms schemeMap_finite
#print axioms schemeMap_surjective
#print axioms schemeMap_closedPoint
#print axioms zero_exact_period_two
#print axioms minusOne_fiberIdeal
#print axioms minusOne_fiber_not_isReduced

end Pcf.Examples.PaperP.BasilicaAffine
