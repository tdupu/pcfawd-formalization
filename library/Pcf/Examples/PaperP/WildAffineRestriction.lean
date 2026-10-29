/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildAffineIndex

/-!
# The actual finite affine restriction in the wild example

The explicit finite-chart map has a commuting restriction square with the
actual closed affine line and `t ↦ t^(p+1)+c`. That return is finite and
surjective. Identifying these affine schemes with the projective source's
canonical divisor and opens remains a separate obligation.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
variable (k : Type*) [Field k] (p : ℕ) (c : k)

/-- The actual affine-plane morphism defined by the finite-chart formulas. -/
noncomputable def affineSchemeMap : Spec (.of (AffinePlane k)) ⟶ Spec (.of (AffinePlane k)) :=
  Spec.map (CommRingCat.ofHom (affineCoordinateMap k p c).toRingHom)

/-- The actual affine-line scheme return. -/
noncomputable def returnSchemeMap : Spec (.of k[X]) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (returnCoordinateMap k p c).toRingHom)

/-- The scheme restriction square uses the actual closed affine-line embedding. -/
theorem affine_restriction_scheme_square (hp : 0 < p) :
    FrobeniusLine.lineEmbedding k ≫ affineSchemeMap k p c =
      returnSchemeMap k p c ≫ FrobeniusLine.lineEmbedding k := by
  unfold FrobeniusLine.lineEmbedding affineSchemeMap returnSchemeMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : AffinePlane k →ₐ[k] k[X] =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (affine_restriction_coordinate_square k p c hp)

/-- The return factors as a positive-degree power followed by a target translation. -/
theorem returnCoordinateMap_factor :
    returnCoordinateMap k p c = (FrobeniusLine.lineCoordinateMap k (p + 1)).comp
      (algEquivAevalXAddC c).toAlgHom := by
  apply Polynomial.algHom_ext
  simp [returnCoordinateMap, returnPolynomial, FrobeniusLine.lineCoordinateMap,
    algEquivAevalXAddC_apply]

/-- The actual return coordinate-ring pullback is finite. -/
theorem returnCoordinateMap_finite (hp : 0 < p) :
    (returnCoordinateMap k p c).toRingHom.Finite := by
  rw [returnCoordinateMap_factor]
  exact (FrobeniusLine.lineCoordinateMap_finite k (p + 1) (by omega)).comp
    (RingHom.Finite.of_surjective _ (algEquivAevalXAddC c).surjective)

/-- The actual affine-line return morphism is finite. -/
theorem returnSchemeMap_finite (hp : 0 < p) : IsFinite (returnSchemeMap k p c) :=
  (IsFinite.SpecMap_iff _).mpr (returnCoordinateMap_finite k p c hp)

/-- The actual affine-line return is surjective on all scheme points. -/
theorem returnSchemeMap_surjective (hp : 0 < p) : Surjective (returnSchemeMap k p c) := by
  rw [surjective_iff]
  exact (returnCoordinateMap_finite k p c hp).to_isIntegral.comap_surjective
    (returnCoordinateMap_injective k p c)

#print axioms affine_restriction_scheme_square
#print axioms returnCoordinateMap_factor
#print axioms returnCoordinateMap_finite
#print axioms returnSchemeMap_finite
#print axioms returnSchemeMap_surjective
end Pcf.Examples.PaperP.Wild
