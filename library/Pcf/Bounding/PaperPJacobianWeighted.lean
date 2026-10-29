/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianGlobalEtale
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian
public import Pcf.Bounding.PaperPProjectiveDominant

/-!
# The normalized weighted critical locus and the homogeneous Jacobian

These assembly lemmas use the actual normalization and weighted divisor
degree. Integrality, normality and local Noetherianity of projective space
are proved in the imported concrete geometry modules, as are finiteness and
dominance of the constructed global map. This file does
not identify the final closure with codimension-one components.
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance : IsIso (Palomar.normalizationMap
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K))) :=
  normalScheme_normalizationMap_isIso
    (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K))

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : PaperPFormsCoverProjective F)

/-- The actual weighted local
degree exceeds one exactly at the codimension-one zeros of the Jacobian.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_weightedCriticalDivisors_eq (hdK : (d : K) ≠ 0) :
    {x : SchemeDivisorPoint
        (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)) |
      1 < schemeDivisorDelta (paperPFormsProjectiveSchemeMap F d hd hF hcover) x} =
      {x : SchemeDivisorPoint
          (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)) |
        Matrix.det (fun i j => pderiv j (F i)) ∈ x.1.asHomogeneousIdeal} := by
  rw [schemeDivisorWeightedCritical_eq_nonEtale,
    paperPFormsProjective_divisorNonEtaleLocus_eq F d hd hF hcover hdK]

/-- Projected critical divisor
points on the actual normalization are precisely the codimension-one
projective zeros of the original homogeneous Jacobian. -/
theorem paperPFormsProjective_normalizedCriticalPointSet_eq (hdK : (d : K) ≠ 0) :
    weightedCriticalPointSet (paperPFormsProjectiveSchemeMap F d hd hF hcover) =
      {x : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K) |
        Order.coheight x = 1 ∧
        Matrix.det (fun i j => pderiv j (F i)) ∈ x.asHomogeneousIdeal} := by
  rw [weightedCriticalPointSet_eq_schemeDelta_of_normal,
    paperPFormsProjective_weightedCriticalDivisors_eq F d hd hF hcover hdK]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hJ⟩
    exact ⟨⟨x, hx⟩, hJ, rfl⟩

/-- The actual normalized
weighted critical locus is the closure of the codimension-one zeros of
the homogeneous Jacobian. The remaining component assertion is topological.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_normalizedCriticalLocus_eq_closure (hdK : (d : K) ≠ 0) :
    weightedCriticalLocus (paperPFormsProjectiveSchemeMap F d hd hF hcover) =
      closure {x : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K) |
        Order.coheight x = 1 ∧
        Matrix.det (fun i j => pderiv j (F i)) ∈ x.asHomogeneousIdeal} := by
  unfold weightedCriticalLocus
  rw [paperPFormsProjective_normalizedCriticalPointSet_eq F d hd hF hcover hdK]

#print axioms paperPFormsProjective_weightedCriticalDivisors_eq
#print axioms paperPFormsProjective_normalizedCriticalPointSet_eq
#print axioms paperPFormsProjective_normalizedCriticalLocus_eq_closure
end Pcf
