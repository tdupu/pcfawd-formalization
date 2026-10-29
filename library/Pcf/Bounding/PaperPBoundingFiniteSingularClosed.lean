/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingFiniteSingularCharP
public import Pcf.Bounding.RegularLocusGenerization

/-!
# Closed singular loci in the one-dimensional case

The full closedness assertion in `paper-p.tex`, Theorem `thm:bounding`,
requires openness of the regular locus of an arbitrary finite-type scheme
over a field. Here we prove the useful special case in which every singular
point is an integral effective divisor generic point. This is the
one-dimensional situation. The proof combines the existing finiteness of
singular divisor points with stability under specialization.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

/-- A finite specialization-stable set is closed in any topological space. -/
theorem isClosed_of_finite_of_stableUnderSpecialization
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (hfinite : S.Finite) (hstable : StableUnderSpecialization S) : IsClosed S := by
  rw [← hstable.Union_eq]
  exact hfinite.isClosed_biUnion (fun _ _ => isClosed_closure)

/-- The singular locus of an integral finite-type scheme is closed when all
its singular points have codimension one. In particular this covers curves.
The unrestricted finite-type regular-locus theorem remains separate. -/
theorem isClosed_stalkSingularLocus_of_finiteType_of_singular_codimOne
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hcodim : ∀ x ∈ stalkSingularLocus X, Order.coheight x = 1) :
    IsClosed (stalkSingularLocus X) := by
  have hdiv : {Q : SchemeDivisorPoint X | Q.1 ∈ stalkSingularLocus X}.Finite :=
    finite_schemeDivisorPoint_stalkSingularLocus_of_finiteType k s
  have hEq :
      (fun Q : SchemeDivisorPoint X => Q.1) ''
        {Q : SchemeDivisorPoint X | Q.1 ∈ stalkSingularLocus X} =
          stalkSingularLocus X := by
    ext x
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact hQ
    · intro hx
      exact ⟨⟨x, hcodim x hx⟩, hx, rfl⟩
  have hfinite : (stalkSingularLocus X).Finite := by
    rw [← hEq]
    exact hdiv.image _
  exact isClosed_of_finite_of_stableUnderSpecialization hfinite
    (stalkSingularLocus_specialization_closed X)

#print axioms isClosed_of_finite_of_stableUnderSpecialization
#print axioms isClosed_stalkSingularLocus_of_finiteType_of_singular_codimOne

end Pcf
