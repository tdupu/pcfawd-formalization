/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingRestriction

/-!
# Reduced point closures as images of closed immersions

On an arbitrary scheme `X`, the canonical reduced subscheme of the closure of a
point is the scheme-theoretic image of every closed immersion from a reduced
scheme whose image is that closure. In particular such a closed immersion is
canonically isomorphic, over `X`, to the reduced point-closure subscheme. This
removes the affineness hypothesis from the corresponding affine statement.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Pcf.PaperCharZero

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of a closed immersion from a reduced scheme is radical. -/
theorem ker_radical_le_of_isReduced {X Z : Scheme.{u}} [IsReduced Z]
    (i : Z ⟶ X) [IsClosedImmersion i] : i.ker.radical ≤ i.ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U a ha
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply] at ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  obtain ⟨m, hm⟩ := ha
  rw [RingHom.mem_ker, map_pow] at hm
  exact IsReduced.eq_zero _ ⟨m, hm⟩

set_option backward.isDefEq.respectTransparency false in
/-- The reduced closure ideal sheaf of a point is the kernel of any closed
immersion of a reduced scheme with image the closure of that point. -/
theorem pointClosureIdealSheaf_eq_ker_of_isReduced {X Z : Scheme.{u}} [IsReduced Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (x : X) (hx : Set.range i = closure {x}) :
    pointClosureIdealSheaf x = i.ker := by
  have hsupp : i.ker.support = ⟨closure {x}, isClosed_closure⟩ := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq, hx]
    rfl
  rw [pointClosureIdealSheaf, ← hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
  exact le_antisymm (ker_radical_le_of_isReduced i) (Scheme.IdealSheafData.le_radical _)

/-- A closed immersion of a reduced scheme onto the closure of a point is
canonically isomorphic to the reduced point-closure subscheme. -/
noncomputable def closureSubschemeIsoOfIsReduced {X Z : Scheme.{u}} [IsReduced Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (x : X) (hx : Set.range i = closure {x}) :
    Z ≅ (pointClosureIdealSheaf x).subscheme :=
  have h : (pointClosureIdealSheaf x).subschemeι.ker = i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, pointClosureIdealSheaf_eq_ker_of_isReduced i x hx]
  have := IsClosedImmersion.isIso_lift (pointClosureIdealSheaf x).subschemeι i h
  asIso (IsClosedImmersion.lift (pointClosureIdealSheaf x).subschemeι i h.le)

@[reassoc (attr := simp)]
theorem closureSubschemeIsoOfIsReduced_hom_ι {X Z : Scheme.{u}} [IsReduced Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (x : X) (hx : Set.range i = closure {x}) :
    (closureSubschemeIsoOfIsReduced i x hx).hom ≫ (pointClosureIdealSheaf x).subschemeι = i := by
  simp [closureSubschemeIsoOfIsReduced]

#print axioms ker_radical_le_of_isReduced
#print axioms pointClosureIdealSheaf_eq_ker_of_isReduced
#print axioms closureSubschemeIsoOfIsReduced
#print axioms closureSubschemeIsoOfIsReduced_hom_ι

end Pcf.PaperCharZero
