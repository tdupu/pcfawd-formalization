/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeExtraction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Reduced point closures on open charts

For `paper-p.tex`, Theorem `thm:tower-restrict`, the affine normalized
blow-up argument takes place on affine charts. The reduced closure of a
point of an open chart is the inverse image of the reduced closure of its
image: the vanishing ideal sheaf pulls back to the vanishing ideal sheaf of
the inverse image along an open immersion. This gives a Cartesian square of
the chart closure, the ambient closure, and the two open immersions.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The vanishing ideal sheaf of a closed set pulls back along an open
immersion to the vanishing ideal sheaf of its inverse image. -/
theorem vanishingIdeal_comap_of_isOpenImmersion {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap j =
      Scheme.IdealSheafData.vanishingIdeal ⟨j ⁻¹' Z, Z.isClosed.preimage j.continuous⟩ := by
  ext U r
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.vanishingIdeal_ideal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  let hU := U.2
  let hjU : IsAffineOpen (j ''ᵁ U.1) := U.2.image_of_isOpenImmersion j
  have hsq : Spec.map (j.appIso U).hom ≫ hjU.fromSpec = hU.fromSpec ≫ j := by
    rw [Scheme.Hom.appIso_hom']
    exact IsAffineOpen.SpecMap_appLE_fromSpec j hjU hU _
  simp only [Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal, Set.mem_preimage]
  constructor
  · intro h p hp
    have hq := h (Spec.map (j.appIso U).hom p) (by
      have := congrArg (fun m => m p) hsq
      simp only [Scheme.Hom.comp_apply] at this
      change hjU.fromSpec (Spec.map (j.appIso U).hom p) ∈ Z
      rw [this]
      exact hp)
    change (j.appIso U).inv.hom r ∈ Ideal.comap (j.appIso U).hom.hom p.asIdeal at hq
    rw [Ideal.mem_comap] at hq
    have hid : (j.appIso U).hom.hom ((j.appIso U).inv.hom r) = r := by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    rwa [hid] at hq
  · intro h q hq
    let p : Spec Γ(V, U) := Spec.map (j.appIso U).inv q
    have hpq : Spec.map (j.appIso U).hom p = q := by
      change (Spec.map (j.appIso U).inv ≫ Spec.map (j.appIso U).hom) q = q
      rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
      rfl
    have hp : j (hU.fromSpec p) ∈ Z := by
      have := congrArg (fun m => m p) hsq
      simp only [Scheme.Hom.comp_apply] at this
      rw [← this, hpq]
      exact hq
    exact h p hp

/-- The reduced closure ideal of the image of a point of an open chart pulls
back to the reduced closure ideal of that point. -/
theorem pointClosureIdealSheaf_comap_of_isOpenImmersion {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (v : V) :
    (pointClosureIdealSheaf (j v)).comap j = pointClosureIdealSheaf v := by
  rw [pointClosureIdealSheaf, pointClosureIdealSheaf,
    vanishingIdeal_comap_of_isOpenImmersion]
  congr 1
  ext1
  change j ⁻¹' closure {j v} = closure {v}
  rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact j.isOpenEmbedding.injective.eq_iff

/-- The reduced closure of a chart point is the inverse image of the ambient
reduced closure: the square of the restricted chart inclusion, the two
closed immersions, and the chart inclusion is Cartesian.

`paper-p.tex` correspondence: Theorem 8.2 (`thm:tower-restrict`). -/
theorem pointClosure_isPullback_of_isOpenImmersion {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (v : V) (x : X) (hx : j v = x) :
    IsPullback (pointClosureIdealSheaf v).subschemeι
      (pointClosureSubschemeMap j v x hx) j
      (pointClosureIdealSheaf x).subschemeι := by
  subst hx
  apply isPullback_of_isClosedImmersion
  · exact (pointClosureSubschemeMap_subschemeι j v (j v) rfl).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    exact pointClosureIdealSheaf_comap_of_isOpenImmersion j v

/-- The restricted chart inclusion of reduced closures is an open immersion. -/
instance pointClosureSubschemeMap_isOpenImmersion {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (v : V) (x : X) (hx : j v = x) :
    IsOpenImmersion (pointClosureSubschemeMap j v x hx) :=
  MorphismProperty.of_isPullback (pointClosure_isPullback_of_isOpenImmersion j v x hx)
    inferInstance

/-- A point of the ambient closure lying over the chart comes from the chart
closure. -/
theorem pointClosure_mem_range_of_isOpenImmersion {V X : Scheme.{u}}
    (j : V ⟶ X) [IsOpenImmersion j] (v : V) (x : X) (hx : j v = x)
    (c : (pointClosureIdealSheaf x).subscheme)
    (hc : (pointClosureIdealSheaf x).subschemeι c ∈ Set.range j) :
    c ∈ Set.range (pointClosureSubschemeMap j v x hx) := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨c', -, hc'⟩ := Scheme.exists_preimage_of_isPullback
    (pointClosure_isPullback_of_isOpenImmersion j v x hx) w c hw
  exact ⟨c', hc'⟩

/-- Restriction to reduced closures carries a commuting chart square to a
commuting chart square. -/
theorem pointClosureSubschemeMap_chart_square {V W X Y : Scheme.{u}}
    (φ : V ⟶ W) (i : V ⟶ X) (j : W ⟶ Y) (f : X ⟶ Y) (hsq : φ ≫ j = i ≫ f)
    (v : V) (w : W) (x : X) (y : Y)
    (hvw : φ v = w) (hvx : i v = x) (hwy : j w = y) (hxy : f x = y) :
    pointClosureSubschemeMap φ v w hvw ≫ pointClosureSubschemeMap j w y hwy =
      pointClosureSubschemeMap i v x hvx ≫ pointClosureSubschemeMap f x y hxy := by
  rw [← cancel_mono (pointClosureIdealSheaf y).subschemeι]
  simp only [Category.assoc, pointClosureSubschemeMap_subschemeι,
    pointClosureSubschemeMap_subschemeι_assoc, hsq]

/-- If the source chart is the full inverse image of the target chart, the
same holds for the restricted maps of reduced closures. -/
theorem pointClosureSubschemeMap_chart_range {V W X Y : Scheme.{u}}
    (i : V ⟶ X) (j : W ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (hrange : ∀ a : X, f a ∈ Set.range j → a ∈ Set.range i)
    (v : V) (w : W) (x : X) (y : Y)
    (hvx : i v = x) (hwy : j w = y) (hxy : f x = y)
    (c : (pointClosureIdealSheaf x).subscheme)
    (hc : pointClosureSubschemeMap f x y hxy c ∈
      Set.range (pointClosureSubschemeMap j w y hwy)) :
    c ∈ Set.range (pointClosureSubschemeMap i v x hvx) := by
  apply pointClosure_mem_range_of_isOpenImmersion
  apply hrange
  obtain ⟨d, hd⟩ := hc
  refine ⟨(pointClosureIdealSheaf w).subschemeι d, ?_⟩
  have h1 := congrArg (fun m => m d) (pointClosureSubschemeMap_subschemeι j w y hwy)
  have h2 := congrArg (fun m => m c) (pointClosureSubschemeMap_subschemeι f x y hxy)
  simp only [Scheme.Hom.comp_apply] at h1 h2
  rw [← h1, hd, h2]

#print axioms vanishingIdeal_comap_of_isOpenImmersion
#print axioms pointClosureIdealSheaf_comap_of_isOpenImmersion
#print axioms pointClosure_isPullback_of_isOpenImmersion
#print axioms pointClosure_mem_range_of_isOpenImmersion

end
end Pcf
