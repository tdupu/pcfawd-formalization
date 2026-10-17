/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AffineStalkBridge
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Extracting affine divisor charts from actual scheme morphisms

This file connects a finite dominant morphism on affine neighborhoods to the pointed
finite-normal divisor chart. It constructs the affine preimage, finite faithful section
algebra, the four prime ideals attached to an actual closed-subscheme point, and the
comparison between the actual stalk arrow and the corresponding affine quotient arrow.
It also identifies the ambient localization and localized divisor quotient with the
actual ambient and divisor stalks, allowing the strongest constructor to transport
regularity and codimension and to choose the local equation itself.
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Pcf

set_option linter.style.haveILetI false

open LocalBoundingChart

/-- Restricting a quasi-finite quasi-compact morphism to codimension-one points gives
finite fibers whenever its images have codimension one.  The explicit subtype map
allows downstream divisor-dynamics constructors to use this without an import cycle. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_subtype_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f]
    (hcodim : ∀ x : SchemeDivisorPoint X, Order.coheight (f x.1) = 1)
    (y : SchemeDivisorPoint Y) :
    ((fun x : SchemeDivisorPoint X ↦
      (⟨f x.1, hcodim x⟩ : SchemeDivisorPoint Y)) ⁻¹' {y}).Finite := by
  refine (AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_fiber f y.1).subset ?_
  intro x hx
  exact congrArg Subtype.val hx

/-- A scheme is normal in the affine-coordinate sense used by the divisor bridge. -/
class IsNormalScheme (X : Scheme.{u}) : Prop where
  component_integrallyClosed : ∀ U : X.affineOpens, IsIntegrallyClosed Γ(X, U)

attribute [instance] IsNormalScheme.component_integrallyClosed

/-- The set of scheme points whose local rings are not regular.  This is the
pointwise definition of the singular locus used in Step 0; no openness or
closedness assertion is built into the definition. -/
def stalkSingularLocus (X : Scheme.{u}) : Set X :=
  {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}

/-- A point outside the pointwise singular locus has a regular local ring. -/
theorem isRegularLocalRing_stalk_of_notMem_stalkSingularLocus
    {X : Scheme.{u}} {x : X} (hx : x ∉ stalkSingularLocus X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  classical
  simpa only [stalkSingularLocus, Set.mem_ofPred_eq, not_not] using hx

/-- The reduced ideal sheaf of the closure of a scheme point.  When the point has
codimension one, this is the canonical reduced integral divisor carried by that point. -/
noncomputable def pointClosureIdealSheaf {X : Scheme.{u}} (x : X) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({x} : Set X), isClosed_closure⟩

set_option backward.isDefEq.respectTransparency false in
/-- On an affine neighborhood of a point, its closure ideal sheaf is represented by
the prime ideal corresponding to that point. -/
theorem pointClosureIdealSheaf_ideal {X : Scheme.{u}} (x : X)
    (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    (pointClosureIdealSheaf x).ideal U =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let hU : IsAffineOpen (U : X.Opens) := U.2
  change (pointClosureIdealSheaf x).ideal U =
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let φ : PrimeSpectrum Γ(X, U) → X := fun p ↦ hU.fromSpec p
  have hφopen : Topology.IsOpenEmbedding φ :=
    hU.fromSpec.isOpenEmbedding
  have hφcontinuous : Continuous φ := hU.fromSpec.continuous
  have hcomponent : (pointClosureIdealSheaf x).ideal U =
      PrimeSpectrum.vanishingIdeal
        (φ ⁻¹' closure ({x} : Set X)) := by
    rw [pointClosureIdealSheaf, Scheme.IdealSheafData.vanishingIdeal_ideal]
    congr 2
  rw [hcomponent]
  rw [hφopen.isOpenMap.preimage_closure_eq_closure_preimage hφcontinuous]
  have hpreimage : φ ⁻¹' ({x} : Set X) =
      {hU.primeIdealOf ⟨x, hx⟩} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp
      apply hφopen.injective
      change hU.fromSpec p = hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)
      rw [hU.fromSpec_primeIdealOf]
      exact hp
    · intro hp
      subst p
      exact hU.fromSpec_primeIdealOf ⟨x, hx⟩
  rw [hpreimage, PrimeSpectrum.vanishingIdeal_closure,
    PrimeSpectrum.vanishingIdeal_singleton]

theorem pointClosureIdealSheaf_ideal_isPrime {X : Scheme.{u}} (x : X)
    (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    ((pointClosureIdealSheaf x).ideal U).IsPrime := by
  rw [pointClosureIdealSheaf_ideal x U hx]
  infer_instance

/-- The closure ideal of a codimension-one point has height one on every affine
neighborhood of that point. -/
theorem pointClosureIdealSheaf_ideal_height (x : SchemeDivisorPoint X)
    (U : X.affineOpens) (hx : x.1 ∈ (U : X.Opens)) :
    ((pointClosureIdealSheaf x.1).ideal U).height = 1 := by
  rw [pointClosureIdealSheaf_ideal x.1 U hx]
  let hU : IsAffineOpen (U : X.Opens) := U.2
  let p : AlgebraicGeometry.Spec Γ(X, U) :=
    hU.primeIdealOf ⟨x.1, hx⟩
  change p.asIdeal.height = 1
  have hcoheight : Order.coheight p = Order.coheight x.1 := by
    symm
    have h := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
      (x := p) hU.fromSpec
    simpa only [p, hU.fromSpec_primeIdealOf] using h
  exact (AlgebraicGeometry.idealHeight_eq_coheight Γ(X, U) p).trans
    (hcoheight.trans x.2)

/-- Taking the reduced closure ideal of a point commutes with scheme morphisms.  This
is the scheme-theoretic form of the fact that a continuous map sends the closure of a
point densely onto the closure of its image point. -/
theorem pointClosureIdealSheaf_map {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (pointClosureIdealSheaf x).map f = pointClosureIdealSheaf (f x) := by
  rw [pointClosureIdealSheaf, Scheme.IdealSheafData.map_vanishingIdeal,
    pointClosureIdealSheaf]
  congr 1
  ext y
  change y ∈ closure (f '' closure ({x} : Set X)) ↔
    y ∈ closure ({f x} : Set Y)
  rw [closure_image_closure f.continuous, Set.image_singleton]

/-- The target point-closure ideal maps into the source point-closure ideal whenever
the chosen points lie over one another.  In fact the two ideal sheaves are equal after
mapping; the inequality is the orientation required by `subschemeMap`. -/
theorem pointClosureIdealSheaf_le_map_of_apply_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    pointClosureIdealSheaf y ≤ (pointClosureIdealSheaf x).map f := by
  subst y
  exact (pointClosureIdealSheaf_map f x).ge

/-- The canonical map between the reduced point-closure subschemes of two points lying
over one another. -/
noncomputable def pointClosureSubschemeMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    (pointClosureIdealSheaf x).subscheme ⟶
      (pointClosureIdealSheaf y).subscheme :=
  (pointClosureIdealSheaf x).subschemeMap
    (pointClosureIdealSheaf y) f
    (pointClosureIdealSheaf_le_map_of_apply_eq f x y hxy)

@[reassoc]
theorem pointClosureSubschemeMap_subschemeι {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    pointClosureSubschemeMap f x y hxy ≫
        (pointClosureIdealSheaf y).subschemeι =
      (pointClosureIdealSheaf x).subschemeι ≫ f := by
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf y
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f x y hxy
  change I.subschemeMap J f H ≫ J.subschemeι = I.subschemeι ≫ f
  exact I.subschemeMap_subschemeι J f H

/-- Restriction to reduced point closures respects composition.  The equality proofs
identifying the three generic points carry no extra data. -/
theorem pointClosureSubschemeMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (y : Y) (z : Z)
    (hxy : f x = y) (hyz : g y = z) (hxz : (f ≫ g) x = z) :
    pointClosureSubschemeMap f x y hxy ≫
        pointClosureSubschemeMap g y z hyz =
      pointClosureSubschemeMap (f ≫ g) x z hxz := by
  apply (cancel_mono (pointClosureIdealSheaf z).subschemeι).mp
  rw [Category.assoc, pointClosureSubschemeMap_subschemeι,
    ← Category.assoc, pointClosureSubschemeMap_subschemeι,
    pointClosureSubschemeMap_subschemeι, Category.assoc]

/-- Restricting the identity morphism to a reduced point closure gives the identity. -/
@[simp]
theorem pointClosureSubschemeMap_id {X : Scheme.{u}} (x : X)
    (hxx : (𝟙 X) x = x) :
    pointClosureSubschemeMap (𝟙 X) x x hxx =
      𝟙 (pointClosureIdealSheaf x).subscheme := by
  apply (cancel_mono (pointClosureIdealSheaf x).subschemeι).mp
  simp only [pointClosureSubschemeMap_subschemeι, Category.id_comp,
    Category.comp_id]

/-- A fixed point of an endomorphism is fixed by every categorical iterate. -/
theorem end_pow_apply_eq_of_apply_eq {X : Scheme.{u}} (f : X ⟶ X)
    (x : X) (hfx : f x = x) (m : ℕ) :
    (CategoryTheory.End.of f ^ m).asHom.base x = x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      change (f ≫ (CategoryTheory.End.of f ^ m).asHom) x = x
      rw [Scheme.Hom.comp_apply, hfx, ih]

/-- The `m`-th iterate of the restricted invariant-divisor morphism still commutes
with the ambient `m`-th iterate. -/
theorem pointClosureSubschemeMap_iterate_subschemeι {X : Scheme.{u}}
    (f : X ⟶ X) (x : X) (hfx : f x = x) (m : ℕ) :
    (CategoryTheory.End.of (pointClosureSubschemeMap f x x hfx) ^ m).asHom ≫
        (pointClosureIdealSheaf x).subschemeι =
      (pointClosureIdealSheaf x).subschemeι ≫
        (CategoryTheory.End.of f ^ m).asHom := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, pow_succ]
      change
        (pointClosureSubschemeMap f x x hfx ≫
            (CategoryTheory.End.of (pointClosureSubschemeMap f x x hfx) ^ m).asHom) ≫
            (pointClosureIdealSheaf x).subschemeι =
          (pointClosureIdealSheaf x).subschemeι ≫
            (f ≫ (CategoryTheory.End.of f ^ m).asHom)
      rw [Category.assoc, ih, ← Category.assoc,
        pointClosureSubschemeMap_subschemeι, Category.assoc]

/-- Iterating the restriction to an invariant reduced point closure is literally the
restriction of the ambient iterate.  This is the global identification needed before
applying the specified-source-point Step-0 chart constructor. -/
theorem pointClosureSubschemeMap_iterate {X : Scheme.{u}}
    (f : X ⟶ X) (x : X) (hfx : f x = x) (m : ℕ) :
    (CategoryTheory.End.of (pointClosureSubschemeMap f x x hfx) ^ m).asHom =
      pointClosureSubschemeMap (CategoryTheory.End.of f ^ m).asHom x x
        (end_pow_apply_eq_of_apply_eq f x hfx m) := by
  apply (cancel_mono (pointClosureIdealSheaf x).subschemeι).mp
  rw [pointClosureSubschemeMap_iterate_subschemeι,
    pointClosureSubschemeMap_subschemeι]

/-- Every categorical iterate of a finite scheme endomorphism is finite. -/
theorem isFinite_end_pow {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f]
    (m : ℕ) : IsFinite (CategoryTheory.End.of f ^ m).asHom := by
  induction m with
  | zero => simpa using (inferInstance : IsFinite (𝟙 X))
  | succ m ih =>
      rw [pow_succ]
      letI : IsFinite (CategoryTheory.End.of f ^ m).asHom := ih
      change IsFinite (f ≫ (CategoryTheory.End.of f ^ m).asHom)
      infer_instance

/-- Every categorical iterate of a dominant scheme endomorphism is dominant. -/
theorem isDominant_end_pow {X : Scheme.{u}} (f : X ⟶ X) [IsDominant f]
    (m : ℕ) : IsDominant (CategoryTheory.End.of f ^ m).asHom := by
  induction m with
  | zero => simpa using (inferInstance : IsDominant (𝟙 X))
  | succ m ih =>
      rw [pow_succ]
      letI : IsDominant (CategoryTheory.End.of f ^ m).asHom := ih
      change IsDominant (f ≫ (CategoryTheory.End.of f ^ m).asHom)
      infer_instance

attribute [instance low] isFinite_end_pow isDominant_end_pow

/-- The height-one prime on an affine neighborhood canonically represented by a
scheme divisor point. -/
noncomputable def affinePrimeOfSchemeDivisorPoint {X : Scheme.{u}}
    (x : SchemeDivisorPoint X) (U : X.affineOpens)
    (hx : x.1 ∈ (U : X.Opens)) : HeightOnePrime Γ(X, U) :=
  ⟨⟨(pointClosureIdealSheaf x.1).ideal U,
      pointClosureIdealSheaf_ideal_isPrime x.1 U hx⟩,
    pointClosureIdealSheaf_ideal_height x U hx⟩

@[simp]
theorem affinePrimeOfSchemeDivisorPoint_asIdeal {X : Scheme.{u}}
    (x : SchemeDivisorPoint X) (U : X.affineOpens)
    (hx : x.1 ∈ (U : X.Opens)) :
    (affinePrimeOfSchemeDivisorPoint x U hx).1.asIdeal =
      (pointClosureIdealSheaf x.1).ideal U :=
  rfl

/-- An ambient point in the closure of `x` has a lift to the reduced point-closure
subscheme. -/
theorem exists_pointClosureSubschemePoint {X : Scheme.{u}} (x y : X)
    (hy : y ∈ closure ({x} : Set X)) :
    ∃ z : (pointClosureIdealSheaf x).subscheme,
      (pointClosureIdealSheaf x).subschemeι z = y := by
  have hsupport : y ∈ (pointClosureIdealSheaf x).support := by
    change y ∈
      (⟨closure ({x} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
    exact hy
  have hrange : y ∈ Set.range (pointClosureIdealSheaf x).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hsupport
  exact Set.mem_range.mp hrange

/-- Lift an ambient point lying in the closure of `x` to the reduced point-closure
subscheme.  This turns the ordinary incidence `y ∈ closure {x}` into the actual
closed-subscheme point required by the stalk bridge. -/
noncomputable def pointClosureSubschemePoint {X : Scheme.{u}} (x y : X)
    (hy : y ∈ closure ({x} : Set X)) : (pointClosureIdealSheaf x).subscheme :=
  Classical.choose (exists_pointClosureSubschemePoint x y hy)

@[simp]
theorem pointClosureSubschemePoint_subschemeι {X : Scheme.{u}} (x y : X)
    (hy : y ∈ closure ({x} : Set X)) :
    (pointClosureIdealSheaf x).subschemeι
      (pointClosureSubschemePoint x y hy) = y := by
  exact Classical.choose_spec (exists_pointClosureSubschemePoint x y hy)

/-- A morphism sends a point lying in the closure of `x` into the closure of the image
point. -/
theorem image_mem_pointClosure {X Y : Scheme.{u}} (f : X ⟶ Y) (x z : X)
    (hz : z ∈ closure ({x} : Set X)) :
    f z ∈ closure ({f x} : Set Y) := by
  have h := (image_closure_subset_closure_image
    (f := f) (s := ({x} : Set X)) f.continuous) ⟨z, hz, rfl⟩
  simpa only [Set.image_singleton] using h

/-- The canonical restricted morphism carries the lifted ambient point to the lifted
image point.  Both lifts are forced because the closed-subscheme immersions are
embeddings. -/
theorem pointClosureSubschemeMap_point {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y)
    (z : X) (hz : z ∈ closure ({x} : Set X)) :
    let hyz : f z ∈ closure ({y} : Set Y) := by
      rw [← hxy]
      exact image_mem_pointClosure f x z hz
    pointClosureSubschemeMap f x y hxy
        (pointClosureSubschemePoint x z hz) =
      pointClosureSubschemePoint y (f z) hyz := by
  dsimp only
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf y
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f x y hxy
  let sourcePoint := pointClosureSubschemePoint x z hz
  let hyz : f z ∈ closure ({y} : Set Y) := by
    rw [← hxy]
    exact image_mem_pointClosure f x z hz
  let targetPoint := pointClosureSubschemePoint y (f z) hyz
  change (I.subschemeMap J f H) sourcePoint = targetPoint
  apply (J.subschemeι.isEmbedding.injective)
  change ((I.subschemeMap J f H ≫ J.subschemeι) sourcePoint) =
    J.subschemeι targetPoint
  rw [I.subschemeMap_subschemeι J f H]
  change f (I.subschemeι sourcePoint) = J.subschemeι targetPoint
  rw [show I.subschemeι sourcePoint = z by
    simpa only [I, sourcePoint] using
      pointClosureSubschemePoint_subschemeι x z hz]
  exact (by
    simpa only [J, targetPoint] using
      (pointClosureSubschemePoint_subschemeι y (f z) hyz).symm)

/-- The restricted map between reduced point closures of two points lying over one
another is finite whenever the ambient morphism is finite. -/
theorem pointClosureSubschemeMap_isFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) (y : Y) (hxy : f x = y) :
    IsFinite (pointClosureSubschemeMap f x y hxy) := by
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf y
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f x y hxy
  let g := I.subschemeMap J f H
  change IsFinite g
  letI : IsFinite (g ≫ J.subschemeι) := by
    rw [I.subschemeMap_subschemeι J f H]
    infer_instance
  exact IsFinite.of_comp g J.subschemeι

/-- Every point of a reduced point-closure subscheme maps into the closure support in
the ambient scheme. -/
theorem pointClosureSubschemeι_mem {X : Scheme.{u}} (x : X)
    (z : (pointClosureIdealSheaf x).subscheme) :
    (pointClosureIdealSheaf x).subschemeι z ∈ closure ({x} : Set X) := by
  have hsupport : (pointClosureIdealSheaf x).subschemeι z ∈
      (pointClosureIdealSheaf x).support := by
    have hrange : (pointClosureIdealSheaf x).subschemeι z ∈
        Set.range (pointClosureIdealSheaf x).subschemeι := ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at hrange
    exact hrange
  change (pointClosureIdealSheaf x).subschemeι z ∈
    (⟨closure ({x} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
    at hsupport
  exact hsupport

/-- If a point of a reduced point closure lies in an open affine, then its generic
point lies in that affine. -/
theorem SchemeDivisorPoint.mem_affine_of_pointClosurePoint_mem
    {X : Scheme.{u}} (A : SchemeDivisorPoint X) (U : X.affineOpens)
    (z : (pointClosureIdealSheaf A.1).subscheme)
    (hzU : (pointClosureIdealSheaf A.1).subschemeι z ∈ (U : X.Opens)) :
    A.1 ∈ (U : X.Opens) := by
  apply specializes_iff_forall_open.mp
    (specializes_iff_mem_closure.mpr (pointClosureSubschemeι_mem A.1 z))
  · exact (U : X.Opens).2
  · exact hzU

/-- The restricted map between reduced point closures is dominant. -/
theorem pointClosureSubschemeMap_isDominant {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    IsDominant (pointClosureSubschemeMap f x y hxy) := by
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf y
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f x y hxy
  let g := I.subschemeMap J f H
  change IsDominant g
  have hsquare (w : I.subscheme) :
      J.subschemeι (g w) = f (I.subschemeι w) := by
    change (g ≫ J.subschemeι) w = (I.subschemeι ≫ f) w
    rw [I.subschemeMap_subschemeι J f H]
  have himage : J.subschemeι '' Set.range g =
      f '' closure ({x} : Set X) := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨I.subschemeι w, ?_, ?_⟩
      · simpa only [I] using pointClosureSubschemeι_mem x w
      · exact (hsquare w).symm
    · rintro ⟨a, ha, rfl⟩
      let w := pointClosureSubschemePoint x a ha
      refine ⟨g w, ⟨w, rfl⟩, ?_⟩
      calc
        J.subschemeι (g w) = f (I.subschemeι w) := hsquare w
        _ = f a := congrArg f (by
          simpa only [I, w] using
            pointClosureSubschemePoint_subschemeι x a ha)
  constructor
  rw [denseRange_iff_closure_range,
    J.subschemeι.isEmbedding.closure_eq_preimage_closure_image]
  apply Set.eq_univ_of_forall
  intro z
  change J.subschemeι z ∈ closure (J.subschemeι '' Set.range g)
  rw [himage, closure_image_closure f.continuous, Set.image_singleton, hxy]
  simpa only [J] using pointClosureSubschemeι_mem y z

/-- A finite ambient morphism induces a surjective map between the reduced closures of a
point and its image. -/
theorem pointClosureSubschemeMap_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) (y : Y) (hxy : f x = y) :
    Function.Surjective (pointClosureSubschemeMap f x y hxy) := by
  let g := pointClosureSubschemeMap f x y hxy
  letI : IsFinite g := pointClosureSubschemeMap_isFinite f x y hxy
  letI : IsDominant g := pointClosureSubschemeMap_isDominant f x y hxy
  exact g.surjective

/-- A chosen point above a point of the target reduced closure under a finite ambient
morphism. -/
noncomputable def pointClosureSubschemePreimage {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) (y : Y) (hxy : f x = y)
    (z : (pointClosureIdealSheaf y).subscheme) :
    (pointClosureIdealSheaf x).subscheme :=
  Classical.choose (pointClosureSubschemeMap_surjective f x y hxy z)

@[simp]
theorem pointClosureSubschemeMap_preimage {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) (y : Y) (hxy : f x = y)
    (z : (pointClosureIdealSheaf y).subscheme) :
    pointClosureSubschemeMap f x y hxy
        (pointClosureSubschemePreimage f x y hxy z) = z :=
  Classical.choose_spec (pointClosureSubschemeMap_surjective f x y hxy z)

/-- The affine preimage of an affine open under a finite morphism. -/
noncomputable def finitePreimageAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (U : Y.affineOpens) : X.affineOpens :=
  ⟨f ⁻¹ᵁ (U : Y.Opens), U.2.preimage f⟩

@[simp]
theorem finitePreimageAffine_opens {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (U : Y.affineOpens) :
    (finitePreimageAffine f U : X.Opens) = f ⁻¹ᵁ (U : Y.Opens) :=
  rfl

/-- Finiteness of a finite morphism on the canonical affine preimage. -/
theorem moduleFinite_finitePreimageAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (U : Y.affineOpens) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    Module.Finite Γ(Y, U) Γ(X, finitePreimageAffine f U) := by
  letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
  change Module.Finite Γ(Y, U) Γ(X, finitePreimageAffine f U)
  exact f.finite_app U U.2

/-- Dominance of a finite morphism makes the canonical affine section algebra faithful. -/
theorem faithfulSMul_finitePreimageAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsReduced Y] (U : Y.affineOpens) :
    letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
    FaithfulSMul Γ(Y, U) Γ(X, finitePreimageAffine f U) := by
  letI : Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) := (f.app U).hom.toAlgebra
  letI : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  change Function.Injective (f.app U).hom
  exact f.app_injective U

/-- Lift the quotient-chart prime of a closed-subscheme point to the unique ambient
prime containing the defining ideal. -/
noncomputable def ambientPrimeOfQuotientPoint
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) : Ideal Γ(X, V) :=
  (I.quotientPoint V x hx).asIdeal.comap (Ideal.Quotient.mk (I.ideal V))

instance ambientPrimeOfQuotientPoint_isPrime
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    (ambientPrimeOfQuotientPoint I V x hx).IsPrime := by
  dsimp [ambientPrimeOfQuotientPoint]
  exact Ideal.IsPrime.comap _

theorem ideal_le_ambientPrimeOfQuotientPoint
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    I.ideal V ≤ ambientPrimeOfQuotientPoint I V x hx := by
  calc
    I.ideal V = RingHom.ker (Ideal.Quotient.mk (I.ideal V)) := Ideal.mk_ker.symm
    _ ≤ (I.quotientPoint V x hx).asIdeal.comap
        (Ideal.Quotient.mk (I.ideal V)) := Ideal.ker_le_comap _

theorem map_ambientPrimeOfQuotientPoint
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    (ambientPrimeOfQuotientPoint I V x hx).map
        (Ideal.Quotient.mk (I.ideal V)) =
      (I.quotientPoint V x hx).asIdeal := by
  exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

/-- The ambient prime lifted from a closed-subscheme point is the ordinary affine-chart
prime of its image in the ambient scheme. -/
theorem ambientPrimeOfQuotientPoint_eq_primeIdealOf
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    ambientPrimeOfQuotientPoint I V x hx =
      (V.2.primeIdealOf ⟨I.subschemeι x, hx⟩).asIdeal := by
  let W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ (V : X.Opens)
  let hW : IsAffineOpen W := by
    letI : IsOpenImmersion (I.subschemeCover.f V) := I.subschemeCover.map_prop V
    dsimp only [W]
    rw [← I.opensRange_subschemeCover_map V]
    exact isAffineOpen_opensRange (I.subschemeCover.f V)
  change
    (((hW.primeIdealOf ⟨x, hx⟩).asIdeal.comap
      (I.subschemeObjIso V).inv.hom).comap
        (Ideal.Quotient.mk (I.ideal V))) = _
  rw [Ideal.comap_comap]
  have hp := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE (V : X.Opens) V.2 W hW le_rfl hx)
  rw [Scheme.Hom.appLE_eq_app] at hp
  rw [I.subschemeι_app] at hp
  change
    (hW.primeIdealOf ⟨x, hx⟩).asIdeal.comap
        ((I.subschemeObjIso V).inv.hom.comp
          (Ideal.Quotient.mk (I.ideal V))) = _ at hp
  exact hp

/-- The canonical localization at the ambient prime lifted from a closed-subscheme point
is the actual ambient-scheme stalk at that point. -/
noncomputable def ambientPrimeLocalizationRingEquivStalk
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx) ≃+*
      X.presheaf.stalk (I.subschemeι x) := by
  let y : (V : X.Opens) := ⟨I.subschemeι x, hx⟩
  letI : Algebra Γ(X, V) (X.presheaf.stalk (I.subschemeι x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf y
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk (I.subschemeι x))
      (ambientPrimeOfQuotientPoint I V x hx) := by
    simpa only [ambientPrimeOfQuotientPoint_eq_primeIdealOf] using
      (V.2.isLocalization_stalk y)
  exact (IsLocalization.algEquiv
    (ambientPrimeOfQuotientPoint I V x hx).primeCompl
    (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx))
    (X.presheaf.stalk (I.subschemeι x))).toRingEquiv

/-- Ambient regularity at the actual scheme point transports to the canonical affine
localization used by the divisor chart. -/
theorem isRegularLocalRing_ambientPrimeLocalization
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hregular : IsRegularLocalRing (X.presheaf.stalk (I.subschemeι x))) :
    IsRegularLocalRing
      (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx)) := by
  letI : IsRegularLocalRing (X.presheaf.stalk (I.subschemeι x)) := hregular
  exact IsRegularLocalRing.of_ringEquiv
    (ambientPrimeLocalizationRingEquivStalk I V x hx).symm

/-- The dimension of the canonical affine localization is the codimension of the actual
ambient-scheme point. -/
theorem ringKrullDim_ambientPrimeLocalization
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    ringKrullDim
        (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx)) =
      Order.coheight (I.subschemeι x) := by
  rw [(ambientPrimeLocalizationRingEquivStalk I V x hx).ringKrullDim]
  exact AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (I.subschemeι x)

/-- Identify a quotient of an affine local ring with the actual closed-subscheme stalk,
when its prime has been proved to be the canonical ambient prime of the point. -/
noncomputable def divisorQuotientLocalizationRingEquivStalkOfEq
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (q : Ideal Γ(X, V)) [q.IsPrime]
    (hq : q = ambientPrimeOfQuotientPoint I V x hx) :
    (Localization.AtPrime q ⧸
        (I.ideal V).map
          (algebraMap Γ(X, V)
            (Localization.AtPrime q))) ≃+*
      I.subscheme.presheaf.stalk x := by
  let R := Γ(X, V)
  let D : Ideal R := I.ideal V
  let A := R ⧸ D
  let C := Localization.AtPrime q ⧸
    D.map (algebraMap R (Localization.AtPrime q))
  let qbar : Ideal A := (I.quotientPoint V x hx).asIdeal
  letI : qbar.IsPrime := inferInstance
  letI : Algebra A C :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp le_rfl)
  have hlocC₀ : IsLocalization
      (Algebra.algebraMapSubmonoid A q.primeCompl) C := by
    apply IsLocalization.of_surjective q.primeCompl (Localization.AtPrime q)
      (Ideal.Quotient.mk D) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk
        (D.map (algebraMap R (Localization.AtPrime q))))
      Ideal.Quotient.mk_surjective
    · rfl
    · rw [Ideal.mk_ker, Ideal.mk_ker]
  letI : qbar.LiesOver q := by
    constructor
    exact hq
  have hsubmonoid :
      Algebra.algebraMapSubmonoid A q.primeCompl = qbar.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      qbar q Ideal.Quotient.mk_surjective
  have hlocC : IsLocalization.AtPrime C qbar := by
    change IsLocalization qbar.primeCompl C
    rw [← hsubmonoid]
    exact hlocC₀
  letI : Algebra A (I.subscheme.presheaf.stalk x) :=
    I.quotientStalkAlgebra V x hx
  have hlocStalk : IsLocalization.AtPrime
      (I.subscheme.presheaf.stalk x) qbar :=
    I.quotientStalk_isLocalization V x hx
  exact (IsLocalization.algEquiv qbar.primeCompl C
    (I.subscheme.presheaf.stalk x)).toRingEquiv

/-- Quotienting the ambient local ring by the localized defining ideal gives the
actual local ring of the closed subscheme.

Both rings are localizations of the same affine quotient ring at the canonical point.
Thus this comparison follows from the quotient and localization universal properties;
it is not an extra identification of divisor coordinates. -/
noncomputable def divisorQuotientLocalizationRingEquivStalk
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx) ⧸
        (I.ideal V).map
          (algebraMap Γ(X, V)
            (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx)))) ≃+*
      I.subscheme.presheaf.stalk x :=
  divisorQuotientLocalizationRingEquivStalkOfEq I V x hx
    (ambientPrimeOfQuotientPoint I V x hx) rfl

/-- Regularity of the actual divisor stalk transports to the quotient of the ambient
local ring by the localized divisor ideal. -/
theorem isRegularLocalRing_divisorQuotientLocalization
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hregular : IsRegularLocalRing (I.subscheme.presheaf.stalk x)) :
    IsRegularLocalRing
      (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx) ⧸
        (I.ideal V).map
          (algebraMap Γ(X, V)
            (Localization.AtPrime
              (ambientPrimeOfQuotientPoint I V x hx)))) := by
  letI : IsRegularLocalRing (I.subscheme.presheaf.stalk x) := hregular
  exact IsRegularLocalRing.of_ringEquiv
    (divisorQuotientLocalizationRingEquivStalk I V x hx).symm

/-- The dimension of the localized divisor quotient is the codimension of the point in
the actual divisor subscheme. -/
theorem ringKrullDim_divisorQuotientLocalization
    {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    ringKrullDim
        (Localization.AtPrime (ambientPrimeOfQuotientPoint I V x hx) ⧸
          (I.ideal V).map
            (algebraMap Γ(X, V)
              (Localization.AtPrime
                (ambientPrimeOfQuotientPoint I V x hx)))) =
      Order.coheight x := by
  rw [(divisorQuotientLocalizationRingEquivStalk I V x hx).ringKrullDim]
  exact AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x

/-- Contraction of the canonical ambient source prime is the canonical ambient target
prime for an actual morphism of closed subschemes. -/
theorem ambientPrimeOfQuotientPoint_comap
    {Y X : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (H : J ≤ I.map f)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    let g := I.subschemeMap J f H
    let map_le := I.subschemeMap_preimage_le J f H U V ambient_map_le
    let hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
    (ambientPrimeOfQuotientPoint I V x hx).comap
        (f.appLE U V ambient_map_le).hom =
      ambientPrimeOfQuotientPoint J U (g x) hy := by
  dsimp only
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U V ambient_map_le
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  let sourcePoint := I.quotientPoint V x hx
  let targetPoint := J.quotientPoint U (g x) hy
  change (sourcePoint.asIdeal.comap (Ideal.Quotient.mk (I.ideal V))).comap
      (f.appLE U V ambient_map_le).hom =
    targetPoint.asIdeal.comap (Ideal.Quotient.mk (J.ideal U))
  rw [Ideal.comap_comap]
  have hq := J.quotientAppLE_comp_mk_subschemeMap I f H U V ambient_map_le map_le
  rw [← hq]
  rw [← Ideal.comap_comap]
  have hp := congrArg PrimeSpectrum.asIdeal
    (J.comap_quotientPoint_quotientAppLE I g U V map_le x hx hy)
  exact congrArg (fun K : Ideal (Γ(Y, U) ⧸ J.ideal U) ↦
    K.comap (Ideal.Quotient.mk (J.ideal U))) hp

section AmbientMap

variable {Y X : Scheme.{u}} (f : X ⟶ Y)
  (U : Y.affineOpens) (V : X.affineOpens)
  (ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))

set_option backward.isDefEq.respectTransparency false in
/-- Construct the actual closed-subscheme stalk presentation from an affine finite normal
algebra and one selected point.

The source prime `Q` is not an input: it is the canonical lift of the quotient-chart point,
and the target prime `q` is its contraction. All four primes and the quotient morphism are
therefore tied to the actual closed-subscheme map. -/
noncomputable def closedSubschemeStalkBoundingLocalizationPresentationOfFiniteNormalAt
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (H : J ≤ I.map f)
    [Algebra Γ(Y, U) Γ(X, V)]
    (hAlg : algebraMap Γ(Y, U) Γ(X, V) = (f.appLE U V ambient_map_le).hom)
    [Algebra ℚ Γ(Y, U)]
    [Module.Finite Γ(Y, U) Γ(X, V)] [FaithfulSMul Γ(Y, U) Γ(X, V)]
    [IsNoetherianRing Γ(Y, U)] [IsNoetherianRing Γ(X, V)]
    [IsDomain Γ(Y, U)] [IsIntegrallyClosed Γ(Y, U)]
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    [hJprime : (J.ideal U).IsPrime] [hIprime : (I.ideal V).IsPrime]
    (hJheight : (J.ideal U).height = 1) (hIheight : (I.ideal V).height = 1)
    (a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)))
    (ha : (J.ideal U).map
        (algebraMap Γ(Y, U) (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)))) =
      Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U))))
    (dim_base : ringKrullDim (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U))) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)) ⧸
        Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)) ⧸
        Ideal.span {a}) = 1)
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, V)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid Γ(X, V)
        ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid Γ(X, V)
        ((ambientPrimeOfQuotientPoint I V x hx).under Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation (I.subschemeMap J f H) x := by
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let D : HeightOnePrime R := ⟨⟨J.ideal U, hJprime⟩, hJheight⟩
  let P : HeightOnePrime S := ⟨⟨I.ideal V, hIprime⟩, hIheight⟩
  let Q : Ideal S := ambientPrimeOfQuotientPoint I V x hx
  let q : Ideal R := Q.under R
  letI : Q.IsPrime := inferInstance
  letI : q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : P.1.asIdeal ≤ Q := ideal_le_ambientPrimeOfQuotientPoint I V x hx
  have hDP : D.1.asIdeal.map (algebraMap R S) ≤ P.1.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    rw [hAlg]
    exact I.subschemeMap_ideal_le J f H U V ambient_map_le
  have hDq : D.1.asIdeal ≤ q := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hDP.trans hPQ
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U V ambient_map_le
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  let sourcePoint := I.quotientPoint V x hx
  have hQmap : Q.map (Ideal.Quotient.mk P.1.asIdeal) = sourcePoint.asIdeal :=
    map_ambientPrimeOfQuotientPoint I V x hx
  let hquot :=
    toGlobalQuotientSchemeStalkBoundingLocalizationPresentationOfHeightOneDivisorsAt
      q D P Q hDq hPQ rfl hDP a ha regular_base dim_base regular_divisor
        dim_divisor havoid purity abhyankar
  let fAB : (R ⧸ D.1.asIdeal) →+* (S ⧸ P.1.asIdeal) :=
    Ideal.quotientMap P.1.asIdeal (algebraMap R S)
      (Ideal.map_le_iff_le_comap.mp hDP)
  have hmap : J.quotientAppLE I g U V map_le = fAB := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    have hq := J.quotientAppLE_comp_mk_subschemeMap I f H U V ambient_map_le map_le
    have hqr := DFunLike.congr_fun hq r
    simpa only [RingHom.comp_apply, fAB, R, S, D, P,
      Ideal.quotientMap_mk, hAlg] using hqr
  letI hQbar : (Q.map (Ideal.Quotient.mk P.1.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact hPQ)
  let quotientPoint : PrimeSpectrum (S ⧸ P.1.asIdeal) :=
    ⟨Q.map (Ideal.Quotient.mk P.1.asIdeal), hQbar⟩
  have hpoint : quotientPoint = sourcePoint := by
    apply PrimeSpectrum.ext
    exact hQmap
  change quotientPoint = I.quotientPoint V x hx at hpoint
  let hactual := J.stalkMapArrowIsoQuotientAppLE I g U V map_le x hx hy
  have hactual' := hactual
  dsimp only at hactual'
  rw [hmap] at hactual'
  rw [← hpoint] at hactual'
  let hchart : SchemeStalkBoundingChart g x := by
    letI : CommRing hquot.R := hquot.commRingR
    letI : CommRing hquot.S := hquot.commRingS
    letI : Algebra hquot.R hquot.S := hquot.algebra
    refine
      { R := hquot.R
        S := hquot.S
        a := hquot.a
        p := hquot.p
        xi := hquot.xi
        chart := hquot.chart
        stalkIso := ?_ }
    exact hactual'.trans
      hquot.toSchemeStalkBoundingPresentation.toSchemeStalkBoundingChart.stalkIso
  exact hchart.toSchemeStalkBoundingLocalizationPresentation

end AmbientMap

section FiniteTypeDivisorMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y]

/-- A finite dominant morphism of integral schemes preserves codimension one at a
point whose image has an affine neighborhood of finite type over a field.
Neither scheme is required to be normal. -/
theorem coheight_apply_eq_one_of_mem_affine_finiteType
    (k : Type*) [Field k] (U : Y.affineOpens)
    [Algebra k Γ(Y, U)] [Algebra.FiniteType k Γ(Y, U)]
    (A : SchemeDivisorPoint X) (hAU : f A.1 ∈ (U : Y.Opens)) :
    Order.coheight (f A.1) = 1 := by
  let V := finitePreimageAffine f U
  have hAV : A.1 ∈ (V : X.Opens) := hAU
  letI : Nonempty (U : Y.Opens) := ⟨⟨f A.1, hAU⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨A.1, hAV⟩⟩
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.app U).hom.toAlgebra
  letI : Module.Finite Γ(Y, U) Γ(X, V) := moduleFinite_finitePreimageAffine f U
  letI : FaithfulSMul Γ(Y, U) Γ(X, V) := faithfulSMul_finitePreimageAffine f U
  let Q : Ideal Γ(X, V) := (V.2.primeIdealOf ⟨A.1, hAV⟩).asIdeal
  let q : Ideal Γ(Y, U) := (U.2.primeIdealOf ⟨f A.1, hAU⟩).asIdeal
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  have hQheight : Q.height = 1 := by
    dsimp only [Q]
    rw [← pointClosureIdealSheaf_ideal A.1 V hAV]
    exact pointClosureIdealSheaf_ideal_height A V hAV
  have hAlg : algebraMap Γ(Y, U) Γ(X, V) =
      (f.appLE U V le_rfl).hom := by
    change (f.app U).hom = (f.appLE U V le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hcontract : Q.under Γ(Y, U) = q := by
    change Q.comap (algebraMap Γ(Y, U) Γ(X, V)) = q
    rw [hAlg]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hAV)
  have hqheight : q.height = 1 := by
    rw [← hcontract]
    exact (height_under_eq_of_finite_of_finiteType k Q).trans hQheight
  let hU : IsAffineOpen (U : Y.Opens) := U.2
  let p : AlgebraicGeometry.Spec Γ(Y, U) :=
    hU.primeIdealOf ⟨f A.1, hAU⟩
  have hopen := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (x := p) hU.fromSpec
  rw [hU.fromSpec_primeIdealOf] at hopen
  exact hopen.trans <| (AlgebraicGeometry.idealHeight_eq_coheight Γ(Y, U) p).symm.trans <| by
    simpa only [q, p] using hqheight

variable (k : Type*) [Field k]
  [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
  [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)]

include k in
/-- Finite dominant morphisms preserve codimension one when the target affine charts
are of finite type over a field, without normality assumptions. -/
theorem coheight_apply_eq_one_of_finiteType (A : SchemeDivisorPoint X) :
    Order.coheight (f A.1) = 1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hAW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f A.1)) isOpen_univ
  exact coheight_apply_eq_one_of_mem_affine_finiteType f k ⟨W, hW⟩ A hAW

/-- The divisor pushforward under a finite dominant morphism with finite-type target
charts.  Its underlying point is the image under the original scheme morphism. -/
noncomputable def SchemeDivisorPoint.mapFiniteDominantFiniteType
    (A : SchemeDivisorPoint X) : SchemeDivisorPoint Y :=
  ⟨f A.1, coheight_apply_eq_one_of_finiteType f k A⟩

@[simp]
theorem SchemeDivisorPoint.mapFiniteDominantFiniteType_val
    (A : SchemeDivisorPoint X) :
    (A.mapFiniteDominantFiniteType f k).1 = f A.1 :=
  rfl

end FiniteTypeDivisorMap

section FiniteDominantMorphism

variable {Y X : Scheme.{u}}
variable (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormalScheme X] [IsNormalScheme Y]
  (U : Y.affineOpens)

local instance finitePreimageAlgebra :
    Algebra Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
  (f.app U).hom.toAlgebra

attribute [local instance] IsLocallyNoetherian.component_noetherian

local instance finitePreimageAffine_moduleFinite :
    Module.Finite Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
  moduleFinite_finitePreimageAffine f U

local instance finitePreimageSourceNoetherian :
    IsNoetherianRing Γ(X, finitePreimageAffine f U) :=
  IsNoetherianRing.of_finite Γ(Y, U) Γ(X, finitePreimageAffine f U)

local instance finitePreimageAffine_faithfulSMul :
    FaithfulSMul Γ(Y, U) Γ(X, finitePreimageAffine f U) :=
  faithfulSMul_finitePreimageAffine f U

omit [IsNormalScheme X] in
/-- A finite dominant morphism to a normal locally Noetherian integral scheme sends a
codimension-one point to a codimension-one point, provided the image is viewed in an
affine neighborhood.  The proof is the affine height-preservation theorem transported
through the two affine open immersions. -/
theorem coheight_apply_eq_one_of_mem_affine
    (A : SchemeDivisorPoint X) (hAU : f A.1 ∈ (U : Y.Opens)) :
    Order.coheight (f A.1) = 1 := by
  let V := finitePreimageAffine f U
  have hAV : A.1 ∈ (V : X.Opens) := by
    exact hAU
  letI : Nonempty (U : Y.Opens) := ⟨⟨f A.1, hAU⟩⟩
  letI : Nonempty (V : X.Opens) := ⟨⟨A.1, hAV⟩⟩
  let Q : Ideal Γ(X, V) := (V.2.primeIdealOf ⟨A.1, hAV⟩).asIdeal
  let q : Ideal Γ(Y, U) := (U.2.primeIdealOf ⟨f A.1, hAU⟩).asIdeal
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : q.IsPrime := by
    dsimp only [q]
    infer_instance
  have hQheight : Q.height = 1 := by
    dsimp only [Q]
    rw [← pointClosureIdealSheaf_ideal A.1 V hAV]
    exact pointClosureIdealSheaf_ideal_height A V hAV
  have hAlg : algebraMap Γ(Y, U) Γ(X, V) =
      (f.appLE U V le_rfl).hom := by
    change (f.app U).hom = (f.appLE U V le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hcontract : Q.under Γ(Y, U) = q := by
    change Q.comap (algebraMap Γ(Y, U) Γ(X, V)) = q
    rw [hAlg]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : Y.Opens) U.2
        (V : X.Opens) V.2 le_rfl hAV)
  have hqheight : q.height = 1 := by
    rw [← hcontract]
    exact (height_under_eq_of_finite_of_normal Q).trans hQheight
  let hU : IsAffineOpen (U : Y.Opens) := U.2
  let p : AlgebraicGeometry.Spec Γ(Y, U) :=
    hU.primeIdealOf ⟨f A.1, hAU⟩
  have hopen := AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (x := p) hU.fromSpec
  rw [hU.fromSpec_primeIdealOf] at hopen
  exact hopen.trans <| (AlgebraicGeometry.idealHeight_eq_coheight Γ(Y, U) p).symm.trans <| by
    simpa only [q, p] using hqheight

set_option backward.isDefEq.respectTransparency false in
/-- Construct the actual closed-subscheme stalk presentation on the canonical affine
preimage of an affine target neighborhood.

Unlike `closedSubschemeStalkBoundingLocalizationPresentationOfFiniteNormalAt`, this
wrapper does not ask for the affine algebra, its finiteness or its faithfulness. They are
the actual map on sections and follow from finiteness and dominance of `f`. The
Noetherian, domain and normal section-ring instances likewise come from the corresponding
scheme hypotheses. -/
noncomputable def
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalAt
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (H : J ≤ I.map f)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (x : I.subscheme)
    (hx : x ∈ I.subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    [hJprime : (J.ideal U).IsPrime]
    [hIprime : (I.ideal (finitePreimageAffine f U)).IsPrime]
    (hJheight : (J.ideal U).height = 1)
    (hIheight : (I.ideal (finitePreimageAffine f U)).height = 1)
    (a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I (finitePreimageAffine f U) x hx).under Γ(Y, U)))
    (ha : (J.ideal U).map
        (algebraMap Γ(Y, U) (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)))) =
      Ideal.span {a})
    (regular_base : IsRegularLocalRing (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).under Γ(Y, U))))
    (dim_base : ringKrullDim (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).under Γ(Y, U))) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)) ⧸
        Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)) ⧸
        Ideal.span {a}) = 1)
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation (I.subschemeMap J f H) x := by
  let V := finitePreimageAffine f U
  have ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens) := by
    rfl
  have hAlg : algebraMap Γ(Y, U) Γ(X, V) =
      (f.appLE U V ambient_map_le).hom := by
    change (f.app U).hom = (f.appLE U V ambient_map_le).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  exact closedSubschemeStalkBoundingLocalizationPresentationOfFiniteNormalAt
    f U V ambient_map_le J I H hAlg x hx hJheight hIheight a ha regular_base
      dim_base regular_divisor dim_divisor havoid purity abhyankar

set_option backward.isDefEq.respectTransparency false in
/-- Construct the actual closed-subscheme stalk presentation without choosing a local
equation.

The equation is generated by the actual target divisor ideal in the two-dimensional
regular local ring. The regularity and dimension of its quotient are transported from the
actual target-divisor stalk, so the caller supplies geometric stalk and codimension facts,
rather than a generator or any coordinate-ring identification. -/
noncomputable def
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormal
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (H : J ≤ I.map f)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (x : I.subscheme)
    (hx : x ∈ I.subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    [hJprime : (J.ideal U).IsPrime]
    [hIprime : (I.ideal (finitePreimageAffine f U)).IsPrime]
    (hJheight : (J.ideal U).height = 1)
    (hIheight : (I.ideal (finitePreimageAffine f U)).height = 1)
    (regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        (J.subschemeι ((I.subschemeMap J f H) x))))
    (ambient_coheight : Order.coheight
      (J.subschemeι ((I.subschemeMap J f H) x)) = 2)
    (regular_divisor : IsRegularLocalRing
      (J.subscheme.presheaf.stalk ((I.subschemeMap J f H) x)))
    (divisor_coheight : Order.coheight ((I.subschemeMap J f H) x) = 1)
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : ∀ a : Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)),
      Stacks.AbhyankarLemma
        (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)))
        (Localization (Algebra.algebraMapSubmonoid
          Γ(X, finitePreimageAffine f U)
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation (I.subschemeMap J f H) x := by
  let R := Γ(Y, U)
  let S := Γ(X, finitePreimageAffine f U)
  let D : Ideal R := J.ideal U
  let P : Ideal S := I.ideal (finitePreimageAffine f U)
  let Q : Ideal S := ambientPrimeOfQuotientPoint I (finitePreimageAffine f U) x hx
  let q : Ideal R := Q.under R
  letI : Q.IsPrime := inferInstance
  letI : q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : P ≤ Q := ideal_le_ambientPrimeOfQuotientPoint I
    (finitePreimageAffine f U) x hx
  have hAlg : algebraMap R S =
      (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
    change (f.app U).hom = (f.appLE U (finitePreimageAffine f U) le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hDP : D.map (algebraMap R S) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    rw [hAlg]
    exact I.subschemeMap_ideal_le J f H U (finitePreimageAffine f U) le_rfl
  have hDq : D ≤ q := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hDP.trans hPQ
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U
    (finitePreimageAffine f U) le_rfl
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  have hq : q = ambientPrimeOfQuotientPoint J U (g x) hy := by
    change Q.comap (algebraMap R S) = _
    rw [hAlg]
    exact ambientPrimeOfQuotientPoint_comap f U (finitePreimageAffine f U)
      le_rfl J I H x hx
  let y : (U : Y.Opens) :=
    ⟨J.subschemeι (g x), hy⟩
  letI : Algebra R (Y.presheaf.stalk (J.subschemeι (g x))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  have hloc : IsLocalization.AtPrime
      (Y.presheaf.stalk (J.subschemeι (g x))) q := by
    simpa only [hq, ambientPrimeOfQuotientPoint_eq_primeIdealOf] using
      (U.2.isLocalization_stalk y)
  let e : Localization.AtPrime q ≃+*
      Y.presheaf.stalk (J.subschemeι (g x)) :=
    (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q)
      (Y.presheaf.stalk (J.subschemeι (g x)))).toRingEquiv
  have regular_base : IsRegularLocalRing
      (Localization.AtPrime q) :=
    letI : IsRegularLocalRing
        (Y.presheaf.stalk (J.subschemeι (g x))) := regular_ambient
    IsRegularLocalRing.of_ringEquiv e.symm
  have dim_base : ringKrullDim (Localization.AtPrime q) = 2 := by
    calc
      ringKrullDim (Localization.AtPrime q) =
          ringKrullDim (Y.presheaf.stalk (J.subschemeι (g x))) :=
        e.ringKrullDim
      _ = ↑(Order.coheight (J.subschemeι (g x))) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight
          (J.subschemeι (g x))
      _ = 2 := by
        rw [show Order.coheight (J.subschemeι (g x)) = 2 by
          simpa only [g] using ambient_coheight]
        norm_num
  let ediv :
      (Localization.AtPrime q ⧸
          D.map (algebraMap R (Localization.AtPrime q))) ≃+*
        J.subscheme.presheaf.stalk (g x) :=
    divisorQuotientLocalizationRingEquivStalkOfEq J U (g x) hy q hq
  have regular_divisor_local : IsRegularLocalRing
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) := by
    letI : IsRegularLocalRing
        (J.subscheme.presheaf.stalk (g x)) := by
      simpa only [g] using regular_divisor
    exact IsRegularLocalRing.of_ringEquiv ediv.symm
  have dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) = 1 := by
    calc
      ringKrullDim
          (Localization.AtPrime q ⧸
            D.map (algebraMap R (Localization.AtPrime q))) =
          ringKrullDim (J.subscheme.presheaf.stalk (g x)) :=
        ediv.ringKrullDim
      _ = ↑(Order.coheight (g x)) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (g x)
      _ = 1 := by
        rw [show Order.coheight (g x) = 1 by
          simpa only [g] using divisor_coheight]
        norm_num
  letI : IsRegularLocalRing (Localization.AtPrime q) := regular_base
  letI : IsRegularLocalRing
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) := regular_divisor_local
  let hex := exists_generator_map_atPrime_regular_dim_two
    D q hDq hJheight dim_base dim_divisor
  let a := Classical.choose hex
  have ha := Classical.choose_spec hex
  have regular_divisor_span : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}) := by
    rw [← ha]
    exact regular_divisor_local
  have dim_divisor_span : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1 := by
    rw [← ha]
    exact dim_divisor
  exact
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalAt
      f U J I H x hx hJheight hIheight a ha regular_base dim_base
        regular_divisor_span dim_divisor_span havoid purity (abhyankar a)

set_option backward.isDefEq.respectTransparency false in
/-- Construct the actual closed-subscheme stalk presentation from a local
effective-Cartier equation.

Compared with
`closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormal`,
this constructor does not ask for ambient codimension two and does not quantify
Abhyankar's lemma over every possible equation.  The caller supplies the actual
nonzerodivisor equation of the target divisor at the selected point.  Since the
divisor point has codimension one in the divisor, Stacks Tag 00KW derives that
the ambient local ring has dimension two. -/
noncomputable def
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (H : J ≤ I.map f)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (x : I.subscheme)
    (hx : x ∈ I.subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    [hJprime : (J.ideal U).IsPrime]
    [hIprime : (I.ideal (finitePreimageAffine f U)).IsPrime]
    (hJheight : (J.ideal U).height = 1)
    (hIheight : (I.ideal (finitePreimageAffine f U)).height = 1)
    (a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).under Γ(Y, U)))
    (ha : (J.ideal U).map
        (algebraMap Γ(Y, U) (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)))) =
      Ideal.span {a})
    (ha_nonZeroDivisor : a ∈ nonZeroDivisors
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U))))
    (regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        (J.subschemeι ((I.subschemeMap J f H) x))))
    (regular_divisor : IsRegularLocalRing
      (J.subscheme.presheaf.stalk ((I.subschemeMap J f H) x)))
    (divisor_coheight : Order.coheight ((I.subschemeMap J f H) x) = 1)
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation (I.subschemeMap J f H) x := by
  let R := Γ(Y, U)
  let S := Γ(X, finitePreimageAffine f U)
  let D : Ideal R := J.ideal U
  let Q : Ideal S := ambientPrimeOfQuotientPoint I
    (finitePreimageAffine f U) x hx
  let q : Ideal R := Q.under R
  letI : Q.IsPrime := inferInstance
  letI : q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : I.ideal (finitePreimageAffine f U) ≤ Q :=
    ideal_le_ambientPrimeOfQuotientPoint I
      (finitePreimageAffine f U) x hx
  have hAlg : algebraMap R S =
      (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
    change (f.app U).hom = (f.appLE U (finitePreimageAffine f U) le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hDP : D.map (algebraMap R S) ≤
      I.ideal (finitePreimageAffine f U) := by
    rw [Ideal.map_le_iff_le_comap]
    rw [hAlg]
    exact I.subschemeMap_ideal_le J f H U (finitePreimageAffine f U) le_rfl
  have hDq : D ≤ q := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hDP.trans hPQ
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U
    (finitePreimageAffine f U) le_rfl
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  have hq : q = ambientPrimeOfQuotientPoint J U (g x) hy := by
    change Q.comap (algebraMap R S) = _
    rw [hAlg]
    exact ambientPrimeOfQuotientPoint_comap f U (finitePreimageAffine f U)
      le_rfl J I H x hx
  let y : (U : Y.Opens) := ⟨J.subschemeι (g x), hy⟩
  letI : Algebra R (Y.presheaf.stalk (J.subschemeι (g x))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  have hloc : IsLocalization.AtPrime
      (Y.presheaf.stalk (J.subschemeι (g x))) q := by
    simpa only [hq, ambientPrimeOfQuotientPoint_eq_primeIdealOf] using
      (U.2.isLocalization_stalk y)
  let e : Localization.AtPrime q ≃+*
      Y.presheaf.stalk (J.subschemeι (g x)) :=
    (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q)
      (Y.presheaf.stalk (J.subschemeι (g x)))).toRingEquiv
  have regular_base : IsRegularLocalRing (Localization.AtPrime q) :=
    letI : IsRegularLocalRing
        (Y.presheaf.stalk (J.subschemeι (g x))) := regular_ambient
    IsRegularLocalRing.of_ringEquiv e.symm
  let ediv :
      (Localization.AtPrime q ⧸
          D.map (algebraMap R (Localization.AtPrime q))) ≃+*
        J.subscheme.presheaf.stalk (g x) :=
    divisorQuotientLocalizationRingEquivStalkOfEq J U (g x) hy q hq
  have regular_divisor_map : IsRegularLocalRing
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) := by
    letI : IsRegularLocalRing
        (J.subscheme.presheaf.stalk (g x)) := by
      simpa only [g] using regular_divisor
    exact IsRegularLocalRing.of_ringEquiv ediv.symm
  have dim_divisor_map : ringKrullDim
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) = 1 := by
    calc
      ringKrullDim
          (Localization.AtPrime q ⧸
            D.map (algebraMap R (Localization.AtPrime q))) =
          ringKrullDim (J.subscheme.presheaf.stalk (g x)) :=
        ediv.ringKrullDim
      _ = ↑(Order.coheight (g x)) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (g x)
      _ = 1 := by
        rw [show Order.coheight (g x) = 1 by
          simpa only [g] using divisor_coheight]
        norm_num
  have ha' : D.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span {a} := by
    simpa only [D, q, Q, R, S] using ha
  have ha_nonZeroDivisor' : a ∈
      nonZeroDivisors (Localization.AtPrime q) := by
    simpa only [q, Q, R, S] using ha_nonZeroDivisor
  have ha_maximal : a ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    have hDmax : D.map (algebraMap R (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hDq
    apply hDmax
    rw [ha']
    exact Ideal.subset_span (Set.mem_singleton a)
  have regular_divisor_span : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}) := by
    rw [← ha']
    exact regular_divisor_map
  have dim_divisor_span : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1 := by
    rw [← ha']
    exact dim_divisor_map
  have dim_base : ringKrullDim (Localization.AtPrime q) = 2 :=
    ringKrullDim_eq_two_of_cartier_quotient_eq_one
      ha_nonZeroDivisor' ha_maximal dim_divisor_span
  exact
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalAt
      f U J I H x hx hJheight hIheight a ha regular_base dim_base
        regular_divisor_span dim_divisor_span havoid purity abhyankar

set_option backward.isDefEq.respectTransparency false in
/-- Construct the bounding presentation from actual source and target divisor points.

The reduced ideal sheaves, their map, and the height-one primes on the chosen affine
charts are all constructed from the closures of `A` and `B`.  Thus this wrapper removes
the arbitrary ideal-sheaf, compatibility, primality, and height hypotheses from
`closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormal`.
The remaining inputs concern the selected codimension-two point, its regularity, branch
avoidance, purity, and Abhyankar. -/
noncomputable def
    pointClosureStalkBoundingLocalizationPresentationOfFiniteDominantNormal
    (A : SchemeDivisorPoint X) (B : SchemeDivisorPoint Y)
    (hAB : f A.1 = B.1)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (hBU : B.1 ∈ (U : Y.Opens))
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf B.1).subschemeι
          ((pointClosureSubschemeMap f A.1 B.1 hAB) x))))
    (ambient_coheight : Order.coheight
      ((pointClosureIdealSheaf B.1).subschemeι
        ((pointClosureSubschemeMap f A.1 B.1 hAB) x)) = 2)
    (regular_divisor : IsRegularLocalRing
      ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk
        ((pointClosureSubschemeMap f A.1 B.1 hAB) x)))
    (divisor_coheight : Order.coheight
      ((pointClosureSubschemeMap f A.1 B.1 hAB) x) = 1)
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ affinePrimeOfSchemeDivisorPoint B U hBU →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : ∀ a : Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)),
      Stacks.AbhyankarLemma
        (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine f U) x hx).under Γ(Y, U)))
        (Localization (Algebra.algebraMapSubmonoid
          Γ(X, finitePreimageAffine f U)
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation
      (pointClosureSubschemeMap f A.1 B.1 hAB) x := by
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 hAB
  have hAU : A.1 ∈ (finitePreimageAffine f U : X.Opens) := by
    change f A.1 ∈ (U : Y.Opens)
    rw [hAB]
    exact hBU
  letI hJprime : (J.ideal U).IsPrime := by
    simpa only [J] using
      pointClosureIdealSheaf_ideal_isPrime B.1 U hBU
  letI hIprime : (I.ideal (finitePreimageAffine f U)).IsPrime := by
    simpa only [I] using
      pointClosureIdealSheaf_ideal_isPrime A.1
        (finitePreimageAffine f U) hAU
  have hJheight : (J.ideal U).height = 1 := by
    simpa only [J] using pointClosureIdealSheaf_ideal_height B U hBU
  have hIheight : (I.ideal (finitePreimageAffine f U)).height = 1 := by
    simpa only [I] using pointClosureIdealSheaf_ideal_height A
      (finitePreimageAffine f U) hAU
  have regular_ambient' : IsRegularLocalRing
      (Y.presheaf.stalk (J.subschemeι ((I.subschemeMap J f H) x))) := by
    simpa only [I, J, H, pointClosureSubschemeMap] using regular_ambient
  have ambient_coheight' :
      Order.coheight (J.subschemeι ((I.subschemeMap J f H) x)) = 2 := by
    simpa only [I, J, H, pointClosureSubschemeMap] using ambient_coheight
  have regular_divisor' : IsRegularLocalRing
      (J.subscheme.presheaf.stalk ((I.subschemeMap J f H) x)) := by
    simpa only [I, J, H, pointClosureSubschemeMap] using regular_divisor
  have divisor_coheight' :
      Order.coheight ((I.subschemeMap J f H) x) = 1 := by
    simpa only [I, J, H, pointClosureSubschemeMap] using divisor_coheight
  have hAvoid' : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U) := by
    simpa only [I, J, affinePrimeOfSchemeDivisorPoint] using havoid
  have purity' : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) := by
    simpa only [I] using purity
  have abhyankar' : ∀ a : Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)),
      Stacks.AbhyankarLemma
        (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)))
        (Localization (Algebra.algebraMapSubmonoid
          Γ(X, finitePreimageAffine f U)
          ((ambientPrimeOfQuotientPoint I
            (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) a := by
    simpa only [I] using abhyankar
  have hresult :=
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormal
      f U J I H x hx hJheight hIheight regular_ambient' ambient_coheight'
        regular_divisor' divisor_coheight' hAvoid' purity' abhyankar'
  simpa only [I, J, H, pointClosureSubschemeMap] using hresult

omit [IsDominant f] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y] in
/-- Contraction at a specified source point for two explicitly supplied divisor
points.  This is the invariant-divisor form of
`SchemeDivisorPoint.closurePoint_under_eq_primeIdealOf`: the target divisor need not be
reconstructed as `mapFiniteDominantNormal`, so the statement composes directly with an
iterate fixing the divisor. -/
theorem pointClosurePoint_under_eq_primeIdealOf
    (A : SchemeDivisorPoint X) (B : SchemeDivisorPoint Y)
    (hAB : f A.1 = B.1)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (z : (pointClosureIdealSheaf B.1).subscheme)
    (hzU : (pointClosureIdealSheaf B.1).subschemeι z ∈ (U : Y.Opens))
    (hxz : pointClosureSubschemeMap f A.1 B.1 hAB x = z) :
    (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
      (finitePreimageAffine f U) x hx).under Γ(Y, U) =
        (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf B.1).subschemeι z, hzU⟩).asIdeal := by
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 hAB
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U
    (finitePreimageAffine f U) le_rfl
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  have hAlg : algebraMap Γ(Y, U) Γ(X, finitePreimageAffine f U) =
      (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
    change (f.app U).hom = (f.appLE U (finitePreimageAffine f U) le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hmap : g x = z := by
    simpa only [g, I, J, H, pointClosureSubschemeMap] using hxz
  calc
    (ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).under Γ(Y, U) =
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).comap
            (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
      change (ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).comap
          (algebraMap Γ(Y, U) Γ(X, finitePreimageAffine f U)) = _
      rw [hAlg]
    _ = ambientPrimeOfQuotientPoint J U (g x) hy :=
      ambientPrimeOfQuotientPoint_comap f U
        (finitePreimageAffine f U) le_rfl J I H x hx
    _ = (U.2.primeIdealOf ⟨J.subschemeι (g x), hy⟩).asIdeal :=
      ambientPrimeOfQuotientPoint_eq_primeIdealOf J U (g x) hy
    _ = (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf B.1).subschemeι z, hzU⟩).asIdeal := by
      apply congrArg PrimeSpectrum.asIdeal
      apply congrArg U.2.primeIdealOf
      apply Subtype.ext
      exact congrArg J.subschemeι hmap

end FiniteDominantMorphism

section FiniteDominantDivisorMap

variable {Y X : Scheme.{u}}
variable (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormalScheme Y]

/-- A finite dominant morphism to a normal locally Noetherian integral scheme preserves
codimension one globally. -/
theorem coheight_apply_eq_one (A : SchemeDivisorPoint X) :
    Order.coheight (f A.1) = 1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hAW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f A.1)) isOpen_univ
  exact coheight_apply_eq_one_of_mem_affine f ⟨W, hW⟩ A hAW

/-- The map on codimension-one scheme points induced by a finite dominant morphism to a
normal locally Noetherian integral target. -/
noncomputable def SchemeDivisorPoint.mapFiniteDominantNormal
    (A : SchemeDivisorPoint X) : SchemeDivisorPoint Y :=
  ⟨f A.1, coheight_apply_eq_one f A⟩

@[simp]
theorem SchemeDivisorPoint.mapFiniteDominantNormal_val
    (A : SchemeDivisorPoint X) :
    (A.mapFiniteDominantNormal f).1 = f A.1 :=
  rfl

/-- The canonical morphism between the reduced closures of a divisor point and its
finite dominant image divisor. -/
noncomputable def SchemeDivisorPoint.closureMapFiniteDominantNormal
    (A : SchemeDivisorPoint X) :
    (pointClosureIdealSheaf A.1).subscheme ⟶
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme :=
  pointClosureSubschemeMap f A.1 (A.mapFiniteDominantNormal f).1 rfl

/-- A chosen source-divisor point above a point of the image divisor. -/
noncomputable def SchemeDivisorPoint.closurePreimageFiniteDominantNormal
    (A : SchemeDivisorPoint X)
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) :
    (pointClosureIdealSheaf A.1).subscheme :=
  pointClosureSubschemePreimage f A.1 (A.mapFiniteDominantNormal f).1 rfl z

@[simp]
theorem SchemeDivisorPoint.closureMap_preimageFiniteDominantNormal
    (A : SchemeDivisorPoint X)
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) :
    A.closureMapFiniteDominantNormal f
        (A.closurePreimageFiniteDominantNormal f z) = z :=
  pointClosureSubschemeMap_preimage f A.1
    (A.mapFiniteDominantNormal f).1 rfl z

/-- The chosen preimage of a target-divisor point belongs to the canonical affine
preimage whenever its target ambient point belongs to the target affine open. -/
theorem SchemeDivisorPoint.closurePreimage_mem_finitePreimage
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z ∈
      (U : Y.Opens)) :
    A.closurePreimageFiniteDominantNormal f z ∈
      (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
        (finitePreimageAffine f U : X.Opens) := by
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1
      (A.mapFiniteDominantNormal f).1 rfl
  let g := I.subschemeMap J f H
  let w := A.closurePreimageFiniteDominantNormal f z
  change f (I.subschemeι w) ∈ (U : Y.Opens)
  have hsquare : J.subschemeι (g w) = f (I.subschemeι w) := by
    change (g ≫ J.subschemeι) w = (I.subschemeι ≫ f) w
    rw [I.subschemeMap_subschemeι J f H]
  rw [← hsquare]
  have hgw : g w = z := by
    simpa only [g, w, I, J, H,
      SchemeDivisorPoint.closureMapFiniteDominantNormal,
      pointClosureSubschemeMap] using
      A.closureMap_preimageFiniteDominantNormal f z
  rwa [hgw]

/-- If a point of the reduced image divisor lies in an affine open, then the generic
point of that divisor lies in the same open.  Open subsets are stable under
generization, and every point of the reduced closure specializes from its generic
point. -/
theorem SchemeDivisorPoint.image_mem_affine_of_closurePoint_mem
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z ∈
      (U : Y.Opens)) :
    (A.mapFiniteDominantNormal f).1 ∈ (U : Y.Opens) := by
  apply specializes_iff_forall_open.mp
    (specializes_iff_mem_closure.mpr
      (pointClosureSubschemeι_mem (A.mapFiniteDominantNormal f).1 z))
  · exact (U : Y.Opens).2
  · exact hzU

end FiniteDominantDivisorMap

section FiniteDominantSelectedDivisorPoint

variable {Y X : Scheme.{u}}
variable (f : X ⟶ Y) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormalScheme X] [IsNormalScheme Y]

attribute [local instance] finitePreimageAlgebra IsLocallyNoetherian.component_noetherian
  finitePreimageAffine_moduleFinite finitePreimageSourceNoetherian
  finitePreimageAffine_faithfulSMul

/-- The union, expressed pointwise on an affine chart, of all height-one branch
components other than the distinguished divisor `D`. -/
def finiteAffineOtherBranchLocus (U : Y.affineOpens)
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (D : HeightOnePrime Γ(Y, U)) : Set (U : Y.Opens) :=
  {y | ∃ E : HeightOnePrime Γ(Y, U),
    E ∈ heightOneBranch
      (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)) ∧
    E ≠ D ∧ E.1.asIdeal ≤ (U.2.primeIdealOf y).asIdeal}

omit [IsNormalScheme X] in
/-- Pointwise nonmembership in the other-branch locus is exactly the avoidance
predicate consumed by the local purity--Abhyankar constructor. -/
theorem avoids_other_heightOneBranch_of_notMem_finiteAffineOtherBranchLocus
    (U : Y.affineOpens)
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (D : HeightOnePrime Γ(Y, U))
    (y : (U : Y.Opens))
    (hy : y ∉ finiteAffineOtherBranchLocus (f := f) U D) :
    ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ D → ¬ E.1.asIdeal ≤ (U.2.primeIdealOf y).asIdeal := by
  intro E hE hED hle
  exact hy ⟨E, hE, hED, hle⟩

omit [IsNormalScheme X] in
/-- The target prime obtained by contracting the chosen source-divisor point is the
ordinary affine prime of the selected target-divisor point. -/
theorem SchemeDivisorPoint.closurePreimage_under_eq_primeIdealOf
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z ∈
      (U : Y.Opens)) :
    (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
      (finitePreimageAffine f U)
      (A.closurePreimageFiniteDominantNormal f z)
      (A.closurePreimage_mem_finitePreimage f U z hzU)).under Γ(Y, U) =
        (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z,
            hzU⟩).asIdeal := by
  let I := pointClosureIdealSheaf A.1
  let B := A.mapFiniteDominantNormal f
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 rfl
  let x := A.closurePreimageFiniteDominantNormal f z
  have hx : x ∈ I.subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens) := by
    simpa only [I, x] using
      A.closurePreimage_mem_finitePreimage f U z hzU
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U
    (finitePreimageAffine f U) le_rfl
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  have hAlg : algebraMap Γ(Y, U) Γ(X, finitePreimageAffine f U) =
      (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
    change (f.app U).hom = (f.appLE U (finitePreimageAffine f U) le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hmap : g x = z := by
    simpa only [g, x, I, J, H, B,
      SchemeDivisorPoint.closureMapFiniteDominantNormal,
      pointClosureSubschemeMap] using
      A.closureMap_preimageFiniteDominantNormal f z
  calc
    (ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).under Γ(Y, U) =
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).comap
            (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
      change (ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).comap
          (algebraMap Γ(Y, U) Γ(X, finitePreimageAffine f U)) = _
      rw [hAlg]
    _ = ambientPrimeOfQuotientPoint J U (g x) hy :=
      ambientPrimeOfQuotientPoint_comap f U
        (finitePreimageAffine f U) le_rfl J I H x hx
    _ = (U.2.primeIdealOf ⟨J.subschemeι (g x), hy⟩).asIdeal :=
      ambientPrimeOfQuotientPoint_eq_primeIdealOf J U (g x) hy
    _ = (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z,
            hzU⟩).asIdeal := by
      apply congrArg PrimeSpectrum.asIdeal
      apply congrArg U.2.primeIdealOf
      apply Subtype.ext
      exact congrArg J.subschemeι hmap

omit [IsNormalScheme X] in
/-- The contraction identity for a specified point of the source divisor closure.

Unlike `closurePreimage_under_eq_primeIdealOf`, this theorem does not replace the
specified point by an arbitrary chosen point in the same fiber.  This is the form needed
by the global chart consumer, which quantifies over a particular source divisor point. -/
theorem SchemeDivisorPoint.closurePoint_under_eq_primeIdealOf
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z ∈
      (U : Y.Opens))
    (hxz : A.closureMapFiniteDominantNormal f x = z) :
    (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
      (finitePreimageAffine f U) x hx).under Γ(Y, U) =
        (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z,
            hzU⟩).asIdeal := by
  let I := pointClosureIdealSheaf A.1
  let B := A.mapFiniteDominantNormal f
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 rfl
  let g := I.subschemeMap J f H
  let map_le := I.subschemeMap_preimage_le J f H U
    (finitePreimageAffine f U) le_rfl
  have hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens) := map_le hx
  have hAlg : algebraMap Γ(Y, U) Γ(X, finitePreimageAffine f U) =
      (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
    change (f.app U).hom = (f.appLE U (finitePreimageAffine f U) le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hmap : g x = z := by
    simpa only [g, I, J, H, B,
      SchemeDivisorPoint.closureMapFiniteDominantNormal,
      pointClosureSubschemeMap] using hxz
  calc
    (ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).under Γ(Y, U) =
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).comap
            (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
      change (ambientPrimeOfQuotientPoint I
        (finitePreimageAffine f U) x hx).comap
          (algebraMap Γ(Y, U) Γ(X, finitePreimageAffine f U)) = _
      rw [hAlg]
    _ = ambientPrimeOfQuotientPoint J U (g x) hy :=
      ambientPrimeOfQuotientPoint_comap f U
        (finitePreimageAffine f U) le_rfl J I H x hx
    _ = (U.2.primeIdealOf ⟨J.subschemeι (g x), hy⟩).asIdeal :=
      ambientPrimeOfQuotientPoint_eq_primeIdealOf J U (g x) hy
    _ = (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z,
            hzU⟩).asIdeal := by
      apply congrArg PrimeSpectrum.asIdeal
      apply congrArg U.2.primeIdealOf
      apply Subtype.ext
      exact congrArg J.subschemeι hmap

/-- Local effective-Cartier data for the canonical image divisor, measured at a
specified point of the source divisor closure.  The dependence on the source point keeps
the local ring aligned with the exact preimage divisor quantified over by the global
chart statement. -/
structure SchemeDivisorPoint.ImageDivisorCartierDataAt
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens)) where
  equation : Localization.AtPrime
    ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
      (finitePreimageAffine f U) x hx).under Γ(Y, U))
  ideal_eq :
    ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).ideal U).map
      (algebraMap Γ(Y, U) (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))) =
      Ideal.span {equation}
  nonZeroDivisor : equation ∈ nonZeroDivisors
    (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine f U) x hx).under Γ(Y, U)))

/-- Construct the local effective-Cartier witness from factoriality of the actual
ambient local ring.  This isolates the only missing standard commutative-algebra input
in Step 0: Stacks 0AG0, regular local rings are UFDs. -/
noncomputable def SchemeDivisorPoint.imageDivisorCartierDataAtOfUFD
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (hBU : (A.mapFiniteDominantNormal f).1 ∈ (U : Y.Opens))
    [UniqueFactorizationMonoid
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))] :
    A.ImageDivisorCartierDataAt f U x hx := by
  letI : Nonempty (U : Y.Opens) :=
    ⟨⟨(A.mapFiniteDominantNormal f).1, hBU⟩⟩
  letI : Nonempty (finitePreimageAffine f U : X.Opens) :=
    ⟨⟨(pointClosureIdealSheaf A.1).subschemeι x, hx⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, finitePreimageAffine f U)
  let I := pointClosureIdealSheaf A.1
  let B := A.mapFiniteDominantNormal f
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 rfl
  let D : Ideal R := J.ideal U
  let Q : Ideal S := ambientPrimeOfQuotientPoint I
    (finitePreimageAffine f U) x hx
  let q : Ideal R := Q.under R
  letI hDprime : D.IsPrime := by
    simpa only [D, J, B] using pointClosureIdealSheaf_ideal_isPrime B.1 U hBU
  letI : Q.IsPrime := inferInstance
  letI : q.IsPrime := Ideal.IsPrime.comap _
  have hPQ : I.ideal (finitePreimageAffine f U) ≤ Q :=
    ideal_le_ambientPrimeOfQuotientPoint I
      (finitePreimageAffine f U) x hx
  have hAlg : algebraMap R S =
      (f.appLE U (finitePreimageAffine f U) le_rfl).hom := by
    change (f.app U).hom = (f.appLE U (finitePreimageAffine f U) le_rfl).hom
    exact congr_arg CommRingCat.Hom.hom f.appLE_eq_app.symm
  have hDP : D.map (algebraMap R S) ≤
      I.ideal (finitePreimageAffine f U) := by
    rw [Ideal.map_le_iff_le_comap]
    rw [hAlg]
    exact I.subschemeMap_ideal_le J f H U (finitePreimageAffine f U) le_rfl
  have hDq : D ≤ q := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hDP.trans hPQ
  have hd : Disjoint (q.primeCompl : Set R) (D : Set R) := by
    rw [Set.disjoint_left]
    exact fun r hrq hrD => hrq (hDq hrD)
  let P : Ideal (Localization.AtPrime q) :=
    D.map (algebraMap R (Localization.AtPrime q))
  letI hPprime : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl
      (Localization.AtPrime q) D hDprime hd
  have hDheight : D.height = 1 := by
    simpa only [D, J, B] using pointClosureIdealSheaf_ideal_height B U hBU
  have hPheight : P.height = 1 :=
    (IsLocalization.height_map_of_disjoint q.primeCompl D hd).trans hDheight
  letI hPprincipal : P.IsPrincipal :=
    UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPheight
  let a := Submodule.IsPrincipal.generator P
  have ha : P = Ideal.span {a} :=
    (Submodule.IsPrincipal.span_singleton_generator P).symm
  have ha0 : a ≠ 0 := by
    intro ha0
    have hPbot : P = ⊥ := by
      rw [ha, ha0]
      simp
    have hzero : P.height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr hPbot
    rw [hzero] at hPheight
    norm_num at hPheight
  refine
    { equation := a
      ideal_eq := ?_
      nonZeroDivisor := ?_ }
  · simpa only [P, D, J, B, q, Q, R, S, I] using ha
  · simpa only [q, Q, R, S, I, mem_nonZeroDivisors_iff_ne_zero] using ha0

/-- Construct the local effective-Cartier witness from the exact low-dimensional
regular-local theorem needed in Step 0.

Unlike `imageDivisorCartierDataAtOfUFD`, this constructor does not assume the full
Stacks 0AG0 statement that every regular local ring is a UFD.  The selected point is
required to have ambient codimension two.  Regularity of the ambient and divisor stalks,
together with codimension one inside the divisor, then makes the localized height-one
prime principal by `heightOne_isPrincipal_of_regularLocalRing_dim_two`.  This is the
narrow argument used in the manuscript. -/
noncomputable def
    SchemeDivisorPoint.imageDivisorCartierDataAtOfRegularDimTwo
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (hxz : A.closureMapFiniteDominantNormal f x = z.1)
    (hambientCoheight : Order.coheight
      ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1) = 2)
    (hambient :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∉
        stalkSingularLocus Y)
    (hdivisor : z.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme) :
    A.ImageDivisorCartierDataAt f U x hx := by
  letI : Nonempty (U : Y.Opens) :=
    ⟨⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
      hzU⟩⟩
  letI : Nonempty (finitePreimageAffine f U : X.Opens) :=
    ⟨⟨(pointClosureIdealSheaf A.1).subschemeι x, hx⟩⟩
  let R := Γ(Y, U)
  let S := Γ(X, finitePreimageAffine f U)
  let I := pointClosureIdealSheaf A.1
  let B := A.mapFiniteDominantNormal f
  let J := pointClosureIdealSheaf B.1
  let D : Ideal R := J.ideal U
  let Q : Ideal S := ambientPrimeOfQuotientPoint I
    (finitePreimageAffine f U) x hx
  let q : Ideal R := Q.under R
  letI hDprime : D.IsPrime := by
    have hBU : B.1 ∈ (U : Y.Opens) := by
      simpa only [B] using A.image_mem_affine_of_closurePoint_mem f U z.1 hzU
    simpa only [D, J] using pointClosureIdealSheaf_ideal_isPrime B.1 U hBU
  letI : Q.IsPrime := inferInstance
  letI : q.IsPrime := Ideal.IsPrime.comap _
  have hq : q = ambientPrimeOfQuotientPoint J U z.1 hzU := by
    calc
      q = (U.2.primeIdealOf
          ⟨(pointClosureIdealSheaf B.1).subschemeι z.1, hzU⟩).asIdeal := by
        simpa only [q, Q, R, S, I, B] using
          A.closurePoint_under_eq_primeIdealOf f U x hx z.1 hzU hxz
      _ = ambientPrimeOfQuotientPoint J U z.1 hzU := by
        symm
        simpa only [J] using
          ambientPrimeOfQuotientPoint_eq_primeIdealOf J U z.1 hzU
  have hDq : D ≤ q := by
    rw [hq]
    exact ideal_le_ambientPrimeOfQuotientPoint J U z.1 hzU
  have hDheight : D.height = 1 := by
    have hBU : B.1 ∈ (U : Y.Opens) := by
      simpa only [B] using A.image_mem_affine_of_closurePoint_mem f U z.1 hzU
    simpa only [D, J] using pointClosureIdealSheaf_ideal_height B U hBU
  let y : (U : Y.Opens) :=
    ⟨J.subschemeι z.1, hzU⟩
  letI : Algebra R (Y.presheaf.stalk (J.subschemeι z.1)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  have hloc : IsLocalization.AtPrime
      (Y.presheaf.stalk (J.subschemeι z.1)) q := by
    simpa only [hq,
      ambientPrimeOfQuotientPoint_eq_primeIdealOf J U z.1 hzU] using
      (U.2.isLocalization_stalk y)
  let e : Localization.AtPrime q ≃+*
      Y.presheaf.stalk (J.subschemeι z.1) :=
    (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q)
      (Y.presheaf.stalk (J.subschemeι z.1))).toRingEquiv
  have regular_ambient_stalk : IsRegularLocalRing
      (Y.presheaf.stalk ((pointClosureIdealSheaf B.1).subschemeι z.1)) := by
    simpa only [B] using
      isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hambient
  have regular_base : IsRegularLocalRing (Localization.AtPrime q) := by
    letI : IsRegularLocalRing
        (Y.presheaf.stalk (J.subschemeι z.1)) := by
      simpa only [J] using regular_ambient_stalk
    exact IsRegularLocalRing.of_ringEquiv e.symm
  have dim_base : ringKrullDim (Localization.AtPrime q) = 2 := by
    calc
      ringKrullDim (Localization.AtPrime q) =
          ringKrullDim (Y.presheaf.stalk (J.subschemeι z.1)) :=
        e.ringKrullDim
      _ = ↑(Order.coheight (J.subschemeι z.1)) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (J.subschemeι z.1)
      _ = 2 := by
        rw [show Order.coheight (J.subschemeι z.1) = 2 by
          simpa only [B, J] using hambientCoheight]
        norm_num
  let ediv :
      (Localization.AtPrime q ⧸
          D.map (algebraMap R (Localization.AtPrime q))) ≃+*
        J.subscheme.presheaf.stalk z.1 :=
    divisorQuotientLocalizationRingEquivStalkOfEq J U z.1 hzU q hq
  have regular_divisor_stalk : IsRegularLocalRing
      ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk z.1) := by
    simpa only [B] using
      isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hdivisor
  have regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) := by
    letI : IsRegularLocalRing (J.subscheme.presheaf.stalk z.1) := by
      simpa only [J] using regular_divisor_stalk
    exact IsRegularLocalRing.of_ringEquiv ediv.symm
  have dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) = 1 := by
    calc
      ringKrullDim
          (Localization.AtPrime q ⧸
            D.map (algebraMap R (Localization.AtPrime q))) =
          ringKrullDim (J.subscheme.presheaf.stalk z.1) :=
        ediv.ringKrullDim
      _ = ↑(Order.coheight z.1) :=
        AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z.1
      _ = 1 := by norm_num [z.2]
  letI : IsRegularLocalRing (Localization.AtPrime q) := regular_base
  letI : IsRegularLocalRing
      (Localization.AtPrime q ⧸
        D.map (algebraMap R (Localization.AtPrime q))) := regular_divisor
  let hex := exists_generator_map_atPrime_regular_dim_two
    D q hDq hDheight dim_base dim_divisor
  let a := Classical.choose hex
  have ha := Classical.choose_spec hex
  have hd : Disjoint (q.primeCompl : Set R) (D : Set R) := by
    rw [Set.disjoint_left]
    exact fun r hrq hrD => hrq (hDq hrD)
  let P : Ideal (Localization.AtPrime q) :=
    D.map (algebraMap R (Localization.AtPrime q))
  have hPheight : P.height = 1 :=
    (IsLocalization.height_map_of_disjoint q.primeCompl D hd).trans hDheight
  have ha0 : a ≠ 0 := by
    intro ha0
    have hPbot : P = ⊥ := by
      rw [show P = Ideal.span {a} by simpa only [P] using ha, ha0]
      simp
    have hzero : P.height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr hPbot
    rw [hzero] at hPheight
    norm_num at hPheight
  refine
    { equation := a
      ideal_eq := ?_
      nonZeroDivisor := ?_ }
  · simpa only [D, J, B, q, Q, R, S, I] using ha
  · simpa only [q, Q, R, S, I, mem_nonZeroDivisors_iff_ne_zero] using ha0

/-- The actual local effective-Cartier equation for the canonical image divisor at a
selected point.  This is the local algebraic content of Step 0 after shrinking away
from the ambient singular locus: the localized divisor ideal is generated by a
nonzerodivisor. -/
structure SchemeDivisorPoint.ImageDivisorCartierData
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    (z : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU : (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z ∈
      (U : Y.Opens)) where
  equation : Localization.AtPrime
    ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
      (finitePreimageAffine f U)
      (A.closurePreimageFiniteDominantNormal f z)
      (A.closurePreimage_mem_finitePreimage f U z hzU)).under Γ(Y, U))
  ideal_eq :
    ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).ideal U).map
      (algebraMap Γ(Y, U) (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z)
          (A.closurePreimage_mem_finitePreimage f U z hzU)).under
            Γ(Y, U)))) = Ideal.span {equation}
  nonZeroDivisor : equation ∈ nonZeroDivisors
    (Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine f U)
        (A.closurePreimageFiniteDominantNormal f z)
        (A.closurePreimage_mem_finitePreimage f U z hzU)).under Γ(Y, U)))

set_option backward.isDefEq.respectTransparency false in
/-- Construct the bounding presentation at an actual codimension-one point of the
image divisor.

Starting from a source divisor point `A`, the target divisor is its finite dominant
image.  The caller selects a codimension-one point `z` on that target divisor.  Lean
then chooses a point of the source divisor above `z`, proves that it lies in the
canonical affine preimage, and obtains the divisor-stalk codimension directly from
`z`.  Thus no arbitrary target divisor, source point, chart-incidence proof, or
divisor-codimension hypothesis remains in the interface. -/
noncomputable def
    SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormal
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1)))
    (ambient_coheight : Order.coheight
      ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1) = 2)
    (regular_divisor : IsRegularLocalRing
      ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme.presheaf.stalk
        z.1))
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
          (by
            apply specializes_iff_forall_open.mp
              (specializes_iff_mem_closure.mpr
                (pointClosureSubschemeι_mem
                  (A.mapFiniteDominantNormal f).1 z.1))
            · exact (U : Y.Opens).2
            · exact hzU) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
            Γ(Y, U)).primeCompl)))
    (abhyankar : ∀ a : Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)),
      Stacks.AbhyankarLemma
        (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine f U)
            (A.closurePreimageFiniteDominantNormal f z.1)
            (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
        (Localization (Algebra.algebraMapSubmonoid
          Γ(X, finitePreimageAffine f U)
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine f U)
            (A.closurePreimageFiniteDominantNormal f z.1)
            (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
              Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation
      (A.closureMapFiniteDominantNormal f)
      (A.closurePreimageFiniteDominantNormal f z.1) := by
  let B := A.mapFiniteDominantNormal f
  let x := A.closurePreimageFiniteDominantNormal f z.1
  have hBU : B.1 ∈ (U : Y.Opens) := by
    apply specializes_iff_forall_open.mp
      (specializes_iff_mem_closure.mpr
        (pointClosureSubschemeι_mem B.1 z.1))
    · exact (U : Y.Opens).2
    · simpa [B] using hzU
  letI : Nonempty (U : Y.Opens) := ⟨⟨B.1, hBU⟩⟩
  have hAU : A.1 ∈ (finitePreimageAffine f U : X.Opens) := by
    change f A.1 ∈ (U : Y.Opens)
    simpa only [B, SchemeDivisorPoint.mapFiniteDominantNormal_val] using hBU
  letI : Nonempty (finitePreimageAffine f U : X.Opens) := ⟨⟨A.1, hAU⟩⟩
  have hx : x ∈
      (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
        (finitePreimageAffine f U : X.Opens) := by
    simpa only [x] using
      A.closurePreimage_mem_finitePreimage f U z.1 hzU
  have hmap : A.closureMapFiniteDominantNormal f x = z.1 := by
    simpa only [x] using A.closureMap_preimageFiniteDominantNormal f z.1
  have regular_ambient' : IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf B.1).subschemeι
          ((A.closureMapFiniteDominantNormal f) x))) := by
    rw [hmap]
    simpa only [B] using regular_ambient
  have ambient_coheight' : Order.coheight
      ((pointClosureIdealSheaf B.1).subschemeι
        ((A.closureMapFiniteDominantNormal f) x)) = 2 := by
    rw [hmap]
    simpa only [B] using ambient_coheight
  have regular_divisor' : IsRegularLocalRing
      ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk
        ((A.closureMapFiniteDominantNormal f) x)) := by
    rw [hmap]
    simpa only [B] using regular_divisor
  have divisor_coheight' : Order.coheight
      ((A.closureMapFiniteDominantNormal f) x) = 1 := by
    rw [hmap]
    exact z.2
  have hresult :=
    pointClosureStalkBoundingLocalizationPresentationOfFiniteDominantNormal
      f U A B rfl hBU x hx
        (by
          simpa only [SchemeDivisorPoint.closureMapFiniteDominantNormal,
            B] using regular_ambient')
        (by
          simpa only [SchemeDivisorPoint.closureMapFiniteDominantNormal,
            B] using ambient_coheight')
        (by
          simpa only [SchemeDivisorPoint.closureMapFiniteDominantNormal,
            B] using regular_divisor')
        (by
          simpa only [SchemeDivisorPoint.closureMapFiniteDominantNormal,
            B] using divisor_coheight')
        (by simpa only [B, x] using havoid)
        (by simpa only [x] using purity)
        (by simpa only [x] using abhyankar)
  simpa only [B, x,
    SchemeDivisorPoint.closureMapFiniteDominantNormal] using hresult

set_option backward.isDefEq.respectTransparency false in
/-- Cartier form of the selected image-divisor-point constructor.

The local equation is the effective-Cartier equation produced in Step 0.  Its
nonzerodivisor property and the codimension-one point `z` determine ambient
dimension two, so this interface has no ambient-codimension argument.  Abhyankar's
lemma is required only for this actual equation. -/
noncomputable def
    SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (a : Localization.AtPrime
      ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
        (finitePreimageAffine f U)
        (A.closurePreimageFiniteDominantNormal f z.1)
        (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
    (ha : ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).ideal U).map
        (algebraMap Γ(Y, U) (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine f U)
            (A.closurePreimageFiniteDominantNormal f z.1)
            (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
              Γ(Y, U)))) = Ideal.span {a})
    (ha_nonZeroDivisor : a ∈ nonZeroDivisors
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U))))
    (regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1)))
    (regular_divisor : IsRegularLocalRing
      ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme.presheaf.stalk
        z.1))
    (havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
          (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
            Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
            Γ(Y, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation
      (A.closureMapFiniteDominantNormal f)
      (A.closurePreimageFiniteDominantNormal f z.1) := by
  let B := A.mapFiniteDominantNormal f
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 rfl
  let x := A.closurePreimageFiniteDominantNormal f z.1
  have hBU : B.1 ∈ (U : Y.Opens) := by
    simpa only [B] using
      A.image_mem_affine_of_closurePoint_mem f U z.1 hzU
  have hAU : A.1 ∈ (finitePreimageAffine f U : X.Opens) := by
    change f A.1 ∈ (U : Y.Opens)
    simpa only [B, SchemeDivisorPoint.mapFiniteDominantNormal_val] using hBU
  have hx : x ∈ I.subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens) := by
    simpa only [I, x] using
      A.closurePreimage_mem_finitePreimage f U z.1 hzU
  letI hJprime : (J.ideal U).IsPrime := by
    simpa only [J, B] using
      pointClosureIdealSheaf_ideal_isPrime B.1 U hBU
  letI hIprime : (I.ideal (finitePreimageAffine f U)).IsPrime := by
    simpa only [I] using pointClosureIdealSheaf_ideal_isPrime A.1
      (finitePreimageAffine f U) hAU
  have hJheight : (J.ideal U).height = 1 := by
    simpa only [J, B] using pointClosureIdealSheaf_ideal_height B U hBU
  have hIheight : (I.ideal (finitePreimageAffine f U)).height = 1 := by
    simpa only [I] using pointClosureIdealSheaf_ideal_height A
      (finitePreimageAffine f U) hAU
  have hmap : A.closureMapFiniteDominantNormal f x = z.1 := by
    simpa only [x] using A.closureMap_preimageFiniteDominantNormal f z.1
  have regular_ambient' : IsRegularLocalRing
      (Y.presheaf.stalk (J.subschemeι ((I.subschemeMap J f H) x))) := by
    change IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf B.1).subschemeι
          ((A.closureMapFiniteDominantNormal f) x)))
    rw [hmap]
    simpa only [B] using regular_ambient
  have regular_divisor' : IsRegularLocalRing
      (J.subscheme.presheaf.stalk ((I.subschemeMap J f H) x)) := by
    change IsRegularLocalRing
      ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk
        ((A.closureMapFiniteDominantNormal f) x))
    rw [hmap]
    simpa only [B] using regular_divisor
  have divisor_coheight' : Order.coheight ((I.subschemeMap J f H) x) = 1 := by
    change Order.coheight ((A.closureMapFiniteDominantNormal f) x) = 1
    rw [hmap]
    exact z.2
  have ha' : (J.ideal U).map
      (algebraMap Γ(Y, U) (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))) =
      Ideal.span {a} := by
    simpa only [I, J, B, x] using ha
  have ha_nonZeroDivisor' : a ∈ nonZeroDivisors
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U))) := by
    simpa only [I, x] using ha_nonZeroDivisor
  have hAvoid' : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U) := by
    simpa only [I, J, B, x, affinePrimeOfSchemeDivisorPoint] using havoid
  have purity' : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) := by
    simpa only [I, x] using purity
  have abhyankar' : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) a := by
    simpa only [I, x] using abhyankar
  have hresult :=
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
      f U J I H x hx hJheight hIheight a ha' ha_nonZeroDivisor'
        regular_ambient' regular_divisor' divisor_coheight' hAvoid' purity' abhyankar'
  simpa only [I, J, H, B, x,
    SchemeDivisorPoint.closureMapFiniteDominantNormal,
    pointClosureSubschemeMap] using hresult

set_option backward.isDefEq.respectTransparency false in
/-- Step-0 constructor at a specified point of the source divisor closure.

This is the quantifier-faithful form for the global application: `x` is the particular
preimage divisor point under consideration, while `z` is its specified image.  Exclusion
from the two pointwise singular loci supplies regularity, and exclusion from the affine
other-branch locus supplies precisely the pointed branch-avoidance predicate. -/
noncomputable def
    SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCorrectionAt
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (hxz : A.closureMapFiniteDominantNormal f x = z.1)
    (cartier : A.ImageDivisorCartierDataAt f U x hx)
    (hambient :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∉
        stalkSingularLocus Y)
    (hdivisor : z.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hbranch :
      (⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
          hzU⟩ : (U : Y.Opens)) ∉
        finiteAffineOtherBranchLocus (f := f) U
          (affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
            (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl))
      cartier.equation) :
    SchemeStalkBoundingLocalizationPresentation
      (A.closureMapFiniteDominantNormal f) x := by
  let B := A.mapFiniteDominantNormal f
  let I := pointClosureIdealSheaf A.1
  let J := pointClosureIdealSheaf B.1
  let H : J ≤ I.map f :=
    pointClosureIdealSheaf_le_map_of_apply_eq f A.1 B.1 rfl
  have hBU : B.1 ∈ (U : Y.Opens) := by
    simpa only [B] using
      A.image_mem_affine_of_closurePoint_mem f U z.1 hzU
  have hAU : A.1 ∈ (finitePreimageAffine f U : X.Opens) := by
    change f A.1 ∈ (U : Y.Opens)
    simpa only [B, SchemeDivisorPoint.mapFiniteDominantNormal_val] using hBU
  letI hJprime : (J.ideal U).IsPrime := by
    simpa only [J, B] using
      pointClosureIdealSheaf_ideal_isPrime B.1 U hBU
  letI hIprime : (I.ideal (finitePreimageAffine f U)).IsPrime := by
    simpa only [I] using pointClosureIdealSheaf_ideal_isPrime A.1
      (finitePreimageAffine f U) hAU
  have hJheight : (J.ideal U).height = 1 := by
    simpa only [J, B] using pointClosureIdealSheaf_ideal_height B U hBU
  have hIheight : (I.ideal (finitePreimageAffine f U)).height = 1 := by
    simpa only [I] using pointClosureIdealSheaf_ideal_height A
      (finitePreimageAffine f U) hAU
  have regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf B.1).subschemeι z.1)) := by
    simpa only [B] using
      isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hambient
  have regular_divisor : IsRegularLocalRing
      ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk z.1) := by
    simpa only [B] using
      isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hdivisor
  have regular_ambient' : IsRegularLocalRing
      (Y.presheaf.stalk (J.subschemeι ((I.subschemeMap J f H) x))) := by
    change IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf B.1).subschemeι
          ((A.closureMapFiniteDominantNormal f) x)))
    rw [hxz]
    exact regular_ambient
  have regular_divisor' : IsRegularLocalRing
      (J.subscheme.presheaf.stalk ((I.subschemeMap J f H) x)) := by
    change IsRegularLocalRing
      ((pointClosureIdealSheaf B.1).subscheme.presheaf.stalk
        ((A.closureMapFiniteDominantNormal f) x))
    rw [hxz]
    exact regular_divisor
  have divisor_coheight' : Order.coheight ((I.subschemeMap J f H) x) = 1 := by
    change Order.coheight ((A.closureMapFiniteDominantNormal f) x) = 1
    rw [hxz]
    exact z.2
  have ha' : (J.ideal U).map
      (algebraMap Γ(Y, U) (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))) =
      Ideal.span {cartier.equation} := by
    simpa only [I, J, B] using cartier.ideal_eq
  have ha_nonZeroDivisor' : cartier.equation ∈ nonZeroDivisors
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U))) := by
    simpa only [I] using cartier.nonZeroDivisor
  have hAvoid' : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ (⟨⟨J.ideal U, hJprime⟩, hJheight⟩ : HeightOnePrime Γ(Y, U)) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U) := by
    intro E hE hED
    rw [A.closurePoint_under_eq_primeIdealOf f U x hx z.1 hzU hxz]
    apply avoids_other_heightOneBranch_of_notMem_finiteAffineOtherBranchLocus
      f U
      (affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
        (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU))
      ⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
        hzU⟩ hbranch E hE
    simpa only [J, B, affinePrimeOfSchemeDivisorPoint] using hED
  have purity' : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)) := by
    simpa only [I] using purity
  have abhyankar' : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint I
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl))
      cartier.equation := by
    simpa only [I] using abhyankar
  have hresult :=
    closedSubschemeStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
      f U J I H x hx hJheight hIheight cartier.equation ha'
        ha_nonZeroDivisor' regular_ambient' regular_divisor' divisor_coheight'
        hAvoid' purity' abhyankar'
  simpa only [I, J, H, B,
    SchemeDivisorPoint.closureMapFiniteDominantNormal,
    pointClosureSubschemeMap] using hresult

set_option backward.isDefEq.respectTransparency false in
/-- Step-0 constructor with the Cartier equation derived from local factoriality.

Once Stacks 0AG0 is available as a `UniqueFactorizationMonoid` instance for the regular
ambient stalk, the only theorem-specific inputs left here are the literal exceptional-
locus exclusions, Zariski--Nagata purity, and Abhyankar's lemma at the constructed
equation. -/
noncomputable def
    SchemeDivisorPoint.closureStalkBoundingLocalizationOfCorrectionUFDAt
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (hxz : A.closureMapFiniteDominantNormal f x = z.1)
    [UniqueFactorizationMonoid
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))]
    (hambient :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∉
        stalkSingularLocus Y)
    (hdivisor : z.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hbranch :
      (⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
          hzU⟩ : (U : Y.Opens)) ∉
        finiteAffineOtherBranchLocus (f := f) U
          (affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
            (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl))
      (A.imageDivisorCartierDataAtOfUFD f U x hx
        (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)).equation) :
    SchemeStalkBoundingLocalizationPresentation
      (A.closureMapFiniteDominantNormal f) x := by
  let cartier := A.imageDivisorCartierDataAtOfUFD f U x hx
    (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)
  exact A.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCorrectionAt
    f U x hx z hzU hxz cartier hambient hdivisor hbranch purity
      (by simpa only [cartier] using abhyankar)

set_option backward.isDefEq.respectTransparency false in
/-- Step-0 constructor using the exact two-dimensional local argument from the
manuscript rather than the full regular-local-UFD theorem.

The ambient codimension-two statement is the only dimension-theoretic input.  The
Cartier equation is then constructed from ambient and divisor regularity, and purity and
Abhyankar are applied to the resulting actual stalk chart. -/
noncomputable def
    SchemeDivisorPoint.closureStalkBoundingLocalizationOfCorrectionRegularDimTwoAt
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine f U : X.Opens))
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (hxz : A.closureMapFiniteDominantNormal f x = z.1)
    (hambientCoheight : Order.coheight
      ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1) = 2)
    (hambient :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∉
        stalkSingularLocus Y)
    (hdivisor : z.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hbranch :
      (⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
          hzU⟩ : (U : Y.Opens)) ∉
        finiteAffineOtherBranchLocus (f := f) U
          (affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
            (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U) x hx).under Γ(Y, U)).primeCompl))
      (A.imageDivisorCartierDataAtOfRegularDimTwo f U x hx z hzU hxz
        hambientCoheight hambient hdivisor).equation) :
    SchemeStalkBoundingLocalizationPresentation
      (A.closureMapFiniteDominantNormal f) x := by
  let cartier := A.imageDivisorCartierDataAtOfRegularDimTwo
    f U x hx z hzU hxz hambientCoheight hambient hdivisor
  exact A.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCorrectionAt
    f U x hx z hzU hxz cartier hambient hdivisor hbranch purity
      (by simpa only [cartier] using abhyankar)

set_option backward.isDefEq.respectTransparency false in
/-- Step-0 form of the selected image-divisor-point constructor.

The ambient and divisor stalks are regular because the selected point was removed
from their pointwise singular loci.  Pointwise removal of every other affine
height-one branch gives the branch-avoidance predicate.  The remaining geometric
input is the actual effective-Cartier equation for the image divisor; purity and
Abhyankar's lemma are then applied only to the local extension and this equation.

This convenience form chooses a source point in the target point's fibre.  The global
chart quantifier must instead use `...OfStep0At`, which preserves its specified source
point. -/
noncomputable def
    SchemeDivisorPoint.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCorrection
    (A : SchemeDivisorPoint X) (U : Y.affineOpens)
    [Algebra ℚ Γ(Y, U)]
    [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (z : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hzU :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∈
        (U : Y.Opens))
    (cartier : A.ImageDivisorCartierData f U z.1 hzU)
    (hambient :
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1 ∉
        stalkSingularLocus Y)
    (hdivisor : z.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme)
    (hbranch :
      (⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
          hzU⟩ : (U : Y.Opens)) ∉
        finiteAffineOtherBranchLocus (f := f) U
          (affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
            (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU)))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
            Γ(Y, U)).primeCompl)))
    (abhyankar : Stacks.AbhyankarLemma
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine f U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under
            Γ(Y, U)).primeCompl)) cartier.equation) :
    SchemeStalkBoundingLocalizationPresentation
      (A.closureMapFiniteDominantNormal f)
      (A.closurePreimageFiniteDominantNormal f z.1) := by
  have regular_ambient : IsRegularLocalRing
      (Y.presheaf.stalk
        ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1)) :=
    isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hambient
  have regular_divisor : IsRegularLocalRing
      ((pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme.presheaf.stalk
        z.1) :=
    isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hdivisor
  have havoid : ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
          (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU) →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine f U)
          (A.closurePreimageFiniteDominantNormal f z.1)
          (A.closurePreimage_mem_finitePreimage f U z.1 hzU)).under Γ(Y, U) := by
    intro E hE hED
    rw [A.closurePreimage_under_eq_primeIdealOf f U z.1 hzU]
    exact avoids_other_heightOneBranch_of_notMem_finiteAffineOtherBranchLocus
      f U
      (affinePrimeOfSchemeDivisorPoint (A.mapFiniteDominantNormal f) U
        (A.image_mem_affine_of_closurePoint_mem f U z.1 hzU))
      ⟨(pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subschemeι z.1,
        hzU⟩ hbranch E hE hED
  exact
    A.closureStalkBoundingLocalizationPresentationOfFiniteDominantNormalOfCartier
      f U z hzU cartier.equation cartier.ideal_eq cartier.nonZeroDivisor
        regular_ambient regular_divisor havoid purity abhyankar

end FiniteDominantSelectedDivisorPoint

section InvariantDivisorIterate

variable {X : Scheme.{u}}
variable (f : X ⟶ X) [IsFinite f] [IsDominant f]
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

/-- The actual self-map induced by an ambient endomorphism on the reduced closure of an
invariant divisor point. -/
noncomputable def SchemeDivisorPoint.invariantClosureMap
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    (pointClosureIdealSheaf A.1).subscheme ⟶
      (pointClosureIdealSheaf A.1).subscheme :=
  pointClosureSubschemeMap f A.1 A.1 hA

omit [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] in
/-- Restriction of a finite endomorphism to an invariant reduced divisor is finite. -/
instance SchemeDivisorPoint.invariantClosureMap_isFinite
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    IsFinite (A.invariantClosureMap f hA) :=
  pointClosureSubschemeMap_isFinite f A.1 A.1 hA

omit [IsDominant f] [IsIntegral X] [IsNormalScheme X] in
/-- Over a locally Noetherian ambient scheme, the finite invariant-divisor restriction
is locally of finite presentation. -/
instance SchemeDivisorPoint.invariantClosureMap_locallyOfFinitePresentation
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) :
    LocallyOfFinitePresentation (A.invariantClosureMap f hA) := by
  letI : IsLocallyNoetherian (pointClosureIdealSheaf A.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureIdealSheaf A.1).subschemeι
  infer_instance

omit [IsFinite f] [IsDominant f] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] in
/-- The iterate of the actual invariant-divisor restriction is the restriction of the
ambient iterate. -/
theorem SchemeDivisorPoint.invariantClosureMap_iterate
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) (m : ℕ) :
    (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom =
      pointClosureSubschemeMap (CategoryTheory.End.of f ^ m).asHom A.1 A.1
        (end_pow_apply_eq_of_apply_eq f A.1 hA m) := by
  exact pointClosureSubschemeMap_iterate f A.1 hA m

local instance invariantIterateFinitePreimageAlgebra
    (m : ℕ) (U : X.affineOpens) :
    Algebra Γ(X, U)
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) :=
  ((CategoryTheory.End.of f ^ m).asHom.app U).hom.toAlgebra

attribute [local instance] IsLocallyNoetherian.component_noetherian

local instance invariantIterateModuleFinite (m : ℕ) (U : X.affineOpens) :
    Module.Finite Γ(X, U)
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) :=
  moduleFinite_finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U

local instance invariantIterateSourceNoetherian (m : ℕ) (U : X.affineOpens) :
    IsNoetherianRing
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) :=
  IsNoetherianRing.of_finite Γ(X, U)
    Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)

local instance invariantIterateFaithfulSMul (m : ℕ) (U : X.affineOpens) :
    FaithfulSMul Γ(X, U)
      Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) :=
  faithfulSMul_finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U

set_option backward.isDefEq.respectTransparency false in
/-- Build the stalk chart for an iterate of the actual restriction to an invariant
divisor closure.

This theorem performs the global-to-local identification formerly left to A6: the map
in the conclusion is the categorical iterate of the actual restricted self-map, while
the affine construction is carried out for the ambient iterate.  Regularity and branch
avoidance come from the literal Step-0 exclusions, and ambient codimension two invokes
the proved low-dimensional principalization theorem.  The only local covering inputs are
Zariski--Nagata purity and Abhyankar's lemma. -/
noncomputable def
    SchemeDivisorPoint.invariantClosureStalkBoundingLocalizationOfCorrectionAt
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)
    (m : ℕ) (U : X.affineOpens)
    [Algebra ℚ Γ(X, U)]
    [Nonempty (U : X.Opens)]
    [Nonempty
      (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens)]
    (x : (pointClosureIdealSheaf A.1).subscheme)
    (hx : x ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U : X.Opens))
    (z : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hzU : (pointClosureIdealSheaf A.1).subschemeι z.1 ∈ (U : X.Opens))
    (hxz : (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom.base x = z.1)
    (hambientCoheight : Order.coheight
      ((pointClosureIdealSheaf A.1).subschemeι z.1) = 2)
    (hambient : (pointClosureIdealSheaf A.1).subschemeι z.1 ∉
      stalkSingularLocus X)
    (hdivisor : z.1 ∉ stalkSingularLocus
      (pointClosureIdealSheaf A.1).subscheme)
    (hbranch :
      (⟨(pointClosureIdealSheaf A.1).subschemeι z.1, hzU⟩ : (U : X.Opens)) ∉
        finiteAffineOtherBranchLocus
          (f := (CategoryTheory.End.of f ^ m).asHom) U
          (affinePrimeOfSchemeDivisorPoint A U
            (by
              apply specializes_iff_forall_open.mp
                (specializes_iff_mem_closure.mpr
                  (pointClosureSubschemeι_mem A.1 z.1))
              · exact (U : X.Opens).2
              · exact hzU)))
    (purity : Stacks.ZariskiNagataPurity
      (Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) x hx).under Γ(X, U)))
      (Localization (Algebra.algebraMapSubmonoid
        Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) x hx).under
            Γ(X, U)).primeCompl)))
    (abhyankar : ∀ a : Localization.AtPrime
        ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) x hx).under Γ(X, U)),
      Stacks.AbhyankarLemma
        (Localization.AtPrime
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) x hx).under Γ(X, U)))
        (Localization (Algebra.algebraMapSubmonoid
          Γ(X, finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U)
          ((ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
            (finitePreimageAffine (CategoryTheory.End.of f ^ m).asHom U) x hx).under
              Γ(X, U)).primeCompl)) a) :
    SchemeStalkBoundingLocalizationPresentation
      (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom x := by
  let fM : X ⟶ X := (CategoryTheory.End.of f ^ m).asHom
  let hAM : fM A.1 = A.1 := end_pow_apply_eq_of_apply_eq f A.1 hA m
  let gM : (pointClosureIdealSheaf A.1).subscheme ⟶
      (pointClosureIdealSheaf A.1).subscheme :=
    pointClosureSubschemeMap fM A.1 A.1 hAM
  letI : IsFinite fM := isFinite_end_pow f m
  letI : IsDominant fM := isDominant_end_pow f m
  have hiter : (CategoryTheory.End.of (A.invariantClosureMap f hA) ^ m).asHom = gM := by
    simpa only [fM, gM, hAM] using A.invariantClosureMap_iterate f hA m
  have hxz' : gM x = z.1 := by
    rw [← hiter]
    exact hxz
  have hAU : A.1 ∈ (U : X.Opens) := by
    apply specializes_iff_forall_open.mp
      (specializes_iff_mem_closure.mpr (pointClosureSubschemeι_mem A.1 z.1))
    · exact (U : X.Opens).2
    · exact hzU
  have regular_ambient : IsRegularLocalRing
      (X.presheaf.stalk ((pointClosureIdealSheaf A.1).subschemeι z.1)) :=
    isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hambient
  have regular_divisor : IsRegularLocalRing
      ((pointClosureIdealSheaf A.1).subscheme.presheaf.stalk z.1) :=
    isRegularLocalRing_stalk_of_notMem_stalkSingularLocus hdivisor
  have regular_ambient' : IsRegularLocalRing
      (X.presheaf.stalk ((pointClosureIdealSheaf A.1).subschemeι (gM x))) := by
    rw [hxz']
    exact regular_ambient
  have ambient_coheight' : Order.coheight
      ((pointClosureIdealSheaf A.1).subschemeι (gM x)) = 2 := by
    rw [hxz']
    exact hambientCoheight
  have regular_divisor' : IsRegularLocalRing
      ((pointClosureIdealSheaf A.1).subscheme.presheaf.stalk (gM x)) := by
    rw [hxz']
    exact regular_divisor
  have divisor_coheight' : Order.coheight (gM x) = 1 := by
    rw [hxz']
    exact z.2
  have havoid : ∀ E ∈ heightOneBranch
        (R := Γ(X, U))
        (S := Γ(X, finitePreimageAffine fM U)),
      E ≠ affinePrimeOfSchemeDivisorPoint A U hAU →
      ¬ E.1.asIdeal ≤
        (ambientPrimeOfQuotientPoint (pointClosureIdealSheaf A.1)
          (finitePreimageAffine fM U) x hx).under Γ(X, U) := by
    intro E hE hEA
    rw [pointClosurePoint_under_eq_primeIdealOf
      fM U A A hAM x hx z.1 hzU hxz']
    exact avoids_other_heightOneBranch_of_notMem_finiteAffineOtherBranchLocus
      fM U (affinePrimeOfSchemeDivisorPoint A U hAU)
      ⟨(pointClosureIdealSheaf A.1).subschemeι z.1, hzU⟩
      (by simpa only [fM] using hbranch) E hE hEA
  have hresult :=
    pointClosureStalkBoundingLocalizationPresentationOfFiniteDominantNormal
      fM U A A hAM hAU x hx regular_ambient' ambient_coheight'
        regular_divisor' divisor_coheight' havoid
        (by simpa only [fM] using purity)
        (by simpa only [fM] using abhyankar)
  rw [hiter]
  exact hresult

end InvariantDivisorIterate

end Pcf
