/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Tactic
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual affine schemes in `ex:smooth-restriction`

We use `K[y][x]` as the plane coordinate ring. The ambient pullback sends
`x` to `u²` and `y` to `v`. The quotients by `x-y` and `x-y²` define the
source line and target parabola. Their restriction map is an actual scheme
isomorphism, with a checked commutative square of closed immersions.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperSmoothRestriction

open Polynomial CategoryTheory AlgebraicGeometry

variable (K : Type*) [CommRing K]

abbrev PlaneRing := Polynomial (Polynomial K)

def ambientPullback : PlaneRing K →+* PlaneRing K :=
  (Polynomial.expand (Polynomial K) 2).toRingHom

@[simp] theorem ambientPullback_X : ambientPullback K X = X ^ 2 := by
  exact Polynomial.expand_X _

@[simp] theorem ambientPullback_C (p : Polynomial K) :
    ambientPullback K (C p) = C p := by
  exact Polynomial.expand_C _ _

theorem ambientPullback_injective : Function.Injective (ambientPullback K) :=
  Polynomial.expand_injective (by decide)

/-- Squaring one variable is a finite ring map over any coefficient ring. -/
theorem ambientPullback_finite : (ambientPullback K).Finite := by
  let : Algebra (PlaneRing K) (PlaneRing K) := (ambientPullback K).toAlgebra
  let : Module (PlaneRing K) (PlaneRing K) := (ambientPullback K).toAlgebra.toModule
  have hx : IsIntegral (PlaneRing K) (X : PlaneRing K) := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [← ambientPullback_X K]
    exact isIntegral_algebraMap
  have ha : Algebra.adjoin (PlaneRing K) ({X} : Set (PlaneRing K)) = ⊤ := by
    apply Algebra.eq_top_iff.mpr
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact add_mem hp hq
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      apply mul_mem
      · have h := (Algebra.adjoin (PlaneRing K) ({X} : Set (PlaneRing K))).algebraMap_mem (C a)
        simpa only [RingHom.algebraMap_toAlgebra, ambientPullback_C] using h
      · exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton X)) n
  have hfg := hx.fg_adjoin_singleton
  rw [ha] at hfg
  exact Module.finite_def.mpr hfg

/-- The source line has equation `u-v=0`, equivalent to the manuscript's `v-u=0`. -/
def lineIdeal : Ideal (PlaneRing K) := Ideal.span {X - C X}

def parabolaIdeal : Ideal (PlaneRing K) := Ideal.span {X - C (X ^ 2)}

abbrev LineRing := PlaneRing K ⧸ lineIdeal K
abbrev ParabolaRing := PlaneRing K ⧸ parabolaIdeal K

def lineEquiv : LineRing K ≃ₐ[Polynomial K] Polynomial K :=
  Polynomial.quotientSpanXSubCAlgEquiv X

def parabolaEquiv : ParabolaRing K ≃ₐ[Polynomial K] Polynomial K :=
  Polynomial.quotientSpanXSubCAlgEquiv (X ^ 2)

/-- The ring isomorphism underlying the restriction, identified with the identity
on the shared parameter ring `K[t]`. -/
def restrictionEquiv : ParabolaRing K ≃+* LineRing K :=
  ((parabolaEquiv K).trans (lineEquiv K).symm).toRingEquiv

theorem restrictionPullback_square :
    (restrictionEquiv K).toRingHom.comp (Ideal.Quotient.mk (parabolaIdeal K)) =
      (Ideal.Quotient.mk (lineIdeal K)).comp (ambientPullback K) := by
  apply RingHom.ext
  intro p
  apply (lineEquiv K).injective
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    restrictionEquiv, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  change p.eval (X ^ 2) = (ambientPullback K p).eval X
  simp only [ambientPullback, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    Polynomial.expand_eq_comp_X_pow, Polynomial.eval_comp, Polynomial.eval_pow,
    Polynomial.eval_X]

abbrev plane : Scheme := Spec (.of (PlaneRing K))
abbrev line : Scheme := Spec (.of (LineRing K))
abbrev parabola : Scheme := Spec (.of (ParabolaRing K))

def ambientMap : plane K ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (ambientPullback K))

theorem ambient_finite : IsFinite (ambientMap K) :=
  (IsFinite.SpecMap_iff _).mpr (ambientPullback_finite K)

theorem ambient_surjective : Surjective (ambientMap K) := by
  constructor
  exact (ambientPullback_finite K).to_isIntegral.comap_surjective
    (ambientPullback_injective K)

def lineImmersion : line K ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (lineIdeal K)))

def parabolaImmersion : parabola K ⟶ plane K :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (parabolaIdeal K)))

def restrictionMap : line K ⟶ parabola K :=
  Spec.map (CommRingCat.ofHom (restrictionEquiv K).toRingHom)

instance restrictionMap_isIso : IsIso (restrictionMap K) := by
  let e : CommRingCat.of (ParabolaRing K) ≅ CommRingCat.of (LineRing K) :=
    RingEquiv.toCommRingCatIso (restrictionEquiv K)
  change IsIso (Scheme.Spec.map e.hom.op)
  infer_instance

def restrictionIso : line K ≅ parabola K := asIso (restrictionMap K)

/-- This square verifies that the displayed isomorphism really restricts the
ambient squaring map to the closed line and its parabola image. -/
theorem restriction_square :
    restrictionMap K ≫ parabolaImmersion K = lineImmersion K ≫ ambientMap K := by
  simp only [restrictionMap, parabolaImmersion, lineImmersion, ambientMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [restrictionPullback_square]

instance lineImmersion_isClosedImmersion : IsClosedImmersion (lineImmersion K) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance parabolaImmersion_isClosedImmersion : IsClosedImmersion (parabolaImmersion K) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem restriction_etale : Etale (restrictionMap K) := inferInstance

theorem restriction_finite : IsFinite (restrictionMap K) := inferInstance

theorem restriction_surjective : Surjective (restrictionMap K) := inferInstance

/-- Equality of the actual topological images, including nonclosed prime points. -/
theorem ambient_line_image :
    (ambientMap K) '' Set.range (lineImmersion K) = Set.range (parabolaImmersion K) := by
  ext y
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨restrictionMap K t, ?_⟩
    exact congrArg (fun f : line K ⟶ plane K => f t) (restriction_square K)
  · rintro ⟨b, rfl⟩
    obtain ⟨t, rfl⟩ := (restrictionMap K).surjective b
    refine ⟨lineImmersion K t, ⟨t, rfl⟩, ?_⟩
    exact (congrArg (fun f : line K ⟶ plane K => f t) (restriction_square K)).symm

/-- Every actual scheme-theoretic fiber of the restriction is reduced. -/
theorem restriction_fiber_isReduced (y : parabola K) :
    AlgebraicGeometry.IsReduced ((restrictionMap K).fiber y) := by
  let : IsIso ((restrictionMap K).fiberToSpecResidueField y) := by
    exact (IsPullback.of_hasPullback (restrictionMap K)
      ((parabola K).fromSpecResidueField y)).isIso_snd_of_isIso (restrictionMap_isIso K)
  exact isReduced_of_isOpenImmersion ((restrictionMap K).fiberToSpecResidueField y)

/-- The all-point nonreduced-fiber locus is empty; in particular any
codimension-one sublocus selected from it is empty. -/
theorem restriction_nonreducedFiberLocus_empty :
    {y : parabola K | ¬ AlgebraicGeometry.IsReduced ((restrictionMap K).fiber y)} = ∅ := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact restriction_fiber_isReduced K y

#print axioms PlaneRing
#check @PlaneRing
#print axioms ambientPullback
#check @ambientPullback
#print axioms ambientPullback_X
#check @ambientPullback_X
#print axioms ambientPullback_C
#check @ambientPullback_C
#print axioms ambientPullback_injective
#check @ambientPullback_injective
#print axioms ambientPullback_finite
#check @ambientPullback_finite
#print axioms lineIdeal
#check @lineIdeal
#print axioms parabolaIdeal
#check @parabolaIdeal
#print axioms LineRing
#check @LineRing
#print axioms ParabolaRing
#check @ParabolaRing
#print axioms lineEquiv
#check @lineEquiv
#print axioms parabolaEquiv
#check @parabolaEquiv
#print axioms restrictionEquiv
#check @restrictionEquiv
#print axioms restrictionPullback_square
#check @restrictionPullback_square
#print axioms plane
#check @plane
#print axioms line
#check @line
#print axioms parabola
#check @parabola
#print axioms ambientMap
#check @ambientMap
#print axioms ambient_finite
#check @ambient_finite
#print axioms ambient_surjective
#check @ambient_surjective
#print axioms lineImmersion
#check @lineImmersion
#print axioms parabolaImmersion
#check @parabolaImmersion
#print axioms restrictionMap
#check @restrictionMap
#print axioms restrictionMap_isIso
#check @restrictionMap_isIso
#print axioms restrictionIso
#check @restrictionIso
#print axioms restriction_square
#check @restriction_square
#print axioms lineImmersion_isClosedImmersion
#check @lineImmersion_isClosedImmersion
#print axioms parabolaImmersion_isClosedImmersion
#check @parabolaImmersion_isClosedImmersion
#print axioms restriction_etale
#check @restriction_etale
#print axioms restriction_finite
#check @restriction_finite
#print axioms restriction_surjective
#check @restriction_surjective
#print axioms ambient_line_image
#check @ambient_line_image
#print axioms restriction_fiber_isReduced
#check @restriction_fiber_isReduced
#print axioms restriction_nonreducedFiberLocus_empty
#check @restriction_nonreducedFiberLocus_empty

end Pcf.Examples.CharZeroPaperSmoothRestriction
