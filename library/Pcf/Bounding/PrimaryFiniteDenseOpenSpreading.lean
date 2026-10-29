/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryGenericFibreInjection
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Dense-open spreading for finite morphisms

Stacks Tag 0578 spreads geometric reducedness of a finite-type morphism's
generic fibre to a dense open of the base. The full result needs generic
flatness and a geometric reducedness spreading theorem. For finite maps, a
closed-image argument already spreads any open source locus containing the
whole generic fibre. We record that topological step and its smooth-locus
instance, a restricted but concrete part of the source argument.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- For a finite morphism, an open source condition holding everywhere on
the fibre over a base point holds on the full inverse image of some open
neighborhood of that point. -/
theorem finite_exists_open_fibre_neighborhood
    (y : Y) (V : X.Opens)
    (hy : ∀ x : X, f x = y → x ∈ V) :
    ∃ U : Y.Opens, y ∈ U ∧ ∀ x : X, f x ∈ U → x ∈ V := by
  let C : Set Y := f '' (V : Set X)ᶜ
  have hC : IsClosed C := f.isClosedMap _ V.2.isClosed_compl
  let U : Y.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · intro hyC
    obtain ⟨x, hxV, hxy⟩ := hyC
    exact hxV (hy x hxy)
  · intro x hxU
    by_contra hxV
    exact hxU ⟨x, hxV, rfl⟩

/-- If the generic fibre of a finite map lies in an open source locus,
that locus contains the inverse image of a dense open of the integral
base. -/
theorem finite_exists_denseOpen_genericFibre_locus
    [IsIntegral Y] (V : X.Opens)
    (hgeneric : ∀ x : X, f x = genericPoint Y → x ∈ V) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧
      ∀ x : X, f x ∈ U → x ∈ V := by
  obtain ⟨U, hη, hU⟩ :=
    finite_exists_open_fibre_neighborhood f (genericPoint Y) V hgeneric
  exact ⟨U, U.2.dense ⟨genericPoint Y, hη⟩, hU⟩

/-- Restricted Tag 0578 step: for a finite map of finite presentation,
formal smoothness at every point of its generic fibre spreads to all
source points above a dense open of the base. -/
theorem finite_exists_denseOpen_smoothLocus
    [IsIntegral Y] [LocallyOfFinitePresentation f]
    (hgeneric : ∀ x : X, f x = genericPoint Y →
      (f.stalkMap x).hom.FormallySmooth) :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧
      ∀ x : X, f x ∈ U → x ∈ f.smoothLocus := by
  exact finite_exists_denseOpen_genericFibre_locus f f.smoothLocus hgeneric

#print axioms finite_exists_open_fibre_neighborhood
#print axioms finite_exists_denseOpen_genericFibre_locus
#print axioms finite_exists_denseOpen_smoothLocus

end Pcf.Bounding.PrimaryFibres
