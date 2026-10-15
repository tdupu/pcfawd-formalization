/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.TensorProduct.Pi
public import Pcf.Stacks.Abhyankar.StandardCoverPresentation

/-!
# Base change of standard tame covers

The standard root algebra and a finite product of standard root algebras commute with arbitrary
base change.  These explicit equivalences are the polynomial bookkeeping required when the
strict-local presentation in Stacks Tag `0EYG` is descended to a pointed etale stage.
-/

@[expose] public section

open TensorProduct

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- A standard root cover commutes with arbitrary base change. -/
noncomputable def standardCoverBaseChangeEquiv
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (unit : Rˣ) (a : R) (e : ℕ) :
    T ⊗[R] AdjoinRoot (Pcf.LocalModel.localPoly unit a e) ≃ₐ[T]
      AdjoinRoot (Pcf.LocalModel.localPoly
        (Units.map (algebraMap R T) unit) (algebraMap R T a) e) := by
  let p := Pcf.LocalModel.localPoly unit a e
  let q := p.map
    (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := R)).toRingHom
  let qT := Pcf.LocalModel.localPoly
    (Units.map (algebraMap R T) unit) (algebraMap R T a) e
  refine (AdjoinRoot.tensorAlgEquiv p q rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R T T) q qT ?_)
  rw [show Polynomial.map (Algebra.TensorProduct.rid R T T) q = qT by
    simp [p, q, qT, Pcf.LocalModel.localPoly, Algebra.smul_def]]

/-- A finite disjoint union of standard root covers commutes with arbitrary base change. -/
noncomputable def standardCoversBaseChangeEquiv
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (i : Type) [Fintype i] (unit : i → Rˣ) (a : R) (e : i → ℕ) :
    T ⊗[R] (∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j) a (e j))) ≃ₐ[T]
      ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly
        (Units.map (algebraMap R T) (unit j)) (algebraMap R T a) (e j)) := by
  classical
  exact (Algebra.TensorProduct.piRight R T T
      (fun j ↦ AdjoinRoot (Pcf.LocalModel.localPoly (unit j) a (e j)))).trans
    (AlgEquiv.piCongrRight (fun j ↦ standardCoverBaseChangeEquiv (unit j) a (e j)))

/-- Base change of a finite standard cover, with the transported coefficients identified with
a specified family of units in the target. -/
noncomputable def standardCoversBaseChangeEquivOfUnitEq
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (i : Type) [Fintype i] (unit : i → Rˣ) (unitT : i → Tˣ)
    (hunit : ∀ j, Units.map (algebraMap R T) (unit j) = unitT j)
    (a : R) (e : i → ℕ) :
    T ⊗[R] (∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unit j) a (e j))) ≃ₐ[T]
      ∀ j, AdjoinRoot (Pcf.LocalModel.localPoly (unitT j) (algebraMap R T a) (e j)) := by
  classical
  exact (standardCoversBaseChangeEquiv i unit a e).trans
    (AlgEquiv.piCongrRight (fun j ↦ AdjoinRoot.algEquivOfEq T _ _ (by rw [hunit j])))

/-- Being a finite disjoint union of standard tame covers is preserved by arbitrary base
change. -/
theorem IsFiniteDisjointUnionOfStandardTameCovers.baseChange
    {R C T : Type u} [CommRing R] [CommRing C] [CommRing T]
    [Algebra R C] [Algebra R T] {a : R}
    (h : IsFiniteDisjointUnionOfStandardTameCovers R C a) :
    IsFiniteDisjointUnionOfStandardTameCovers T (T ⊗[R] C) (algebraMap R T a) := by
  classical
  rcases h with ⟨i, hi, e, unit, he, heUnit, ⟨hC⟩⟩
  letI := hi
  refine ⟨i, inferInstance, e, fun j ↦ Units.map (algebraMap R T) (unit j), he,
    fun j ↦ by simpa using (heUnit j).map (algebraMap R T), ?_⟩
  exact ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) hC).trans
    (standardCoversBaseChangeEquiv i unit a e)⟩

#print axioms standardCoverBaseChangeEquiv
#print axioms standardCoversBaseChangeEquiv
#print axioms standardCoversBaseChangeEquivOfUnitEq
#print axioms IsFiniteDisjointUnionOfStandardTameCovers.baseChange

end Pcf.Stacks
