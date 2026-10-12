/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.TensorProduct.Pi
import Pcf.Stacks.Abhyankar.StandardCover

/-!
# Base change of standard tame covers

The standard root algebra and a finite product of standard root algebras commute with arbitrary
base change.  These explicit equivalences are the polynomial bookkeeping required when the
strict-local presentation in Stacks Tag `0EYG` is descended to a pointed etale stage.
-/

open TensorProduct

universe u

namespace Pcf.Stacks

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

#print axioms standardCoverBaseChangeEquiv
#print axioms standardCoversBaseChangeEquiv

end Pcf.Stacks
