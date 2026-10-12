/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Pcf.Stacks.Purity.IntegralClosure

/-!
# Finite normal model of a separable generic fibre

In Stacks Tag `0BM9`, the generic fibre of an arbitrary finite étale cover of a punctured
spectrum is a finite product of finite separable field extensions.  Taking the integral closure
in each field and their finite product gives the candidate finite normal algebra over the base.
This file establishes finiteness and Stacks-normality, including the disconnected case.
-/

noncomputable section

open CategoryTheory
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (I : Type u) [Finite I] (L : I → Type u) [∀ i, Field (L i)]
  [∀ i, Algebra K (L i)] [∀ i, FiniteDimensional K (L i)]
  [∀ i, Algebra.IsSeparable K (L i)]

/-- The finite product of the integral closures of `R` in the field factors of a finite
separable generic fibre.  The source `R → K` is the fraction-field map. -/
noncomputable def finiteNormalModel : CommAlgCat R := by
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  exact .of R (∀ i, integralClosure R (L i))

/-- The candidate normal model is finite over the base, even when it has several components. -/
theorem finiteNormalModel_moduleFinite : Module.Finite R (finiteNormalModel R K I L) := by
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  letI (i : I) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
      (A := R) (K := K) (L := L i) (C := integralClosure R (L i))
  change Module.Finite R (∀ i, integralClosure R (L i))
  infer_instance

omit [IsIntegrallyClosed R] [IsNoetherianRing R]
  [∀ i, Algebra.IsSeparable K (L i)] in
/-- The candidate model is normal in the literal Stacks sense: each local ring at a prime is a
normal domain, although the product itself can have zero divisors. -/
theorem finiteNormalModel_isStacksNormalRing :
    IsStacksNormalRing (finiteNormalModel R K I L) := by
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  have hi (i : I) : IsStacksNormalRing (integralClosure R (L i)) :=
    IsIntegralClosure.isStacksNormalRing_of_finiteExtension
      (A := R) (K := K) (L := L i) (C := integralClosure R (L i))
  change IsStacksNormalRing (∀ i, integralClosure R (L i))
  exact IsStacksNormalRing.pi hi

end Pcf.Stacks
