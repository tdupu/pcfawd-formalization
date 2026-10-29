/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalVariety
public import Pcf.Examples.PaperP.MonodromyLossDescentFinal
public import Pcf.Examples.PaperP.PinchedPushoutGlobal

/-!
# The descended map `f : X → X` of `ex:monodromy-loss` is finite

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "The map `F` descends to a finite map
`f` of the resulting nonnormal variety `X`."

* `isFinite_of_surjective_comp` (general): if `ν : Y → X` is surjective, `ν ≫ g` is finite, and
  `g` is separated and locally of finite type, then `g` is finite (`g` is universally closed and
  has finite fibres, so it is proper and quasi-finite: Zariski's main theorem in Mathlib,
  `IsFinite.of_isProper_of_locallyQuasiFinite`);
* `nu_epi`; `bigF_sEP` (`F` is over `k`); **`fX_sX`**: `f` is a `k`-morphism;
* **`fX_isFinite`**: `f` is finite.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.FiniteCoverDescent

set_option linter.style.haveILetI false

universe u

/-- A morphism that becomes finite after precomposing with a surjection is finite, provided it is
separated and locally of finite type. -/
theorem isFinite_of_surjective_comp {X Y Z : Scheme.{u}} (ν : Y ⟶ X) (g : X ⟶ Z) [Surjective ν]
    [IsFinite (ν ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] : IsFinite g := by
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective ν g
  haveI : IsProper g := ⟨⟩
  haveI : LocallyQuasiFinite g := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton g fun z => ?_
    have h := (ν ≫ g).finite_preimage_singleton z
    have : g ⁻¹' {z} = ν '' ((ν ≫ g) ⁻¹' {z}) := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, rfl⟩ := ν.surjective x
        exact ⟨y, by simpa using hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [this]
    exact h.image _
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end Pcf.Examples.PaperP.FiniteCoverDescent

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open BasilicaProjectiveScheme (grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `ν` is an epimorphism of schemes. -/
instance nu_epi : Epi (nu k i hi) := PinchedPushoutGlobal.epi_of_surjective_of_isSchemeTheoreticallyDominant _

/-- `F` is a `k`-morphism. -/
@[reassoc] theorem bigF_sEP : bigF k i hi ≫ sEP k = sEP k := by
  rw [sEP, ← Category.assoc, bigF_fst, Category.assoc, phi_toSpec]

/-- **`f` is a `k`-morphism.** -/
@[reassoc] theorem fX_sX : fX k i hi ≫ sX k i hi = sX k i hi := by
  rw [← cancel_epi (nu k i hi), nu_fX_assoc, nu_sX, bigF_sEP]

instance fX_isSeparated : IsSeparated (fX k i hi) := by
  haveI : IsSeparated (fX k i hi ≫ sX k i hi) := by rw [fX_sX]; infer_instance
  exact IsSeparated.of_comp (fX k i hi) (sX k i hi)

instance fX_locallyOfFiniteType : LocallyOfFiniteType (fX k i hi) := by
  haveI : LocallyOfFiniteType (fX k i hi ≫ sX k i hi) := by rw [fX_sX]; infer_instance
  exact locallyOfFiniteType_of_comp (fX k i hi) (sX k i hi)

/-- **`f : X → X` is finite.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
instance fX_isFinite : IsFinite (fX k i hi) := by
  haveI : IsFinite (nu k i hi ≫ fX k i hi) := by rw [nu_fX]; infer_instance
  exact FiniteCoverDescent.isFinite_of_surjective_comp (nu k i hi) (fX k i hi)

#print axioms FiniteCoverDescent.isFinite_of_surjective_comp
#print axioms fX_sX
#print axioms fX_isFinite

end Pcf.Examples.PaperP.MonodromyLossGlobal
