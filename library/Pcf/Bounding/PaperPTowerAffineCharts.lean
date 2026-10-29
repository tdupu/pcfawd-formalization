/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupBranchOpenRestriction
public import Pcf.Bounding.PrimaryFibresScheme

/-!
# Affine charts of a normal tower

For `paper-p.tex`, Theorem `thm:tower-restrict`, each nonempty affine open
`U = Spec R` of the base `X₀` of a tower of normal varieties gives a sequence
of finite dominant normal affine covers: the full inverse images of `U`
under the composites `fₙ₊₁`, which are affine because finite morphisms are
affine. The chart squares commute and each source chart is the full inverse
image of `U`. These are the commuting open-chart presentations required by
`NormalAffineFiniteCover.normalizedReesTowerW_finite_of_open_towerCharts`.
-/

@[expose] public section

namespace Pcf.PaperPTower

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Pcf.Bounding.AllCodimBlowup

universe u

noncomputable section

set_option linter.style.haveILetI false

namespace Tower

variable {k : Type u} [Field k] (T : Tower k) [∀ n, IsNormalScheme (T.X n)]
  (U : (T.X 0).affineOpens) [Nonempty (U : (T.X 0).Opens)]

/-- The inverse image chart of `U` under the composite `fₙ₊₁`. -/
abbrev chartOpen (n : ℕ) : (T.X (n + 1)).Opens := T.composite (n + 1) ⁻¹ᵁ (U : (T.X 0).Opens)

omit [∀ n, IsNormalScheme (T.X n)] [Nonempty (U : (T.X 0).Opens)] in
theorem chartOpen_isAffine (n : ℕ) : IsAffineOpen (T.chartOpen U n) :=
  U.2.preimage (T.composite (n + 1))

omit [∀ n, IsNormalScheme (T.X n)] in
instance chartOpen_nonempty (n : ℕ) : Nonempty (T.chartOpen U n) := by
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty (U : (T.X 0).Opens))
  obtain ⟨x, rfl⟩ := T.composite_surjective (n + 1) y
  exact ⟨⟨x, hy⟩⟩

/-- The `n`-th affine chart of the tower over `U`, as a finite dominant
cover of normal domains.

`paper-p.tex` correspondence: Theorem 8.2 (`thm:tower-restrict`). -/
def chartCover (n : ℕ) : NormalAffineFiniteCover Γ(T.X 0, U) where
  S := Γ(T.X (n + 1), T.chartOpen U n)
  commRing := inferInstance
  domain := inferInstance
  integrallyClosed :=
    IsNormalScheme.component_integrallyClosed ⟨T.chartOpen U n, T.chartOpen_isAffine U n⟩
  f := ((T.composite (n + 1)).app U).hom
  injective := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Pcf.Bounding.appLE_injective_of_dominant (T.composite (n + 1)) U _ _
  finite := (T.composite (n + 1)).finite_app U U.2

/-- The source chart inclusion `Spec Sₙ ⟶ Xₙ₊₁`. -/
def chartSourceι (n : ℕ) : Spec (.of (T.chartCover U n).S) ⟶ T.X (n + 1) :=
  (T.chartOpen_isAffine U n).fromSpec

instance chartSourceι_isOpenImmersion (n : ℕ) : IsOpenImmersion (T.chartSourceι U n) := by
  change IsOpenImmersion (T.chartOpen_isAffine U n).fromSpec
  infer_instance

/-- The chart squares commute. -/
theorem chartCover_comm (n : ℕ) :
    (T.chartCover U n).specMap ≫ U.2.fromSpec =
      T.chartSourceι U n ≫ T.composite (n + 1) := by
  change Spec.map ((T.composite (n + 1)).app U) ≫ U.2.fromSpec = _
  rw [Scheme.Hom.app_eq_appLE]
  exact IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 (T.chartOpen_isAffine U n) _

/-- Each source chart is the full inverse image of the target chart. -/
theorem chartCover_range (n : ℕ) (a : T.X (n + 1))
    (ha : T.composite (n + 1) a ∈ Set.range U.2.fromSpec) :
    a ∈ Set.range (T.chartSourceι U n) := by
  change a ∈ Set.range (T.chartOpen_isAffine U n).fromSpec
  rw [IsAffineOpen.range_fromSpec]
  have hr := U.2.range_fromSpec
  rw [hr] at ha
  exact ha

#print axioms chartCover
#print axioms chartCover_comm
#print axioms chartCover_range

end Tower
end
end Pcf.PaperPTower
