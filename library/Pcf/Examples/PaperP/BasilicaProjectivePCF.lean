/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaProjectiveEtale
public import Pcf.Palomar.Statement

/-!
# Ramification-based PCF for the actual global basilica morphism

For `latex/paper-p.tex`, Example `ex:basilica`, every noncritical scheme
point has ramification index one along the actual stalk map. Therefore
the actual ramification-index postcritical set is contained in the
proved finite three-point non-étale orbit, and the existing
`Pcf.Palomar.IsPCF` predicate holds in characteristic different from two.

The conclusion is the actual global ramification-based scheme PCF
predicate. Comparison with the paper's normalized weighted divisor PCF
predicate remains a separate step.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.BasilicaProjectiveScheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
variable (k : Type*) [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual stalk ramification index is one away from `0` and `∞`. -/
theorem ramificationIndexAt_eq_one_of_noncritical (h2 : (2 : k) ≠ 0)
    (p : Proj (grading k)) (hp : p ≠ zero k ∧ p ≠ infinity k) :
    Pcf.Palomar.ramificationIndexAt (schemeMap k) p = 1 := by
  letI : IsFinite (schemeMap k) := global_schemeMap_finite k
  have hfe : ((schemeMap k).stalkMap p).hom.FormallyEtale := by
    apply (Pcf.paperPFormsProjective_stalk_formallyEtale_iff (forms k) 2 (by decide)
      (forms_homogeneous k) (forms_cover k) h2 p).mpr
    rw [jacobian_mem_iff k h2 p]
    exact not_or.mpr hp
  letI := ((schemeMap k).stalkMap p).hom.toAlgebra
  haveI : Algebra.FormallyEtale
      ((Proj (grading k)).presheaf.stalk (schemeMap k p))
      ((Proj (grading k)).presheaf.stalk p) :=
    RingHom.formallyEtale_algebraMap.mp hfe
  haveI : Algebra.EssFiniteType
      ((Proj (grading k)).presheaf.stalk (schemeMap k p))
      ((Proj (grading k)).presheaf.stalk p) :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap (schemeMap k) p)
  exact Ideal.ramificationIdx_eq_one _ _

/-- The ramification-based orbit is contained in the actual non-étale orbit. -/
theorem postcriticalSet_subset_globalNonEtalePostorbit (h2 : (2 : k) ≠ 0) :
    Pcf.Palomar.postcriticalSet (schemeMap k) ⊆ globalNonEtalePostorbit k := by
  rintro y ⟨p, _, hr, n, he⟩
  by_cases hp : p = zero k ∨ p = infinity k
  · refine ⟨p, ?_, n + 1, Nat.zero_lt_succ _, he.symm⟩
    rw [global_nonEtaleLocus_eq_pair k h2]
    exact hp
  · have h1 := ramificationIndexAt_eq_one_of_noncritical k h2 p (not_or.mp hp)
    omega

/-- The actual projective basilica scheme map is ramification-based PCF.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem isPCF (h2 : (2 : k) ≠ 0) : Pcf.Palomar.IsPCF (schemeMap k) :=
  (globalNonEtalePostorbit_finite k h2).subset
    (postcriticalSet_subset_globalNonEtalePostorbit k h2)

end Pcf.Examples.PaperP.BasilicaProjectiveScheme
