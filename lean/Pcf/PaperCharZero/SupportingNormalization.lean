/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingDynamics
public import Pcf.Bounding.NormalizationPcfEquiv

/-!
# The preliminary PCF equivalence on the canonical normalization

`paper.tex`, Proposition `prop:pcf-equiv`, including its critical-locus clause.
Critical and branch loci here are their sets of integral effective divisors.
The actual canonical normalization and the actual downstairs divisor map are
used, also when the variety is nonnormal. No preperiodicity or finiteness of the
postcritical set is supplied as a structural assumption.
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

namespace NormalizationUnnormalizedDynamics

variable {PN : Type u} {PU : Type v} (D : Pcf.NormalizationUnnormalizedDynamics PN PU)

/-- `prop:pcf-equiv`, (1) ⇔ (2), for the downstairs normalized branch locus. -/
theorem isPCF_iff_branch_preperiodic : D.IsPCF ↔
    ∀ Q ∈ D.branch, ∃ r s : ℕ, 0 < s ∧ D.step^[r + s] Q = D.step^[r] Q :=
  finite_forward_support_iff_preperiodic D.step D.branch D.branch_finite

/-- `prop:pcf-equiv`, (1) ⇔ (3), with the two divisor carriers kept distinct. -/
theorem isPCF_iff_critical_preperiodic : D.IsPCF ↔
    ∃ r s : ℕ, 0 < s ∧ D.step^[r + s] '' D.criticalLocus = D.step^[r] '' D.criticalLocus :=
  finite_forward_image_support_iff_repeat D.step D.criticalLocus D.branch_finite

end NormalizationUnnormalizedDynamics

section Schemes

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

/-- The critical integral effective divisors downstairs, computed using the actual
ramification indices on the canonical normalization (`def:crit-branch`). -/
noncomputable def schemeNormalizedCriticalDivisors : Set (SchemeDivisorPoint A) :=
  Pcf.NormalizationUnnormalizedDynamics.criticalLocus
    (schemeGlobalNormalizationUnnormalizedDynamics k g).toNormalizationUnnormalizedDynamics

/-- `prop:pcf-equiv`, (1) ⇔ (2), for actual finite dominant scheme maps in
characteristic zero. The source's divisors are represented by codimension-one points. -/
theorem scheme_isNormalizedPCF_iff_branch_preperiodic : IsNormalizedPCF k g ↔
    ∀ Q ∈ schemeNormalizedBranch k g, ∃ r s : ℕ, 0 < s ∧
      (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[r + s] Q =
      (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[r] Q :=
  NormalizationUnnormalizedDynamics.isPCF_iff_branch_preperiodic
    (schemeGlobalNormalizationUnnormalizedDynamics k g).toNormalizationUnnormalizedDynamics

/-- `prop:pcf-equiv`, (1) ⇔ (3), expressed as equality of the sets of critical
integral effective divisors after pushforward. In particular no normality of `A`
is required. The source's equality of closed unions is represented by equality of
their codimension-one components. -/
theorem scheme_isNormalizedPCF_iff_critical_preperiodic : IsNormalizedPCF k g ↔
    ∃ r s : ℕ, 0 < s ∧
      (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[r + s] ''
        schemeNormalizedCriticalDivisors k g =
      (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[r] ''
        schemeNormalizedCriticalDivisors k g :=
  NormalizationUnnormalizedDynamics.isPCF_iff_critical_preperiodic
    (schemeGlobalNormalizationUnnormalizedDynamics k g).toNormalizationUnnormalizedDynamics

end Schemes
end Pcf.PaperCharZero
