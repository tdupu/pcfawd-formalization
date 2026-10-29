/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NonEtaleSeparableDynamics
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian

/-!
# Weighted and non-étale PCF agree on normal schemes

For a finite dominant generically separable self-map of a normal integral
locally Noetherian scheme, the divisors with weighted local degree `δ > 1`
are exactly the actual non-étale divisor stalks. Hence the weighted PCF
predicate used in `latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`, is
the normal non-étale PCF predicate of Definition `def:pcf`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

/-- Weighted PCF is non-étale PCF on a normal scheme. -/
theorem isNormalNonEtalePCF_iff_deltaPCF
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] (hsep : IsGenericallySeparable f) :
    IsNormalNonEtalePCF f hsep ↔ (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep
  let E := schemeDeltaDynamicsOfFiniteDominantNormal f
  have hstep : D.step = E.step := by
    funext d
    apply Subtype.ext
    rfl
  have hcrit : D.nonEtaleLocus 1 = E.critical := by
    change schemeDivisorNonEtaleLocus (End.of f ^ 1).asHom =
      {d | 1 < schemeDivisorDelta f d}
    rw [schemeDivisorWeightedCritical_eq_nonEtale f, pow_one]
  have hset : D.nonEtalePostcriticalSet = E.postcriticalSet := by
    change (⋃ n : ℕ, D.step^[n] '' (D.step^[1] '' D.nonEtaleLocus 1)) =
      ⋃ n : ℕ, E.step^[n] '' (E.step '' E.critical)
    rw [hstep, hcrit, Function.iterate_one]
  change D.nonEtalePostcriticalSet.Finite ↔ E.postcriticalSet.Finite
  rw [hset]

#print axioms isNormalNonEtalePCF_iff_deltaPCF

end
end Pcf
