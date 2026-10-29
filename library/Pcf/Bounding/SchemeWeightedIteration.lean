/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeDeltaEtaleNoetherian
public import Pcf.Bounding.GlobalNormalizationIteration

/-!
# Iteration of the weighted divisor degree

The finite-map tower law is iterated at actual divisor points.  Combining it
with the local δ/non-étale comparison will identify normalized non-étale PCF
for positive iterates in every characteristic.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- Pushforward of a divisor by a scheme power is iteration of the actual
divisor step. -/
theorem schemeDivisorMap_pow_eq_iterate
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (m : ℕ) (d : SchemeDivisorPoint X) :
    d.mapFiniteDominantNormal (End.of f ^ m).asHom =
      ((schemeDeltaDynamicsOfFiniteDominantNormal f).step^[m]) d := by
  apply Subtype.ext
  induction m with
  | zero => rfl
  | succ m ih =>
      change (End.of f ^ m).asHom.base d.1 =
        (((schemeDeltaDynamicsOfFiniteDominantNormal f).step^[m]) d).1 at ih
      change (End.of f ^ (m + 1)).asHom.base d.1 =
        (((schemeDeltaDynamicsOfFiniteDominantNormal f).step^[m + 1]) d).1
      rw [pow_succ', End.mul_asHom]
      simpa only [Scheme.Hom.comp_apply, Function.iterate_succ_apply',
        schemeDeltaDynamics_step_val] using congrArg f ih

/-- The weighted local degree of the identity is one. -/
@[simp] theorem schemeDivisorDelta_id
    {X : Scheme.{u}} (d : SchemeDivisorPoint X) :
    schemeDivisorDelta (𝟙 X) d = 1 := by
  apply schemeDivisorDelta_eq_one_of_formallyEtale
  rw [Scheme.Hom.stalkMap_id]
  change (RingHom.id _).FormallyEtale
  rw [RingHom.FormallyEtale]
  infer_instance

/-- Weighted divisor degrees multiply along every actual positive iterate. -/
theorem schemeDivisorDelta_pow
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (m : ℕ) (d : SchemeDivisorPoint X) :
    schemeDivisorDelta (End.of f ^ m).asHom d =
      ∏ i ∈ Finset.range m,
        schemeDivisorDelta f
          (((schemeDeltaDynamicsOfFiniteDominantNormal f).step^[i]) d) := by
  induction m with
  | zero => simp [schemeDivisorDelta_id]
  | succ m ih =>
      rw [pow_succ', End.mul_asHom]
      rw [schemeDivisorDelta_comp_of_isFinite (End.of f ^ m).asHom f d]
      rw [schemeDivisorMap_pow_eq_iterate f m d, ih, Finset.prod_range_succ]
      exact mul_comm _ _

/-- The paper's weighted degree supplies an actual positive divisor
dynamical system for a generically separable finite normal self-map. -/
noncomputable def schemeWeightedDivisorDynamics
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    DivisorDynamics (SchemeDivisorPoint X) := by
  have hfinite : (schemeDivisorNonEtaleLocus f).Finite :=
    schemeDivisorNonEtaleLocus_finite_of_exists_formallyEtale f
      ⟨genericPoint X,
        formallyEtale_stalkMap_genericPoint_of_finite_dominant_separable f hsep⟩
  let D := schemeDeltaDynamicsOfFiniteDominantNormal f
  have hcrit : D.critical.Finite := by
    change {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d}.Finite
    rw [schemeDivisorWeightedCritical_eq_nonEtale f]
    exact hfinite
  exact D.toDivisorDynamics
    (schemeDivisorDelta_pos_of_isFinite f)
    (SchemeDivisorPoint.mapFiniteDominantNormal_surjective f)
    (hcrit.image D.step)

@[simp] theorem schemeWeightedDivisorDynamics_step
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    (schemeWeightedDivisorDynamics f hsep).step =
      (schemeDeltaDynamicsOfFiniteDominantNormal f).step := rfl

@[simp] theorem schemeWeightedDivisorDynamics_ramificationIdx
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    (schemeWeightedDivisorDynamics f hsep).ramificationIdx =
      schemeDivisorDelta f := rfl

/-- The weighted system of a scheme power is the abstract weighted
divisor iterate, using the actual residue-field inseparable degrees. -/
theorem schemeWeightedDivisorDynamics_pow_eq_iterate
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) (m : ℕ) :
    schemeWeightedDivisorDynamics (End.of f ^ m).asHom
      (isGenericallySeparable_pow f hsep m) =
      (schemeWeightedDivisorDynamics f hsep).iterate m := by
  apply DivisorDynamics.ext_of_step_ramificationIdx
  · funext d
    exact (schemeDivisorMap_pow_eq_iterate f m d).trans rfl
  · funext d
    exact schemeDivisorDelta_pow f m d

/-- The normal map's actual non-étale postcritical set is exactly the
postcritical set of the paper's weighted degree dynamics. -/
theorem schemeNormalNonEtalePostcriticalSet_eq_weighted
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    (unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep).nonEtalePostcriticalSet =
      (schemeWeightedDivisorDynamics f hsep).postcriticalSet := by
  let D := unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep
  let E := schemeWeightedDivisorDynamics f hsep
  have hstep : D.step = E.step := rfl
  have hcrit : D.nonEtaleLocus 1 =
      {d : SchemeDivisorPoint X | 1 < E.ramificationIdx d} := by
    change schemeDivisorNonEtaleLocus (End.of f ^ 1).asHom =
      {d : SchemeDivisorPoint X | 1 < schemeDivisorDelta f d}
    simpa only [pow_one] using (schemeDivisorWeightedCritical_eq_nonEtale f).symm
  have hbranch : D.nonEtaleBranch 1 = E.branch := by
    simp only [UnnormalizedDynamics.nonEtaleBranch,
      DivisorDynamics.branch, hstep, hcrit,
      Function.iterate_one]
    ext q
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    aesop
  change (⋃ n : ℕ, D.step^[n] '' D.nonEtaleBranch 1) =
    ⋃ n : ℕ, E.step^[n] '' E.branch
  rw [hstep, hbranch]

/-- Normal non-étale PCF is the paper's weighted PCF. -/
theorem isNormalNonEtalePCF_iff_weighted
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    IsNormalNonEtalePCF f hsep ↔
      (schemeWeightedDivisorDynamics f hsep).IsPCF := by
  change
    (unnormalizedDynamicsOfFiniteDominantNormalSeparable f hsep).nonEtalePostcriticalSet.Finite ↔
      (schemeWeightedDivisorDynamics f hsep).postcriticalSet.Finite
  rw [schemeNormalNonEtalePostcriticalSet_eq_weighted f hsep]

/-- Normal non-étale PCF is invariant under every positive iterate in
arbitrary characteristic. This is the normal case of the paper's
iteration lemma with its weighted degree convention. -/
theorem isNormalNonEtalePCF_pow_iff
    {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) (m : ℕ) (hm : 1 ≤ m) :
    IsNormalNonEtalePCF (End.of f ^ m).asHom
      (isGenericallySeparable_pow f hsep m) ↔
      IsNormalNonEtalePCF f hsep := by
  rw [isNormalNonEtalePCF_iff_weighted,
    isNormalNonEtalePCF_iff_weighted f hsep,
    schemeWeightedDivisorDynamics_pow_eq_iterate f hsep m]
  change ((schemeWeightedDivisorDynamics f hsep).iterate m).postcriticalSet.Finite ↔
    (schemeWeightedDivisorDynamics f hsep).postcriticalSet.Finite
  rw [DivisorDynamics.postcriticalSet_iterate _ hm]

#print axioms schemeDivisorMap_pow_eq_iterate
#print axioms schemeDivisorDelta_id
#print axioms schemeDivisorDelta_pow
#print axioms schemeWeightedDivisorDynamics
#print axioms schemeWeightedDivisorDynamics_pow_eq_iterate
#print axioms schemeNormalNonEtalePostcriticalSet_eq_weighted
#print axioms isNormalNonEtalePCF_iff_weighted
#print axioms isNormalNonEtalePCF_pow_iff

end Pcf
