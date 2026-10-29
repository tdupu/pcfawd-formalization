/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingNormalization
public import Pcf.PaperCharZero.SupportingDictionary
public import Pcf.PaperCharZero.SupportingIterates
public import Pcf.Bounding.NormalSchemePCFComparison

/-!
# Normalized critical and branch divisors on a normal variety

For a finite dominant endomorphism of a normal integral scheme of finite type
over a characteristic-zero field, the paper's normalized critical divisors
(`def:crit-branch` of `paper.tex`, computed on the actual canonical
normalization) are exactly the integral effective divisors at whose generic
point the actual stalk map is not formally étale. The normalized branch
divisors are their actual images. This combines `lem:dictionary` on the
normalization with the canonical normalization isomorphism of a normal scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

section Normal

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (s : A ⟶ Spec (.of k)) (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A] [IsNormalScheme A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

omit [LocallyOfFinitePresentation g] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))] in
include k s in
/-- On a normal scheme, a codimension-one point of the canonical normalization
is ramified for the actual lift exactly when the original stalk map at its image
is not formally étale. -/
theorem normalScheme_one_lt_ramificationIdx_lift_iff
    (Q : SchemeDivisorPoint (Palomar.normalization A)) :
    letI : IsFinite (Palomar.normalizationMap A) :=
      schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
    1 < schemeDivisorRamificationIdx (schemeGlobalNormalizationLift g) Q ↔
      ¬ (g.stalkMap (Palomar.normalizationMap A Q.1)).hom.FormallyEtale := by
  let : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
  have hpos := schemeDivisorRamificationIdx_pos (schemeGlobalNormalizationLift g) Q
  have hdict := ramificationIdx_eq_one_iff_formallyEtale_charZero k
    (Palomar.normalizationMap A ≫ s) (schemeGlobalNormalizationLift g) Q
  rw [← normalScheme_formallyEtale_normalizationLift_iff g Q.1, ← hdict]
  omega

include s in
/-- The normalized critical divisors of an endomorphism of a normal scheme are
exactly the divisors at which the actual stalk map is not formally étale. -/
theorem normalScheme_mem_criticalDivisors_iff (P : SchemeDivisorPoint A) :
    P ∈ schemeNormalizedCriticalDivisors k g ↔ ¬ (g.stalkMap P.1).hom.FormallyEtale := by
  let : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
  let e := normalScheme_normalizationDivisorEquiv A
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (normalScheme_one_lt_ramificationIdx_lift_iff k s g Q).mp hQ
  · intro hP
    refine ⟨e.symm P, ?_, ?_⟩
    · have hval : Palomar.normalizationMap A (e.symm P).1 = P.1 :=
        congrArg Subtype.val (e.apply_symm_apply P)
      change 1 < schemeDivisorRamificationIdx (schemeGlobalNormalizationLift g) (e.symm P)
      rw [normalScheme_one_lt_ramificationIdx_lift_iff k s g, hval]
      exact hP
    · apply Subtype.ext
      exact congrArg Subtype.val (e.apply_symm_apply P)

include s in
/-- The normalized branch divisors of an endomorphism of a normal scheme are the
actual images of the divisors at which the stalk map is not formally étale. -/
theorem normalScheme_mem_branch_iff (E : SchemeDivisorPoint A) :
    E ∈ schemeNormalizedBranch k g ↔
      ∃ P : SchemeDivisorPoint A, g P.1 = E.1 ∧ ¬ (g.stalkMap P.1).hom.FormallyEtale := by
  change E ∈ (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k)) ''
      schemeNormalizedCriticalDivisors k g ↔ _
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, rfl, (normalScheme_mem_criticalDivisors_iff k s g P).mp hP⟩
  · rintro ⟨P, hPE, hP⟩
    exact ⟨P, (normalScheme_mem_criticalDivisors_iff k s g P).mpr hP, Subtype.ext hPE⟩

end Normal

#print axioms normalScheme_one_lt_ramificationIdx_lift_iff
#print axioms normalScheme_mem_criticalDivisors_iff
#print axioms normalScheme_mem_branch_iff

end Pcf.PaperCharZero
