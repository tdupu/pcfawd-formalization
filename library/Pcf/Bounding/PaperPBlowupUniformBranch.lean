/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundBlowupRamificationSquare
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.PaperPPrimeToPTameFiniteMap
public import Pcf.Bounding.PaperPBlowupNormalizedSquare

/-!
# Uniform weighted branch bound in a proper component square

This is the final valuation-to-branch step of `paper-p.tex`, Proposition
`prop:bound-blowup`, for an actual commuting square of normal integral schemes.
The fixed proper component map `q` chooses the bad divisors; the finite upper
cover and proper vertical lift may vary. Applying it to the normalized Rees
component square remains a separate geometric specialization.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The bad set depends only on the fixed proper component map `q`.
Outside it, étaleness of every upper divisor over `D` excludes `D` from
the weighted branch locus of every compatible prime-to-`p` finite normal
cover. The proper vertical map supplies the required divisor over each
ramified divisor of the lower cover. -/
theorem exists_finite_bad_for_weighted_branch_of_component_map
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme Z]
    [CompactSpace Z] [NoetherianSpace Z]
    (s : Z ⟶ Spec (.of k)) (q : Y ⟶ Z)
    [IsDominant q] [LocallyOfFiniteType q] [QuasiCompact q] :
    letI : IsFinite (Palomar.normalizationMap Z) := by
      letI : IsIso (Palomar.normalizationMap Z) :=
        normalScheme_normalizationMap_isIso Z
      infer_instance
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ {X W : Scheme.{u}}
        [IsIntegral X] [IsIntegral W]
        [IsLocallyNoetherian X] [IsLocallyNoetherian W]
        [IsNormalScheme W]
        (u : X ⟶ Y) (v : X ⟶ W) (g : W ⟶ Z)
        [IsFinite u] [IsDominant u]
        [IsProper v] [IsDominant v]
        [IsFinite g] [IsDominant g]
        (_hcomm : u ≫ q = v ≫ g)
        (_hmono : IsPrimeToPMonodromyMap p g)
        (D : SchemeDivisorPoint Z),
        letI : IsFinite (Palomar.normalizationMap W) := by
          letI : IsIso (Palomar.normalizationMap W) :=
            normalScheme_normalizationMap_isIso W
          infer_instance
        D.1 ∉ Bad →
        (∀ x : SchemeDivisorPoint X,
          q (u x.1) = D.1 → (u.stalkMap x.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet g := by
  obtain ⟨Bad, hBad, hindex⟩ :=
    exists_finite_bad_for_component_map p k s q
  refine ⟨Bad, hBad, ?_⟩
  intro X W _ _ _ _ _ u v g _ _ _ _ _ _ hcomm hmono D hDnot hetale hbranch
  letI : IsIso (Palomar.normalizationMap W) :=
    normalScheme_normalizationMap_isIso W
  letI : IsIso (Palomar.normalizationMap Z) :=
    normalScheme_normalizationMap_isIso Z
  letI : IsFinite (Palomar.normalizationMap W) := inferInstance
  letI : IsFinite (Palomar.normalizationMap Z) := inferInstance
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal g] at hbranch
  obtain ⟨Q, hQ, hQD⟩ := hbranch
  change 1 < schemeDivisorDelta g Q at hQ
  change g Q.1 = D.1 at hQD
  have hvsurj : Function.Surjective v :=
    (surjective_of_isDominant_of_isClosed_range v
      v.isClosedMap.isClosed_range).surj
  obtain ⟨x₀, hx₀⟩ := hvsurj Q.1
  obtain ⟨x, hvx, _⟩ := exists_schemeDivisorPoint_over v Q x₀ hx₀
  have hy : Order.coheight (u x.1) = 1 :=
    (x.mapFiniteDominantNormal u).2
  have hw : Order.coheight (v x.1) = 1 := hvx ▸ Q.2
  have hpoint := congrArg (fun m : X ⟶ Z => m x.1) hcomm
  change q (u x.1) = g (v x.1) at hpoint
  have hqD : q (u x.1) = D.1 := by
    calc
      q (u x.1) = g (v x.1) := hpoint
      _ = g Q.1 := by rw [hvx]
      _ = D.1 := hQD
  have hz : Order.coheight (q (u x.1)) = 1 := hqD ▸ D.2
  have htame : (schemeDivisorRamificationIdx g Q).Coprime p :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (finiteMap_schemeDivisor_tame_of_primeToP
        p (Fact.out) k s g hmono Q).1).symm
  have hQeq : (⟨v x.1, hw⟩ : SchemeDivisorPoint W) = Q := Subtype.ext hvx
  have hindex1 := hindex u v g hcomm x hy hw hz
    (by simpa only [hqD] using hDnot) (hetale x hqD) (by simpa only [hQeq] using htame)
  rw [hQeq] at hindex1
  have hdelta := finiteMap_schemeDivisorDelta_eq_ramificationIdx_of_primeToP
    p (Fact.out) k s g hmono Q
  rw [hdelta, hindex1] at hQ
  omega

/-- For a finite map over a characteristic-zero field, the residue-field
inseparable degree at every integral effective divisor is one. Thus the
manuscript's weighted local degree is its ramification index. -/
theorem schemeDivisorDelta_eq_ramificationIdx_of_charZero
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [IsFinite f] (Q : SchemeDivisorPoint X) :
    schemeDivisorDelta f Q = schemeDivisorRamificationIdx f Q := by
  letI := (f.residueFieldMap Q.1).hom.toAlgebra
  letI : FiniteDimensional (Y.residueField (f Q.1)) (X.residueField Q.1) :=
    finiteResidueField_of_isFinite f Q.1
  let := schemeStalkAlgebraOfField k s (f Q.1)
  haveI : CharZero (Y.residueField (f Q.1)) := charZero_of_injective_ringHom
    ((Y.residue (f Q.1)).hom.comp (algebraMap k (Y.presheaf.stalk (f Q.1)))).injective
  haveI : Algebra.IsSeparable (Y.residueField (f Q.1)) (X.residueField Q.1) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  unfold schemeDivisorDelta
  rw [Algebra.IsSeparable.finInsepDegree_eq, mul_one]

/-- The characteristic-zero version of the uniform weighted branch bound.
The fixed component map selects the bad set; a varying finite normal cover
has no weighted branch divisor outside it if its upper component map is
étale above that divisor. -/
theorem exists_finite_bad_for_weighted_branch_of_component_map_charZero
    (k : Type u) [Field k] [CharZero k]
    {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsNormalScheme Y] [IsNormalScheme Z]
    [CompactSpace Z] [NoetherianSpace Z]
    (s : Z ⟶ Spec (.of k)) (q : Y ⟶ Z)
    [IsDominant q] [LocallyOfFiniteType q] [QuasiCompact q] :
    letI : IsFinite (Palomar.normalizationMap Z) := by
      letI : IsIso (Palomar.normalizationMap Z) :=
        normalScheme_normalizationMap_isIso Z
      infer_instance
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ {X W : Scheme.{u}}
        [IsIntegral X] [IsIntegral W]
        [IsLocallyNoetherian X] [IsLocallyNoetherian W]
        [IsNormalScheme W]
        (u : X ⟶ Y) (v : X ⟶ W) (g : W ⟶ Z)
        [IsFinite u] [IsDominant u]
        [IsProper v] [IsDominant v]
        [IsFinite g] [IsDominant g]
        (_hcomm : u ≫ q = v ≫ g)
        (D : SchemeDivisorPoint Z),
        letI : IsFinite (Palomar.normalizationMap W) := by
          letI : IsIso (Palomar.normalizationMap W) :=
            normalScheme_normalizationMap_isIso W
          infer_instance
        D.1 ∉ Bad →
        (∀ x : SchemeDivisorPoint X,
          q (u x.1) = D.1 → (u.stalkMap x.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet g := by
  obtain ⟨Bad, hBad, hindex⟩ :=
    exists_finite_bad_for_component_map_charZero k s q
  refine ⟨Bad, hBad, ?_⟩
  intro X W _ _ _ _ _ u v g _ _ _ _ _ _ hcomm D hDnot hetale hbranch
  letI : IsIso (Palomar.normalizationMap W) :=
    normalScheme_normalizationMap_isIso W
  letI : IsIso (Palomar.normalizationMap Z) :=
    normalScheme_normalizationMap_isIso Z
  letI : IsFinite (Palomar.normalizationMap W) := inferInstance
  letI : IsFinite (Palomar.normalizationMap Z) := inferInstance
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal g] at hbranch
  obtain ⟨Q, hQ, hQD⟩ := hbranch
  change 1 < schemeDivisorDelta g Q at hQ
  change g Q.1 = D.1 at hQD
  have hvsurj : Function.Surjective v :=
    (surjective_of_isDominant_of_isClosed_range v
      v.isClosedMap.isClosed_range).surj
  obtain ⟨x₀, hx₀⟩ := hvsurj Q.1
  obtain ⟨x, hvx, _⟩ := exists_schemeDivisorPoint_over v Q x₀ hx₀
  have hy : Order.coheight (u x.1) = 1 :=
    (x.mapFiniteDominantNormal u).2
  have hw : Order.coheight (v x.1) = 1 := hvx ▸ Q.2
  have hpoint := congrArg (fun m : X ⟶ Z => m x.1) hcomm
  change q (u x.1) = g (v x.1) at hpoint
  have hqD : q (u x.1) = D.1 := by
    calc
      q (u x.1) = g (v x.1) := hpoint
      _ = g Q.1 := by rw [hvx]
      _ = D.1 := hQD
  have hz : Order.coheight (q (u x.1)) = 1 := hqD ▸ D.2
  have hQeq : (⟨v x.1, hw⟩ : SchemeDivisorPoint W) = Q := Subtype.ext hvx
  have hindex1 := hindex u v g hcomm x hy hw hz
    (by simpa only [hqD] using hDnot) (hetale x hqD)
  rw [hQeq] at hindex1
  have hdelta := schemeDivisorDelta_eq_ramificationIdx_of_charZero k s g Q
  rw [hdelta, hindex1] at hQ
  omega

#print axioms exists_finite_bad_for_weighted_branch_of_component_map
#print axioms schemeDivisorDelta_eq_ramificationIdx_of_charZero
#print axioms exists_finite_bad_for_weighted_branch_of_component_map_charZero

end
end Pcf.Bounding
