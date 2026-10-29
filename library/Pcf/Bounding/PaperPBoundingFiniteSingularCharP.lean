/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FiniteSingularCorrection
public import Pcf.Bounding.NonNormalCodimOne
public import Pcf.Bounding.PaperPBoundingStepZero

/-!
# Finite singular divisor correction in arbitrary characteristic

The regular-locus openness theorem is needed to prove that the manuscript's
exact exceptional set is closed. For the finite set of divisor generic points,
normalization gives a more elementary route: an integral codimension-one
local ring is regular whenever it is normal, and nonnormal divisor points
are finite for a finite-type integral scheme.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The singular codimension-one points of an integral finite-type scheme
over any field are finite, without perfection of the field or openness of the
full regular locus. -/
theorem finite_schemeDivisorPoint_stalkSingularLocus_of_finiteType
    (k : Type u) [Field k]
    {D : Scheme.{u}} [IsIntegral D] [NoetherianSpace D]
    (s : D ⟶ Spec (.of k)) [LocallyOfFiniteType s] :
    {Q : SchemeDivisorPoint D | Q.1 ∈ stalkSingularLocus D}.Finite := by
  have hnon := finite_nonNormal_schemeDivisorPoint k s
  refine hnon.subset ?_
  intro Q hsing hnormal
  letI : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian s
  letI : IsIntegrallyClosed (D.presheaf.stalk Q.1) := hnormal
  have hdim : ringKrullDim (D.presheaf.stalk Q.1) = 1 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight Q.1, Q.2]
    norm_num
  letI : IsDiscreteValuationRing (D.presheaf.stalk Q.1) :=
    Pcf.Stacks.isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
      _ hdim
  exact hsing inferInstance

/-- The original image divisor is locally Cartier near its generic point.
On that neighborhood, every normal codimension-one divisor stalk forces the
ambient codimension-two stalk to be regular. This uses the regular quotient
criterion and works over an arbitrary field. -/
theorem exists_open_invariantDivisor_regularityCorrection_of_finiteType
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X) :
    ∃ V : (pointClosureIdealSheaf A.1).subscheme.Opens,
      genericPoint (pointClosureIdealSheaf A.1).subscheme ∈ V ∧
      ∀ Q : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme,
        Q.1 ∈ V →
        IsIntegrallyClosed
          ((pointClosureIdealSheaf A.1).subscheme.presheaf.stalk Q.1) →
          (pointClosureIdealSheaf A.1).subschemeι Q.1 ∉ stalkSingularLocus X ∧
            Q.1 ∉ stalkSingularLocus (pointClosureIdealSheaf A.1).subscheme := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hAU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ A.1) isOpen_univ
  let W : X.affineOpens := ⟨U, hU⟩
  let I := pointClosureIdealSheaf A.1
  let R := Γ(X, W)
  let p : Ideal R := I.ideal W
  letI : Nonempty (W : X.Opens) := ⟨⟨A.1, hAU⟩⟩
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian W
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed W
  letI : p.IsPrime := pointClosureIdealSheaf_ideal_isPrime A.1 W hAU
  have hp : p.height = 1 := pointClosureIdealSheaf_ideal_height A W hAU
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne p hp
  letI : (p.map (algebraMap R (Localization.AtPrime p))).IsPrincipal :=
    IsPrincipalIdealRing.principal _
  obtain ⟨a, ha, f, hfp, hf⟩ :=
    exists_principalOpen_map_eq_span_of_isPrincipal_atPrime p
      (Ideal.fg_of_isNoetherianRing p) p
  have hAf : A.1 ∈ X.basicOpen f := by
    apply (Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf W.2 f
      ⟨A.1, hAU⟩).mpr
    simpa only [p, I, pointClosureIdealSheaf_ideal A.1 W hAU] using hfp
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ X.basicOpen f
  have hηV : genericPoint I.subscheme ∈ V := by
    change I.subschemeι (genericPoint I.subscheme) ∈ X.basicOpen f
    simpa only [I, pointClosureSubscheme_genericPoint] using hAf
  refine ⟨V, hηV, ?_⟩
  intro Q hQV hnormal
  have hQf : I.subschemeι Q.1 ∈ X.basicOpen f := hQV
  have hQU : I.subschemeι Q.1 ∈ (W : X.Opens) := X.basicOpen_le f hQf
  let sA := I.subschemeι ≫ s
  haveI : LocallyOfFiniteType sA := inferInstance
  letI : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian sA
  letI : IsIntegrallyClosed (I.subscheme.presheaf.stalk Q.1) := hnormal
  have hdimA : ringKrullDim (I.subscheme.presheaf.stalk Q.1) = 1 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight Q.1, Q.2]
    norm_num
  letI : IsDiscreteValuationRing (I.subscheme.presheaf.stalk Q.1) :=
    Pcf.Stacks.isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
      _ hdimA
  have hdiv : IsRegularLocalRing (I.subscheme.presheaf.stalk Q.1) := inferInstance
  refine ⟨?_, fun h ↦ h hdiv⟩
  let q : Ideal R := ambientPrimeOfQuotientPoint I W Q.1 hQU
  letI : q.IsPrime := ambientPrimeOfQuotientPoint_isPrime I W Q.1 hQU
  have hfq : f ∉ q := by
    rw [show q = (W.2.primeIdealOf ⟨I.subschemeι Q.1, hQU⟩).asIdeal from
      ambientPrimeOfQuotientPoint_eq_primeIdealOf I W Q.1 hQU]
    exact (Stacks.SchemeLevel.mem_basicOpen_iff_notMem_primeIdealOf W.2 f _).mp hQf
  let P : Ideal (Localization.AtPrime q) := p.map (algebraMap R _)
  have hP : P = Ideal.span {algebraMap R (Localization.AtPrime q) a} := hf q hfq
  letI : P.IsPrincipal := ⟨algebraMap R (Localization.AtPrime q) a, hP⟩
  letI : IsRegularLocalRing (Localization.AtPrime q ⧸ P) :=
    isRegularLocalRing_divisorQuotientLocalization I W Q.1 hQU hdiv
  have hdimQ : ringKrullDim (Localization.AtPrime q ⧸ P) = 1 := by
    simpa only [Q.2, WithBot.coe_one] using
      ringKrullDim_divisorQuotientLocalization I W Q.1 hQU
  have hdimR : 2 ≤ ringKrullDim (Localization.AtPrime q) := by
    rw [show ringKrullDim (Localization.AtPrime q) =
      ↑(Order.coheight (I.subschemeι Q.1)) from
        ringKrullDim_ambientPrimeLocalization I W Q.1 hQU]
    exact WithBot.coe_le_coe.mpr (A.two_le_coheight_closureDivisor Q)
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    isRegularLocalRing_of_principal_quotient_of_dim_one P hdimQ hdimR
  have hreg : IsRegularLocalRing (X.presheaf.stalk (I.subschemeι Q.1)) :=
    IsRegularLocalRing.of_ringEquiv
      (ambientPrimeLocalizationRingEquivStalk I W Q.1 hQU)
  exact fun h ↦ h hreg

/-- The two actual singular corrections on an original divisor have only
finitely many divisor generic points over an arbitrary field. This replaces
the perfect-field generic-smoothness argument for the finite part of Step 0. -/
theorem invariantDivisorSing_finite_of_finiteType
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (A : SchemeDivisorPoint X) : (invariantDivisorSing A).Finite := by
  obtain ⟨V, hV, hregular⟩ :=
    exists_open_invariantDivisor_regularityCorrection_of_finiteType k s A
  let D := (pointClosureIdealSheaf A.1).subscheme
  let sD := (pointClosureIdealSheaf A.1).subschemeι ≫ s
  haveI : LocallyOfFiniteType sD := inferInstance
  have hN : {Q : SchemeDivisorPoint D |
      ¬ IsIntegrallyClosed (D.presheaf.stalk Q.1)}.Finite :=
    finite_nonNormal_schemeDivisorPoint k sD
  have hVfin : {Q : SchemeDivisorPoint D | Q.1 ∈ (V : Set _)ᶜ}.Finite := by
    apply finite_schemeDivisorPoint_mem_of_isClosed V.isOpen.isClosed_compl
    intro heq
    exact (heq.symm ▸ Set.mem_univ _) hV
  refine (hVfin.union hN).subset ?_
  intro Q hQ
  by_cases hQV : Q.1 ∈ V
  · by_cases hnormal : IsIntegrallyClosed (D.presheaf.stalk Q.1)
    · have hreg := hregular Q hQV hnormal
      exact False.elim (hQ.elim hreg.1 hreg.2)
    · exact Or.inr hnormal
  · exact Or.inl hQV

/-- The exact `Σ` from `thm:bounding` contains only finitely many generic
points of integral effective divisors on the original reduced image divisor,
in positive characteristic. This is a finite-divisor statement; closedness
of the entire pointwise set remains the regular-locus openness obligation. -/
theorem paperPBoundingSigma_badDivisors_finite_charP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hmono : IsPrimeToPMonodromyMap p f)
    (A : SchemeDivisorPoint X) :
    letI : IsFinite (Palomar.normalizationMap X) :=
      schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
    letI : IsFinite (Palomar.normalizationMap Y) :=
      schemeGlobalNormalizationMap_isFinite Y k s
    {Q : SchemeDivisorPoint
      (pointClosureIdealSheaf (A.mapFiniteDominantNormal f).1).subscheme |
        Q.1 ∈ paperPBoundingSigma f (A.mapFiniteDominantNormal f)}.Finite := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  letI : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k s
  let B := A.mapFiniteDominantNormal f
  let I := pointClosureIdealSheaf B.1
  let SigmaOther : Set I.subscheme := I.subschemeι ⁻¹'
    paperPBoundingOtherBranch f B
  have hotherData := paperPBoundingOtherBranch_intersection_finite p hp k s f hmono A
  have hother : {Q : SchemeDivisorPoint I.subscheme | Q.1 ∈ SigmaOther}.Finite := by
    refine hotherData.2.2.subset ?_
    intro Q hQ
    exact closure_minimal (Set.singleton_subset_iff.mpr hQ) hotherData.1
  have hsing : (invariantDivisorSing B).Finite :=
    invariantDivisorSing_finite_of_finiteType k s B
  refine (hother.union hsing).subset ?_
  intro Q hQ
  change Q.1 ∈ (SigmaOther ∪
    I.subschemeι ⁻¹' stalkSingularLocus Y) ∪
      stalkSingularLocus I.subscheme at hQ
  rcases hQ with (hO | hY) | hB
  · exact Or.inl hO
  · exact Or.inr (Or.inl hY)
  · exact Or.inr (Or.inr hB)

#print axioms finite_schemeDivisorPoint_stalkSingularLocus_of_finiteType
#print axioms exists_open_invariantDivisor_regularityCorrection_of_finiteType
#print axioms invariantDivisorSing_finite_of_finiteType
#print axioms paperPBoundingSigma_badDivisors_finite_charP

end
end Pcf
