/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBranchZero
public import Pcf.Unnormalized.Recursive
public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Pcf.Bounding.NormalizationSchemeBridge
public import Pcf.Bounding.AllCodimBlowupIsoOffCentre

/-!
# Comparing the unnormalized and normalized branch loci

This module concerns `paper-p.tex`, Proposition `prop:loci-compare`.
The normalized-to-unnormalized comparison on nonnormal varieties is
the geometric part of the statement; the simpler inclusions and
finiteness statements are stated for actual finite scheme maps here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf
universe u
noncomputable section
set_option linter.style.haveILetI false

/-- Ramification of the map between two normalizations obstructs
unramifiedness of the original map at the source divisor's image.
This is the two-carrier form of the local comparison used in
`paper-p.tex`, Proposition `prop:loci-compare`(2). -/
theorem not_formallyUnramified_stalkMap_of_normalized_ramification
    {X Y NX NY : Scheme.{u}}
    (g : X ⟶ Y) (F : NX ⟶ NY) (νX : NX ⟶ X) (νY : NY ⟶ Y)
    [LocallyOfFiniteType g] [IsFinite F] [IsDominant F]
    [IsIntegral NX] [IsIntegral NY]
    [IsLocallyNoetherian NX] [IsLocallyNoetherian NY]
    [IsNormalScheme NX] [IsNormalScheme NY]
    (hsquare : F ≫ νY = νX ≫ g) (Q : SchemeDivisorPoint NX)
    (hbirational : IsStalkBirationalAt νX Q.1)
    (hQ : 1 < schemeDivisorRamificationIdx F Q) :
    ¬ (g.stalkMap (νX Q.1)).hom.FormallyUnramified := by
  let R₀ := Y.presheaf.stalk (g (νX Q.1))
  let B := X.presheaf.stalk (νX Q.1)
  let R := NY.presheaf.stalk (F Q.1)
  let S := NX.presheaf.stalk Q.1
  let K := NX.functionField
  have hpoint : g (νX Q.1) = νY (F Q.1) :=
    congrArg (fun f : NX ⟶ Y => f Q.1) hsquare.symm
  let v : R₀ →+* R :=
    ((Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫ νY.stalkMap (F Q.1)).hom
  letI : Algebra R₀ B := (g.stalkMap (νX Q.1)).hom.toAlgebra
  letI : Algebra B S := (νX.stalkMap Q.1).hom.toAlgebra
  letI : Algebra R S := (F.stalkMap Q.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (F.stalkMap Q.1).hom)
  letI : Algebra R₀ R := v.toAlgebra
  letI : Algebra R₀ S :=
    ((νX.stalkMap Q.1).hom.comp (g.stalkMap (νX Q.1)).hom).toAlgebra
  letI : IsScalarTower R₀ B S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' (by
    change ((g.stalkMap (νX Q.1)) ≫ νX.stalkMap Q.1).hom =
      ((F.stalkMap Q.1).hom.comp v)
    have h := Scheme.Hom.stalkMap_congr_hom (νX ≫ g) (F ≫ νY) hsquare.symm Q.1
    simp only [Scheme.Hom.stalkMap_comp] at h
    exact congrArg CommRingCat.Hom.hom h)
  letI : Algebra B K := ((algebraMap S K).comp (algebraMap B S)).toAlgebra
  letI : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing B K := hbirational
  letI : IsDiscreteValuationRing R :=
    (schemeDivisorMap F (coheight_apply_eq_one F) Q).stalk_isDiscreteValuationRing
  letI : Algebra.EssFiniteType R₀ B := LocallyOfFiniteType.stalkMap g (νX Q.1)
  intro hu
  letI : Algebra.FormallyUnramified R₀ B := hu
  have he := ramificationIdx_eq_one_of_local_birational_square R₀ B R S K
    (IsLocalRing.maximalIdeal S)
  exact (Nat.lt_irrefl 1) (he ▸ hQ)

/-- Proposition `prop:loci-compare`(2), the normalized weighted critical
points lie in the non-unramified critical locus on the original source.

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`), item (2) of Proposition A.4
(`item:compare-incl`). -/
theorem weightedCriticalPointSet_subset_schemeUnnormalizedCriticalZero
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) :
    weightedCriticalPointSet g ⊆
      {x : X | ∃ P : SchemeDivisorPoint X,
        P.1 = x ∧ P ∈ schemeUnnormalizedCriticalZero g} := by
  intro x hx
  obtain ⟨Q, hδ, rfl⟩ := hx
  let F := schemeGlobalNormalizationMorphism g
  let νX := Palomar.normalizationMap X
  let νY := Palomar.normalizationMap Y
  letI := (F.residueFieldMap Q.1).hom.toAlgebra
  letI : FiniteDimensional
      ((Palomar.normalization Y).residueField (F Q.1))
      ((Palomar.normalization X).residueField Q.1) :=
    finiteResidueField_of_isFinite F Q.1
  let := schemeStalkAlgebraOfField k (νY ≫ sY) (F Q.1)
  haveI : CharZero ((Palomar.normalization Y).residueField (F Q.1)) :=
    charZero_of_injective_ringHom
      (((Palomar.normalization Y).residue (F Q.1)).hom.comp
        (algebraMap k ((Palomar.normalization Y).presheaf.stalk (F Q.1)))).injective
  have hsep : Algebra.IsSeparable
      ((Palomar.normalization Y).residueField (F Q.1))
      ((Palomar.normalization X).residueField Q.1) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have he : 1 < schemeDivisorRamificationIdx F Q := by
    rcases (schemeDivisorDelta_one_lt_iff F Q).mp hδ with he | hnot
    · exact he
    · exact False.elim (hnot hsep)
  let P : SchemeDivisorPoint X :=
    ⟨νX Q.1, coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sX νX Q⟩
  refine ⟨P, rfl, ?_⟩
  change ¬ (g.stalkMap (νX Q.1)).hom.FormallyUnramified
  exact not_formallyUnramified_stalkMap_of_normalized_ramification
    g F νX νY (schemeGlobalNormalizationMorphism_comp g) Q
    (schemeGlobalNormalizationMap_stalkBirationalAt X Q.1) he

/-- Proposition `prop:loci-compare`(2), the normalized weighted branch
points lie in the nonreduced-fiber branch locus on the original target.

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`). -/
theorem weightedBranchPointSet_subset_schemeUnnormalizedBranchZero_points
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)] :
    weightedBranchPointSet g ⊆
      {y : Y | ∃ E : SchemeDivisorPoint Y,
        E.1 = y ∧ E ∈ schemeUnnormalizedBranchZero g} := by
  rw [weightedBranchPointSet_eq_image_criticalPointSet g]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨P, rfl, hP⟩ :=
    weightedCriticalPointSet_subset_schemeUnnormalizedCriticalZero g k sX sY hx
  let E : SchemeDivisorPoint Y :=
    ⟨g P.1, coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sY g P⟩
  refine ⟨E, rfl, ?_⟩
  exact (mem_schemeUnnormalizedBranchZero_iff_critical_divisor g k E).2
    ⟨P, rfl, hP⟩

/-- Proposition `prop:loci-compare`(3) at a chosen divisor above `P`:
if the two original stalks are normal, all three criticality tests agree.
The normalized test is the actual weighted degree of the canonical lift. -/
theorem normalizedCritical_iff_unnormalizedCritical_of_normal_stalks
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sY : Y ⟶ Spec (.of k))
    (Q : SchemeDivisorPoint (Palomar.normalization X))
    (hnormalX : IsIntegrallyClosed
      (X.presheaf.stalk (Palomar.normalizationMap X Q.1)))
    (hnormalY : IsIntegrallyClosed
      (Y.presheaf.stalk
        (Palomar.normalizationMap Y (schemeGlobalNormalizationMorphism g Q.1)))) :
    let P : SchemeDivisorPoint X :=
      ⟨Palomar.normalizationMap X Q.1,
        coheight_eq_of_stalkMap_bijective (Palomar.normalizationMap X) Q.1
          (stalkMap_bijective_of_isIntegralHom_of_integrallyClosed
            (Palomar.normalizationMap X) Q.1
            (schemeGlobalNormalizationMap_stalkBirationalAt X Q.1) hnormalX) ▸ Q.2⟩
    (1 < schemeDivisorDelta (schemeGlobalNormalizationMorphism g) Q ↔
      P ∈ schemeUnnormalizedCriticalZero g) ∧
    (P ∈ schemeUnnormalizedCriticalZero g ↔
      P ∈ schemeUnnormalizedCriticalOne g) := by
  let F := schemeGlobalNormalizationMorphism g
  let νX := Palomar.normalizationMap X
  let νY := Palomar.normalizationMap Y
  have hX : Function.Bijective (νX.stalkMap Q.1).hom :=
    stalkMap_bijective_of_isIntegralHom_of_integrallyClosed νX Q.1
      (schemeGlobalNormalizationMap_stalkBirationalAt X Q.1) hnormalX
  have hY : Function.Bijective (νY.stalkMap (F Q.1)).hom :=
    stalkMap_bijective_of_isIntegralHom_of_integrallyClosed νY (F Q.1)
      (schemeGlobalNormalizationMap_stalkBirationalAt Y (F Q.1)) hnormalY
  have hform : (F.stalkMap Q.1).hom.FormallyEtale ↔
      (g.stalkMap (νX Q.1)).hom.FormallyEtale :=
    formallyEtale_stalkMap_iff_of_square F νX νY g
      (schemeGlobalNormalizationMorphism_comp g) Q.1 hX hY
  let P : SchemeDivisorPoint X :=
    ⟨νX Q.1, coheight_eq_of_stalkMap_bijective νX Q.1 hX ▸ Q.2⟩
  change (1 < schemeDivisorDelta F Q ↔
      P ∈ schemeUnnormalizedCriticalZero g) ∧
    (P ∈ schemeUnnormalizedCriticalZero g ↔
      P ∈ schemeUnnormalizedCriticalOne g)
  have hδpos : 0 < schemeDivisorDelta F Q :=
    schemeDivisorDelta_pos_of_isFinite F Q
  have hδiff : 1 < schemeDivisorDelta F Q ↔
      ¬ (F.stalkMap Q.1).hom.FormallyEtale := by
    rw [← schemeDivisorDelta_eq_one_iff_formallyEtale F Q]
    omega
  have hδcrit1 : 1 < schemeDivisorDelta F Q ↔
      P ∈ schemeUnnormalizedCriticalOne g := by
    rw [hδiff, hform]
    rfl
  have hδcrit0 : 1 < schemeDivisorDelta F Q ↔
      P ∈ schemeUnnormalizedCriticalZero g := by
    constructor
    · intro hδ
      have he : 1 < schemeDivisorRamificationIdx F Q := by
        letI := (F.residueFieldMap Q.1).hom.toAlgebra
        letI : FiniteDimensional
            ((Palomar.normalization Y).residueField (F Q.1))
            ((Palomar.normalization X).residueField Q.1) :=
          finiteResidueField_of_isFinite F Q.1
        let := schemeStalkAlgebraOfField k (νY ≫ sY) (F Q.1)
        haveI : CharZero ((Palomar.normalization Y).residueField (F Q.1)) :=
          charZero_of_injective_ringHom
            (((Palomar.normalization Y).residue (F Q.1)).hom.comp
              (algebraMap k ((Palomar.normalization Y).presheaf.stalk (F Q.1)))).injective
        have hsep : Algebra.IsSeparable
            ((Palomar.normalization Y).residueField (F Q.1))
            ((Palomar.normalization X).residueField Q.1) :=
          Algebra.IsAlgebraic.isSeparable_of_perfectField
        rcases (schemeDivisorDelta_one_lt_iff F Q).mp hδ with he | hnot
        · exact he
        · exact False.elim (hnot hsep)
      exact not_formallyUnramified_stalkMap_of_normalized_ramification
        g F νX νY (schemeGlobalNormalizationMorphism_comp g) Q
        (schemeGlobalNormalizationMap_stalkBirationalAt X Q.1) he
    · intro hcrit
      by_contra hδ
      have hδ1 : schemeDivisorDelta F Q = 1 := by omega
      have hF := (schemeDivisorDelta_eq_one_iff_formallyEtale F Q).mp hδ1
      have hg := hform.mp hF
      letI := (g.stalkMap (νX Q.1)).hom.toAlgebra
      letI : Algebra.FormallyEtale
          (Y.presheaf.stalk (g (νX Q.1)))
          (X.presheaf.stalk (νX Q.1)) := hg
      exact hcrit (inferInstance : Algebra.FormallyUnramified _ _)
  exact ⟨hδcrit0, hδcrit0.symm.trans hδcrit1⟩

/-- Proposition `prop:loci-compare`(3) for an original divisor `P`:
normality of precisely the two stalks named in the manuscript makes
normalized weighted criticality, non-unramifiedness, and non-étaleness
equivalent.

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`), item (3) of Proposition A.4
(`item:compare-normal`). -/
theorem weightedCriticalPoint_iff_unnormalized_of_normal_stalks
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sY : Y ⟶ Spec (.of k))
    (P : SchemeDivisorPoint X)
    (hnormalX : IsIntegrallyClosed (X.presheaf.stalk P.1))
    (hnormalY : IsIntegrallyClosed (Y.presheaf.stalk (g P.1))) :
    (P.1 ∈ weightedCriticalPointSet g ↔
      P ∈ schemeUnnormalizedCriticalZero g) ∧
    (P ∈ schemeUnnormalizedCriticalZero g ↔
      P ∈ schemeUnnormalizedCriticalOne g) := by
  let F := schemeGlobalNormalizationMorphism g
  let νX := Palomar.normalizationMap X
  let νY := Palomar.normalizationMap Y
  have compare (Q : SchemeDivisorPoint (Palomar.normalization X))
      (hQ : νX Q.1 = P.1) :
      (1 < schemeDivisorDelta F Q ↔
        P ∈ schemeUnnormalizedCriticalZero g) ∧
      (P ∈ schemeUnnormalizedCriticalZero g ↔
        P ∈ schemeUnnormalizedCriticalOne g) := by
    have hpoint : g (νX Q.1) = νY (F Q.1) :=
      congrArg (fun f : Palomar.normalization X ⟶ Y => f Q.1)
        (schemeGlobalNormalizationMorphism_comp g).symm
    have hnormalX' : IsIntegrallyClosed (X.presheaf.stalk (νX Q.1)) := by
      rw [hQ]
      exact hnormalX
    have hnormalY' : IsIntegrallyClosed (Y.presheaf.stalk (νY (F Q.1))) := by
      rw [← hpoint, hQ]
      exact hnormalY
    have h := normalizedCritical_iff_unnormalizedCritical_of_normal_stalks
      g k sY Q hnormalX' hnormalY'
    let P' : SchemeDivisorPoint X :=
      ⟨νX Q.1,
        coheight_eq_of_stalkMap_bijective νX Q.1
          (stalkMap_bijective_of_isIntegralHom_of_integrallyClosed νX Q.1
            (schemeGlobalNormalizationMap_stalkBirationalAt X Q.1) hnormalX') ▸ Q.2⟩
    change (1 < schemeDivisorDelta F Q ↔
        P' ∈ schemeUnnormalizedCriticalZero g) ∧
      (P' ∈ schemeUnnormalizedCriticalZero g ↔
        P' ∈ schemeUnnormalizedCriticalOne g) at h
    have hP : P' = P := Subtype.ext hQ
    simpa only [hP] using h
  constructor
  · constructor
    · rintro ⟨Q, hδ, hQ⟩
      exact (compare Q hQ).1.mp hδ
    · intro hcrit
      obtain ⟨q, hq⟩ := νX.surjective P.1
      have hnormalX' : IsIntegrallyClosed (X.presheaf.stalk (νX q)) := by
        rw [hq]
        exact hnormalX
      have hbij : Function.Bijective (νX.stalkMap q).hom :=
        stalkMap_bijective_of_isIntegralHom_of_integrallyClosed νX q
          (schemeGlobalNormalizationMap_stalkBirationalAt X q) hnormalX'
      have hcoheight : Order.coheight q = 1 := by
        rw [coheight_eq_of_stalkMap_bijective νX q hbij, hq]
        exact P.2
      let Q : SchemeDivisorPoint (Palomar.normalization X) := ⟨q, hcoheight⟩
      exact ⟨Q, (compare Q hq).1.mpr hcrit, hq⟩
  · obtain ⟨q, hq⟩ := νX.surjective P.1
    have hnormalX' : IsIntegrallyClosed (X.presheaf.stalk (νX q)) := by
      rw [hq]
      exact hnormalX
    have hbij : Function.Bijective (νX.stalkMap q).hom :=
      stalkMap_bijective_of_isIntegralHom_of_integrallyClosed νX q
        (schemeGlobalNormalizationMap_stalkBirationalAt X q) hnormalX'
    have hcoheight : Order.coheight q = 1 := by
      rw [coheight_eq_of_stalkMap_bijective νX q hbij, hq]
      exact P.2
    exact (compare ⟨q, hcoheight⟩ hq).2

/-- The nonreduced-fiber branch set is finite in characteristic zero,
as a consequence of `prop:loci-compare`(1) and `lem:branch-crit`(0).

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`), item (1) of Proposition A.4
(`item:compare-finite`). -/
theorem schemeUnnormalizedBranchZero_finite_charZero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [LocallyOfFinitePresentation g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [NoetherianSpace X]
    [CharZero (Y.presheaf.stalk (genericPoint Y))]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)] :
    (schemeUnnormalizedBranchZero g).Finite := by
  rw [schemeUnnormalizedBranchZero_eq_image_critical g k]
  exact (schemeUnnormalizedCritical_finite_charZero g).1.image _

/-- Proposition `prop:loci-compare`(2), the inclusion of non-unramified
source divisors in non-étale source divisors.

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`), item (2) of Proposition A.4
(`item:compare-incl`). -/
theorem schemeUnnormalizedCriticalZero_subset_one
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    schemeUnnormalizedCriticalZero g ⊆ schemeUnnormalizedCriticalOne g :=
  schemeDivisorNonUnramifiedLocus_subset_nonEtaleLocus g

/-- Proposition `prop:loci-compare`(2), the corresponding branch-locus
inclusion on actual finite maps of characteristic-zero varieties.

`paper-p.tex` correspondence: Proposition A.4 (`prop:loci-compare`). -/
theorem schemeUnnormalizedBranchZero_subset_one
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [CharZero k]
    [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
    [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)] :
    schemeUnnormalizedBranchZero g ⊆ schemeUnnormalizedBranchOne g := by
  rw [schemeUnnormalizedBranchZero_eq_image_critical g k,
    schemeUnnormalizedBranchOne_eq_image_critical g k]
  exact Set.image_mono (schemeUnnormalizedCriticalZero_subset_one g)

/-- The manuscript's inclusion `PC₀(f) ⊆ PC₁(f)` for the actual
postcritical sets of an original-scheme endomorphism. -/
theorem schemeUnnormalizedPostcriticalSet_zero_subset_one
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    [∀ U : X.affineOpens, Algebra k Γ(X, U)]
    [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)] :
    schemeUnnormalizedPostcriticalSet false k s f ⊆
      schemeUnnormalizedPostcriticalSet true k s f := by
  unfold schemeUnnormalizedPostcriticalSet
  refine Set.iUnion_mono fun n => ?_
  exact Set.image_mono (by
    simpa [schemeUnnormalizedBranch] using
      schemeUnnormalizedBranchZero_subset_one f k)

/-- A `1`-PCF original-scheme endomorphism is `0`-PCF, as used in the
proof of `paper-p.tex`, Corollary `cor:chains-unnormalized`. -/
theorem IsSchemeUnnormalizedPCF.one_implies_zero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X]
    [∀ U : X.affineOpens, Algebra k Γ(X, U)]
    [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)]
    (h : IsSchemeUnnormalizedPCF true k s f) :
    IsSchemeUnnormalizedPCF false k s f :=
  h.subset (schemeUnnormalizedPostcriticalSet_zero_subset_one k s f)

#print axioms schemeUnnormalizedBranchZero_finite_charZero
#print axioms not_formallyUnramified_stalkMap_of_normalized_ramification
#print axioms weightedCriticalPointSet_subset_schemeUnnormalizedCriticalZero
#print axioms weightedBranchPointSet_subset_schemeUnnormalizedBranchZero_points
#print axioms normalizedCritical_iff_unnormalizedCritical_of_normal_stalks
#print axioms weightedCriticalPoint_iff_unnormalized_of_normal_stalks
#print axioms schemeUnnormalizedCriticalZero_subset_one
#print axioms schemeUnnormalizedBranchZero_subset_one
#print axioms schemeUnnormalizedPostcriticalSet_zero_subset_one
#print axioms IsSchemeUnnormalizedPCF.one_implies_zero

end
end Pcf
