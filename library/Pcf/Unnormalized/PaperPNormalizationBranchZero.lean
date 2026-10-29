/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeLociCompare
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian

/-!
# The normalized branch locus as the image of `branch₀` of the lift

`paper-p.tex`, l. 405–410 and l. 2104–2106: in characteristic zero,
`branch(g) = ν_B(branch₀(g̃))`, where `g̃` is the lift of `g` to the
normalizations and `branch₀(g̃)` is the union of the divisors of `B̃` over
whose generic point the fibre of `g̃` is not reduced. The same holds with the
étale branch locus `branch₁(g̃)`. Divisors are represented by generic points
(convention C1).
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- For a finite dominant map between normal integral locally Noetherian
schemes in characteristic zero, the non-unramified and non-étale divisor loci
coincide. -/
theorem schemeDivisorNonUnramifiedLocus_eq_nonEtale_of_normal_charZero
    {NX NY : Scheme.{u}} (F : NX ⟶ NY) [IsFinite F] [IsDominant F]
    [IsIntegral NX] [IsIntegral NY]
    [IsLocallyNoetherian NX] [IsLocallyNoetherian NY]
    [IsNormalScheme NX] [IsNormalScheme NY]
    (k : Type u) [Field k] [CharZero k] (sY : NY ⟶ Spec (.of k)) :
    schemeUnnormalizedCriticalZero F = schemeUnnormalizedCriticalOne F := by
  apply Set.Subset.antisymm (schemeUnnormalizedCriticalZero_subset_one F)
  intro Q hQ
  by_contra hunr
  apply hQ
  have hunr' : (F.stalkMap Q.1).hom.FormallyUnramified := by
    by_contra h
    exact hunr h
  have he : ¬ 1 < schemeDivisorRamificationIdx F Q := by
    intro he
    haveI : IsIso ((𝟙 NX : NX ⟶ NX).stalkMap (genericPoint NX)) := by
      rw [Scheme.Hom.stalkMap_id]
      exact IsIso.id _
    have hbir : IsStalkBirationalAt (𝟙 NX) Q.1 :=
      isStalkBirationalAt_of_isIso_generic_stalkMap (𝟙 NX) Q.1
    have := not_formallyUnramified_stalkMap_of_normalized_ramification
      F F (𝟙 NX) (𝟙 NY) (by simp) Q hbir he
    exact this hunr'
  have hsep : (letI := (F.residueFieldMap Q.1).hom.toAlgebra
      Algebra.IsSeparable (NY.residueField (F Q.1)) (NX.residueField Q.1)) := by
    letI := (F.residueFieldMap Q.1).hom.toAlgebra
    letI : FiniteDimensional (NY.residueField (F Q.1)) (NX.residueField Q.1) :=
      finiteResidueField_of_isFinite F Q.1
    let := schemeStalkAlgebraOfField k sY (F Q.1)
    haveI : CharZero (NY.residueField (F Q.1)) := charZero_of_injective_ringHom
      ((NY.residue (F Q.1)).hom.comp (algebraMap k (NY.presheaf.stalk (F Q.1)))).injective
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hδ : schemeDivisorDelta F Q = 1 := by
    have hpos : 0 < schemeDivisorDelta F Q := schemeDivisorDelta_pos_of_isFinite F Q
    have : ¬ 1 < schemeDivisorDelta F Q := by
      rw [schemeDivisorDelta_one_lt_iff]
      rintro (h | h)
      · exact he h
      · exact h hsep
    omega
  exact (schemeDivisorDelta_eq_one_iff_formallyEtale F Q).mp hδ

/-- **`paper-p.tex`, l. 405–410 and l. 2104–2106.** In characteristic zero,
the normalized branch locus of `g : A → B` is the image under `ν_B` of the
unnormalized branch locus `branch₀(g̃)` of the lift `g̃` to the
normalizations (the divisors of `B̃` over whose generic point the fibre of
`g̃` is not reduced), and equally of `branch₁(g̃)`. -/
theorem weightedBranchPointSet_eq_normalization_image_branchZero_charZero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)] [IsFinite (Palomar.normalizationMap Y)]
    (k : Type u) [Field k] [CharZero k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] :
    weightedBranchPointSet g =
        Palomar.normalizationMap Y '' {y | ∃ E ∈ schemeUnnormalizedBranchZero
          (schemeGlobalNormalizationMorphism g), E.1 = y} ∧
    weightedBranchPointSet g =
        Palomar.normalizationMap Y '' {y | ∃ E ∈ schemeUnnormalizedBranchOne
          (schemeGlobalNormalizationMorphism g), E.1 = y} := by
  let F := schemeGlobalNormalizationMorphism g
  let νX := Palomar.normalizationMap X
  let νY := Palomar.normalizationMap Y
  let sNY : Palomar.normalization Y ⟶ Spec (.of k) := νY ≫ sY
  haveI : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian sNY
  haveI : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (νX ≫ g ≫ sY)
  letI (U : (Palomar.normalization Y).affineOpens) := schemeAffineAlgebraOfField k sNY U
  letI (U : (Palomar.normalization Y).affineOpens) :=
    schemeAffineAlgebraOfField_finiteType k sNY U
  have hcrit : {p : SchemeDivisorPoint (Palomar.normalization X) |
      1 < schemeDivisorDelta F p} = schemeUnnormalizedCriticalOne F :=
    schemeDivisorWeightedCritical_eq_nonEtale F
  have h01 := schemeDivisorNonUnramifiedLocus_eq_nonEtale_of_normal_charZero F k sNY
  have himage (C : Set (SchemeDivisorPoint (Palomar.normalization X)))
      (hC : C = schemeUnnormalizedCriticalOne F) :
      weightedBranchPointSet g = νY '' {y | ∃ E ∈ (fun P => P.mapFiniteDominantFiniteType F k) '' C,
        E.1 = y} := by
    subst hC
    ext y
    simp only [weightedBranchPointSet, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, ⟨p, rfl, hp⟩, rfl⟩
      refine ⟨F p.1, ⟨_, ⟨p, ?_, rfl⟩, rfl⟩, rfl⟩
      rw [← hcrit]
      exact hp
    · rintro ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
      refine ⟨p.mapFiniteDominantNormal F, ⟨p, rfl, ?_⟩, rfl⟩
      rw [← hcrit] at hp
      exact hp
  constructor
  · rw [schemeUnnormalizedBranchZero_eq_image_critical F k]
    exact himage _ h01
  · rw [schemeUnnormalizedBranchOne_eq_image_critical F k]
    exact himage _ rfl

#print axioms schemeDivisorNonUnramifiedLocus_eq_nonEtale_of_normal_charZero
#print axioms weightedBranchPointSet_eq_normalization_image_branchZero_charZero

end

end Pcf
