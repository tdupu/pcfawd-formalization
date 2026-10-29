/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingClosedSupports
public import Pcf.Bounding.GlobalNormalizationMorphism

/-!
# Branch loci of actual towers

`paper.tex`, Lemma `lem:tower`. First prove the branch-divisor formula on normal
schemes from actual stalk ramification multiplication and actual divisor lifting.
Then push the closed supports through the canonical normalizations. The final
theorem allows nonnormal source, intermediate, and target schemes.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

private theorem one_lt_mul_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    1 < a * b ↔ 1 < a ∨ 1 < b := by
  constructor
  · intro h
    by_contra hn
    have ha' : a = 1 := by omega
    have hb' : b = 1 := by omega
    simp [ha', hb'] at h
  · rintro (h | h)
    · exact h.trans_le (Nat.le_mul_of_pos_right _ hb)
    · exact h.trans_le (Nat.le_mul_of_pos_left _ ha)

/-- The branch-divisor tower formula for actual normal schemes. The reverse
inclusion uses the proved surjectivity of finite dominant divisor pushforward. -/
theorem reducedFiberBranch_tower
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsNormalScheme X] [IsNormalScheme Y] [IsNormalScheme Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] :
    schemeReducedFiberBranch (f ≫ g) = schemeReducedFiberBranch g ∪
      schemeDivisorMap g (coheight_apply_eq_one g) '' schemeReducedFiberBranch f := by
  have hram (Q : SchemeDivisorPoint X) :
      1 < schemeDivisorRamificationIdx (f ≫ g) Q ↔
        1 < schemeDivisorRamificationIdx g (Q.mapFiniteDominantNormal f) ∨
          1 < schemeDivisorRamificationIdx f Q := by
    rw [schemeDivisorRamificationIdx_comp, one_lt_mul_iff
      (schemeDivisorRamificationIdx_pos g _) (schemeDivisorRamificationIdx_pos f _)]
  ext E
  constructor
  · intro hE
    obtain ⟨Q, hQE, hQ⟩ := (mem_schemeReducedFiberBranch_iff (f ≫ g) E).mp hE
    rcases (hram Q).mp hQ with hg | hf
    · exact Or.inl ((mem_schemeReducedFiberBranch_iff g E).mpr
        ⟨Q.mapFiniteDominantNormal f, hQE, hg⟩)
    · refine Or.inr ⟨Q.mapFiniteDominantNormal f,
        (mem_schemeReducedFiberBranch_iff f _).mpr ⟨Q, rfl, hf⟩, ?_⟩
      exact Subtype.ext hQE
  · rintro (hE | ⟨D, hD, rfl⟩)
    · obtain ⟨D, hDE, hD⟩ := (mem_schemeReducedFiberBranch_iff g E).mp hE
      obtain ⟨Q, hQD⟩ := SchemeDivisorPoint.mapFiniteDominantNormal_surjective f D
      apply (mem_schemeReducedFiberBranch_iff (f ≫ g) E).mpr
      refine ⟨Q, ?_, (hram Q).mpr (Or.inl (by simpa only [hQD] using hD))⟩
      change g (f Q.1) = E.1
      have hp := congrArg Subtype.val hQD
      exact (congrArg g hp).trans hDE
    · obtain ⟨Q, hQD, hQ⟩ := (mem_schemeReducedFiberBranch_iff f D).mp hD
      exact (mem_schemeReducedFiberBranch_iff (f ≫ g) _).mpr
        ⟨Q, congrArg g hQD, (hram Q).mpr (Or.inr hQ)⟩

/-- Unions of divisor sets correspond to unions of their supports. -/
theorem divisorSupport_union {X : Scheme.{u}} (S T : Set (SchemeDivisorPoint X)) :
    divisorSupport (S ∪ T) = divisorSupport S ∪ divisorSupport T := by
  ext x
  simp only [divisorSupport, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨Q, hQ | hQ, hx⟩
    · exact Or.inl ⟨Q, hQ, hx⟩
    · exact Or.inr ⟨Q, hQ, hx⟩
  · rintro (⟨Q, hQ, hx⟩ | ⟨Q, hQ, hx⟩)
    · exact ⟨Q, Or.inl hQ, hx⟩
    · exact ⟨Q, Or.inr hQ, hx⟩

/-- The normal-scheme tower formula as an equality of actual branch supports. -/
theorem reducedFiberBranch_support_tower
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsNormalScheme X] [IsNormalScheme Y] [IsNormalScheme Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] :
    divisorSupport (schemeReducedFiberBranch (f ≫ g)) =
      divisorSupport (schemeReducedFiberBranch g) ∪
        g '' divisorSupport (schemeReducedFiberBranch f) := by
  rw [reducedFiberBranch_tower, divisorSupport_union,
    ← image_divisorSupport g (coheight_apply_eq_one g)]

/-- The normalized branch support of an arbitrary finite dominant morphism,
using the actual canonical normalizations and their nonreduced divisor fibers.
This is `eq:branch-normalization` for a map between distinct schemes. -/
noncomputable def normalizedMorphismBranchSupport
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] : Set Y :=
  Palomar.normalizationMap Y ''
    divisorSupport (schemeReducedFiberBranch (schemeGlobalNormalizationMorphism f))

/-- On endomorphisms, the arbitrary-morphism branch support agrees with the
existing normalized branch-divisor definition used by the PCF statements. -/
theorem normalizedMorphismBranchSupport_eq_schemeNormalizedBranch
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [CharZero (X.presheaf.stalk (genericPoint X))]
    [∀ U : X.affineOpens, Algebra k Γ(X, U)]
    [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] [LocallyOfFinitePresentation f] :
    normalizedMorphismBranchSupport f = divisorSupport (schemeNormalizedBranch k f) := by
  let : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType X k
  unfold normalizedMorphismBranchSupport
  rw [schemeGlobalNormalizationMorphism_eq_lift,
    schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch]
  exact image_divisorSupport (Palomar.normalizationMap X)
    (coheight_apply_eq_one_of_finiteType (Palomar.normalizationMap X) k) _

/-- `lem:tower`: the normalized branch support of the composite is the union
of the bottom branch support and the actual image of the upper branch support.
All three schemes may be nonnormal. Finite type over the field supplies finite
normalizations; no branch equality is an input. This stronger form works in
every characteristic, including the paper's characteristic-zero setting.

Manuscript: `lem:tower` (Lemma 5.2). -/
theorem normalized_branch_tower
    (k : Type u) [Field k]
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g] :
    normalizedMorphismBranchSupport (f ≫ g) = normalizedMorphismBranchSupport g ∪
      g '' normalizedMorphismBranchSupport f := by
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsFinite (Palomar.normalizationMap Z) := schemeGlobalNormalizationMap_isFinite Z k s
  let : IsFinite (Palomar.normalizationMap Y) :=
    schemeGlobalNormalizationMap_isFinite Y k (g ≫ s)
  let : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ g ≫ s)
  unfold normalizedMorphismBranchSupport
  rw [← schemeGlobalNormalizationMorphism_comp_morphism,
    reducedFiberBranch_support_tower, Set.image_union]
  congr 1
  simp only [Set.image_image]
  congr 1
  funext x
  exact congrArg (fun h : Palomar.normalization Y ⟶ Z => h x)
    (schemeGlobalNormalizationMorphism_comp g)

end Pcf.PaperCharZero
