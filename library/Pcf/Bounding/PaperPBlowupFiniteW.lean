/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupBranchFamilyActual

/-!
# A fixed finite branch family on the normalized Rees target

The finite-lift theorem gives a finite set of actual target divisor generic
points, not merely a finite set of codimension-one subtype values. This is
the set `W` used to fix the bounding correction across a tower.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The fixed normalized Rees target has a finite union of branch generic
points whenever all off-exceptional points map into one finite ambient
family. The branch family and its ambient bound may range over every level
of a tower. -/
theorem normalizedRees_fixed_branch_family_finite
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (Ambient : Set (Spec (.of R))) (hAmbient : Ambient.Finite)
    (branch :
      (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
       ℕ → Set (Palomar.normalization (reesProj I))))
    (hcodim :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      ∀ n y, y ∈ branch n → Order.coheight y = 1)
    (hbound :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let β := normalizedReesProjToSpec I a ha
      ∀ n y, y ∈ branch n →
        y ∈ (normalizedReesExceptionalIdealSheaf I a ha).support ∨
          β y ∈ Ambient) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (⋃ n, branch n).Finite) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  let Exceptional : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
    {D | D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}
  let branchDivisor (n : ℕ) : Set (SchemeDivisorPoint (Palomar.normalization (reesProj I))) :=
    {D | D.1 ∈ branch n}
  have hfinite : (⋃ n, branchDivisor n).Finite :=
    normalizedRees_lifted_branch_family_finite k I hI a ha Ambient hAmbient
      branchDivisor (by
        dsimp only
        intro n D hD
        exact hbound n D.1 hD)
  have heq : (⋃ n, branch n) =
      (fun D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) => D.1) ''
        (⋃ n, branchDivisor n) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      refine ⟨⟨y, hcodim n y hn⟩, ?_, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    · rintro ⟨D, hD, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hD
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq]
  exact hfinite.image _

/-- Every point in the non-etale divisor image of a finite dominant cover
to a normal locally Noetherian target has codimension one. -/
theorem schemeDivisorBranchImage_coheight_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormalScheme Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (y : Y) (hy : y ∈ schemeDivisorBranchImage f) :
    Order.coheight y = 1 := by
  obtain ⟨d, -, rfl⟩ := hy
  exact (d.mapFiniteDominantNormal f).2

/-- For actual finite dominant covers of one normalized Rees target, the
union of their non-etale divisor images is finite once each off-exceptional
image maps into the fixed finite ambient branch family. The maps may have
different source schemes at different tower levels. -/
theorem normalizedRees_actual_branch_images_finite
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (Ambient : Set (Spec (.of R))) (hAmbient : Ambient.Finite)
    (X : ℕ → Scheme.{u})
    (hX : ∀ n, IsIntegral (X n))
    (F : (n : ℕ) → X n ⟶
      (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
       Palomar.normalization (reesProj I)))
    (hfinite : ∀ n, IsFinite (F n))
    (hdominant : ∀ n, IsDominant (F n))
    (hbound :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let β := normalizedReesProjToSpec I a ha
      ∀ n y, y ∈ schemeDivisorBranchImage (F n) →
        y ∈ (normalizedReesExceptionalIdealSheaf I a ha).support ∨
          β y ∈ Ambient) :
    (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
     (⋃ n, schemeDivisorBranchImage (F n)).Finite) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpec I)
  letI : IsLocallyNoetherian (Palomar.normalization (reesProj I)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap (reesProj I))
  apply normalizedRees_fixed_branch_family_finite k I hI a ha Ambient hAmbient
    (fun n => schemeDivisorBranchImage (F n))
  · intro n y hy
    letI : IsIntegral (X n) := hX n
    letI : IsFinite (F n) := hfinite n
    letI : IsDominant (F n) := hdominant n
    exact schemeDivisorBranchImage_coheight_one (F n) y hy
  · exact hbound

#print axioms normalizedRees_fixed_branch_family_finite
#print axioms schemeDivisorBranchImage_coheight_one
#print axioms normalizedRees_actual_branch_images_finite

end
end Pcf.Bounding.AllCodimBlowup
