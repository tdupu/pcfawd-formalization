/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupFiniteLiftOffCentre
public import Pcf.Bounding.PaperPBlowupBranch
public import Pcf.Bounding.PaperPBoundingBranchBridge

/-!
# Branch support of the actual normalized Rees lift

Every non-etale divisor image of the finite normalized Rees lift is either
exceptional or lies over an ambient branch divisor of the original affine
cover. The weighted branch set is contained in this divisor image.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- Target generic points of images of non-etale source divisors. -/
def schemeDivisorBranchImage {X Y : Scheme.{u}} (f : X ⟶ Y) : Set Y :=
  (fun d : SchemeDivisorPoint X => f d.1) '' schemeDivisorNonEtaleLocus f

/-- On a normal finite cover, every weighted branch generic point is the
image of a non-etale source divisor. -/
theorem weightedBranchPointSet_subset_schemeDivisorBranchImage
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    weightedBranchPointSet f ⊆ schemeDivisorBranchImage f := by
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal f]
  rintro y ⟨d, hd, rfl⟩
  change 1 < schemeDivisorDelta f d at hd
  refine ⟨d, ?_, rfl⟩
  change ¬ (f.stalkMap d.1).hom.FormallyEtale
  intro he
  have hδ := schemeDivisorDelta_eq_one_of_formallyEtale f d he
  omega

set_option maxHeartbeats 800000 in
/-- The non-exceptional branch image of the actual normalized Rees lift
maps into the branch image of the original affine cover. -/
theorem normalizedReesProjMap_branchImage_offExceptional
    {R S : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (Ambient : Set (Spec (.of R)))
    (hAmbient : schemeDivisorBranchImage (Spec.map (CommRingCat.ofHom f)) ⊆
      Ambient)
    (y : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      Palomar.normalization (reesProj I)))
    (hy :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
      y ∈ schemeDivisorBranchImage (normalizedReesProjMap f hf hfin I a ha))
    (hOff :
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      y ∉ (normalizedReesExceptionalIdealSheaf I a ha).support) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    (normalizedReesProjToSpec I a ha) y ∈ Ambient := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f hf hfin I a ha
  let β := normalizedReesProjToSpec I a ha
  let φ := Spec.map (CommRingCat.ofHom f)
  change y ∈ schemeDivisorBranchImage F at hy
  obtain ⟨w, hcrit, hwF⟩ := hy
  have hFoff : F w.1 ∉ (normalizedReesExceptionalIdealSheaf I a ha).support := by
    simpa only [hwF] using hOff
  obtain ⟨d, -, hd, hβ⟩ :=
    normalizedReesProjMap_branch_offCentre f hf hfin I a ha w.1 w.2 hFoff hcrit
  change β y ∈ Ambient
  rw [← hwF, hβ]
  exact hAmbient ⟨d, hd, rfl⟩

#print axioms weightedBranchPointSet_subset_schemeDivisorBranchImage
#print axioms normalizedReesProjMap_branchImage_offExceptional

end
end Pcf.Bounding.AllCodimBlowup
