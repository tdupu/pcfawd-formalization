/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupMonodromyTransport
public import Pcf.Bounding.FieldExtensionNormalizationFieldEquiv
public import Pcf.Bounding.AllCodimBlowupExceptionalSurjectivity
public import Pcf.Bounding.PaperPBlowupExceptionalComponents
public import Pcf.Bounding.CriticalLoci
public import Pcf.Bounding.PaperPBlowupArbitraryCentre

/-!
# The finite surjective affine normalized blow-up map

This supplies the surjectivity clause of `paper-p.tex`, Proposition
`prop:normalized-blowup-construction`, for the actual absolute
normalizations of the Rees blow-ups associated to an affine finite cover.
The global gluing and uniqueness clauses remain separate.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A finite dominant map of the normalized Rees blow-ups is surjective.
This is the actual affine morphism, rather than a map on a chart. -/
theorem normalizedReesProjMap_surjective
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    Function.Surjective (normalizedReesProjMap f hf hfin I a ha) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f hf hfin I a ha
  letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant f hf hfin I a ha
  exact (surjective_of_isDominant_of_isClosed_range F
    F.isClosedMap.isClosed_range).surj

/-- For an integral reduced source and a separated target over the base,
a dominant lift across a birational map is determined by the base square.
This is the uniqueness principle in the affine form of
`prop:normalized-blowup-construction`. -/
theorem dominantLift_eq_of_genericField_surjective
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (β : Y ⟶ Z) [IsDominant β] [IsSeparated β]
    (hβsurj : Function.Surjective (Pcf.schemeGenericFieldHom β))
    (F G : X ⟶ Y) [IsDominant F] [IsDominant G]
    (hsquare : F ≫ β = G ≫ β) : F = G := by
  have hfield : Pcf.schemeGenericFieldHom F = Pcf.schemeGenericFieldHom G := by
    have hcomp := Pcf.schemeGenericFieldHom_congr hsquare
    rw [Pcf.schemeGenericFieldHom_comp, Pcf.schemeGenericFieldHom_comp] at hcomp
    ext y
    obtain ⟨z, rfl⟩ := hβsurj y
    exact congrArg (fun φ : Z.functionField →+* X.functionField => φ z) hcomp
  have hgeneric : Pcf.schemeGenericMorphism F = Pcf.schemeGenericMorphism G := by
    apply Spec.preimage_injective
    ext y
    exact RingHom.congr_fun hfield y
  apply ext_of_isDominant_of_isSeparated β hsquare (Pcf.schemeGenericInclusion X)
  calc
    Pcf.schemeGenericInclusion X ≫ F =
        Pcf.schemeGenericMorphism F ≫ Pcf.schemeGenericInclusion Y :=
      (Pcf.schemeGenericMorphism_comp F).symm
    _ = Pcf.schemeGenericMorphism G ≫ Pcf.schemeGenericInclusion Y := by rw [hgeneric]
    _ = Pcf.schemeGenericInclusion X ≫ G := Pcf.schemeGenericMorphism_comp G

/-- The normalized Rees blow-up map has surjective pullback on rational
function fields; its generic stalk map is an isomorphism. -/
theorem normalizedReesProjToSpec_genericField_surjective
    {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    letI : IsDominant (normalizedReesProjToSpec I a ha) :=
      normalizedReesProjToSpec_isDominant I a ha
    Function.Surjective
      (Pcf.schemeGenericFieldHom (normalizedReesProjToSpec I a ha)) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let β := normalizedReesProjToSpec I a ha
  letI : IsDominant β := normalizedReesProjToSpec_isDominant I a ha
  letI : IsIso (β.stalkMap
      (genericPoint (Palomar.normalization (reesProj I)))) :=
    normalizedReesProjToSpec_genericStalk_isIso I a ha
  let hgp := map_genericPoint_eq_of_isDominant β
  let e := ((Spec (.of R)).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  rw [Pcf.schemeGenericFieldHom_eq_stalkCongr]
  exact ((ConcreteCategory.bijective_of_isIso
    (β.stalkMap (genericPoint (Palomar.normalization (reesProj I))))).surjective).comp
      e.symm.surjective

/-- The affine normalized Rees lift is unique among surjective maps
satisfying the manuscript's commuting square over the original finite
cover. This is the uniqueness clause for the finite surjections of
`prop:normalized-blowup-construction`. -/
theorem normalizedReesProjMap_unique
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    let X' := Palomar.normalization (reesProj (I.map f))
    let Y' := Palomar.normalization (reesProj I)
    ∀ (G : X' ⟶ Y'),
      Function.Surjective G →
      G ≫ normalizedReesProjToSpec I a ha =
        normalizedReesProjToSpec (I.map f) b hb ≫
          Spec.map (CommRingCat.ofHom f) →
      G = normalizedReesProjMap f hf hfin I a ha := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  let X' := Palomar.normalization (reesProj (I.map f))
  let Y' := Palomar.normalization (reesProj I)
  let F : X' ⟶ Y' := normalizedReesProjMap f hf hfin I a ha
  let β : Y' ⟶ Spec (.of R) := normalizedReesProjToSpec I a ha
  let α : X' ⟶ Spec (.of S) := normalizedReesProjToSpec (I.map f) b hb
  let φ : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom f)
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper β := by
    dsimp only [β, normalizedReesProjToSpec]
    infer_instance
  letI : IsSeparated β := inferInstance
  letI : IsDominant β := normalizedReesProjToSpec_isDominant I a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant f hf hfin I a ha
  letI : IsDominant α := normalizedReesProjToSpec_isDominant (I.map f) b hb
  letI : IsDominant φ := affineSpecMap_isDominant f hf
  dsimp only
  intro G hGsurj hG
  letI : Surjective G := ⟨hGsurj⟩
  letI : IsDominant G := inferInstance
  apply dominantLift_eq_of_genericField_surjective β
    (normalizedReesProjToSpec_genericField_surjective I a ha) G F
  calc
    G ≫ β = α ≫ φ := hG
    _ = F ≫ β := (normalizedReesProjToSpec_comm f hf hfin I a ha).symm

/-- The complete existence and uniqueness statement of the normalized
blow-up construction for a finite dominant **affine** variety cover and a
nonzero finitely generated centre. The unique morphism is finite,
surjective, and commutes with the maps to the original affine schemes.
Global gluing beyond an affine base is still open. -/
theorem normalizedReesProjMap_existsUnique_finiteSurjective
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    let X' := Palomar.normalization (reesProj (I.map f))
    let Y' := Palomar.normalization (reesProj I)
    ∃! F : X' ⟶ Y',
      IsFinite F ∧ Function.Surjective F ∧
      F ≫ normalizedReesProjToSpec I a ha =
        normalizedReesProjToSpec (I.map f) b hb ≫
          Spec.map (CommRingCat.ofHom f) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
  dsimp only
  refine ⟨normalizedReesProjMap f hf hfin I a ha, ?_, ?_⟩
  · exact ⟨normalizedReesProjMap_isFinite k f hf hfin I hI a ha,
      normalizedReesProjMap_surjective k f hf hfin I hI a ha,
      normalizedReesProjToSpec_comm f hf hfin I a ha⟩
  · intro G hG
    exact normalizedReesProjMap_unique k f hf hfin I hI a ha G hG.2.1 hG.2.2

/-- A fixed normalized affine blow-up has only finitely many exceptional
integral effective divisor generic points. These are the possible `E_j`
in the proof of `thm:tower-restrict`, independently of the varying covers
above the fixed base. -/
theorem normalizedReesExceptional_divisorPoints_finite
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    {D : SchemeDivisorPoint (Palomar.normalization (reesProj I)) |
      D.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support}.Finite := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : NoetherianSpace (Palomar.normalization (reesProj I)) :=
    normalizedReesProj_noetherianSpace k I hI a ha
  exact finite_schemeDivisorPoint_mem_of_isClosed
    (normalizedReesExceptionalIdealSheaf I a ha).support.isClosed
    (normalizedReesExceptional_support_proper I a ha)

/-- The affine construction applies to the image of every proper integral
closed subvariety of the finite source: its contracted prime centre is
nonzero, so no centre equation must be supplied by the caller. -/
theorem normalizedReesProjMap_existsUnique_for_proper_source
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (P' : Ideal S) [P'.IsPrime] (hP' : P' ≠ ⊥) :
    letI : Algebra R S := f.toAlgebra
    let I := P'.under R
    ∃ a : I, ∃ ha : (a : R) ≠ 0,
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      let X' := Palomar.normalization (reesProj (I.map f))
      let Y' := Palomar.normalization (reesProj I)
      ∃! F : X' ⟶ Y',
        IsFinite F ∧ Function.Surjective F ∧
        F ≫ normalizedReesProjToSpec I a ha =
          normalizedReesProjToSpec (I.map f) b hb ≫
            Spec.map (CommRingCat.ofHom f) := by
  letI : Algebra R S := f.toAlgebra
  let I := P'.under R
  have hIne := (properSourcePrime_minimalPulledBackCentre f hfin P' hP').1
  obtain ⟨av, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIne
  let a : I := ⟨av, haI⟩
  have ha : (a : R) ≠ 0 := ha0
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  exact ⟨a, ha, normalizedReesProjMap_existsUnique_finiteSurjective
    k f hf hfin I hI a ha⟩

#print axioms normalizedReesProjMap_surjective
#print axioms dominantLift_eq_of_genericField_surjective
#print axioms normalizedReesProjToSpec_genericField_surjective
#print axioms normalizedReesProjMap_unique
#print axioms normalizedReesProjMap_existsUnique_finiteSurjective
#print axioms normalizedReesExceptional_divisorPoints_finite
#print axioms normalizedReesProjMap_existsUnique_for_proper_source

end
end Pcf.Bounding.AllCodimBlowup
