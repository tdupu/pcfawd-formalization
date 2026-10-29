/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGenericStalkComparison
public import Pcf.Bounding.GenericStalkMonodromyTransport

/-!
# Generic monodromy transport through the normalized Rees blow-up

The structural maps of the Rees Proj and their absolute normalizations
induce isomorphisms on generic stalks. A commuting square with these
birational maps therefore preserves the finite map's generic field
extension and its prime-to-characteristic monodromy, as used in
`latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

noncomputable section

/-- A commuting square with dominant generically isomorphic vertical maps
preserves prime-to-`p` generic monodromy of its finite horizontal maps. -/
theorem primeToPMonodromy_of_genericBirationalSquare
    (p : ℕ) {X Y X' Y' : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral X'] [IsIntegral Y']
    (f : X ⟶ Y) (g : X' ⟶ Y')
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    (vX : X' ⟶ X) (vY : Y' ⟶ Y)
    [IsDominant vX] [IsDominant vY]
    [IsIso (vX.stalkMap (genericPoint X'))]
    [IsIso (vY.stalkMap (genericPoint Y'))]
    (hcomm : g ≫ vY = vX ≫ f)
    (hmono : Pcf.IsPrimeToPMonodromyMap p f) :
    Pcf.IsPrimeToPMonodromyMap p g := by
  let η := genericPoint X'
  have hX : vX η = genericPoint X :=
    map_genericPoint_eq_of_isDominant vX
  have hg : g η = genericPoint Y' :=
    map_genericPoint_eq_of_isDominant g
  have hpoint : f (genericPoint X) = vY (g η) := by
    have h := congrArg (fun m : X' ⟶ Y => m η) hcomm
    change vY (g η) = f (vX η) at h
    rw [hX] at h
    exact h.symm
  have hisoY : IsIso (vY.stalkMap (g η)) := by
    rw [hg]
    infer_instance
  let eE : X.presheaf.stalk (genericPoint X) ≃+* X'.presheaf.stalk η :=
    ((X.presheaf.stalkCongr (.of_eq hX.symm)) ≪≫
      asIso (vX.stalkMap η)).commRingCatIsoToRingEquiv
  let eK : Y.presheaf.stalk (f (genericPoint X)) ≃+*
      Y'.presheaf.stalk (g η) :=
    ((Y.presheaf.stalkCongr (.of_eq hpoint)) ≪≫
      asIso (vY.stalkMap (g η))).commRingCatIsoToRingEquiv
  have hcommField : (g.stalkMap η).hom.comp eK.toRingHom =
      eE.toRingHom.comp (f.stalkMap (genericPoint X)).hom := by
    have hsqpoint : vY (g η) = f (vX η) := by
      have h := congrArg (fun m : X' ⟶ Y => m η) hcomm
      simpa only [Scheme.Hom.comp_apply] using h
    have himage : f (genericPoint X) = f (vX η) :=
      congrArg f hX.symm
    have hcompCongr :
        (Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
          (Y.presheaf.stalkCongr (.of_eq hsqpoint)).hom =
        (Y.presheaf.stalkCongr (.of_eq himage)).hom := by
      change Y.presheaf.stalkSpecializes (Inseparable.of_eq hpoint).ge ≫
        Y.presheaf.stalkSpecializes (Inseparable.of_eq hsqpoint).ge =
        Y.presheaf.stalkSpecializes (Inseparable.of_eq himage).ge
      exact TopCat.Presheaf.stalkSpecializes_comp _ _ _
    have hsquare := Scheme.Hom.stalkMap_congr_hom (g ≫ vY) (vX ≫ f)
      hcomm η
    simp only [Scheme.Hom.stalkMap_comp] at hsquare
    let cE : X.presheaf.stalk (genericPoint X) ⟶ X'.presheaf.stalk η :=
      (X.presheaf.stalkCongr (.of_eq hX.symm)).hom ≫ vX.stalkMap η
    let cK : Y.presheaf.stalk (f (genericPoint X)) ⟶
        Y'.presheaf.stalk (g η) :=
      (Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫ vY.stalkMap (g η)
    have hcat : cK ≫ g.stalkMap η =
        f.stalkMap (genericPoint X) ≫ cE := by
      dsimp only [cK, cE]
      have hnat := Scheme.Hom.stalkMap_congr_point f
        (genericPoint X) (vX η) hX.symm
      calc
        ((Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            vY.stalkMap (g η)) ≫ g.stalkMap η =
          (Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            (vY.stalkMap (g η) ≫ g.stalkMap η) := Category.assoc _ _ _
        _ = (Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            ((Y.presheaf.stalkCongr (.of_eq hsqpoint)).hom ≫
              f.stalkMap (vX η) ≫ vX.stalkMap η) := by
          rw [hsquare]
          rfl
        _ = ((Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫
            (Y.presheaf.stalkCongr (.of_eq hsqpoint)).hom) ≫
              f.stalkMap (vX η) ≫ vX.stalkMap η := by
          simp only [Category.assoc]
        _ = (Y.presheaf.stalkCongr (.of_eq himage)).hom ≫
              f.stalkMap (vX η) ≫ vX.stalkMap η := by rw [hcompCongr]
        _ = (f.stalkMap (genericPoint X) ≫
              (X.presheaf.stalkCongr (.of_eq hX.symm)).hom) ≫
                vX.stalkMap η := by
          rw [hnat]
          exact (Category.assoc _ _ _).symm
        _ = f.stalkMap (genericPoint X) ≫
            ((X.presheaf.stalkCongr (.of_eq hX.symm)).hom ≫
              vX.stalkMap η) := by
          exact Category.assoc _ _ _
    change (g.stalkMap η).hom.comp cK.hom =
      cE.hom.comp (f.stalkMap (genericPoint X)).hom
    exact congrArg CommRingCat.Hom.hom hcat
  exact Pcf.isPrimeToPMonodromyMap_of_genericStalkEquivs p f g
    eK eE hcommField hmono

#print axioms primeToPMonodromy_of_genericBirationalSquare

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The actual structural map from the absolute normalization of a Rees
blow-up to its affine base. -/
def normalizedReesProjToSpec (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    Palomar.normalization (reesProj I) ⟶ Spec (.of R) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  exact Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I

/-- The normalized blow-up structural map is dominant. -/
theorem normalizedReesProjToSpec_isDominant (I : Ideal R) (a : I)
    (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    IsDominant (normalizedReesProjToSpec I a ha) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsDominant (reesProjToSpec I) :=
    reesProjToSpec_isDominant I a ha
  unfold normalizedReesProjToSpec
  infer_instance

/-- The normalized blow-up remains generically identical to its affine
base, as an isomorphism of actual scheme stalks. -/
theorem normalizedReesProjToSpec_genericStalk_isIso
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    IsIso ((normalizedReesProjToSpec I a ha).stalkMap
      (genericPoint (Palomar.normalization (reesProj I)))) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let η := genericPoint (Palomar.normalization (reesProj I))
  have hη : Palomar.normalizationMap (reesProj I) η =
      genericPoint (reesProj I) :=
    map_genericPoint_eq_of_isDominant _
  have hblow : IsIso ((reesProjToSpec I).stalkMap
      (Palomar.normalizationMap (reesProj I) η)) := by
    rw [hη]
    exact reesProjToSpec_genericStalk_isIso I a ha
  letI : IsIso ((reesProjToSpec I).stalkMap
      (Palomar.normalizationMap (reesProj I) η)) := hblow
  letI : IsIso ((Palomar.normalizationMap (reesProj I)).stalkMap η) :=
    inferInstance
  unfold normalizedReesProjToSpec
  rw [Scheme.Hom.stalkMap_comp]
  exact IsIso.comp_isIso' hblow
    (inferInstance : IsIso ((Palomar.normalizationMap (reesProj I)).stalkMap η))

#print axioms normalizedReesProjToSpec_isDominant
#print axioms normalizedReesProjToSpec_genericStalk_isIso

variable {S : Type u} [CommRing S] [IsDomain S]

/-- The normalized Rees lift lies over the original finite affine morphism. -/
theorem normalizedReesProjToSpec_comm
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 :=
      fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    normalizedReesProjMap f hf hfin I a ha ≫
        normalizedReesProjToSpec I a ha =
      normalizedReesProjToSpec (I.map f) b hb ≫
        Spec.map (CommRingCat.ofHom f) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 :=
    fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  dsimp only [normalizedReesProjToSpec]
  calc
    normalizedReesProjMap f hf hfin I a ha ≫
        (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) =
      (normalizedReesProjMap f hf hfin I a ha ≫
        Palomar.normalizationMap (reesProj I)) ≫ reesProjToSpec I :=
        (Category.assoc _ _ _).symm
    _ = (Palomar.normalizationMap (reesProj (I.map f)) ≫
        reesProjMap f I) ≫ reesProjToSpec I := by
          rw [normalizedReesProjMap_comm f hf hfin I a ha]
    _ = Palomar.normalizationMap (reesProj (I.map f)) ≫
        (reesProjMap f I ≫ reesProjToSpec I) := Category.assoc _ _ _
    _ = Palomar.normalizationMap (reesProj (I.map f)) ≫
        (reesProjToSpec (I.map f) ≫ Spec.map (CommRingCat.ofHom f)) := by
          rw [reesProjMap_toSpec]
    _ = (Palomar.normalizationMap (reesProj (I.map f)) ≫
        reesProjToSpec (I.map f)) ≫ Spec.map (CommRingCat.ofHom f) :=
          (Category.assoc _ _ _).symm

#print axioms normalizedReesProjToSpec_comm

omit [IsDomain R] [IsDomain S] in
theorem affineSpecMap_isFinite (f : R →+* S) (hfin : f.Finite) :
    IsFinite (Spec.map (CommRingCat.ofHom f)) :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom f)).mpr hfin

omit [IsDomain R] [IsDomain S] in
theorem affineSpecMap_isDominant (f : R →+* S)
    (hf : Function.Injective f) :
    IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  rw [isDominant_iff]
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hf]; exact bot_le)

theorem normalizedReesProjMap_isDominant
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 :=
      fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    IsDominant (normalizedReesProjMap f hf hfin I a ha) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 :=
    fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  letI : IsFinite (reesProjMap f I) := reesProjMap_isFinite f I hfin
  letI : IsDominant (reesProjMap f I) :=
    reesProjMap_isDominant_of_injective f hf I a ha
  change IsDominant (Pcf.schemeGlobalNormalizationMorphism (reesProjMap f I))
  infer_instance

/-- The actual finite morphism of absolute normalizations of Rees blow-ups
has the same prime-to-`p` generic monodromy as its original affine map. -/
theorem normalizedReesProjMap_primeToPMonodromy
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (p : ℕ) (f : R →+* S) (hf : Function.Injective f)
    (hfin : f.Finite) (I : Ideal R) (hI : I.FG)
    (a : I) (ha : (a : R) ≠ 0)
    (hmono :
      letI : IsFinite (Spec.map (CommRingCat.ofHom f)) :=
        affineSpecMap_isFinite f hfin
      letI : IsDominant (Spec.map (CommRingCat.ofHom f)) :=
        affineSpecMap_isDominant f hf
      Pcf.IsPrimeToPMonodromyMap p (Spec.map (CommRingCat.ofHom f))) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 :=
      fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    letI : IsFinite (normalizedReesProjMap f hf hfin I a ha) :=
      normalizedReesProjMap_isFinite k f hf hfin I hI a ha
    letI : IsDominant (normalizedReesProjMap f hf hfin I a ha) :=
      normalizedReesProjMap_isDominant f hf hfin I a ha
    Pcf.IsPrimeToPMonodromyMap p
      (normalizedReesProjMap f hf hfin I a ha) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 :=
    fun h => ha (hf (by simpa [b, mappedCenterElement] using h))
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let F : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom f)
  let G : Palomar.normalization (reesProj (I.map f)) ⟶
      Palomar.normalization (reesProj I) :=
    normalizedReesProjMap f hf hfin I a ha
  let vX : Palomar.normalization (reesProj (I.map f)) ⟶
      Spec (.of S) :=
    normalizedReesProjToSpec (I.map f) b hb
  let vY : Palomar.normalization (reesProj I) ⟶ Spec (.of R) :=
    normalizedReesProjToSpec I a ha
  letI : IsFinite F := affineSpecMap_isFinite f hfin
  letI : IsDominant F := affineSpecMap_isDominant f hf
  letI : IsFinite G := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsDominant G := normalizedReesProjMap_isDominant f hf hfin I a ha
  letI : IsDominant vX := normalizedReesProjToSpec_isDominant
    (I.map f) b hb
  letI : IsDominant vY := normalizedReesProjToSpec_isDominant I a ha
  letI : IsIso (vX.stalkMap
      (genericPoint (Palomar.normalization (reesProj (I.map f))))) :=
    normalizedReesProjToSpec_genericStalk_isIso (I.map f) b hb
  letI : IsIso (vY.stalkMap
      (genericPoint (Palomar.normalization (reesProj I)))) :=
    normalizedReesProjToSpec_genericStalk_isIso I a ha
  exact primeToPMonodromy_of_genericBirationalSquare p F G vX vY
    (normalizedReesProjToSpec_comm f hf hfin I a ha) hmono

#print axioms normalizedReesProjMap_primeToPMonodromy
#print axioms normalizedReesProjMap_isDominant

end

end Pcf.Bounding.AllCodimBlowup
