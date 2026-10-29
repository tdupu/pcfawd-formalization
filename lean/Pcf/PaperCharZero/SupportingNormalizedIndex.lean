/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingDictionary
public import Pcf.Bounding.GlobalNormalizationMorphism

/-!
# Étale restriction and every normalized ramification branch

`paper.tex`, Lemma `lem:etale-normalized-index`. A two-scheme form of the
existing local birational-square argument supplies the actual normalization
comparison. Its stronger core does not need regularity of the downstairs
target: downstairs unramifiedness already forces the normalized index to one.
The final source-facing theorem retains the manuscript's regularity and
characteristic-zero hypotheses and quantifies over every divisor upstairs.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Pcf.PaperCharZero

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- For a commuting square of actual scheme maps, downstairs unramifiedness
forces index one upstairs when the source vertical map is birational and the
upper target is normal. This generalizes the existing endomorphism wrapper
to distinct source and target schemes; the local algebra theorem is reused. -/
theorem ramificationIdx_eq_one_of_birational_square
    {X Y NX NY : Scheme.{u}} (f : X ⟶ Y) (fN : NX ⟶ NY)
    (νX : NX ⟶ X) (νY : NY ⟶ Y)
    [LocallyOfFiniteType f] [IsFinite fN] [IsDominant fN]
    [IsIntegral NX] [IsIntegral NY] [IsLocallyNoetherian NY] [IsNormalScheme NY]
    (hsquare : fN ≫ νY = νX ≫ f) (Q : SchemeDivisorPoint NX)
    (hbirational : IsStalkBirationalAt νX Q.1)
    (hunramified : (f.stalkMap (νX Q.1)).hom.FormallyUnramified) :
    schemeDivisorRamificationIdx fN Q = 1 := by
  let R₀ := Y.presheaf.stalk (f (νX Q.1))
  let B := X.presheaf.stalk (νX Q.1)
  let R := NY.presheaf.stalk (fN Q.1)
  let S := NX.presheaf.stalk Q.1
  let K := NX.functionField
  have hpoint : f (νX Q.1) = νY (fN Q.1) :=
    congrArg (fun h : NX ⟶ Y => h Q.1) hsquare.symm
  let v : R₀ →+* R :=
    ((Y.presheaf.stalkCongr (.of_eq hpoint)).hom ≫ νY.stalkMap (fN Q.1)).hom
  letI : Algebra R₀ B := (f.stalkMap (νX Q.1)).hom.toAlgebra
  letI : Algebra B S := (νX.stalkMap Q.1).hom.toAlgebra
  letI : Algebra R S := (fN.stalkMap Q.1).hom.toAlgebra
  letI : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (fN.stalkMap Q.1).hom)
  letI : Algebra R₀ R := v.toAlgebra
  letI : Algebra R₀ S :=
    ((νX.stalkMap Q.1).hom.comp (f.stalkMap (νX Q.1)).hom).toAlgebra
  letI : IsScalarTower R₀ B S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' (by
    change ((f.stalkMap (νX Q.1)) ≫ νX.stalkMap Q.1).hom =
      ((fN.stalkMap Q.1).hom.comp v)
    have h := Scheme.Hom.stalkMap_congr_hom (νX ≫ f) (fN ≫ νY) hsquare.symm Q.1
    simp only [Scheme.Hom.stalkMap_comp] at h
    exact congrArg CommRingCat.Hom.hom h)
  letI : Algebra B K := ((algebraMap S K).comp (algebraMap B S)).toAlgebra
  letI : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing B K := hbirational
  letI : IsDiscreteValuationRing R :=
    (Q.mapFiniteDominantNormal fN).stalk_isDiscreteValuationRing
  letI : Algebra.EssFiniteType R₀ B := LocallyOfFiniteType.stalkMap f (νX Q.1)
  letI : Algebra.FormallyUnramified R₀ B := hunramified
  exact ramificationIdx_eq_one_of_local_birational_square R₀ B R S K (maximalIdeal S)

/-- For the canonical normalizations, every divisor above an étale downstairs
divisor has normalized ramification index one. All normalization finiteness,
normality, and birationality facts are constructed from the actual geometry.
This stronger form works over any field without downstairs regularity. -/
theorem normalized_index_eq_one_of_etale
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (P : SchemeDivisorPoint X)
    (hetale : ∃ U : X.Opens, P.1 ∈ U ∧ Etale (U.ι ≫ f)) :
    ∀ Q : SchemeDivisorPoint (Palomar.normalization X),
      Palomar.normalizationMap X Q.1 = P.1 →
        schemeDivisorRamificationIdx (schemeGlobalNormalizationMorphism f) Q = 1 := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsFinite (Palomar.normalizationMap Y) := schemeGlobalNormalizationMap_isFinite Y k s
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k (f ≫ s)
  have hformal := (formallyEtale_stalkMap_iff_etale_neighborhood f P.1).mpr hetale
  intro Q hQ
  apply ramificationIdx_eq_one_of_birational_square f
    (schemeGlobalNormalizationMorphism f) (Palomar.normalizationMap X)
    (Palomar.normalizationMap Y) (schemeGlobalNormalizationMorphism_comp f) Q
    (schemeGlobalNormalizationMap_stalkBirationalAt X Q.1)
  rw [hQ]
  letI := (f.stalkMap P.1).hom.toAlgebra
  letI : Algebra.FormallyEtale (Y.presheaf.stalk (f P.1)) (X.presheaf.stalk P.1) := hformal
  exact inferInstanceAs (Algebra.FormallyUnramified _ _)

/-- `lem:etale-normalized-index`, with the universal quantifier over all
normalization branches over the specified source divisor. The regularity
assumption is retained verbatim; the preceding stronger theorem shows it is
unnecessary for this index-one conclusion. -/
theorem etale_normalized_index
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (P : SchemeDivisorPoint X)
    (_hregular : IsRegularLocalRing (Y.presheaf.stalk (f P.1)))
    (hetale : ∃ U : X.Opens, P.1 ∈ U ∧ Etale (U.ι ≫ f)) :
    ∀ Q : SchemeDivisorPoint (Palomar.normalization X),
      Palomar.normalizationMap X Q.1 = P.1 →
        schemeDivisorRamificationIdx (schemeGlobalNormalizationMorphism f) Q = 1 :=
  normalized_index_eq_one_of_etale k s f P hetale

end Pcf.PaperCharZero
