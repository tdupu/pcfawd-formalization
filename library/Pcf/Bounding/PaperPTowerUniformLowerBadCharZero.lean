/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupExceptionalBadUnionCharZero
public import Pcf.Bounding.PaperPBlowupFiniteWUpperEtaCharZero
public import Pcf.Bounding.PaperPBlowupSourceClosureFinite
public import Pcf.Bounding.PaperPBlowupComponentSquare

/-!
# One finite bad set for every level of an affine tower chart (characteristic zero)

This is the affine heart of the last paragraph of the proof of
`paper-p.tex`, Theorem `thm:tower-restrict`, in characteristic zero. Fix a
normal affine chart `Spec R` of the base, an ideal `I` with a nonzero element,
and a sequence of finite normal affine covers with finite total branch image.
No monodromy hypothesis is needed in characteristic zero. Let `W` be the fixed finite family of
codimension-one points of the normalized Rees target (exceptional divisors and
lifted branch images). A single finite set `Bad` of points of `Spec R` works
simultaneously for every level `n` and every exceptional source divisor `x`:

* the exceptional corrections of `prop:bound-blowup`
  (`exists_finite_ambient_bad_for_all_exceptional_Rees_squares_charZero`), together with
* the images of the fixed bounding corrections `Σ(W, B)` of `thm:bounding`
  (`NormalAffineFiniteCover.upperEtale_of_fixedW_charZero`) over the finitely many
  exceptional divisors `B` that occur.

Outside `Bad`, no divisor of the lower closure is a weighted branch point of
the lower point-closure map.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 1600000 in
/-- **Uniform lower branch bound on an affine chart, characteristic zero.** -/
theorem NormalAffineFiniteCover.exists_uniform_lower_branch_bad_charZero
    (k : Type u) [Field k] [CharZero k]
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (C : ℕ → NormalAffineFiniteCover R)
    (hpcf : (⋃ n, schemeDivisorBranchImage (C n).specMap).Finite) :
    ∃ Bad : Set (Spec (.of R)), Bad.Finite ∧
      ∀ (n : ℕ)
        (x : (let Cn := C n
          let b : I.map Cn.f := mappedCenterElement Cn.f I a
          let hb : (b : Cn.S) ≠ 0 := mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
          letI : IsIntegral (reesProj (I.map Cn.f)) :=
            reesProj_isIntegral (I.map Cn.f) b hb
          SchemeDivisorPoint (Palomar.normalization (reesProj (I.map Cn.f))))),
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let Cn := C n
      let b : I.map Cn.f := mappedCenterElement Cn.f I a
      let hb : (b : Cn.S) ≠ 0 := mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
      letI : IsIntegral (reesProj (I.map Cn.f)) :=
        reesProj_isIntegral (I.map Cn.f) b hb
      let F := normalizedReesProjMap Cn.f Cn.injective Cn.finite I a ha
      F x.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support →
      let α := normalizedReesProjToSpec (I.map Cn.f) b hb
      let β := normalizedReesProjToSpec I a ha
      let φ := Spec.map (CommRingCat.ofHom Cn.f)
      letI : IsFinite φ := affineSpecMap_isFinite Cn.f Cn.finite
      letI : IsDominant φ := affineSpecMap_isDominant Cn.f Cn.injective
      let hbase : φ (α x.1) = β (F x.1) := by
        have h := congrArg (fun m => m x.1)
          (normalizedReesProjToSpec_comm Cn.f Cn.injective Cn.finite I a ha)
        simpa only [Scheme.Hom.comp_apply] using h.symm
      let W₀ := (pointClosureIdealSheaf (α x.1)).subscheme
      let Z₀ := (pointClosureIdealSheaf (β (F x.1))).subscheme
      let g := pointClosureSubschemeMap φ (α x.1) (β (F x.1)) hbase
      let hSource := normalizedRees_source_pointClosures_finiteNormalization
        k Cn.f Cn.injective Cn.finite I hI a ha x.1
      letI : IsLocallyNoetherian W₀ := hSource.2.1
      letI : IsFinite (Palomar.normalizationMap W₀) := hSource.2.2.2
      let sR : Spec (.of R) ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k R))
      letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
      letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
      letI : IsLocallyNoetherian Z₀ := inferInstance
      letI : LocallyOfFiniteType
          ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR) := by
        letI : LocallyOfFiniteType sR := by
          rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
          exact RingHom.finiteType_algebraMap.mpr inferInstance
        infer_instance
      letI : IsFinite (Palomar.normalizationMap Z₀) :=
        schemeGlobalNormalizationMap_isFinite Z₀ k
          ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR)
      letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
      letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
      ∀ D : SchemeDivisorPoint Z₀,
        (pointClosureIdealSheaf (β (F x.1))).subschemeι D.1 ∉ Bad →
        D.1 ∉ weightedBranchPointSet g := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let Y' := Palomar.normalization (reesProj I)
  let β := normalizedReesProjToSpec I a ha
  let Wset := normalizedReesTowerW I a ha C
  obtain ⟨Bad₁, hBad₁, hspec⟩ :=
    exists_finite_ambient_bad_for_all_exceptional_Rees_squares_charZero k I hI a ha
  -- the exceptional divisors which actually occur as images of source divisors
  let Exc : Set (SchemeDivisorPoint Y') :=
    {B | B.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support ∧
      ∃ n, ∃ x : (let Cn := C n
          let b : I.map Cn.f := mappedCenterElement Cn.f I a
          let hb : (b : Cn.S) ≠ 0 := mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
          letI : IsIntegral (reesProj (I.map Cn.f)) :=
            reesProj_isIntegral (I.map Cn.f) b hb
          SchemeDivisorPoint (Palomar.normalization (reesProj (I.map Cn.f)))),
        normalizedReesProjMap (C n).f (C n).injective (C n).finite I a ha x.1 = B.1}
  have hExc : Exc.Finite :=
    (normalizedReesExceptional_divisorPoints_finite k I hI a ha).subset
      (fun B hB => hB.1)
  let Bad₂ : Set (Spec (.of R)) :=
    ⋃ B ∈ Exc, (fun D' : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme =>
      β ((pointClosureIdealSheaf B.1).subschemeι D'.1)) ''
        {D' | D'.1 ∈ Pcf.paperPBoundingFixedSigma Wset B}
  have hBad₂ : Bad₂.Finite := by
    refine Set.Finite.biUnion hExc ?_
    rintro B ⟨-, n, x, hx⟩
    apply Set.Finite.image
    have hup := NormalAffineFiniteCover.upperEtale_of_fixedW_charZero k I hI a ha
      C hpcf n x
    rcases B with ⟨B1, hB1⟩
    dsimp only at hx
    subst hx
    exact hup.1
  refine ⟨Bad₁ ∪ Bad₂, hBad₁.union hBad₂, ?_⟩
  intro n x
  dsimp only
  intro hexc
  let Cn := C n
  let b : I.map Cn.f := mappedCenterElement Cn.f I a
  have hb : (b : Cn.S) ≠ 0 := mappedCenterElement_ne_zero Cn.f Cn.injective I a ha
  letI : IsIntegral (reesProj (I.map Cn.f)) := reesProj_isIntegral (I.map Cn.f) b hb
  let F := normalizedReesProjMap Cn.f Cn.injective Cn.finite I a ha
  let α := normalizedReesProjToSpec (I.map Cn.f) b hb
  let φ := Spec.map (CommRingCat.ofHom Cn.f)
  have hbase : φ (α x.1) = β (F x.1) := by
    have h := congrArg (fun m => m x.1)
      (normalizedReesProjToSpec_comm Cn.f Cn.injective Cn.finite I a ha)
    simpa only [Scheme.Hom.comp_apply] using h.symm
  let X₀ := (pointClosureIdealSheaf x.1).subscheme
  let W₀ := (pointClosureIdealSheaf (α x.1)).subscheme
  let Z₀ := (pointClosureIdealSheaf (β (F x.1))).subscheme
  let u := pointClosureSubschemeMap F x.1 (F x.1) rfl
  let v := pointClosureSubschemeMap α x.1 (α x.1) rfl
  let q := pointClosureSubschemeMap β (F x.1) (β (F x.1)) rfl
  let g := pointClosureSubschemeMap φ (α x.1) (β (F x.1)) hbase
  letI : Algebra k Cn.S := (Cn.f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k Cn.S :=
    RingHom.finiteType_algebraMap.mp
      (Cn.finite.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance))
  letI : IsFinite F := normalizedReesProjMap_isFinite k Cn.f Cn.injective Cn.finite I hI a ha
  letI : IsDominant F := normalizedReesProjMap_isDominant Cn.f Cn.injective Cn.finite I a ha
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) I) :=
    reesProjToSpecField_locallyOfFiniteType k I hI
  letI : IsLocallyNoetherian (reesProj I) :=
    LocallyOfFiniteType.isLocallyNoetherian (reesProjToSpecField (k := k) I)
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsLocallyNoetherian Y' := inferInstance
  let dY : SchemeDivisorPoint Y' := x.mapFiniteDominantNormal F
  let hSource := normalizedRees_source_pointClosures_finiteNormalization
    k Cn.f Cn.injective Cn.finite I hI a ha x.1
  letI : IsLocallyNoetherian X₀ := hSource.1
  letI : IsLocallyNoetherian W₀ := hSource.2.1
  letI : IsFinite (Palomar.normalizationMap X₀) := hSource.2.2.1
  letI : IsFinite (Palomar.normalizationMap W₀) := hSource.2.2.2
  letI : IsFinite u := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsDominant u := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsProper (reesProjToSpec (I.map Cn.f)) :=
    reesProjToSpec_isProper (I.map Cn.f) (Ideal.FG.map hI Cn.f)
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map Cn.f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map Cn.f)
      (Ideal.FG.map hI Cn.f) b hb
  letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
  letI : IsProper v := pointClosureSubschemeMap_isProper _ _ _ _
  letI : IsDominant v := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsFinite φ := affineSpecMap_isFinite Cn.f Cn.finite
  letI : IsDominant φ := affineSpecMap_isDominant Cn.f Cn.injective
  letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
  letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : IsLocallyNoetherian (Spec (.of R)) := inferInstance
  letI : IsLocallyNoetherian Z₀ := inferInstance
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  letI : LocallyOfFiniteType
      ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR) := inferInstance
  letI : IsFinite (Palomar.normalizationMap Z₀) :=
    schemeGlobalNormalizationMap_isFinite Z₀ k
      ((pointClosureIdealSheaf (β (F x.1))).subschemeι ≫ sR)
  let sS : Spec (.of Cn.S) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Cn.S))
  letI : LocallyOfFiniteType sS := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let sX : X₀ ⟶ Spec (.of k) :=
    (pointClosureIdealSheaf x.1).subschemeι ≫ α ≫ sS
  letI : LocallyOfFiniteType sX := inferInstance
  have hsq := normalizedReesProjMap_pointClosure_square Cn.f Cn.injective Cn.finite I a ha x.1
  have hup := NormalAffineFiniteCover.upperEtale_of_fixedW_charZero k I hI a ha
    C hpcf n x
  -- a structure map on the exceptional closure, for divisor transport
  let Y₀ := (pointClosureIdealSheaf (F x.1)).subscheme
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper β := by dsimp only [β, normalizedReesProjToSpec]; infer_instance
  let sY₀ : Y₀ ⟶ Spec (.of k) := (pointClosureIdealSheaf (F x.1)).subschemeι ≫ β ≫ sR
  letI : LocallyOfFiniteType sY₀ := inferInstance
  intro D hD hbranch
  have hD₁ : (pointClosureIdealSheaf (β (F x.1))).subschemeι D.1 ∉ Bad₁ :=
    fun h => hD (Or.inl h)
  have hboundY := hspec dY hexc (X := X₀) (W := W₀)
  dsimp only [dY, SchemeDivisorPoint.mapFiniteDominantNormal] at hboundY
  refine hboundY sX u v g hsq D hD₁ ?_ hbranch
  intro E hE
  have hEcoh : Order.coheight (u E.1) = 1 :=
    coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k sY₀ u E
  let D' : SchemeDivisorPoint Y₀ := ⟨u E.1, hEcoh⟩
  apply hup.2 D' _ E rfl
  intro hSig
  apply hD
  refine Or.inr ?_
  refine Set.mem_biUnion (x := dY) ⟨hexc, n, x, rfl⟩ ⟨D', hSig, ?_⟩
  have h1 := congrArg (fun m => m (u E.1))
    (pointClosureSubschemeMap_subschemeι β (F x.1) (β (F x.1)) rfl)
  simp only [Scheme.Hom.comp_apply] at h1
  change β ((pointClosureIdealSheaf (F x.1)).subschemeι (u E.1)) =
    (pointClosureIdealSheaf (β (F x.1))).subschemeι D.1
  rw [← h1, ← hE]
  rfl

#print axioms NormalAffineFiniteCover.exists_uniform_lower_branch_bad_charZero

end
end Pcf.Bounding.AllCodimBlowup
