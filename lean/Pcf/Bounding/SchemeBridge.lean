/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.LocalChart
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.RingHomProperties

/-!
# Identifying the bounding chart with an actual scheme stalk map

The old chart link A6 contained an implication from membership in the abstract `crit₁`
set to non-étaleness of a quotient chart.  Relative to the chart theorem that implication
was as strong as the desired conclusion.

This file replaces that implication at the geometric level.  Failure of formal étaleness
is defined directly from the actual stalk map of a scheme morphism.  The dynamics-facing
`SchemeStalkBoundingLocalizationPresentation` records quotient-ring algebra maps,
localization universal properties, and their square; Lean constructs the two coordinate
isomorphisms and the corresponding arrow isomorphism.  The
alternative open-neighbourhood interfaces `SchemeLocalBoundingPresentation` and
`SchemeAffineLocalBoundingPresentation` do the analogous job when the whole restriction
has affine quotient coordinates.  All routes derive formal étaleness and exclusion
from the critical locus.  None contains the non-étaleness implication or the bounding
conclusion it is used to prove. For actual closed subschemes, the canonical affine
section quotients are proved to localize to the actual stalks, and
`closedSubschemeStalkBoundingLocalizationPresentation` constructs the entire
dynamics-facing stalk presentation from section-level quotient coordinates.  When the
closed-subscheme morphism is induced by an actual ambient morphism,
`closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap` derives the quotient
map and its square functorially, leaving only the two equalities of defining ideals.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option linter.style.haveILetI false

/-- A morphism that is surjective on stalks identifies each source stalk with the
corresponding target stalk modulo the kernel of the stalk map.

For a closed immersion, Mathlib supplies `SurjectiveOnStalks`; the geometric part of a
quotient-stalk comparison is therefore reduced to identifying this kernel with the stalk
of the defining ideal sheaf. -/
noncomputable def Scheme.Hom.stalkQuotientKerEquiv
    {X Y : Scheme.{u}} (i : X ⟶ Y) [SurjectiveOnStalks i] (x : X) :
    ((Arrow.mk (i.stalkMap x)).left ⧸ RingHom.ker (i.stalkMap x).hom) ≃+*
      (Arrow.mk (i.stalkMap x)).right :=
  RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective x)

@[simp]
theorem Scheme.Hom.stalkQuotientKerEquiv_mk
    {X Y : Scheme.{u}} (i : X ⟶ Y) [SurjectiveOnStalks i] (x : X)
    (r : (Arrow.mk (i.stalkMap x)).left) :
    i.stalkQuotientKerEquiv x (Ideal.Quotient.mk _ r) = i.stalkMap x r :=
  RingHom.quotientKerEquivOfSurjective_apply_mk (i.stalkMap_surjective x) r

/-- The prime of an affine closed-subscheme chart corresponding to a point of the
subscheme.

Mathlib presents the inverse image of an affine open `U` in the closed subscheme as
`Spec (Γ(X, U) / I(U))`.  This is the prime of that quotient ring obtained from the
point under the canonical presentation. -/
noncomputable def Scheme.IdealSheafData.quotientPoint
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens)) :
    PrimeSpectrum (Γ(X, U) ⧸ I.ideal U) := by
  let W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ (U : X.Opens)
  let hW : IsAffineOpen W := by
    letI : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    dsimp only [W]
    rw [← I.opensRange_subschemeCover_map U]
    exact isAffineOpen_opensRange (I.subschemeCover.f U)
  exact PrimeSpectrum.comap (I.subschemeObjIso U).inv.hom
    (hW.primeIdealOf ⟨x, hx⟩)

/-- The canonical algebra structure of a closed-subscheme stalk over the quotient of
sections on an ambient affine open. -/
@[instance_reducible]
noncomputable def Scheme.IdealSheafData.quotientStalkAlgebra
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens)) :
    Algebra (Γ(X, U) ⧸ I.ideal U) (I.subscheme.presheaf.stalk x) :=
  ((I.subscheme.presheaf.germ
      (I.subschemeι ⁻¹ᵁ (U : X.Opens)) x hx).hom.comp
    (I.subschemeObjIso U).inv.hom).toAlgebra

/-- A stalk of a closed subscheme over an ambient affine open is the localization of
the quotient of sections by the ideal-sheaf sections at the corresponding prime.

This packages the quotient--stalk localization input required by the geometric bridge;
it is derived from Mathlib's affine cover of the closed subscheme, not assumed. -/
theorem Scheme.IdealSheafData.quotientStalk_isLocalization
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens)) :
    letI : Algebra (Γ(X, U) ⧸ I.ideal U) (I.subscheme.presheaf.stalk x) :=
      I.quotientStalkAlgebra U x hx
    IsLocalization.AtPrime (I.subscheme.presheaf.stalk x)
      (I.quotientPoint U x hx).asIdeal := by
  let W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ (U : X.Opens)
  let hW : IsAffineOpen W := by
    letI : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    dsimp only [W]
    rw [← I.opensRange_subschemeCover_map U]
    exact isAffineOpen_opensRange (I.subschemeCover.f U)
  let P := (hW.primeIdealOf ⟨x, hx⟩).asIdeal
  let e : (Γ(X, U) ⧸ I.ideal U) ≃+* Γ(I.subscheme, W) :=
    (I.subschemeObjIso U).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(I.subscheme, W) (I.subscheme.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk I.subscheme.presheaf ⟨x, hx⟩
  haveI hloc : IsLocalization.AtPrime (I.subscheme.presheaf.stalk x) P :=
    hW.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra (Γ(X, U) ⧸ I.ideal U) (I.subscheme.presheaf.stalk x) :=
    I.quotientStalkAlgebra U x hx
  change IsLocalization ((P.comap e).primeCompl) (I.subscheme.presheaf.stalk x)
  apply IsLocalization.of_ringEquiv_left e (e.map_primeCompl_comap_eq P)
  intro r
  rfl

/-- The map on the affine quotient charts of two closed subschemes induced by a scheme
morphism between them. -/
noncomputable def Scheme.IdealSheafData.quotientAppLE
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (g : I.subscheme ⟶ J.subscheme) (U : Y.affineOpens) (V : X.affineOpens)
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      g ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens))) :
    (Γ(Y, U) ⧸ J.ideal U) →+* (Γ(X, V) ⧸ I.ideal V) :=
  ((J.subschemeObjIso U).inv ≫
    g.appLE (J.subschemeι ⁻¹ᵁ (U : Y.Opens))
      (I.subschemeι ⁻¹ᵁ (V : X.Opens)) map_le ≫
    (I.subschemeObjIso V).hom).hom

/-- The actual stalk map of a morphism between closed subschemes commutes with the
canonical quotient maps on affine ambient charts.

This is the `stalkMap_algebraMap` field of the geometric bridge for canonical closed-
subscheme coordinates; it follows from functoriality of germs. -/
theorem Scheme.IdealSheafData.stalkMap_comp_quotientStalkAlgebraMap
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (g : I.subscheme ⟶ J.subscheme) (U : Y.affineOpens) (V : X.affineOpens)
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      g ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens)))
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens)) :
    letI : Algebra (Γ(Y, U) ⧸ J.ideal U) (J.subscheme.presheaf.stalk (g x)) :=
      J.quotientStalkAlgebra U (g x) hy
    letI : Algebra (Γ(X, V) ⧸ I.ideal V) (I.subscheme.presheaf.stalk x) :=
      I.quotientStalkAlgebra V x hx
    (g.stalkMap x).hom.comp
        (algebraMap (Γ(Y, U) ⧸ J.ideal U) (J.subscheme.presheaf.stalk (g x))) =
      (algebraMap (Γ(X, V) ⧸ I.ideal V) (I.subscheme.presheaf.stalk x)).comp
        (J.quotientAppLE I g U V map_le) := by
  letI : Algebra (Γ(Y, U) ⧸ J.ideal U) (J.subscheme.presheaf.stalk (g x)) :=
    J.quotientStalkAlgebra U (g x) hy
  letI : Algebra (Γ(X, V) ⧸ I.ideal V) (I.subscheme.presheaf.stalk x) :=
    I.quotientStalkAlgebra V x hx
  have hcat :
      (J.subschemeObjIso U).inv ≫
          J.subscheme.presheaf.germ
            (J.subschemeι ⁻¹ᵁ (U : Y.Opens)) (g x) hy ≫
          g.stalkMap x =
        (J.subschemeObjIso U).inv ≫
          g.appLE (J.subschemeι ⁻¹ᵁ (U : Y.Opens))
            (I.subschemeι ⁻¹ᵁ (V : X.Opens)) map_le ≫
          (I.subschemeObjIso V).hom ≫ (I.subschemeObjIso V).inv ≫
          I.subscheme.presheaf.germ
            (I.subschemeι ⁻¹ᵁ (V : X.Opens)) x hx := by
    simp only [Iso.hom_inv_id_assoc]
    rw [g.germ_stalkMap]
    simp only [Scheme.Hom.appLE]
    rw [Category.assoc, I.subscheme.presheaf.germ_res]
  have hr := congrArg CommRingCat.Hom.hom hcat
  simpa only [RingHom.algebraMap_toAlgebra, quotientStalkAlgebra,
    quotientAppLE, CommRingCat.hom_comp, RingHom.comp_assoc,
    Iso.inv_hom_id_assoc] using hr

/-- The point of the target quotient chart is the contraction of the point of the
source quotient chart under `quotientAppLE`. -/
theorem Scheme.IdealSheafData.comap_quotientPoint_quotientAppLE
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (g : I.subscheme ⟶ J.subscheme) (U : Y.affineOpens) (V : X.affineOpens)
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      g ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens)))
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens)) :
    PrimeSpectrum.comap (J.quotientAppLE I g U V map_le)
        (I.quotientPoint V x hx) =
      J.quotientPoint U (g x) hy := by
  let WI : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ (V : X.Opens)
  let WJ : J.subscheme.Opens := J.subschemeι ⁻¹ᵁ (U : Y.Opens)
  let hWI : IsAffineOpen WI := by
    letI : IsOpenImmersion (I.subschemeCover.f V) := I.subschemeCover.map_prop V
    dsimp only [WI]
    rw [← I.opensRange_subschemeCover_map V]
    exact isAffineOpen_opensRange (I.subschemeCover.f V)
  let hWJ : IsAffineOpen WJ := by
    letI : IsOpenImmersion (J.subschemeCover.f U) := J.subschemeCover.map_prop U
    dsimp only [WJ]
    rw [← J.opensRange_subschemeCover_map U]
    exact isAffineOpen_opensRange (J.subschemeCover.f U)
  apply PrimeSpectrum.ext
  change
    ((hWI.primeIdealOf ⟨x, hx⟩).asIdeal.comap
      (I.subschemeObjIso V).inv.hom).comap
        (J.quotientAppLE I g U V map_le) =
      (hWJ.primeIdealOf ⟨g x, hy⟩).asIdeal.comap
        (J.subschemeObjIso U).inv.hom
  rw [Ideal.comap_comap]
  simp only [quotientAppLE, CommRingCat.hom_comp, RingHom.comp_assoc]
  have he :
      (I.subschemeObjIso V).inv.hom.comp (I.subschemeObjIso V).hom.hom =
        RingHom.id Γ(I.subscheme, WI) := by
    exact congrArg CommRingCat.Hom.hom (Iso.hom_inv_id (I.subschemeObjIso V))
  rw [← RingHom.comp_assoc, he, RingHom.id_comp]
  rw [← Ideal.comap_comap]
  have hp := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE WJ hWJ WI hWI map_le hx)
  change
    (hWI.primeIdealOf ⟨x, hx⟩).asIdeal.comap
        (g.appLE WJ WI map_le).hom =
      (hWJ.primeIdealOf ⟨g x, hy⟩).asIdeal at hp
  rw [hp]

set_option backward.isDefEq.respectTransparency false in
/-- The actual stalk arrow of a morphism between closed subschemes is canonically
isomorphic to the stalk arrow of the induced morphism between its affine quotient
charts.

Both sides use the same quotient-ring map. The comparison is derived from the fact that
the two actual stalks and the two affine-scheme stalks are localizations at the same
contracted primes, together with functoriality of germs. In particular, the arrow
isomorphism is not an extra chart assumption. -/
noncomputable def Scheme.IdealSheafData.stalkMapArrowIsoQuotientAppLE
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (g : I.subscheme ⟶ J.subscheme) (U : Y.affineOpens) (V : X.affineOpens)
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      g ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens)))
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens)) :
    let fAB := J.quotientAppLE I g U V map_le
    let sourcePoint := I.quotientPoint V x hx
    Arrow.mk (g.stalkMap x) ≅
      Arrow.mk ((Spec.map (CommRingCat.ofHom fAB)).stalkMap sourcePoint) := by
  let A := Γ(Y, U) ⧸ J.ideal U
  let B := Γ(X, V) ⧸ I.ideal V
  let fAB : A →+* B := J.quotientAppLE I g U V map_le
  let sourcePoint : PrimeSpectrum B := I.quotientPoint V x hx
  let targetPoint : PrimeSpectrum A := J.quotientPoint U (g x) hy
  let target := PrimeSpectrum.comap fAB sourcePoint
  have htarget : target = targetPoint :=
    J.comap_quotientPoint_quotientAppLE I g U V map_le x hx hy
  letI : Algebra A (J.subscheme.presheaf.stalk (g x)) :=
    J.quotientStalkAlgebra U (g x) hy
  letI : Algebra B (I.subscheme.presheaf.stalk x) :=
    I.quotientStalkAlgebra V x hx
  haveI hTargetLoc0 : IsLocalization.AtPrime
      (J.subscheme.presheaf.stalk (g x)) targetPoint.asIdeal :=
    J.quotientStalk_isLocalization U (g x) hy
  haveI hTargetLoc : IsLocalization.AtPrime
      (J.subscheme.presheaf.stalk (g x)) target.asIdeal := by
    rw [htarget]
    exact hTargetLoc0
  haveI hSourceLoc : IsLocalization.AtPrime
      (I.subscheme.presheaf.stalk x) sourcePoint.asIdeal :=
    I.quotientStalk_isLocalization V x hx
  let localHom := Localization.localRingHom target.asIdeal sourcePoint.asIdeal fAB rfl
  let eBase : Localization.AtPrime target.asIdeal ≃ₐ[A]
      J.subscheme.presheaf.stalk (g x) :=
    IsLocalization.algEquiv target.asIdeal.primeCompl _ _
  let eCover : Localization.AtPrime sourcePoint.asIdeal ≃ₐ[B]
      I.subscheme.presheaf.stalk x :=
    IsLocalization.algEquiv sourcePoint.asIdeal.primeCompl _ _
  let eLocalActual : Arrow.mk (CommRingCat.ofHom localHom) ≅
      Arrow.mk (g.stalkMap x) := by
    refine Arrow.isoMk eBase.toRingEquiv.toCommRingCatIso
      eCover.toRingEquiv.toCommRingCatIso ?_
    apply CommRingCat.hom_ext
    change (g.stalkMap x).hom.comp eBase.toRingEquiv.toRingHom =
      eCover.toRingEquiv.toRingHom.comp localHom
    apply IsLocalization.ringHom_ext target.asIdeal.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    change
      (g.stalkMap x).hom
          (eBase (algebraMap A (Localization.AtPrime target.asIdeal)
            (Ideal.Quotient.mk (J.ideal U) r))) =
        eCover (localHom (algebraMap A (Localization.AtPrime target.asIdeal)
          (Ideal.Quotient.mk (J.ideal U) r)))
    rw [eBase.commutes]
    rw [Localization.localRingHom_to_map target.asIdeal sourcePoint.asIdeal fAB rfl
      (Ideal.Quotient.mk (J.ideal U) r)]
    rw [eCover.commutes]
    exact DFunLike.congr_fun
      (J.stalkMap_comp_quotientStalkAlgebraMap I g U V map_le x hx hy)
      (Ideal.Quotient.mk (J.ideal U) r)
  exact eLocalActual.symm.trans
    (AlgebraicGeometry.Scheme.arrowStalkMapSpecIso
      (CommRingCat.ofHom fAB) sourcePoint).symm

/-- An inclusion of ambient opens pulls back to the corresponding inclusion on closed
subschemes under the morphism induced by an inclusion of ideal sheaves. -/
theorem Scheme.IdealSheafData.subschemeMap_preimage_le
    {Y X : Scheme.{u}} (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    I.subschemeι ⁻¹ᵁ V ≤
      I.subschemeMap J f H ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ U) := by
  have h' := I.subschemeι.preimage_mono h
  simpa only [← Scheme.Hom.comp_preimage,
    I.subschemeMap_subschemeι J f H] using h'

/-- On affine ambient opens, the quotient-chart map induced by `subschemeMap` commutes
with the two canonical quotient maps and the ambient map on sections. -/
theorem Scheme.IdealSheafData.quotientAppLE_comp_mk_subschemeMap
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f)
    (U : Y.affineOpens) (V : X.affineOpens)
    (ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      I.subschemeMap J f H ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens))) :
    (J.quotientAppLE I (I.subschemeMap J f H) U V map_le).comp
        (Ideal.Quotient.mk (J.ideal U)) =
      (Ideal.Quotient.mk (I.ideal V)).comp
        (f.appLE U V ambient_map_le).hom := by
  let WJ : J.subscheme.Opens := J.subschemeι ⁻¹ᵁ (U : Y.Opens)
  let WI : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ (V : X.Opens)
  have hsections :
      J.subschemeι.app U ≫ (I.subschemeMap J f H).appLE WJ WI map_le =
        f.appLE U V ambient_map_le ≫ I.subschemeι.app V := by
    rw [J.subschemeι.app_eq_appLE]
    rw [Scheme.Hom.appLE_comp_appLE]
    rw [I.subschemeι.app_eq_appLE]
    rw [Scheme.Hom.appLE_comp_appLE]
    simp only [I.subschemeMap_subschemeι J f H]
    rfl
  have hquot :
      CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫
            (J.subschemeObjIso U).inv ≫
            (I.subschemeMap J f H).appLE WJ WI map_le ≫
            (I.subschemeObjIso V).hom =
        f.appLE U V ambient_map_le ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal V)) := by
    calc
      _ = (J.subschemeι.app U ≫
          (I.subschemeMap J f H).appLE WJ WI map_le) ≫
          (I.subschemeObjIso V).hom := by
            rw [J.subschemeι_app U]
            simp only [Category.assoc]
      _ = (f.appLE U V ambient_map_le ≫ I.subschemeι.app V) ≫
          (I.subschemeObjIso V).hom := by rw [hsections]
      _ = _ := by
        rw [I.subschemeι_app V]
        simp
  exact congrArg CommRingCat.Hom.hom hquot

/-- The ambient map on affine sections sends the target defining ideal into the source
defining ideal.  This is derived from the actual induced map of closed subschemes. -/
theorem Scheme.IdealSheafData.subschemeMap_ideal_le
    {Y X : Scheme.{u}} (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f)
    (U : Y.affineOpens) (V : X.affineOpens)
    (ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    J.ideal U ≤ (I.ideal V).comap (f.appLE U V ambient_map_le).hom := by
  intro r hr
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  have hq := J.quotientAppLE_comp_mk_subschemeMap I f H U V ambient_map_le
    (I.subschemeMap_preimage_le J f H U V ambient_map_le)
  have hqr := DFunLike.congr_fun hq r
  simp only [RingHom.comp_apply] at hqr
  rw [← hqr, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- The map on canonical affine quotient charts induced by `subschemeMap` is the
ordinary quotient of the ambient map on sections. -/
theorem Scheme.IdealSheafData.quotientAppLE_subschemeMap_eq_quotientMap
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f)
    (U : Y.affineOpens) (V : X.affineOpens)
    (ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) :
    J.quotientAppLE I (I.subschemeMap J f H) U V
        (I.subschemeMap_preimage_le J f H U V ambient_map_le) =
      Ideal.quotientMap (I.ideal V) (f.appLE U V ambient_map_le).hom
        (I.subschemeMap_ideal_le J f H U V ambient_map_le) := by
  apply Ideal.Quotient.ringHom_ext
  exact (J.quotientAppLE_comp_mk_subschemeMap I f H U V ambient_map_le
    (I.subschemeMap_preimage_le J f H U V ambient_map_le)).trans
      (Ideal.quotientMap_comp_mk
        (I.subschemeMap_ideal_le J f H U V ambient_map_le)).symm

end AlgebraicGeometry

namespace Pcf

set_option linter.style.haveILetI false

/-- A ring isomorphism is formally étale as a ring homomorphism. -/
theorem ringEquiv_formallyEtale {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) : e.toRingHom.FormallyEtale := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  rw [RingHom.FormallyEtale]
  let ae : R ≃ₐ[R] S := { e with commutes' := fun _ ↦ rfl }
  exact Algebra.FormallyEtale.of_equiv ae

/-- Formal étaleness is invariant under isomorphism of arrows in `CommRingCat`. -/
theorem formallyEtale_respectsIso : RingHom.RespectsIso @RingHom.FormallyEtale := by
  constructor
  · intro R S T _ _ _ f e hf
    exact hf.comp (ringEquiv_formallyEtale e)
  · intro R S T _ _ _ f e hf
    exact (ringEquiv_formallyEtale e).comp hf

/-- The local-ring map obtained by localizing an étale ring homomorphism at a prime is
formally étale.

This is the ring-theoretic input used below to pass from an étale morphism of schemes to
formal étaleness of its stalk maps. -/
theorem RingHom.Etale.localRingHom_formallyEtale
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (q : Ideal S) [q.IsPrime] :
    (Localization.localRingHom (q.comap f) q f rfl).FormallyEtale := by
  letI : Algebra R S := f.toAlgebra
  let q0 := q.under R
  letI : Algebra (Localization.AtPrime q0) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver q0 q
  haveI : IsScalarTower R (Localization.AtPrime q0) (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (Localization.localRingHom_to_map q0 q f rfl x).symm
  haveI : Algebra.FormallyEtale R S := hf.toAlgebra.formallyEtale
  have hglobal : Algebra.FormallyEtale R (Localization.AtPrime q) := inferInstance
  let _ : Algebra.FormallyEtale R (Localization.AtPrime q) := hglobal
  have hlocal : Algebra.FormallyEtale (Localization.AtPrime q0)
      (Localization.AtPrime q) :=
    Algebra.FormallyEtale.localization_base q0.primeCompl
  rw [RingHom.FormallyEtale]
  exact hlocal

/-- Every stalk map of an étale morphism of schemes is formally étale. -/
theorem AlgebraicGeometry.Etale.stalkMap_formallyEtale
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y}
    (hg : AlgebraicGeometry.Etale g) (x : X) :
    (g.stalkMap x).hom.FormallyEtale := by
  exact AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso
    formallyEtale_respectsIso
    (fun {R S} [CommRing R] [CommRing S] (f : R →+* S)
      (hf : RingHom.Etale f) q _ ↦
        RingHom.Etale.localRingHom_formallyEtale f hf q)
    hg x

/-- A local bounding chart identified with the actual stalk map of a scheme morphism.

The `stalkIso` field is structural: it is an isomorphism between two concrete ring maps.
It does not mention `crit₁`, non-étaleness, or the conclusion of the bounding theorem. -/
structure SchemeStalkBoundingChart {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (x : X) where
  R : Type u
  S : Type u
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [algebra : Algebra R S]
  a : R
  p : Ideal S
  xi : PrimeSpectrum (S ⧸ p)
  chart : LocalBoundingChart R S a p
  stalkIso : Arrow.mk (g.stalkMap x) ≅
    Arrow.mk (CommRingCat.ofHom (chart.restrictionLocalRingHom xi))

namespace SchemeStalkBoundingChart

/-- The actual stalk map is formally étale, derived from purity and Abhyankar on the
identified local chart. -/
theorem formallyEtale {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {x : X}
    (h : SchemeStalkBoundingChart g x) : (g.stalkMap x).hom.FormallyEtale := by
  letI : CommRing h.R := h.commRingR
  letI : CommRing h.S := h.commRingS
  letI : Algebra h.R h.S := h.algebra
  exact (formallyEtale_respectsIso.arrow_mk_iso_iff h.stalkIso).mpr
    (h.chart.formallyEtale_localRingHom h.xi)

end SchemeStalkBoundingChart

/-- Structural local-ring coordinates identifying an actual scheme stalk map with the
localized quotient map of a `LocalBoundingChart`.

Unlike `SchemeStalkBoundingChart`, this does not ask the caller to manufacture an
isomorphism in the arrow category.  It records the two concrete local-ring
identifications and their commutative square; the arrow isomorphism is constructed below.
These are the data naturally produced by quotient-stalk and finite-base-change
identifications in Step 0. -/
structure SchemeStalkBoundingPresentation {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (x : X) where
  R : Type u
  S : Type u
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [algebra : Algebra R S]
  a : R
  p : Ideal S
  xi : PrimeSpectrum (S ⧸ p)
  chart : LocalBoundingChart R S a p
  baseIso : (Arrow.mk (g.stalkMap x)).left ≅
    (Arrow.mk (CommRingCat.ofHom (chart.restrictionLocalRingHom xi))).left
  coverIso : (Arrow.mk (g.stalkMap x)).right ≅
    (Arrow.mk (CommRingCat.ofHom (chart.restrictionLocalRingHom xi))).right
  stalkMap_comm : baseIso.hom ≫
      CommRingCat.ofHom (chart.restrictionLocalRingHom xi) =
    g.stalkMap x ≫ coverIso.hom

namespace SchemeStalkBoundingPresentation

/-- The two local-ring coordinates and their square construct the required arrow
isomorphism. -/
noncomputable def toSchemeStalkBoundingChart
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {x : X}
    (h : SchemeStalkBoundingPresentation g x) :
    SchemeStalkBoundingChart g x := by
  letI : CommRing h.R := h.commRingR
  letI : CommRing h.S := h.commRingS
  letI : Algebra h.R h.S := h.algebra
  refine
    { R := h.R
      S := h.S
      a := h.a
      p := h.p
      xi := h.xi
      chart := h.chart
      stalkIso := ?_ }
  exact Arrow.isoMk h.baseIso h.coverIso h.stalkMap_comm

/-- Formal étaleness of the actual stalk follows from the structural local-ring
presentation and the purity--Abhyankar chart theorem. -/
theorem formallyEtale {X Y : AlgebraicGeometry.Scheme.{u}}
    {g : X ⟶ Y} {x : X} (h : SchemeStalkBoundingPresentation g x) :
    (g.stalkMap x).hom.FormallyEtale :=
  h.toSchemeStalkBoundingChart.formallyEtale

end SchemeStalkBoundingPresentation

/-- A local bounding chart presented by the localization properties of the two actual
stalks.

This is weaker and more geometric than supplying the two coordinate isomorphisms in
`SchemeStalkBoundingPresentation`.  The caller gives the natural algebra structures of
the actual stalks over the quotient rings, proves that they have the expected universal
properties as localizations, and proves the square before localization.  The coordinate
isomorphisms and their localized square are constructed below. -/
structure SchemeStalkBoundingLocalizationPresentation
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (x : X) where
  R : Type u
  S : Type u
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [algebra : Algebra R S]
  a : R
  p : Ideal S
  xi : PrimeSpectrum (S ⧸ p)
  chart : LocalBoundingChart R S a p
  [baseAlgebra : Algebra (R ⧸ Ideal.span {a}) (Arrow.mk (g.stalkMap x)).left]
  [coverAlgebra : Algebra (S ⧸ p) (Arrow.mk (g.stalkMap x)).right]
  [baseLocalization : IsLocalization.AtPrime (Arrow.mk (g.stalkMap x)).left
    (chart.restrictionPoint xi).asIdeal]
  [coverLocalization : IsLocalization.AtPrime (Arrow.mk (g.stalkMap x)).right xi.asIdeal]
  stalkMap_algebraMap :
    (g.stalkMap x).hom.comp
      (algebraMap (R ⧸ Ideal.span {a}) (Arrow.mk (g.stalkMap x)).left) =
    (algebraMap (S ⧸ p) (Arrow.mk (g.stalkMap x)).right).comp
      chart.restrictionRingHom

namespace SchemeStalkBoundingLocalizationPresentation

/-- The universal property of localization constructs the two stalk coordinates and
their commutative square. -/
noncomputable def toSchemeStalkBoundingPresentation
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {x : X}
    (h : SchemeStalkBoundingLocalizationPresentation g x) :
    SchemeStalkBoundingPresentation g x := by
  letI : CommRing h.R := h.commRingR
  letI : CommRing h.S := h.commRingS
  letI : Algebra h.R h.S := h.algebra
  letI : Algebra (h.R ⧸ Ideal.span {h.a}) (h.S ⧸ h.p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.chart.toBoundingChart.span_le_comap
  letI : Algebra (h.R ⧸ Ideal.span {h.a})
      (Arrow.mk (g.stalkMap x)).left := h.baseAlgebra
  letI : Algebra (h.S ⧸ h.p) (Arrow.mk (g.stalkMap x)).right := h.coverAlgebra
  letI : IsLocalization.AtPrime (Arrow.mk (g.stalkMap x)).left
      (h.chart.restrictionPoint h.xi).asIdeal := h.baseLocalization
  letI : IsLocalization.AtPrime (Arrow.mk (g.stalkMap x)).right h.xi.asIdeal :=
    h.coverLocalization
  let eBase := (IsLocalization.algEquiv
    (h.chart.restrictionPoint h.xi).asIdeal.primeCompl
    (Arrow.mk (g.stalkMap x)).left
    (Localization.AtPrime
      (h.chart.restrictionPoint h.xi).asIdeal)).toRingEquiv.toCommRingCatIso
  let eCover := (IsLocalization.algEquiv h.xi.asIdeal.primeCompl
    (Arrow.mk (g.stalkMap x)).right
    (Localization.AtPrime h.xi.asIdeal)).toRingEquiv.toCommRingCatIso
  refine
    { R := h.R
      S := h.S
      a := h.a
      p := h.p
      xi := h.xi
      chart := h.chart
      baseIso := eBase
      coverIso := eCover
      stalkMap_comm := ?_ }
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext
    (h.chart.restrictionPoint h.xi).asIdeal.primeCompl
  change
    (h.chart.restrictionLocalRingHom h.xi).comp
        (eBase.hom.hom.comp
          (algebraMap (h.R ⧸ Ideal.span {h.a}) (Arrow.mk (g.stalkMap x)).left)) =
      eCover.hom.hom.comp
        ((g.stalkMap x).hom.comp
          (algebraMap (h.R ⧸ Ideal.span {h.a}) (Arrow.mk (g.stalkMap x)).left))
  rw [h.stalkMap_algebraMap]
  ext r
  simp only [RingHom.comp_apply]
  simp [eBase, eCover]
  simpa [LocalBoundingChart.restrictionLocalRingHom,
    LocalBoundingChart.restrictionRingHom] using
      (Localization.localRingHom_to_map
        (h.chart.restrictionPoint h.xi).asIdeal h.xi.asIdeal
        (algebraMap (h.R ⧸ Ideal.span {h.a}) (h.S ⧸ h.p))
        (by simp only [LocalBoundingChart.restrictionPoint, Ideal.under_def])
        (Ideal.Quotient.mk (Ideal.span {h.a}) r))

/-- Formal étaleness follows from the localization presentation and the
purity--Abhyankar chart theorem. -/
theorem formallyEtale {X Y : AlgebraicGeometry.Scheme.{u}}
    {g : X ⟶ Y} {x : X} (h : SchemeStalkBoundingLocalizationPresentation g x) :
    (g.stalkMap x).hom.FormallyEtale :=
  h.toSchemeStalkBoundingPresentation.formallyEtale

end SchemeStalkBoundingLocalizationPresentation

namespace SchemeStalkBoundingChart

/-- Transport the canonical localization structures on the chart's two local rings
across a stalk-arrow isomorphism.

The forward construction from a localization presentation is the preferred geometric
interface because it does not ask a caller to supply any isomorphism.  This reverse
construction is useful after an arrow isomorphism has itself been derived, as in the
global affine divisor comparison: it shows that the resulting chart supplies exactly the
localization-presentation type consumed by the dynamics. -/
noncomputable def toSchemeStalkBoundingLocalizationPresentation
    {X Y : Scheme.{u}} {g : X ⟶ Y} {x : X}
    (h : SchemeStalkBoundingChart g x) :
    SchemeStalkBoundingLocalizationPresentation g x := by
  letI : CommRing h.R := h.commRingR
  letI : CommRing h.S := h.commRingS
  letI : Algebra h.R h.S := h.algebra
  let A := h.R ⧸ Ideal.span {h.a}
  let B := h.S ⧸ h.p
  letI : Algebra A B :=
    Ideal.Quotient.algebraQuotientOfLEComap
      h.chart.toBoundingChart.span_le_comap
  let LBase := (Arrow.mk (g.stalkMap x)).left
  let LCover := (Arrow.mk (g.stalkMap x)).right
  let TBase := Localization.AtPrime (h.chart.restrictionPoint h.xi).asIdeal
  let TCover := Localization.AtPrime h.xi.asIdeal
  let eBase : LBase ≃+* TBase :=
    (Arrow.leftFunc.mapIso h.stalkIso).commRingCatIsoToRingEquiv
  let eCover : LCover ≃+* TCover :=
    (Arrow.rightFunc.mapIso h.stalkIso).commRingCatIsoToRingEquiv
  letI baseAlgebra : Algebra A LBase :=
    (eBase.symm.toRingHom.comp (algebraMap A TBase)).toAlgebra
  letI coverAlgebra : Algebra B LCover :=
    (eCover.symm.toRingHom.comp (algebraMap B TCover)).toAlgebra
  let eBaseAlg : TBase ≃ₐ[A] LBase :=
    AlgEquiv.ofRingEquiv (R := A) (f := eBase.symm) (by
      intro z
      rfl)
  let eCoverAlg : TCover ≃ₐ[B] LCover :=
    AlgEquiv.ofRingEquiv (R := B) (f := eCover.symm) (by
      intro z
      rfl)
  have hBaseLoc : IsLocalization.AtPrime LBase
      (h.chart.restrictionPoint h.xi).asIdeal :=
    IsLocalization.isLocalization_of_algEquiv
      (h.chart.restrictionPoint h.xi).asIdeal.primeCompl eBaseAlg
  have hCoverLoc : IsLocalization.AtPrime LCover h.xi.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv
      h.xi.asIdeal.primeCompl eCoverAlg
  refine
    { R := h.R
      S := h.S
      a := h.a
      p := h.p
      xi := h.xi
      chart := h.chart
      baseAlgebra := baseAlgebra
      coverAlgebra := coverAlgebra
      baseLocalization := hBaseLoc
      coverLocalization := hCoverLoc
      stalkMap_algebraMap := ?_ }
  have hsquare :
      (g.stalkMap x).hom.comp eBase.symm.toRingHom =
        eCover.symm.toRingHom.comp (h.chart.restrictionLocalRingHom h.xi) := by
    exact congrArg CommRingCat.Hom.hom h.stalkIso.inv.w
  ext z
  change
    (g.stalkMap x).hom
        (eBase.symm (algebraMap A TBase (Ideal.Quotient.mk (Ideal.span {h.a}) z))) =
      eCover.symm
        (algebraMap B TCover
          (h.chart.restrictionRingHom
            (Ideal.Quotient.mk (Ideal.span {h.a}) z)))
  calc
    _ = eCover.symm
        ((h.chart.restrictionLocalRingHom h.xi)
          (algebraMap A TBase (Ideal.Quotient.mk (Ideal.span {h.a}) z))) :=
      DFunLike.congr_fun hsquare
        (algebraMap A TBase (Ideal.Quotient.mk (Ideal.span {h.a}) z))
    _ = _ := by
      congr 1
      simpa [LocalBoundingChart.restrictionLocalRingHom,
        LocalBoundingChart.restrictionRingHom] using
        (Localization.localRingHom_to_map
          (h.chart.restrictionPoint h.xi).asIdeal h.xi.asIdeal
          (algebraMap (h.R ⧸ Ideal.span {h.a}) (h.S ⧸ h.p))
          (by simp only [LocalBoundingChart.restrictionPoint, Ideal.under_def])
          (Ideal.Quotient.mk (Ideal.span {h.a}) z))

end SchemeStalkBoundingChart

/-- Construct the stalk-localization presentation from affine quotient coordinates for
a morphism between actual closed subschemes.

The only coordinate inputs are ring equivalences between the chart quotients and the
canonical affine section quotients, together with their square.  The two localization
properties, the contraction of the selected point, and the square on actual stalks are
all derived.  In particular, no stalk isomorphism or kernel identification is an input. -/
noncomputable def closedSubschemeStalkBoundingLocalizationPresentation
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (g : I.subscheme ⟶ J.subscheme) (U : Y.affineOpens) (V : X.affineOpens)
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      g ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens)))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {a : R} {p : Ideal S} (h : LocalBoundingChart R S a p)
    (eBase : (R ⧸ Ideal.span {a}) ≃+* (Γ(Y, U) ⧸ J.ideal U))
    (eCover : (S ⧸ p) ≃+* (Γ(X, V) ⧸ I.ideal V))
    (hsquare :
      (J.quotientAppLE I g U V map_le).comp eBase.toRingHom =
        eCover.toRingHom.comp h.restrictionRingHom)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens)) :
    SchemeStalkBoundingLocalizationPresentation g x := by
  let targetPoint := J.quotientPoint U (g x) hy
  let sourcePoint := I.quotientPoint V x hx
  let xi := PrimeSpectrum.comap eCover.toRingHom sourcePoint
  letI : Algebra (Γ(Y, U) ⧸ J.ideal U) (J.subscheme.presheaf.stalk (g x)) :=
    J.quotientStalkAlgebra U (g x) hy
  letI : Algebra (Γ(X, V) ⧸ I.ideal V) (I.subscheme.presheaf.stalk x) :=
    I.quotientStalkAlgebra V x hx
  haveI hTargetLoc : IsLocalization.AtPrime (J.subscheme.presheaf.stalk (g x))
      targetPoint.asIdeal := J.quotientStalk_isLocalization U (g x) hy
  haveI hSourceLoc : IsLocalization.AtPrime (I.subscheme.presheaf.stalk x)
      sourcePoint.asIdeal := I.quotientStalk_isLocalization V x hx
  let baseAlgebra : Algebra (R ⧸ Ideal.span {a})
      (J.subscheme.presheaf.stalk (g x)) :=
    ((algebraMap (Γ(Y, U) ⧸ J.ideal U) (J.subscheme.presheaf.stalk (g x))).comp
      eBase.toRingHom).toAlgebra
  let coverAlgebra : Algebra (S ⧸ p) (I.subscheme.presheaf.stalk x) :=
    ((algebraMap (Γ(X, V) ⧸ I.ideal V) (I.subscheme.presheaf.stalk x)).comp
      eCover.toRingHom).toAlgebra
  have hBaseLoc0 :
      letI := baseAlgebra
      IsLocalization.AtPrime (J.subscheme.presheaf.stalk (g x))
        (PrimeSpectrum.comap eBase.toRingHom targetPoint).asIdeal := by
    letI := baseAlgebra
    change IsLocalization ((targetPoint.asIdeal.comap eBase).primeCompl)
      (J.subscheme.presheaf.stalk (g x))
    apply IsLocalization.of_ringEquiv_left eBase
      (eBase.map_primeCompl_comap_eq targetPoint.asIdeal)
    intro r
    rfl
  have hCoverLoc :
      letI := coverAlgebra
      IsLocalization.AtPrime (I.subscheme.presheaf.stalk x) xi.asIdeal := by
    letI := coverAlgebra
    change IsLocalization ((sourcePoint.asIdeal.comap eCover).primeCompl)
      (I.subscheme.presheaf.stalk x)
    apply IsLocalization.of_ringEquiv_left eCover
      (eCover.map_primeCompl_comap_eq sourcePoint.asIdeal)
    intro r
    rfl
  have htarget : h.restrictionPoint xi =
      PrimeSpectrum.comap eBase.toRingHom targetPoint := by
    have hcontract := J.comap_quotientPoint_quotientAppLE I g U V map_le x hx hy
    change
      PrimeSpectrum.comap h.restrictionRingHom
          (PrimeSpectrum.comap eCover.toRingHom sourcePoint) =
        PrimeSpectrum.comap eBase.toRingHom targetPoint
    rw [← PrimeSpectrum.comap_comp_apply]
    rw [← hsquare, PrimeSpectrum.comap_comp_apply, hcontract]
  let hBaseLoc :
      letI := baseAlgebra
      IsLocalization.AtPrime (J.subscheme.presheaf.stalk (g x))
        (h.restrictionPoint xi).asIdeal := by
    letI := baseAlgebra
    rw [htarget]
    exact hBaseLoc0
  refine
    { R := R
      S := S
      a := a
      p := p
      xi := xi
      chart := h
      baseAlgebra := baseAlgebra
      coverAlgebra := coverAlgebra
      baseLocalization := hBaseLoc
      coverLocalization := hCoverLoc
      stalkMap_algebraMap := ?_ }
  change
    (g.stalkMap x).hom.comp
        ((algebraMap (Γ(Y, U) ⧸ J.ideal U)
          (J.subscheme.presheaf.stalk (g x))).comp eBase.toRingHom) =
      ((algebraMap (Γ(X, V) ⧸ I.ideal V)
          (I.subscheme.presheaf.stalk x)).comp eCover.toRingHom).comp
        h.restrictionRingHom
  rw [← RingHom.comp_assoc,
    J.stalkMap_comp_quotientStalkAlgebraMap I g U V map_le x hx hy]
  rw [RingHom.comp_assoc, hsquare]
  rw [← RingHom.comp_assoc]

/-- Construct the stalk-localization presentation when the local chart rings are the
ambient affine section rings themselves.

The coordinate inputs are only equalities identifying the two defining ideals and the
assertion that the map on closed-subscheme sections is the quotient of the ambient
algebra map.  The quotient equivalences and their commutative square are constructed
canonically. -/
noncomputable def closedSubschemeStalkBoundingLocalizationPresentationOfIdeals
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (g : I.subscheme ⟶ J.subscheme) (U : Y.affineOpens) (V : X.affineOpens)
    (map_le : I.subschemeι ⁻¹ᵁ (V : X.Opens) ≤
      g ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ (U : Y.Opens)))
    [Algebra Γ(Y, U) Γ(X, V)]
    {a : Γ(Y, U)} {p : Ideal Γ(X, V)}
    (h : LocalBoundingChart Γ(Y, U) Γ(X, V) a p)
    (hJ : J.ideal U = Ideal.span {a})
    (hI : I.ideal V = p)
    (hmap :
      J.quotientAppLE I g U V map_le =
        Ideal.quotientMap (I.ideal V) (algebraMap Γ(Y, U) Γ(X, V)) (by
          rw [hJ, hI]
          exact h.toBoundingChart.span_le_comap))
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens))
    (hy : g x ∈ J.subschemeι ⁻¹ᵁ (U : Y.Opens)) :
    SchemeStalkBoundingLocalizationPresentation g x := by
  let eBase : (Γ(Y, U) ⧸ Ideal.span {a}) ≃+* (Γ(Y, U) ⧸ J.ideal U) :=
    (Ideal.quotientEquivAlgOfEq ℤ hJ.symm).toRingEquiv
  let eCover : (Γ(X, V) ⧸ p) ≃+* (Γ(X, V) ⧸ I.ideal V) :=
    (Ideal.quotientEquivAlgOfEq ℤ hI.symm).toRingEquiv
  apply closedSubschemeStalkBoundingLocalizationPresentation J I g U V map_le h
    eBase eCover
  · apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    rw [hmap]
    simp only [eBase, eCover]
    change
      Ideal.Quotient.mk (I.ideal V) (algebraMap Γ(Y, U) Γ(X, V) r) =
        Ideal.Quotient.mk (I.ideal V) (algebraMap Γ(Y, U) Γ(X, V) r)
    rfl
  · exact hx
  · exact hy

/-- Construct the stalk-localization presentation for the restriction of an actual
ambient morphism to closed subschemes.

Functoriality supplies the source-open inclusion, the containment of defining ideals,
and the quotient-map square.  Thus, once the ambient section rings carry the local
bounding chart, the only remaining coordinate assumptions are the two equalities of
defining ideals. -/
noncomputable def closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap
    {Y X : Scheme.{u}} (J : Y.IdealSheafData) (I : X.IdealSheafData)
    (f : X ⟶ Y) (H : J ≤ I.map f)
    (U : Y.affineOpens) (V : X.affineOpens)
    (ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    {a : Γ(Y, U)} {p : Ideal Γ(X, V)}
    (h : letI : Algebra Γ(Y, U) Γ(X, V) :=
          (f.appLE U V ambient_map_le).hom.toAlgebra
        LocalBoundingChart Γ(Y, U) Γ(X, V) a p)
    (hJ : J.ideal U = Ideal.span {a})
    (hI : I.ideal V = p)
    (x : I.subscheme) (hx : x ∈ I.subschemeι ⁻¹ᵁ (V : X.Opens)) :
    SchemeStalkBoundingLocalizationPresentation (I.subschemeMap J f H) x := by
  letI : Algebra Γ(Y, U) Γ(X, V) :=
    (f.appLE U V ambient_map_le).hom.toAlgebra
  let map_le := I.subschemeMap_preimage_le J f H U V ambient_map_le
  apply closedSubschemeStalkBoundingLocalizationPresentationOfIdeals
    J I (I.subschemeMap J f H) U V map_le h hJ hI
  · simpa only [RingHom.algebraMap_toAlgebra] using
      J.quotientAppLE_subschemeMap_eq_quotientMap I f H U V ambient_map_le
  · exact hx
  · exact map_le hx

/-- If the ideal of an ideal sheaf becomes principal in the local ring at a point, then
it is generated by one section on a principal-open affine neighborhood of that point.

This is the scheme-coordinate form of
`exists_principal_map_of_atPrime_isPrincipal`: the target localization is taken to be the
actual section ring of the affine basic open, and the ideal-sheaf restriction axiom
identifies the localized ideal with the ideal on that open. -/
theorem exists_principal_affineBasicOpen_of_atPrime_isPrincipal
    {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (p q : Ideal Γ(X, U))
    [IsNoetherianRing Γ(X, U)] [p.IsPrime] [q.IsPrime]
    (hJ : J.ideal U = p) (hpq : p ≤ q)
    [(p.map (algebraMap Γ(X, U) (Localization.AtPrime q))).IsPrincipal] :
    ∃ a f : Γ(X, U), a ∈ p ∧ f ∉ q ∧
      J.ideal (X.affineBasicOpen f) =
        Ideal.span {X.presheaf.map (homOfLE (X.basicOpen_le f)).op a} := by
  obtain ⟨a, f, ha, hf, h⟩ :=
    exists_principal_map_of_atPrime_isPrincipal p q hpq
  refine ⟨a, f, ha, hf, ?_⟩
  rw [← J.map_ideal_basicOpen U f, hJ]
  letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  letI : IsLocalization.Away f Γ(X, X.affineBasicOpen f) :=
    U.2.isLocalization_basicOpen f
  exact h Γ(X, X.affineBasicOpen f)

/-- At a codimension-two regular point, a height-one divisor ideal is generated by one
section after shrinking to an affine basic open containing the point.

This is the exact scheme-coordinate consequence of the low-dimensional replacement for
Stacks 0AG0/0AGA proved in `Bounding.Divisors`: regularity of the two-dimensional ambient
local ring and of the one-dimensional divisor quotient makes the localized prime
principal, after which the preceding theorem spreads its generator. -/
theorem exists_principal_affineBasicOpen_of_atPrime_regular_dim_two
    {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (p q : Ideal Γ(X, U))
    [IsNoetherianRing Γ(X, U)] [IsDomain Γ(X, U)]
    [p.IsPrime] [q.IsPrime]
    (hJ : J.ideal U = p) (hpq : p ≤ q) (hp : p.height = 1)
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = 2)
    [IsRegularLocalRing
      (Localization.AtPrime q ⧸ p.map
        (algebraMap Γ(X, U) (Localization.AtPrime q)))]
    (hquotdim : ringKrullDim
      (Localization.AtPrime q ⧸ p.map
        (algebraMap Γ(X, U) (Localization.AtPrime q))) = 1) :
    ∃ a f : Γ(X, U), a ∈ p ∧ f ∉ q ∧
      J.ideal (X.affineBasicOpen f) =
        Ideal.span {X.presheaf.map (homOfLE (X.basicOpen_le f)).op a} := by
  let Rq := Localization.AtPrime q
  let P : Ideal Rq := p.map (algebraMap Γ(X, U) Rq)
  have hd : Disjoint (q.primeCompl : Set Γ(X, U)) (p : Set Γ(X, U)) := by
    rw [Set.disjoint_left]
    exact fun x hxq hxp => hxq (hpq hxp)
  let _ : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Rq p inferInstance hd
  have hheight : P.height = 1 :=
    (IsLocalization.height_map_of_disjoint q.primeCompl p hd).trans hp
  let _ : P.IsPrincipal :=
    heightOne_isPrincipal_of_regularLocalRing_dim_two Rq hdim P hheight hquotdim
  exact exists_principal_affineBasicOpen_of_atPrime_isPrincipal
    J U p q hJ hpq

/-- Principality of an ideal sheaf on an affine open becomes the exact top-section
principal-ideal equality for the pullback ideal sheaf on the corresponding open scheme.

This removes the coordinate mismatch between an affine open `V` of `X` and the affine
scheme `V.toScheme` used as a target chart. -/
theorem IdealSheafData.exists_generator_comap_top_of_ideal_eq_span
    {X : Scheme.{u}} (J : X.IdealSheafData) (V : X.affineOpens)
    (b : Γ(X, V)) (h : J.ideal V = Ideal.span {b}) :
    ∃ c : Γ(V.1.toScheme, ⊤),
      (J.comap V.1.ι).ideal
          ⟨⊤, isAffineOpen_top V.1.toScheme⟩ = Ideal.span {c} := by
  have himage : V.1.ι ''ᵁ (⊤ : V.1.toScheme.Opens) = V.1 := by simp
  let W : X.affineOpens :=
    ⟨V.1.ι ''ᵁ (⊤ : V.1.toScheme.Opens),
      (isAffineOpen_top V.1.toScheme).image_of_isOpenImmersion V.1.ι⟩
  have hWV : W = V := by
    apply Subtype.ext
    exact himage
  have hle : W ≤ V := by
    rw [hWV]
  let bW : Γ(X, W) := X.presheaf.map (homOfLE hle).op b
  refine ⟨bW, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  change (J.ideal W).comap (V.1.ι.appIso ⊤).inv.hom = _
  have hbW : J.ideal W = Ideal.span {bW} := by
    rw [← J.map_ideal hle, h, Ideal.map_span, Set.image_singleton]
  rw [hbW, Scheme.Opens.ι_appIso]
  change Ideal.comap (RingHom.id _) (Ideal.span {bW}) = Ideal.span {bW}
  exact Ideal.comap_id _

/-- At a codimension-two regular point, the actual pullback of the divisor ideal sheaf to
a suitable affine basic-open scheme has a principal top-section ideal.

The returned equality is exactly the `hJ` coordinate hypothesis of
`affineIdealSheafStalkBoundingLocalizationPresentation`; it is obtained from local
regularity and dimension, not assumed. -/
theorem exists_principal_comap_affineBasicOpen_of_atPrime_regular_dim_two
    {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (p q : Ideal Γ(X, U))
    [IsNoetherianRing Γ(X, U)] [IsDomain Γ(X, U)]
    [p.IsPrime] [q.IsPrime]
    (hJ : J.ideal U = p) (hpq : p ≤ q) (hp : p.height = 1)
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = 2)
    [IsRegularLocalRing
      (Localization.AtPrime q ⧸ p.map
        (algebraMap Γ(X, U) (Localization.AtPrime q)))]
    (hquotdim : ringKrullDim
      (Localization.AtPrime q ⧸ p.map
        (algebraMap Γ(X, U) (Localization.AtPrime q))) = 1) :
    ∃ (a f : Γ(X, U))
        (c : Γ((X.affineBasicOpen f).1.toScheme, ⊤)),
      a ∈ p ∧ f ∉ q ∧
      (J.comap (X.affineBasicOpen f).1.ι).ideal
          ⟨⊤, isAffineOpen_top (X.affineBasicOpen f).1.toScheme⟩ =
        Ideal.span {c} := by
  obtain ⟨a, f, ha, hf, hprincipal⟩ :=
    exists_principal_affineBasicOpen_of_atPrime_regular_dim_two
      J U p q hJ hpq hp hdim hquotdim
  obtain ⟨c, hc⟩ :=
    IdealSheafData.exists_generator_comap_top_of_ideal_eq_span J
      (X.affineBasicOpen f)
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op a)
      hprincipal
  exact ⟨a, f, c, ha, hf, hc⟩

/-- On affine ambient schemes, a local bounding chart whose selected source component is
the source ideal sheaf itself proves that the ambient morphism restricts to the two closed
subschemes.

The only ideal-coordinate input is that the target ideal sheaf is generated by the chart
equation `a`.  The containment of ideal sheaves follows from the chart's canonical
containment `(a) ⊆ f⁻¹(I)` on global sections. -/
theorem affineIdealSheaf_le_map_of_localBoundingChart
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X]
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (f : X ⟶ Y)
    {a : Γ(Y, ⊤)}
    (h : let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
         let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
         let ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens) := by rfl
         letI : Algebra Γ(Y, U) Γ(X, V) :=
           (f.appLE U V ambient_map_le).hom.toAlgebra
         LocalBoundingChart Γ(Y, U) Γ(X, V) a (I.ideal V))
    (hJ : J.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {a}) :
    J ≤ I.map f := by
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens) := by rfl
  letI : Algebra Γ(Y, U) Γ(X, V) :=
    (f.appLE U V ambient_map_le).hom.toAlgebra
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
  let W : X.affineOpens := ⟨f ⁻¹ᵁ (U : Y.Opens), U.2.preimage f⟩
  change J.ideal U ≤ (I.ideal W).comap (f.app U).hom
  have hWV : W = V := by
    apply Subtype.ext
    rfl
  rw [hJ]
  subst W
  have hspan := h.toBoundingChart.span_le_comap
  change Ideal.span {a} ≤
    (I.ideal V).comap (f.appLE U V ambient_map_le).hom at hspan
  have happ : f.appLE U V ambient_map_le = f.app ⊤ := by
    convert f.appLE_eq_app using 1 <;> rfl
  rw [happ] at hspan
  exact hspan

/-- Construct the complete actual-stalk localization presentation on affine ambient
schemes from a local bounding chart and one principal-ideal identification.

The selected component `p` is definitionally the source ideal sheaf on the top affine
open.  The preceding theorem constructs the restricted morphism; affine ideal-sheaf
functoriality constructs its quotient map and square; and the closed-subscheme bridge
constructs both quotient-to-stalk localizations and the actual stalk square. -/
noncomputable def affineIdealSheafStalkBoundingLocalizationPresentation
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X]
    (J : Y.IdealSheafData) (I : X.IdealSheafData) (f : X ⟶ Y)
    {a : Γ(Y, ⊤)}
    (h : let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
         let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
         let ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens) := by rfl
         letI : Algebra Γ(Y, U) Γ(X, V) :=
           (f.appLE U V ambient_map_le).hom.toAlgebra
         LocalBoundingChart Γ(Y, U) Γ(X, V) a (I.ideal V))
    (hJ : J.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {a})
    (x : I.subscheme) :
    SchemeStalkBoundingLocalizationPresentation
      (I.subschemeMap J f
        (affineIdealSheaf_le_map_of_localBoundingChart J I f h hJ)) x := by
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let ambient_map_le : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens) := by rfl
  letI : Algebra Γ(Y, U) Γ(X, V) :=
    (f.appLE U V ambient_map_le).hom.toAlgebra
  apply closedSubschemeStalkBoundingLocalizationPresentationOfAmbientMap
    J I f (affineIdealSheaf_le_map_of_localBoundingChart J I f h hJ)
      U V ambient_map_le h hJ rfl
  simp [V]

/-- Failure of formal unramifiedness at a point, defined from the actual stalk map. -/
def schemeCrit0At {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (x : X) : Prop :=
  ¬ (g.stalkMap x).hom.FormallyUnramified

/-- The codimension-one stalk-formal-non-unramified locus of an actual scheme morphism. -/
def schemeDivisorCrit0 {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint X) :=
  {x | schemeCrit0At g x.1}

@[simp]
theorem mem_schemeDivisorCrit0_iff {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (x : SchemeDivisorPoint X) :
    x ∈ schemeDivisorCrit0 g ↔ ¬ (g.stalkMap x.1).hom.FormallyUnramified :=
  Iff.rfl

/-- Failure of formal étaleness at a point, defined from the actual stalk map.

For the locally finitely presented morphisms used in `SchemeNormalizationUnnormDyn`, this
is the stalk criterion underlying the manuscript's pointwise non-étale locus. -/
def schemeCrit1At {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (x : X) : Prop :=
  ¬ (g.stalkMap x).hom.FormallyEtale

/-- The codimension-one stalk-formal-non-étale locus of an actual scheme morphism. -/
def schemeDivisorCrit1 {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint X) :=
  {x | schemeCrit1At g x.1}

@[simp]
theorem mem_schemeDivisorCrit1_iff {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (x : SchemeDivisorPoint X) :
    x ∈ schemeDivisorCrit1 g ↔ ¬ (g.stalkMap x.1).hom.FormallyEtale :=
  Iff.rfl

/-- Formal étaleness implies formal unramifiedness, so the actual non-unramified
divisor locus is contained in the actual non-étale divisor locus (U2). -/
theorem schemeDivisorCrit0_subset_crit1 {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) : schemeDivisorCrit0 g ⊆ schemeDivisorCrit1 g := by
  intro x hx he
  apply hx
  letI := (g.stalkMap x.1).hom.toAlgebra
  letI : Algebra.FormallyEtale (Y.presheaf.stalk (g x.1))
      (X.presheaf.stalk x.1) := he
  exact (inferInstance : Algebra.FormallyUnramified
    (Y.presheaf.stalk (g x.1)) (X.presheaf.stalk x.1))

/-- A divisor point represented by a local bounding chart is not in the actual
codimension-one non-étale locus. -/
theorem SchemeStalkBoundingChart.not_mem_schemeDivisorCrit1
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y}
    {x : SchemeDivisorPoint X} (h : SchemeStalkBoundingChart g x.1) :
    x ∉ schemeDivisorCrit1 g := by
  rw [mem_schemeDivisorCrit1_iff]
  exact not_not_intro h.formallyEtale

/-- A divisor point with structural local-ring coordinates is not in the actual
codimension-one non-étale locus. -/
theorem SchemeStalkBoundingPresentation.not_mem_schemeDivisorCrit1
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y}
    {x : SchemeDivisorPoint X} (h : SchemeStalkBoundingPresentation g x.1) :
    x ∉ schemeDivisorCrit1 g := by
  rw [mem_schemeDivisorCrit1_iff]
  exact not_not_intro h.formallyEtale

/-- A divisor point whose quotient rings localize to its actual stalks is not in the
actual codimension-one non-étale locus. -/
theorem SchemeStalkBoundingLocalizationPresentation.not_mem_schemeDivisorCrit1
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y}
    {x : SchemeDivisorPoint X}
    (h : SchemeStalkBoundingLocalizationPresentation g x.1) :
    x ∉ schemeDivisorCrit1 g := by
  rw [mem_schemeDivisorCrit1_iff]
  exact not_not_intro h.formallyEtale

namespace LocalBoundingChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {a : R} {p : Ideal S} (h : LocalBoundingChart R S a p)

/-- The quotient ring map supplied by a local bounding chart is globally étale.

The chart theorem proves étaleness at every prime.  Finite presentation follows from
module-finiteness over the Noetherian quotient of the base, so the pointwise statement
promotes to `RingHom.Etale`. -/
theorem restrictionRingHom_etale :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)).Etale := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  letI : IsNoetherianRing R := h.toBoundingChart.noetherian_base
  letI : Module.Finite R S := h.finite
  letI : IsScalarTower R (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : Module.Finite R (S ⧸ p) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R p).toLinearMap
      Ideal.Quotient.mk_surjective
  let _ : Module.Finite (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Module.Finite.of_restrictScalars_finite R _ _
  let _ : Algebra.FinitePresentation (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [RingHom.etale_algebraMap]
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  ext xi
  simp only [Set.mem_univ, iff_true]
  exact h.isEtaleAt_restriction xi

/-- The affine quotient morphism supplied by a local bounding chart is étale. -/
theorem restrictionScheme_etale :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale)]
  exact h.restrictionRingHom_etale

/-- On the affine quotient chart, the required stalk identification is Mathlib's
canonical identification of a `Spec.map` stalk map with the localized ring homomorphism.

Thus `SchemeStalkBoundingChart.stalkIso` is not an additional assumption for the affine
morphism `Spec (S/p) → Spec (R/(a))`; only transporting an actual restricted morphism to
this affine presentation remains. -/
noncomputable def toSchemeStalkBoundingChart (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    SchemeStalkBoundingChart
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) xi := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  refine
    { R := R
      S := S
      a := a
      p := p
      xi := xi
      chart := h
      stalkIso := ?_ }
  exact AlgebraicGeometry.Scheme.arrowStalkMapSpecIso
    (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))) xi

/-- For the literal affine quotient morphism, the structural local-ring coordinates are
the source and target components of Mathlib's canonical stalk-map isomorphism. -/
noncomputable def toSchemeStalkBoundingPresentation
    (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    SchemeStalkBoundingPresentation
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) xi := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  let f := CommRingCat.ofHom
    (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))
  let e := AlgebraicGeometry.Scheme.arrowStalkMapSpecIso f xi
  refine
    { R := R
      S := S
      a := a
      p := p
      xi := xi
      chart := h
      baseIso := Arrow.leftFunc.mapIso e
      coverIso := Arrow.rightFunc.mapIso e
      stalkMap_comm := ?_ }
  exact e.hom.w

/-- For the literal affine quotient morphism, the actual source and target stalks carry
their canonical localization structures over the quotient rings, and functoriality of
`Spec` supplies the quotient-ring square. -/
noncomputable def toSchemeStalkBoundingLocalizationPresentation
    (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    SchemeStalkBoundingLocalizationPresentation
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) xi := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  let f := CommRingCat.ofHom
    (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))
  refine
    { R := R
      S := S
      a := a
      p := p
      xi := xi
      chart := h
      baseAlgebra := StructureSheaf.stalkAlgebra (R ⧸ Ideal.span {a})
        (PrimeSpectrum.comap f.hom xi)
      coverAlgebra := StructureSheaf.stalkAlgebra (S ⧸ p) xi
      baseLocalization := StructureSheaf.IsLocalization.to_stalk
        (R ⧸ Ideal.span {a}) (PrimeSpectrum.comap f.hom xi)
      coverLocalization := StructureSheaf.IsLocalization.to_stalk (S ⧸ p) xi
      stalkMap_algebraMap := ?_ }
  change
    (StructureSheaf.toStalk (R ⧸ Ideal.span {a})
        (PrimeSpectrum.comap f.hom xi) ≫
      (AlgebraicGeometry.Spec.sheafedSpaceMap f).hom.stalkMap xi).hom =
    (f ≫ StructureSheaf.toStalk (S ⧸ p) xi).hom
  exact congrArg CommRingCat.Hom.hom
    (AlgebraicGeometry.stalkMap_toStalk f xi)

/-- The actual stalk-defined codimension-one non-étale locus of the affine quotient
morphism is empty. -/
theorem schemeDivisorCrit1_restriction_eq_empty :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    schemeDivisorCrit1
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) = ∅ := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x
  exact (h.toSchemeStalkBoundingChart x.1).not_mem_schemeDivisorCrit1

end LocalBoundingChart

/-- A local presentation of an actual scheme morphism by the affine quotient morphism
attached to a `LocalBoundingChart`.

Unlike `SchemeStalkBoundingChart`, this records only scheme-level geometric data: open
neighbourhoods of the chosen point and an isomorphism of arrows identifying the restricted
morphism with `Spec (S/p) → Spec (R/(a))`.  The isomorphism of local-ring maps, and hence
formal étaleness of the actual stalk, are derived below. -/
structure SchemeLocalBoundingPresentation {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (x : X) where
  U : Y.Opens
  V : X.Opens
  map_le : V ≤ g ⁻¹ᵁ U
  mem : x ∈ V
  R : Type u
  S : Type u
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [algebra : Algebra R S]
  a : R
  p : Ideal S
  chart : LocalBoundingChart R S a p
  presentation :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap chart.toBoundingChart.span_le_comap
    Arrow.mk (g.resLE U V map_le) ≅
      Arrow.mk (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))))

/-- Restricting a scheme morphism to the top open on source and target gives an
isomorphic arrow. -/
noncomputable def schemeResLETopIso
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) :
    Arrow.mk (g.resLE ⊤ ⊤ (by simp)) ≅ Arrow.mk g := by
  refine Arrow.isoMk (AlgebraicGeometry.Scheme.topIso X)
    (AlgebraicGeometry.Scheme.topIso Y) ?_
  change (⊤ : X.Opens).ι ≫ g =
    g.resLE (⊤ : Y.Opens) (⊤ : X.Opens) (by simp) ≫ (⊤ : Y.Opens).ι
  exact (g.resLE_comp_ι (U := ⊤) (V := ⊤) (by simp)).symm

/-- A morphism restricted between affine opens is isomorphic, as an arrow of schemes, to
the spectrum of its map on sections. -/
noncomputable def affineResLEArrowIso
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (map_le : V ≤ g ⁻¹ᵁ U)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (hV : AlgebraicGeometry.IsAffineOpen V) :
    Arrow.mk (g.resLE U V map_le) ≅
      Arrow.mk (AlgebraicGeometry.Spec.map (g.appLE U V map_le)) := by
  refine Arrow.isoMk hV.isoSpec hU.isoSpec ?_
  exact AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE g U V map_le

/-- If the section rings on two affine opens are identified with the quotient rings of a
local bounding chart, and the induced ring maps commute under those identifications, then
the restricted scheme morphism has the required affine quotient presentation.

This is the automatic affine-scheme part of Step 0: callers no longer construct an
isomorphism in the arrow category. -/
noncomputable def affineQuotientArrowIso
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (map_le : V ≤ g ⁻¹ᵁ U)
    (hU : AlgebraicGeometry.IsAffineOpen U)
    (hV : AlgebraicGeometry.IsAffineOpen V)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {a : R} {p : Ideal S} (h : LocalBoundingChart R S a p)
    (eU : Γ(Y, U) ≅ CommRingCat.of (R ⧸ Ideal.span {a}))
    (eV : Γ(X, V) ≅ CommRingCat.of (S ⧸ p))
    (hsquare : g.appLE U V map_le ≫ eV.hom =
      eU.hom ≫ CommRingCat.ofHom
        (letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
          Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
         algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    Arrow.mk (g.resLE U V map_le) ≅
      Arrow.mk (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  refine (affineResLEArrowIso g U V map_le hU hV).trans ?_
  refine Arrow.isoMk
    (AlgebraicGeometry.Scheme.Spec.mapIso eV.symm.op)
    (AlgebraicGeometry.Scheme.Spec.mapIso eU.symm.op) ?_
  change AlgebraicGeometry.Spec.map eV.inv ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))) =
    AlgebraicGeometry.Spec.map (g.appLE U V map_le) ≫
      AlgebraicGeometry.Spec.map eU.inv
  rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  rw [← cancel_mono eV.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hsquare, Iso.inv_hom_id_assoc]

/-- Affine-open data presenting an actual local scheme morphism by the quotient map of a
`LocalBoundingChart`.

The two ring isomorphisms and `appLE_comm` are the standard affine-coordinate content of
the geometric Step 0 construction.  In particular, this structure contains neither an
arrow isomorphism nor any étaleness or critical-locus conclusion. -/
structure SchemeAffineLocalBoundingPresentation
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (x : X) where
  U : Y.Opens
  V : X.Opens
  map_le : V ≤ g ⁻¹ᵁ U
  mem : x ∈ V
  affine_U : AlgebraicGeometry.IsAffineOpen U
  affine_V : AlgebraicGeometry.IsAffineOpen V
  R : Type u
  S : Type u
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [algebra : Algebra R S]
  a : R
  p : Ideal S
  chart : LocalBoundingChart R S a p
  baseIso : Γ(Y, U) ≅ CommRingCat.of (R ⧸ Ideal.span {a})
  coverIso : Γ(X, V) ≅ CommRingCat.of (S ⧸ p)
  appLE_comm :
    g.appLE U V map_le ≫ coverIso.hom =
      baseIso.hom ≫ CommRingCat.ofHom
        (letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
          Ideal.Quotient.algebraQuotientOfLEComap
            chart.toBoundingChart.span_le_comap
         algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))

namespace SchemeAffineLocalBoundingPresentation

/-- The affine-open coordinate data canonically constructs the scheme-arrow presentation. -/
noncomputable def toSchemeLocalBoundingPresentation
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y} {x : X}
    (h : SchemeAffineLocalBoundingPresentation g x) :
    SchemeLocalBoundingPresentation g x := by
  letI : CommRing h.R := h.commRingR
  letI : CommRing h.S := h.commRingS
  letI : Algebra h.R h.S := h.algebra
  refine
    { U := h.U
      V := h.V
      map_le := h.map_le
      mem := h.mem
      R := h.R
      S := h.S
      a := h.a
      p := h.p
      chart := h.chart
      presentation := ?_ }
  exact affineQuotientArrowIso g h.U h.V h.map_le h.affine_U h.affine_V
    h.chart h.baseIso h.coverIso h.appLE_comm

end SchemeAffineLocalBoundingPresentation

namespace LocalBoundingChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {a : R} {p : Ideal S} (h : LocalBoundingChart R S a p)

/-- The affine quotient morphism of a local chart has its canonical scheme-level local
bounding presentation.  This witnesses that `SchemeLocalBoundingPresentation` adds no
extra hypothesis in the literal affine case. -/
noncomputable def toSchemeLocalBoundingPresentation (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    SchemeLocalBoundingPresentation
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) xi := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  let g := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))
  refine
    { U := ⊤
      V := ⊤
      map_le := by simp
      mem := trivial
      R := R
      S := S
      a := a
      p := p
      chart := h
      presentation := ?_ }
  exact schemeResLETopIso g

/-- The literal affine quotient morphism also has the more geometric affine-open
presentation.  The section-ring identifications are the canonical `Γ(Spec(-))`
isomorphisms, and their compatibility is naturality. -/
noncomputable def toSchemeAffineLocalBoundingPresentation
    (xi : PrimeSpectrum (S ⧸ p)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    SchemeAffineLocalBoundingPresentation
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p)))) xi := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
  let f := CommRingCat.ofHom
    (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ p))
  refine
    { U := ⊤
      V := ⊤
      map_le := by simp
      mem := trivial
      affine_U := AlgebraicGeometry.isAffineOpen_top _
      affine_V := AlgebraicGeometry.isAffineOpen_top _
      R := R
      S := S
      a := a
      p := p
      chart := h
      baseIso := AlgebraicGeometry.Scheme.ΓSpecIso _
      coverIso := AlgebraicGeometry.Scheme.ΓSpecIso _
      appLE_comm := ?_ }
  change (AlgebraicGeometry.Spec.map f).appTop ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso _).hom =
    (AlgebraicGeometry.Scheme.ΓSpecIso _).hom ≫ f
  exact AlgebraicGeometry.Scheme.ΓSpecIso_naturality f

end LocalBoundingChart

namespace SchemeLocalBoundingPresentation

/-- The actual restricted morphism is étale, derived from the local chart's purity and
Abhyankar inputs and the scheme-level affine presentation. -/
theorem restrictedEtale {X Y : AlgebraicGeometry.Scheme.{u}}
    {g : X ⟶ Y} {x : X} (h : SchemeLocalBoundingPresentation g x) :
    AlgebraicGeometry.Etale (g.resLE h.U h.V h.map_le) := by
  letI : CommRing h.R := h.commRingR
  letI : CommRing h.S := h.commRingS
  letI : Algebra h.R h.S := h.algebra
  letI : Algebra (h.R ⧸ Ideal.span {h.a}) (h.S ⧸ h.p) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.chart.toBoundingChart.span_le_comap
  have hspec : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (algebraMap (h.R ⧸ Ideal.span {h.a}) (h.S ⧸ h.p)))) :=
    h.chart.restrictionScheme_etale
  letI : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale) := by
    rw [AlgebraicGeometry.HasRingHomProperty.eq_affineLocally
      (@AlgebraicGeometry.Etale)]
    exact AlgebraicGeometry.affineLocally_respectsIso _ RingHom.Etale.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff
    (@AlgebraicGeometry.Etale) h.presentation).mpr hspec

/-- The actual stalk map is formally étale.  The proof first derives étaleness of the
restricted morphism and then uses Mathlib's canonical stalk isomorphism for restriction
to transport back to `g.stalkMap x`. -/
theorem formallyEtale {X Y : AlgebraicGeometry.Scheme.{u}}
    {g : X ⟶ Y} {x : X} (h : SchemeLocalBoundingPresentation g x) :
    (g.stalkMap x).hom.FormallyEtale := by
  have hrestricted :
      ((g.resLE h.U h.V h.map_le).stalkMap ⟨x, h.mem⟩).hom.FormallyEtale :=
    AlgebraicGeometry.Etale.stalkMap_formallyEtale h.restrictedEtale ⟨x, h.mem⟩
  exact (formallyEtale_respectsIso.arrow_mk_iso_iff
    (g.resLEStalkMap h.map_le ⟨x, h.mem⟩)).mp hrestricted

/-- A divisor point admitting a scheme-level local bounding presentation is not in the
actual codimension-one non-étale locus. -/
theorem not_mem_schemeDivisorCrit1
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y}
    {x : SchemeDivisorPoint X} (h : SchemeLocalBoundingPresentation g x.1) :
    x ∉ schemeDivisorCrit1 g := by
  rw [mem_schemeDivisorCrit1_iff]
  exact not_not_intro h.formallyEtale

end SchemeLocalBoundingPresentation

namespace SchemeAffineLocalBoundingPresentation

/-- Formal étaleness of the actual stalk, derived after constructing the arrow
presentation from affine section rings. -/
theorem formallyEtale {X Y : AlgebraicGeometry.Scheme.{u}}
    {g : X ⟶ Y} {x : X} (h : SchemeAffineLocalBoundingPresentation g x) :
    (g.stalkMap x).hom.FormallyEtale :=
  h.toSchemeLocalBoundingPresentation.formallyEtale

/-- A divisor point with affine local bounding data is not in the actual codimension-one
non-étale locus. -/
theorem not_mem_schemeDivisorCrit1
    {X Y : AlgebraicGeometry.Scheme.{u}} {g : X ⟶ Y}
    {x : SchemeDivisorPoint X} (h : SchemeAffineLocalBoundingPresentation g x.1) :
    x ∉ schemeDivisorCrit1 g :=
  h.toSchemeLocalBoundingPresentation.not_mem_schemeDivisorCrit1

end SchemeAffineLocalBoundingPresentation

end Pcf
