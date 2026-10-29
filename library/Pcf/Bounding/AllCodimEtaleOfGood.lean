/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimCoreGood
public import Pcf.Bounding.AllCodimChartStatement
public import Pcf.Bounding.AllCodimBlowupDominatingDivisor
public import Pcf.Bounding.NormalDominantLift
public import Pcf.Bounding.CodimOneFibre
public import Pcf.Bounding.ProperLiftSurjective
public import Pcf.Bounding.SchemePrimeToPTameDivisor
public import Pcf.Bounding.AllCodimCoreAssembly
public import Pcf.Bounding.AllCodimBlowupIsoOffCentre
public import Pcf.Bounding.ClosureStalk
public import Pcf.Bounding.ClosureStalkNormalization
public import Pcf.Bounding.PointRamificationIdx
public import Pcf.Bounding.PrimeToPMonodromyOpenSquare
public import Pcf.Bounding.AllCodimChartProof

/-!
# Étaleness of the normalized return over a good point

This proves `AllCodimEtaleOfGood` from the chart property: the valuation
argument of `latex/paper-p.tex`, proof of Theorem `thm:allcodim-normal`.
Given a divisor `Q₁` of the normalization of the periodic subvariety `A`
whose image `x` is good, a dominating exceptional divisor `d'` of the second
normalized blow-up, a codimension-one point `z` of the normalization of its
closure over `Q₁`, and its images `E₀` and `E` give the commuting square of
discrete valuation rings `𝒪_{A,x} → 𝒪_{D,E} → 𝒪_{D',E₀}` and
`𝒪_{A,x} → 𝒪_{A^ν,Q₁} → 𝒪_{Z,z}`. The chart makes the middle map
unramified, so the ramification index at `Q₁` divides the fibre multiplicity,
a power of `p`; prime-to-`p` monodromy forces it to be one.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Pcf.Bounding.AllCodimBlowup

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- A prime lying over `P` in an integral extension is minimal over the
extension of `P`. -/
theorem mem_minimalPrimes_map_of_liesOver {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal R) [P.IsPrime] (P' : Ideal S)
    [P'.IsPrime] (hP' : P'.under R = P) :
    P' ∈ (P.map (algebraMap R S)).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.map_le_of_le_comap (le_of_eq hP'.symm)⟩, ?_⟩
  intro Q ⟨hQ, hPQ⟩ hQP'
  by_contra hne
  have hlt : Q < P' := lt_of_le_of_ne hQP' (fun h => hne (h ▸ le_refl _))
  have := Ideal.IsIntegral.under_lt_under (R := R) hlt
  rw [hP'] at this
  have hle : P ≤ Q.under R := Ideal.map_le_iff_le_comap.mp hPQ
  exact absurd (lt_of_le_of_lt hle this) (lt_irrefl _)

#print axioms mem_minimalPrimes_map_of_liesOver

/-- The stalk ramification index of a map of point closures is the closure
fibre multiplicity of the ambient map. -/
theorem pointRamificationIdx_pointClosureSubschemeMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : X) (y : Y) (hy : f d = y) (e : (pointClosureIdealSheaf d).subscheme)
    (h : d ⤳ (pointClosureIdealSheaf d).subschemeι e) :
    pointRamificationIdx (pointClosureSubschemeMap f d y hy) e =
      closureFibreMultiplicity f h := by
  subst hy
  let g := pointClosureSubschemeMap f d (f d) rfl
  have hE : (pointClosureIdealSheaf (f d)).subschemeι (g e) =
      f ((pointClosureIdealSheaf d).subschemeι e) := by
    rw [← Scheme.Hom.comp_apply, pointClosureSubschemeMap_subschemeι,
      Scheme.Hom.comp_apply]
  let e₁ := pointClosureStalkEquiv' (f d) (g e) hE (h.map f.continuous)
  let e₂ := pointClosureStalkEquiv d e h
  have hcomm : (g.stalkMap e).hom.comp e₁.toRingHom =
      e₂.toRingHom.comp (stalkGenerizationQuotientMap f h) := by
    ext x
    exact pointClosureStalkEquiv_naturality d f e h x
  exact (ramificationIdx_maximalIdeal_eq_of_ringEquiv (stalkGenerizationQuotientMap f h)
    (g.stalkMap e).hom e₁ e₂ hcomm).symm

/-- The closure fibre multiplicity only depends on the endpoint up to
equality. -/
theorem closureFibreMultiplicity_eq_of_eq {X Y : Scheme.{u}} (β : Y ⟶ X) {d E E' : Y}
    (hE : E = E') (h : d ⤳ E) (h' : d ⤳ E') :
    closureFibreMultiplicity β h = closureFibreMultiplicity β h' := by
  subst hE
  rfl

/-- Prime-to-`p` monodromy depends only on the morphism. -/
theorem isPrimeToPMonodromyMap_of_eq (p : ℕ) {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {f g : X ⟶ Y} [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g] (e : f = g)
    (hf : IsPrimeToPMonodromyMap p f) : IsPrimeToPMonodromyMap p g := by
  subst e
  exact hf

/-- **L1** from the chart property. -/
theorem allCodimEtaleOfGood_of_chart (p : ℕ) (hp : p.Prime) (k : Type u) [Field k]
    [CharP k p] (hchart : AllCodimChartProperty p k) : AllCodimEtaleOfGood p k := by
  intro X _ _ _ _ s _ y hy B U _ hyU a ha h _ _ hfix hmono hbranch A F Q₁ hxU hgood
  letI : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite A k ((pointClosureIdealSheaf y).subschemeι ≫ s)
  letI : IsFinite (pointClosureReturnMap h y hfix) := pointClosureReturnMap_isFinite h y hfix
  letI : IsDominant (pointClosureReturnMap h y hfix) :=
    pointClosureReturnMap_isDominant h y hfix
  -- the affine comparison `R → S`
  let R := Γ(X, U)
  let P := allCodimCentrePrime U y hyU
  let V := finitePreimageAffine h U
  let S := Γ(X, V)
  letI : Algebra R S := (h.app U).hom.toAlgebra
  letI : Module.Finite R S := moduleFinite_finitePreimageAffine h U
  letI : FaithfulSMul R S := faithfulSMul_finitePreimageAffine h U
  let φ : R →+* S := algebraMap R S
  have hφinj : Function.Injective φ := FaithfulSMul.algebraMap_injective R S
  have hφfin : φ.Finite := RingHom.finite_algebraMap.mpr inferInstance
  have hyV : y ∈ (V : X.Opens) := by
    change h y ∈ (U : X.Opens)
    rw [hfix]
    exact hyU
  haveI : Nonempty (V : X.Opens) := ⟨⟨y, hyV⟩⟩
  let P' : Ideal S := (V.2.primeIdealOf ⟨y, hyV⟩).asIdeal
  have hP'under : P'.under R = P := by
    have hAlg : algebraMap R S = (h.appLE U V le_rfl).hom := by
      change (h.app U).hom = (h.appLE U V le_rfl).hom
      exact congr_arg CommRingCat.Hom.hom h.appLE_eq_app.symm
    change P'.comap (algebraMap R S) = P
    rw [hAlg]
    have hc := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (U : X.Opens) U.2 (V : X.Opens) V.2 le_rfl hyV)
    refine hc.trans ?_
    have hpt : (⟨h y, hyV⟩ : (U : X.Opens)) = ⟨y, hyU⟩ := Subtype.ext hfix
    rw [hpt]
  have hP'min : P' ∈ (P.map φ).minimalPrimes :=
    mem_minimalPrimes_map_of_liesOver P P' hP'under
  -- finite-type structures over `k`
  letI : Algebra k R :=
    ((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType k R := by
    apply RingHom.finiteType_algebraMap.mp
    change ((s.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  letI : Algebra k S :=
    ((s.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType k S := by
    apply RingHom.finiteType_algebraMap.mp
    change ((s.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).FiniteType
    exact (s.finiteType_appLE (isAffineOpen_top _) V.2 (by simp)).comp
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite.finiteType
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hPfg : P.FG := (IsNoetherian.noetherian P)
  have hPSfg : (P.map φ).FG := (IsNoetherian.noetherian (P.map φ))
  -- the two normalized blow-ups and the finite map between them
  let b : P.map φ := mappedCenterElement φ P a
  have hb : (b : S) ≠ 0 := fun hz => ha (hφinj (by simpa [b, mappedCenterElement] using hz))
  letI : IsIntegral (reesProj P) := reesProj_isIntegral P a ha
  letI : IsIntegral (reesProj (P.map φ)) := reesProj_isIntegral (P.map φ) b hb
  let Y := Palomar.normalization (reesProj P)
  let XS := Palomar.normalization (reesProj (P.map φ))
  let FS : XS ⟶ Y := normalizedReesProjMap φ hφinj hφfin P a ha
  letI : IsFinite FS := normalizedReesProjMap_isFinite k φ hφinj hφfin P hPfg a ha
  letI : IsDominant FS := normalizedReesProjMap_isDominant φ hφinj hφfin P a ha
  let βY : Y ⟶ Spec (.of R) := normalizedReesProjToSpec P a ha
  let αS : XS ⟶ Spec (.of S) := normalizedReesProjToSpec (P.map φ) b hb
  have hsq : FS ≫ βY = αS ≫ Spec.map (CommRingCat.ofHom φ) :=
    normalizedReesProjToSpec_comm φ hφinj hφfin P a ha
  -- a dominating exceptional divisor upstairs
  obtain ⟨d', hd'⟩ := exists_normalizedRees_divisorPoint_over_minimalPrime k (P.map φ) hPSfg
    b hb P' hP'min
  -- maps to the ambient scheme
  let ιU : Spec (.of R) ⟶ X := U.2.fromSpec
  let ιV : Spec (.of S) ⟶ X := V.2.fromSpec
  haveI : IsOpenImmersion ιV := V.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion ιU := U.2.isOpenImmersion_fromSpec
  have hUV : Spec.map (CommRingCat.ofHom φ) ≫ ιU = ιV ≫ h := by
    have hφ : CommRingCat.ofHom φ = h.appLE U V le_rfl := by
      change CommRingCat.ofHom (h.app U).hom = _
      rw [CommRingCat.ofHom_hom]
      exact h.appLE_eq_app.symm
    rw [hφ]
    exact IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 le_rfl
  let β' : Y ⟶ X := βY ≫ ιU
  let αX : XS ⟶ X := αS ≫ ιV
  have hsqX : FS ≫ β' = αX ≫ h := by
    simp only [β', αX, ← Category.assoc, hsq]
    rw [Category.assoc, hUV, Category.assoc]
  have hαd : αX d'.1 = y := by
    change ιV (αS d'.1) = y
    have h1 : αS d'.1 = V.2.primeIdealOf ⟨y, hyV⟩ := hd'
    rw [h1]
    exact V.2.fromSpec_primeIdealOf ⟨y, hyV⟩
  -- finite type over `k` of the upper blow-up
  letI : IsFinite (Palomar.normalizationMap (reesProj (P.map φ))) :=
    reesProj_absoluteNormalizationMap_isFinite k (P.map φ) hPSfg b hb
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) (P.map φ)) :=
    reesProjToSpecField_locallyOfFiniteType k (P.map φ) hPSfg
  let sXS : XS ⟶ Spec (.of k) :=
    Palomar.normalizationMap (reesProj (P.map φ)) ≫ reesProjToSpecField (k := k) (P.map φ)
  haveI : LocallyOfFiniteType sXS := inferInstance
  haveI : IsLocallyNoetherian XS := LocallyOfFiniteType.isLocallyNoetherian sXS
  letI : IsFinite (Palomar.normalizationMap (reesProj P)) :=
    reesProj_absoluteNormalizationMap_isFinite k P hPfg a ha
  letI : LocallyOfFiniteType (reesProjToSpecField (k := k) P) :=
    reesProjToSpecField_locallyOfFiniteType k P hPfg
  let sY : Y ⟶ Spec (.of k) :=
    Palomar.normalizationMap (reesProj P) ≫ reesProjToSpecField (k := k) P
  haveI : LocallyOfFiniteType sY := inferInstance
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  -- the closure `D'` of `d'`, its normalization `Z`, and the map to `A`
  let D' := (pointClosureIdealSheaf d'.1).subscheme
  let ιD : D' ⟶ XS := (pointClosureIdealSheaf d'.1).subschemeι
  let ψD : D' ⟶ A := pointClosureSubschemeMap αX d'.1 y hαd
  haveI : IsDominant ψD := pointClosureSubschemeMap_isDominant αX d'.1 y hαd
  letI : IsFinite (Palomar.normalizationMap D') :=
    schemeGlobalNormalizationMap_isFinite D' k (ιD ≫ sXS)
  let Z := Palomar.normalization D'
  let νD : Z ⟶ D' := Palomar.normalizationMap D'
  let ψ : Z ⟶ A := νD ≫ ψD
  haveI : IsDominant ψ := inferInstance
  let ψν : Z ⟶ Palomar.normalization A := normalDominantNormalizationLift ψ
  have hψν : ψν ≫ Palomar.normalizationMap A = ψ := normalDominantNormalizationLift_comp ψ
  -- the open `A ∩ V` and the universally closed corestriction of `ψD`
  let ιA : A ⟶ X := (pointClosureIdealSheaf y).subschemeι
  have hψD : ψD ≫ ιA = ιD ≫ αX := pointClosureSubschemeMap_subschemeι αX d'.1 y hαd
  let W' : A.Opens := ιA ⁻¹ᵁ (V : X.Opens)
  let j : W'.toScheme ⟶ A := W'.ι
  have hrangeD : Set.range ψD ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ιA (ψD w) ∈ (V : X.Opens)
    have h1 : ιA (ψD w) = αX (ιD w) := by
      rw [← Scheme.Hom.comp_apply, hψD, Scheme.Hom.comp_apply]
    rw [h1]
    have hmem : ιV (αS (ιD w)) ∈ Set.range ιV := ⟨_, rfl⟩
    rw [V.2.range_fromSpec] at hmem
    exact hmem
  let τ : D' ⟶ W'.toScheme := IsOpenImmersion.lift j ψD hrangeD
  have hτ : τ ≫ j = ψD := IsOpenImmersion.lift_fac j ψD hrangeD
  have hrangeW : Set.range (j ≫ ιA) ⊆ Set.range ιV := by
    rintro _ ⟨w, rfl⟩
    have hw : ιA (j w) ∈ (V : X.Opens) := w.2
    rw [V.2.range_fromSpec]
    exact hw
  let κ : W'.toScheme ⟶ Spec (.of S) := IsOpenImmersion.lift ιV (j ≫ ιA) hrangeW
  have hκ : κ ≫ ιV = j ≫ ιA := IsOpenImmersion.lift_fac ιV (j ≫ ιA) hrangeW
  haveI : IsSeparated κ := by
    have : IsSeparated (κ ≫ ιV) := by rw [hκ]; infer_instance
    exact IsSeparated.of_comp κ ιV
  have hτκ : τ ≫ κ = ιD ≫ αS := by
    rw [← cancel_mono ιV, Category.assoc, hκ, ← Category.assoc, hτ, hψD, Category.assoc]
  letI : IsProper (reesProjToSpec (P.map φ)) := reesProjToSpec_isProper (P.map φ) hPSfg
  haveI : UniversallyClosed (ιD ≫ αS) := by
    change UniversallyClosed (ιD ≫ (Palomar.normalizationMap (reesProj (P.map φ)) ≫
      reesProjToSpec (P.map φ)))
    infer_instance
  haveI : UniversallyClosed τ := by
    have : UniversallyClosed (τ ≫ κ) := by rw [hτκ]; infer_instance
    exact UniversallyClosed.of_comp_of_isSeparated τ κ
  -- a point of `Z` over `Q₁`, then a codimension-one one
  let νA := Palomar.normalizationMap A
  let q := pointClosureReturnMap h y hfix
  have hq : q ≫ ιA = ιA ≫ h := pointClosureSubschemeMap_subschemeι h y y hfix
  have hF : F ≫ νA = νA ≫ q := schemeGlobalNormalizationLift_comp q
  have hQ₁V : νA Q₁.1 ∈ Set.range j := by
    rw [Scheme.Opens.range_ι]
    change h (ιA (νA Q₁.1)) ∈ (U : X.Opens)
    have h1 : h (ιA (νA Q₁.1)) = ιA (νA (F Q₁.1)) := by
      rw [← Scheme.Hom.comp_apply, ← hq, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply νA q,
        ← hF, Scheme.Hom.comp_apply]
    rw [h1]
    exact hxU
  have hcommZ : ψν ≫ νA = νD ≫ τ ≫ j := by rw [hψν, hτ]
  obtain ⟨z₀, hz₀⟩ := mem_range_of_dominant_lift_finite_comp νA j νD τ ψν hcommZ Q₁.1 hQ₁V
  haveI : LocallyOfFiniteType (νD ≫ ιD ≫ sXS) := inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (νD ≫ ιD ≫ sXS)
  obtain ⟨z, hzQ, -⟩ := exists_schemeDivisorPoint_over ψν Q₁ z₀ hz₀
  -- the points `E₀ ∈ X_S` and `E ∈ Y`
  let e₀ : SchemeDivisorPoint D' :=
    ⟨νD z.1, coheight_apply_eq_one_of_finite_of_locallyOfFiniteType k (ιD ≫ sXS) νD z⟩
  let E₀ : XS := ιD e₀.1
  have hd'E₀ : d'.1 ⤳ E₀ := pointClosure_specializes d'.1 e₀.1
  have hcohE₀ : Order.coheight E₀ = 2 :=
    SchemeDivisorPoint.closureDivisor_coheight_of_finiteType k sXS d' e₀
  let d : SchemeDivisorPoint Y := d'.mapFiniteDominantNormal FS
  let E : Y := FS E₀
  have hdE : d.1 ⤳ E := hd'E₀.map FS.continuous
  have hcohE : Order.coheight E = 2 :=
    (coheight_apply_eq_of_finite_dominant_normal FS E₀).trans hcohE₀
  have hβd : β' d.1 = y := by
    change β' (FS d'.1) = y
    rw [← Scheme.Hom.comp_apply, hsqX, Scheme.Hom.comp_apply, hαd, hfix]
  have hαE₀ : αX E₀ = ιA (νA Q₁.1) := by
    change αX (ιD (νD z.1)) = _
    rw [← Scheme.Hom.comp_apply ιD αX, ← hψD, Scheme.Hom.comp_apply, ← hzQ,
      ← Scheme.Hom.comp_apply ψν νA, hψν]
    rfl
  have hβE : β' E = ιA (νA (F Q₁.1)) := by
    change β' (FS E₀) = _
    rw [← Scheme.Hom.comp_apply, hsqX, Scheme.Hom.comp_apply, hαE₀,
      ← Scheme.Hom.comp_apply ιA h, ← hq, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply νA q, ← hF, Scheme.Hom.comp_apply]
  -- the good-point data at `E`
  obtain ⟨hyx, hAdvr, hall⟩ := hgood
  have hgoodE : AllCodimGoodAt p β' y B d E hdE := hall d hβd E hdE hβE hcohE
  -- étaleness of `F_S` at divisors other than `d'` through `E`
  haveI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  haveI : IsIntegrallyClosed S := IsNormalScheme.component_integrallyClosed V
  have hunram : ∀ w : SchemeDivisorPoint XS, FS w.1 ⤳ FS E₀ → FS w.1 ≠ FS d'.1 →
      (FS.stalkMap w.1).hom.FormallyEtale := by
    intro w hwE hwd
    let wY : SchemeDivisorPoint Y := w.mapFiniteDominantNormal FS
    have hne : wY ≠ d := fun heq => hwd (congrArg Subtype.val heq)
    obtain ⟨hnot, hnotB⟩ := hgoodE.isolated wY hwE hne
    have hoffY : ¬ P ≤ (βY wY.1).asIdeal := by
      intro hle
      apply hnot
      have hsp : (⟨P, inferInstance⟩ : Spec (.of R)) ⤳ βY wY.1 :=
        (PrimeSpectrum.le_iff_specializes _ _).mp hle
      have hy' : ιU ⟨P, inferInstance⟩ = y := U.2.fromSpec_primeIdealOf ⟨y, hyU⟩
      rw [← hy']
      exact hsp.map ιU.continuous
    have hoffS : ¬ P.map φ ≤ (αS w.1).asIdeal := by
      intro hle
      apply hoffY
      have h1 : βY wY.1 = Spec.map (CommRingCat.ofHom φ) (αS w.1) := by
        change βY (FS w.1) = _
        rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
      rw [h1]
      intro r hr
      exact hle (Ideal.mem_map_of_mem φ hr)
    have hbijY : Function.Bijective (βY.stalkMap (FS w.1)).hom :=
      normalizedReesToSpec_stalkMap_bijective P a ha (FS w.1) hoffY
    have hbijS : Function.Bijective (αS.stalkMap w.1).hom :=
      normalizedReesToSpec_stalkMap_bijective (P.map φ) b hb w.1 hoffS
    rw [formallyEtale_stalkMap_iff_of_square FS αS βY (Spec.map (CommRingCat.ofHom φ)) hsq w.1
      hbijS hbijY]
    have hbijV : Function.Bijective (ιV.stalkMap (αS w.1)).hom :=
      ConcreteCategory.bijective_of_isIso _
    have hbijU : Function.Bijective
        (ιU.stalkMap (Spec.map (CommRingCat.ofHom φ) (αS w.1))).hom :=
      ConcreteCategory.bijective_of_isIso _
    rw [formallyEtale_stalkMap_iff_of_square (Spec.map (CommRingCat.ofHom φ)) ιV ιU h hUV
      (αS w.1) hbijV hbijU]
    have hcoh : Order.coheight (ιV (αS w.1)) = 1 := by
      rw [← coheight_eq_of_stalkMap_bijective ιV _ hbijV,
        ← coheight_eq_of_stalkMap_bijective αS _ hbijS]
      exact w.2
    apply hbranch ⟨ιV (αS w.1), hcoh⟩
    change h (ιV (αS w.1)) ∉ B
    rw [← Scheme.Hom.comp_apply ιV h, ← hUV, Scheme.Hom.comp_apply]
    have h2 : Spec.map (CommRingCat.ofHom φ) (αS w.1) = βY (FS w.1) := by
      rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    rw [h2]
    exact hnotB
  -- the chart at `E`
  letI : IsFinite (Spec.map (CommRingCat.ofHom φ)) := affineSpecMap_isFinite φ hφfin
  letI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := affineSpecMap_isDominant φ hφinj
  have hmonoSpec : IsPrimeToPMonodromyMap p (Spec.map (CommRingCat.ofHom φ)) := by
    exact isPrimeToPMonodromyMap_of_openImmersion_square p (Spec.map (CommRingCat.ofHom φ))
      ιV ιU h hUV hmono
  have hmonoFS : IsPrimeToPMonodromyMap p FS :=
    normalizedReesProjMap_primeToPMonodromy k p φ hφinj hφfin P hPfg a ha hmonoSpec
  obtain ⟨hD'dvr, hram1⟩ := hchart sY FS hmonoFS d' E₀ hd'E₀ hcohE₀ hgoodE.principal
    hgoodE.divisor_dvr hunram
  -- the closure `D` of `d` and the two paths `Z ⟶ A`
  let D := (pointClosureIdealSheaf d.1).subscheme
  let ιDY : D ⟶ Y := (pointClosureIdealSheaf d.1).subschemeι
  let ψD' : D' ⟶ D := pointClosureSubschemeMap FS d'.1 d.1 rfl
  let ψDA : D ⟶ A := pointClosureSubschemeMap β' d.1 y hβd
  have hψD'ι : ψD' ≫ ιDY = ιD ≫ FS := pointClosureSubschemeMap_subschemeι FS d'.1 d.1 rfl
  have hψDAι : ψDA ≫ ιA = ιDY ≫ β' := pointClosureSubschemeMap_subschemeι β' d.1 y hβd
  have hclos : ψD' ≫ ψDA = ψD ≫ q := by
    rw [← cancel_mono ιA]
    calc (ψD' ≫ ψDA) ≫ ιA = ιD ≫ FS ≫ β' := by
          rw [Category.assoc, hψDAι, ← Category.assoc, hψD'ι, Category.assoc]
      _ = ιD ≫ αX ≫ h := by rw [hsqX]
      _ = (ψD ≫ q) ≫ ιA := by
          rw [Category.assoc ψD q ιA, hq, ← Category.assoc ψD ιA h, hψD]
          simp only [αX, Category.assoc]
  have hpath : νD ≫ ψD' ≫ ψDA = ψν ≫ F ≫ νA := by
    rw [hclos, hF, ← Category.assoc ψν νA q, hψν, ← Category.assoc]
  -- the points on the two paths
  let eD : D := ψD' e₀.1
  have heDι : ιDY eD = E := by
    change ιDY (ψD' e₀.1) = FS (ιD e₀.1)
    rw [← Scheme.Hom.comp_apply, hψD'ι, Scheme.Hom.comp_apply]
  -- discrete valuation stalks
  haveI : IsDiscreteValuationRing (closureStalk XS hd'E₀) := hD'dvr
  haveI : IsDomain (D'.presheaf.stalk e₀.1) := inferInstance
  haveI : IsDiscreteValuationRing (D'.presheaf.stalk e₀.1) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (pointClosureStalkEquiv d'.1 e₀.1 hd'E₀)
  haveI : IsDiscreteValuationRing (closureStalk Y hdE) := hgoodE.divisor_dvr
  have hdeD : d.1 ⤳ ιDY eD := heDι ▸ hdE
  haveI : IsDomain (D.presheaf.stalk eD) := inferInstance
  haveI : IsDiscreteValuationRing (D.presheaf.stalk eD) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (pointClosureStalkEquiv' d.1 eD heDι hdE)
  haveI : IsIntegrallyClosed (D'.presheaf.stalk (νD z.1)) :=
    inferInstanceAs (IsIntegrallyClosed (D'.presheaf.stalk e₀.1))
  -- path one: `μ`
  have hνD : pointRamificationIdx νD z.1 = 1 :=
    pointRamificationIdx_eq_one_of_bijective νD z.1 (ConcreteCategory.bijective_of_isIso _)
  have hψD' : pointRamificationIdx ψD' e₀.1 = 1 := by
    rw [pointRamificationIdx_pointClosureSubschemeMap FS d'.1 d.1 rfl e₀.1 hd'E₀]
    exact hram1
  have hψDA : ∃ b : ℕ, pointRamificationIdx ψDA eD = p ^ b := by
    obtain ⟨b, hb'⟩ := hgoodE.primary
    refine ⟨b, ?_⟩
    rw [pointRamificationIdx_pointClosureSubschemeMap β' d.1 y hβd eD hdeD,
      closureFibreMultiplicity_eq_of_eq β' heDι hdeD hdE]
    exact hb'
  obtain ⟨b, hbμ⟩ := hψDA
  -- Noetherian sources make every map quasi-compact
  haveI : CompactSpace D' := by
    have : QuasiCompact (ιD ≫ αS) := by
      change QuasiCompact (ιD ≫ (Palomar.normalizationMap (reesProj (P.map φ)) ≫
        reesProjToSpec (P.map φ)))
      infer_instance
    exact QuasiCompact.compactSpace_of_compactSpace (ιD ≫ αS)
  haveI : IsLocallyNoetherian D' := LocallyOfFiniteType.isLocallyNoetherian (ιD ≫ sXS)
  haveI : IsNoetherian D' := ⟨⟩
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace νD
  haveI : IsNoetherian Z := ⟨⟩
  have hinjψD' : Function.Injective (ψD'.stalkMap e₀.1).hom := by
    haveI : IsDominant ψD' := pointClosureSubschemeMap_isDominant FS d'.1 d.1 rfl
    exact stalkMap_injective_of_dominant_integral ψD' e₀.1
  have hpath1 : pointRamificationIdx (νD ≫ ψD' ≫ ψDA) z.1 = p ^ b := by
    rw [pointRamificationIdx_comp νD (ψD' ≫ ψDA) z.1
        (ConcreteCategory.bijective_of_isIso (νD.stalkMap z.1)).1, hνD, mul_one]
    change pointRamificationIdx (ψD' ≫ ψDA) e₀.1 = p ^ b
    rw [pointRamificationIdx_comp ψD' ψDA e₀.1 hinjψD', hψD', mul_one]
    exact hbμ
  -- path two
  haveI : IsLocallyNoetherian (Palomar.normalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian (νA ≫ ιA ≫ s)
  let Qt : SchemeDivisorPoint (Palomar.normalization A) := Q₁.mapFiniteDominantNormal F
  haveI : IsDiscreteValuationRing ((Palomar.normalization A).presheaf.stalk (F Q₁.1)) := by
    change IsDiscreteValuationRing ((Palomar.normalization A).presheaf.stalk Qt.1)
    exact Qt.stalk_isDiscreteValuationRing
  haveI : IsDiscreteValuationRing ((Palomar.normalization A).presheaf.stalk (ψν z.1)) := by
    rw [hzQ]
    exact Q₁.stalk_isDiscreteValuationRing
  haveI : IsIntegrallyClosed (A.presheaf.stalk (νA (F Q₁.1))) := by
    haveI : IsDiscreteValuationRing (closureStalk X hyx) := hAdvr
    exact IsIntegrallyClosed.of_equiv (pointClosureStalkEquiv y (νA (F Q₁.1)) hyx)
  have hνA : pointRamificationIdx νA (F Q₁.1) = 1 :=
    pointRamificationIdx_eq_one_of_bijective νA (F Q₁.1)
      (ConcreteCategory.bijective_of_isIso (νA.stalkMap (F Q₁.1)))
  have hinjψν : Function.Injective (ψν.stalkMap z.1).hom :=
    stalkMap_injective_of_dominant_integral ψν z.1
  have hinjF : Function.Injective (F.stalkMap (ψν z.1)).hom :=
    stalkMap_injective_of_dominant_integral F (ψν z.1)
  have hpath2 : pointRamificationIdx (ψν ≫ F ≫ νA) z.1 =
      pointRamificationIdx F Q₁.1 * pointRamificationIdx ψν z.1 := by
    haveI : IsDiscreteValuationRing
        ((Palomar.normalization A).presheaf.stalk ((ψν ≫ F) z.1)) := by
      rw [Scheme.Hom.comp_apply, hzQ]
      infer_instance
    rw [← Category.assoc, pointRamificationIdx_comp (ψν ≫ F) νA z.1
        (by rw [Scheme.Hom.stalkMap_comp]; exact hinjψν.comp hinjF)]
    change pointRamificationIdx νA (F (ψν z.1)) * _ = _
    rw [hzQ, hνA, one_mul, pointRamificationIdx_comp ψν F z.1 hinjψν, hzQ]
  have hdvd : schemeDivisorRamificationIdx F Q₁ ∣ p ^ b := by
    rw [← hpath1, hpath, hpath2]
    exact Dvd.intro _ rfl
  -- prime-to-`p` monodromy of the normalized return
  have hy1 : schemePointIterate h 1 y = y := by
    simpa [schemePointIterate] using hfix
  letI : IsFinite (End.of h ^ 1).asHom := isFinite_end_pow h 1
  letI : IsDominant (End.of h ^ 1).asHom := isDominant_end_pow h 1
  letI : IsFinite (pointClosureReturnMap (End.of h ^ 1).asHom y hy1) :=
    pointClosureReturnMap_isFinite _ y hy1
  letI : IsDominant (pointClosureReturnMap (End.of h ^ 1).asHom y hy1) :=
    pointClosureReturnMap_isDominant _ y hy1
  have hmono1 := finiteType_pointClosureReturn_iterate_normalization_primeToPMonodromy p hp k
    h s hmono 1 one_pos y hy1
  have hret : pointClosureReturnMap (End.of h ^ 1).asHom y hy1 = q := by
    rw [← pointClosureReturnMap_iterate h y hfix 1, pow_one]
  have hmonoF : IsPrimeToPMonodromyMap p F :=
    isPrimeToPMonodromyMap_of_eq p (schemeGlobalNormalizationLift_congr hret) hmono1
  exact formallyEtale_of_ramificationIdx_dvd_pow_of_primeToP p hp k (νA ≫ ιA ≫ s) F hmonoF Q₁
    b hdvd

#print axioms allCodimEtaleOfGood_of_chart

/-- **L1.** The normalized return is étale over every good point. -/
theorem allCodimEtaleOfGood (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p] :
    AllCodimEtaleOfGood p k :=
  allCodimEtaleOfGood_of_chart p hp k (allCodimChartProperty p hp k)

#print axioms allCodimEtaleOfGood

end
end Pcf
