/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSingularImageGeometry
public import Pcf.PaperCharZero.SupportingBoundingClosed

/-!
# The singular-image-divisor example against the literal bounding theorem

For `latex/paper.tex`, Example `ex:branch-sing-B`, and
`Pcf.PaperCharZero.bounding_theorem`.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperSingularImageBounding

open CategoryTheory AlgebraicGeometry MvPolynomial
open Pcf.PaperCharZero

universe u

/-! ### Reduced closures in affine schemes -/

set_option backward.isDefEq.respectTransparency false in
/-- On an affine scheme, the reduced closure ideal sheaf of a point is the kernel of any
closed immersion of an integral scheme with image the closure of that point. -/
theorem pointClosureIdealSheaf_eq_ker {X Z : Scheme.{u}} [IsAffine X] [IsIntegral Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (x : X) (hx : Set.range i = closure {x}) :
    pointClosureIdealSheaf x = i.ker := by
  have hsupp : i.ker.support = ⟨closure {x}, isClosed_closure⟩ := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq, hx]
    rfl
  rw [pointClosureIdealSheaf, ← hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  have : Nonempty (i ⁻¹ᵁ (⊤ : X.Opens)) := by
    obtain ⟨z⟩ := (inferInstance : Nonempty Z)
    exact ⟨⟨z, trivial⟩⟩
  exact (RingHom.ker_isPrime _).radical.le

/-- The reduced closure subscheme of a point is any integral closed subscheme with that
image, compatibly with the inclusions. -/
def closureSubschemeIso {X Z : Scheme.{u}} [IsAffine X] [IsIntegral Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (x : X) (hx : Set.range i = closure {x}) :
    Z ≅ (pointClosureIdealSheaf x).subscheme :=
  have h : (pointClosureIdealSheaf x).subschemeι.ker = i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, pointClosureIdealSheaf_eq_ker i x hx]
  have := IsClosedImmersion.isIso_lift (pointClosureIdealSheaf x).subschemeι i h
  asIso (IsClosedImmersion.lift (pointClosureIdealSheaf x).subschemeι i h.le)

@[reassoc (attr := simp)]
theorem closureSubschemeIso_hom_ι {X Z : Scheme.{u}} [IsAffine X] [IsIntegral Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (x : X) (hx : Set.range i = closure {x}) :
    (closureSubschemeIso i x hx).hom ≫ (pointClosureIdealSheaf x).subschemeι = i := by
  simp [closureSubschemeIso]

/-! ### Stalk ramification for maps of affine schemes -/

set_option backward.isDefEq.respectTransparency false in
/-- For a finite injective extension `R → S` of Noetherian domains with `R` integrally
closed, the actual stalk ramification index of `Spec S → Spec R` at a codimension-one
point is the ring-theoretic ramification index of the corresponding prime. -/
theorem schemeDivisorRamificationIdx_specMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Module.Finite R S] [FaithfulSMul R S] (x : SchemeDivisorPoint (Spec (.of S))) :
    schemeDivisorRamificationIdx (Spec.map (CommRingCat.ofHom (algebraMap R S))) x =
      x.1.asIdeal.ramificationIdx R := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have : Surjective f := ⟨(RingHom.finite_algebraMap.mpr
    (inferInstance : Module.Finite R S)).to_isIntegral.comap_surjective
    (FaithfulSMul.algebraMap_injective R S)⟩
  have : IsNormalScheme (Spec (.of R)) := CharZeroPaperSmoothBranch.normal_spec R
  let p : PrimeSpectrum R := f x.1
  let Rp := (Spec (.of R)).presheaf.stalk (f x.1)
  let Sq := (Spec (.of S)).presheaf.stalk x.1
  let : Algebra R Rp := (StructureSheaf.toStalk R p).hom.toAlgebra
  let : Algebra S Sq := (StructureSheaf.toStalk S x.1).hom.toAlgebra
  let : Algebra Rp Sq := (f.stalkMap x.1).hom.toAlgebra
  let : Algebra R Sq := ((StructureSheaf.toStalk S x.1).hom.comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S Sq := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R Rp Sq := IsScalarTower.of_algebraMap_eq (fun r =>
    (AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom (algebraMap R S)) x.1 r).symm)
  let : IsLocalization.AtPrime Rp p.asIdeal := StructureSheaf.IsLocalization.to_stalk R p
  let : IsLocalization.AtPrime Sq x.1.asIdeal := StructureSheaf.IsLocalization.to_stalk S x.1
  let : IsLocalHom (algebraMap Rp Sq) :=
    show IsLocalHom (f.stalkMap x.1).hom from inferInstance
  let : IsDiscreteValuationRing Rp :=
    (x.mapFiniteDominantNormal f).stalk_isDiscreteValuationRing
  let : FaithfulSMul Rp Sq := (faithfulSMul_iff_algebraMap_injective Rp Sq).mpr
    (stalkMap_injective_of_dominant_integral f x.1)
  let : Module.Flat Rp Sq := inferInstance
  exact ramificationIdx_eq_of_localization_square p.asIdeal x.1.asIdeal

/-- Étaleness on an open neighborhood gives a formally étale stalk map. -/
theorem stalkMap_formallyEtale_of_etale_open {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (x : X) (hx : x ∈ V) (h : Etale (V.ι ≫ f)) : (f.stalkMap x).hom.FormallyEtale := by
  have h1 := Etale.stalkMap_formallyEtale h ⟨x, hx⟩
  have hc := Scheme.Hom.stalkMap_comp V.ι f ⟨x, hx⟩
  rw [hc] at h1
  have : IsIso (V.ι.stalkMap ⟨x, hx⟩) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  exact (formallyEtale_respectsIso.cancel_right_isIso (f.stalkMap (V.ι ⟨x, hx⟩))
    (V.ι.stalkMap ⟨x, hx⟩)).mp h1

/-! ### The example -/

open CharZeroPaperSingularImage CharZeroPaperSingularImageGeometry

variable {K : Type u} [Field K]

instance plane_isNormal' : IsNormalScheme (plane K) := CharZeroPaperSmoothBranch.normal_spec _

/-- The source divisor `A_z = V(y-zx)`. -/
def lineDivisorPoint (a z : K) : SchemeDivisorPoint (plane K) :=
  ⟨(⟨lineIdeal a z, lineIdeal_isPrime a z⟩ : PrimeSpectrum (MvPolynomial (Fin 2) K)),
    (idealHeight_eq_coheight (.of (MvPolynomial (Fin 2) K))
      ⟨lineIdeal a z, lineIdeal_isPrime a z⟩).symm.trans (lineIdeal_height a z)⟩

/-- `ex:branch-sing-B`, gap 2: the actual stalk ramification index of `f` along each
critical line is three. -/
theorem planeMap_schemeDivisorRamificationIdx_line [CharZero K] (a z : K) (ha : a ^ 2 = -3)
    (hz : h a z = 0) :
    schemeDivisorRamificationIdx (planeMap a) (lineDivisorPoint a z) = 3 := by
  have h1 := @schemeDivisorRamificationIdx_specMap (MvPolynomial (Fin 2) K) (SourceRing a)
    _ _ (sourceAlgebra a) _ _ _ _ (sourceRing_finite a ha) (sourceRing_faithful a ha)
    (lineDivisorPoint a z)
  exact h1.trans (lineIdeal_ramificationIdx a z ha hz)

/-- The restriction, as the spectrum of a single ring map. -/
def restrictionRingHom [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    BRing a →+* Polynomial K :=
  (CharZeroPaperConeBranch.squarePullback K).comp
    (bParam a (c4 a z) (c6 z) (line_coefficients_relation a z ha hz)).toRingHom

theorem restriction_eq_specMap [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    restriction a z ha hz = Spec.map (CommRingCat.ofHom (restrictionRingHom a z ha hz)) := by
  simp only [restriction, normalizationParam, CharZeroPaperConeBranch.squareMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem restrictionRingHom_mem_sq [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0)
    (b : BRing a) (hb : restrictionRingHom a z ha hz b ∈ CharZeroPaperConeBranch.axisIdeal K) :
    restrictionRingHom a z ha hz b ∈ Ideal.span {(Polynomial.X : Polynomial K) ^ 2} := by
  set q := bParam a (c4 a z) (c6 z) (line_coefficients_relation a z ha hz) b
  change Polynomial.expand K 2 q ∈ _ at hb ⊢
  rw [CharZeroPaperConeBranch.axisIdeal, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_expand (by norm_num)] at hb
  simp only [dvd_zero, ↓reduceIte, Nat.zero_div] at hb
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hb
  rw [Ideal.mem_span_singleton, hr, map_mul, Polynomial.expand_X]
  exact dvd_mul_right _ _

set_option backward.isDefEq.respectTransparency false in
/-- The restriction is not formally étale at the origin of the source line: its maximal
ideal is not generated by the pulled-back maximal ideal of `B`. -/
theorem restriction_stalk_not_formallyEtale [CharZero K] (a z : K) (ha : a ^ 2 = -3)
    (hz : h a z = 0) :
    ¬ ((restriction a z ha hz).stalkMap
      (CharZeroPaperConeBranch.axisDivisorPoint K).1).hom.FormallyEtale := by
  have hfin := restriction_isFinite a z ha hz
  rw [restriction_eq_specMap] at hfin ⊢
  intro hfe
  let ρ := restrictionRingHom a z ha hz
  let f := Spec.map (CommRingCat.ofHom ρ)
  let x : PrimeSpectrum (Polynomial K) := (CharZeroPaperConeBranch.axisDivisorPoint K).1
  let Rp := (cuspB a).presheaf.stalk (f x)
  let Sq := (line K).presheaf.stalk x
  let : Algebra Rp Sq := (f.stalkMap x).hom.toAlgebra
  have : Algebra.FormallyEtale Rp Sq := hfe
  have : Algebra.EssFiniteType Rp Sq := LocallyOfFiniteType.stalkMap f x
  have : IsLocalHom (algebraMap Rp Sq) := show IsLocalHom (f.stalkMap x).hom from inferInstance
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := Rp) (S := Sq)
  let : Algebra (BRing a) Rp := (StructureSheaf.toStalk (BRing a) (f x)).hom.toAlgebra
  let : Algebra (Polynomial K) Sq := (StructureSheaf.toStalk (Polynomial K) x).hom.toAlgebra
  have : IsLocalization.AtPrime Rp (f x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (BRing a) (f x)
  have : IsLocalization.AtPrime Sq x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (Polynomial K) x
  have hR : IsLocalRing.maximalIdeal Rp = (f x).asIdeal.map (algebraMap (BRing a) Rp) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal (f x).asIdeal Rp).symm
  have hS : IsLocalRing.maximalIdeal Sq = x.asIdeal.map (algebraMap (Polynomial K) Sq) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal Sq).symm
  have hcomp : (algebraMap Rp Sq).comp (algebraMap (BRing a) Rp) =
      (algebraMap (Polynomial K) Sq).comp ρ :=
    RingHom.ext fun r => AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom ρ) x r
  have hle : (f x).asIdeal.map ρ ≤ Ideal.span {(Polynomial.X : Polynomial K) ^ 2} := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact restrictionRingHom_mem_sq a z ha hz b hb
  have hmap : IsLocalRing.maximalIdeal Sq =
      ((f x).asIdeal.map ρ).map (algebraMap (Polynomial K) Sq) := by
    rw [← hmax, hR, Ideal.map_map, hcomp, ← Ideal.map_map]
  have hS' : IsLocalRing.maximalIdeal Sq =
      (Ideal.span {(Polynomial.X : Polynomial K)}).map (algebraMap (Polynomial K) Sq) := hS
  have hsq : IsLocalRing.maximalIdeal Sq ^ 2 =
      (Ideal.span {(Polynomial.X : Polynomial K) ^ 2}).map (algebraMap (Polynomial K) Sq) := by
    rw [hS', ← Ideal.map_pow, Ideal.span_singleton_pow]
  have hmsq : IsLocalRing.maximalIdeal Sq ≤ IsLocalRing.maximalIdeal Sq ^ 2 := by
    rw [hsq]
    conv_lhs => rw [hmap]
    exact Ideal.map_mono hle
  have : IsNoetherianRing Sq := IsLocalization.isNoetherianRing x.asIdeal.primeCompl Sq
    inferInstance
  have hbot : IsLocalRing.maximalIdeal Sq = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal Sq)
    · exact IsNoetherian.noetherian _
    · rw [smul_eq_mul, ← pow_two]
      exact hmsq
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hX : algebraMap (Polynomial K) Sq Polynomial.X ∈ IsLocalRing.maximalIdeal Sq := by
    rw [hS]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)
  rw [hbot, Ideal.mem_bot] at hX
  have hinj : Function.Injective (algebraMap (Polynomial K) Sq) :=
    IsLocalization.injective Sq x.asIdeal.primeCompl_le_nonZeroDivisors
  exact Polynomial.X_ne_zero (hinj (hX.trans (map_zero _).symm))

/-! ### The divisors `A_z` and `B` as reduced closures -/

theorem linePullback_ker (z : K) :
    RingHom.ker (linePullback z).toRingHom = Ideal.span {lineForm z} := by
  have hcomp : ((Polynomial.aeval (Polynomial.C z * Polynomial.X : Polynomial K)).restrictScalars
      K).comp (CharZeroPaperCuspBranch.toTower K) = linePullback z := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [CharZeroPaperCuspBranch.toTower, linePullback]
  have hl : CharZeroPaperCuspBranch.toTower K (lineForm z) =
      Polynomial.X - Polynomial.C (Polynomial.C z * Polynomial.X) := by
    simp [lineForm, CharZeroPaperCuspBranch.toTower, Polynomial.algebraMap_eq]
  ext P
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change linePullback z P = 0 ↔ _
  rw [← hcomp, AlgHom.comp_apply, AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval,
    ← Polynomial.IsRoot.def, ← Polynomial.dvd_iff_isRoot, ← hl]
  exact map_dvd_iff (CharZeroPaperCuspBranch.planeTowerEquiv K)

theorem sourceLine_range (a z : K) :
    Set.range (sourceLine z) = closure {(lineDivisorPoint a z).1} := by
  change Set.range (PrimeSpectrum.comap (linePullback z).toRingHom) = _
  rw [range_comap_of_surjective _ _ (linePullback_surjective z), linePullback_ker]
  change _ = closure ({(⟨lineIdeal a z, lineIdeal_isPrime a z⟩ :
    PrimeSpectrum (MvPolynomial (Fin 2) K))} : Set (PrimeSpectrum (MvPolynomial (Fin 2) K)))
  rw [PrimeSpectrum.closure_singleton]
  rfl

/-- The reduced closure of `A_z` is the line `Spec k[t]`. -/
def aIso (a z : K) : line K ≅ (pointClosureIdealSheaf (lineDivisorPoint a z).1).subscheme :=
  closureSubschemeIso (sourceLine z) _ (sourceLine_range a z)

theorem planeMap_lineDivisorPoint [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    planeMap a (lineDivisorPoint a z).1 = (bDivisorPoint a ha).1 :=
  planeMap_linePoint a z ha hz

/-- The reduced closure of `B = f(A_z)` is the explicit cusp `Spec k[U,V]/(U³-12aV²)`. -/
def bIso [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    cuspB a ≅ (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subscheme :=
  have := cuspB_isIntegral a ha
  closureSubschemeIso (cuspBImmersion a) _ (by
    rw [cuspBImmersion_range a ha, planeMap_lineDivisorPoint a z ha hz])

theorem lineDivisor_map [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    haveI := planeMap_isFinite a ha
    haveI := planeMap_surjective a ha
    (lineDivisorPoint a z).mapFiniteDominantNormal (planeMap a) = bDivisorPoint a ha := by
  have := planeMap_isFinite a ha
  have := planeMap_surjective a ha
  exact Subtype.ext (planeMap_lineDivisorPoint a z ha hz)

/-- `g = f|_A`, under the two identifications, is the explicit restriction. -/
theorem closureMap_square [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    haveI := planeMap_isFinite a ha
    haveI := planeMap_surjective a ha
    (aIso a z).hom ≫ (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) =
      restriction a z ha hz ≫ (bIso a z ha hz).hom := by
  have := planeMap_isFinite a ha
  have := planeMap_surjective a ha
  have := cuspB_isIntegral a ha
  apply (cancel_mono (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι).mp
  have e1 : (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) ≫
      (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι =
      (pointClosureIdealSheaf (lineDivisorPoint a z).1).subschemeι ≫ planeMap a :=
    pointClosureSubschemeMap_subschemeι _ _ _ _
  have e2 : (aIso a z).hom ≫ (pointClosureIdealSheaf (lineDivisorPoint a z).1).subschemeι =
      sourceLine z := closureSubschemeIso_hom_ι _ _ _
  have e3 : (bIso a z ha hz).hom ≫
      (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι =
      cuspBImmersion a := closureSubschemeIso_hom_ι (cuspBImmersion a) _ (by
        rw [cuspBImmersion_range a ha, planeMap_lineDivisorPoint a z ha hz])
  calc _ = (aIso a z).hom ≫ ((lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) ≫
        (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι) :=
          Category.assoc _ _ _
    _ = ((aIso a z).hom ≫ (pointClosureIdealSheaf (lineDivisorPoint a z).1).subschemeι) ≫
        planeMap a := by rw [e1, Category.assoc]
    _ = sourceLine z ≫ planeMap a := by rw [e2]
    _ = restriction a z ha hz ≫ cuspBImmersion a := (restriction_square a z ha hz).symm
    _ = restriction a z ha hz ≫ ((bIso a z ha hz).hom ≫
        (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι) := by rw [e3]
    _ = _ := (Category.assoc _ _ _).symm

theorem squareMap_axis :
    CharZeroPaperConeBranch.squareMap K (CharZeroPaperConeBranch.axisDivisorPoint K).1 =
      (CharZeroPaperConeBranch.axisDivisorPoint K).1 := by
  apply PrimeSpectrum.ext
  ext p
  change Polynomial.expand K 2 p ∈ CharZeroPaperConeBranch.axisIdeal K ↔
    p ∈ CharZeroPaperConeBranch.axisIdeal K
  simp only [CharZeroPaperConeBranch.axisIdeal, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_expand (show 0 < 2 by norm_num)]
  simp

theorem restriction_axis [CharZero K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    restriction a z ha hz (CharZeroPaperConeBranch.axisDivisorPoint K).1 = originB a := by
  rw [restriction, Scheme.Hom.comp_apply, squareMap_axis, normalizationParam_origin]

/-! ### The literal statements -/

set_option backward.isDefEq.respectTransparency false in
/-- `ex:branch-sing-B` against `bounding_theorem`: the origin of `B` lies in the exceptional
set `Σ = (B ∩ Z) ∪ (B ∩ Sing Y) ∪ Sing B` for `f` and the source divisor `A_z`, and it lies
only in the `Sing B` term. -/
theorem origin_mem_boundingExceptionalSet_only_singB [CharZero K] [IsAlgClosed K]
    (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    haveI := planeMap_isFinite a ha
    haveI := planeMap_surjective a ha
    (bIso a z ha hz).hom (originB a) ∈
        boundingExceptionalSet (planeMap a)
          ((lineDivisorPoint a z).mapFiniteDominantNormal (planeMap a)) ∧
      (bIso a z ha hz).hom (originB a) ∉
        (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι ⁻¹'
          divisorSupport (schemeReducedFiberBranch (planeMap a) \
            {(lineDivisorPoint a z).mapFiniteDominantNormal (planeMap a)}) ∧
      (bIso a z ha hz).hom (originB a) ∉
        (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι ⁻¹'
          stalkSingularLocus (plane K) ∧
      (bIso a z ha hz).hom (originB a) ∈
        stalkSingularLocus
          (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subscheme := by
  have := planeMap_isFinite a ha
  have := planeMap_surjective a ha
  have hsing : (bIso a z ha hz).hom (originB a) ∈
      stalkSingularLocus
        (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subscheme := by
    intro hreg
    have : IsIso ((bIso a z ha hz).hom.stalkMap (originB a)) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have : IsRegularLocalRing ((cuspB a).presheaf.stalk (originB a)) :=
      IsRegularLocalRing.of_ringEquiv
        (asIso ((bIso a z ha hz).hom.stalkMap (originB a))).commRingCatIsoToRingEquiv
    exact originB_mem_singularLocus a ha this
  have hZ : divisorSupport (schemeReducedFiberBranch (planeMap a) \
      {(lineDivisorPoint a z).mapFiniteDominantNormal (planeMap a)}) = ∅ := by
    rw [lineDivisor_map a z ha hz]
    exact otherBranch_empty a ha
  refine ⟨Or.inr hsing, ?_, ?_, hsing⟩
  · intro hmem
    rw [Set.mem_preimage, hZ] at hmem
    exact hmem
  · intro hmem
    rw [Set.mem_preimage, plane_singularLocus_empty] at hmem
    exact hmem

/-- `ex:branch-sing-B` against `bounding_theorem`: the restriction `g` is not étale at the
integral effective divisor of `A_z` over the origin of `B`. -/
theorem closureMap_not_etale_over_origin [CharZero K] (a z : K) (ha : a ^ 2 = -3)
    (hz : h a z = 0) :
    haveI := planeMap_isFinite a ha
    haveI := planeMap_surjective a ha
    ∃ Q : SchemeDivisorPoint (pointClosureIdealSheaf (lineDivisorPoint a z).1).subscheme,
      (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) Q.1 =
          (bIso a z ha hz).hom (originB a) ∧
        ¬ ∃ V : (pointClosureIdealSheaf (lineDivisorPoint a z).1).subscheme.Opens, Q.1 ∈ V ∧
          Etale (V.ι ≫ (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a)) := by
  have := planeMap_isFinite a ha
  have := planeMap_surjective a ha
  let x := (CharZeroPaperConeBranch.axisDivisorPoint K).1
  let g := (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a)
  have hsq := closureMap_square a z ha hz
  refine ⟨⟨(aIso a z).hom x, (AlgebraicGeometry.coheight_eq_of_isOpenImmersion
    (aIso a z).hom).trans (CharZeroPaperConeBranch.axisDivisorPoint K).2⟩, ?_, ?_⟩
  · change g ((aIso a z).hom x) = _
    rw [← Scheme.Hom.comp_apply, hsq]
    exact congrArg (fun p => (bIso a z ha hz).hom p) (restriction_axis a z ha hz)
  · rintro ⟨V, hV, het⟩
    let V' := (aIso a z).hom ⁻¹ᵁ V
    have hxV' : x ∈ V' := hV
    have hr : ((aIso a z).hom ∣_ V) ≫ V.ι = V'.ι ≫ (aIso a z).hom := morphismRestrict_ι _ _
    have h1 : V'.ι ≫ restriction a z ha hz =
        (((aIso a z).hom ∣_ V) ≫ (V.ι ≫ g)) ≫ (bIso a z ha hz).inv := by
      calc V'.ι ≫ restriction a z ha hz =
            (V'.ι ≫ restriction a z ha hz ≫ (bIso a z ha hz).hom) ≫ (bIso a z ha hz).inv := by
              simp
        _ = (V'.ι ≫ (aIso a z).hom ≫ g) ≫ (bIso a z ha hz).inv :=
              congrArg (fun φ => (V'.ι ≫ φ) ≫ (bIso a z ha hz).inv) hsq.symm
        _ = (((aIso a z).hom ∣_ V ≫ V.ι) ≫ g) ≫ (bIso a z ha hz).inv := by
              rw [hr, Category.assoc]
        _ = _ := by rw [Category.assoc]
    have e0 : Etale (V.ι ≫ g) := het
    have e1 : Etale ((aIso a z).hom ∣_ V) := inferInstance
    have e2 : Etale (((aIso a z).hom ∣_ V) ≫ (V.ι ≫ g)) := inferInstance
    have e3 : Etale (bIso a z ha hz).inv := inferInstance
    have het' : Etale (V'.ι ≫ restriction a z ha hz) := by
      rw [h1]
      exact @Etale.etale_comp _ _ _ _ _ e2 e3
    exact restriction_stalk_not_formallyEtale a z ha hz
      (stalkMap_formallyEtale_of_etale_open _ V' x hxV' het')

/-- `ex:branch-sing-B`: the `Sing(B)` term of `Σ` in `bounding_theorem` cannot be dropped.
For `f = (F,G)`, the source divisor `A_z` and `g = f|_{A_z}`, there is an integral effective
divisor `Q` of `A_z` over the origin `o` of `B` at which `g` is not étale; `o` lies in `Σ`
and in `Sing B`, but the image of the closure of `Q` is not contained in
`(B ∩ Z) ∪ (B ∩ Sing Y)`. So the étaleness conclusion of `bounding_theorem` would be false
with the third term removed. -/
theorem singB_term_cannot_be_dropped [CharZero K] [IsAlgClosed K] (a z : K) (ha : a ^ 2 = -3)
    (hz : h a z = 0) :
    haveI := planeMap_isFinite a ha
    haveI := planeMap_surjective a ha
    ∃ Q : SchemeDivisorPoint (pointClosureIdealSheaf (lineDivisorPoint a z).1).subscheme,
      (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) Q.1 ∈
          boundingExceptionalSet (planeMap a)
            ((lineDivisorPoint a z).mapFiniteDominantNormal (planeMap a)) ∧
        (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) Q.1 ∈
          stalkSingularLocus
            (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subscheme ∧
        ¬ ((lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a) ''
            closure {Q.1} ⊆
          (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι ⁻¹'
              divisorSupport (schemeReducedFiberBranch (planeMap a) \
                {(lineDivisorPoint a z).mapFiniteDominantNormal (planeMap a)}) ∪
            (pointClosureIdealSheaf (planeMap a (lineDivisorPoint a z).1)).subschemeι ⁻¹'
              stalkSingularLocus (plane K)) ∧
        ¬ ∃ V : (pointClosureIdealSheaf (lineDivisorPoint a z).1).subscheme.Opens, Q.1 ∈ V ∧
          Etale (V.ι ≫ (lineDivisorPoint a z).closureMapFiniteDominantNormal (planeMap a)) := by
  have := planeMap_isFinite a ha
  have := planeMap_surjective a ha
  obtain ⟨Q, hQ, hne⟩ := closureMap_not_etale_over_origin a z ha hz
  obtain ⟨hmem, hZ, hY, hsing⟩ := origin_mem_boundingExceptionalSet_only_singB a z ha hz
  refine ⟨Q, hQ ▸ hmem, hQ ▸ hsing, ?_, hne⟩
  intro hsub
  have h := hsub ⟨Q.1, subset_closure rfl, rfl⟩
  rw [hQ] at h
  rcases h with h | h
  · exact hZ h
  · exact hY h


#print axioms pointClosureIdealSheaf_eq_ker
#print axioms closureSubschemeIso
#print axioms closureSubschemeIso_hom_ι
#print axioms schemeDivisorRamificationIdx_specMap
#print axioms stalkMap_formallyEtale_of_etale_open
#print axioms planeMap_schemeDivisorRamificationIdx_line
#print axioms restriction_eq_specMap
#print axioms restriction_stalk_not_formallyEtale
#print axioms linePullback_ker
#print axioms sourceLine_range
#print axioms aIso
#print axioms bIso
#print axioms lineDivisor_map
#print axioms closureMap_square
#print axioms restriction_axis
#print axioms origin_mem_boundingExceptionalSet_only_singB
#print axioms closureMap_not_etale_over_origin
#print axioms singB_term_cannot_be_dropped

end Pcf.Examples.CharZeroPaperSingularImageBounding
