/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedLift
public import Pcf.Examples.PaperP.PinchedNormalization
public import Pcf.Examples.PaperP.FrobeniusPinchingPCF
public import Pcf.Bounding.AllSubvarietyCharZeroSeparable
public import Pcf.Examples.PaperP.BasilicaAffinePCF

/-!
# `g = f|_B` is PCF in the normalized weighted sense

For `paper-p.tex`, Example `ex:pinched`: "its normalization is `𝔸¹_z`, and `g` is
`p(z) ↦ p(z²)`, with lift `z ↦ z²`. The branch locus of `z ↦ z²` is the fixed point `0`, so
`g` is PCF, as Theorem `thm:general` predicts."

Here `B = Spec R_B`, `R_B = {p ∈ k[z] : p(2) = p(-2)}`, and `g = gScheme` is the actual affine
scheme map of `p ↦ p(z²)`.

* `node_isFractionRing`: `R_B ⊆ k[z]` is birational (`(z² - 4)·k[z] ⊆ R_B`).
* `normIso`: the library's absolute normalization of `B` is `𝔸¹_z`, over `B`
  (`BirationalAffineNormalization.normalizationIsoCover`).
* `lift_eq_canonical`: the canonical normalized lift of `g` is `z ↦ z²`.
* `weightedBranchPointSet_eq`: the normalized weighted branch divisors of `g` are exactly the
  image `ν_B(0)` of `z = 0`, and `g` fixes it (`gScheme_zeroB`).
* `weightedPostcriticalPointSet_eq`: `PC(g) = {ν_B(0)}`.
* `g_isWeightedNormalizedPCFDownstairs`, `g_isSeparableNormalizedPCF`: `g` is PCF in the sense
  of `def:pcf` (generic separability holds in characteristic zero).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedNodePCF

open AlgebraicGeometry CategoryTheory Polynomial
open Pcf.Examples.PaperP.PinchedNodeFibre

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "RB" => NodeRing k

/-- The conductor element `z² - 4` of `R_B`. -/
noncomputable def condElt : RB := mk k ((X ^ 2 - 4) * 1) (mem_of_dvd k 1)

theorem condElt_ne_zero : condElt k ≠ 0 := by
  intro h
  have h' := congrArg (val k) h
  change ((X ^ 2 - 4) * 1 : k[X]) = 0 at h'
  have := congrArg (Polynomial.eval 0) h'
  norm_num at this

/-- `R_B ⊆ k[z]` is birational. -/
instance node_isFractionRing : IsFractionRing RB (FractionRing k[X]) :=
  PinchedNormalization.isFractionRing_of_conductor (condElt k) (condElt_ne_zero k)
    (fun s => ⟨mk k ((X ^ 2 - 4) * s) (mem_of_dvd k s), by
      change ((X ^ 2 - 4) * s : k[X]) = ((X ^ 2 - 4) * 1) * s
      ring⟩)

/-- `B`. -/
noncomputable abbrev Bs := Spec (.of RB)

/-- The normalization of `B` is `𝔸¹_z`. -/
noncomputable def normIso : Pcf.Palomar.normalization (Bs k) ≅ Spec (.of k[X]) :=
  BirationalAffineNormalization.normalizationIsoCover RB k[X]

theorem normIso_hom_comp :
    (normIso k).hom ≫ PinchedLift.nuB k = Pcf.Palomar.normalizationMap (Bs k) :=
  BirationalAffineNormalization.normalizationIsoCover_hom_comp RB k[X]

instance normalizationFinite : IsFinite (Pcf.Palomar.normalizationMap (Bs k)) :=
  BirationalAffineNormalization.normalizationMap_isFinite RB k[X]

/-- The candidate lift `iso⁻¹ ∘ (z ↦ z²) ∘ iso`. -/
noncomputable def lift : Pcf.Palomar.normalization (Bs k) ⟶ Pcf.Palomar.normalization (Bs k) :=
  (normIso k).hom ≫ PinchedLift.liftMap k ≫ (normIso k).inv

theorem lift_comp_normalizationMap :
    lift k ≫ Pcf.Palomar.normalizationMap (Bs k) =
      Pcf.Palomar.normalizationMap (Bs k) ≫ gScheme k := by
  rw [← normIso_hom_comp, lift]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [PinchedLift.liftMap_comp_nuB]

theorem spec_ext {L : CommRingCat} (hL : IsField L) (u v : Spec L ⟶ Spec (.of k[X]))
    (c : RB →+* L) (hc : Function.Injective c)
    (hu : u ≫ PinchedLift.nuB k = Spec.map (CommRingCat.ofHom c))
    (hv : v ≫ PinchedLift.nuB k = Spec.map (CommRingCat.ofHom c)) : u = v := by
  letI : Field L := hL.toField
  obtain ⟨a, rfl⟩ := Spec.map_surjective u
  obtain ⟨b, rfl⟩ := Spec.map_surjective v
  unfold PinchedLift.nuB at hu hv
  rw [← Spec.map_comp] at hu hv
  have ha := congrArg CommRingCat.Hom.hom (Spec.map_injective hu)
  have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective hv)
  congr 1
  apply CommRingCat.hom_ext
  apply BirationalAffineNormalization.ringHom_ext_of_birational RB k[X]
  · exact ha.trans hb.symm
  · change Function.Injective ((CommRingCat.ofHom (algebraMap RB k[X]) ≫ a).hom)
    rw [Spec.map_injective hu]
    exact hc

/-- The generic inclusion of `B` composed with `g`, as a ring map. -/
noncomputable def genericRing : RB →+* (Bs k).functionField :=
  ((Scheme.ΓSpecIso (.of RB)).inv ≫
    (Bs k).presheaf.germ ⊤ (genericPoint (Bs k)) trivial).hom.comp (gStar k)

theorem genericRing_injective : Function.Injective (genericRing k) := by
  intro a b h
  apply gStar_injective k
  have hg := germ_injective_of_isIntegral (Bs k) (U := ⊤) (genericPoint (Bs k)) trivial
  have h' := hg h
  exact (Scheme.ΓSpecIso (.of RB)).commRingCatIsoToRingEquiv.symm.injective h'

theorem genericIncl_g :
    Pcf.schemeGenericInclusion (Bs k) ≫ gScheme k =
      Spec.map (CommRingCat.ofHom (genericRing k)) := by
  unfold Pcf.schemeGenericInclusion gScheme genericRing
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

theorem lift_generic :
    Pcf.Palomar.genericToNormalization (Bs k) ≫ lift k =
      Pcf.schemeGenericMorphism (gScheme k) ≫ Pcf.Palomar.genericToNormalization (Bs k) := by
  apply (cancel_mono (normIso k).hom).mp
  have hG : Pcf.Palomar.genericToNormalization (Bs k) ≫ (normIso k).hom =
      BirationalAffineNormalization.genericToCover RB k[X] :=
    BirationalAffineNormalization.genericToNormalization_normalizationToCover _ _
  simp only [lift, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hG]
  have hgc := BirationalAffineNormalization.genericToCover_comp RB k[X]
  apply spec_ext k (Field.toIsField _) _ _ (genericRing k) (genericRing_injective k)
  · rw [Category.assoc, PinchedLift.liftMap_comp_nuB, ← Category.assoc]
    erw [hgc]
    rw [genericIncl_g]
  · rw [Category.assoc]
    erw [hgc]
    rw [Pcf.schemeGenericMorphism_comp, genericIncl_g]

/-- **The canonical lift of `g` to the normalization `𝔸¹_z` is `z ↦ z²`.** -/
theorem lift_eq_canonical : lift k = Pcf.schemeGlobalNormalizationMorphism (gScheme k) :=
  Pcf.schemeGlobalNormalizationMorphism_unique _ _ (lift_comp_normalizationMap k)
    (lift_generic k)

/-! ### Branch divisors -/

theorem lift_finite : IsFinite (lift k) := by
  unfold lift; infer_instance

theorem lift_stalk_formallyEtale (z : Pcf.Palomar.normalization (Bs k))
    (hz : (X : k[X]) ∉ ((normIso k).hom z).asIdeal) :
    ((lift k).stalkMap z).hom.FormallyEtale := by
  unfold lift
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
  refine RingHom.FormallyEtale.comp ?_ (FrobeniusPinchingPCF.iso_stalk_formallyEtale _ _)
  exact RingHom.FormallyEtale.comp (FrobeniusPinchingPCF.iso_stalk_formallyEtale _ _)
    (AffineLociBridge.stalk_formallyEtale_of_isStacksEtaleAt _ _
      (QuadricConeRestriction.schemeMap_isStacksEtaleAt_of_X_notMem k _ hz))

/-- The point `ν_B(0)` of `B`. -/
noncomputable def zeroB : Bs k := PinchedLift.nuB k (NodalCubic.paramPoint k 0)

theorem gScheme_zeroB : gScheme k (zeroB k) = zeroB k := by
  unfold zeroB
  rw [← Scheme.Hom.comp_apply, ← PinchedLift.liftMap_comp_nuB, Scheme.Hom.comp_apply,
    PinchedLift.liftMap_origin]

theorem delta_gt_one_zero (d : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Bs k)))
    (hd : 1 < Pcf.schemeDivisorDelta (lift k) d) :
    (normIso k).hom d.1 = NodalCubic.paramPoint k 0 := by
  haveI := lift_finite k
  by_cases h0 : (X : k[X]) ∈ ((normIso k).hom d.1).asIdeal
  · exact NodalCubic.eq_paramPoint_of_mem k _ 0 (by simpa using h0)
  exfalso
  have := Pcf.schemeDivisorDelta_eq_one_of_formallyEtale (lift k) d
    (lift_stalk_formallyEtale k d.1 h0)
  omega

/-- The normalized weighted branch divisors of `g` lie over `ν_B(0)`. -/
theorem weightedBranchPointSet_subset :
    Pcf.weightedBranchPointSet (gScheme k) ⊆ {zeroB k} := by
  have hF := (lift_eq_canonical k).symm
  rintro q ⟨r, ⟨d, hdr, hd⟩, rfl⟩
  rw [hF] at hd
  have hi := delta_gt_one_zero k d hd
  subst hdr
  rw [Set.mem_singleton_iff]
  change Pcf.Palomar.normalizationMap (Bs k)
    (Pcf.schemeGlobalNormalizationMorphism (gScheme k) d.1) = zeroB k
  rw [hF, ← Scheme.Hom.comp_apply, lift_comp_normalizationMap, Scheme.Hom.comp_apply,
    ← normIso_hom_comp, Scheme.Hom.comp_apply, hi]
  exact gScheme_zeroB k

local instance lineNormal : Pcf.IsNormalScheme (Spec (.of k[X])) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro p
  haveI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of k[X]) p).symm.commRingCatIsoToRingEquiv

/-- `z ↦ z²` has weighted local degree `> 1` at `z = 0`: the affine basilica map
`z ↦ z² - 1` is `z ↦ z²` followed by a translation, and has degree `> 1` there. -/
theorem liftMap_delta_zero :
    1 < Pcf.schemeDivisorDelta (PinchedLift.liftMap k) (NodalCubic.paramDivisor k 0) := by
  haveI := BasilicaAffine.schemeMap_finite k
  have h := (BasilicaAffine.divisorDelta_gt_one_iff k (NodalCubic.paramDivisor k 0)).2 rfl
  rw [BasilicaAffine.schemeMap_factor, Pcf.schemeDivisorDelta_comp_of_isFinite,
    Pcf.schemeDivisorDelta_of_isIso, one_mul] at h
  exact h

/-- The divisor of the normalization of `B` over `z = 0`. -/
noncomputable def zeroDiv : Pcf.SchemeDivisorPoint (Pcf.Palomar.normalization (Bs k)) :=
  ⟨(normIso k).inv (NodalCubic.paramPoint k 0),
    (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (normIso k).inv).trans
      (NodalCubic.paramPoint_coheight k 0)⟩

theorem normIso_hom_zeroDiv : (normIso k).hom (zeroDiv k).1 = NodalCubic.paramPoint k 0 := by
  change ((normIso k).inv ≫ (normIso k).hom) (NodalCubic.paramPoint k 0) = _
  rw [Iso.inv_hom_id]
  rfl

theorem lift_delta_zeroDiv : 1 < Pcf.schemeDivisorDelta (lift k) (zeroDiv k) := by
  haveI := lift_finite k
  have e : lift k = (normIso k).hom ≫ (PinchedLift.liftMap k ≫ (normIso k).inv) := rfl
  rw [e, Pcf.schemeDivisorDelta_comp_of_isFinite, Pcf.schemeDivisorDelta_comp_of_isFinite,
    Pcf.schemeDivisorDelta_of_isIso (normIso k).inv,
    Pcf.schemeDivisorDelta_of_isIso (normIso k).hom,
    one_mul, mul_one]
  have hd : (zeroDiv k).mapFiniteDominantNormal (normIso k).hom = NodalCubic.paramDivisor k 0 :=
    Subtype.ext (normIso_hom_zeroDiv k)
  rw [hd]
  exact liftMap_delta_zero k

/-- **The normalized weighted branch divisors of `g` are exactly `{ν_B(0)}`**, the image of
the branch point `0` of `z ↦ z²`. -/
theorem weightedBranchPointSet_eq :
    Pcf.weightedBranchPointSet (gScheme k) = {zeroB k} := by
  refine Set.Subset.antisymm (weightedBranchPointSet_subset k) ?_
  rintro _ rfl
  have hF := (lift_eq_canonical k).symm
  refine ⟨(zeroDiv k).mapFiniteDominantNormal (Pcf.schemeGlobalNormalizationMorphism (gScheme k)),
    ⟨zeroDiv k, rfl, ?_⟩, ?_⟩
  · rw [hF]; exact lift_delta_zeroDiv k
  · change Pcf.Palomar.normalizationMap (Bs k)
      (Pcf.schemeGlobalNormalizationMorphism (gScheme k) (zeroDiv k).1) = zeroB k
    rw [hF, ← Scheme.Hom.comp_apply, lift_comp_normalizationMap, Scheme.Hom.comp_apply,
      ← normIso_hom_comp, Scheme.Hom.comp_apply, normIso_hom_zeroDiv]
    exact gScheme_zeroB k

/-- **`PC(g) ⊆ {ν_B(0)}`**. -/
theorem weightedPostcriticalPointSet_subset :
    Pcf.weightedPostcriticalPointSet (gScheme k) ⊆ {zeroB k} := by
  intro q hq
  simp only [Pcf.weightedPostcriticalPointSet, Set.mem_iUnion] at hq
  obtain ⟨n, z, hz, rfl⟩ := hq
  have hz' := weightedBranchPointSet_subset k hz
  rw [Set.mem_singleton_iff] at hz' ⊢
  subst hz'
  induction n with
  | zero => rfl
  | succ n ih =>
      change (gScheme k : _ → _)^[n + 1] (zeroB k) = _
      rw [Function.iterate_succ_apply',
        show (gScheme k : _ → _)^[n] (zeroB k) = zeroB k from ih, gScheme_zeroB]

/-- **`PC(g) = {ν_B(0)}`**. -/
theorem weightedPostcriticalPointSet_eq :
    Pcf.weightedPostcriticalPointSet (gScheme k) = {zeroB k} := by
  refine Set.Subset.antisymm (weightedPostcriticalPointSet_subset k) ?_
  rintro _ rfl
  simp only [Pcf.weightedPostcriticalPointSet, Set.mem_iUnion]
  exact ⟨0, zeroB k, by rw [weightedBranchPointSet_eq]; rfl, rfl⟩

/-- **`g` is PCF** (weighted normalized, downstairs form of `def:pcf`). -/
theorem g_isWeightedNormalizedPCFDownstairs :
    Pcf.IsWeightedNormalizedPCFDownstairs k (structureMap k) (gScheme k) := by
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k
    (structureMap k) _).2
  exact (Set.finite_singleton _).subset (weightedPostcriticalPointSet_subset k)

/-- **`g` is PCF** in the sense of `def:pcf`: generically separable (characteristic zero) with
finitely many weighted normalized postcritical divisors.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem g_isSeparableNormalizedPCF :
    Pcf.IsSeparableNormalizedPCF k (structureMap k) (gScheme k) :=
  (Pcf.isSeparableNormalizedPCF_iff_downstairs k (structureMap k) _).2
    ⟨Pcf.isGenericallySeparable_of_charZero_field k (structureMap k) _,
      g_isWeightedNormalizedPCFDownstairs k⟩

#print axioms lift_eq_canonical
#print axioms weightedBranchPointSet_eq
#print axioms weightedPostcriticalPointSet_eq
#print axioms g_isSeparableNormalizedPCF

end Pcf.Examples.PaperP.PinchedNodePCF
