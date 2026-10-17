/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Pcf.Stacks.Abhyankar.StrictHenselizationColimit
public import Pcf.Stacks.Abhyankar.StrictHenselizationLocalBaseChange

/-!
# Localizing the base of the strict local colimit (Stacks 04GW)

All strict-henselization results in pcf assume a local base ring `R` and use the colimit model
`LocalColimit R Ω` of pointed etale neighbourhoods.  Abhyankar's lemma needs the same model for a
non-local `R` at a geometric point `R → Ω` with kernel `p`.  This file proves that the two agree:
for any localization `S = M⁻¹ R` through which the point factors, the canonical base-change map

  `LocalColimit R Ω → LocalColimit S Ω`

is a ring isomorphism, and likewise for the unlocalized colimits.  Taking `S = R_p` gives the
base-point comparison of Stacks Tag 04GW: the colimit over pointed etale `R`-algebras is pcf's
model of `(R_p)ˢʰ`.

## Proof

The base-change functor from pointed etale neighbourhoods over `R` to those over `S` is final.

* Objects: a pointed etale `S`-algebra becomes standard etale after a pointed localization
  (`00UE`).  Scaling the generator by a common denominator `b ∈ M` turns its monic polynomial
  into one with a monic lift `F` over `R`; clearing denominators lifts the localizing polynomial
  to `G`.  The pair `(F, F' G)` is standard etale over `R`, and its generator divided by `b`
  satisfies the original pair after base change.
* Morphisms: two pointed maps into a base-changed stage are equalized after inverting, on the
  original stage, the numerator of the complement of the diagonal idempotent.

Finality identifies the colimits.  Bijectivity is then checked with the elementwise description
of `S ⊗[R] Y` as the localization of `Y` at the image of `M`; elements of `M` are already units
in the colimit over `R` because they are nonzero at the geometric point.

## Main declarations

* `localizationBaseChange_final`: base change along a localization is final.
* `colimitLocalizationRingEquiv`, `localColimitLocalizationRingEquiv`: the comparisons.
* `localColimitAtPrimeRingEquiv`, `colimitAtPrimeRingEquiv`: the case `S = R_p` (Stacks 04GW).
-/

@[expose] public section

open CategoryTheory Limits Polynomial
open scoped TensorProduct

universe u

namespace Pcf.Stacks.PointedEtaleNeighborhood

/-- Scaling the roots of `p` by `s` and substituting `s X` multiplies `p` by `s ^ deg p`. -/
theorem _root_.Polynomial.scaleRoots_comp_C_mul_X {A : Type*} [CommRing A] (p : A[X]) (s : A) :
    (p.scaleRoots s).comp (C s * X) = C (s ^ p.natDegree) * p := by
  rw [comp, scaleRoots_eval₂_mul (f := C) X s, eval₂_C_X, map_pow]

/-- The derivative of `p.scaleRoots s`, evaluated at `s • ξ`, is `s ^ (deg p - 1)` times the
derivative of `p` at `ξ`, in the form `s • p'ˢ(s ξ) = s ^ deg p • p'(ξ)`. -/
theorem _root_.Polynomial.aeval_smul_derivative_scaleRoots {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : A[X]) (s : A) (ξ : B) :
    algebraMap A B s * aeval (algebraMap A B s * ξ) (derivative (p.scaleRoots s)) =
      algebraMap A B (s ^ p.natDegree) * aeval ξ (derivative p) := by
  have h := congrArg derivative (Polynomial.scaleRoots_comp_C_mul_X p s)
  rw [derivative_comp, derivative_C_mul_X, derivative_C_mul] at h
  have h' := congrArg (aeval ξ) h
  simp only [map_mul, aeval_C, aeval_comp, aeval_X] at h'
  exact h'


variable {R S Ω : Type u} [CommRing R] [CommRing S] [Field Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]
  (M : Submonoid R) [IsLocalization M S]

/-- Elements of the localizing submonoid have nonzero image in the geometric point. -/
theorem algebraMap_ne_zero_of_mem (S : Type u) [CommRing S] [Algebra R S] [Algebra S Ω]
    [IsScalarTower R S Ω] (M : Submonoid R) [IsLocalization M S] {m : R} (hm : m ∈ M) :
    algebraMap R Ω m ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply R S Ω]
  exact ((IsLocalization.map_units S ⟨m, hm⟩).map (algebraMap S Ω)).ne_zero

include M in
/-- Every pointed etale neighbourhood over the localization `S = M⁻¹ R` maps to the base change
of a pointed etale neighbourhood over `R`.

At the point, `X` becomes standard etale after a pointed localization (`00UE`).  After scaling
the generator by a common denominator `b ∈ M`, its monic polynomial has a monic lift `F` over `R`;
the localizing polynomial is lifted after clearing denominators to `G`.  The pair `(F, F' G)` is
standard etale over `R` for trivial reasons, and its generator divided by `b` satisfies the
original pair after base change. -/
theorem exists_localizationBaseChange_refinement (X : PointedEtaleNeighborhood S Ω) :
    ∃ Y : PointedEtaleNeighborhood R Ω,
      Nonempty (X ⟶ (baseChange (R := R) (S := S) (Ω := Ω)).obj Y) := by
  let Q := RingHom.ker X.point.toRingHom
  let _ : Q.IsPrime := RingHom.ker_isPrime X.point.toRingHom
  let _ : Algebra.IsEtaleAt S Q := inferInstance
  obtain ⟨f, hfQ, hfstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) (S := X) Q
  let L := Localization.Away f
  let _ : Algebra.IsStandardEtale S L := hfstd
  let pointL : L →ₐ[S] Ω := IsLocalization.Away.liftAlgHom f
    (f := X.point) (isUnit_iff_ne_zero.mpr fun h ↦ hfQ (RingHom.mem_ker.mpr h))
  let toL : X →ₐ[S] L := IsScalarTower.toAlgHom S X L
  have hpointL : pointL.comp toL = X.point := by
    ext x
    simp [pointL, toL]
  let P : StandardEtalePresentation S L :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  -- the common denominator and the monic lift
  have hlift := IsLocalization.scaleRoots_commonDenom_mem_lifts M P.f
    (by rw [P.monic_f.leadingCoeff]; exact ⟨1, map_one _⟩)
  set b : M := IsLocalization.commonDenom M P.f.support P.f.coeff with hb_def
  set bS : S := algebraMap R S b with hbS
  obtain ⟨F, hFmap, hFdeg, hFmonic⟩ := lifts_and_natDegree_eq_and_monic hlift
    ((monic_scaleRoots_iff _).mpr P.monic_f)
  obtain ⟨c, hcM, hG⟩ := IsLocalization.integerNormalization_spec M (P.g.scaleRoots bS)
  set G := IsLocalization.integerNormalization M (P.g.scaleRoots bS) with hG_def
  have hbunit : IsUnit bS := IsLocalization.map_units S b
  have hcunit : IsUnit (algebraMap R S c) := IsLocalization.map_units S ⟨c, hcM⟩
  let U : StandardEtalePair R := ⟨F, hFmonic, derivative F * G, G, 0, 1, by ring⟩
  -- evaluation identities, valid in any `S`-algebra
  have hFeval : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
      (w : B), aeval (algebraMap S B bS * w) F =
        algebraMap S B (bS ^ P.f.natDegree) * aeval w P.f := by
    intro B _ _ _ _ w
    rw [← aeval_map_algebraMap S, hFmap, ← Algebra.smul_def, scaleRoots_aeval_smul,
      Algebra.smul_def]
  have hGeval : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
      (w : B), aeval (algebraMap S B bS * w) G =
        algebraMap S B (algebraMap R S c * bS ^ P.g.natDegree) * aeval w P.g := by
    intro B _ _ _ _ w
    rw [← aeval_map_algebraMap S, hG, ← algebraMap_smul S c, smul_eq_C_mul, map_mul, aeval_C,
      ← Algebra.smul_def bS w, scaleRoots_aeval_smul, Algebra.smul_def, map_mul,
      mul_assoc]
  have hFd : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
      (w : B), algebraMap S B bS * aeval (algebraMap S B bS * w) (derivative F) =
        algebraMap S B (bS ^ P.f.natDegree) * aeval w (derivative P.f) := by
    intro B _ _ _ _ w
    rw [← aeval_map_algebraMap S, ← derivative_map, hFmap]
    exact Polynomial.aeval_smul_derivative_scaleRoots P.f bS w
  have hdown : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
      (w : B), U.HasMap (algebraMap S B bS * w) → P.P.HasMap w := by
    intro B _ _ _ _ w hw
    constructor
    · have h := hFeval B w
      rw [show aeval (algebraMap S B bS * w) F = 0 from hw.1] at h
      exact ((hbunit.pow _).map (algebraMap S B)).mul_right_eq_zero.mp h.symm
    · have hu := hw.2
      change IsUnit (aeval _ (derivative F * G)) at hu
      rw [map_mul, hGeval] at hu
      exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)
  -- the geometric point
  let ξ : Ω := pointL P.x
  have hξf : aeval ξ P.f = 0 := by
    rw [aeval_algHom_apply, P.hasMap.1, map_zero]
  have hξg : aeval ξ P.g ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (P.hasMap.2.map pointL).ne_zero
  have hξd : aeval ξ (derivative P.f) ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (P.hasMap.isUnit_derivative_f.map pointL).ne_zero
  have hbΩ : algebraMap S Ω bS ≠ 0 := (hbunit.map (algebraMap S Ω)).ne_zero
  have hUξ : U.HasMap (algebraMap S Ω bS * ξ) := by
    constructor
    · change aeval _ F = 0
      rw [hFeval, hξf, mul_zero]
    · change IsUnit (aeval _ (derivative F * G))
      rw [map_mul]
      apply isUnit_iff_ne_zero.mpr
      apply mul_ne_zero
      · intro h0
        have h := hFd Ω ξ
        rw [h0, mul_zero] at h
        exact mul_ne_zero ((hbunit.pow _).map (algebraMap S Ω)).ne_zero hξd h.symm
      · rw [hGeval]
        exact mul_ne_zero ((hcunit.mul (hbunit.pow _)).map (algebraMap S Ω)).ne_zero hξg
  let pointU : U.Ring →ₐ[R] Ω := U.lift (algebraMap S Ω bS * ξ) hUξ
  let Y : PointedEtaleNeighborhood R Ω := ofEtaleAlgebra U.Ring pointU
  let EY : Y ≃ₐ[R] U.Ring := ofEtaleAlgebraEquiv U.Ring pointU
  have hYpoint : ∀ x, Y.point (EY.symm x) = pointU x := fun x ↦
    DFunLike.congr_fun (ofEtaleAlgebra_point_comp_equiv (R := R) (Ω := Ω) U.Ring pointU) x
  let ι : U.Ring →ₐ[R] (S ⊗[R] (Y : Type u)) :=
    Algebra.TensorProduct.includeRight.comp EY.symm.toAlgHom
  let w0 : (S ⊗[R] (Y : Type u)) := ι U.X
  have hw0 : ∀ p : R[X], aeval w0 p = ι (aeval U.X p) := fun p ↦
    (aeval_algHom_apply ι U.X p)
  have hbT : IsUnit (algebraMap S (S ⊗[R] (Y : Type u)) bS) :=
    RingHom.isUnit_map (algebraMap S (S ⊗[R] (Y : Type u))) hbunit
  let z : (S ⊗[R] (Y : Type u)) := ↑hbT.unit⁻¹ * w0
  have hbz' : (hbT.unit : S ⊗[R] (Y : Type u)) * z = w0 := by
    exact Units.mul_inv_cancel_left _ _
  have hz : P.P.HasMap z := by
    apply hdown _ z
    have hw0U : U.HasMap w0 := by
      constructor
      · rw [hw0, U.hasMap_X.1, map_zero]
      · rw [hw0]
        exact RingHom.isUnit_map ι.toRingHom U.hasMap_X.2
    convert hw0U using 1
    rw [← hbT.unit_spec]
    exact hbz'
  let raw : X →ₐ[S] (S ⊗[R] (Y : Type u)) :=
    ((P.P.lift z hz).comp P.equivRing.toAlgHom).comp toL
  have hraw : (baseChangePoint (S := S) Y).comp raw = X.point := by
    rw [← hpointL]
    change ((baseChangePoint (S := S) Y).comp
      ((P.P.lift z hz).comp P.equivRing.toAlgHom)).comp toL = pointL.comp toL
    congr 1
    apply P.hom_ext
    change baseChangePoint (S := S) Y (P.P.lift z hz (P.equivRing P.x)) = ξ
    rw [StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
    have h1 := congrArg (baseChangePoint (S := S) Y) hbz'
    rw [map_mul, hbT.unit_spec, AlgHom.commutes] at h1
    have h2 : baseChangePoint (S := S) Y w0 = algebraMap S Ω bS * ξ := by
      change baseChangePoint (S := S) Y (1 ⊗ₜ[R] EY.symm U.X) = _
      simp only [baseChangePoint, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [hYpoint]
      exact StandardEtalePair.lift_X _ _ _
    rw [h2] at h1
    exact mul_left_cancel₀ hbΩ h1
  refine ⟨Y, ⟨?_⟩⟩
  exact homToOfEtaleAlgebra (S ⊗[R] (Y : Type u)) (baseChangePoint (S := S) Y) raw hraw


include M in
/-- Every element of `S ⊗[R] B` becomes a pure tensor `1 ⊗ b` after multiplication by an element
of `M`: the scalar extension to `S = M⁻¹ R` is the localization of `B` at the image of `M`. -/
theorem exists_mem_mul_eq_one_tmul (B : Type u) [CommRing B] [Algebra R B] (w : S ⊗[R] B) :
    ∃ (b : B) (m : R), m ∈ M ∧ algebraMap R (S ⊗[R] B) m * w = (1 : S) ⊗ₜ[R] b := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := B)
  obtain ⟨⟨b, ⟨_, m, hm, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid B M) w
  refine ⟨b, m, hm, ?_⟩
  rw [mul_comm, ← Algebra.TensorProduct.right_algebraMap_apply]
  rw [← h, IsScalarTower.algebraMap_apply R B (S ⊗[R] B)]

include M in
/-- A pure tensor `1 ⊗ b` vanishes in `S ⊗[R] B` exactly when `b` is killed by an element of
`M`. -/
theorem exists_mem_mul_eq_zero_of_one_tmul_eq_zero (B : Type u) [CommRing B] [Algebra R B]
    (b : B) (h : (1 : S) ⊗ₜ[R] b = 0) :
    ∃ m : R, m ∈ M ∧ algebraMap R B m * b = 0 := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := B)
  rw [← Algebra.TensorProduct.right_algebraMap_apply,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid B M)] at h
  obtain ⟨⟨_, m, hm, rfl⟩, hm0⟩ := h
  exact ⟨m, hm, hm0⟩

include M in
/-- Two pointed maps into the base change of one stage to `S = M⁻¹ R` are equalized after
refining that stage over `R`.  The diagonal idempotent of the source cuts out the equalizer; the
complement of its image, cleared of its denominator in `M`, is inverted on the original stage. -/
theorem exists_localizationBaseChange_equalizing_refinement
    {X : PointedEtaleNeighborhood S Ω} {Y : PointedEtaleNeighborhood R Ω}
    (s t : X ⟶ baseChangeObj (R := R) (S := S) Y) :
    ∃ (Y' : PointedEtaleNeighborhood R Ω) (h : Y ⟶ Y'),
      s ≫ baseChangeMap (S := S) h = t ≫ baseChangeMap (S := S) h := by
  let J := KaehlerDifferential.ideal S X
  have hJ : IsIdempotentElem J :=
    (Ideal.cotangent_subsingleton_iff J).mp (by
      change Subsingleton Ω[X⁄S]
      infer_instance)
  obtain ⟨e, he, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg J (KaehlerDifferential.ideal_fg S X)).mp hJ
  let p : X ⊗[S] X →ₐ[S] baseChangeObj (R := R) (S := S) Y :=
    Algebra.TensorProduct.productMap s.hom t.hom
  let d : baseChangeObj (R := R) (S := S) Y := p e
  have hd : IsIdempotentElem d := by
    change d * d = d
    simp only [d, ← map_mul, he.eq]
  have hpcomp : (baseChangeObj (R := R) (S := S) Y).point.comp p =
      X.point.comp (Algebra.TensorProduct.lmul' S) := by
    ext x
    · simpa [p] using DFunLike.congr_fun s.point_comp x
    · simpa [p] using DFunLike.congr_fun t.point_comp x
  have heJ : e ∈ J := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self e
  have hlmule : Algebra.TensorProduct.lmul' S e = 0 := by
    rw [RingHom.mem_ker] at heJ
    exact heJ
  have hpointd : (baseChangeObj (R := R) (S := S) Y).point d = 0 := by
    change ((baseChangeObj (R := R) (S := S) Y).point.comp p) e = 0
    rw [hpcomp]
    simp [hlmule]
  let E : baseChangeObj (R := R) (S := S) Y ≃ₐ[S] TensorProduct R S Y :=
    ofEtaleAlgebraEquiv (TensorProduct R S Y) (baseChangePoint (R := R) (S := S) Y)
  obtain ⟨y, m, hm, hy⟩ := exists_mem_mul_eq_one_tmul M (Y : Type u) (E (1 - d))
  have hpointy : Y.point y = algebraMap R Ω m := by
    calc
      Y.point y = baseChangePoint (R := R) (S := S) Y ((1 : S) ⊗ₜ[R] y) := by
        simp [baseChangePoint]
      _ = baseChangePoint (R := R) (S := S) Y
          (algebraMap R (S ⊗[R] (Y : Type u)) m * E (1 - d)) := congrArg _ hy.symm
      _ = algebraMap R Ω m * (baseChangeObj (R := R) (S := S) Y).point (1 - d) := by
        rw [map_mul, IsScalarTower.algebraMap_apply R S (S ⊗[R] (Y : Type u)), AlgHom.commutes,
          ← IsScalarTower.algebraMap_apply]
        rfl
      _ = algebraMap R Ω m := by rw [map_sub, map_one, hpointd, sub_zero, mul_one]
  have hyunitΩ : IsUnit (Y.point y) := by
    rw [hpointy]
    exact isUnit_iff_ne_zero.mpr (algebraMap_ne_zero_of_mem S M hm)
  let L := Localization.Away y
  let pointL : L →ₐ[R] Ω := IsLocalization.Away.liftAlgHom y (f := Y.point) hyunitΩ
  let q : Y →ₐ[R] L := IsScalarTower.toAlgHom R Y L
  have hpointLq : pointL.comp q = Y.point := by
    ext z
    simp [pointL, q]
  let Y' := ofEtaleAlgebra L pointL
  let h : Y ⟶ Y' := homToOfEtaleAlgebra L pointL q hpointLq
  let E' : Y' ≃ₐ[R] L := ofEtaleAlgebraEquiv L pointL
  let m' : TensorProduct R S Y →ₐ[S] TensorProduct R S Y' :=
    Algebra.TensorProduct.map (AlgHom.id S S) h.hom
  let k : baseChangeObj (R := R) (S := S) Y →ₐ[S] TensorProduct R S Y' := m'.comp E.toAlgHom
  have hyunit : IsUnit (h.hom y) := by
    change IsUnit (E'.symm (q y))
    exact (IsLocalization.Away.algebraMap_isUnit y (S := L)).map E'.symm.toRingHom
  have hcompunit : IsUnit (k (1 - d)) := by
    have hu : IsUnit ((1 : S) ⊗ₜ[R] h.hom y) :=
      RingHom.isUnit_map Algebra.TensorProduct.includeRight.toRingHom hyunit
    have hm' := congrArg m' hy
    have hm'' : m' ((1 : S) ⊗ₜ[R] y) = (1 : S) ⊗ₜ[R] h.hom y := by simp [m']
    rw [hm''] at hm'
    rw [map_mul] at hm'
    obtain ⟨a, ha⟩ : ∃ a, a * k (1 - d) = (1 : S) ⊗ₜ[R] h.hom y := ⟨_, hm'⟩
    rw [← ha] at hu
    exact isUnit_of_mul_isUnit_right (M := TensorProduct R S Y') hu
  have hkdzero : k d = 0 := by
    apply hcompunit.mul_left_cancel
    change k (1 - d) * k d = k (1 - d) * 0
    calc
      k (1 - d) * k d = k ((1 - d) * d) := (map_mul k _ _).symm
      _ = 0 := by rw [hd.one_sub_mul_self, map_zero]
      _ = k (1 - d) * 0 := (mul_zero (k (1 - d))).symm
  have hkst : k.comp s.hom = k.comp t.hom := by
    ext x
    have hxJ : (1 : X) ⊗ₜ[S] x - x ⊗ₜ[S] (1 : X) ∈ J :=
      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal S x
    rw [hspan, Ideal.mem_span_singleton'] at hxJ
    obtain ⟨a, ha⟩ := hxJ
    have hx := congrArg k (congrArg p ha)
    simp only [map_sub, p, Algebra.TensorProduct.productMap_apply_tmul] at hx
    have hpezero : k (p e) = 0 := by
      change k d = 0
      exact hkdzero
    simp only [map_mul, map_one, one_mul, mul_one] at hx
    rw [hpezero] at hx
    have hxzero : k (p a) * (0 : TensorProduct R S Y') = 0 :=
      mul_zero (k (p a))
    have hx' : 0 = k (t.hom x) - k (s.hom x) := by
      exact hxzero ▸ hx
    exact (sub_eq_zero.mp hx'.symm).symm
  refine ⟨Y', h, ?_⟩
  apply Hom.ext
  ext x
  change (baseChangeMap (S := S) h).hom (s.hom x) =
    (baseChangeMap (S := S) h).hom (t.hom x)
  apply (ofEtaleAlgebraEquiv
    (TensorProduct R S Y') (baseChangePoint (R := R) (S := S) Y')).injective
  rw [ofEtaleAlgebraEquiv_baseChangeMap_apply,
    ofEtaleAlgebraEquiv_baseChangeMap_apply]
  exact DFunLike.congr_fun hkst x

include M in
/-- Base change from `R` to a localization `S = M⁻¹ R` is final on pointed etale
neighbourhoods. -/
theorem localizationBaseChange_final :
    (baseChange (R := R) (S := S) (Ω := Ω)).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · exact exists_localizationBaseChange_refinement M
  · intro X Y s t
    exact exists_localizationBaseChange_equalizing_refinement M s t


include M in
/-- Equality in the pointed-etale colimit over `S = M⁻¹ R` is detected after a refinement that is
itself the base change of a pointed-etale neighbourhood over `R`. -/
theorem exists_localizationBaseChange_refinement_of_toColimit_eq
    {Y : PointedEtaleNeighborhood R Ω} {x y : baseChangeObj (R := R) (S := S) Y}
    (hxy : toColimit (R := S) (Ω := Ω) (baseChangeObj (R := R) (S := S) Y) x =
      toColimit (R := S) (Ω := Ω) (baseChangeObj (R := R) (S := S) Y) y) :
    ∃ (Y' : PointedEtaleNeighborhood R Ω) (f : Y ⟶ Y'),
      (baseChangeMap (S := S) f).hom x = (baseChangeMap (S := S) f).hom y := by
  let F := baseChange (R := R) (S := S) (Ω := Ω)
  let G := functor (R := S) (Ω := Ω)
  let U := Under.forget (CommRingCat.of S)
  let V := forget CommRingCat
  let c := V.mapCocone (U.mapCocone (colimit.cocone G))
  have hcTarget : Limits.IsColimit c :=
    Limits.isColimitOfPreserves V (Limits.isColimitOfPreserves U (colimit.isColimit G))
  let _ : F.Final := localizationBaseChange_final M
  have hc : Limits.IsColimit (c.whisker F) :=
    (Functor.Final.isColimitWhiskerEquiv F c).symm hcTarget
  have hxy' : (c.whisker F).ι.app Y x = (c.whisker F).ι.app Y y := hxy
  obtain ⟨Y', f, hf⟩ :=
    (Limits.Types.FilteredColimit.isColimit_eq_iff' hc x y).mp hxy'
  exact ⟨Y', f, hf⟩

/-- Elements of `M` are units in the pointed-etale colimit over `R`: they are nonzero at the
geometric point, and the colimit already inverts every element nonzero at the point. -/
theorem isUnit_algebraMap_colimit_of_mem (S : Type u) [CommRing S] [Algebra R S] [Algebra S Ω]
    [IsScalarTower R S Ω] (M : Submonoid R) [IsLocalization M S] {m : R} (hm : m ∈ M) :
    IsUnit (algebraMap R (Colimit R Ω) m) := by
  apply colimitPointPrime_primeCompl_le_isUnit (R := R) (Ω := Ω)
  apply Ideal.mem_primeCompl_iff.mpr
  intro hmem
  apply algebraMap_ne_zero_of_mem (Ω := Ω) S M hm
  change colimitPoint (R := R) (Ω := Ω) (algebraMap R (Colimit R Ω) m) = 0 at hmem
  rwa [AlgHom.commutes] at hmem

include M in
/-- The canonical map from the pointed-etale colimit over `R` to the one over `S = M⁻¹ R` is
surjective. -/
theorem colimitBaseChangeRingHom_surjective_of_isLocalization :
    Function.Surjective (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) := by
  intro z
  obtain ⟨X, x, hx⟩ := exists_stage_of_colimit_element (R := S) (Ω := Ω) z
  obtain ⟨Y, ⟨s⟩⟩ := exists_localizationBaseChange_refinement M X
  change X ⟶ baseChangeObj (R := R) (S := S) Y at s
  let E : baseChangeObj (R := R) (S := S) Y ≃ₐ[S] TensorProduct R S Y :=
    ofEtaleAlgebraEquiv (TensorProduct R S Y) (baseChangePoint (R := R) (S := S) Y)
  obtain ⟨y, m, hm, hy⟩ := exists_mem_mul_eq_one_tmul M (Y : Type u) (E (s.hom x))
  rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] (Y : Type u))] at hy
  have hu := isUnit_algebraMap_colimit_of_mem (Ω := Ω) S M hm
  let φ := colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)
  have hφy : φ (toColimit (R := R) (Ω := Ω) Y y) =
      algebraMap S (Colimit S Ω) (algebraMap R S m) * z := by
    rw [colimitBaseChangeRingHom_toColimit]
    change toColimit (R := S) (Ω := Ω) (baseChangeObj (R := R) (S := S) Y)
      (E.symm ((1 : S) ⊗ₜ[R] y)) = _
    rw [← hy, map_mul, AlgEquiv.commutes, E.symm_apply_apply, map_mul, AlgHom.commutes, ← hx]
    rw [← DFunLike.congr_fun (toColimit_naturality (R := S) (Ω := Ω) s) x]
    rfl
  refine ⟨↑hu.unit⁻¹ * toColimit (R := R) (Ω := Ω) Y y, ?_⟩
  change φ (↑hu.unit⁻¹ * toColimit (R := R) (Ω := Ω) Y y) = z
  rw [map_mul, hφy, ← colimitBaseChangeRingHom_algebraMap, ← mul_assoc, ← map_mul]
  change φ (↑hu.unit⁻¹ * ↑hu.unit) * z = z
  rw [Units.inv_mul, map_one, one_mul]

include M in
/-- The canonical map from the pointed-etale colimit over `R` to the one over `S = M⁻¹ R` is
injective. -/
theorem colimitBaseChangeRingHom_injective_of_isLocalization :
    Function.Injective (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨Y, y, rfl⟩ := exists_stage_of_colimit_element (R := R) (Ω := Ω) c
  rw [colimitBaseChangeRingHom_toColimit] at hc
  let E : baseChangeObj (R := R) (S := S) Y ≃ₐ[S] TensorProduct R S Y :=
    ofEtaleAlgebraEquiv (TensorProduct R S Y) (baseChangePoint (R := R) (S := S) Y)
  let z : baseChangeObj (R := R) (S := S) Y := E.symm ((1 : S) ⊗ₜ[R] y)
  have hz : toColimit (R := S) (Ω := Ω) (baseChangeObj (R := R) (S := S) Y) z =
      toColimit (R := S) (Ω := Ω) (baseChangeObj (R := R) (S := S) Y) 0 := by
    rw [map_zero]
    exact hc
  obtain ⟨Y', f, hf⟩ := exists_localizationBaseChange_refinement_of_toColimit_eq M hz
  have htensor : (1 : S) ⊗ₜ[R] f.hom y = (0 : TensorProduct R S Y') := by
    let E' : baseChangeObj (R := R) (S := S) Y' ≃ₐ[S] TensorProduct R S Y' :=
      ofEtaleAlgebraEquiv (TensorProduct R S Y') (baseChangePoint (R := R) (S := S) Y')
    have hE := congrArg E' hf
    change E' ((baseChangeMap (S := S) f).hom z) =
      E' ((baseChangeMap (S := S) f).hom 0) at hE
    rw [ofEtaleAlgebraEquiv_baseChangeMap_apply, map_zero, map_zero] at hE
    change baseChangeRawMap (S := S) f (E (E.symm ((1 : S) ⊗ₜ[R] y))) = 0 at hE
    rw [E.apply_symm_apply] at hE
    simpa [baseChangeRawMap] using hE
  obtain ⟨m, hm, hmy⟩ :=
    exists_mem_mul_eq_zero_of_one_tmul_eq_zero M (Y' : Type u) (f.hom y) htensor
  have hu := isUnit_algebraMap_colimit_of_mem (Ω := Ω) S M hm
  have h0 := congrArg (toColimit (R := R) (Ω := Ω) Y') hmy
  rw [map_mul, AlgHom.commutes, map_zero] at h0
  rw [← DFunLike.congr_fun (toColimit_naturality (R := R) (Ω := Ω) f) y]
  exact (hu.mul_right_eq_zero).mp h0

include M in
/-- The canonical map of pointed-etale colimits along a localization `R → S = M⁻¹ R` is
bijective. -/
theorem colimitBaseChangeRingHom_bijective_of_isLocalization :
    Function.Bijective (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) :=
  ⟨colimitBaseChangeRingHom_injective_of_isLocalization M,
    colimitBaseChangeRingHom_surjective_of_isLocalization M⟩


/-- The pointed-etale colimit is unchanged by localizing the base: the canonical map along
`R → S = M⁻¹ R` is a ring isomorphism. -/
noncomputable def colimitLocalizationRingEquiv : Colimit R Ω ≃+* Colimit S Ω :=
  RingEquiv.ofBijective (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω))
    (colimitBaseChangeRingHom_bijective_of_isLocalization M)

@[simp]
theorem colimitLocalizationRingEquiv_apply (c : Colimit R Ω) :
    colimitLocalizationRingEquiv (S := S) M c =
      colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) c := rfl

include M in
/-- The canonical map of strict local colimits along a localization `R → S = M⁻¹ R` is
bijective. -/
theorem localColimitBaseChangeRingHom_bijective_of_isLocalization :
    Function.Bijective (localColimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) := by
  have hR : Function.Bijective (algebraMap (Colimit R Ω) (LocalColimit R Ω)) :=
    (colimitToLocalColimitAlgEquiv (R := R) (Ω := Ω)).bijective
  have hS : Function.Bijective (algebraMap (Colimit S Ω) (LocalColimit S Ω)) :=
    (colimitToLocalColimitAlgEquiv (R := S) (Ω := Ω)).bijective
  have hcomp : (localColimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) ∘
      (algebraMap (Colimit R Ω) (LocalColimit R Ω)) =
      (algebraMap (Colimit S Ω) (LocalColimit S Ω)) ∘
        (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) := by
    funext c
    exact localColimitBaseChangeRingHom_toLocalColimit c
  rw [← Function.Bijective.of_comp_iff _ hR, hcomp]
  exact hS.comp (colimitBaseChangeRingHom_bijective_of_isLocalization M)

/-- **Base-point comparison.**  The strict local colimit of `R` at a geometric point `Ω` is
canonically isomorphic to the strict local colimit of any localization `S = M⁻¹ R` through which
the point factors.  The isomorphism is the canonical base-change map. -/
noncomputable def localColimitLocalizationRingEquiv : LocalColimit R Ω ≃+* LocalColimit S Ω :=
  RingEquiv.ofBijective (localColimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω))
    (localColimitBaseChangeRingHom_bijective_of_isLocalization M)

@[simp]
theorem localColimitLocalizationRingEquiv_apply (a : LocalColimit R Ω) :
    localColimitLocalizationRingEquiv (S := S) M a =
      localColimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) a := rfl

/-- The base-point comparison is compatible with the structure maps from `R`. -/
theorem localColimitLocalizationRingEquiv_algebraMap (r : R) :
    localColimitLocalizationRingEquiv (S := S) M (algebraMap R (LocalColimit R Ω) r) =
      algebraMap S (LocalColimit S Ω) (algebraMap R S r) := by
  rw [localColimitLocalizationRingEquiv_apply,
    IsScalarTower.algebraMap_apply R (Colimit R Ω) (LocalColimit R Ω),
    localColimitBaseChangeRingHom_toLocalColimit, colimitBaseChangeRingHom_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- The base-point comparison is compatible with the geometric points. -/
theorem localPoint_comp_localColimitLocalizationRingEquiv :
    (localPoint (R := S) (Ω := Ω) (Field.toIsField Ω)).comp
        (localColimitLocalizationRingEquiv (S := S) M).toRingHom =
      localPoint (R := R) (Ω := Ω) (Field.toIsField Ω) := by
  apply IsLocalization.ringHom_ext (colimitPointPrime (R := R) (Ω := Ω)).primeCompl
  rw [RingHom.comp_assoc]
  ext c
  change localPoint (R := S) (Ω := Ω) (Field.toIsField Ω)
      (localColimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)
        (algebraMap (Colimit R Ω) (LocalColimit R Ω) c)) =
    localPoint (R := R) (Ω := Ω) (Field.toIsField Ω)
      (algebraMap (Colimit R Ω) (LocalColimit R Ω) c)
  rw [localColimitBaseChangeRingHom_toLocalColimit]
  have hS := DFunLike.congr_fun (localPoint_comp_toLocalColimit (R := S) (Ω := Ω)
    (Field.toIsField Ω)) (colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω) c)
  have hR := DFunLike.congr_fun (localPoint_comp_toLocalColimit (R := R) (Ω := Ω)
    (Field.toIsField Ω)) c
  have hpt := DFunLike.congr_fun
    (colimitPoint_comp_colimitBaseChangeRingHom (R := R) (S := S) (Ω := Ω)) c
  exact hS.trans (hpt.trans hR.symm)


end Pcf.Stacks.PointedEtaleNeighborhood

namespace Pcf.Stacks.PointedEtaleNeighborhood

section AtPrime

variable {R Ω : Type u} [CommRing R] [Field Ω] [Algebra R Ω]
  (p : Ideal R) [p.IsPrime] (hΩ : RingHom.ker (algebraMap R Ω) = p)

/-- A geometric point `R → Ω` with kernel `p` factors through the local ring `R_p`. -/
@[instance_reducible]
noncomputable def atPrimeAlgebra : Algebra (Localization.AtPrime p) Ω :=
  (IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
    (g := algebraMap R Ω) (fun x ↦ isUnit_iff_ne_zero.mpr fun h ↦ by
      have hx : (x : R) ∈ RingHom.ker (algebraMap R Ω) := h
      rw [hΩ] at hx
      exact x.2 hx)).toAlgebra

theorem atPrimeAlgebra_isScalarTower :
    letI := atPrimeAlgebra p hΩ
    IsScalarTower R (Localization.AtPrime p) Ω := by
  let _ := atPrimeAlgebra p hΩ
  exact IsScalarTower.of_algebraMap_eq fun r ↦
    (IsLocalization.lift_eq (M := p.primeCompl) (S := Localization.AtPrime p) _ r).symm

/-- **Base-point comparison at a prime (Stacks 04GW, pcf model).**  Let `R` be any ring and
`R → Ω` a geometric point with kernel `p`.  The strict local colimit of `R` at `Ω` (the localized
colimit of pointed etale `R`-algebras, i.e. of the triples `(S, q, φ)` of Tag 04GW) is canonically
isomorphic to the strict local colimit of the local ring `R_p` at `Ω`, which is pcf's model of
`(R_p)ˢʰ`.  Hence every strict-henselization result proved for local base rings applies to
`LocalColimit R Ω` for non-local `R`.

Divergence from Stacks: Tag 04GW takes `Ω = κ(p)ˢᵉᵖ` and identifies the colimit with the strict
henselization of `R_p` by showing that it is strictly henselian.  Here `Ω` is any field with
kernel `p`, and the identification is with pcf's colimit model of `(R_p)ˢʰ`.  The proof route is
different: base change `R → R_p` is shown to be final on pointed etale neighbourhoods (standard
etale lifting after clearing denominators, plus diagonal-idempotent equalization). -/
@[stacks 04GW "pcf colimit model of (R_p)^sh; Ω any field with kernel p"]
noncomputable def localColimitAtPrimeRingEquiv :
    letI := atPrimeAlgebra p hΩ
    LocalColimit R Ω ≃+* LocalColimit (Localization.AtPrime p) Ω :=
  letI := atPrimeAlgebra p hΩ
  haveI := atPrimeAlgebra_isScalarTower p hΩ
  localColimitLocalizationRingEquiv (S := Localization.AtPrime p) p.primeCompl

/-- The base-point comparison at a prime is compatible with the structure maps from `R`. -/
theorem localColimitAtPrimeRingEquiv_algebraMap (r : R) :
    letI := atPrimeAlgebra p hΩ
    localColimitAtPrimeRingEquiv p hΩ (algebraMap R (LocalColimit R Ω) r) =
      algebraMap (Localization.AtPrime p) (LocalColimit (Localization.AtPrime p) Ω)
        (algebraMap R (Localization.AtPrime p) r) := by
  let _ := atPrimeAlgebra p hΩ
  have := atPrimeAlgebra_isScalarTower p hΩ
  exact localColimitLocalizationRingEquiv_algebraMap (S := Localization.AtPrime p) p.primeCompl r

/-- The unlocalized form of Stacks 04GW: the colimit over all pointed etale `R`-algebras is
already `(R_p)ˢʰ` (in pcf's model), without localizing at the point. -/
@[stacks 04GW "colim S form; pcf colimit model of (R_p)^sh; Ω any field with kernel p"]
noncomputable def colimitAtPrimeRingEquiv :
    letI := atPrimeAlgebra p hΩ
    Colimit R Ω ≃+* LocalColimit (Localization.AtPrime p) Ω :=
  letI := atPrimeAlgebra p hΩ
  haveI := atPrimeAlgebra_isScalarTower p hΩ
  (colimitLocalizationRingEquiv (S := Localization.AtPrime p) p.primeCompl).trans
    (colimitToLocalColimitAlgEquiv (R := Localization.AtPrime p) (Ω := Ω)).toRingEquiv

end AtPrime

end Pcf.Stacks.PointedEtaleNeighborhood

open Pcf.Stacks.PointedEtaleNeighborhood in
#print axioms localizationBaseChange_final
open Pcf.Stacks.PointedEtaleNeighborhood in
#print axioms localColimitLocalizationRingEquiv
open Pcf.Stacks.PointedEtaleNeighborhood in
#print axioms localColimitAtPrimeRingEquiv
open Pcf.Stacks.PointedEtaleNeighborhood in
#print axioms colimitAtPrimeRingEquiv
open Pcf.Stacks.PointedEtaleNeighborhood in
#print axioms localPoint_comp_localColimitLocalizationRingEquiv
open Pcf.Stacks.PointedEtaleNeighborhood in
#print axioms localColimitAtPrimeRingEquiv_algebraMap
