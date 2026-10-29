/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineRestriction
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI
public import Pcf.Bounding.NormalizationSeparable

/-!
# Étaleness away from the invariant Frobenius line

The equation `T^p+yT-x` has derivative `y`. After inverting `y`, an explicit
standard étale algebra is identified with the actual localized source ring.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory Polynomial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

abbrev SourceAway := Localization.Away (v k)

noncomputable def sourceLocalization : Plane k →+* SourceAway k := algebraMap _ _

noncomputable def awayCoordinateMap : Plane k →+* SourceAway k :=
  (sourceLocalization k).comp (coordinateMap k p).toRingHom

noncomputable def etalePair : StandardEtalePair (Plane k) :=
  ⟨X ^ p + C (v k) * X - C (u k),
    Pcf.Examples.CharP.monic_charPoly (Fact.out : p.Prime).two_le _ _, C (v k), 1, 0, 1, by
      rw [Pcf.Examples.CharP.derivative_charPoly]
      simp⟩

noncomputable instance pairKAlgebra : Algebra k (etalePair k p).Ring :=
  ((algebraMap (Plane k) (etalePair k p).Ring).comp (algebraMap k (Plane k))).toAlgebra

instance pairKTower : IsScalarTower k (Plane k) (etalePair k p).Ring :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem etalePair_root_relation : (etalePair k p).X ^ p +
    algebraMap (Plane k) (etalePair k p).Ring (v k) * (etalePair k p).X =
      algebraMap (Plane k) (etalePair k p).Ring (u k) := by
  have h := (etalePair k p).hasMap_X.1
  change aeval (etalePair k p).X (X ^ p + C (v k) * X - C (u k)) = 0 at h
  simpa only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C, sub_eq_zero] using h

theorem etalePair_v_unit : IsUnit (algebraMap (Plane k) (etalePair k p).Ring (v k)) := by
  have h := (etalePair k p).hasMap_X.2
  change IsUnit (aeval (etalePair k p).X (C (v k))) at h
  simpa using h

noncomputable def sourceToPair : Plane k →ₐ[k] (etalePair k p).Ring :=
  MvPolynomial.aeval ![(etalePair k p).X,
    algebraMap (Plane k) (etalePair k p).Ring (v k)]

@[simp] theorem sourceToPair_u : sourceToPair k p (u k) = (etalePair k p).X := by
  simp [sourceToPair, u]

@[simp] theorem sourceToPair_v : sourceToPair k p (v k) =
    algebraMap (Plane k) (etalePair k p).Ring (v k) := by
  simp [sourceToPair, v]

theorem sourceToPair_map : (sourceToPair k p).comp (coordinateMap k p) =
    IsScalarTower.toAlgHom k (Plane k) (etalePair k p).Ring := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change sourceToPair k p (coordinateMap k p (u k)) = _
    rw [coordinateMap_u, map_add, map_pow, map_mul, sourceToPair_u, sourceToPair_v]
    change (etalePair k p).X ^ p + (etalePair k p).X *
      algebraMap (Plane k) (etalePair k p).Ring (v k) =
        algebraMap (Plane k) (etalePair k p).Ring (u k)
    simpa only [mul_comm] using etalePair_root_relation k p
  · change sourceToPair k p (coordinateMap k p (v k)) = _
    rw [coordinateMap_v, sourceToPair_v]
    rfl

noncomputable def awayToPair : SourceAway k →+* (etalePair k p).Ring :=
  IsLocalization.Away.lift (v k) (g := (sourceToPair k p).toRingHom)
    (by change IsUnit (sourceToPair k p (v k)); rw [sourceToPair_v]; exact etalePair_v_unit k p)

@[simp] theorem awayToPair_on_source (q : Plane k) :
    awayToPair k p (sourceLocalization k q) = sourceToPair k p q :=
  IsLocalization.Away.lift_eq _ _ _

theorem sourceLocalization_v_unit : IsUnit (sourceLocalization k (v k)) :=
  IsLocalization.Away.algebraMap_isUnit (v k)

noncomputable def pairToAway : (etalePair k p).Ring →+* SourceAway k := by
  letI : Algebra (Plane k) (SourceAway k) := (awayCoordinateMap k p).toAlgebra
  refine ((etalePair k p).lift (sourceLocalization k (u k)) ⟨?_, ?_⟩).toRingHom
  · change aeval (sourceLocalization k (u k))
      (X ^ p + C (v k) * X - C (u k)) = 0
    simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C]
    change sourceLocalization k (u k) ^ p + awayCoordinateMap k p (v k) *
      sourceLocalization k (u k) - awayCoordinateMap k p (u k) = 0
    simp only [awayCoordinateMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coordinateMap_u, coordinateMap_v,
      map_add, map_pow, map_mul]
    ring
  · change IsUnit (aeval (sourceLocalization k (u k)) (C (v k)))
    rw [aeval_C]
    change IsUnit (awayCoordinateMap k p (v k))
    simpa only [awayCoordinateMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coordinateMap_v] using
      sourceLocalization_v_unit k

@[simp] theorem pairToAway_root :
    pairToAway k p (etalePair k p).X = sourceLocalization k (u k) := by
  simp [pairToAway]

theorem pairToAway_commutes (q : Plane k) :
    pairToAway k p (algebraMap (Plane k) (etalePair k p).Ring q) = awayCoordinateMap k p q := by
  unfold pairToAway
  letI : Algebra (Plane k) (SourceAway k) := (awayCoordinateMap k p).toAlgebra
  exact ((etalePair k p).lift _ _).commutes q

theorem pairToAway_sourceToPair :
    (pairToAway k p).comp (sourceToPair k p).toRingHom = sourceLocalization k := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change pairToAway k p (sourceToPair k p (MvPolynomial.C a)) = _
    rw [show MvPolynomial.C a = algebraMap k (Plane k) a by rfl, (sourceToPair k p).commutes,
      IsScalarTower.algebraMap_apply k (Plane k) (etalePair k p).Ring,
      pairToAway_commutes]
    simp [awayCoordinateMap]
  · intro i
    fin_cases i
    · change pairToAway k p (sourceToPair k p (u k)) = _
      simp only [sourceToPair_u, pairToAway_root]
      rfl
    · change pairToAway k p (sourceToPair k p (v k)) = _
      rw [sourceToPair_v, pairToAway_commutes]
      change sourceLocalization k (coordinateMap k p (v k)) = sourceLocalization k (v k)
      rw [coordinateMap_v]

theorem awayToPair_map (q : Plane k) :
    awayToPair k p (awayCoordinateMap k p q) =
      algebraMap (Plane k) (etalePair k p).Ring q := by
  change awayToPair k p (sourceLocalization k (coordinateMap k p q)) = _
  rw [awayToPair_on_source]
  exact congrArg (fun f : Plane k →ₐ[k] (etalePair k p).Ring => f q) (sourceToPair_map k p)

theorem pairToAway_awayToPair :
    (pairToAway k p).comp (awayToPair k p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (v k))
  apply RingHom.ext
  intro q
  change pairToAway k p (awayToPair k p (sourceLocalization k q)) = sourceLocalization k q
  rw [awayToPair_on_source]
  exact congrArg (fun f : Plane k →+* SourceAway k => f q) (pairToAway_sourceToPair k p)

theorem awayToPair_pairToAway :
    (awayToPair k p).comp (pairToAway k p) = RingHom.id _ := by
  let h : (etalePair k p).Ring →ₐ[Plane k] (etalePair k p).Ring :=
    ⟨(awayToPair k p).comp (pairToAway k p), fun q => by
      change awayToPair k p (pairToAway k p (algebraMap _ _ q)) = _
      rw [pairToAway_commutes, awayToPair_map]⟩
  have heq : h = AlgHom.id _ _ := (etalePair k p).hom_ext (by simp [h])
  exact congrArg AlgHom.toRingHom heq

/-- The actual ambient coordinate map is étale after inverting the source `v`. -/
theorem awayCoordinateMap_etale : (awayCoordinateMap k p).Etale := by
  letI : Algebra (Plane k) (SourceAway k) := (awayCoordinateMap k p).toAlgebra
  let e : (etalePair k p).Ring ≃ₐ[Plane k] SourceAway k :=
    { RingEquiv.ofRingHom (pairToAway k p) (awayToPair k p)
        (pairToAway_awayToPair k p) (awayToPair_pairToAway k p) with
      commutes' := pairToAway_commutes k p }
  haveI : Algebra.Etale (Plane k) (SourceAway k) := Algebra.Etale.of_equiv e
  exact RingHom.etale_algebraMap.mpr inferInstance

noncomputable def sourceOpen : (Spec (.of (Plane k))).Opens := PrimeSpectrum.basicOpen (v k)

/-- The actual scheme map restricted on its source to `D(v)` is étale. -/
theorem schemeMap_sourceOpen_etale : Etale ((sourceOpen k).ι ≫ schemeMap k p) := by
  haveI : Etale (Spec.map (CommRingCat.ofHom (awayCoordinateMap k p))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (awayCoordinateMap_etale k p)
  have h : (sourceOpen k).ι ≫ schemeMap k p =
      (basicOpenIsoSpecAway (R := .of (Plane k)) (v k)).hom ≫
        Spec.map (CommRingCat.ofHom (awayCoordinateMap k p)) := by
    have he : (basicOpenIsoSpecAway (R := .of (Plane k)) (v k)).hom ≫
        Spec.map (CommRingCat.ofHom (sourceLocalization k)) = (sourceOpen k).ι :=
      basicOpenIsoSpecAway_hom_SpecMap (R := .of (Plane k)) (v k)
    unfold schemeMap
    rw [← he, Category.assoc, ← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

/-- The actual ambient morphism is étale at every scheme point off `V(v)`.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_isStacksEtaleAt_off_line
    (q : Spec (.of (Plane k))) (hq : v k ∉ q.asIdeal) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k p) q := by
  let U : (Spec (.of (Plane k))).Opens := sourceOpen k
  exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
    (f := schemeMap k p) U.ι ⟨q, hq⟩).mp
      (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr (schemeMap_sourceOpen_etale k p) ⟨q, hq⟩)

local instance ambientFinite : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).two_le

local instance ambientSurjective : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).two_le

/-- The actual stalk map is formally étale off the invariant line. -/
theorem schemeMap_stalk_formallyEtale_off_line
    (q : Spec (.of (Plane k))) (hq : v k ∉ q.asIdeal) :
    ((schemeMap k p).stalkMap q).hom.FormallyEtale := by
  let f := schemeMap k p
  let U := sourceOpen k
  have e : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of (Plane k))).Opens) := by simp
  haveI : Etale (f.resLE ⊤ U e ≫ (⊤ : (Spec (.of (Plane k))).Opens).ι) := by
    simpa only [Scheme.Hom.resLE_comp_ι] using schemeMap_sourceOpen_etale k p
  have hres : Etale (f.resLE ⊤ U e) :=
    Etale.of_comp _ (⊤ : (Spec (.of (Plane k))).Opens).ι
  exact (Pcf.formallyEtale_respectsIso.arrow_mk_iso_iff
    (f.resLEStalkMap e ⟨q, hq⟩)).mp (Etale.stalkMap_formallyEtale hres ⟨q, hq⟩)

/-- The actual ambient map is generically separable.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_isGenericallySeparable : Pcf.IsGenericallySeparableSchemeMap (schemeMap k p) := by
  apply Pcf.isGenericallySeparableSchemeMap_of_formallyEtale_generic
  apply schemeMap_stalk_formallyEtale_off_line
  rw [genericPoint_eq_bot_of_affine]
  change v k ≠ 0
  exact MvPolynomial.X_ne_zero 1

noncomputable def jacobianMatrix : Matrix (Fin 2) (Fin 2) (Plane k) :=
  fun i j => MvPolynomial.pderiv j (coordinateMap k p (MvPolynomial.X i))

omit [Fact p.Prime] in
/-- The exact affine Jacobian determinant in the source example is `v`.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem jacobianMatrix_det : (jacobianMatrix k p).det = v k := by
  simp [jacobianMatrix, Matrix.det_fin_two, coordinateMap, u, v,
    CharP.cast_eq_zero]

#print axioms etalePair
#print axioms awayCoordinateMap_etale
#print axioms schemeMap_sourceOpen_etale
#print axioms schemeMap_isStacksEtaleAt_off_line
#print axioms schemeMap_stalk_formallyEtale_off_line
#print axioms schemeMap_isGenericallySeparable
#print axioms jacobianMatrix_det

end Pcf.Examples.PaperP.FrobeniusLine
