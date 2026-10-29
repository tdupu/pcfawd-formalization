/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Pcf.Bounding.CriticalLoci

/-!
# Squaring one coordinate is étale where that coordinate is a unit

For a field `k` with `2 ≠ 0` and a polynomial ring `k[X_j]`, the substitution
`X_i ↦ X_i²` (other variables fixed) becomes étale after inverting `X_i` in the source:
an explicit standard étale pair `T² - X_i` with `T` inverted is identified with the
localized source ring. Composing over all coordinates gives the étaleness of coordinate
squaring `(x, y) ↦ (x², y²)` on `D(xy)`, used for `paper-p.tex`,
Example `ex:frobenius-pinching`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CoordinateSquareEtale

open AlgebraicGeometry CategoryTheory Polynomial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (σ : Type*) [DecidableEq σ] (i : σ)

abbrev P := MvPolynomial σ k

/-- Squaring the `i`-th coordinate. -/
noncomputable def sq : P k σ →ₐ[k] P k σ :=
  MvPolynomial.aeval (fun j => if j = i then MvPolynomial.X j ^ 2 else MvPolynomial.X j)

@[simp] theorem sq_X_self : sq k σ i (MvPolynomial.X i) = MvPolynomial.X i ^ 2 := by
  simp [sq]

@[simp] theorem sq_X_ne {j : σ} (h : j ≠ i) :
    sq k σ i (MvPolynomial.X j) = MvPolynomial.X j := by
  simp [sq, h]

abbrev SourceAway := Localization.Away (MvPolynomial.X i : P k σ)

noncomputable def sourceLoc : P k σ →+* SourceAway k σ i := algebraMap _ _

noncomputable def awaySq : P k σ →+* SourceAway k σ i :=
  (sourceLoc k σ i).comp (sq k σ i).toRingHom

variable (h2 : (2 : k) ≠ 0)

/-- The standard étale pair `T² - X_i`, `g = X_i`. -/
noncomputable def pair : StandardEtalePair (P k σ) :=
  ⟨X ^ 2 - C (MvPolynomial.X i), monic_X_pow_sub_C _ two_ne_zero,
   C (MvPolynomial.X i),
   ⟨C (MvPolynomial.C (2 : k)⁻¹) * X, -1, 1, by
      rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_one]
      have h : (MvPolynomial.C (2 : k)⁻¹ : P k σ) * 2 = 1 := by
        rw [show (2 : P k σ) = MvPolynomial.C 2 from (map_ofNat _ 2).symm, ← map_mul,
          inv_mul_cancel₀ h2, map_one]
      have h' : (C (MvPolynomial.C (2 : k)⁻¹) : (P k σ)[X]) * C 2 = 1 := by
        rw [← C_mul, h, C_1]
      simp only [Nat.cast_ofNat]
      linear_combination (X ^ 2 : (P k σ)[X]) * h'⟩⟩


noncomputable instance pairKAlgebra : Algebra k (pair k σ i h2).Ring :=
  ((algebraMap (P k σ) (pair k σ i h2).Ring).comp (algebraMap k (P k σ))).toAlgebra

instance pairKTower : IsScalarTower k (P k σ) (pair k σ i h2).Ring :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem pair_root_relation : (pair k σ i h2).X ^ 2 =
    algebraMap (P k σ) (pair k σ i h2).Ring (MvPolynomial.X i) := by
  have h := (pair k σ i h2).hasMap_X.1
  change aeval (pair k σ i h2).X (X ^ 2 - C (MvPolynomial.X i)) = 0 at h
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h

theorem pair_unit : IsUnit (algebraMap (P k σ) (pair k σ i h2).Ring (MvPolynomial.X i)) := by
  have h := (pair k σ i h2).hasMap_X.2
  change IsUnit (aeval (pair k σ i h2).X (C (MvPolynomial.X i))) at h
  simpa using h

theorem pair_X_unit : IsUnit (pair k σ i h2).X := by
  have h := pair_unit k σ i h2
  rw [← pair_root_relation, pow_two] at h
  exact isUnit_of_mul_isUnit_left h

/-- Source coordinates into the pair ring: `X_i ↦ T`, `X_j ↦ X_j`. -/
noncomputable def sourceToPair : P k σ →ₐ[k] (pair k σ i h2).Ring :=
  MvPolynomial.aeval (fun j => if j = i then (pair k σ i h2).X
    else algebraMap (P k σ) (pair k σ i h2).Ring (MvPolynomial.X j))

@[simp] theorem sourceToPair_self :
    sourceToPair k σ i h2 (MvPolynomial.X i) = (pair k σ i h2).X := by
  simp [sourceToPair]

@[simp] theorem sourceToPair_ne {j : σ} (h : j ≠ i) :
    sourceToPair k σ i h2 (MvPolynomial.X j) =
      algebraMap (P k σ) (pair k σ i h2).Ring (MvPolynomial.X j) := by
  simp [sourceToPair, h]

theorem sourceToPair_sq : (sourceToPair k σ i h2).comp (sq k σ i) =
    IsScalarTower.toAlgHom k (P k σ) (pair k σ i h2).Ring := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases h : j = i
  · subst h
    change sourceToPair k σ j h2 (sq k σ j (MvPolynomial.X j)) = _
    rw [sq_X_self, map_pow, sourceToPair_self, pair_root_relation]
    rfl
  · change sourceToPair k σ i h2 (sq k σ i (MvPolynomial.X j)) = _
    rw [sq_X_ne k σ i h, sourceToPair_ne k σ i h2 h]
    rfl

noncomputable def awayToPair : SourceAway k σ i →+* (pair k σ i h2).Ring :=
  IsLocalization.Away.lift (MvPolynomial.X i) (g := (sourceToPair k σ i h2).toRingHom)
    (by change IsUnit (sourceToPair k σ i h2 _); rw [sourceToPair_self]; exact pair_X_unit k σ i h2)

@[simp] theorem awayToPair_on_source (q : P k σ) :
    awayToPair k σ i h2 (algebraMap _ _ q) = sourceToPair k σ i h2 q :=
  IsLocalization.Away.lift_eq _ _ _

theorem sourceLoc_X_isUnit : IsUnit (sourceLoc k σ i (MvPolynomial.X i)) :=
  IsLocalization.Away.algebraMap_isUnit _

noncomputable def pairToAway : (pair k σ i h2).Ring →+* SourceAway k σ i := by
  letI : Algebra (P k σ) (SourceAway k σ i) := (awaySq k σ i).toAlgebra
  refine ((pair k σ i h2).lift (sourceLoc k σ i (MvPolynomial.X i))
    ⟨?_, ?_⟩).toRingHom
  · change aeval (sourceLoc k σ i (MvPolynomial.X i))
      (X ^ 2 - C (MvPolynomial.X i)) = 0
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    change _ - awaySq k σ i (MvPolynomial.X i) = 0
    simp [awaySq]
  · change IsUnit (aeval (sourceLoc k σ i (MvPolynomial.X i))
      (C (MvPolynomial.X i)))
    rw [aeval_C]
    change IsUnit (awaySq k σ i (MvPolynomial.X i))
    simp only [awaySq, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sq_X_self,
      map_pow]
    exact (sourceLoc_X_isUnit k σ i).pow 2

@[simp] theorem pairToAway_root :
    pairToAway k σ i h2 (pair k σ i h2).X = sourceLoc k σ i (MvPolynomial.X i) := by
  simp [pairToAway]

theorem pairToAway_commutes (q : P k σ) :
    pairToAway k σ i h2 (algebraMap (P k σ) (pair k σ i h2).Ring q) = awaySq k σ i q := by
  unfold pairToAway
  letI : Algebra (P k σ) (SourceAway k σ i) := (awaySq k σ i).toAlgebra
  exact ((pair k σ i h2).lift _ _).commutes q

theorem pairToAway_sourceToPair :
    (pairToAway k σ i h2).comp (sourceToPair k σ i h2).toRingHom = sourceLoc k σ i := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change pairToAway k σ i h2 (sourceToPair k σ i h2 (MvPolynomial.C a)) = _
    rw [show MvPolynomial.C a = algebraMap k (P k σ) a by rfl, (sourceToPair k σ i h2).commutes,
      IsScalarTower.algebraMap_apply k (P k σ) (pair k σ i h2).Ring, pairToAway_commutes]
    simp [awaySq, sourceLoc]
  · intro j
    change pairToAway k σ i h2 (sourceToPair k σ i h2 (MvPolynomial.X j)) = _
    by_cases h : j = i
    · subst h
      rw [sourceToPair_self, pairToAway_root]
    · rw [sourceToPair_ne k σ i h2 h, pairToAway_commutes]
      simp [awaySq, sourceLoc, sq_X_ne k σ i h]

theorem awayToPair_map (q : P k σ) :
    awayToPair k σ i h2 (awaySq k σ i q) =
      algebraMap (P k σ) (pair k σ i h2).Ring q := by
  change awayToPair k σ i h2 (sourceLoc k σ i (sq k σ i q)) = _
  rw [show sourceLoc k σ i (sq k σ i q) = algebraMap _ _ (sq k σ i q) from rfl,
    awayToPair_on_source]
  exact congrArg (fun f : P k σ →ₐ[k] (pair k σ i h2).Ring => f q) (sourceToPair_sq k σ i h2)

theorem pairToAway_awayToPair :
    (pairToAway k σ i h2).comp (awayToPair k σ i h2) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.X i : P k σ))
  apply RingHom.ext
  intro q
  change pairToAway k σ i h2 (awayToPair k σ i h2 (sourceLoc k σ i q)) = sourceLoc k σ i q
  rw [show sourceLoc k σ i q = algebraMap _ _ q from rfl, awayToPair_on_source]
  exact congrArg (fun f : P k σ →+* SourceAway k σ i => f q) (pairToAway_sourceToPair k σ i h2)

theorem awayToPair_pairToAway :
    (awayToPair k σ i h2).comp (pairToAway k σ i h2) = RingHom.id _ := by
  let h : (pair k σ i h2).Ring →ₐ[P k σ] (pair k σ i h2).Ring :=
    ⟨(awayToPair k σ i h2).comp (pairToAway k σ i h2), fun q => by
      change awayToPair k σ i h2 (pairToAway k σ i h2 (algebraMap _ _ q)) = _
      rw [pairToAway_commutes, awayToPair_map]⟩
  have heq : h = AlgHom.id _ _ := (pair k σ i h2).hom_ext (by
    change awayToPair k σ i h2 (pairToAway k σ i h2 (pair k σ i h2).X) = _
    rw [pairToAway_root, show sourceLoc k σ i (MvPolynomial.X i) = algebraMap _ _ _ from rfl,
      awayToPair_on_source, sourceToPair_self]
    rfl)
  exact congrArg AlgHom.toRingHom heq

/-- Squaring `X_i` is étale after inverting `X_i` in the source. -/
theorem awaySq_etale (h2 : (2 : k) ≠ 0) : (awaySq k σ i).Etale := by
  letI : Algebra (P k σ) (SourceAway k σ i) := (awaySq k σ i).toAlgebra
  let e : (pair k σ i h2).Ring ≃ₐ[P k σ] SourceAway k σ i :=
    { RingEquiv.ofRingHom (pairToAway k σ i h2) (awayToPair k σ i h2)
        (pairToAway_awayToPair k σ i h2) (awayToPair_pairToAway k σ i h2) with
      commutes' := pairToAway_commutes k σ i h2 }
  haveI : Algebra.Etale (P k σ) (SourceAway k σ i) := Algebra.Etale.of_equiv e
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The scheme map of squaring `X_i`. -/
noncomputable def sqScheme : Spec (.of (P k σ)) ⟶ Spec (.of (P k σ)) :=
  Spec.map (CommRingCat.ofHom (sq k σ i).toRingHom)

noncomputable def sourceOpen : (Spec (.of (P k σ))).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X i : P k σ)

theorem sqScheme_sourceOpen_etale (h2 : (2 : k) ≠ 0) : Etale ((sourceOpen k σ i).ι ≫ sqScheme k σ i) := by
  haveI : Etale (Spec.map (CommRingCat.ofHom (awaySq k σ i))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (awaySq_etale k σ i h2)
  have h : (sourceOpen k σ i).ι ≫ sqScheme k σ i =
      (basicOpenIsoSpecAway (R := .of (P k σ)) (MvPolynomial.X i)).hom ≫
        Spec.map (CommRingCat.ofHom (awaySq k σ i)) := by
    have he : (basicOpenIsoSpecAway (R := .of (P k σ)) (MvPolynomial.X i)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (P k σ) (SourceAway k σ i))) =
          (sourceOpen k σ i).ι :=
      basicOpenIsoSpecAway_hom_SpecMap (R := .of (P k σ)) (MvPolynomial.X i)
    unfold sqScheme
    rw [← he, Category.assoc, ← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

/-- The stalk of `X_i ↦ X_i²` is formally étale at every point with `X_i ∉ q`. -/
theorem sqScheme_stalk_formallyEtale (h2 : (2 : k) ≠ 0) (q : Spec (.of (P k σ)))
    (hq : (MvPolynomial.X i : P k σ) ∉ q.asIdeal) :
    ((sqScheme k σ i).stalkMap q).hom.FormallyEtale := by
  let f := sqScheme k σ i
  let U := sourceOpen k σ i
  have e : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of (P k σ))).Opens) := by simp
  haveI : Etale (f.resLE ⊤ U e ≫ (⊤ : (Spec (.of (P k σ))).Opens).ι) := by
    simpa only [Scheme.Hom.resLE_comp_ι] using sqScheme_sourceOpen_etale k σ i h2
  have hres : Etale (f.resLE ⊤ U e) :=
    Etale.of_comp _ (⊤ : (Spec (.of (P k σ))).Opens).ι
  exact (Pcf.formallyEtale_respectsIso.arrow_mk_iso_iff
    (f.resLEStalkMap e ⟨q, hq⟩)).mp (Etale.stalkMap_formallyEtale hres ⟨q, hq⟩)

#print axioms awaySq_etale
#print axioms sqScheme_stalk_formallyEtale

end Pcf.Examples.PaperP.CoordinateSquareEtale
