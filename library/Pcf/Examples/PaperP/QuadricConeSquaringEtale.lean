/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeRestriction
public import Pcf.Examples.PaperP.QuadricConeEtaleCharts
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI

/-!
# The squaring map is étale away from the origin

An explicit standard étale presentation has equation `T²-x` with `T` inverted.
It identifies its algebra with the source polynomial ring localized away from `u`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConeRestriction

open AlgebraicGeometry CategoryTheory Polynomial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

abbrev SourceAway := Localization.Away (X : Polynomial k)

/-- The canonical localization map on the source polynomial ring. -/
noncomputable def sourceLocalization : Polynomial k →+* SourceAway k := algebraMap _ _

omit [CharZero k] in
theorem sourceLocalization_X_unit : IsUnit (sourceLocalization k X) :=
  IsLocalization.Away.algebraMap_isUnit (X : Polynomial k)

/-- The actual squaring map followed by source localization. -/
noncomputable def squareAway : Polynomial k →+* SourceAway k :=
  (sourceLocalization k).comp (coordinateMap k).toRingHom

noncomputable def squaringPair : StandardEtalePair (Polynomial k) :=
  ⟨X ^ 2 - C X, monic_X_pow_sub_C _ (by decide), X,
    C (C ((2 : k)⁻¹)), 0, 1, by
      simp only [derivative_sub, derivative_pow, derivative_X, mul_one, derivative_C,
        sub_zero, mul_zero, add_zero, pow_one, Nat.reduceSub]
      have h2 : (2 : k) * (2 : k)⁻¹ = 1 := mul_inv_cancel₀ (by norm_num)
      have hc := congrArg (fun a : k => (C (C a) : (Polynomial k)[X])) h2
      simp only [map_mul, map_one] at hc
      simp only [map_ofNat, map_natCast] at hc ⊢
      linear_combination X * hc⟩

theorem squaringPair_root_sq : (squaringPair k).X ^ 2 =
    algebraMap (Polynomial k) (squaringPair k).Ring X := by
  have h := (squaringPair k).hasMap_X.1
  change aeval (squaringPair k).X (X ^ 2 - C X) = 0 at h
  simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using h

theorem squaringPair_root_unit : IsUnit (squaringPair k).X := by
  have h := (squaringPair k).hasMap_X.2
  change IsUnit (aeval (squaringPair k).X X) at h
  simpa using h

/-- Send the source parameter to the standard étale generator. -/
noncomputable def sourceToPair : Polynomial k →+* (squaringPair k).Ring :=
  Polynomial.eval₂RingHom
    ((algebraMap (Polynomial k) (squaringPair k).Ring).comp Polynomial.C)
    (squaringPair k).X

@[simp] theorem sourceToPair_X : sourceToPair k X = (squaringPair k).X := by
  simp [sourceToPair]

theorem sourceToPair_square :
    (sourceToPair k).comp (coordinateMap k).toRingHom =
      algebraMap (Polynomial k) (squaringPair k).Ring := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [sourceToPair, coordinateMap, Polynomial.expand_C]
  · simp [squaringPair_root_sq]

noncomputable def awayToPair : SourceAway k →+* (squaringPair k).Ring :=
  IsLocalization.Away.lift (X : Polynomial k)
    (g := sourceToPair k) (by rw [sourceToPair_X]; exact squaringPair_root_unit k)

@[simp] theorem awayToPair_on_source (p : Polynomial k) :
    awayToPair k (sourceLocalization k p) = sourceToPair k p := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The standard étale map into the actual source localization. -/
noncomputable def pairToAway : (squaringPair k).Ring →+* SourceAway k := by
  letI : Algebra (Polynomial k) (SourceAway k) := (squareAway k).toAlgebra
  refine ((squaringPair k).lift (sourceLocalization k X) ⟨?_, ?_⟩).toRingHom
  · change aeval (sourceLocalization k X) (X ^ 2 - C X) = 0
    simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    change sourceLocalization k X ^ 2 = squareAway k X
    simp [squareAway, coordinateMap_X]
  · change IsUnit (aeval (sourceLocalization k X) X)
    simpa only [aeval_X] using sourceLocalization_X_unit k

@[simp] theorem pairToAway_X :
    pairToAway k (squaringPair k).X = sourceLocalization k X := by
  simp [pairToAway]

theorem pairToAway_commutes (p : Polynomial k) :
    pairToAway k (algebraMap (Polynomial k) (squaringPair k).Ring p) = squareAway k p := by
  unfold pairToAway
  letI : Algebra (Polynomial k) (SourceAway k) := (squareAway k).toAlgebra
  exact ((squaringPair k).lift _ _).commutes p

theorem pairToAway_sourceToPair :
    (pairToAway k).comp (sourceToPair k) = sourceLocalization k := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, sourceToPair, coe_eval₂RingHom, eval₂_C]
    change pairToAway k (algebraMap (Polynomial k) (squaringPair k).Ring (C a)) = _
    rw [pairToAway_commutes]
    simp [squareAway, coordinateMap]
  · simp

theorem awayToPair_square (p : Polynomial k) :
    awayToPair k (squareAway k p) = algebraMap (Polynomial k) (squaringPair k).Ring p := by
  change awayToPair k (sourceLocalization k (coordinateMap k p)) = _
  rw [awayToPair_on_source]
  exact congrArg (fun f : Polynomial k →+* (squaringPair k).Ring => f p)
    (sourceToPair_square k)

theorem pairToAway_awayToPair :
    (pairToAway k).comp (awayToPair k) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : Polynomial k))
  apply RingHom.ext
  intro p
  change pairToAway k (awayToPair k (sourceLocalization k p)) = sourceLocalization k p
  rw [awayToPair_on_source]
  exact congrArg (fun f : Polynomial k →+* SourceAway k => f p)
    (pairToAway_sourceToPair k)

theorem awayToPair_pairToAway :
    (awayToPair k).comp (pairToAway k) = RingHom.id _ := by
  let h : (squaringPair k).Ring →ₐ[Polynomial k] (squaringPair k).Ring :=
    ⟨(awayToPair k).comp (pairToAway k), fun p => by
      change awayToPair k (pairToAway k (algebraMap _ _ p)) = _
      rw [pairToAway_commutes, awayToPair_square]⟩
  have heq : h = AlgHom.id _ _ := (squaringPair k).hom_ext (by simp [h])
  exact congrArg AlgHom.toRingHom heq

/-- The actual squaring coordinate map is étale after source localization at `u`. -/
theorem squareAway_etale : (squareAway k).Etale := by
  letI : Algebra (Polynomial k) (SourceAway k) := (squareAway k).toAlgebra
  let e : (squaringPair k).Ring ≃ₐ[Polynomial k] SourceAway k :=
    { RingEquiv.ofRingHom (pairToAway k) (awayToPair k)
        (pairToAway_awayToPair k) (awayToPair_pairToAway k) with
      commutes' := pairToAway_commutes k }
  haveI : Algebra.Etale (Polynomial k) (SourceAway k) := Algebra.Etale.of_equiv e
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The source coordinate open `D(u)`. -/
noncomputable def sourceOpen : (Spec (.of (Polynomial k))).Opens :=
  PrimeSpectrum.basicOpen (X : Polynomial k)

/-- The actual scheme map with only its source restricted to `D(u)` is étale. -/
theorem schemeMap_sourceAway_etale :
    Etale ((sourceOpen k).ι ≫ schemeMap k) := by
  haveI : Etale (Spec.map (CommRingCat.ofHom (squareAway k))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (squareAway_etale k)
  have h : (sourceOpen k).ι ≫ schemeMap k =
      (basicOpenIsoSpecAway (R := .of (Polynomial k)) X).hom ≫
        Spec.map (CommRingCat.ofHom (squareAway k)) := by
    have he : (basicOpenIsoSpecAway (R := .of (Polynomial k)) X).hom ≫
        Spec.map (CommRingCat.ofHom (sourceLocalization k)) = (sourceOpen k).ι :=
      basicOpenIsoSpecAway_hom_SpecMap (R := .of (Polynomial k)) X
    unfold schemeMap
    rw [← he, Category.assoc, ← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

/-- At all scheme points where the source parameter is invertible, squaring is étale. -/
theorem schemeMap_isStacksEtaleAt_of_X_notMem
    (p : Spec (.of (Polynomial k))) (hp : X ∉ p.asIdeal) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k) p := by
  let U : (Spec (.of (Polynomial k))).Opens := sourceOpen k
  exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
    (f := schemeMap k) U.ι ⟨p, hp⟩).mp
      (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr (schemeMap_sourceAway_etale k) ⟨p, hp⟩)

#print axioms squaringPair
#print axioms sourceToPair_square
#print axioms pairToAway_commutes
#print axioms squareAway_etale
#print axioms schemeMap_sourceAway_etale
#print axioms schemeMap_isStacksEtaleAt_of_X_notMem

end Pcf.Examples.PaperP.QuadricConeRestriction
