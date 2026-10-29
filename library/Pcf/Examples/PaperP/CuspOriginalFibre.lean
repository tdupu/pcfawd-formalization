/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.Cusp
public import Pcf.Examples.PaperP.CuspFiber
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Finsupp.Weight

/-!
# The original cusp fibre in `paper-p.tex`

For Example `ex:cusp`, the target of the restricted map is the cuspidal
coordinate ring `k[x,y]/(y²-x³)`. This file identifies the pullback of its
origin ideal under that actual coordinate-ring map with `(u²,u³)=(u²)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CuspOriginalFibre

open Polynomial
open AlgebraicGeometry CategoryTheory

set_option linter.style.haveILetI false

variable (k : Type*) [Field k]

abbrev CoordinateRing := MvPolynomial (Fin 2) k ⧸ Pcf.Examples.Cusp.cuspIdeal k

/-- The origin ideal in the cuspidal coordinate ring. -/
noncomputable def originIdeal : Ideal (CoordinateRing k) :=
  Ideal.map (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k))
    (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1})

/-- The plane origin ideal is the kernel of constant-term evaluation. -/
private theorem planeOrigin_eq_ker :
    (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1} :
      Ideal (MvPolynomial (Fin 2) k)) =
        RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k) := by
  have hset :
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) =
        {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro h
      rcases h with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  rw [← hset]
  ext P
  change P ∈ MvPolynomial.idealOfVars (Fin 2) k ↔
    MvPolynomial.constantCoeff P = 0
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 2) k),
    MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    simpa only [MvPolynomial.constantCoeff_eq] using h 0 (by simp)
  · intro h x hx
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
    subst x
    simpa only [MvPolynomial.constantCoeff_eq] using h

/-- The origin of the affine plane is a maximal ideal. -/
private instance planeOrigin_isMaximal :
    (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1} :
      Ideal (MvPolynomial (Fin 2) k)).IsMaximal := by
  rw [planeOrigin_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)

/-- The origin of the cuspidal cubic is a maximal ideal. -/
instance originIdeal_isMaximal : (originIdeal k).IsMaximal := by
  let : (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1} :
      Ideal (MvPolynomial (Fin 2) k)).IsMaximal := planeOrigin_isMaximal k
  unfold originIdeal
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  rw [planeOrigin_eq_ker]
  change MvPolynomial.constantCoeff
    (MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.X 0 ^ 3) = 0
  simp

/-- Pulling back the cusp origin along the restricted map gives the
scheme fibre ideal `(u²)`. -/
theorem originIdeal_map :
    Ideal.map (Pcf.Examples.Cusp.cuspParam k).toRingHom (originIdeal k) =
      Pcf.Examples.PaperP.CuspFiber.fiberIdeal k := by
  rw [originIdeal, Ideal.map_map]
  change Ideal.map (Pcf.Examples.PaperP.CuspFiber.parametrization k).toRingHom
    (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1}) = _
  exact Pcf.Examples.PaperP.CuspFiber.origin_ideal_map k

/-- The fibre of the actual map from the affine line to the cuspidal
coordinate ring over the cusp origin is nonreduced. -/
theorem originFiber_not_isReduced :
    ¬ IsReduced (k[X] ⧸
      Ideal.map (Pcf.Examples.Cusp.cuspParam k).toRingHom (originIdeal k)) := by
  rw [originIdeal_map]
  exact Pcf.Examples.PaperP.CuspFiber.fiber_not_isReduced k

/-- The actual cusp parametrization is not formally unramified over the
original cuspidal coordinate ring: its origin fibre is nonreduced. -/
theorem parametrization_not_formallyUnramified (k : Type*) [Field k] :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    ¬ Algebra.FormallyUnramified (CoordinateRing k) k[X] := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  intro hunram
  haveI : Algebra.FormallyUnramified (CoordinateRing k) k[X] := hunram
  haveI : IsScalarTower k (CoordinateRing k) k[X] :=
    IsScalarTower.of_algebraMap_eq' (Pcf.Examples.Cusp.cuspParam k).comp_algebraMap.symm
  haveI : Algebra.EssFiniteType (CoordinateRing k) k[X] :=
    Algebra.EssFiniteType.of_comp k (CoordinateRing k) k[X]
  have hrad :
      (Ideal.map (Pcf.Examples.Cusp.cuspParam k).toRingHom
        (originIdeal k)).IsRadical :=
    Algebra.FormallyUnramified.isRadical_map_isMaximal
      (CoordinateRing k) k[X] (originIdeal k)
  exact originFiber_not_isReduced k
    ((Ideal.isRadical_iff_quotient_reduced _).mp hrad)

/-- The original cusp parametrization cannot be étale everywhere. -/
theorem parametrization_not_etale (k : Type*) [Field k] :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    ¬ Algebra.Etale (CoordinateRing k) k[X] := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  intro hetale
  haveI : Algebra.Etale (CoordinateRing k) k[X] := hetale
  exact parametrization_not_formallyUnramified k inferInstance

/-- The restricted map from the affine line to the actual cuspidal cubic. -/
noncomputable def schemeMap :
    Spec (.of k[X]) ⟶ Spec (.of (CoordinateRing k)) :=
  Spec.map (CommRingCat.ofHom (Pcf.Examples.Cusp.cuspParam k).toRingHom)

/-- The original cusp parametrization is not an étale scheme morphism. -/
theorem schemeMap_not_etale : ¬ AlgebraicGeometry.Etale (schemeMap k) := by
  intro hetale
  have hring :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp hetale
  change (Pcf.Examples.Cusp.cuspParam k).toRingHom.Etale at hring
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  exact parametrization_not_etale k (RingHom.etale_algebraMap.mp hring)

/-- On the explicit subalgebra model `k[u²,u³]`, the parameter ring is
the integral closure in the shared function field `k(u)`. -/
noncomputable def parameterRing_integralClosureEquiv :
    k[X] ≃ₐ[Pcf.Examples.Cusp.cuspAlg k]
      integralClosure (Pcf.Examples.Cusp.cuspAlg k) (FractionRing k[X]) := by
  letI : IsIntegralClosure k[X] (Pcf.Examples.Cusp.cuspAlg k)
      (FractionRing k[X]) := Pcf.Examples.Cusp.isIntegralClosure_cuspAlg k
  exact IsIntegralClosure.equiv (Pcf.Examples.Cusp.cuspAlg k) k[X]
    (FractionRing k[X])
      (integralClosure (Pcf.Examples.Cusp.cuspAlg k) (FractionRing k[X]))

/-- The parameter affine line is the spectrum of that integral closure. -/
noncomputable def parameterSpec_integralClosureIso :
    Spec (.of k[X]) ≅
      Spec (.of (integralClosure (Pcf.Examples.Cusp.cuspAlg k)
        (FractionRing k[X]))) :=
  (Scheme.Spec.mapIso (parameterRing_integralClosureEquiv k).toCommRingCatIso.op).symm

/-- The image of the actual quotient-coordinate map is the explicit cusp
subalgebra `k[u²,u³]`. -/
theorem cuspParam_range_eq_cuspAlg :
    (Pcf.Examples.Cusp.cuspParam k).range = Pcf.Examples.Cusp.cuspAlg k := by
  have hrange :
      Set.range (![((X : k[X]) ^ 2), (X : k[X]) ^ 3] : Fin 2 → k[X]) =
        {(X : k[X]) ^ 2, (X : k[X]) ^ 3} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · exact ⟨1, hz.symm⟩
  ext z
  change z ∈ (Pcf.Examples.Cusp.cuspParam k).range ↔
    z ∈ Algebra.adjoin k {(X : k[X]) ^ 2, (X : k[X]) ^ 3}
  rw [← hrange, Algebra.adjoin_range_eq_range_aeval]
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k) p, rfl⟩

/-- The polynomial coordinate ring of the horizontal `x`-axis maps to
the cusp through the coordinate `x`. -/
noncomputable def projection : k[X] →ₐ[k] CoordinateRing k :=
  Polynomial.aeval (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)
    (MvPolynomial.X 0))

@[simp] theorem projection_X :
    projection k (X : k[X]) =
      Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k) (MvPolynomial.X 0) := by
  simp [projection]

private theorem cuspParam_comp_projection :
    (Pcf.Examples.Cusp.cuspParam k).comp (projection k) =
      Polynomial.aeval ((X : k[X]) ^ 2) := by
  ext
  simp

private theorem coordinate_y_sq_eq :
    (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)
      (MvPolynomial.X 1) : CoordinateRing k) ^ 2 =
      (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)
        (MvPolynomial.X 0) : CoordinateRing k) ^ 3 := by
  have hrel : Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)
      (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  simpa only [map_sub, map_pow, sub_eq_zero] using hrel

/-- Every cusp-coordinate function has a representative linear in `y`
with coefficients in `k[x]`. -/
theorem coordinate_normalForm (c : CoordinateRing k) :
    ∃ a b : k[X], c = projection k a + projection k b *
      (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)
        (MvPolynomial.X 1) : CoordinateRing k) := by
  let x : CoordinateRing k :=
    Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k) (MvPolynomial.X 0)
  let y : CoordinateRing k :=
    Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k) (MvPolynomial.X 1)
  have hy : y ^ 2 = x ^ 3 := coordinate_y_sq_eq k
  refine Quotient.inductionOn c ?_
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨Polynomial.C a, 0, ?_⟩
      change (Ideal.Quotient.mkₐ k (Pcf.Examples.Cusp.cuspIdeal k))
        (MvPolynomial.C a) = _
      simp [projection]
  | add p q hp hq =>
      obtain ⟨a, b, hab⟩ := hp
      obtain ⟨a', b', hab'⟩ := hq
      change (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)) p = _ at hab
      change (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)) q = _ at hab'
      refine ⟨a + a', b + b', ?_⟩
      change (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)) (p + q) = _
      rw [map_add, hab, hab']
      simp only [map_add]
      ring
  | mul_X p i hp =>
      obtain ⟨a, b, hab⟩ := hp
      change (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k)) p = _ at hab
      fin_cases i
      · refine ⟨a * X, b * X, ?_⟩
        change (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k))
          (p * MvPolynomial.X 0) = _
        rw [map_mul, hab]
        simp only [map_mul, projection_X]
        ring
      · refine ⟨b * X ^ 3, a, ?_⟩
        change (Ideal.Quotient.mk (Pcf.Examples.Cusp.cuspIdeal k))
          (p * MvPolynomial.X 1) = _
        rw [map_mul, hab]
        simp only [map_mul, map_pow, projection_X]
        linear_combination (projection k b) * hy

private theorem square_substitution_injective :
    Function.Injective (fun a : k[X] => a.comp (X ^ 2)) := by
  intro a b hab
  have hzero : (a - b).comp (X ^ 2 : k[X]) = 0 := by
    have hab' : a.comp (X ^ 2 : k[X]) = b.comp (X ^ 2 : k[X]) := hab
    rw [sub_comp, hab', sub_self]
  rcases (Polynomial.comp_eq_zero_iff.mp hzero) with h | h
  · exact sub_eq_zero.mp h
  · have hq : (X ^ 2 : k[X]) ≠ C ((X ^ 2 : k[X]).coeff 0) := by
      intro heq
      have hd := congrArg Polynomial.natDegree heq
      simp at hd
    exact False.elim (hq h.2)

/-- Even and odd terms in a cusp normal form are independent after
substitution `x=u²`, `y=u³` in characteristic zero. -/
theorem cuspParam_normalForm_independent [CharZero k] (a b : k[X])
    (h : a.comp (X ^ 2) + X ^ 3 * b.comp (X ^ 2) = 0) :
    a = 0 ∧ b = 0 := by
  have hqneg : (X ^ 2 : k[X]).comp (-X) = X ^ 2 := by
    simp only [pow_comp, X_comp]
    ring
  have hX3neg : (X ^ 3 : k[X]).comp (-X) = -(X ^ 3) := by
    simp only [pow_comp, X_comp]
    ring
  have hneg : a.comp (X ^ 2) - X ^ 3 * b.comp (X ^ 2) = 0 := by
    have hh : (a.comp (X ^ 2) + X ^ 3 * b.comp (X ^ 2)).comp (-X) = 0 := by
      simpa only [zero_comp] using congrArg (fun p : k[X] => p.comp (-X)) h
    simpa only [add_comp, mul_comp, comp_assoc, hqneg, hX3neg,
      zero_comp, neg_mul, sub_eq_add_neg] using hh
  have htwo : (2 : k[X]) * (X ^ 3 * b.comp (X ^ 2)) = 0 := by
    linear_combination h - hneg
  have hterm : X ^ 3 * b.comp (X ^ 2) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hbcomp : b.comp (X ^ 2 : k[X]) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (pow_ne_zero _ (by simp))
  have hacomp : a.comp (X ^ 2 : k[X]) = 0 := by
    simpa only [hterm, add_zero] using h
  exact ⟨square_substitution_injective k (by simpa using hacomp),
    square_substitution_injective k (by simpa using hbcomp)⟩

private theorem cuspParam_projection_apply (a : k[X]) :
    Pcf.Examples.Cusp.cuspParam k (projection k a) = a.comp (X ^ 2) := by
  have h := congrArg (fun f : k[X] →ₐ[k] k[X] => f a)
    (cuspParam_comp_projection k)
  simpa only [AlgHom.comp_apply, Polynomial.comp_eq_aeval] using h

/-- The actual cusp coordinate-ring map injects into the parameter ring
in characteristic zero. -/
theorem cuspParam_injective [CharZero k] :
    Function.Injective (Pcf.Examples.Cusp.cuspParam k) := by
  intro c d hcd
  have hzero : Pcf.Examples.Cusp.cuspParam k (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  obtain ⟨a, b, hab⟩ := coordinate_normalForm k (c - d)
  have hparity : a.comp (X ^ 2) + X ^ 3 * b.comp (X ^ 2) = 0 := by
    rw [hab, map_add, map_mul, cuspParam_projection_apply,
      cuspParam_projection_apply, Pcf.Examples.Cusp.cuspParam_y] at hzero
    simpa only [mul_comm] using hzero
  obtain ⟨ha, hb⟩ := cuspParam_normalForm_independent k a b hparity
  rw [ha, hb] at hab
  simp only [map_zero, zero_mul, add_zero] at hab
  exact sub_eq_zero.mp hab

/-- In characteristic zero the quotient coordinate ring of the geometric
cuspidal cubic is exactly the explicit subalgebra `k[u²,u³]`. -/
noncomputable def coordinateRingEquivCuspAlg [CharZero k] :
    CoordinateRing k ≃ₐ[k] Pcf.Examples.Cusp.cuspAlg k := by
  let φ : CoordinateRing k →ₐ[k] Pcf.Examples.Cusp.cuspAlg k :=
    (Pcf.Examples.Cusp.cuspParam k).codRestrict
      (Pcf.Examples.Cusp.cuspAlg k) (fun c => by
        rw [← cuspParam_range_eq_cuspAlg k]
        exact AlgHom.mem_range_self _ c)
  have hinj : Function.Injective φ :=
    (AlgHom.injective_codRestrict _ _ _).mpr (cuspParam_injective k)
  have hsurj : Function.Surjective φ := by
    intro z
    have hz : (z : k[X]) ∈ (Pcf.Examples.Cusp.cuspParam k).range := by
      rw [cuspParam_range_eq_cuspAlg k]
      exact z.property
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, Subtype.ext hc⟩
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- The actual cuspidal coordinate ring has `k[u]` as its integral closure
inside the parameter function field. -/
theorem coordinateRing_isIntegralClosure [CharZero k] :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    letI : Algebra (CoordinateRing k) (FractionRing k[X]) :=
      ((algebraMap k[X] (FractionRing k[X])).comp
        (Pcf.Examples.Cusp.cuspParam k).toRingHom).toAlgebra
    IsIntegralClosure k[X] (CoordinateRing k) (FractionRing k[X]) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : Algebra (CoordinateRing k) (FractionRing k[X]) :=
    ((algebraMap k[X] (FractionRing k[X])).comp
      (Pcf.Examples.Cusp.cuspParam k).toRingHom).toAlgebra
  letI : IsIntegralClosure k[X] (Pcf.Examples.Cusp.cuspAlg k)
      (FractionRing k[X]) := Pcf.Examples.Cusp.isIntegralClosure_cuspAlg k
  have hcompat :
      (algebraMap (Pcf.Examples.Cusp.cuspAlg k) (FractionRing k[X])).comp
        (coordinateRingEquivCuspAlg k).toRingEquiv.toRingHom =
      algebraMap (CoordinateRing k) (FractionRing k[X]) := by
    apply RingHom.ext
    intro c
    change algebraMap k[X] (FractionRing k[X])
      ((coordinateRingEquivCuspAlg k c : Pcf.Examples.Cusp.cuspAlg k) : k[X]) =
      algebraMap k[X] (FractionRing k[X]) (Pcf.Examples.Cusp.cuspParam k c)
    rfl
  refine { algebraMap_injective := IsFractionRing.injective k[X] (FractionRing k[X]),
           isIntegral_iff := ?_ }
  intro z
  exact (RingEquiv.isIntegral_iff (coordinateRingEquivCuspAlg k).toRingEquiv
    hcompat z).trans (IsIntegralClosure.isIntegral_iff
      (A := k[X]) (R := Pcf.Examples.Cusp.cuspAlg k) (B := FractionRing k[X]))

#print axioms originIdeal_map
#print axioms originFiber_not_isReduced
#print axioms parametrization_not_formallyUnramified
#print axioms parametrization_not_etale
#print axioms schemeMap_not_etale
#print axioms parameterRing_integralClosureEquiv
#print axioms parameterSpec_integralClosureIso
#print axioms cuspParam_range_eq_cuspAlg
#print axioms coordinate_normalForm
#print axioms cuspParam_normalForm_independent
#print axioms cuspParam_injective
#print axioms coordinateRingEquivCuspAlg
#print axioms coordinateRing_isIntegralClosure

end Pcf.Examples.PaperP.CuspOriginalFibre
