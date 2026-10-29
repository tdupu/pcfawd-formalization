/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.DegreeOnlyResidueMap
public import Pcf.Examples.PaperP.MonodromyLossPhiMonodromy
public import Mathlib.FieldTheory.Separable
public import Pcf.Bounding.SchemeWeightedCriticalFinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The generic degree `p + 1` and generic separability of `F`

For the map `F^*(u) = x^p + x w`, `F^*(v) = w (x - 1)` of `DegreeOnlyResidueMap`:

* `finrank_of_fractionRings`, `isSeparable_of_fractionRings`: for any fraction fields
  `K` of `k[u,v]` and `L` of `k[x,w]`, and any `K → L` restricting to `F^*`, the
  extension `L / K` has degree `p + 1` and is separable. The degree comes from the
  free rank of `k[x,w]` over `k[u,v]`. Separability: `L = K(x)`, and `x` is a root of
  `P = T^{p+1} - T^p - (u-v) T + u`, whose derivative in characteristic `p` is
  `P' = T^p - (u - v)`; the identity `P + (1 - T) P' = v` makes `P` separable.
* `schemeMap_genericDegree`, `schemeMap_isGenericallySeparable`: the same for the actual
  generic stalk map of the scheme morphism.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.DegreeOnlyResidue

open AlgebraicGeometry CategoryTheory Polynomial IntermediateField
open Pcf.Examples.PaperP.FrobeniusLine (Plane u v)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe w

variable {k : Type w} [Field k] {p : ℕ}

section Fields

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (iB : Plane k →+* K) (iA : Plane k →+* L)
  (hB : @IsFractionRing (Plane k) _ K _ iB.toAlgebra)
  (hA : @IsFractionRing (Plane k) _ L _ iA.toAlgebra)
  (hcomm : (algebraMap K L).comp iB = iA.comp (coordinateMap k p).toRingHom)

include hB hA hcomm in
/-- The function-field degree is the free rank `p + 1`. -/
theorem finrank_of_fractionRings (hp : 0 < p) : Module.finrank K L = p + 1 := by
  letI : Algebra (Plane k) K := iB.toAlgebra
  letI : Algebra (Source k p) L := (iA.comp (toSource k p).symm.toRingHom).toAlgebra
  letI : Algebra (Plane k) L := (iA.comp (coordinateMap k p).toRingHom).toAlgebra
  haveI : IsFractionRing (Source k p) L := hA
  haveI : IsScalarTower (Plane k) K L := IsScalarTower.of_algebraMap_eq fun b =>
    (congrArg (fun f => f b) hcomm).symm
  haveI : IsScalarTower (Plane k) (Source k p) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [IsFractionRing.finrank_eq (Plane k) K (Source k p) L, finrank_source k p hp]

omit hB in
include hA hcomm in
/-- Every element of `L` lies in `K(x)`. -/
theorem adjoin_x_eq_top : K⟮iA (u k)⟯ = ⊤ := by
  set E := K⟮iA (u k)⟯
  have hx : iA (u k) ∈ E := IntermediateField.mem_adjoin_simple_self K _
  have hc (b : Plane k) : iA (coordinateMap k p b) ∈ E := by
    have h : iA (coordinateMap k p b) = algebraMap K L (iB b) :=
      (congrArg (fun f => f b) hcomm).symm
    rw [h]
    exact E.algebraMap_mem _
  have hall (a : Plane k) : iA a ∈ E := by
    induction a using MvPolynomial.induction_on with
    | C c =>
        have := hc (MvPolynomial.C c)
        rwa [show coordinateMap k p (MvPolynomial.C c) = MvPolynomial.C c from
          (coordinateMap k p).commutes c] at this
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | mul_X a i ha =>
        rw [map_mul]
        refine mul_mem ha ?_
        fin_cases i
        · exact hx
        · have hw : (MvPolynomial.X 1 : Plane k) =
              coordinateMap k p (u k) - coordinateMap k p (v k) - u k ^ p := by
            rw [coordinateMap_u, coordinateMap_v]
            simp only [u, v]
            ring
          change iA (MvPolynomial.X 1) ∈ E
          rw [hw, map_sub, map_sub, map_pow]
          exact sub_mem (sub_mem (hc _) (hc _)) (pow_mem hx _)
  rw [eq_top_iff]
  intro l _
  letI : Algebra (Plane k) L := iA.toAlgebra
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Plane k) l
  exact div_mem (hall a) (hall b)

omit hA in
include hB hcomm in
/-- `x` is separable over `K`. -/
theorem isSeparable_x [CharP k p] : IsSeparable K (iA (u k)) := by
  letI : Algebra (Plane k) K := iB.toAlgebra
  have hinj : Function.Injective iB := IsFractionRing.injective (Plane k) K
  haveI : CharP K p := charP_of_injective_ringHom
    (iB.comp (algebraMap k (Plane k))).injective p
  set Q := (minPoly k p).map iB
  have hroot : aeval (iA (u k)) Q = 0 := by
    rw [aeval_def, eval₂_map, hcomm, ← hom_eval₂]
    have h := aeval_xs k (p := p)
    rw [aeval_def] at h
    rw [show eval₂ (coordinateMap k p).toRingHom (u k) (minPoly k p) = 0 from h, map_zero]
  have hsep : Q.Separable := by
    have hv : iB (v k) ≠ 0 := by
      rw [map_ne_zero_iff _ hinj]
      exact MvPolynomial.X_ne_zero 1
    have hder : derivative Q = X ^ p - C (iB (u k - v k)) := by
      simp only [Q, minPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, map_C, derivative_add, derivative_sub, derivative_mul,
        derivative_X_pow, derivative_C, derivative_X]
      simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, zero_add, map_one, one_mul,
        map_zero, zero_mul, mul_one, Nat.add_sub_cancel, sub_zero, add_zero]
    have hid : Q + (1 - X) * derivative Q = C (iB (v k)) := by
      rw [hder]
      simp only [Q, minPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, map_C, map_sub]
      ring
    refine ⟨C (iB (v k))⁻¹, C (iB (v k))⁻¹ * (1 - X), ?_⟩
    rw [mul_assoc, ← mul_add, hid, ← C_mul, inv_mul_cancel₀ hv, C_1]
  exact hsep.of_dvd (minpoly.dvd K _ hroot)

include hB hA hcomm in
/-- **The function-field extension is separable.** -/
theorem isSeparable_of_fractionRings [CharP k p] : Algebra.IsSeparable K L := by
  haveI : Algebra.IsSeparable K K⟮iA (u k)⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr
      (isSeparable_x iB iA hB hcomm)
  exact Algebra.IsSeparable.of_algHom K K⟮iA (u k)⟯
    (((IntermediateField.equivOfEq (adjoin_x_eq_top iB iA hA hcomm)).symm.toAlgHom).comp
      IntermediateField.topEquiv.symm.toAlgHom)

end Fields

section Stalks

open Pcf.Examples.PaperP.MonodromyLossCurve (stalkCoord stalkCoord_isFractionRing
  SpecMap_stalkMap_stalkCoord genericPoint_asIdeal_Spec)

variable (k p)

theorem schemeMap_genericPoint_asIdeal (hp : 0 < p) :
    (schemeMap k p (genericPoint (Spec (.of (Plane k))))).asIdeal = ⊥ := by
  change ((genericPoint (Spec (.of (Plane k)))).asIdeal).comap (coordinateMap k p).toRingHom = ⊥
  rw [genericPoint_asIdeal_Spec]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (coordinateMap_injective k p hp)

theorem stalk_square :
    ((schemeMap k p).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.comp
      (stalkCoord (schemeMap k p (genericPoint (Spec (.of (Plane k)))))) =
    (stalkCoord (genericPoint (Spec (.of (Plane k))))).comp
      (coordinateMap k p).toRingHom :=
  RingHom.ext fun a => SpecMap_stalkMap_stalkCoord (coordinateMap k p).toRingHom _ a

/-- **(b) Generic degree `p + 1`.** The actual generic stalk extension of `F` has degree
`p + 1`. -/
theorem schemeMap_genericDegree (hp : 0 < p) :
    letI := ((schemeMap k p).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.toAlgebra
    Module.finrank
      ((Spec (.of (Plane k))).presheaf.stalk (schemeMap k p (genericPoint (Spec (.of (Plane k))))))
      ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k))))) = p + 1 := by
  let η := genericPoint (Spec (.of (Plane k)))
  have hB := stalkCoord_isFractionRing _ (schemeMap_genericPoint_asIdeal k p hp)
  have hA := stalkCoord_isFractionRing η genericPoint_asIdeal_Spec
  haveI : Surjective (schemeMap k p) := schemeMap_surjective k p hp
  have hgp : schemeMap k p η = genericPoint (Spec (.of (Plane k))) :=
    map_genericPoint_eq_of_isDominant _
  let e := ((Spec (.of (Plane k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field ((Spec (.of (Plane k))).presheaf.stalk (schemeMap k p η)) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI := ((schemeMap k p).stalkMap η).hom.toAlgebra
  exact finrank_of_fractionRings _ _ hB hA (stalk_square k p) hp

/-- The degree `p + 1` of `F` is prime to `p`. -/
theorem schemeMap_genericDegree_coprime [Fact p.Prime] :
    letI := ((schemeMap k p).stalkMap (genericPoint (Spec (.of (Plane k))))).hom.toAlgebra
    (Module.finrank
      ((Spec (.of (Plane k))).presheaf.stalk (schemeMap k p (genericPoint (Spec (.of (Plane k))))))
      ((Spec (.of (Plane k))).presheaf.stalk (genericPoint (Spec (.of (Plane k)))))).Coprime p := by
  rw [schemeMap_genericDegree k p (Fact.out : p.Prime).pos]
  exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left p)

local instance schemeMapFinite [Fact p.Prime] : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).pos
local instance schemeMapSurjective [Fact p.Prime] : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).pos

/-- **(a) Generic separability.** -/
theorem schemeMap_isGenericallySeparable [Fact p.Prime] [CharP k p] :
    Pcf.IsGenericallySeparableSchemeMap (schemeMap k p) := by
  let η := genericPoint (Spec (.of (Plane k)))
  have hB := stalkCoord_isFractionRing _ (schemeMap_genericPoint_asIdeal k p
    (Fact.out : p.Prime).pos)
  have hA := stalkCoord_isFractionRing η genericPoint_asIdeal_Spec
  have hgp : schemeMap k p η = genericPoint (Spec (.of (Plane k))) :=
    map_genericPoint_eq_of_isDominant _
  let e := ((Spec (.of (Plane k))).presheaf.stalkCongr
    (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field ((Spec (.of (Plane k))).presheaf.stalk (schemeMap k p η)) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI := ((schemeMap k p).stalkMap η).hom.toAlgebra
  exact isSeparable_of_fractionRings _ _ hB hA (stalk_square k p)

#print axioms finrank_of_fractionRings
#print axioms isSeparable_of_fractionRings
#print axioms schemeMap_genericDegree
#print axioms schemeMap_genericDegree_coprime
#print axioms schemeMap_isGenericallySeparable

end Stalks

end Pcf.Examples.PaperP.DegreeOnlyResidue
