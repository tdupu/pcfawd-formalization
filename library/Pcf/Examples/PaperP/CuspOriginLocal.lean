/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CuspNormalization
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The source point above the cusp origin

For the remark after `paper-p.tex`, Example `ex:cusp`, the source point
`u = 0` lies above the actual cusp origin. Its fibre has coordinate ring
`k[u]/(u²)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CuspOriginalFibre

open Polynomial

set_option linter.style.haveILetI false

variable (k : Type*) [Field k]

/-- The origin ideal `(u)` in the parameter line. -/
noncomputable def parameterOriginIdeal : Ideal k[X] :=
  RingHom.ker (Polynomial.evalRingHom (0 : k))

instance parameterOriginIdeal_isMaximal :
    (parameterOriginIdeal k).IsMaximal := by
  unfold parameterOriginIdeal
  exact RingHom.ker_isMaximal_of_surjective _
    (fun a => ⟨Polynomial.C a, by simp⟩)

instance parameterOriginIdeal_isPrime :
    (parameterOriginIdeal k).IsPrime :=
  (parameterOriginIdeal_isMaximal k).isPrime

/-- The parameter origin lies over the origin of the actual cusp quotient. -/
theorem parameterOriginIdeal_comap :
    Ideal.comap (Pcf.Examples.Cusp.cuspParam k).toRingHom
      (parameterOriginIdeal k) = originIdeal k := by
  symm
  apply (show (originIdeal k).IsMaximal from inferInstance).eq_of_le
  · exact (Ideal.comap_isPrime _ _).ne_top
  · rw [originIdeal]
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · change Polynomial.eval (0 : k)
        (Pcf.Examples.PaperP.CuspFiber.parametrization k
          (MvPolynomial.X (0 : Fin 2))) = 0
      simp [Pcf.Examples.PaperP.CuspFiber.parametrization]
    · change Polynomial.eval (0 : k)
        (Pcf.Examples.PaperP.CuspFiber.parametrization k
          (MvPolynomial.X (1 : Fin 2))) = 0
      simp [Pcf.Examples.PaperP.CuspFiber.parametrization]

/-- The parameter origin has the expected single generator. -/
theorem parameterOriginIdeal_eq_span_X :
    parameterOriginIdeal k = Ideal.span {(X : k[X])} := by
  unfold parameterOriginIdeal
  rw [Polynomial.ker_evalRingHom]
  simp

/-- The nonreduced cusp-origin fibre is the square of the parameter
origin ideal. -/
theorem fiberIdeal_eq_parameterOrigin_sq :
    Pcf.Examples.PaperP.CuspFiber.fiberIdeal k =
      parameterOriginIdeal k ^ 2 := by
  rw [Pcf.Examples.PaperP.CuspFiber.fiberIdeal_eq,
    parameterOriginIdeal_eq_span_X, Ideal.span_singleton_pow]

theorem parameterOrigin_sq_ne_self :
    parameterOriginIdeal k ^ 2 ≠ parameterOriginIdeal k := by
  intro h
  have hrad : (Pcf.Examples.PaperP.CuspFiber.fiberIdeal k).IsRadical := by
    rw [fiberIdeal_eq_parameterOrigin_sq, h]
    exact (show (parameterOriginIdeal k).IsMaximal from inferInstance).isPrime.isRadical
  exact Pcf.Examples.PaperP.CuspFiber.fiber_not_isReduced k
    ((Ideal.isRadical_iff_quotient_reduced _).mp hrad)

theorem parameterOrigin_not_unramified (k : Type*) [Field k] [CharZero k] :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    letI : (parameterOriginIdeal k).IsPrime :=
      (parameterOriginIdeal_isMaximal k).isPrime
    ¬ Algebra.IsUnramifiedAt (CoordinateRing k) (parameterOriginIdeal k) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : (parameterOriginIdeal k).IsPrime :=
    (parameterOriginIdeal_isMaximal k).isPrime
  letI : (parameterOriginIdeal k).LiesOver (originIdeal k) :=
    ⟨(parameterOriginIdeal_comap k).symm⟩
  haveI : Module.Finite (CoordinateRing k) k[X] := cuspParam_finite k
  haveI : Algebra.EssFiniteType (CoordinateRing k) k[X] := inferInstance
  letI : Algebra (Localization.AtPrime (originIdeal k))
      (Localization.AtPrime (parameterOriginIdeal k)) :=
    Localization.AtPrime.algebraOfLiesOver (originIdeal k) (parameterOriginIdeal k)
  haveI : IsScalarTower (CoordinateRing k) k[X]
      (Localization.AtPrime (parameterOriginIdeal k)) := inferInstance
  intro h
  have hc := (Algebra.isUnramifiedAt_iff_map_eq
    (CoordinateRing k) (originIdeal k) (parameterOriginIdeal k)).mp h
  let q := parameterOriginIdeal k
  let L := Localization.AtPrime q
  have hpq :
      (originIdeal k).map (algebraMap (CoordinateRing k) k[X]) = q ^ 2 := by
    change Ideal.map (Pcf.Examples.Cusp.cuspParam k).toRingHom
      (originIdeal k) = _
    rw [originIdeal_map, fiberIdeal_eq_parameterOrigin_sq]
  have hpowMap : (q ^ 2).map (algebraMap k[X] L) =
      IsLocalRing.maximalIdeal L := by
    rw [← hpq, Ideal.map_map]
    rw [← IsScalarTower.algebraMap_eq (CoordinateRing k) k[X] L]
    exact hc.2
  have hmaxMap : q.map (algebraMap k[X] L) =
      IsLocalRing.maximalIdeal L := IsLocalization.AtPrime.map_eq_maximalIdeal q L
  have hmaxPow : (IsLocalRing.maximalIdeal L) ^ 2 =
      IsLocalRing.maximalIdeal L := by
    simpa only [Ideal.map_pow, hmaxMap] using hpowMap
  have hqPow : q ^ 2 = q := by
    have hh := congrArg (Ideal.comap (algebraMap k[X] L)) hmaxPow
    change (IsLocalRing.maximalIdeal L ^ 2).under k[X] =
      (IsLocalRing.maximalIdeal L).under k[X] at hh
    rw [IsLocalization.AtPrime.under_maximalIdeal_pow q L 2,
      ← pow_one (IsLocalRing.maximalIdeal L),
      IsLocalization.AtPrime.under_maximalIdeal_pow q L 1] at hh
    simpa using hh
  exact parameterOrigin_sq_ne_self k hqPow

/-- The original cusp parametrization is not étale at the specified
parameter-origin point above the cusp singularity. -/
theorem parameterOrigin_not_etale (k : Type*) [Field k] [CharZero k] :
    letI : Algebra (CoordinateRing k) k[X] :=
      (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
    letI : (parameterOriginIdeal k).IsPrime :=
      parameterOriginIdeal_isPrime k
    ¬ Algebra.IsEtaleAt (CoordinateRing k) (parameterOriginIdeal k) := by
  letI : Algebra (CoordinateRing k) k[X] :=
    (Pcf.Examples.Cusp.cuspParam k).toRingHom.toAlgebra
  letI : (parameterOriginIdeal k).IsPrime := parameterOriginIdeal_isPrime k
  intro h
  letI : Algebra.FormallyEtale (CoordinateRing k)
      (Localization.AtPrime (parameterOriginIdeal k)) := h
  exact parameterOrigin_not_unramified k inferInstance

#print axioms parameterOriginIdeal_comap
#print axioms fiberIdeal_eq_parameterOrigin_sq
#print axioms parameterOrigin_sq_ne_self
#print axioms parameterOrigin_not_unramified
#print axioms parameterOrigin_not_etale

end Pcf.Examples.PaperP.CuspOriginalFibre
