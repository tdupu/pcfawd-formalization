/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Abhyankar
import Pcf.Stacks.Abhyankar.DVRAbhyankar
import Pcf.Stacks.Abhyankar.KummerClauses
import Pcf.Stacks.Abhyankar.StandardCoverNormalization
import Pcf.Bounding.SmoothRegularLocal

/-!
# The root-of-a-unit leg in the DVR Abhyankar square

In the last paragraph of Stacks Tag `0BRM`, after adjoining the ramified root on the base,
the other leg is obtained by adjoining an `e`th root of a unit.  That Kummer algebra is etale
when `e` is invertible.  A chosen finite local factor is therefore etale as well, and the
ramification-square theorem applies.

This file makes that implication explicit.  Its localization equivalence is the actual output
of choosing a prime of the Kummer algebra; it does not assume etaleness of the desired leg.
-/

open IsLocalRing

universe u v w x

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- The root-of-a-unit algebra over a DVR is the integral closure of the DVR in its
generic localization.

This supplies the common ambient generic algebra used in the last paragraph of Stacks
Tag `0BRM`.  The Kummer algebra is finite over the DVR, its uniformizer stays a
nonzerodivisor by flatness, and its closed fibre is reduced because the Kummer algebra is
etale.  Hence the principal ideal of the uniformizer is radical, so the elementary
normalization calculation for localization away from a radical nonzerodivisor applies. -/
theorem kummerUnit_isIntegralClosure_localizationAway_uniformizer
    (S : Type v) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (pi : S) (hpi : Irreducible pi)
    (unit : Sˣ) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (heUnit : IsUnit (exponent : S)) :
    IsIntegralClosure
      (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) S
      (Localization.Away
        (algebraMap S (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) pi)) := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
  let C := Localization.Away (algebraMap S U pi)
  letI : Module.Free S U :=
    (Abhyankar.kummerPoly_monic unit (by omega)).free_adjoinRoot
  letI : Module.Finite S U :=
    (Abhyankar.kummerPoly_monic unit (by omega)).finite_adjoinRoot
  letI : Algebra.Etale S U :=
    Abhyankar.etale unit (by omega) heUnit
  have hpi_regular : pi ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hpi.ne_zero
  have hsmul : IsSMulRegular U pi :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hpi_regular
  have hmap_regular : algebraMap S U pi ∈ nonZeroDivisors U := by
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      apply hsmul
      simpa only [Algebra.smul_def, mul_zero] using hx
    · intro x hx
      apply hsmul
      simpa only [Algebra.smul_def, mul_zero] using (mul_comm x (algebraMap S U pi) ▸ hx)
  let p : Ideal S := Ideal.span {pi}
  letI : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpi
  have hrad_map : (p.map (algebraMap S U)).IsRadical :=
    Algebra.FormallyUnramified.isRadical_map_isMaximal S U p
  have hrad : (Ideal.span ({algebraMap S U pi} : Set U)).IsRadical := by
    simpa [p, Ideal.map_span] using hrad_map
  let _ : IsIntegrallyClosedIn U C :=
    isIntegrallyClosedIn_away_of_span_isRadical hmap_regular hrad
  let _ : Algebra.IsIntegral S U :=
    AdjoinRoot.isIntegral_of_monic (Abhyankar.kummerPoly_monic unit (by omega))
  exact IsIntegralClosure.of_isIntegrallyClosedIn

/-- A closed local factor of the root-of-a-unit Kummer algebra over a DVR is regular
local.  This is the auxiliary vertical leg of the last square in Tag `0BRM`, proved from
the etale Kummer presentation rather than assumed. -/
theorem kummerUnit_localizationAtPrime_isRegularLocalRing
    (S : Type v) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (unit : Sˣ) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (heUnit : IsUnit (exponent : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit exponent))) [q.IsPrime]
    (hq : q.under S = maximalIdeal S) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
  let T := Localization.AtPrime q
  letI : Algebra.Etale S U :=
    Abhyankar.etale unit (by omega) heUnit
  letI : IsLocalHom (algebraMap S T) := by
    apply ((IsLocalRing.local_hom_TFAE
      (algebraMap S T)).out 5 1).mp
    change (maximalIdeal T).under S = maximalIdeal S
    rw [← Ideal.under_under (B := U),
      Localization.AtPrime.under_maximalIdeal, hq]
  exact Pcf.isRegularLocalRing_of_flat_of_formallyUnramified S T

/-- The closed local factor of a Kummer unit algebra over a DVR is a domain. -/
theorem kummerUnit_localizationAtPrime_isDomain
    (S : Type v) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (unit : Sˣ) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (heUnit : IsUnit (exponent : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit exponent))) [q.IsPrime]
    (hq : q.under S = maximalIdeal S) :
    IsDomain (Localization.AtPrime q) := by
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    kummerUnit_localizationAtPrime_isRegularLocalRing
      S unit exponent hexponent heUnit q hq
  exact Pcf.Stacks.isDomain_of_isRegularLocalRing (Localization.AtPrime q)

/-- A closed local factor of the root-of-a-unit Kummer algebra over a DVR is again a
DVR.  Regularity comes from the etale local map, while formal unramifiedness identifies
the target maximal ideal with the extension of the principal maximal ideal of the base. -/
theorem kummerUnit_localizationAtPrime_isDiscreteValuationRing
    (S : Type v) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (pi : S) (hpi : Irreducible pi)
    (unit : Sˣ) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (heUnit : IsUnit (exponent : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit exponent))) [q.IsPrime]
    (hq : q.under S = maximalIdeal S) :
    @IsDiscreteValuationRing (Localization.AtPrime q) _
      (kummerUnit_localizationAtPrime_isDomain
        S unit exponent hexponent heUnit q hq) := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
  let T := Localization.AtPrime q
  letI : Algebra.Etale S U :=
    Abhyankar.etale unit (by omega) heUnit
  letI : IsLocalHom (algebraMap S T) := by
    apply ((IsLocalRing.local_hom_TFAE
      (algebraMap S T)).out 5 1).mp
    change (maximalIdeal T).under S = maximalIdeal S
    rw [← Ideal.under_under (B := U),
      Localization.AtPrime.under_maximalIdeal, hq]
  letI : IsRegularLocalRing T :=
    kummerUnit_localizationAtPrime_isRegularLocalRing
      S unit exponent hexponent heUnit q hq
  letI : IsDomain T :=
    kummerUnit_localizationAtPrime_isDomain
      S unit exponent hexponent heUnit q hq
  have hmax : (maximalIdeal T).IsPrincipal := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := S),
      hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    infer_instance
  have hpi_regular : pi ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hpi.ne_zero
  have hsmul : IsSMulRegular T pi :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hpi_regular
  have hpiT : algebraMap S T pi ≠ 0 := by
    intro hzero
    have hone : (1 : T) = 0 := by
      apply hsmul
      change pi • (1 : T) = pi • (0 : T)
      rw [Algebra.smul_def, Algebra.smul_def, hzero]
      simp
    exact one_ne_zero hone
  have hnotField : ¬ IsField T := by
    intro hfield
    letI : IsField T := hfield
    have hmem : algebraMap S T pi ∈ maximalIdeal T := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := S)]
      exact Ideal.mem_map_of_mem (algebraMap S T) <| by
        rw [hpi.maximalIdeal_eq]
        exact Ideal.subset_span (Set.mem_singleton pi)
    have hmaxbot : maximalIdeal T = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    exact hpiT (Ideal.mem_bot.mp (hmaxbot ▸ hmem))
  exact ((IsDiscreteValuationRing.TFAE T hnotField).out 5 1).mp hmax

/-- If a normalization `N` and the root-of-a-unit algebra are realized as integral
closures in the same ambient generic algebra, their local factors are canonically
equivalent.

This is the literal normalization/localization bridge in the last paragraph of Tag
`0BRM`: uniqueness of integral closure first identifies the finite models, and
`Localization.localAlgEquiv` then identifies the factors selected by corresponding
primes. -/
noncomputable def localizationEquivKummerUnit_of_isIntegralClosure
    (S : Type v) (N : Type w) (C : Type x)
    [CommRing S] [CommRing N] [CommRing C]
    [Algebra S N] [Algebra S C] [Algebra N C] [IsScalarTower S N C]
    [IsIntegralClosure N S C]
    (unit : Sˣ) (e : ℕ)
    [Algebra (AdjoinRoot (Abhyankar.kummerPoly unit e)) C]
    [IsScalarTower S (AdjoinRoot (Abhyankar.kummerPoly unit e)) C]
    [IsIntegralClosure (AdjoinRoot (Abhyankar.kummerPoly unit e)) S C]
    (m : Ideal N) [m.IsPrime] :
    let g : N ≃ₐ[S] AdjoinRoot (Abhyankar.kummerPoly unit e) :=
      IsIntegralClosure.equiv S N C _
    Localization.AtPrime m ≃ₐ[S] Localization.AtPrime (m.map g) := by
  let g : N ≃ₐ[S] AdjoinRoot (Abhyankar.kummerPoly unit e) :=
    IsIntegralClosure.equiv S N C _
  exact Localization.localAlgEquiv m (m.map g) g
    (Ideal.comap_map_of_bijective g g.bijective).symm

/-- A map of local rings is local when the closed point of the target lies over the
closed point of the source. -/
theorem isLocalHom_of_maximalIdeal_under_eq
    (S : Type v) (T : Type w) [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T] [Algebra S T]
    (h : (maximalIdeal T).under S = maximalIdeal S) :
    IsLocalHom (algebraMap S T) := by
  apply ((IsLocalRing.local_hom_TFAE
    (algebraMap S T)).out 5 1).mp
  exact h

/-- Localizing at a prime over the closed point of a local base produces a local
algebra map from that base. -/
theorem isLocalHom_localizationAtPrime_of_under_eq_maximalIdeal
    (S : Type v) (N : Type w) [CommRing S] [CommRing N]
    [IsLocalRing S] [Algebra S N]
    (m : Ideal N) [m.IsPrime]
    (hm : m.under S = maximalIdeal S) :
    IsLocalHom (algebraMap S (Localization.AtPrime m)) := by
  apply isLocalHom_of_maximalIdeal_under_eq
  change (maximalIdeal (Localization.AtPrime m)).under S = maximalIdeal S
  rw [← Ideal.under_under (B := N),
    Localization.AtPrime.under_maximalIdeal, hm]

/-- A maximal ideal of an integral-closure model over a local base lies over the closed
point.  This is the lying-over equality used for the selected normalization factor in
Tag `0BRM`; it follows from integrality rather than being extra incidence data. -/
theorem maximalIdeal_under_eq_of_isIntegralClosure
    (S : Type v) (N : Type w) (C : Type x)
    [CommRing S] [CommRing N] [CommRing C]
    [IsLocalRing S]
    [Algebra S N] [Algebra S C] [Algebra N C] [IsScalarTower S N C]
    [IsIntegralClosure N S C]
    (m : Ideal N) [m.IsMaximal] :
    m.under S = maximalIdeal S := by
  letI : Algebra.IsIntegral S N :=
    IsIntegralClosure.isIntegral_algebra S C
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal m)

/-- Residue-field separability composes with a formally unramified top leg.

This is the residue-field argument in the final sentence of Tag `0BRM`: every residue
extension on the formally unramified leg is separable, and separability is transitive with
the residue extension on the original DVR leg. -/
theorem hasSeparableResidueFieldsAt_comp_formallyUnramified
    (R : Type u) (S : Type v) (T : Type x)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime]
    [Algebra.HasSeparableResidueFieldsAt R S p]
    [Algebra.EssFiniteType S T] [Algebra.FormallyUnramified S T] :
    Algebra.HasSeparableResidueFieldsAt R T p := by
  constructor
  intro q _ _
  let qS : Ideal S := q.under S
  letI : qS.IsPrime := inferInstance
  letI : q.LiesOver qS := ⟨rfl⟩
  letI : qS.LiesOver p := ⟨by
    rw [Ideal.under_under]
    exact q.over_def p⟩
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime qS) :=
    Localization.AtPrime.algebraOfLiesOver p qS
  letI : Algebra (Localization.AtPrime qS) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver qS q
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime qS) :=
    inferInstance
  letI : IsScalarTower S (Localization.AtPrime qS) (Localization.AtPrime q) :=
    inferInstance
  letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    inferInstance
  letI : Algebra.IsUnramifiedAt S q :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance ⟨q, inferInstance⟩
  letI : Algebra.IsSeparable p.ResidueField qS.ResidueField := inferInstance
  letI : Algebra.IsSeparable qS.ResidueField q.ResidueField := inferInstance
  exact Algebra.IsSeparable.trans p.ResidueField qS.ResidueField q.ResidueField

/-- The literal normalization-factor form of the last paragraph of Tag `0BRM`.

The normalization `N` and the Kummer algebra `S[x]/(x^e-u)` are integral closures in the
same ambient generic algebra `C`.  Their uniqueness equivalence produces the corresponding
prime `q` and the local-factor equivalence required by the root-of-a-unit square.  The
remaining structural facts are then derived as follows:

* flatness of the desired leg follows from the two DVRs and faithful scalar action;
* essential finite type descends from the finite lower legs and the Kummer localization;
* both maps into the selected local factor are local because its closed point lies over the
  displayed closed points;
* residue separability is the composite of the original DVR residue extension and the
  formally unramified Kummer localization, then is passed to the totally ramified standard
  root leg.

Thus the hypotheses describe the actual normalization square and its prime incidences;
none assumes unramifiedness or etaleness of the desired standard-root leg. -/
theorem isUnramifiedAt_of_standardRoot_integralClosure_kummerUnit_localFactor
    (R : Type u) (S : Type v) (N : Type w) (C : Type x)
    [CommRing R] [CommRing S] [CommRing N] [CommRing C]
    [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S]
    [IsLocalHom (algebraMap R S)]
    [Algebra.HasSeparableResidueFieldsAt R S (maximalIdeal R)]
    (pi : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (unit : Sˣ) (heUnit : IsUnit (exponent : S))
    [Algebra S N] [Algebra R N] [IsScalarTower R S N]
    [Algebra S C] [Algebra N C] [IsScalarTower S N C]
    [IsIntegralClosure N S C]
    [Algebra (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) C]
    [IsScalarTower S (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) C]
    [IsIntegralClosure
      (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) S C]
    (m : Ideal N) [m.IsPrime]
    (hmS : m.under S = maximalIdeal S)
    [Algebra (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization.AtPrime m)]
    [IsScalarTower R (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization.AtPrime m)]
    [IsDomain (Localization.AtPrime m)]
    [IsDiscreteValuationRing (Localization.AtPrime m)]
    [FaithfulSMul (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization.AtPrime m)]
    (hmA : (maximalIdeal (Localization.AtPrime m)).under
      (AdjoinRoot (dvrRootPoly pi exponent)) =
      Ideal.span {AdjoinRoot.root (dvrRootPoly pi exponent)})
    (hramification : (maximalIdeal S).ramificationIdx R = exponent) :
    Algebra.IsUnramifiedAt
      (AdjoinRoot (dvrRootPoly pi exponent))
      (maximalIdeal (Localization.AtPrime m)) := by
  let A := AdjoinRoot (dvrRootPoly pi exponent)
  let T := Localization.AtPrime m
  let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
  let g : N ≃ₐ[S] U := IsIntegralClosure.equiv S N C U
  let q : Ideal U := m.map g
  let equiv : T ≃ₐ[S] Localization.AtPrime q :=
    localizationEquivKummerUnit_of_isIntegralClosure
      S N C unit exponent m
  letI : IsDomain A := dvrRootAlgebra_isDomain pi hexponent hpi
  letI : IsLocalRing A := dvrRootAlgebra_isLocalRing pi hexponent hpi
  letI : IsDiscreteValuationRing A :=
    dvrRootAlgebra_isDiscreteValuationRing pi hexponent hpi
  letI : Module.Finite R A :=
    (dvrRootPoly_monic pi hexponent).finite_adjoinRoot
  letI : IsLocalHom (algebraMap R A) :=
    AdjoinRoot.isLocalHom_of_monic_of_degree_pos
      (dvrRootPoly_monic pi hexponent) <| by
        rw [← Polynomial.natDegree_pos_iff_degree_pos, dvrRootPoly,
          Polynomial.natDegree_X_pow_sub_C]
        exact hexponent
  have hmaximalA : maximalIdeal A =
      Ideal.span {AdjoinRoot.root (dvrRootPoly pi exponent)} :=
    (IsLocalRing.eq_maximalIdeal
      (dvrRootIdeal_isMaximal pi hexponent hpi)).symm
  have hunderA : (maximalIdeal T).under A = maximalIdeal A :=
    hmA.trans hmaximalA.symm
  letI : IsLocalHom (algebraMap S T) :=
    isLocalHom_localizationAtPrime_of_under_eq_maximalIdeal S N m hmS
  letI : IsLocalHom (algebraMap A T) :=
    isLocalHom_of_maximalIdeal_under_eq A T hunderA
  letI : Module.Flat A T := inferInstance
  letI : Algebra.Etale S U :=
    Abhyankar.etale unit (by omega) heUnit
  letI : Module.Flat S (Localization.AtPrime q) := inferInstance
  letI : Module.Flat S T := Module.Flat.of_linearEquiv equiv.toLinearEquiv
  letI : Algebra.EssFiniteType S (Localization.AtPrime q) := inferInstance
  letI : Algebra.EssFiniteType S T :=
    (Algebra.EssFiniteType.iff_of_algEquiv equiv).mpr inferInstance
  letI : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R S T
  letI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp R A T
  letI : Algebra.FormallyEtale S (Localization.AtPrime q) := inferInstance
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_equiv equiv.symm
  letI : Algebra.IsUnramifiedAt S (maximalIdeal T) :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance
      ⟨maximalIdeal T, inferInstance⟩
  letI : Algebra.HasSeparableResidueFieldsAt R T (maximalIdeal R) :=
    hasSeparableResidueFieldsAt_comp_formallyUnramified
      R S T (maximalIdeal R)
  letI : (maximalIdeal A).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R A)).symm⟩
  letI hsepA : Algebra.HasSeparableResidueFieldsAt A T (maximalIdeal A) :=
    Algebra.HasSeparableResidueFieldsAt.tower_top
      (maximalIdeal R) (maximalIdeal A)
  letI : (maximalIdeal T).LiesOver (maximalIdeal A) :=
    ⟨hunderA.symm⟩
  have hindex : (maximalIdeal S).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R := by
    rw [hramification, hmaximalA]
    exact (dvrRootIdeal_ramificationIdx pi hexponent hpi).symm
  have hunderS : (maximalIdeal T).under S = maximalIdeal S :=
    IsLocalRing.maximalIdeal_comap (algebraMap S T)
  have htopOverS : (maximalIdeal T).ramificationIdx S = 1 :=
    Ideal.ramificationIdx_eq_one (maximalIdeal T) S
  have htower := Ideal.ramificationIdx_tower
    (R := R) (S := S) (T := T)
      ((maximalIdeal T).under S) (maximalIdeal T)
  have htotal : (maximalIdeal T).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R := by
    rw [htower, hunderS, htopOverS, mul_one, hindex]
  exact isUnramifiedAt_of_ramificationIdx_total_eq_intermediate_at
    R A T (maximalIdeal A) (maximalIdeal T) htotal

/-- The literal `0BRM` local factor with the common generic algebra constructed rather
than postulated.

The ambient algebra is the Kummer root algebra localized away from a uniformizer of the
upper DVR.  The preceding normalization theorem proves that the Kummer root algebra is its
integral closure.  A maximal ideal of the competing normalization automatically lies over
the closed point by integrality.  Consequently the only remaining hypotheses concern the
other map in the ramification square: the closed Kummer factor is proved internally to be
a DVR and that structure is transported to the selected normalization factor. -/
theorem isUnramifiedAt_of_standardRoot_kummerGenericNormalization_localFactor
    (R : Type u) (S : Type v) (N : Type w)
    [CommRing R] [CommRing S] [CommRing N]
    [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S]
    [IsLocalHom (algebraMap R S)]
    [Algebra.HasSeparableResidueFieldsAt R S (maximalIdeal R)]
    (pi : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (piS : S) (hpiS : Irreducible piS)
    (unit : Sˣ) (heUnit : IsUnit (exponent : S))
    [Algebra S N] [Algebra R N] [IsScalarTower R S N]
    [Algebra N (Localization.Away
      (algebraMap S (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) piS))]
    [IsScalarTower S N (Localization.Away
      (algebraMap S (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) piS))]
    [IsIntegralClosure N S (Localization.Away
      (algebraMap S (AdjoinRoot (Abhyankar.kummerPoly unit exponent)) piS))]
    (m : Ideal N) [m.IsMaximal]
    [Algebra (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization.AtPrime m)]
    [IsScalarTower R (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization.AtPrime m)]
    [FaithfulSMul (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization.AtPrime m)]
    (hmA : (maximalIdeal (Localization.AtPrime m)).under
      (AdjoinRoot (dvrRootPoly pi exponent)) =
      Ideal.span {AdjoinRoot.root (dvrRootPoly pi exponent)})
    (hramification : (maximalIdeal S).ramificationIdx R = exponent) :
    Algebra.IsUnramifiedAt
      (AdjoinRoot (dvrRootPoly pi exponent))
      (maximalIdeal (Localization.AtPrime m)) := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
  let C := Localization.Away (algebraMap S U piS)
  letI : IsIntegralClosure U S C :=
    kummerUnit_isIntegralClosure_localizationAway_uniformizer
      S piS hpiS unit exponent hexponent heUnit
  have hmS : m.under S = maximalIdeal S :=
    maximalIdeal_under_eq_of_isIntegralClosure S N C m
  let g : N ≃ₐ[S] U := IsIntegralClosure.equiv S N C U
  let q : Ideal U := m.map g
  letI : q.IsMaximal := by
    dsimp only [q]
    infer_instance
  have hqS : q.under S = maximalIdeal S := by
    have hmaps : algebraMap S U = g.toRingHom.comp (algebraMap S N) := by
      ext s
      simp
    have hcomap : (m.map g).comap g.toRingHom = m := by
      exact Ideal.comap_map_of_bijective g.toRingHom g.bijective
    change (m.map g).comap (algebraMap S U) = maximalIdeal S
    rw [hmaps, ← Ideal.comap_comap, hcomap]
    exact hmS
  let T := Localization.AtPrime m
  let V := Localization.AtPrime q
  let equiv : T ≃ₐ[S] V :=
    localizationEquivKummerUnit_of_isIntegralClosure
      S N C unit exponent m
  letI : IsDomain V :=
    kummerUnit_localizationAtPrime_isDomain
      S unit exponent hexponent heUnit q hqS
  letI : IsDiscreteValuationRing V :=
    kummerUnit_localizationAtPrime_isDiscreteValuationRing
      S piS hpiS unit exponent hexponent heUnit q hqS
  letI : IsDomain T := equiv.toMulEquiv.isDomain _
  letI : IsDiscreteValuationRing T :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing equiv.symm
  exact isUnramifiedAt_of_standardRoot_integralClosure_kummerUnit_localFactor
    R S N C pi exponent hexponent hpi unit heUnit m hmS hmA hramification

/-- A finite algebra identified with a local factor of a root-of-a-unit Kummer algebra is
etale over the base DVR.

The finite-module hypothesis turns the formally etale localized Kummer algebra into a finitely
presented algebra after transport across the displayed equivalence. -/
theorem etale_of_equiv_localization_kummerUnit
    (S : Type v) (T : Type x) [CommRing S] [CommRing T] [Algebra S T]
    [IsNoetherianRing S] [Module.Finite S T]
    (unit : Sˣ) (e : ℕ) (he : e ≠ 0) (heUnit : IsUnit (e : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit e))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q) :
    Algebra.Etale S T := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit e)
  letI : Algebra.Etale S U := Abhyankar.etale unit he heUnit
  letI : Algebra.FormallyEtale S (Localization.AtPrime q) := inferInstance
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_equiv equiv.symm
  letI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- The local root-of-a-unit leg in the `0BRM` ramification square.

The displayed equivalence supplies all three properties of the auxiliary leg needed by
`isUnramifiedAt_of_local_ramification_square`: its localization is flat and essentially of
finite type over `S`, and is formally unramified because the Kummer algebra is etale.  Thus
only the structural flatness and essential finite type of the desired leg `A → T` remain
as hypotheses.  In particular, no finiteness hypothesis is imposed on the local ring `T`. -/
theorem isUnramifiedAt_of_kummerUnit_local_ramification_square
    (R : Type u) (S : Type v) (A : Type w) (T : Type x)
    [CommRing R] [CommRing S] [CommRing A] [CommRing T]
    [IsLocalRing S] [IsLocalRing A] [IsLocalRing T]
    [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S T] [Algebra A T]
    [IsScalarTower R S T] [IsScalarTower R A T]
    [Module.Finite R S] [Module.Finite R A]
    [Module.Flat A T] [Algebra.EssFiniteType A T]
    [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap A T)]
    [Algebra.HasSeparableResidueFieldsAt A T ((maximalIdeal T).under A)]
    (unit : Sˣ) (e : ℕ) (he : e ≠ 0) (heUnit : IsUnit (e : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit e))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q)
    (hindex : (maximalIdeal S).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R) :
    Algebra.IsUnramifiedAt A (maximalIdeal T) := by
  let U := AdjoinRoot (Abhyankar.kummerPoly unit e)
  letI : Algebra.Etale S U := Abhyankar.etale unit he heUnit
  letI : Module.Flat S (Localization.AtPrime q) := inferInstance
  letI : Module.Flat S T := Module.Flat.of_linearEquiv equiv.toLinearEquiv
  letI : Algebra.EssFiniteType S (Localization.AtPrime q) := inferInstance
  letI : Algebra.EssFiniteType S T :=
    (Algebra.EssFiniteType.iff_of_algEquiv equiv).mpr inferInstance
  letI : Algebra.FormallyEtale S (Localization.AtPrime q) := inferInstance
  letI : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_equiv equiv.symm
  letI : Algebra.IsUnramifiedAt S (maximalIdeal T) :=
    Algebra.formallyUnramified_iff_forall.mp inferInstance
      ⟨maximalIdeal T, inferInstance⟩
  exact isUnramifiedAt_of_local_ramification_square R S A T hindex

/-- The local standard-root specialization of the `0BRM` square.

The lower ramified leg is the literal standard root DVR `R[π^(1/e)]`.  Its index is
computed by the `09EV` clauses, while the root-of-a-unit localization equivalence supplies
the flat unramified auxiliary leg.  The conclusion is precisely unramifiedness at the
closed point of the desired local leg; unlike the finite-etale specialization below, this
matches the local rings used in Tag `0BRM`. -/
theorem isUnramifiedAt_of_standardRoot_kummerUnit_local_square
    (R : Type u) (S : Type v) (T : Type x)
    [CommRing R] [CommRing S] [CommRing T]
    [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [IsLocalRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [IsLocalHom (algebraMap S T)]
    (pi : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    [Algebra (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [IsScalarTower R (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [Module.Flat (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [Algebra.EssFiniteType (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [IsLocalHom
      (algebraMap (AdjoinRoot (dvrRootPoly pi exponent)) T)]
    [Algebra.HasSeparableResidueFieldsAt
      (AdjoinRoot (dvrRootPoly pi exponent)) T
      ((maximalIdeal T).under (AdjoinRoot (dvrRootPoly pi exponent)))]
    (unit : Sˣ) (heUnit : IsUnit (exponent : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit exponent))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q)
    (hramification : (maximalIdeal S).ramificationIdx R = exponent) :
    Algebra.IsUnramifiedAt
      (AdjoinRoot (dvrRootPoly pi exponent)) (maximalIdeal T) := by
  let A := AdjoinRoot (dvrRootPoly pi exponent)
  letI : IsDomain A := dvrRootAlgebra_isDomain pi hexponent hpi
  letI : IsLocalRing A := dvrRootAlgebra_isLocalRing pi hexponent hpi
  letI : Module.Finite R A :=
    (dvrRootPoly_monic pi hexponent).finite_adjoinRoot
  have hmaximal : maximalIdeal A =
      Ideal.span {AdjoinRoot.root (dvrRootPoly pi exponent)} :=
    (IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal pi hexponent hpi)).symm
  have hindex : (maximalIdeal S).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R := by
    rw [hramification, hmaximal]
    exact (dvrRootIdeal_ramificationIdx pi hexponent hpi).symm
  exact isUnramifiedAt_of_kummerUnit_local_ramification_square
    R S A T unit exponent (by omega) heUnit q equiv hindex

/-- The root-of-a-unit specialization of the final ramification square in Tag `0BRM`.

The lower extensions `S/R` and `A/R` have the same ramification index.  The chosen top ring
`T` is a finite local factor of the Kummer algebra obtained from `S` by adjoining an `e`th
root of a unit.  The preceding theorem proves that auxiliary leg etale, after which
`etale_of_dvr_ramification_square` proves that `A → T` is finite etale. -/
theorem etale_of_dvr_kummerUnit_ramification_square
    (R : Type u) (S : Type v) (A : Type w) (T : Type x)
    [CommRing R] [CommRing S] [CommRing A] [CommRing T]
    [IsDomain R] [IsDomain S] [IsDomain A] [IsDomain T]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S T] [Algebra A T]
    [IsScalarTower R S T] [IsScalarTower R A T]
    [Module.Finite R S] [Module.Finite R A] [Module.Finite S T] [Module.Finite A T]
    [FaithfulSMul A T]
    [IsLocalHom (algebraMap S T)] [IsLocalHom (algebraMap A T)]
    [Algebra.HasSeparableResidueFieldsAt A T ((maximalIdeal T).under A)]
    (unit : Sˣ) (e : ℕ) (he : e ≠ 0) (heUnit : IsUnit (e : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit e))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q)
    (hindex : (maximalIdeal S).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R) :
    Algebra.Etale A T := by
  letI : Algebra.Etale S T :=
    etale_of_equiv_localization_kummerUnit S T unit e he heUnit q equiv
  exact etale_of_dvr_ramification_square R S A T hindex

/-- The standard-root specialization of the `0BRM` square used in Tag `0EYG`.

The lower ramified leg is now the literal DVR `R[π^(1/e)]`.  The `09EV` calculation proves
that its ramification index is `e`, so the only numerical input is that the original DVR
extension `S/R` also has index `e`.  The other top leg is the chosen local factor of the
root-of-a-unit Kummer algebra over `S`. -/
theorem etale_of_dvr_standardRoot_kummerUnit_square
    (R : Type u) (S : Type v) (T : Type x)
    [CommRing R] [CommRing S] [CommRing T]
    [IsDomain R] [IsDomain S] [IsDomain T]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Finite S T]
    [IsLocalHom (algebraMap S T)]
    (pi : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    [Algebra (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [IsScalarTower R (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [Module.Finite (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [FaithfulSMul (AdjoinRoot (dvrRootPoly pi exponent)) T]
    [IsLocalHom
      (algebraMap (AdjoinRoot (dvrRootPoly pi exponent)) T)]
    [Algebra.HasSeparableResidueFieldsAt
      (AdjoinRoot (dvrRootPoly pi exponent)) T
      ((maximalIdeal T).under (AdjoinRoot (dvrRootPoly pi exponent)))]
    (unit : Sˣ) (heUnit : IsUnit (exponent : S))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit exponent))) [q.IsPrime]
    (equiv : T ≃ₐ[S] Localization.AtPrime q)
    (hramification : (maximalIdeal S).ramificationIdx R = exponent) :
    Algebra.Etale (AdjoinRoot (dvrRootPoly pi exponent)) T := by
  let A := AdjoinRoot (dvrRootPoly pi exponent)
  letI : IsDomain A := dvrRootAlgebra_isDomain pi hexponent hpi
  letI : IsLocalRing A := dvrRootAlgebra_isLocalRing pi hexponent hpi
  letI : IsDiscreteValuationRing A :=
    dvrRootAlgebra_isDiscreteValuationRing pi hexponent hpi
  letI : Module.Finite R A :=
    (dvrRootPoly_monic pi hexponent).finite_adjoinRoot
  have hmaximal : maximalIdeal A =
      Ideal.span {AdjoinRoot.root (dvrRootPoly pi exponent)} :=
    (IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal pi hexponent hpi)).symm
  have hindex : (maximalIdeal S).ramificationIdx R =
      (maximalIdeal A).ramificationIdx R := by
    rw [hramification, hmaximal]
    exact (dvrRootIdeal_ramificationIdx pi hexponent hpi).symm
  exact etale_of_dvr_kummerUnit_ramification_square
    R S A T unit exponent (by omega) heUnit q equiv hindex

#print axioms localizationEquivKummerUnit_of_isIntegralClosure
#print axioms kummerUnit_isIntegralClosure_localizationAway_uniformizer
#print axioms kummerUnit_localizationAtPrime_isRegularLocalRing
#print axioms kummerUnit_localizationAtPrime_isDomain
#print axioms kummerUnit_localizationAtPrime_isDiscreteValuationRing
#print axioms isLocalHom_of_maximalIdeal_under_eq
#print axioms isLocalHom_localizationAtPrime_of_under_eq_maximalIdeal
#print axioms maximalIdeal_under_eq_of_isIntegralClosure
#print axioms hasSeparableResidueFieldsAt_comp_formallyUnramified
#print axioms isUnramifiedAt_of_standardRoot_integralClosure_kummerUnit_localFactor
#print axioms isUnramifiedAt_of_standardRoot_kummerGenericNormalization_localFactor
#print axioms etale_of_equiv_localization_kummerUnit
#print axioms isUnramifiedAt_of_kummerUnit_local_ramification_square
#print axioms isUnramifiedAt_of_standardRoot_kummerUnit_local_square
#print axioms etale_of_dvr_kummerUnit_ramification_square
#print axioms etale_of_dvr_standardRoot_kummerUnit_square

end Pcf.Stacks
