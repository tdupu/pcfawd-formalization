/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.KummerIntermediateEquiv
public import Pcf.Stacks.Abhyankar.StrictHenselization
public import Pcf.Stacks.Abhyankar.Tag0EYE

/-!
# The strict-local field embedding after 0EYE

This file formalizes the middle-to-last transition in Stacks Tag `0EYG` for one connected
generic component.  The input is the actual local normalization component over the strict
root cover.  Tag `0EYE`, conditional only on the named Zariski--Nagata purity theorem, makes
that component finite etale.  Strict henselian local triviality then identifies it with the
root cover.  Passing to fraction fields constructs the embedding used by Tag `09EV`.

The codimension-one unramifiedness hypothesis is deliberately literal.  In the Stacks proof
it is produced by Tag `0BRM`; the remaining global assembly must still transport the existing
DVR-local `0BRM` theorem to every height-one localization of the normalization.  Nothing in
this file assumes the resulting radical-field equivalence or a standard-cover presentation.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

noncomputable section

/-- A finite-etale local normalization over a strictly henselian base has the same fraction
field as the base.

The equivalence is constructed in two steps: strict henselian local triviality identifies the
normalization with the base, and functoriality of fraction fields transports that identification
to the two chosen fraction-ring realizations. -/
noncomputable def fractionRingAlgEquivOfFiniteEtaleLocal
    (A N D K : Type u)
    [CommRing A] [CommRing N] [CommRing D] [CommRing K]
    [Algebra A N] [StrictlyHenselianLocalRing A]
    [IsLocalRing N] [IsLocalHom (algebraMap A N)]
    [Module.Finite A N] [Algebra.Etale A N]
    [Algebra N D] [IsFractionRing N D]
    [Algebra A D] [IsScalarTower A N D]
    [Algebra A K] [IsFractionRing A K] :
    D ≃ₐ[A] K := by
  let eNA : N ≃ₐ[A] A :=
    StrictlyHenselianLocalRing.finiteEtaleLocalAlgEquiv A N
  let eDN : D ≃ₐ[A] FractionRing N :=
    (FractionRing.algEquiv N D).symm.restrictScalars A
  let eNK : FractionRing N ≃ₐ[A] K :=
    IsFractionRing.algEquivOfAlgEquiv eNA
  exact eDN.trans eNK

/-- The fraction-field identification of a finite-etale local normalization is linear over a
smaller fraction field.

Here `R → A` is the root-cover map, `K₀` is the original fraction field, and `K` is the
fraction field of the root cover.  The only point not contained in the preceding equivalence is
linearity over `K₀`; it follows from uniqueness of maps out of a fraction ring. -/
noncomputable def fractionRingAlgEquivOfFiniteEtaleLocalOverFraction
    (R A N D K₀ K : Type u)
    [CommRing R] [CommRing A] [CommRing N]
    [CommRing D] [Field K₀] [Field K]
    [Algebra R A] [Algebra A N] [Algebra R N] [IsScalarTower R A N]
    [StrictlyHenselianLocalRing A]
    [IsLocalRing N] [IsLocalHom (algebraMap A N)]
    [Module.Finite A N] [Algebra.Etale A N]
    [Algebra N D] [IsFractionRing N D]
    [Algebra A D] [IsScalarTower A N D]
    [Algebra R D] [IsScalarTower R A D]
    [Algebra R K₀] [IsFractionRing R K₀]
    [Algebra K₀ D] [IsScalarTower R K₀ D]
    [Algebra A K] [IsFractionRing A K]
    [Algebra R K] [IsScalarTower R A K]
    [Algebra K₀ K] [IsScalarTower R K₀ K] :
    D ≃ₐ[K₀] K := by
  let e : D ≃ₐ[A] K := fractionRingAlgEquivOfFiniteEtaleLocal A N D K
  have hcommutes : e.toRingHom.comp (algebraMap K₀ D) = algebraMap K₀ K := by
    apply IsFractionRing.ringHom_ext (A := R) (K := K₀) (L := K)
    intro r
    rw [RingHom.comp_apply]
    calc
      e (algebraMap K₀ D (algebraMap R K₀ r)) =
          e (algebraMap R D r) := by
            rw [IsScalarTower.algebraMap_apply R K₀ D]
      _ = e (algebraMap A D (algebraMap R A r)) := by
            rw [IsScalarTower.algebraMap_apply R A D]
      _ = algebraMap A K (algebraMap R A r) := e.commutes _
      _ = algebraMap R K r := by
            rw [IsScalarTower.algebraMap_apply R A K]
      _ = algebraMap K₀ K (algebraMap R K₀ r) := by
            rw [IsScalarTower.algebraMap_apply R K₀ K]
  let f : D →ₐ[K₀] K :=
    { e.toRingHom with
      commutes' := fun x ↦ DFunLike.congr_fun hcommutes x }
  exact AlgEquiv.ofBijective f e.bijective

/-- A field equivalence between the fraction fields of two finite normal domain models
extends uniquely to an equivalence of the models.

This is the normalization step used after `09EV` in Tag `0EYG`.  The field equivalence is
not the desired integral presentation: both models are independently characterized as the
integral closure of the base in their fraction fields, and uniqueness of integral closure
constructs the integral equivalence. -/
noncomputable def normalIntegralAlgEquivOfFractionRingEquiv
    (R B C KB KC : Type u)
    [CommRing R]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [CommRing KB] [CommRing KC]
    [Algebra R B] [Algebra.IsIntegral R B]
    [Algebra R C] [Algebra.IsIntegral R C]
    [Algebra B KB] [IsFractionRing B KB]
    [Algebra R KB] [IsScalarTower R B KB]
    [Algebra C KC] [IsFractionRing C KC]
    [Algebra R KC] [IsScalarTower R C KC]
    (e : KB ≃ₐ[R] KC) :
    B ≃ₐ[R] C := by
  letI : IsIntegralClosure B R KB :=
    IsIntegralClosure.of_isIntegrallyClosed B R KB
  letI : Algebra B KC :=
    (e.toRingHom.comp (algebraMap B KB)).toAlgebra
  letI : IsScalarTower R B KC := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R KC r = e (algebraMap B KB (algebraMap R B r))
    rw [← IsScalarTower.algebraMap_apply R B KB]
    exact (e.commutes r).symm
  let hB : IsIntegralClosure B R KC :=
    IsIntegralClosure.of_algEquiv B e (fun _ ↦ rfl)
  letI : IsIntegralClosure B R KC := hB
  letI : IsIntegralClosure C R KC :=
    IsIntegralClosure.of_isIntegrallyClosed C R KC
  exact IsIntegralClosure.equiv R B KC C

/-- **Tags `0EYE` and strict splitting, connected local-normalization chain.**

Let `A` be the strict local root cover of a base `R`, let `N` be one local normal component
of the normalization after generic base change, and let `D` be its fraction field.  Etaleness
away from the root divisor, codimension-one unramifiedness, and Zariski--Nagata purity make
`N/A` finite etale.  Strict henselian local triviality then identifies `N` with `A`; taking
fraction fields and composing with the original generic-component map constructs the field
embedding used in the last paragraph of Tag `0EYG`.

This statement keeps the high-dimensional root cover `A` separate from the height-one DVR
used by Tag `09EV`.  Relating their fraction-field root presentations is an upstream
localization/base-change step, not silently built into this theorem. -/
theorem exists_fractionFieldEmbedding_of_tag0EYE_strict_local_normalization
    (R A N D K₀ K M : Type u)
    [CommRing R]
    [CommRing A] [IsNoetherianRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing N] [IsDomain N] [IsIntegrallyClosed N]
    [Field D] [Field K₀] [Field K] [Field M]
    [Algebra R A]
    [Algebra A N] [Algebra R N] [IsScalarTower R A N]
    [StrictlyHenselianLocalRing A]
    [IsLocalRing N] [IsLocalHom (algebraMap A N)]
    [Module.Finite A N] [FaithfulSMul A N]
    [Algebra N D] [IsFractionRing N D]
    [Algebra A D] [IsScalarTower A N D]
    [Algebra R D] [IsScalarTower R A D]
    [Algebra R K₀] [IsFractionRing R K₀]
    [Algebra K₀ D] [IsScalarTower R K₀ D]
    [Algebra A K] [IsFractionRing A K]
    [Algebra R K] [IsScalarTower R A K]
    [Algebra K₀ K] [IsScalarTower R K₀ K]
    [Algebra K₀ M]
    [Algebra M D] [IsScalarTower K₀ M D]
    (z : A) (hz : z ∈ nonZeroDivisors A)
    [IsRegularRing (A ⧸ Ideal.span ({z} : Set A))]
    (hetaleAway : ∀ w : PrimeSpectrum N, algebraMap A N z ∉ w.asIdeal →
      Algebra.IsEtaleAt A w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum N, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt A w.asIdeal)
    (hpurity : ZariskiNagataPurity A N) :
    Nonempty (M →ₐ[K₀] K) := by
  letI : Algebra.Etale A N :=
    Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain
      z hz hetaleAway hunramified hpurity
  exact ⟨(fractionRingAlgEquivOfFiniteEtaleLocalOverFraction
    R A N D K₀ K).toAlgHom.comp (IsScalarTower.toAlgHom K₀ M D)⟩

/-- DVR-root specialization of the `0EYE`/strict splitting/`09EV` chain.

Let `A` be a DVR with uniformizer `π`, and let `A' = A[z]/(z^n-π)`.  Suppose `N` is the
chosen local normal component of the normalization after the root base change and `D` is its
fraction field.  Etaleness away from `z`, together with codimension-one unramifiedness and
Zariski--Nagata purity, makes `N/A'` finite etale.  If the root DVR is strictly henselian, its
local finite-etale component is trivial.  Therefore every original generic field `M` mapping
to `D` embeds in the full radical field, and the proved `09EV` classification constructs a
smaller radical field of exponent dividing `n`.

The theorem does not assume a field embedding, a radical-field equivalence, or any standard
presentation.  Those are its conclusions.  In the full high-dimensional proof of Tag `0EYG`,
the preceding theorem is applied to the strict root cover, and a separate localization
comparison identifies its fraction field with this DVR radical field. -/
theorem exists_dvrRootFractionPowerEquiv_of_strict_local_normalization
    (A N D M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    [CommRing N] [IsDomain N] [IsIntegrallyClosed N]
    [Field D] [Field M]
    (pi : A) {n : ℕ} (hn : 2 ≤ n) (hpi : Irreducible pi)
    (hunit : IsUnit ((n : ℕ) : IsLocalRing.ResidueField A))
    [StrictlyHenselianLocalRing (AdjoinRoot (dvrRootPoly pi n))]
    [Algebra (AdjoinRoot (dvrRootPoly pi n)) N]
    [Algebra A N] [IsScalarTower A (AdjoinRoot (dvrRootPoly pi n)) N]
    [IsLocalRing N]
    [IsLocalHom (algebraMap (AdjoinRoot (dvrRootPoly pi n)) N)]
    [Module.Finite (AdjoinRoot (dvrRootPoly pi n)) N]
    [FaithfulSMul (AdjoinRoot (dvrRootPoly pi n)) N]
    [Algebra N D] [IsFractionRing N D]
    [Algebra (AdjoinRoot (dvrRootPoly pi n)) D]
    [IsScalarTower (AdjoinRoot (dvrRootPoly pi n)) N D]
    [Algebra A D]
    [IsScalarTower A (AdjoinRoot (dvrRootPoly pi n)) D]
    [Algebra (FractionRing A) D] [IsScalarTower A (FractionRing A) D]
    [Algebra (FractionRing A) M]
    [Algebra M D] [IsScalarTower (FractionRing A) M D]
    (hetaleAway : ∀ w : PrimeSpectrum N,
      algebraMap (AdjoinRoot (dvrRootPoly pi n)) N
          (AdjoinRoot.root (dvrRootPoly pi n)) ∉ w.asIdeal →
        Algebra.IsEtaleAt (AdjoinRoot (dvrRootPoly pi n)) w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum N, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt (AdjoinRoot (dvrRootPoly pi n)) w.asIdeal)
    (hpurity : ZariskiNagataPurity (AdjoinRoot (dvrRootPoly pi n)) N) :
    ∃ d : ℕ, d ∣ n ∧ 1 ≤ d ∧
      Nonempty (M ≃ₐ[FractionRing A]
        AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) pi) d)) := by
  let hn1 : 1 ≤ n := by omega
  let B := AdjoinRoot (dvrRootPoly pi n)
  letI : IsDomain B := dvrRootAlgebra_isDomain pi hn1 hpi
  letI : IsDiscreteValuationRing B :=
    dvrRootAlgebra_isDiscreteValuationRing pi hn1 hpi
  letI : Algebra.Etale B N :=
    Algebra.etale_across_nonZeroDivisor_of_zariskiNagataPurity_finite_normal_domain
      (AdjoinRoot.root (dvrRootPoly pi n))
      (dvrRoot_mem_nonZeroDivisors pi hn1
        (mem_nonZeroDivisors_iff_ne_zero.mpr hpi.ne_zero))
      hetaleAway hunramified hpurity
  letI : FaithfulSMul A B :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos
      (dvrRootPoly_monic pi hn1) <| by
        rw [← Polynomial.natDegree_pos_iff_degree_pos, dvrRootPoly,
          Polynomial.natDegree_X_pow_sub_C]
        exact hn1
  letI : FaithfulSMul A (FractionRing B) :=
    FaithfulSMul.trans A B _
  letI : Algebra (FractionRing A) (FractionRing B) :=
    dvrRootFractionRingAlgebra pi hn1 hpi
  letI : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A _
  let eD : D ≃ₐ[FractionRing A] FractionRing B :=
    fractionRingAlgEquivOfFiniteEtaleLocalOverFraction
      A B N D (FractionRing A) (FractionRing B)
  let f : M →ₐ[FractionRing A] FractionRing B :=
    eD.toAlgHom.comp (IsScalarTower.toAlgHom (FractionRing A) M D)
  let froot : M →ₐ[FractionRing A]
      AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) pi) n) :=
    (dvrRootFractionEquiv pi hn1 hpi).toAlgHom.comp f
  exact exists_dvrRootFractionPowerEquiv_of_embedding
    pi hn hpi hunit froot

#print axioms fractionRingAlgEquivOfFiniteEtaleLocal
#print axioms fractionRingAlgEquivOfFiniteEtaleLocalOverFraction
#print axioms normalIntegralAlgEquivOfFractionRingEquiv
#print axioms exists_fractionFieldEmbedding_of_tag0EYE_strict_local_normalization
#print axioms exists_dvrRootFractionPowerEquiv_of_strict_local_normalization

end

end Pcf.Stacks
