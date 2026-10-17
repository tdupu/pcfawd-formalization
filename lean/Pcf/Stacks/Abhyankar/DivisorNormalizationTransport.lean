/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.LocalizedNormalizationComparison
public import Mathlib.RingTheory.Localization.AtPrime.Extension

/-!
# The divisor-local normalization in the canonical punctured root square

This file performs the integral-closure uniqueness step in the divisor branch of Stacks
Tag `0EYG`.  An actual normalization is first localized at the multiplicative system of
the upper divisor.  Once the resulting generic algebra is identified with the literal
punctured `09EV` root square, localization of integral closure and uniqueness identify the
localized normalization with `DVRRootPuncturedNormalization`.

The generic equivalence below is the base-change square, not an equivalence of the desired
integral models.  The latter is constructed here, together with its compatibility with the
embeddings in the generic algebra.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

open IsLocalRing

set_option linter.style.haveILetI false
set_option maxRecDepth 4096

noncomputable section

/-- The localization of an actual normalization is canonically the literal normalization
in the punctured DVR root square, after identifying the two generic ambient algebras. -/
noncomputable def localizedNormalizationEquivDVRRootPuncturedNormalization
    (A R N D : Type u)
    [CommRing A] [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) [Algebra A (Localization M)]
    (pi : A) (piS : Localization M) (exponent : ℕ)
    (genericEquiv :
      Localization (Algebra.algebraMapSubmonoid D M) ≃ₐ[Localization M]
        DVRRootPuncturedBaseChange
          A (Localization M) pi piS exponent) :
    let S := Localization M
    let Nm := Localization (Algebra.algebraMapSubmonoid N M)
    let Dm := Localization (Algebra.algebraMapSubmonoid D M)
    let C := DVRRootPuncturedBaseChange A S pi piS exponent
    let _ : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
    let _ : IsScalarTower S Nm Dm :=
      localizedNormalization_isScalarTower R N D M
    let _ : Algebra Nm C :=
      normalizationAlgebraOfGenericEquiv S Nm Dm C genericEquiv
    let _ : IsScalarTower S Nm C :=
      normalizationAlgebraOfGenericEquiv_isScalarTower S Nm Dm C genericEquiv
    Nm ≃ₐ[S] DVRRootPuncturedNormalization A S pi piS exponent := by
  dsimp only
  let S := Localization M
  let Nm := Localization (Algebra.algebraMapSubmonoid N M)
  let Dm := Localization (Algebra.algebraMapSubmonoid D M)
  let C := DVRRootPuncturedBaseChange A S pi piS exponent
  letI : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
  letI : IsScalarTower S Nm Dm :=
    localizedNormalization_isScalarTower R N D M
  letI : IsIntegralClosure Nm S Dm :=
    localizedNormalization_isIntegralClosure R N D M
  letI : Algebra Nm C :=
    normalizationAlgebraOfGenericEquiv S Nm Dm C genericEquiv
  letI : IsScalarTower S Nm C :=
    normalizationAlgebraOfGenericEquiv_isScalarTower S Nm Dm C genericEquiv
  letI : IsIntegralClosure Nm S C :=
    isIntegralClosure_of_genericEquiv S Nm Dm C genericEquiv
  exact IsIntegralClosure.equiv S Nm C
    (DVRRootPuncturedNormalization A S pi piS exponent)

/-- The divisor-local normalization equivalence is the unique comparison inside the
punctured root generic algebra. -/
theorem localizedNormalizationEquivDVRRootPuncturedNormalization_algebraMap
    (A R N D : Type u)
    [CommRing A] [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (M : Submonoid R) [Algebra A (Localization M)]
    (pi : A) (piS : Localization M) (exponent : ℕ)
    (genericEquiv :
      Localization (Algebra.algebraMapSubmonoid D M) ≃ₐ[Localization M]
        DVRRootPuncturedBaseChange
          A (Localization M) pi piS exponent)
    (x : Localization (Algebra.algebraMapSubmonoid N M)) :
    let S := Localization M
    let Nm := Localization (Algebra.algebraMapSubmonoid N M)
    let Dm := Localization (Algebra.algebraMapSubmonoid D M)
    let C := DVRRootPuncturedBaseChange A S pi piS exponent
    let _ : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
    let _ : IsScalarTower S Nm Dm :=
      localizedNormalization_isScalarTower R N D M
    let _ : Algebra Nm C :=
      normalizationAlgebraOfGenericEquiv S Nm Dm C genericEquiv
    let _ : IsScalarTower S Nm C :=
      normalizationAlgebraOfGenericEquiv_isScalarTower S Nm Dm C genericEquiv
    algebraMap (DVRRootPuncturedNormalization A S pi piS exponent) C
        (localizedNormalizationEquivDVRRootPuncturedNormalization
          A R N D M pi piS exponent genericEquiv x) =
      genericEquiv (algebraMap Nm Dm x) := by
  dsimp only
  let S := Localization M
  let Nm := Localization (Algebra.algebraMapSubmonoid N M)
  let Dm := Localization (Algebra.algebraMapSubmonoid D M)
  let C := DVRRootPuncturedBaseChange A S pi piS exponent
  letI : Algebra Nm Dm := localizedNormalizationAlgebra R N D M
  letI : IsScalarTower S Nm Dm :=
    localizedNormalization_isScalarTower R N D M
  letI : IsIntegralClosure Nm S Dm :=
    localizedNormalization_isIntegralClosure R N D M
  letI : Algebra Nm C :=
    normalizationAlgebraOfGenericEquiv S Nm Dm C genericEquiv
  letI : IsScalarTower S Nm C :=
    normalizationAlgebraOfGenericEquiv_isScalarTower S Nm Dm C genericEquiv
  letI : IsIntegralClosure Nm S C :=
    isIntegralClosure_of_genericEquiv S Nm Dm C genericEquiv
  exact IsIntegralClosure.algebraMap_equiv S Nm C
    (DVRRootPuncturedNormalization A S pi piS exponent) x

/-- Unramifiedness at the prime obtained after simultaneous localization descends back to
the original prime.  The two target local rings are canonically equivalent, while the base
localization is formally unramified over the original base. -/
theorem isUnramifiedAt_of_localizedNormalizationAtPrime
    (R N : Type u) [CommRing R] [CommRing N] [Algebra R N]
    (p : Ideal R) [p.IsPrime]
    (w : Ideal N) [w.IsPrime] [w.LiesOver p]
    (hlocal :
      let Nm := Localization (Algebra.algebraMapSubmonoid N p.primeCompl)
      let wS := w.map (algebraMap N Nm)
      let _ : wS.IsPrime :=
        IsLocalization.AtPrime.isPrime_map_of_liesOver N p Nm w
      Algebra.IsUnramifiedAt (Localization.AtPrime p) wS) :
    Algebra.IsUnramifiedAt R w := by
  let S := Localization.AtPrime p
  let Nm := Localization (Algebra.algebraMapSubmonoid N p.primeCompl)
  let wS : Ideal Nm := w.map (algebraMap N Nm)
  letI : wS.IsPrime :=
    IsLocalization.AtPrime.isPrime_map_of_liesOver N p Nm w
  letI : Algebra.FormallyUnramified S (Localization.AtPrime wS) := hlocal
  letI : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  have hRT : Algebra.FormallyUnramified R (Localization.AtPrime wS) :=
    Algebra.FormallyUnramified.comp R S (Localization.AtPrime wS)
  have hdisjoint : Disjoint
      (Algebra.algebraMapSubmonoid N p.primeCompl : Set N) (w : Set N) :=
    Ideal.disjoint_primeCompl_of_liesOver w p
  have hunder : wS.under N = w :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid N p.primeCompl) Nm inferInstance hdisjoint
  let T := Localization.AtPrime wS
  haveI : IsLocalization.AtPrime T w := by
    have hlocalization : IsLocalization.AtPrime T (wS.under N) :=
      IsLocalization.isLocalization_atPrime_localization_atPrime
      (Algebra.algebraMapSubmonoid N p.primeCompl) wS
    simpa only [hunder] using hlocalization
  let e : Localization.AtPrime w ≃ₐ[N] T :=
    IsLocalization.algEquiv w.primeCompl _ _
  letI : Algebra.FormallyUnramified R T := hRT
  exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars R).symm

/-- The standard-root map into the divisor localization of an actual normalization.

All algebra structures used to construct the map are internal to this definition.  Thus the
resulting ring homomorphism can be installed as the root-algebra structure without exposing
the chain of transported integral-closure instances in downstream statements. -/
noncomputable def localizedDVRRootNormalizationRingHom
    (A R N D : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (p : Ideal R) [p.IsPrime]
    [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [Algebra A (Localization.AtPrime p)]
    [Module.Finite A (Localization.AtPrime p)]
    [FaithfulSMul A (Localization.AtPrime p)]
    [IsLocalHom (algebraMap A (Localization.AtPrime p))]
    (pi : A) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (piS : Localization.AtPrime p) (hpiS : Irreducible piS)
    (heUnit : IsUnit (exponent : Localization.AtPrime p))
    (hramification :
      (maximalIdeal (Localization.AtPrime p)).ramificationIdx A = exponent)
    (genericEquiv :
      Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
          ≃ₐ[Localization.AtPrime p]
        DVRRootPuncturedBaseChange
          A (Localization.AtPrime p) pi piS exponent) :
    AdjoinRoot (dvrRootPoly pi exponent) →+*
      Localization (Algebra.algebraMapSubmonoid N p.primeCompl) := by
  let S := Localization.AtPrime p
  let Nm := Localization (Algebra.algebraMapSubmonoid N p.primeCompl)
  let Dm := Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
  let C := DVRRootPuncturedBaseChange A S pi piS exponent
  letI : Algebra A Nm :=
    ((algebraMap S Nm).comp (algebraMap A S)).toAlgebra
  letI : IsScalarTower A S Nm := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Nm Dm := localizedNormalizationAlgebra R N D p.primeCompl
  letI : IsScalarTower S Nm Dm :=
    localizedNormalization_isScalarTower R N D p.primeCompl
  letI : IsIntegralClosure Nm S Dm :=
    localizedNormalization_isIntegralClosure R N D p.primeCompl
  letI : Algebra Nm C :=
    normalizationAlgebraOfGenericEquiv S Nm Dm C genericEquiv
  letI : IsScalarTower S Nm C :=
    normalizationAlgebraOfGenericEquiv_isScalarTower S Nm Dm C genericEquiv
  letI : IsIntegralClosure Nm S C :=
    isIntegralClosure_of_genericEquiv S Nm Dm C genericEquiv
  let genericEquivK :=
    dvrRootPuncturedBaseChangeEquivDVRRamificationKummerLocalization
      A S pi hpi piS hpiS exponent hramification
  let K := DVRRamificationKummerLocalization
    A S pi hpi piS hpiS exponent hramification
  letI : Algebra Nm K :=
    normalizationAlgebraOfGenericEquiv S Nm C K genericEquivK
  letI : IsScalarTower S Nm K :=
    normalizationAlgebraOfGenericEquiv_isScalarTower S Nm C K genericEquivK
  letI : IsIntegralClosure Nm S K :=
    isIntegralClosure_of_genericEquiv S Nm C K genericEquivK
  let unit := dvrRamificationUnit
    A S pi hpi piS hpiS exponent hramification
  let U := AdjoinRoot (Pcf.Kummer.kummerPoly unit exponent)
  letI : IsIntegralClosure U S K :=
    kummerUnit_isIntegralClosure_localizationAway_uniformizer
      S piS hpiS unit exponent hexponent heUnit
  exact (dvrRootToKummerNormalization
    A S Nm K pi piS unit exponent
      (dvrRamificationUnit_spec
        A S pi hpi piS hpiS exponent hramification)).toRingHom

/-- The divisor-local standard-root map restricts to the canonical composite on the lower
DVR. -/
theorem localizedDVRRootNormalizationRingHom_comp_algebraMap
    (A R N D : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (p : Ideal R) [p.IsPrime]
    [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [Algebra A (Localization.AtPrime p)]
    [Module.Finite A (Localization.AtPrime p)]
    [FaithfulSMul A (Localization.AtPrime p)]
    [IsLocalHom (algebraMap A (Localization.AtPrime p))]
    (pi : A) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (piS : Localization.AtPrime p) (hpiS : Irreducible piS)
    (heUnit : IsUnit (exponent : Localization.AtPrime p))
    (hramification :
      (maximalIdeal (Localization.AtPrime p)).ramificationIdx A = exponent)
    (genericEquiv :
      Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
          ≃ₐ[Localization.AtPrime p]
        DVRRootPuncturedBaseChange
          A (Localization.AtPrime p) pi piS exponent)
    (x : A) :
    localizedDVRRootNormalizationRingHom
        A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification genericEquiv
        (algebraMap A (AdjoinRoot (dvrRootPoly pi exponent)) x) =
      algebraMap (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid N p.primeCompl))
        (algebraMap A (Localization.AtPrime p) x) := by
  simp [localizedDVRRootNormalizationRingHom,
    dvrRootToKummerNormalization]
  rfl

/-- The algebra structure underlying `localizedDVRRootNormalizationRingHom`. -/
@[instance_reducible]
noncomputable def localizedDVRRootNormalizationAlgebra
    (A R N D : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (p : Ideal R) [p.IsPrime]
    [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [Algebra A (Localization.AtPrime p)]
    [Module.Finite A (Localization.AtPrime p)]
    [FaithfulSMul A (Localization.AtPrime p)]
    [IsLocalHom (algebraMap A (Localization.AtPrime p))]
    (pi : A) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (piS : Localization.AtPrime p) (hpiS : Irreducible piS)
    (heUnit : IsUnit (exponent : Localization.AtPrime p))
    (hramification :
      (maximalIdeal (Localization.AtPrime p)).ramificationIdx A = exponent)
    (genericEquiv :
      Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
          ≃ₐ[Localization.AtPrime p]
        DVRRootPuncturedBaseChange
          A (Localization.AtPrime p) pi piS exponent) :
    Algebra (AdjoinRoot (dvrRootPoly pi exponent))
      (Localization (Algebra.algebraMapSubmonoid N p.primeCompl)) :=
  (localizedDVRRootNormalizationRingHom
    A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification
      genericEquiv).toAlgebra

/-- The divisor-localization of an actual normalization is unramified over the standard
root DVR.

Here `p` is the upper divisor prime before localization, `w` is a prime of the actual
normalization lying over `p`, and `genericEquiv` is the literal generic base-change square.
Localization of integral closure supplies the normalization input to `0BRM`.  The image of
`w` lies over the closed point of the upper DVR; the ramification-index factorization and
the equation `root ^ exponent = pi` therefore put the standard root in that prime.  The
height-one Kummer transport theorem then gives unramifiedness, with no unramifiedness or
etaleness premise. -/
theorem isUnramifiedAt_localizedNormalization_of_dvrRootPuncturedGenericEquiv
    (A R N D : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [CommRing N] [CommRing D]
    [Algebra R N] [Algebra R D] [Algebra N D] [IsScalarTower R N D]
    [IsIntegralClosure N R D]
    (p : Ideal R) [p.IsPrime]
    [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [Algebra A (Localization.AtPrime p)]
    [Module.Finite A (Localization.AtPrime p)]
    [FaithfulSMul A (Localization.AtPrime p)]
    [IsLocalHom (algebraMap A (Localization.AtPrime p))]
    [Algebra.HasSeparableResidueFieldsAt A (Localization.AtPrime p) (maximalIdeal A)]
    (pi : A) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (piS : Localization.AtPrime p) (hpiS : Irreducible piS)
    (heUnit : IsUnit (exponent : Localization.AtPrime p))
    (hramification :
      (maximalIdeal (Localization.AtPrime p)).ramificationIdx A = exponent)
    (genericEquiv :
      Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
          ≃ₐ[Localization.AtPrime p]
        DVRRootPuncturedBaseChange
          A (Localization.AtPrime p) pi piS exponent)
    (w : Ideal N) [w.IsPrime] [w.LiesOver p] :
    let Nm := Localization (Algebra.algebraMapSubmonoid N p.primeCompl)
    let wS := w.map (algebraMap N Nm)
    let _ : wS.IsPrime :=
      IsLocalization.AtPrime.isPrime_map_of_liesOver N p Nm w
    let _ : Algebra (AdjoinRoot (dvrRootPoly pi exponent)) Nm :=
      localizedDVRRootNormalizationAlgebra
        A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification genericEquiv
    Algebra.IsUnramifiedAt
      (AdjoinRoot (dvrRootPoly pi exponent)) wS := by
  dsimp only
  let S := Localization.AtPrime p
  let Nm := Localization (Algebra.algebraMapSubmonoid N p.primeCompl)
  let Dm := Localization (Algebra.algebraMapSubmonoid D p.primeCompl)
  let C := DVRRootPuncturedBaseChange A S pi piS exponent
  let wS : Ideal Nm := w.map (algebraMap N Nm)
  letI : wS.IsPrime :=
    IsLocalization.AtPrime.isPrime_map_of_liesOver N p Nm w
  letI : Algebra A Nm :=
    ((algebraMap S Nm).comp (algebraMap A S)).toAlgebra
  letI : IsScalarTower A S Nm := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra Nm Dm := localizedNormalizationAlgebra R N D p.primeCompl
  letI : IsScalarTower S Nm Dm :=
    localizedNormalization_isScalarTower R N D p.primeCompl
  letI : IsIntegralClosure Nm S Dm :=
    localizedNormalization_isIntegralClosure R N D p.primeCompl
  letI : Algebra Nm C :=
    normalizationAlgebraOfGenericEquiv S Nm Dm C genericEquiv
  letI : IsScalarTower S Nm C :=
    normalizationAlgebraOfGenericEquiv_isScalarTower S Nm Dm C genericEquiv
  letI : IsIntegralClosure Nm S C :=
    isIntegralClosure_of_genericEquiv S Nm Dm C genericEquiv
  letI : Algebra (AdjoinRoot (dvrRootPoly pi exponent)) Nm :=
    localizedDVRRootNormalizationAlgebra
      A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification genericEquiv
  letI : IsScalarTower A (AdjoinRoot (dvrRootPoly pi exponent)) Nm := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (localizedDVRRootNormalizationRingHom_comp_algebraMap
      A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification
        genericEquiv x).symm
  letI : wS.LiesOver (maximalIdeal S) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver p S Nm w
  have hpiS_mem : piS ∈ maximalIdeal S := by
    rw [hpiS.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton piS)
  have hpiS_w : algebraMap S Nm piS ∈ wS := by
    change piS ∈ wS.under S
    rw [← Ideal.LiesOver.over (P := wS) (p := maximalIdeal S)]
    exact hpiS_mem
  have hpi_w : algebraMap S Nm (algebraMap A S pi) ∈ wS := by
    rw [dvrRamificationUnit_spec
        A S pi hpi piS hpiS exponent hramification,
      map_mul, map_pow]
    exact wS.mul_mem_left _
      (wS.pow_mem_of_mem hpiS_w exponent (by omega))
  have hroot : algebraMap (AdjoinRoot (dvrRootPoly pi exponent)) Nm
      (AdjoinRoot.root (dvrRootPoly pi exponent)) ∈ wS := by
    apply (inferInstance : wS.IsPrime).mem_of_pow_mem exponent
    rw [← map_pow, dvrRoot_pow_eq]
    change localizedDVRRootNormalizationRingHom
      A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification genericEquiv
        (algebraMap A (AdjoinRoot (dvrRootPoly pi exponent)) pi) ∈ wS
    rw [localizedDVRRootNormalizationRingHom_comp_algebraMap
      A R N D p pi exponent hexponent hpi piS hpiS heUnit hramification genericEquiv pi]
    exact hpi_w
  exact
    isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_of_root_mem
      A S Nm pi exponent hexponent hpi piS hpiS heUnit hramification wS hroot

#print axioms localizedNormalizationEquivDVRRootPuncturedNormalization
#print axioms localizedNormalizationEquivDVRRootPuncturedNormalization_algebraMap
#print axioms isUnramifiedAt_of_localizedNormalizationAtPrime
#print axioms localizedDVRRootNormalizationRingHom
#print axioms localizedDVRRootNormalizationRingHom_comp_algebraMap
#print axioms localizedDVRRootNormalizationAlgebra
#print axioms
  isUnramifiedAt_localizedNormalization_of_dvrRootPuncturedGenericEquiv

end

end Pcf.Stacks
