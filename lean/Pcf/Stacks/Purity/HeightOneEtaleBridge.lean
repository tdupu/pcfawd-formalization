/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Pcf.Stacks.Purity.DiscriminantFiber

/-!
# Height-one base change from codimension-one unramifiedness

This file supplies the geometric input to the finite-free discriminant argument in Stacks
Tags `0BJH` and `0BJF`.  For a finite flat algebra, a maximal point after base change to a
height-one localization contracts to a height-one point of the original source.  Thus the
literal codimension-one unramifiedness hypothesis makes every such maximal point etale.  Since
the etale locus is open, it is then the whole height-one base change.

No connectedness or domain hypothesis is imposed on the finite algebra.  This is important for
the finite torsion-free Stacks-normal algebras occurring in Tag `0BM9`, which are allowed to be
disconnected.
-/

open scoped TensorProduct

namespace Pcf.Stacks

universe u v z

/-- A finite flat algebra preserves the height of a prime under contraction.

Flatness supplies going down.  Finiteness makes the prime minimal over the extension of its
contraction, so the fibre contribution in the height formula is zero.  Unlike the domain form
of this statement, this version applies to disconnected finite algebras. -/
theorem Ideal.height_under_eq_of_finite_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite R S] [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] :
    (P.under R).height = P.height := by
  let p : Ideal R := P.under R
  letI : p.IsPrime := Ideal.IsPrime.under R P
  letI : P.LiesOver p := ⟨rfl⟩
  let q : Ideal (S ⧸ p.map (algebraMap R S)) :=
    P.map (Ideal.Quotient.mk (p.map (algebraMap R S)))
  have hq : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa [p] using Ideal.map_comap_le)
  have hPmin : P ∈ (p.map (algebraMap R S)).minimalPrimes :=
    Ideal.IsIntegral.mem_minimalPrimes_map_under P
  rw [Ideal.minimalPrimes_eq_comap] at hPmin
  obtain ⟨q', hq'min, hq'⟩ := hPmin
  have hqq' : q = q' := by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [show q.comap (Ideal.Quotient.mk _) = P by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      apply sup_eq_left.mpr
      change (P.under R).map (algebraMap R S) ≤ P
      exact Ideal.map_comap_le]
    exact hq'.symm
  have hq0 : q.height = 0 := Ideal.height_eq_zero_iff.mpr (hqq' ▸ hq'min)
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  rw [show P.map (Ideal.Quotient.mk (p.map (algebraMap R S))) = q by rfl,
    hq0, add_zero] at hheight
  exact hheight.symm

/-- The contraction to `S` of a maximal point of the height-one base change has contraction
`p` to the base. -/
theorem heightOneBaseChange_maximal_under_under
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (p : Ideal R) [p.IsPrime]
    (Q : Ideal (Localization.AtPrime p ⊗[R] S)) [Q.IsMaximal] :
    (Q.comap Algebra.TensorProduct.includeRight.toRingHom).under R = p := by
  let A := Localization.AtPrime p ⊗[R] S
  letI : Algebra S A := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul x)
  have hQpmax : (Q.under (Localization.AtPrime p)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hQp : Q.under (Localization.AtPrime p) =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    IsLocalRing.eq_maximalIdeal hQpmax
  have hleft :
      ((Q.comap Algebra.TensorProduct.includeRight.toRingHom).under R) = Q.under R := by
    exact Ideal.under_under Q
  have hright : (Q.under (Localization.AtPrime p)).under R = Q.under R := by
    exact Ideal.under_under Q
  rw [hleft, ← hright, hQp]
  exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p

/-- **Height-one geometric bridge (`0BJH`/`0BJF`).**

If a finite flat algebra is unramified at every codimension-one source point, then its base
change to the localization at every height-one base prime is etale.  The statement quantifies
over the source primes themselves, exactly as does the punctured-source hypothesis in the
purity argument; it does not replace that hypothesis by a conclusion-shaped base-change
assumption. -/
theorem Algebra.etale_heightOne_baseChange_of_unramifiedAt_height_one
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite R S] [Module.Flat R S]
    (hunramified : ∀ (q : Ideal S) [q.IsPrime], q.height = 1 →
      Algebra.IsUnramifiedAt R q)
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] S) := by
  let Rp := Localization.AtPrime p
  let A := Rp ⊗[R] S
  letI : Algebra S A := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul x)
  letI : Module.Finite Rp A := inferInstance
  letI : Module.FinitePresentation Rp A :=
    Module.finitePresentation_of_finite Rp A
  letI : Algebra.FinitePresentation Rp A := inferInstance
  letI : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  letI : Algebra.FinitePresentation R S := inferInstance
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro Q
  obtain ⟨M, hMmax, hQM⟩ := Q.asIdeal.exists_le_maximal Q.isPrime.ne_top
  letI : M.IsMaximal := hMmax
  letI : M.IsPrime := hMmax.isPrime
  let q : Ideal S := M.comap Algebra.TensorProduct.includeRight.toRingHom
  letI : q.IsPrime := Ideal.IsPrime.comap _
  have hqunder : q.under R = p :=
    heightOneBaseChange_maximal_under_under (R := R) (S := S) p M
  have hqheight : q.height = 1 := by
    rw [← Ideal.height_under_eq_of_finite_of_flat (R := R) q, hqunder, hp]
  letI : Algebra.IsUnramifiedAt R q := hunramified q hqheight
  letI : Algebra.IsEtaleAt R q :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
  have hloc : Algebra.FormallyEtale R (Localization.AtPrime M) := by
    letI : IsLocalization.AtPrime (Localization.AtPrime M) q :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime M) M
    let e : Localization.AtPrime q ≃ₐ[S] Localization.AtPrime M :=
      IsLocalization.algEquiv q.primeCompl _ _
    exact Algebra.FormallyEtale.of_equiv (e.restrictScalars R)
  letI : Algebra.FormallyEtale R (Localization.AtPrime M) := hloc
  letI : Algebra.FormallyUnramified R Rp :=
    Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  letI : Algebra.FormallyEtale Rp (Localization.AtPrime M) :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  letI : Algebra.IsEtaleAt Rp M := inferInstance
  obtain ⟨f, hfM, hf⟩ := Algebra.exists_etale_of_isEtaleAt (R := Rp) M
  have hfQ : f ∉ Q.asIdeal := fun hfQ ↦ hfM (hQM hfQ)
  exact (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := Rp) (f := f)).mpr hf hfQ

/-- The finite-free local discriminant endpoint with its height-one input discharged from the
literal codimension-one unramifiedness hypothesis on the source. -/
theorem Algebra.etale_of_genericFiber_and_unramifiedAt_height_one
    {R S K : Type u} {ι : Type z}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S)
    [Algebra.FormallyEtale K (K ⊗[R] S)]
    (hunramified : ∀ (q : Ideal S) [q.IsPrime], q.height = 1 →
      Algebra.IsUnramifiedAt R q) :
    Algebra.Etale R S := by
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  apply Algebra.etale_of_genericFiber_and_heightOne_baseChange (K := K) b
  intro p _ hp
  exact Algebra.etale_heightOne_baseChange_of_unramifiedAt_height_one
    hunramified p hp

end Pcf.Stacks
