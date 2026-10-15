/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Pcf.Stacks.Common.RegularDimensionOne
public import Pcf.Stacks.Purity.Defs
public import Pcf.Stacks.Purity.LocalEtale

/-!
# The dimension-one case of Zariski--Nagata purity

This module proves the base case in the dimension induction of Stacks Tag `0BMB` (the first
paragraph of the proof).  Both local rings are DVRs.  Quasi-finiteness forces the local ring map
to be injective, hence torsion-free and flat; formal unramifiedness then gives formal étaleness.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

open IsLocalRing

/-- A one-dimensional Noetherian normal local domain is a discrete valuation ring.

This is the normal-local half of Stacks Tag `00PD`.  The regular-local half used below is
`isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one`. -/
theorem isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hnotfield : ¬ IsField R := by
    intro h
    exact zero_ne_one ((ringKrullDim_eq_zero_of_isField h).symm.trans hdim)
  apply ((IsDiscreteValuationRing.TFAE R hnotfield).out 4 1).mp
  refine ⟨inferInstance, maximalIdeal R, ⟨?_, inferInstance⟩, ?_⟩
  · exact (IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnotfield)
  · intro P hP
    have hle : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim.le
    exact IsLocalRing.eq_maximalIdeal
      ((Ring.krullDimLE_one_iff_of_isPrime_bot.mp hle) P hP.1 hP.2)

/-- The dimension-one branch of the affine pointwise Zariski--Nagata purity statement.

This proves the base case of Tag `0BMB`, not the full tag: the higher-dimensional induction
still requires punctured-spectrum purity (Tag `0BMA`) and the étale-local finite reduction
(Tag `02LK`). -/
theorem hasZariskiNagataPurityAt_of_height_eq_one
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (w : PrimeSpectrum S) (hw : w.asIdeal.height = 1) :
    HasZariskiNagataPurityAt R S w := by
  intro h
  let p := w.asIdeal.under R
  let q := w.asIdeal
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let _ : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let _ : IsScalarTower R Rp Sq := by infer_instance
  let _ : IsLocalHom (algebraMap Rp Sq) := by infer_instance
  let _ : IsRegularLocalRing Rp := h.target_isRegular
  let _ : IsDomain Rp := isDomain_of_isRegularLocalRing Rp
  let _ : IsDomain Sq := h.source_isDomain
  let _ : IsIntegrallyClosed Sq := h.source_isIntegrallyClosed
  have hpHeight : p.height = 1 := h.equalDimension.symm.trans hw
  have hRpDim : ringKrullDim Rp = 1 := by
    simpa [hpHeight] using IsLocalization.AtPrime.ringKrullDim_eq_height p Rp
  have hSqDim : ringKrullDim Sq = 1 := by
    have hqHeight : q.height = 1 := hw
    simpa only [hqHeight, WithBot.coe_one] using
      IsLocalization.AtPrime.ringKrullDim_eq_height q Sq
  let _ : IsDiscreteValuationRing Rp :=
    isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one Rp hRpDim
  let _ : IsDiscreteValuationRing Sq :=
    isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one Sq hSqDim
  let _ : Algebra.QuasiFinite R Sq := h.quasiFinite
  let _ : Algebra.QuasiFinite Rp Sq := Algebra.QuasiFinite.of_restrictScalars R Rp Sq
  have hinjective : Function.Injective (algebraMap Rp Sq) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    have hkerMax : RingHom.ker (algebraMap Rp Sq) = maximalIdeal Rp := by
      have hkerPrime : (RingHom.ker (algebraMap Rp Sq)).IsPrime :=
        RingHom.ker_isPrime (algebraMap Rp Sq)
      have hle : Ring.KrullDimLE 1 Rp := Ring.krullDimLE_iff.mpr hRpDim.le
      exact IsLocalRing.eq_maximalIdeal
        ((Ring.krullDimLE_one_iff_of_isPrime_bot.mp hle) _ hker hkerPrime)
    have hunderBot : Ideal.under Rp (⊥ : Ideal Sq) = maximalIdeal Rp := by
      simpa [Ideal.under_def, hkerMax]
    have hunderMax : Ideal.under Rp (maximalIdeal Sq) = maximalIdeal Rp := by
      exact IsLocalRing.maximalIdeal_comap (algebraMap Rp Sq)
    have hbotMax : (⊥ : Ideal Sq) = maximalIdeal Sq :=
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := Rp) _ _ bot_le
        (hunderBot.trans hunderMax.symm)
    exact IsDiscreteValuationRing.not_isField Sq
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbotMax.symm)
  let _ : Module.IsTorsionFree Rp Sq :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjective
  let _ : Module.Flat Rp Sq := by infer_instance
  let _ : Algebra.FormallyUnramified R Sq :=
    h.unramifiedCodimensionOne w (by rfl) hw
  let _ : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  let _ : Algebra.EssFiniteType R Sq := by infer_instance
  let _ : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let P := Algebra.EssFiniteType.subalgebra Rp Sq
  let M := Algebra.EssFiniteType.submonoid Rp Sq
  let _ : Algebra.FinitePresentation Rp P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let _ : Algebra.FormallyEtale Rp Sq :=
    formallyEtale_of_flat_of_formallyUnramified_of_isLocalization Rp Sq P M
  exact Algebra.FormallyEtale.comp R Rp Sq

end Pcf.Stacks
