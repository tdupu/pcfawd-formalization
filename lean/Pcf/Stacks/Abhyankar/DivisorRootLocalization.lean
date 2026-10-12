/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.HeightOneKummerTransport
import Pcf.Stacks.Abhyankar.StandardCoverBaseChange

/-!
# The divisor localization of a standard root cover

This file supplies the first localization comparison in the codimension-one part of
Stacks Tag `0EYG`.  If `p` is the divisor prime of the original base, then base changing
the global standard root algebra to `R_p` is the `09EV` root algebra over the DVR `R_p`.
The latter is itself the localization of the global root algebra at the unique prime over
`p`; this prime contains the distinguished root and has height one.

All maps below are the canonical base-change maps.  In particular, the theorem does not
assume an abstract equivalence with the DVR root algebra or any pointwise unramifiedness.
-/

open IsLocalRing

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

noncomputable section

/-- Base change of the global standard root algebra to a divisor localization, written in
the literal `09EV` form `R_p[z]/(z^e-pi)`. -/
noncomputable def standardRootTensorAtPrimeEquivDVRRoot
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (a : R) (exponent : ℕ) :
    TensorProduct R (Localization.AtPrime p)
        (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent))
        ≃ₐ[Localization.AtPrime p]
      AdjoinRoot (dvrRootPoly
        (algebraMap R (Localization.AtPrime p) a) exponent) := by
  let e := standardCoverBaseChangeEquiv
    (R := R) (T := Localization.AtPrime p) (1 : Rˣ) a exponent
  refine e.trans (AdjoinRoot.algEquivOfEq (Localization.AtPrime p) _ _ ?_)
  rw [dvrRootPoly_eq_localPoly]
  simp

@[simp]
theorem standardRootTensorAtPrimeEquivDVRRoot_root
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (a : R) (exponent : ℕ) :
    standardRootTensorAtPrimeEquivDVRRoot R p a exponent
        (1 ⊗ₜ AdjoinRoot.root
          (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent)) =
      AdjoinRoot.root
        (dvrRootPoly (algebraMap R (Localization.AtPrime p) a) exponent) := by
  simp only [standardRootTensorAtPrimeEquivDVRRoot, AlgEquiv.trans_apply,
    AdjoinRoot.algEquivOfEq_root, standardCoverBaseChangeEquiv,
    AdjoinRoot.tensorAlgEquiv_root, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_root]

/-- The prime of the global standard root cover selected by the local `09EV` root DVR.

The algebra structure is the actual composite through the tensor-product base change.
This definition is useful because its localization is therefore definitionally compatible
with the base-change square used by `0BRM`. -/
noncomputable def standardRootDivisorPrime
    (R : Type u) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    (a : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible (algebraMap R (Localization.AtPrime p) a)) :
    Ideal (AdjoinRoot (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent)) := by
  let Rp := Localization.AtPrime p
  let pi := algebraMap R Rp a
  let B := AdjoinRoot (dvrRootPoly pi exponent)
  letI : IsDomain B := dvrRootAlgebra_isDomain pi hexponent hpi
  letI : IsDiscreteValuationRing B :=
    dvrRootAlgebra_isDiscreteValuationRing pi hexponent hpi
  exact (maximalIdeal B).comap
    ((standardRootTensorAtPrimeEquivDVRRoot R p a exponent).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := R) (A := Rp)
        (B := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent))).toRingHom)

/-- The local `09EV` root algebra is the localization of the global standard root cover at
the selected divisor prime.  The theorem also records that this prime contains the actual
global root and has height one, so a height-one prime containing the root must be this one.
-/
theorem standardRoot_dvrRoot_isLocalizationAtDivisorPrime
    (R : Type u) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    (a : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible (algebraMap R (Localization.AtPrime p) a)) :
    let C := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent)
    let Rp := Localization.AtPrime p
    let pi := algebraMap R Rp a
    let B := AdjoinRoot (dvrRootPoly pi exponent)
    let eBC := standardRootTensorAtPrimeEquivDVRRoot R p a exponent
    let _ : Algebra C B :=
      ((eBC.toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeRight (R := R) (A := Rp) (B := C))).toRingHom.toAlgebra
    let q := standardRootDivisorPrime R p a exponent hexponent hpi
    ∃ hq : q.IsPrime,
      let _ : q.IsPrime := hq
      IsLocalization q.primeCompl B ∧
        algebraMap C B (AdjoinRoot.root
          (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent)) =
          AdjoinRoot.root (dvrRootPoly pi exponent) ∧
        AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent) ∈ q ∧
        q.height = 1 := by
  dsimp only
  let C := AdjoinRoot (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent)
  let Rp := Localization.AtPrime p
  let pi := algebraMap R Rp a
  let B := AdjoinRoot (dvrRootPoly pi exponent)
  let eBC := standardRootTensorAtPrimeEquivDVRRoot R p a exponent
  letI : IsDomain B := dvrRootAlgebra_isDomain pi hexponent hpi
  letI : IsDiscreteValuationRing B :=
    dvrRootAlgebra_isDiscreteValuationRing pi hexponent hpi
  letI : Algebra C B :=
    ((eBC.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := Rp) (B := C))).toRingHom.toAlgebra
  let q : Ideal C := standardRootDivisorPrime R p a exponent hexponent hpi
  have hq : q = (maximalIdeal B).under C := rfl
  letI : q.IsPrime := by rw [hq]; infer_instance
  let M := Algebra.algebraMapSubmonoid C p.primeCompl
  letI : Algebra C (TensorProduct R Rp C) :=
    Algebra.TensorProduct.rightAlgebra
  let eC : TensorProduct R Rp C ≃ₐ[C] B :=
    { eBC.toRingEquiv with
      commutes' := fun x ↦ rfl }
  letI : IsLocalization M (TensorProduct R Rp C) :=
    inferInstance
  letI : IsLocalization M B :=
    IsLocalization.isLocalization_of_algEquiv M eC
  have hle : M ≤ q.primeCompl := by
    intro x hx
    change (x : C) ∉ q
    rw [hq, Ideal.mem_comap]
    intro hmem
    exact (maximalIdeal.isMaximal B).ne_top
      ((maximalIdeal B).eq_top_of_isUnit_mem hmem
        (IsLocalization.map_units B ⟨x, hx⟩))
  have hdvd : ∀ x ∈ q.primeCompl, ∃ m ∈ M, x ∣ m := by
    intro x hx
    have hxnot : algebraMap C B x ∉ maximalIdeal B := by
      simpa only [Ideal.mem_primeCompl_iff, hq, Ideal.mem_comap] using hx
    have hunit : IsUnit (algebraMap C B x) := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Classical.not_not] using hxnot
    exact (IsLocalization.algebraMap_isUnit_iff M).mp hunit
  letI : IsLocalization q.primeCompl B :=
    (IsLocalization.iff_of_le_of_exists_dvd M q.primeCompl hle hdvd).mp inferInstance
  have hroot : algebraMap C B
      (AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent)) =
      AdjoinRoot.root (dvrRootPoly pi exponent) := by
    exact standardRootTensorAtPrimeEquivDVRRoot_root R p a exponent
  have hrootMax : AdjoinRoot.root (dvrRootPoly pi exponent) ∈ maximalIdeal B := by
    rw [← IsLocalRing.eq_maximalIdeal
      (dvrRootIdeal_isMaximal pi hexponent hpi)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hheightMax : (maximalIdeal B).height = 1 := by
    rw [← WithBot.coe_inj]
    calc
      ((maximalIdeal B).height : WithBot ℕ∞) = ringKrullDim B :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      _ = 1 := IsDiscreteValuationRing.ringKrullDim_eq_one B
  refine ⟨inferInstance, inferInstance, hroot, ?_, ?_⟩
  · change AdjoinRoot.root
      (Pcf.LocalModel.localPoly (1 : Rˣ) a exponent) ∈ q
    rw [hq, Ideal.mem_comap, hroot]
    exact hrootMax
  · change q.height = 1
    rw [hq, IsLocalization.height_under q.primeCompl]
    exact hheightMax

#print axioms standardRootTensorAtPrimeEquivDVRRoot
#print axioms standardRootTensorAtPrimeEquivDVRRoot_root
#print axioms standardRoot_dvrRoot_isLocalizationAtDivisorPrime

end

end Pcf.Stacks
