/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFibreValuationSquare
public import Pcf.Bounding.Divisors
public import Pcf.Bounding.ReducedFiberBranch
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Reduced local fibres without a finite source map

The comparison map `D' → A'` in `paper-p.tex`, Lemma `lem:primary-fibres`,
is dominant but need not be finite. At a source divisor over a target
divisor, the pullback of the target maximal ideal is a nonzero proper
ideal in the source DVR. A reduced local fibre is equivalent to that ideal
having valuation one. This statement needs no module-finiteness assumption.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

noncomputable section

open IsLocalRing

set_option linter.style.haveILetI false

/-- In a DVR, a nonzero proper ideal has reduced quotient precisely when
the quotient has length one. This is the local multiplicity-one criterion
for a reduced geometric fibre, without assuming the morphism is finite. -/
theorem reduced_quotient_iff_length_one_of_dvr
    (S : Type*) [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsDiscreteValuationRing S]
    (I : Ideal S) (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    _root_.IsReduced (S ⧸ I) ↔ (Module.length S (S ⧸ I)).toNat = 1 := by
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal S inferInstance I hI0
  have hnpos : 0 < n := by
    by_contra h
    have hzero : n = 0 := Nat.eq_zero_of_not_pos h
    exact hItop (by simpa [hzero] using hn)
  rw [← Ideal.isRadical_iff_quotient_reduced, hn,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
    ENat.toNat_natCast]
  constructor
  · intro hrad
    have heq : maximalIdeal S ^ n = maximalIdeal S := by
      rw [← hrad.radical, Ideal.radical_pow (maximalIdeal S) (Nat.ne_of_gt hnpos)]
      exact (inferInstance : (maximalIdeal S).IsPrime).radical
    have hcoheight := congrArg Order.coheight heq
    have hleft : Order.coheight (maximalIdeal S ^ n) = (n : ℕ∞) := by
      rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal]
    have hright : Order.coheight (maximalIdeal S) = (1 : ℕ∞) := by
      rw [← pow_one (maximalIdeal S),
        IsDiscreteValuationRing.coheight_pow_maximalIdeal]
      norm_num
    exact_mod_cast hleft.symm.trans (hcoheight.trans hright)
  · intro hn1
    rw [hn1, pow_one]
    exact (inferInstance : (maximalIdeal S).IsPrime).isRadical

#print axioms reduced_quotient_iff_length_one_of_dvr

/-- At a normal source divisor, a reduced local fibre has ramification
index one even when the dominant source map is not finite. The two
nontriviality hypotheses say that the pulled-back target divisor defines
a nonzero proper ideal in the source DVR. -/
theorem localFiber_isReduced_iff_ramificationIdx_eq_one_of_nonzero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [IsDomain S] [IsIntegrallyClosed S]
    (Q : Pcf.HeightOnePrime S)
    (hI0 : (Q.1.asIdeal.under R).map
      (algebraMap R (Localization.AtPrime Q.1.asIdeal)) ≠ ⊥)
    (hItop : (Q.1.asIdeal.under R).map
      (algebraMap R (Localization.AtPrime Q.1.asIdeal)) ≠ ⊤) :
    _root_.IsReduced
      (Localization.AtPrime Q.1.asIdeal ⧸
        (Q.1.asIdeal.under R).map
          (algebraMap R (Localization.AtPrime Q.1.asIdeal))) ↔
      Q.1.asIdeal.ramificationIdx R = 1 := by
  let Sq := Localization.AtPrime Q.1.asIdeal
  letI : IsDiscreteValuationRing Sq :=
    Pcf.heightOnePrime_localRing_isDiscreteValuationRing Q
  rw [Ideal.ramificationIdx_def]
  exact reduced_quotient_iff_length_one_of_dvr Sq _ hI0 hItop

#print axioms localFiber_isReduced_iff_ramificationIdx_eq_one_of_nonzero

/-- Local reducedness of an affine fibre at a specified source divisor
detects its ramification index even when the source map is not finite.
The source divisor and its contraction are supplied explicitly because
height preservation is not automatic for a nonfinite map. -/
theorem localizationFiber_isReduced_iff_ramificationIdx_eq_one_of_nonzero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    (p : Pcf.HeightOnePrime R) (Q : Pcf.HeightOnePrime S)
    [Q.1.asIdeal.LiesOver p.1.asIdeal]
    (q : Ideal (p.1.asIdeal.Fiber S)) [q.IsPrime]
    (hq : q.comap Algebra.TensorProduct.includeRight = Q.1.asIdeal)
    (hI0 : p.1.asIdeal.map
      (algebraMap R (Localization.AtPrime
        (q.comap Algebra.TensorProduct.includeRight))) ≠ ⊥)
    (hItop : p.1.asIdeal.map
      (algebraMap R (Localization.AtPrime
        (q.comap Algebra.TensorProduct.includeRight))) ≠ ⊤) :
    _root_.IsReduced (Localization.AtPrime q) ↔
      Q.1.asIdeal.ramificationIdx R = 1 := by
  let r : Ideal S := q.comap Algebra.TensorProduct.includeRight
  letI : r.IsPrime := (inferInstance : q.IsPrime).comap
    Algebra.TensorProduct.includeRight
  letI : r.LiesOver p.1.asIdeal := inferInstance
  letI : Algebra (Localization.AtPrime p.1.asIdeal)
      (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p.1.asIdeal r
  let e := Ideal.Fiber.localizationAlgEquivQuotient p.1.asIdeal q
  have hrheight : r.height = 1 := by rw [show r = Q.1.asIdeal from hq]; exact Q.2
  let Qr : Pcf.HeightOnePrime S := ⟨⟨r, inferInstance⟩, hrheight⟩
  have hunder : r.under R = p.1.asIdeal :=
    (Ideal.LiesOver.over (p := p.1.asIdeal) (P := r)).symm
  have hlocal := localFiber_isReduced_iff_ramificationIdx_eq_one_of_nonzero
    (R := R) Qr (hunder ▸ hI0) (hunder ▸ hItop)
  have hlocal' : _root_.IsReduced
      (Localization.AtPrime r ⧸
        p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) ↔
      r.ramificationIdx R = 1 := by
    rw [hunder] at hlocal
    exact hlocal
  constructor
  · intro hred
    letI : _root_.IsReduced (Localization.AtPrime q) := hred
    have hquot : _root_.IsReduced
        (Localization.AtPrime r ⧸
          p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) := by
      exact isReduced_of_injective e.symm e.symm.injective
    simpa only [show r = Q.1.asIdeal from hq] using hlocal'.mp hquot
  · intro hram
    have hquot : _root_.IsReduced
        (Localization.AtPrime r ⧸
          p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) :=
      hlocal'.mpr (by simpa only [show r = Q.1.asIdeal from hq] using hram)
    letI : _root_.IsReduced
        (Localization.AtPrime r ⧸
          p.1.asIdeal.map (algebraMap R (Localization.AtPrime r))) := hquot
    exact isReduced_of_injective e e.injective

#print axioms localizationFiber_isReduced_iff_ramificationIdx_eq_one_of_nonzero

/-- A reduced affine fibre has multiplicity one at every specified
height-one source prime lying above the target divisor. No finiteness
assumption on `S` over `R` is used. -/
theorem ramificationIdx_eq_one_of_reduced_affineFiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S]
    (p : Pcf.HeightOnePrime R) (Q : Pcf.HeightOnePrime S)
    [Q.1.asIdeal.LiesOver p.1.asIdeal]
    (q : Ideal (p.1.asIdeal.Fiber S)) [q.IsPrime]
    (hq : q.comap Algebra.TensorProduct.includeRight = Q.1.asIdeal)
    (hI0 : p.1.asIdeal.map
      (algebraMap R (Localization.AtPrime
        (q.comap Algebra.TensorProduct.includeRight))) ≠ ⊥)
    (hItop : p.1.asIdeal.map
      (algebraMap R (Localization.AtPrime
        (q.comap Algebra.TensorProduct.includeRight))) ≠ ⊤)
    (hred : _root_.IsReduced (p.1.asIdeal.Fiber S)) :
    Q.1.asIdeal.ramificationIdx R = 1 := by
  letI : _root_.IsReduced (p.1.asIdeal.Fiber S) := hred
  have hredq : _root_.IsReduced (Localization.AtPrime q) := inferInstance
  exact (localizationFiber_isReduced_iff_ramificationIdx_eq_one_of_nonzero
    p Q q hq hI0 hItop).mp hredq

#print axioms ramificationIdx_eq_one_of_reduced_affineFiber

/-- For a dominant affine map, the nonzero-proper conditions on the
pulled-back divisor follow from injectivity and the fact that the source
prime lies over the target prime. Thus reducedness of the actual fibre
alone forces multiplicity one at a specified divisorial component. -/
theorem ramificationIdx_eq_one_of_reduced_affineFiber_dominant
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsDomain R] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [FaithfulSMul R S]
    (p : Pcf.HeightOnePrime R) (Q : Pcf.HeightOnePrime S)
    [Q.1.asIdeal.LiesOver p.1.asIdeal]
    (q : Ideal (p.1.asIdeal.Fiber S)) [q.IsPrime]
    (hq : q.comap Algebra.TensorProduct.includeRight = Q.1.asIdeal)
    (hred : _root_.IsReduced (p.1.asIdeal.Fiber S)) :
    Q.1.asIdeal.ramificationIdx R = 1 := by
  let r : Ideal S := q.comap Algebra.TensorProduct.includeRight
  letI : r.IsPrime := (inferInstance : q.IsPrime).comap
    Algebra.TensorProduct.includeRight
  let Sq := Localization.AtPrime r
  letI : FaithfulSMul R Sq := FaithfulSMul.trans R S Sq
  have hpn : p.1.asIdeal ≠ ⊥ := Ideal.ne_bot_of_height_eq_one p.2
  have hI0 : p.1.asIdeal.map (algebraMap R Sq) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hpn
  have hbase : p.1.asIdeal = Q.1.asIdeal.under R :=
    Ideal.LiesOver.over (p := p.1.asIdeal) (P := Q.1.asIdeal)
  have hle0 : p.1.asIdeal.map (algebraMap R S) ≤ r := by
    rw [hbase, show r = Q.1.asIdeal from hq]
    exact Ideal.map_comap_le
  have hle : p.1.asIdeal.map (algebraMap R Sq) ≤ IsLocalRing.maximalIdeal Sq := by
    calc
      p.1.asIdeal.map (algebraMap R Sq) =
          (p.1.asIdeal.map (algebraMap R S)).map (algebraMap S Sq) := by
        rw [Ideal.map_map]
        rfl
      _ ≤ r.map (algebraMap S Sq) := Ideal.map_mono hle0
      _ = IsLocalRing.maximalIdeal Sq :=
        IsLocalization.AtPrime.map_eq_maximalIdeal r Sq
  have hItop : p.1.asIdeal.map (algebraMap R Sq) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal Sq).ne_top hle
  exact ramificationIdx_eq_one_of_reduced_affineFiber
    p Q q hq hI0 hItop hred

#print axioms ramificationIdx_eq_one_of_reduced_affineFiber_dominant

end
end Pcf.Bounding.PrimaryFibres
