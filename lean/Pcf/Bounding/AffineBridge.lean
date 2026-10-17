/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Chart
public import Pcf.Bounding.Divisors
public import Pcf.Bounding.FibreProduct

/-!
# The bounding chart on the concrete affine divisor carrier

`Pcf.affineCrit1` is the codimension-one non-étale locus of an actual ring map, rather than
an abstract predicate supplied as a field of `Pcf.UnnormalizedDynamics`.  The theorem below applies the
derived bounding theorem to this carrier: the restriction attached to a `BoundingChart` has
no codimension-one critical points.

This is the affine form of the identification requested in item 5 of `HANDOFF.md` §9.2.
It deliberately does not construct the global Step 0 chart, nor the normalized dynamics of
a possibly nonnormal divisor; those are the remaining scheme-level parts of A6.
-/

@[expose] public section

namespace Pcf

universe u

set_option linter.style.haveILetI false

/-- On a bounding chart, the concrete codimension-one non-étale locus of the restricted
map `R/(a) → S/𝔭` is empty. -/
theorem BoundingChart.affineCrit1_restriction_eq_empty
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {a : R} {𝔭 : Ideal S} (h : BoundingChart R S a 𝔭) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
    affineCrit1 (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) = ∅ := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact hq (h.isEtaleAt_restriction Stacks.existsPrimeOverBoth q.1)

/-- Pointwise form of `affineCrit1_restriction_eq_empty`. -/
theorem BoundingChart.not_mem_affineCrit1_restriction
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {a : R} {𝔭 : Ideal S} (h : BoundingChart R S a 𝔭)
    (q : HeightOnePrime (S ⧸ 𝔭)) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
    q ∉ affineCrit1 (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
  rw [h.affineCrit1_restriction_eq_empty]
  simp

end Pcf
