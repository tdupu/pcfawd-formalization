/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineFunctionField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The actual residue extension along the Frobenius line

The residue field at the actual prime `(v)` is identified with `k(u)` by the
quotient equivalence and fraction-field universal property. The actual induced
residue-field homomorphism is conjugate to the previously constructed map
`u ↦ u^p`, so it is purely inseparable and not separable.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open Polynomial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

instance lineIdeal_isPrime : (lineIdeal k).IsPrime := by
  rw [← lineEvaluation_ker]
  exact RingHom.ker_isPrime _

noncomputable def lineResidueEquiv : (lineIdeal k).ResidueField ≃+* RatFunc k :=
  IsFractionRing.ringEquivOfRingEquiv (lineQuotientEquiv k).toRingEquiv

@[simp] theorem lineResidueEquiv_on_plane (q : Plane k) :
    lineResidueEquiv k (algebraMap (Plane k) (lineIdeal k).ResidueField q) =
      algebraMap (Polynomial k) (RatFunc k) (lineEvaluation k q) := by
  change lineResidueEquiv k
    (algebraMap (Plane k ⧸ lineIdeal k) (lineIdeal k).ResidueField (Ideal.Quotient.mk _ q)) = _
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (lineQuotientEquiv k).toRingEquiv _

/-- The actual residue-field pullback at the invariant prime `(v)`. -/
noncomputable def lineResidueMap : (lineIdeal k).ResidueField →ₐ[k] (lineIdeal k).ResidueField :=
  Ideal.ResidueField.mapₐ (lineIdeal k) (lineIdeal k) (coordinateMap k p)
    (lineIdeal_comap k p (Fact.out : p.Prime).pos).symm

omit [CharP k p] in
@[simp] theorem lineResidueMap_on_plane (q : Plane k) :
    lineResidueMap k p (algebraMap (Plane k) (lineIdeal k).ResidueField q) =
      algebraMap (Plane k) (lineIdeal k).ResidueField (coordinateMap k p q) := by
  exact Ideal.ResidueField.map_algebraMap ..

omit [CharP k p] in
/-- The two residue-field models give the same actual pullback.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineResidueMap_conjugation :
    (lineFunctionFieldMap k p).toRingHom.comp (lineResidueEquiv k).toRingHom =
      (lineResidueEquiv k).toRingHom.comp (lineResidueMap k p).toRingHom := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Plane k ⧸ lineIdeal k))
  apply RingHom.ext
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change lineFunctionFieldMap k p
      (lineResidueEquiv k (algebraMap (Plane k) (lineIdeal k).ResidueField r)) =
    lineResidueEquiv k (lineResidueMap k p (algebraMap (Plane k) (lineIdeal k).ResidueField r))
  rw [lineResidueEquiv_on_plane, lineFunctionFieldMap_on_polynomial,
    lineResidueMap_on_plane, lineResidueEquiv_on_plane]
  exact congrArg (algebraMap (Polynomial k) (RatFunc k))
    (congrArg (fun f : Plane k →ₐ[k] Polynomial k => f r)
      (restriction_coordinate_square k p)).symm

/-- The actual residue extension along the invariant divisor is not separable.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineResidueMap_not_isSeparable :
    letI := (lineResidueMap k p).toRingHom.toAlgebra
    ¬ Algebra.IsSeparable (lineIdeal k).ResidueField (lineIdeal k).ResidueField := by
  letI := (lineResidueMap k p).toRingHom.toAlgebra
  intro hsep
  letI := hsep
  apply lineFunctionFieldMap_not_isSeparable k p
  letI := (lineFunctionFieldMap k p).toRingHom.toAlgebra
  exact Algebra.IsSeparable.of_equiv_equiv (lineResidueEquiv k) (lineResidueEquiv k)
    (lineResidueMap_conjugation k p)

/-- The actual residue extension along the invariant divisor is purely inseparable.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem lineResidueMap_isPurelyInseparable :
    letI := (lineResidueMap k p).toRingHom.toAlgebra
    IsPurelyInseparable (lineIdeal k).ResidueField (lineIdeal k).ResidueField := by
  letI := (lineResidueMap k p).toRingHom.toAlgebra
  haveI : CharP (lineIdeal k).ResidueField p :=
    charP_of_injective_ringHom (f := (lineResidueEquiv k).symm.toRingHom)
      (lineResidueEquiv k).symm.injective p
  apply (isPurelyInseparable_iff_pow_mem (lineIdeal k).ResidueField p).mpr
  intro x
  let j := lineFunctionFieldMap k p
  letI := j.toRingHom.toAlgebra
  obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem (RatFunc k) p).mp
    (lineFunctionFieldMap_isPurelyInseparable k p) (lineResidueEquiv k x)
  refine ⟨n, (lineResidueEquiv k).symm y, ?_⟩
  apply (lineResidueEquiv k).injective
  rw [map_pow]
  have h := congrArg (fun f : (lineIdeal k).ResidueField →+* RatFunc k =>
    f ((lineResidueEquiv k).symm y)) (lineResidueMap_conjugation k p)
  change j (lineResidueEquiv k ((lineResidueEquiv k).symm y)) =
    lineResidueEquiv k (lineResidueMap k p ((lineResidueEquiv k).symm y)) at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm.trans hy

#print axioms lineResidueEquiv_on_plane
#print axioms lineResidueMap_conjugation
#print axioms lineResidueMap_not_isSeparable
#print axioms lineResidueMap_isPurelyInseparable

end Pcf.Examples.PaperP.FrobeniusLine
