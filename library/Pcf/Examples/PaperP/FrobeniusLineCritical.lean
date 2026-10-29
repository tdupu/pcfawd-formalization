/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineEtale
public import Pcf.Examples.PaperP.FrobeniusLineResidue
public import Mathlib.RingTheory.Unramified.LocalRing
public import Pcf.Unnormalized.SchemeBranch
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# The actual non-étale divisor of the Frobenius-line map

The invariant prime has inseparable residue extension. It is therefore not
unramified, despite having ramification index one. The complement is étale.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem residueMap_isSeparable_of_isUnramifiedAt
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (hf : I = J.comap f)
    (hft : f.FiniteType) (h : letI := f.toAlgebra; Algebra.IsUnramifiedAt R J) :
    letI := (Ideal.ResidueField.map I J f hf).toAlgebra
    Algebra.IsSeparable I.ResidueField J.ResidueField := by
  letI := f.toAlgebra
  haveI : Algebra.EssFiniteType R S := hft.essFiniteType
  haveI : J.LiesOver I := ⟨hf⟩
  letI : Algebra (Localization.AtPrime I) (Localization.AtPrime J) :=
    Localization.AtPrime.algebraOfLiesOver I J
  haveI : IsScalarTower R (Localization.AtPrime I) (Localization.AtPrime J) := inferInstance
  letI := h
  have hsep : Algebra.IsSeparable I.ResidueField J.ResidueField := inferInstance
  have heq : (inferInstance : Algebra I.ResidueField J.ResidueField) =
      (Ideal.ResidueField.map I J f hf).toAlgebra := by
    apply Algebra.algebra_ext
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    change IsLocalRing.residue _ (algebraMap (Localization.AtPrime I) (Localization.AtPrime J) y) =
      IsLocalRing.residue _ (Localization.localRingHom I J f hf y)
    rw [Localization.AtPrime.algebraMap_eq]
    rfl
  exact heq ▸ hsep

private theorem isUnramifiedAt_of_localRingHom_formallyEtale
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (J : Ideal S) [J.IsPrime]
    (h : (Localization.localRingHom (J.comap f) J f rfl).FormallyEtale) :
    letI := f.toAlgebra
    Algebra.IsUnramifiedAt R J := by
  letI := f.toAlgebra
  let I := J.under R
  letI : Algebra (Localization.AtPrime I) (Localization.AtPrime J) :=
    Localization.AtPrime.algebraOfLiesOver I J
  haveI : IsScalarTower R (Localization.AtPrime I) (Localization.AtPrime J) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (Localization.localRingHom_to_map I J f rfl x).symm
  haveI : Algebra.FormallyEtale (Localization.AtPrime I) (Localization.AtPrime J) := h
  haveI : Algebra.FormallyEtale R (Localization.AtPrime I) :=
    Algebra.FormallyEtale.of_isLocalization I.primeCompl
  haveI := Algebra.FormallyEtale.comp R (Localization.AtPrime I) (Localization.AtPrime J)
  infer_instance

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual ambient ring map is not unramified at its invariant height-one prime. -/
theorem not_isUnramifiedAt_lineIdeal :
    letI := (coordinateMap k p).toRingHom.toAlgebra
    ¬ Algebra.IsUnramifiedAt (Plane k) (lineIdeal k) := by
  intro h
  exact lineResidueMap_not_isSeparable k p
    (residueMap_isSeparable_of_isUnramifiedAt (coordinateMap k p).toRingHom
      (lineIdeal k) (lineIdeal k) (lineIdeal_comap k p (Fact.out : p.Prime).pos).symm
      (coordinateMap_finite k p (Fact.out : p.Prime).two_le).finiteType h)

/-- The generic point of the invariant line in the actual affine plane. -/
noncomputable def linePoint : Spec (.of (Plane k)) := ⟨lineIdeal k, inferInstance⟩

/-- The actual scheme stalk map is not formally étale at the invariant line. -/
theorem schemeMap_stalk_not_formallyEtale_linePoint :
    ¬ ((schemeMap k p).stalkMap (linePoint k)).hom.FormallyEtale := by
  intro h
  have hlocal := (Pcf.formallyEtale_respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (coordinateMap k p).toRingHom)
      (linePoint k))).mp h
  exact not_isUnramifiedAt_lineIdeal k p
    (isUnramifiedAt_of_localRingHom_formallyEtale (coordinateMap k p).toRingHom
      (lineIdeal k) hlocal)

/-- The invariant line has codimension one. -/
theorem linePoint_coheight : Order.coheight (linePoint k) = 1 := by
  rw [← idealHeight_eq_coheight (.of (Plane k)) (linePoint k)]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (1 : Fin 2)))
    (MvPolynomial.X_prime (R := k) (i := (1 : Fin 2))).not_isUnit

/-- The actual integral effective divisor represented by the invariant line. -/
noncomputable def lineDivisor : Pcf.SchemeDivisorPoint (Spec (.of (Plane k))) :=
  ⟨linePoint k, linePoint_coheight k⟩

/-- Every other integral effective divisor lies in the étale locus. -/
theorem divisor_stalk_formallyEtale_of_ne_line
    (d : Pcf.SchemeDivisorPoint (Spec (.of (Plane k)))) (hd : d ≠ lineDivisor k) :
    ((schemeMap k p).stalkMap d.1).hom.FormallyEtale := by
  apply schemeMap_stalk_formallyEtale_off_line
  intro hv
  have heq := Ideal.eq_span_singleton_of_height_eq_one
    ((idealHeight_eq_coheight (.of (Plane k)) d.1).trans d.2) hv
    (MvPolynomial.X_prime (R := k) (i := (1 : Fin 2)))
  apply hd
  apply Subtype.ext
  exact PrimeSpectrum.ext heq

/-- The exact non-étale integral effective divisor locus is the invariant line.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_divisorNonEtaleLocus :
    Pcf.schemeDivisorNonEtaleLocus (schemeMap k p) = {lineDivisor k} := by
  ext d
  change (¬ ((schemeMap k p).stalkMap d.1).hom.FormallyEtale) ↔ d = lineDivisor k
  constructor
  · intro h
    by_contra hd
    exact h (divisor_stalk_formallyEtale_of_ne_line k p d hd)
  · rintro rfl
    exact schemeMap_stalk_not_formallyEtale_linePoint k p

omit [CharP k p] in
/-- The ambient map fixes the generic point of the invariant line. -/
theorem schemeMap_linePoint : schemeMap k p (linePoint k) = linePoint k := by
  apply PrimeSpectrum.ext
  exact lineIdeal_comap k p (Fact.out : p.Prime).pos

#print axioms not_isUnramifiedAt_lineIdeal
#print axioms linePoint_coheight
#print axioms schemeMap_divisorNonEtaleLocus
#print axioms schemeMap_linePoint
#print axioms schemeMap_stalk_not_formallyEtale_linePoint

end Pcf.Examples.PaperP.FrobeniusLine
