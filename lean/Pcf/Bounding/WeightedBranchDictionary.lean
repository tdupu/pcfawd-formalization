/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TameChart
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The local branch dictionary with separable residue fields

In characteristic `p`, ramification index one alone does not imply
étaleness. The paper's weighted branch multiplicity also records the
inseparable residue degree. This file derives the local implication from
index one plus separable residue field extension to unramifiedness, using
the actual local rings at a prime.
-/

@[expose] public section

namespace Pcf

universe u v

set_option linter.style.haveILetI false

/-- The paper's weighted local branch multiplicity `δ=e f_{insep}` at an
actual prime of a finite cover. The residue-field algebra is induced by the
map of local rings. -/
noncomputable def weightedDivisorMultiplicity
    (R : Type u) {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] : ℕ :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  q.ramificationIdx R *
    Field.finInsepDegree (q.under R).ResidueField q.ResidueField

/-- Weighted multiplicity one forces both index one and separability of the
residue extension. This retains the residue condition that index-only
branch predicates miss in characteristic `p`. -/
theorem weightedDivisorMultiplicity_eq_one_iff
    (R : Type u) {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    weightedDivisorMultiplicity R q = 1 ↔
      q.ramificationIdx R = 1 ∧
        Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := by
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  unfold weightedDivisorMultiplicity
  rw [mul_eq_one]
  exact and_congr_right fun _ =>
    (isSeparable_iff_finInsepDegree_eq_one _ _).symm

/-- A prime with ramification index one and separable residue extension is
unramified. Unlike the characteristic-zero dictionary, the separability
premise is explicit and applies in every characteristic. This is the local
content of `paper-p.tex`, Lemma `lem:dictionary`. -/
theorem isUnramifiedAt_of_index_one_and_residueSeparable
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S]
    (q : Ideal S) [q.IsPrime]
    (he : q.ramificationIdx R = 1)
    (hsep : letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField) :
    Algebra.IsUnramifiedAt R q := by
  let p := q.under R
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : Algebra.IsSeparable p.ResidueField q.ResidueField := hsep
  have hmap : p.map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast,
      Nat.cast_one, Module.length_eq_one_iff,
      isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff] at he
    exact he
  exact (Algebra.isUnramifiedAt_iff_map_eq R p q).mpr ⟨hsep, hmap⟩

/-- On an essentially finite-type cover, the weighted branch multiplicity
is one exactly at the unramified primes. This is the local numerical
dictionary in `paper-p.tex` in arbitrary characteristic. -/
theorem isUnramifiedAt_iff_weightedDivisorMultiplicity_eq_one
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q ↔
      weightedDivisorMultiplicity R q = 1 := by
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  constructor
  · intro hu
    letI : Algebra.IsUnramifiedAt R q := hu
    apply (weightedDivisorMultiplicity_eq_one_iff R q).2
    exact ⟨Ideal.ramificationIdx_eq_one q R, inferInstance⟩
  · intro hδ
    obtain ⟨he, hs⟩ := (weightedDivisorMultiplicity_eq_one_iff R q).1 hδ
    exact isUnramifiedAt_of_index_one_and_residueSeparable q he hs

/-- For a finite-presentation flat cover, the paper's weighted branch
multiplicity detects the actual étale locus. In the divisorial application
flatness follows from torsion freeness over the normal target DVR. -/
theorem isEtaleAt_iff_weightedDivisorMultiplicity_eq_one
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsEtaleAt R q ↔
      weightedDivisorMultiplicity R q = 1 := by
  constructor
  · intro he
    letI : Algebra.IsEtaleAt R q := he
    exact (isUnramifiedAt_iff_weightedDivisorMultiplicity_eq_one q).mp inferInstance
  · intro hδ
    letI : Algebra.IsUnramifiedAt R q :=
      (isUnramifiedAt_iff_weightedDivisorMultiplicity_eq_one q).mpr hδ
    exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q

/-- For a finite faithful domain cover of a Dedekind base, flatness and
finite presentation follow from the actual ring extension. Thus the
weighted local multiplicity detects étaleness without assuming either
geometric property separately. This is the divisor-DVR situation used in
`paper-p.tex`, Lemma `lem:dictionary`. -/
theorem finiteDedekind_isEtaleAt_iff_weightedDivisorMultiplicity_eq_one
    (R : Type u) {S : Type v}
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsEtaleAt R q ↔
      weightedDivisorMultiplicity R q = 1 := by
  letI : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Module.IsTorsionFree R S := Module.IsTorsionFree.of_smul_eq_zero (by
    intro r s hs
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have hr' : algebraMap R S r ≠ 0 :=
        by simpa using (FaithfulSMul.algebraMap_injective R S).ne hr
      exact (mul_eq_zero.mp (show algebraMap R S r * s = 0 by
        simpa [Algebra.smul_def] using hs)).resolve_left hr')
  letI : Module.Flat R S := inferInstance
  exact isEtaleAt_iff_weightedDivisorMultiplicity_eq_one q

#print axioms weightedDivisorMultiplicity
#print axioms weightedDivisorMultiplicity_eq_one_iff
#print axioms isUnramifiedAt_of_index_one_and_residueSeparable
#print axioms isUnramifiedAt_iff_weightedDivisorMultiplicity_eq_one
#print axioms isEtaleAt_iff_weightedDivisorMultiplicity_eq_one
#print axioms finiteDedekind_isEtaleAt_iff_weightedDivisorMultiplicity_eq_one

end Pcf
