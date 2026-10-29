/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Pcf.PrimeToPMonodromy

/-!
# Prime-to-characteristic indices in a Galois cover

The Galois fundamental identity gives the index and inertia-degree
coprimality part of `latex/paper-p.tex`, Lemma `lem:prime-to-p-restrict`,
at the ring-theoretic level. The passage from a geometric divisor to this
Galois cover, and the residue-field Galois closure, remain separate goals.
-/

@[expose] public section

namespace Pcf

set_option linter.style.haveILetI false

/-- A finite field extension in characteristic `p` whose degree is prime to
`p` is separable. Its inseparable degree is a power of `p`, so it must be one. -/
theorem isSeparable_of_finrank_coprime_expChar
    (p : ℕ) (hp : p.Prime) (F E : Type*)
    [Field F] [Field E] [Algebra F E] [ExpChar F p]
    [FiniteDimensional F E]
    (hdegree : (Module.finrank F E).Coprime p) :
    Algebra.IsSeparable F E := by
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F E p
  have hdiv : Field.finInsepDegree F E ∣ Module.finrank F E := by
    rw [← Field.finSepDegree_mul_finInsepDegree]
    exact dvd_mul_left _ _
  have hcoprime : (p ^ n).Coprime p := by
    rw [← hn]
    exact Nat.Coprime.of_dvd_left hdiv hdegree
  have hpow : p ^ n = 1 := by
    by_contra hne
    have hn0 : n ≠ 0 := by
      intro hz
      simp [hz] at hne
    exact (hp.coprime_iff_not_dvd.mp hcoprime.symm) (dvd_pow_self p hn0)
  exact (isSeparable_iff_finInsepDegree_eq_one F E).mpr (hn.trans hpow)

/-- In a finite flat Galois extension of domains whose group order is
coprime to `q`, every ramification index and inertia degree over a prime
is coprime to `q`. -/
theorem galois_ramificationIdx_inertiaDeg_coprime
    {R S G : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (q : ℕ) (p : Ideal R) [p.IsPrime] (P : Ideal S)
    [P.IsPrime] [P.LiesOver p]
    (hgroup : (Nat.card G).Coprime q) :
    (P.ramificationIdx R).Coprime q ∧ (P.inertiaDeg R).Coprime q := by
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    p S G
  have he : Ideal.ramificationIdxIn p S ∣ Nat.card G := by
    rw [← hfund]
    refine ⟨(p.primesOver S).ncard * Ideal.inertiaDegIn p S, ?_⟩
    ac_rfl
  have hd : Ideal.inertiaDegIn p S ∣ Nat.card G := by
    rw [← hfund]
    refine ⟨(p.primesOver S).ncard * Ideal.ramificationIdxIn p S, ?_⟩
    ac_rfl
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    ← Ideal.inertiaDegIn_eq_inertiaDeg p P G]
  exact ⟨Nat.Coprime.of_dvd_left he hgroup,
    Nat.Coprime.of_dvd_left hd hgroup⟩

/-- In the same Galois situation, a residue extension in characteristic
`q` is separable when the Galois-group order is prime to `q`. -/
theorem galois_residueField_isSeparable_of_coprime
    {R S G : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (q : ℕ) (hq : q.Prime) (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [ExpChar p.ResidueField q]
    (hgroup : (Nat.card G).Coprime q) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Algebra.IsSeparable p.ResidueField P.ResidueField := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have hdegree : (Module.finrank p.ResidueField P.ResidueField).Coprime q := by
    rw [← Ideal.inertiaDeg_eq p P]
    exact (galois_ramificationIdx_inertiaDeg_coprime q p P hgroup).2
  have hpos : 0 < Module.finrank p.ResidueField P.ResidueField := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact (hq.coprime_iff_not_dvd.mp hdegree.symm) (hz ▸ dvd_zero q)
  letI : FiniteDimensional p.ResidueField P.ResidueField :=
    Module.finite_of_finrank_pos hpos
  exact isSeparable_of_finrank_coprime_expChar q hq
    p.ResidueField P.ResidueField hdegree

/-- The residue extension of the Galois cover is itself finite Galois with
degree prime to `q` in residue characteristic `q`. -/
theorem galois_residueField_isGalois_coprime
    {R S G : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (q : ℕ) (hq : q.Prime) (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    [ExpChar p.ResidueField q]
    (hgroup : (Nat.card G).Coprime q) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsGalois p.ResidueField P.ResidueField ∧
      (Module.finrank p.ResidueField P.ResidueField).Coprime q := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have hsep : Algebra.IsSeparable p.ResidueField P.ResidueField :=
    galois_residueField_isSeparable_of_coprime q hq p P hgroup
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp
      (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp
        (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  letI := ((algebraMap (S ⧸ P) P.ResidueField).comp
    (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField :=
    IsScalarTower.of_algebraMap_eq' heq
  have hnormal : Normal p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField
  constructor
  · exact isGalois_iff.mpr ⟨hsep, hnormal⟩
  · rw [← Ideal.inertiaDeg_eq p P]
    exact (galois_ramificationIdx_inertiaDeg_coprime q p P hgroup).2

/-- Specialization to an integral closure of a Dedekind domain in a
finite Galois extension. This is the local-ring calculation required
at a codimension-one divisor in `lem:prime-to-p-restrict`. -/
theorem galois_integralClosure_ramification_residue_coprime
    (q : ℕ) (hq : q.Prime)
    (R F L S : Type*) [CommRing R] [IsDedekindDomain R]
    [Field F] [Field L] [CommRing S]
    [Algebra R F] [IsFractionRing R F]
    [Algebra F L] [IsGalois F L] [FiniteDimensional F L]
    [Algebra R S] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R F L]
    [IsIntegralClosure S R L]
    (p : Ideal R) [p.IsPrime] (P : Ideal S)
    [P.IsPrime] [P.LiesOver p] [ExpChar p.ResidueField q]
    (hdegree : (Module.finrank F L).Coprime q) :
    (P.ramificationIdx R).Coprime q ∧
      (letI := Localization.AtPrime.algebraOfLiesOver p P
       IsGalois p.ResidueField P.ResidueField ∧
         (Module.finrank p.ResidueField P.ResidueField).Coprime q) := by
  letI : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain _
  letI : Module.Finite R S := IsIntegralClosure.finite R F L S
  letI : FaithfulSMul R L := .trans R F L
  letI : Module.IsTorsionFree R L := inferInstance
  letI : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L
  letI : Module.Flat R S := inferInstance
  letI : IsFractionRing S L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F L S
  letI : MulSemiringAction Gal(L/F) S :=
    IsIntegralClosure.MulSemiringAction R F L S
  letI : IsGaloisGroup Gal(L/F) R S :=
    IsGaloisGroup.of_isFractionRing Gal(L/F) R S F L
  have hcard : (Nat.card Gal(L/F)).Coprime q := by
    rwa [IsGalois.card_aut_eq_finrank F L]
  exact ⟨(galois_ramificationIdx_inertiaDeg_coprime q p P hcard).1,
    galois_residueField_isGalois_coprime q hq p P hcard⟩

#print axioms isSeparable_of_finrank_coprime_expChar
#print axioms galois_ramificationIdx_inertiaDeg_coprime
#print axioms galois_residueField_isSeparable_of_coprime
#print axioms galois_residueField_isGalois_coprime
#print axioms galois_integralClosure_ramification_residue_coprime

end Pcf
