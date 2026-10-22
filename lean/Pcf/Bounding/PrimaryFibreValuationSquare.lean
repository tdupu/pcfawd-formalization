/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryFibres
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Valuation multiplicities in the purely inseparable comparison square

The proof of `latex/paper-p.tex`, Lemma `lem:primary-fibres`, compares
the two paths around a square of normalizations. The identity is the
ramification-index tower law applied to both paths. It forces the
original fibre multiplicity to divide the purely inseparable base
degree once the altered fibre is generically reduced.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

universe u v w x

/-- The two paths around an actual commutative algebra square have the
same total ramification index at a prime. -/
theorem ramificationIdx_square
    {R : Type u} {S : Type v} {Rp : Type w} {T : Type x}
    [CommRing R] [CommRing S] [CommRing Rp] [CommRing T]
    [Algebra R S] [Algebra R Rp] [Algebra S T] [Algebra Rp T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R Rp T]
    [Module.Flat S T] [Module.Flat Rp T]
    (P : Ideal S) (Q : Ideal Rp) (E : Ideal T)
    [E.LiesOver P] [E.LiesOver Q] :
    P.ramificationIdx R * E.ramificationIdx S =
      Q.ramificationIdx R * E.ramificationIdx Rp := by
  exact (Ideal.ramificationIdx_tower (R := R) P E).symm.trans
    (Ideal.ramificationIdx_tower (R := R) Q E)

/-- If the altered fibre has multiplicity one and the purely
inseparable base normalization has index dividing `p^a`, the original fibre
multiplicity is a bounded power of `p`. The geometric argument must
still supply these two hypotheses uniformly on a dense open. -/
theorem ramificationIdx_is_prime_power_of_square
    {R : Type u} {S : Type v} {Rp : Type w} {T : Type x}
    [CommRing R] [CommRing S] [CommRing Rp] [CommRing T]
    [Algebra R S] [Algebra R Rp] [Algebra S T] [Algebra Rp T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R Rp T]
    [Module.Flat S T] [Module.Flat Rp T]
    (P : Ideal S) (Q : Ideal Rp) (E : Ideal T)
    [E.LiesOver P] [E.LiesOver Q]
    (p a : ℕ) (hp : p.Prime)
    (hbase : Q.ramificationIdx R ∣ p ^ a)
    (hreduced : E.ramificationIdx Rp = 1) :
    ∃ b ≤ a, P.ramificationIdx R = p ^ b := by
  have hsq := ramificationIdx_square (R := R) P Q E
  rw [hreduced, mul_one] at hsq
  have hdiv : P.ramificationIdx R ∣ p ^ a :=
    (show P.ramificationIdx R ∣ Q.ramificationIdx R from
      ⟨E.ramificationIdx S, hsq.symm⟩).trans hbase
  exact (Nat.dvd_prime_pow hp).mp hdiv

#print axioms ramificationIdx_square
#print axioms ramificationIdx_is_prime_power_of_square

end Pcf.Bounding.PrimaryFibres
