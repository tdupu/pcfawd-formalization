/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimeToPMonodromy

/-!
# Manuscript monodromy convention in characteristic zero

`paper-p.tex`, Definition `def:prime-to-p`, says that monodromy is not
divisible by the characteristic. In characteristic zero this is automatic
for a finite dominant map. For a positive prime characteristic the existing
Galois-closure certificate supplies precisely the required condition.

The certificate's coprimality field alone would require degree one at
`p = 0`, so the source-facing definition treats that case explicitly.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry

universe u

/-- The manuscript's monodromy condition for characteristic `p`, including
the automatic characteristic-zero case.

`paper-p.tex` correspondence: Definition 1.1 (`def:prime-to-p`). -/
def IsPaperPMonodromyNotDivisibleBy
    (p : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y] : Prop :=
  p = 0 ∨ IsPrimeToPMonodromyMap p f

/-- The manuscript convention is automatic when the characteristic is zero. -/
theorem isPaperPMonodromyNotDivisibleBy_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y] :
    IsPaperPMonodromyNotDivisibleBy 0 f :=
  Or.inl rfl

/-- In positive prime characteristic the source-facing condition is exactly
the existing finite Galois-closure certificate. -/
theorem isPaperPMonodromyNotDivisibleBy_iff_of_prime
    (p : ℕ) [Fact p.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y] :
    IsPaperPMonodromyNotDivisibleBy p f ↔
      IsPrimeToPMonodromyMap p f := by
  constructor
  · rintro (hzero | hmono)
    · exact False.elim ((Fact.out : p.Prime).ne_zero hzero)
    · exact hmono
  · exact Or.inr

/-- For prime `p`, the certificate's coprimality condition is exactly the
manuscript's assertion that `p` does not divide the closure degree. -/
theorem coprime_degree_iff_prime_not_dvd
    (p degree : ℕ) [Fact p.Prime] :
    degree.Coprime p ↔ ¬ p ∣ degree := by
  constructor
  · intro h
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp h.symm
  · intro h
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr h).symm

#print axioms isPaperPMonodromyNotDivisibleBy_zero
#print axioms isPaperPMonodromyNotDivisibleBy_iff_of_prime
#print axioms coprime_degree_iff_prime_not_dvd

end Pcf
