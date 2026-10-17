/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.KummerClauses
public import Pcf.Stacks.Abhyankar.TameRamification
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The tame half of clause (6) of Stacks Tag 09EV

The first assertion of clause (6) says that the standard root extension is tamely ramified
when `n` is invertible in the residue field.  This file proves that assertion for the honest
primewise predicate `IsTamelyRamifiedAt`.

The intermediate-field classification in the second assertion of clause (6) is not claimed
here.  Its remaining Stacks input is Tag `0EXP`, together with the root-of-unity descent
specific to the Eisenstein root extension.
-/

@[expose] public section

open Polynomial IsLocalRing

universe u v

namespace Pcf.Stacks

/-- A field extension of degree one is separable. -/
theorem isSeparable_of_finrank_eq_one
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L = 1) : Algebra.IsSeparable K L := by
  have hb : Function.Bijective (algebraMap K L) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (Algebra.ofId K L) hb
  apply Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl K) e.toRingEquiv
  ext x
  simp [e]

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The tame assertion in clause (6) of Stacks Tag `09EV`: if `n` is invertible in the
residue field of the DVR, then the unique root prime is tamely ramified. -/
theorem dvrRootExtension_isTamelyRamifiedAt (π : A) {n : ℕ} (hn : 2 ≤ n)
    (hπ : Irreducible π)
    (hunit :
      let qIdeal : Ideal (AdjoinRoot (dvrRootPoly π n)) :=
        Ideal.span {AdjoinRoot.root (dvrRootPoly π n)}
      letI : qIdeal.IsPrime := (dvrRootIdeal_isMaximal π (by omega) hπ).isPrime
      IsUnit ((n : ℕ) : (qIdeal.under A).ResidueField)) :
    let q : PrimeSpectrum (AdjoinRoot (dvrRootPoly π n)) :=
      ⟨Ideal.span {AdjoinRoot.root (dvrRootPoly π n)},
        (dvrRootIdeal_isMaximal π (by omega) hπ).isPrime⟩
    IsTamelyRamifiedAt A (AdjoinRoot (dvrRootPoly π n)) q := by
  let hn1 : 1 ≤ n := by omega
  let qIdeal : Ideal (AdjoinRoot (dvrRootPoly π n)) :=
    Ideal.span {AdjoinRoot.root (dvrRootPoly π n)}
  let q : PrimeSpectrum (AdjoinRoot (dvrRootPoly π n)) :=
    ⟨qIdeal, (dvrRootIdeal_isMaximal π hn1 hπ).isPrime⟩
  letI : qIdeal.IsPrime := (dvrRootIdeal_isMaximal π hn1 hπ).isPrime
  letI : (qIdeal.under A).IsPrime := inferInstance
  change
    let p := qIdeal.under A
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime qIdeal) :=
      Localization.AtPrime.algebraOfLiesOver p qIdeal
    IsUnit ((qIdeal.ramificationIdx A : ℕ) : p.ResidueField) ∧
      Algebra.IsSeparable p.ResidueField qIdeal.ResidueField
  dsimp only
  letI : Algebra (Localization.AtPrime (qIdeal.under A))
      (Localization.AtPrime qIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (qIdeal.under A) qIdeal
  constructor
  · rw [dvrRootIdeal_ramificationIdx π hn1 hπ]
    exact hunit
  · apply isSeparable_of_finrank_eq_one
    rw [← Ideal.inertiaDeg_def qIdeal A]
    exact dvrRootIdeal_inertiaDeg π hn1 hπ

#print axioms isSeparable_of_finrank_eq_one
#print axioms dvrRootExtension_isTamelyRamifiedAt

end Pcf.Stacks
