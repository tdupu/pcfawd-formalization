/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSingularImageGeometry
public import Pcf.Examples.CharZeroPaperSmoothBranch

/-!
# `branch(f) = B` for the normalized branch locus, `ex:branch-sing-B` in `paper.tex`

`CharZeroPaperSingularImageGeometry.planeMap_reducedFiberBranch` identifies the
reduced-fibre branch divisors of `f = (F, G) : 𝔸² → 𝔸²` with `{B}`. Since source and
target are normal, the canonical normalized branch support of `f` (the branch locus of
Definition `def:crit-branch`) is the support of the reduced-fibre branch divisors
(`CharZeroPaperSmoothBranch.normalized_support_eq_reduced_support`). Hence the
normalized branch locus of `f` is exactly the closure of the generic point of `B`,
which is the zero locus of `U³ - 12aV²`.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperSingularImageNormalizedBranch

open CategoryTheory AlgebraicGeometry MvPolynomial
open Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSingularImage
open Pcf.Examples.CharZeroPaperSingularImageGeometry

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- `ex:branch-sing-B`: the normalized branch locus of `f = (F, G)` is `B`: it equals the
support of the single divisor `B`, i.e. the closure of the generic point of `B`, i.e. the
zero locus `V(U³ - 12aV²)`.

Manuscript: `ex:branch-sing-B` (Example 6.8). -/
theorem planeMap_normalizedBranch (a : K) (ha : a ^ 2 = -3) :
    haveI := planeMap_isFinite a ha
    haveI := planeMap_surjective a ha
    normalizedMorphismBranchSupport (planeMap a) = divisorSupport {bDivisorPoint a ha} ∧
      normalizedMorphismBranchSupport (planeMap a) =
        closure ({(bDivisorPoint a ha).1} : Set (plane K)) ∧
      normalizedMorphismBranchSupport (planeMap a) =
        PrimeSpectrum.zeroLocus {cuspEquation a} := by
  have := planeMap_isFinite a ha
  have := planeMap_surjective a ha
  have h : normalizedMorphismBranchSupport (planeMap a) = divisorSupport {bDivisorPoint a ha} := by
    rw [CharZeroPaperSmoothBranch.normalized_support_eq_reduced_support,
      planeMap_reducedFiberBranch a ha]
  have hc : normalizedMorphismBranchSupport (planeMap a) =
      closure ({(bDivisorPoint a ha).1} : Set (plane K)) := by
    rw [h]
    simp [divisorSupport]
  refine ⟨h, hc, ?_⟩
  rw [hc]
  change closure ({(⟨bIdeal a, bIdeal_isPrime a ha⟩ : PrimeSpectrum (MvPolynomial (Fin 2) K))} :
    Set (PrimeSpectrum (MvPolynomial (Fin 2) K))) = _
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_span _

end Pcf.Examples.CharZeroPaperSingularImageNormalizedBranch

#print axioms Pcf.Examples.CharZeroPaperSingularImageNormalizedBranch.planeMap_normalizedBranch
