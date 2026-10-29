/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsCritical
public import Pcf.Examples.CharZeroPaperSquaringProjective

/-!
# Branch locus and PCF of projective squaring, `paper.tex`, `ex:squaring-PN`

For the actual squaring endomorphism `ψ` of `ℙ^N` over a field of
characteristic zero:

* the Jacobian determinant is `∏ 2 x_i`;
* the normalized critical divisors and the normalized branch divisors
  (`def:crit-branch`, computed on the actual canonical normalization) are
  exactly the coordinate hyperplanes `H_i`;
* the actual ramification index exceeds one along each `H_i` and is one along
  every other integral effective divisor, and `ψ` is étale on a neighbourhood of
  every point off `⋃ H_i`;
* the postcritical set is `{H_0, …, H_N}`, so `ψ` is PCF;
* no diagonal hyperplane `V(x_a - x_b)`, in particular `D`, is a normalized branch
  divisor of any iterate `ψ^m`, although it is invariant.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperSquaringBranch
open MvPolynomial AlgebraicGeometry CategoryTheory Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

instance squaringMap_isDominant : IsDominant (squaringMap (K := K) (n := n)) :=
  projFormsProjective_isDominant _ _ _ _ _

instance squaringMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (squaringMap (K := K) (n := n)) :=
  projFormsProjectiveSchemeMap_locallyOfFinitePresentation _ _ _ _ _

/-- The Jacobian determinant of coordinatewise squaring. -/
theorem squaringForms_jacobian :
    Matrix.det (fun i j => pderiv j (squaringForms (K := K) (n := n) i)) =
      ∏ i, 2 * X i := by
  classical
  have h : (fun i j => pderiv j (squaringForms (K := K) (n := n) i)) =
      Matrix.diagonal (fun i => (2 : MvPolynomial (Fin n ⊕ Unit) K) * X i) := by
    funext i j
    by_cases hij : i = j
    · subst hij
      simp [squaringForms, pderiv_X]
    · simp [squaringForms, pderiv_X, hij]
  rw [h, Matrix.det_diagonal]

/-- The Jacobian determinant lies in a homogeneous prime exactly when some
coordinate does. -/
theorem squaringForms_jacobian_mem_iff [CharZero K] (x : AlgebraicGeometry.Proj polyGrade) :
    Matrix.det (fun i j => pderiv j (squaringForms (K := K) (n := n) i)) ∈
        x.asHomogeneousIdeal ↔
      ∃ i, (X i : MvPolynomial (Fin n ⊕ Unit) K) ∈ x.asHomogeneousIdeal := by
  have hp : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have h2 : (2 : MvPolynomial (Fin n ⊕ Unit) K) ∉ x.asHomogeneousIdeal.toIdeal := by
    intro h
    have hu : IsUnit (2 : MvPolynomial (Fin n ⊕ Unit) K) := by
      rw [show (2 : MvPolynomial (Fin n ⊕ Unit) K) = C 2 from (map_ofNat C 2).symm]
      exact (Ne.isUnit (two_ne_zero : (2 : K) ≠ 0)).map C
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  rw [squaringForms_jacobian]
  change _ ∈ x.asHomogeneousIdeal.toIdeal ↔ ∃ i, _ ∈ x.asHomogeneousIdeal.toIdeal
  rw [hp.prod_mem_iff]
  simp only [Finset.mem_univ, true_and]
  exact exists_congr fun i => ⟨fun h => (hp.mem_or_mem h).resolve_left h2,
    fun h => Ideal.mul_mem_left _ _ h⟩

/-- The coordinate hyperplane `H_i` as an integral effective divisor. -/
noncomputable def hyperplaneDivisor [NeZero n] (i : Fin n ⊕ Unit) :
    SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade) :=
  ⟨hyperplane (K := K) i, hyperplane_coheight i⟩

theorem hyperplaneDivisor_injective [NeZero n] :
    Function.Injective (hyperplaneDivisor (K := K) (n := n)) := fun _ _ h =>
  hyperplane_injective (congrArg Subtype.val h)

/-- A divisor contains `x_i` exactly when it is `H_i`. -/
theorem divisor_X_mem_iff [NeZero n] (P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade))
    (i : Fin n ⊕ Unit) :
    (X i : MvPolynomial (Fin n ⊕ Unit) K) ∈ P.1.asHomogeneousIdeal ↔ P = hyperplaneDivisor i :=
  proj_divisor_mem_iff_eq_projLinePoint _ _ _ _ _ P

/-- `ex:squaring-PN`: the normalized critical divisors are exactly the `H_i`. -/
theorem squaringMap_criticalDivisors [CharZero K] [NeZero n] :
    schemeNormalizedCriticalDivisors K (squaringMap (K := K) (n := n)) =
      Set.range hyperplaneDivisor := by
  ext P
  unfold squaringMap
  rw [projForms_mem_criticalDivisors_iff, squaringForms_jacobian_mem_iff]
  simp only [divisor_X_mem_iff, Set.mem_range]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

/-- `ψ` maps each `H_i` divisor to itself. -/
theorem squaringMap_divisorMap_hyperplane [CharZero K] [NeZero n] (i : Fin n ⊕ Unit) :
    schemeDivisorMap (squaringMap (K := K) (n := n))
        (coheight_apply_eq_one_of_finiteType _ K) (hyperplaneDivisor i) =
      hyperplaneDivisor i :=
  Subtype.ext (squaringMap_hyperplane i)

/-- `ex:squaring-PN`: the normalized branch divisors are exactly the `H_i`. -/
theorem squaringMap_branch [CharZero K] [NeZero n] :
    schemeNormalizedBranch K (squaringMap (K := K) (n := n)) = Set.range hyperplaneDivisor := by
  ext E
  have hiff := projForms_mem_branch_iff squaringForms 2 two_pos squaringForms_isHomogeneous
    squaringForms_cover E
  refine hiff.trans ?_
  simp only [squaringForms_jacobian_mem_iff, divisor_X_mem_iff, Set.mem_range]
  constructor
  · rintro ⟨P, hPE, i, rfl⟩
    exact ⟨i, Subtype.ext ((squaringMap_hyperplane i).symm.trans hPE)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨hyperplaneDivisor i, squaringMap_hyperplane i, i, rfl⟩

/-- `ex:squaring-PN`: the actual ramification index exceeds one along each `H_i`. -/
theorem squaringMap_ramified [CharZero K] [NeZero n] (i : Fin n ⊕ Unit) :
    1 < schemeDivisorRamificationIdx (squaringMap (K := K) (n := n)) (hyperplaneDivisor i) := by
  unfold squaringMap
  rw [projForms_one_lt_ramificationIdx_iff, squaringForms_jacobian_mem_iff]
  exact ⟨i, (divisor_X_mem_iff _ i).mpr rfl⟩

/-- `ex:squaring-PN`: the actual ramification index is one along every other
integral effective divisor. -/
theorem squaringMap_unramified [CharZero K] [NeZero n]
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade))
    (hP : ∀ i, P ≠ hyperplaneDivisor i) :
    schemeDivisorRamificationIdx (squaringMap (K := K) (n := n)) P = 1 := by
  unfold squaringMap
  rw [projForms_ramificationIdx_eq_one_iff, squaringForms_jacobian_mem_iff]
  rintro ⟨i, hi⟩
  exact hP i ((divisor_X_mem_iff P i).mp hi)

/-- `ex:squaring-PN`: `ψ` is étale on a neighbourhood of every point off the
union of the coordinate hyperplanes. -/
theorem squaringMap_etale_off_hyperplanes [CharZero K] (x : AlgebraicGeometry.Proj polyGrade)
    (hx : ∀ i, (X i : MvPolynomial (Fin n ⊕ Unit) K) ∉ x.asHomogeneousIdeal) :
    ((squaringMap (K := K) (n := n)).stalkMap x).hom.FormallyEtale ∧
      ∃ U : (AlgebraicGeometry.Proj polyGrade).Opens, x ∈ U ∧
        Etale (U.ι ≫ squaringMap (K := K) (n := n)) := by
  have hdet : Matrix.det (fun i j => pderiv j (squaringForms (K := K) (n := n) i)) ∉
      x.asHomogeneousIdeal := by
    rw [squaringForms_jacobian_mem_iff]
    rintro ⟨i, hi⟩
    exact hx i hi
  exact ⟨(projForms_stalk_formallyEtale_iff _ _ _ _ _ x).mpr hdet,
    projForms_etale_neighborhood _ _ _ _ _ x hdet⟩

/-- `ex:squaring-PN`: the postcritical set is `{H_0, …, H_N}`. -/
theorem squaringMap_postcritical [CharZero K] [NeZero n] :
    schemeNormalizedPostcriticalSet K (squaringMap (K := K) (n := n)) =
      Set.range hyperplaneDivisor := by
  rw [schemeNormalizedPostcriticalSet_eq_iUnion, squaringMap_branch]
  ext E
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨m, _, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (Function.iterate_fixed (squaringMap_divisorMap_hyperplane i) m).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨0, _, ⟨i, rfl⟩, rfl⟩

/-- `ex:squaring-PN`: `ψ` is PCF for the paper's normalized branch locus. -/
theorem squaringMap_isPCF [CharZero K] [NeZero n] :
    IsNormalizedPCF K (squaringMap (K := K) (n := n)) := by
  unfold IsNormalizedPCF
  rw [squaringMap_postcritical]
  exact Set.finite_range _

/-- `ex:squaring-PN`: every normalized branch divisor of every iterate `ψ^m` is
a coordinate hyperplane. -/
theorem squaringMap_pow_branch_subset [CharZero K] [NeZero n] (m : ℕ) :
    schemeNormalizedBranch K (End.of (squaringMap (K := K) (n := n)) ^ m).asHom ⊆
      Set.range hyperplaneDivisor := by
  rw [normalized_branch_divisors_pow K, squaringMap_branch]
  intro E hE
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range] at hE
  obtain ⟨i, -, _, ⟨j, rfl⟩, rfl⟩ := hE
  exact ⟨j, (Function.iterate_fixed (squaringMap_divisorMap_hyperplane j) i).symm⟩

/-- The diagonal hyperplane `V(x_a - x_b)` as an integral effective divisor. -/
noncomputable def diagonalDivisor {a b : Fin n ⊕ Unit} (hab : a ≠ b) :
    SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade) :=
  ⟨diagonal (K := K) hab, diagonal_coheight hab⟩

/-- `ex:squaring-PN`: `D` is invariant under `ψ`. -/
theorem squaringMap_divisorMap_diagonal [CharZero K] {a b : Fin n ⊕ Unit} (hab : a ≠ b) :
    schemeDivisorMap (squaringMap (K := K) (n := n))
        (coheight_apply_eq_one_of_finiteType _ K) (diagonalDivisor hab) = diagonalDivisor hab :=
  Subtype.ext (squaringMap_diagonal hab)

/-- `ex:squaring-PN`: the invariant divisor `D = V(x_a - x_b)` is not a
normalized branch divisor of any iterate `ψ^m`; periodic integral effective
divisors need not be postcritical. -/
theorem diagonal_not_mem_branch_pow [CharZero K] [NeZero n] {a b : Fin n ⊕ Unit}
    (hab : a ≠ b) (m : ℕ) :
    diagonalDivisor (K := K) hab ∉
      schemeNormalizedBranch K (End.of (squaringMap (K := K) (n := n)) ^ m).asHom := by
  intro h
  obtain ⟨i, hi⟩ := squaringMap_pow_branch_subset m h
  exact diagonal_ne_hyperplane hab i (congrArg Subtype.val hi).symm

/-- `ex:squaring-PN`: `D` is not in the postcritical set. -/
theorem diagonal_not_mem_postcritical [CharZero K] [NeZero n] {a b : Fin n ⊕ Unit}
    (hab : a ≠ b) :
    diagonalDivisor (K := K) hab ∉
      schemeNormalizedPostcriticalSet K (squaringMap (K := K) (n := n)) := by
  rw [squaringMap_postcritical]
  rintro ⟨i, hi⟩
  exact diagonal_ne_hyperplane hab i (congrArg Subtype.val hi).symm

#print axioms squaringForms_jacobian
#print axioms squaringForms_jacobian_mem_iff
#print axioms divisor_X_mem_iff
#print axioms squaringMap_criticalDivisors
#print axioms squaringMap_branch
#print axioms squaringMap_ramified
#print axioms squaringMap_unramified
#print axioms squaringMap_etale_off_hyperplanes
#print axioms squaringMap_postcritical
#print axioms squaringMap_isPCF
#print axioms squaringMap_pow_branch_subset
#print axioms squaringMap_divisorMap_diagonal
#print axioms diagonal_not_mem_branch_pow
#print axioms diagonal_not_mem_postcritical
end Pcf.Examples.CharZeroPaperSquaringBranch
