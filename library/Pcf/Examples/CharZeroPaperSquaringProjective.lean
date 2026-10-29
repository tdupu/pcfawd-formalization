/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsLines
public import Mathlib.Algebra.MvPolynomial.Expand

/-!
# Projective coordinatewise squaring, `paper.tex`, Example `ex:squaring-PN`

Projective space `ℙ^N = Proj K[x_0, …, x_N]` is modelled with the coordinate
index type `Fin N ⊕ Unit`, which has `N + 1` elements. The actual morphism
`[x_0 : ⋯ : x_N] ↦ [x_0^2 : ⋯ : x_N^2]` is constructed from the general layer
in `Pcf.PaperCharZero.SupportingProjectiveForms*`. It is finite and surjective
for every `N`, over every field.

Every coordinate hyperplane `H_i = V(x_i)` is an integral effective divisor
(a codimension-one point), invariant under the actual morphism, with
`ψ⁻¹(H_i) = H_i` as closed sets. Every diagonal hyperplane `V(x_a - x_b)`,
`a ≠ b`, in particular `D = V(x_0 - x_1)`, is an invariant integral effective
divisor different from every coordinate hyperplane. The image equalities are
equalities of actual scheme points, proved by going down for the finite
substitution; they are not statements about field-valued coordinate vectors.

The branch-locus identification, the restriction to `H_i` and the PCF
assertions are not proved here.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperSquaringProjective
open MvPolynomial AlgebraicGeometry Pcf.PaperCharZero
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- A root of `T^2 - f a` is integral along `f`. -/
theorem isIntegralElem_of_sq_eq {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {x : B} {a : A} (h : x ^ 2 = f a) : f.IsIntegralElem x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a,
    Polynomial.monic_X_pow_sub_C a two_ne_zero, ?_⟩
  simp [Polynomial.eval₂_sub, h]

/-- The homogeneous squaring forms `x_i ↦ x_i^2`. -/
noncomputable def squaringForms : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K :=
  fun i => X i ^ 2

theorem squaringForms_isHomogeneous (i : Fin n ⊕ Unit) :
    (squaringForms (K := K) i).IsHomogeneous 2 := by
  unfold squaringForms
  simpa using (isHomogeneous_X K i).pow 2

theorem squaringForms_cover : FormsCoverProjective (squaringForms (K := K) (n := n)) :=
  projCoordinatePowers_cover 2

/-- The actual projective scheme endomorphism `ψ` of `ℙ^N` in
`ex:squaring-PN`. -/
noncomputable def squaringMap :
    AlgebraicGeometry.Proj polyGrade ⟶ AlgebraicGeometry.Proj polyGrade :=
  projFormsProjectiveSchemeMap squaringForms 2 two_pos squaringForms_isHomogeneous
    squaringForms_cover

/-- `ex:squaring-PN`, first clause: `ψ` is a finite surjective endomorphism of
projective space, in every dimension. -/
theorem squaringMap_isFinite_surjective :
    IsFinite (squaringMap (K := K) (n := n)) ∧
      Function.Surjective (squaringMap (K := K) (n := n)) :=
  projFormsProjective_isFinite_surjective _ _ _ _ _

instance squaringMap_isFinite : IsFinite (squaringMap (K := K) (n := n)) :=
  (squaringMap_isFinite_surjective).1

/-- Substitution of the squares is the expansion map, hence injective. -/
theorem squaringForms_aeval_injective :
    Function.Injective (aeval (R := K) (squaringForms (K := K) (n := n))) := by
  have h : aeval (R := K) (squaringForms (K := K) (n := n)) = expand 2 := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [squaringForms, expand]
  rw [h]
  exact expand_injective two_pos

/-- Every polynomial is integral over its square substitution. -/
theorem squaringForms_aeval_isIntegral :
    (aeval (R := K) (squaringForms (K := K) (n := n))).toRingHom.IsIntegral :=
  aeval_isIntegral_of_X _ fun i =>
    isIntegralElem_of_sq_eq _ (a := X i) (by simp [squaringForms])

/-- A coordinate different from a given one, which exists since `N ≥ 1`. -/
def otherIndex [NeZero n] : Fin n ⊕ Unit → Fin n ⊕ Unit
  | Sum.inl _ => Sum.inr ()
  | Sum.inr _ => Sum.inl 0

theorem otherIndex_ne [NeZero n] (i : Fin n ⊕ Unit) : otherIndex i ≠ i := by
  cases i <;> simp [otherIndex]

theorem X_not_mem_span_X {i j : Fin n ⊕ Unit} (hij : j ≠ i) :
    (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {X i} :=
  not_mem_span_of_eval (Pi.single j 1) (by simp [hij.symm])
    (by simp)

/-- The coordinate hyperplane `H_i = V(x_i)`, as a projective point. -/
noncomputable def hyperplane [NeZero n] (i : Fin n ⊕ Unit) : AlgebraicGeometry.Proj polyGrade :=
  projLinePoint (X i) (isHomogeneous_X K i) (X_ne_zero i) (otherIndex i)
    (X_not_mem_span_X (otherIndex_ne i))

/-- `H_i` is an integral effective divisor: a codimension-one point. -/
theorem hyperplane_coheight [NeZero n] (i : Fin n ⊕ Unit) :
    Order.coheight (hyperplane (K := K) i) = 1 :=
  projLinePoint_coheight _ _ _ _ _

/-- The support of `H_i` is the zero locus of `x_i`. -/
theorem hyperplane_closure [NeZero n] (i : Fin n ⊕ Unit) :
    closure ({hyperplane (K := K) i} : Set (AlgebraicGeometry.Proj polyGrade)) =
      ProjectiveSpectrum.zeroLocus polyGrade {X i} :=
  projLinePoint_closure _ _ _ _ _

/-- The coordinate hyperplanes are pairwise distinct. -/
theorem hyperplane_injective [NeZero n] :
    Function.Injective (hyperplane (K := K) (n := n)) := by
  intro i j h
  by_contra hij
  exact projLinePoint_ne_of_eval _ _ _ _ _ _ _ _ _ _ (Pi.single j 1)
    (by simp [hij]) (by simp) h

/-- `ex:squaring-PN`: each coordinate hyperplane is invariant, `ψ(H_i) = H_i`,
as actual scheme points. -/
theorem squaringMap_hyperplane [NeZero n] (i : Fin n ⊕ Unit) :
    squaringMap (hyperplane (K := K) i) = hyperplane i :=
  projFormsProjectiveSchemeMap_projLinePoint _ _ _ _ _
    squaringForms_aeval_injective squaringForms_aeval_isIntegral
    _ _ _ _ _ _ _ _ _ _
    (Ideal.mem_span_singleton.mpr ⟨X i, by simp [squaringForms, sq]⟩)

/-- The set-theoretic inverse image of the coordinate hyperplane is itself:
`ψ⁻¹(V(x_i)) = V(x_i)`. -/
theorem squaringMap_preimage_hyperplane (i : Fin n ⊕ Unit) :
    (squaringMap (K := K) (n := n)) ⁻¹' ProjectiveSpectrum.zeroLocus polyGrade {X i} =
      ProjectiveSpectrum.zeroLocus polyGrade {X i} := by
  rw [squaringMap, projFormsProjectiveSchemeMap_preimage_zeroLocus, Set.image_singleton]
  ext x
  simp only [ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
  simp only [aeval_X, squaringForms]
  exact ⟨fun h => x.isPrime.mem_of_pow_mem 2 h,
    fun h => x.asHomogeneousIdeal.toIdeal.pow_mem_of_mem h 2 two_pos⟩

/-- The iterates fix every coordinate hyperplane. -/
theorem squaringMap_iterate_hyperplane [NeZero n] (i : Fin n ⊕ Unit) (m : ℕ) :
    (⇑(squaringMap (K := K) (n := n)))^[m] (hyperplane i) = hyperplane i :=
  Function.iterate_fixed (squaringMap_hyperplane i) m

/-- A vector on the diagonal hyperplane `x_a = x_b` with `x_a ≠ 0`. -/
def diagonalVector (a b : Fin n ⊕ Unit) : Fin n ⊕ Unit → K :=
  fun k => if k = a ∨ k = b then 1 else 0

theorem diagonalForm_isHomogeneous (a b : Fin n ⊕ Unit) :
    (X a - X b : MvPolynomial (Fin n ⊕ Unit) K).IsHomogeneous 1 :=
  (isHomogeneous_X K a).sub (isHomogeneous_X K b)

theorem diagonalForm_ne_zero {a b : Fin n ⊕ Unit} (hab : a ≠ b) :
    (X a - X b : MvPolynomial (Fin n ⊕ Unit) K) ≠ 0 := by
  intro h
  have := congrArg (eval (Pi.single a (1 : K))) h
  simp [hab.symm] at this

theorem X_not_mem_span_diagonalForm (a b : Fin n ⊕ Unit) :
    (X a : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {X a - X b} :=
  not_mem_span_of_eval (diagonalVector a b) (by simp [diagonalVector]) (by simp [diagonalVector])

/-- The diagonal hyperplane `V(x_a - x_b)`, as a projective point. For
`a = x_0`, `b = x_1` this is the divisor `D` of `ex:squaring-PN`. -/
noncomputable def diagonal {a b : Fin n ⊕ Unit} (hab : a ≠ b) : AlgebraicGeometry.Proj polyGrade :=
  projLinePoint (X a - X b) (diagonalForm_isHomogeneous a b) (diagonalForm_ne_zero hab) a
    (X_not_mem_span_diagonalForm a b)

/-- The diagonal hyperplane is an integral effective divisor. -/
theorem diagonal_coheight {a b : Fin n ⊕ Unit} (hab : a ≠ b) :
    Order.coheight (diagonal (K := K) hab) = 1 :=
  projLinePoint_coheight _ _ _ _ _

/-- The support of the diagonal divisor is `V(x_a - x_b)`. -/
theorem diagonal_closure {a b : Fin n ⊕ Unit} (hab : a ≠ b) :
    closure ({diagonal (K := K) hab} : Set (AlgebraicGeometry.Proj polyGrade)) =
      ProjectiveSpectrum.zeroLocus polyGrade {X a - X b} :=
  projLinePoint_closure _ _ _ _ _

/-- `ex:squaring-PN`: `D` is invariant. The divisibility is
`x_a^2 - x_b^2 = (x_a - x_b)(x_a + x_b)`; the equality of image divisors uses
the finite substitution, not divisibility alone. -/
theorem squaringMap_diagonal {a b : Fin n ⊕ Unit} (hab : a ≠ b) :
    squaringMap (diagonal (K := K) hab) = diagonal hab :=
  projFormsProjectiveSchemeMap_projLinePoint _ _ _ _ _
    squaringForms_aeval_injective squaringForms_aeval_isIntegral
    _ _ _ _ _ _ _ _ _ _
    (Ideal.mem_span_singleton'.mpr ⟨X a + X b, by simp [squaringForms]; ring⟩)

/-- The iterates fix the diagonal divisor: it is periodic of period one. -/
theorem squaringMap_iterate_diagonal {a b : Fin n ⊕ Unit} (hab : a ≠ b) (m : ℕ) :
    (⇑(squaringMap (K := K) (n := n)))^[m] (diagonal hab) = diagonal hab :=
  Function.iterate_fixed (squaringMap_diagonal hab) m

/-- `D` is not a coordinate hyperplane. -/
theorem diagonal_ne_hyperplane [NeZero n] {a b : Fin n ⊕ Unit} (hab : a ≠ b)
    (i : Fin n ⊕ Unit) : diagonal (K := K) hab ≠ hyperplane i :=
  projLinePoint_ne_of_eval _ _ _ _ _ _ _ _ _ _ (fun _ => 1) (by simp) (by simp)

#print axioms isIntegralElem_of_sq_eq
#print axioms squaringMap
#print axioms squaringMap_isFinite_surjective
#print axioms squaringForms_aeval_injective
#print axioms squaringForms_aeval_isIntegral
#print axioms hyperplane_coheight
#print axioms hyperplane_closure
#print axioms hyperplane_injective
#print axioms squaringMap_hyperplane
#print axioms squaringMap_preimage_hyperplane
#print axioms squaringMap_iterate_hyperplane
#print axioms diagonal_coheight
#print axioms diagonal_closure
#print axioms squaringMap_diagonal
#print axioms squaringMap_iterate_diagonal
#print axioms diagonal_ne_hyperplane
end Pcf.Examples.CharZeroPaperSquaringProjective
