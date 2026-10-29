/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaAffine
public import Mathlib.Algebra.MvPolynomial.Expand
public import Pcf.Bounding.PaperPJacobianProjectiveChartMap
/-!
# The global projective basilica scheme morphism

For `latex/paper-p.tex`, Example `ex:basilica`, the homogeneous forms
`[x₀²-x₁²:x₁²]` have no common projective zero and define an actual global
scheme morphism of the projective line. Rational projective scheme points
are represented by homogeneous prime ideals, rather than by the separate
linear-algebraic projectivization quotient. The scheme map has the expected
coordinate formula, `0 ↔ -1`, and a fixed infinity point.

The positive orbit of the two critical candidates is the three-point set.
Their identification with the global weighted critical locus, global
finiteness, and global normalized PCF are separate obligations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.BasilicaProjectiveScheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (k : Type*) [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev Index := Fin 1 ⊕ Unit
abbrev Coordinates := MvPolynomial Index k
abbrev grading := MvPolynomial.homogeneousSubmodule Index k
/-- The two homogeneous basilica coordinate forms. -/
noncomputable def forms : Index → Coordinates k
  | Sum.inl _ => X (Sum.inl 0) ^ 2 - X (Sum.inr ()) ^ 2
  | Sum.inr _ => X (Sum.inr ()) ^ 2

/-- Both coordinate forms have degree two. -/
theorem forms_homogeneous (i : Index) : (forms k i).IsHomogeneous 2 := by
  cases i with
  | inl i => exact ((isHomogeneous_X k _).pow 2).sub ((isHomogeneous_X k _).pow 2)
  | inr i => exact (isHomogeneous_X k _).pow 2

/-- The forms have no common projective zero, in the radical-ideal sense. -/
theorem forms_cover : Pcf.PaperPFormsCoverProjective (forms k) := by
  apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)).trans
  change Ideal.span (Set.range (X : Index → Coordinates k)) ≤
    (Ideal.span (Set.range (forms k))).radical
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  apply Ideal.mem_radical_iff.mpr
  refine ⟨2, ?_⟩
  cases i with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have h0 : forms k (Sum.inl 0) ∈ Ideal.span (Set.range (forms k)) :=
      Ideal.subset_span ⟨Sum.inl 0, rfl⟩
    have h1 : forms k (Sum.inr ()) ∈ Ideal.span (Set.range (forms k)) :=
      Ideal.subset_span ⟨Sum.inr (), rfl⟩
    have hh := Ideal.add_mem _ h0 h1
    simpa [forms] using hh
  | inr i => exact Ideal.subset_span ⟨Sum.inr i, rfl⟩

/-- The actual global basilica morphism of the projective-line scheme. -/
noncomputable def schemeMap : Proj (grading k) ⟶ Proj (grading k) :=
  Pcf.paperPFormsProjectiveSchemeMap (forms k) 2 (by decide) (forms_homogeneous k) (forms_cover k)

theorem preimage_basicOpen (P : Coordinates k) :
    schemeMap k ⁻¹ᵁ Proj.basicOpen (grading k) P =
      Proj.basicOpen (grading k) (aeval (forms k) P) := rfl

/-- The standard finite affine chart is exactly its own inverse image. -/
theorem preimage_affineChart :
    schemeMap k ⁻¹ᵁ Proj.basicOpen (grading k) (X (Sum.inr ())) =
      Proj.basicOpen (grading k) (X (Sum.inr ())) := by
  rw [preimage_basicOpen]
  simp only [aeval_X, forms]
  exact Proj.basicOpen_pow _ _ 2 (by decide)
noncomputable def pointForms (a b : k) : Index → Coordinates k
  | Sum.inl _ => C a * X (Sum.inl 0)
  | Sum.inr _ => C b * X (Sum.inl 0)

theorem pointForms_homogeneous (a b : k) (i : Index) :
    (pointForms k a b i).IsHomogeneous 1 := by
  cases i <;> exact (isHomogeneous_C _ _).mul (isHomogeneous_X _ _)

/-- The homogeneous prime ideal of the rational scheme point `[a:b]`. -/
noncomputable def point (a b : k) (h : a ≠ 0 ∨ b ≠ 0) : Proj (grading k) where
  asHomogeneousIdeal := Pcf.paperPFormsHomogeneousIdealComap
    (pointForms k a b) 1 (by decide) (pointForms_homogeneous k a b) ⊥
  isPrime := by
    change (Ideal.comap (aeval (pointForms k a b)).toRingHom ⊥).IsPrime
    infer_instance
  not_irrelevant_le hi := by
    rcases h with ha | hb
    · have hh := hi (HomogeneousIdeal.mem_irrelevant_of_mem (grading k)
        Nat.zero_lt_one (isHomogeneous_X k (Sum.inl 0)))
      change aeval (pointForms k a b) (X (Sum.inl 0)) = 0 at hh
      simp [pointForms, ha] at hh
    · have hh := hi (HomogeneousIdeal.mem_irrelevant_of_mem (grading k)
        Nat.zero_lt_one (isHomogeneous_X k (Sum.inr ())))
      change aeval (pointForms k a b) (X (Sum.inr ())) = 0 at hh
      simp [pointForms, hb] at hh

theorem output_nonzero (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 - b ^ 2 ≠ 0 ∨ b ^ 2 ≠ 0 := by
  by_cases hb : b = 0
  · left
    have ha : a ≠ 0 := h.resolve_right (not_not.mpr hb)
    simpa [hb] using pow_ne_zero 2 ha
  · exact Or.inr (pow_ne_zero 2 hb)

theorem pointForms_comp_forms (a b : k) :
    (aeval (pointForms k a b)).comp (aeval (forms k)) =
      (MvPolynomial.expand 2).comp (aeval (pointForms k (a ^ 2 - b ^ 2) (b ^ 2))) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [pointForms, forms, MvPolynomial.expand_X] <;> ring

/-- The global scheme map obeys the displayed homogeneous coordinate formula. -/
theorem schemeMap_point (a b : k) (h : a ≠ 0 ∨ b ≠ 0) :
    schemeMap k (point k a b h) =
      point k (a ^ 2 - b ^ 2) (b ^ 2) (output_nonzero k a b h) := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (pointForms k a b) (aeval (forms k) P) = 0 ↔
    aeval (pointForms k (a ^ 2 - b ^ 2) (b ^ 2)) P = 0
  rw [← AlgHom.comp_apply, pointForms_comp_forms, AlgHom.comp_apply]
  exact MvPolynomial.expand_eq_zero (by decide : 0 < 2)

/-- The actual projective scheme point `[0:1]`. -/
noncomputable def zero : Proj (grading k) := point k 0 1 (Or.inr one_ne_zero)
/-- The actual projective scheme point `[-1:1]`. -/
noncomputable def minusOne : Proj (grading k) := point k (-1) 1 (Or.inr one_ne_zero)
/-- The actual projective scheme point `[1:0]`. -/
noncomputable def infinity : Proj (grading k) := point k 1 0 (Or.inl one_ne_zero)

/-- The projective scheme origin maps to `-1`. -/
theorem zero_to_minusOne : schemeMap k (zero k) = minusOne k := by
  unfold zero minusOne
  simpa using schemeMap_point k 0 1 (Or.inr one_ne_zero)

/-- The projective scheme point `-1` returns to the origin. -/
theorem minusOne_to_zero : schemeMap k (minusOne k) = zero k := by
  unfold zero minusOne
  simpa using schemeMap_point k (-1) 1 (Or.inr one_ne_zero)

/-- The actual projective scheme point at infinity is fixed. -/
theorem infinity_fixed : schemeMap k (infinity k) = infinity k := by
  unfold infinity
  simpa using schemeMap_point k 1 0 (Or.inl one_ne_zero)
theorem zero_ne_minusOne : zero k ≠ minusOne k := by
  intro h
  have hx : X (Sum.inl 0) ∈ (zero k).asHomogeneousIdeal := by
    change aeval (pointForms k 0 1) (X (Sum.inl 0)) = 0
    simp [pointForms]
  rw [h] at hx
  change aeval (pointForms k (-1) 1) (X (Sum.inl 0)) = 0 at hx
  simp [pointForms] at hx

private theorem period_two_of_cycle {α : Type*} (f : α → α) (x y : α)
    (hxy : f x = y) (hyx : f y = x) (hne : x ≠ y) :
    f^[2] x = x ∧ f x ≠ x := by
  constructor
  · simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      (congrArg f hxy).trans hyx
  · rw [hxy]
    exact hne.symm

/-- The actual projective scheme origin has exact period two. -/
theorem zero_exact_period_two :
    (schemeMap k)^[2] (zero k) = zero k ∧ schemeMap k (zero k) ≠ zero k :=
  period_two_of_cycle (schemeMap k) (zero k) (minusOne k)
    (zero_to_minusOne k) (minusOne_to_zero k) (zero_ne_minusOne k)

def threePoints : Set (Proj (grading k)) := {zero k, minusOne k, infinity k}

theorem threePoints_forward (p : Proj (grading k)) (hp : p ∈ threePoints k) :
    schemeMap k p ∈ threePoints k := by
  rcases hp with rfl | hp
  · rw [zero_to_minusOne]; simp [threePoints]
  rcases hp with rfl | hp
  · rw [minusOne_to_zero]; simp [threePoints]
  obtain rfl := Set.mem_singleton_iff.mp hp
  rw [infinity_fixed]; simp [threePoints]

/-- Positive orbits of the two critical candidates. The equality of those
candidates with the actual global critical locus is not assumed or proved here. -/
def criticalCandidatePostorbit (q : Proj (grading k)) : Prop :=
  ∃ p ∈ ({zero k, infinity k} : Set (Proj (grading k))),
    ∃ n : ℕ, 0 < n ∧ q = (schemeMap k)^[n] p

theorem criticalCandidatePostorbit_eq_threePoints :
    {q | criticalCandidatePostorbit k q} = threePoints k := by
  ext q
  constructor
  · rintro ⟨p, hp, n, _, rfl⟩
    have hp' : p ∈ threePoints k := by
      rcases hp with rfl | hp
      · simp [threePoints]
      · obtain rfl := Set.mem_singleton_iff.mp hp
        simp [threePoints]
    have hi : ∀ m : ℕ, (schemeMap k)^[m] p ∈ threePoints k := by
      intro m
      induction m with
      | zero => exact hp'
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact threePoints_forward k _ ih
    exact hi n
  · intro hq
    rcases hq with rfl | hq
    · refine ⟨zero k, by simp, 2, by decide, ?_⟩
      exact (zero_exact_period_two k).1.symm
    rcases hq with rfl | hq
    · exact ⟨zero k, by simp, 1, by decide, (zero_to_minusOne k).symm⟩
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact ⟨infinity k, by simp, 1, by decide, (infinity_fixed k).symm⟩
#print axioms forms_cover
#print axioms schemeMap
#print axioms preimage_affineChart
#print axioms schemeMap_point
#print axioms zero_exact_period_two
#print axioms infinity_fixed
#print axioms criticalCandidatePostorbit_eq_threePoints

end Pcf.Examples.PaperP.BasilicaProjectiveScheme
