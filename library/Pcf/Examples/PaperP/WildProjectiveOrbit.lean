/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildOrbit
public import Pcf.Examples.PaperP.WildRestrictions
public import Mathlib.Algebra.MvPolynomial.Expand

/-!
# The infinite orbit on the actual wild projective scheme

The field orbit is realized by the actual projective-plane scheme points
`[0:t:1]`. The displayed global morphism acts on these points by `t ↦ t^(p+1)+c`.
This does not by itself assert the projective restriction's PCF predicate.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type*) [Field k] (p : ℕ) (c : k)

noncomputable def linePointForms (t : k) : Index → Coordinates k
  | Sum.inl i => if i = 0 then 0 else C t * x k
  | Sum.inr _ => x k

theorem linePointForms_homogeneous (t : k) (i : Index) :
    (linePointForms k t i).IsHomogeneous 1 := by
  have hx : (x k).IsHomogeneous 1 := isHomogeneous_X k _
  cases i with
  | inl i =>
    fin_cases i
    · exact isHomogeneous_zero Index k 1
    · simpa [linePointForms] using (isHomogeneous_C Index t).mul hx
  | inr i => exact hx

/-- The actual projective scheme point `[0:t:1]`, not a quotient of field vectors. -/
noncomputable def linePoint (t : k) : Proj (grading k) where
  asHomogeneousIdeal := Pcf.paperPFormsHomogeneousIdealComap
    (linePointForms k t) 1 (by decide) (linePointForms_homogeneous k t) ⊥
  isPrime := by
    change (Ideal.comap (aeval (linePointForms k t)).toRingHom ⊥).IsPrime
    infer_instance
  not_irrelevant_le hi := by
    have hh := hi (HomogeneousIdeal.mem_irrelevant_of_mem (grading k)
      Nat.zero_lt_one (isHomogeneous_X k (Sum.inr ())))
    change aeval (linePointForms k t) (z k) = 0 at hh
    simp [linePointForms, z, x] at hh

/-- Different finite coordinates give different actual scheme points. -/
theorem linePoint_injective : Function.Injective (linePoint k) := by
  intro a b h
  have ha : y k - C a * z k ∈ (linePoint k a).asHomogeneousIdeal := by
    change aeval (linePointForms k a) (y k - C a * z k) = 0
    simp [linePointForms, y, z]
  rw [h] at ha
  change aeval (linePointForms k b) (y k - C a * z k) = 0 at ha
  have hh : C (b - a) * x k = 0 := by
    simpa [linePointForms, y, z, map_sub, sub_mul] using ha
  have hC : C (b - a) = (0 : Coordinates k) :=
    (mul_eq_zero.mp hh).resolve_right (X_ne_zero (Sum.inl (0 : Fin 2)))
  exact (sub_eq_zero.mp ((C_injective Index k) (by simpa using hC))).symm

/-- The pullback square on point-evaluation homomorphisms is exact. -/
theorem linePointForms_comp_forms (hp : 0 < p) (t : k) :
    (aeval (linePointForms k t)).comp (aeval (forms k p c)) =
      (MvPolynomial.expand (p + 1)).comp
        (aeval (linePointForms k (t ^ (p + 1) + c))) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
    fin_cases i <;>
      simp [linePointForms, forms, x, y, z, zero_pow (by omega : p ≠ 0),
        MvPolynomial.expand_X, mul_pow, map_add, map_pow]
    all_goals ring
  | inr i => simp [linePointForms, forms, z, x, MvPolynomial.expand_X]

/-- The actual projective-plane morphism restricts on these scheme points to `h`. -/
theorem schemeMap_linePoint (hp : 0 < p) (t : k) :
    schemeMap k p c hp (linePoint k t) = linePoint k (returnFunction k p c t) := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (linePointForms k t) (aeval (forms k p c) P) = 0 ↔
    aeval (linePointForms k (returnFunction k p c t)) P = 0
  rw [← AlgHom.comp_apply, linePointForms_comp_forms k p c hp, AlgHom.comp_apply]
  exact MvPolynomial.expand_eq_zero (by omega : 0 < p + 1)

/-- Every iterate on the actual projective scheme agrees with the field orbit. -/
theorem schemeMap_iterate_linePoint (hp : 0 < p) (t : k) (n : ℕ) :
    (schemeMap k p c hp)^[n] (linePoint k t) =
      linePoint k ((returnFunction k p c)^[n] t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, schemeMap_linePoint, Function.iterate_succ_apply']

/-- Every finite scheme point on the invariant line avoids the infinity line. -/
theorem linePoint_not_mem_H2 (t : k) : linePoint k t ∉ H2 k := by
  change aeval (linePointForms k t) (z k) ≠ 0
  simp [linePointForms, z, x]

local instance projectivePrimeFieldAlgebra [CharP k p] : Algebra (ZMod p) k := ZMod.algebra k p

/-- The actual orbit in the projective scheme is infinite for transcendental `c`. -/
theorem schemeMap_lineOrigin_orbit_infinite [Fact p.Prime] [CharP k p]
    (hc : Transcendental (ZMod p) c) :
    (Set.range (fun n : ℕ => (schemeMap k p c (Fact.out : p.Prime).pos)^[n]
      (linePoint k 0))).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  apply returnFunction_orbit_injective k p c hc
  apply linePoint_injective k
  simpa only [schemeMap_iterate_linePoint] using h

#print axioms linePoint_injective
#print axioms linePointForms_comp_forms
#print axioms schemeMap_linePoint
#print axioms schemeMap_iterate_linePoint
#print axioms linePoint_not_mem_H2
#print axioms schemeMap_lineOrigin_orbit_infinite
end Pcf.Examples.PaperP.Wild
