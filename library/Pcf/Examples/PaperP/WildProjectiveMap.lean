/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianProjectiveChartMap
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# The actual projective-plane morphism of the wild example

The displayed forms have a common positive degree and no common projective
zero. They therefore define an actual global morphism of the projective-plane
scheme. Global finiteness is a separate assertion, not assumed or proved here.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Index := Fin 2 ⊕ Unit
abbrev Coordinates (k : Type*) [CommRing k] := MvPolynomial Index k
abbrev grading (k : Type*) [CommRing k] := MvPolynomial.homogeneousSubmodule Index k

variable (k : Type*) [Field k] (p : ℕ) (c : k)

noncomputable def x : Coordinates k := X (Sum.inl 0)
noncomputable def y : Coordinates k := X (Sum.inl 1)
noncomputable def z : Coordinates k := X (Sum.inr ())

/-- The three exact homogeneous forms of `paper-p.tex`, Example `ex:wild`. -/
noncomputable def forms : Index → Coordinates k
  | Sum.inl i => if i = 0 then x k ^ p * (x k + y k)
      else y k ^ (p + 1) - x k ^ (p + 1) - x k ^ p * z k +
        x k * y k ^ p + C c * z k ^ (p + 1)
  | Sum.inr _ => z k ^ (p + 1)

@[simp] theorem forms_zero : forms k p c (Sum.inl 0) = x k ^ p * (x k + y k) := by
  simp [forms]
@[simp] theorem forms_one : forms k p c (Sum.inl 1) =
    y k ^ (p + 1) - x k ^ (p + 1) - x k ^ p * z k +
      x k * y k ^ p + C c * z k ^ (p + 1) := by simp [forms]
@[simp] theorem forms_two : forms k p c (Sum.inr ()) = z k ^ (p + 1) := rfl

/-- All three forms have the required common degree `p+1`. -/
theorem forms_homogeneous (i : Index) : (forms k p c i).IsHomogeneous (p + 1) := by
  have hx : (x k).IsHomogeneous 1 := isHomogeneous_X k _
  have hy : (y k).IsHomogeneous 1 := isHomogeneous_X k _
  have hz : (z k).IsHomogeneous 1 := isHomogeneous_X k _
  have hxp (n : ℕ) : (x k ^ n).IsHomogeneous n := by simpa using hx.pow n
  have hyp (n : ℕ) : (y k ^ n).IsHomogeneous n := by simpa using hy.pow n
  have hzp (n : ℕ) : (z k ^ n).IsHomogeneous n := by simpa using hz.pow n
  have hxy : (x k * y k ^ p).IsHomogeneous (p + 1) := by
    simpa only [Nat.add_comm 1 p] using hx.mul (hyp p)
  have hcz : (C c * z k ^ (p + 1)).IsHomogeneous (p + 1) := by
    simpa only [Nat.zero_add] using (isHomogeneous_C Index c).mul (hzp (p + 1))
  cases i with
  | inl i =>
    fin_cases i
    · simpa [forms] using (hxp p).mul (hx.add hy)
    · simpa [forms] using
        ((((hyp (p + 1)).sub (hxp (p + 1))).sub ((hxp p).mul hz)).add hxy).add
          hcz
  | inr i => simpa [forms] using hzp (p + 1)

/-- Any prime containing the three forms contains every source coordinate. -/
theorem coordinates_mem_of_forms_mem (hp : 0 < p) (I : Ideal (Coordinates k)) [I.IsPrime]
    (h : ∀ i, forms k p c i ∈ I) : x k ∈ I ∧ y k ∈ I ∧ z k ∈ I := by
  have hIp : I.IsPrime := inferInstance
  have hz : z k ∈ I := hIp.mem_of_pow_mem (p + 1) (h (Sum.inr ()))
  have hf0 : x k ^ p * (x k + y k) ∈ I := h (Sum.inl 0)
  have hf1 : y k ^ (p + 1) - x k ^ (p + 1) + x k * y k ^ p ∈ I := by
    have H := I.sub_mem (I.add_mem (h (Sum.inl 1)) (I.mul_mem_left (x k ^ p) hz))
      (I.mul_mem_left (C c) (I.pow_mem_of_mem hz (p + 1) (by omega)))
    convert H using 1
    simp only [forms_one]
    ring
  have hx : x k ∈ I := by
    rcases hIp.mem_or_mem hf0 with hx | hxy
    · exact hIp.mem_of_pow_mem p hx
    · have H := I.sub_mem (I.mul_mem_right (y k ^ p) hxy) hf1
      have he : (x k + y k) * y k ^ p -
          (y k ^ (p + 1) - x k ^ (p + 1) + x k * y k ^ p) = x k ^ (p + 1) := by ring
      rw [he] at H
      exact hIp.mem_of_pow_mem (p + 1) H
  have hy : y k ∈ I := by
    have H := I.sub_mem (I.add_mem hf1 (I.pow_mem_of_mem hx (p + 1) (by omega)))
      (I.mul_mem_right (y k ^ p) hx)
    have he : y k ^ (p + 1) - x k ^ (p + 1) + x k * y k ^ p + x k ^ (p + 1) -
        x k * y k ^ p = y k ^ (p + 1) := by ring
    rw [he] at H
    exact hIp.mem_of_pow_mem (p + 1) H
  exact ⟨hx, hy, hz⟩

/-- The exact forms have no common projective zero, including non-rational scheme points. -/
theorem forms_cover (hp : 0 < p) : Pcf.PaperPFormsCoverProjective (forms k p c) := by
  apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 2)).trans
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro I hI
  letI := hI.2
  change Ideal.span (Set.range (X : Index → Coordinates k)) ≤ I
  rw [Ideal.span_le, Set.range_subset_iff]
  have hh := coordinates_mem_of_forms_mem k p c hp I (fun i => hI.1 (Ideal.subset_span ⟨i, rfl⟩))
  intro i
  cases i with
  | inl i =>
    fin_cases i
    · exact hh.1
    · exact hh.2.1
  | inr i => exact hh.2.2

/-- The actual global projective scheme morphism defined by the source formulas.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
noncomputable def schemeMap (hp : 0 < p) : Proj (grading k) ⟶ Proj (grading k) :=
  Pcf.paperPFormsProjectiveSchemeMap (forms k p c) (p + 1) (by omega)
    (forms_homogeneous k p c) (forms_cover k p c hp)

/-- Actual projective basic opens pull back by substitution of the displayed forms.

Analogy with Stacks Lemma 01MY(2): only its basic-open identity is asserted here.
The substitution multiplies degrees by `p+1`, rather than preserving the
original grading; the ambient projective-map construction handles this
explicitly. No twisted-sheaf characterization from the tag is claimed.
-/
theorem preimage_basicOpen (hp : 0 < p) (P : Coordinates k) :
    schemeMap k p c hp ⁻¹ᵁ Proj.basicOpen (grading k) P =
      Proj.basicOpen (grading k) (aeval (forms k p c) P) := rfl

/-- The finite chart `D₊(z)` is invariant under the actual projective morphism. -/
theorem preimage_affineChart (hp : 0 < p) :
    schemeMap k p c hp ⁻¹ᵁ Proj.basicOpen (grading k) (z k) =
      Proj.basicOpen (grading k) (z k) := by
  rw [preimage_basicOpen]
  simp only [z, aeval_X, forms_two]
  exact Proj.basicOpen_pow _ _ (p + 1) (by omega)

#print axioms forms_homogeneous
#print axioms coordinates_mem_of_forms_mem
#print axioms forms_cover
#print axioms schemeMap
#print axioms preimage_affineChart
end Pcf.Examples.PaperP.Wild
