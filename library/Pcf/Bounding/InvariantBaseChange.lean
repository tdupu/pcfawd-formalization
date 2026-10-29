/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.ReynoldsSpecialization
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Invariants after base change to a centre's function field

The fibre algebra in `latex/paper-p.tex`, Lemma
`lem:allcodim-monodromy`, is `C=B⊗[R]F`. The finite Galois group
acts on the first tensor factor. When its order is invertible, the
Reynolds projection proves that all invariant tensors are scalars,
without a flatness hypothesis on `B/R`.
-/

@[expose] public section

namespace Pcf

universe u v w x

open scoped TensorProduct
set_option linter.style.haveILetI false

variable {R : Type u} {B : Type v} {F : Type w} {G : Type x}
  [CommRing R] [CommRing B] [Field F]
  [Algebra R B] [Algebra R F]
  [Group G] [Fintype G]

/-- The group action on the first tensor factor of the actual fibre
algebra `B⊗[R]F`. -/
def tensorBaseChangeRepresentation (ρ : Representation R G B) :
    Representation R G (B ⊗[R] F) where
  toFun g := TensorProduct.map (ρ g) LinearMap.id
  map_one' := by
    ext b a
    simp
  map_mul' g h := by
    ext b a
    simp [map_mul]

omit [Fintype G] in
@[simp] theorem tensorBaseChangeRepresentation_tmul
    (ρ : Representation R G B) (g : G) (b : B) (a : F) :
    tensorBaseChangeRepresentation (F := F) ρ g (b ⊗ₜ[R] a) =
      ρ g b ⊗ₜ[R] a := by
  simp [tensorBaseChangeRepresentation]

section InvertibleOrder

variable [Invertible (Fintype.card G : R)]

/-- Reynolds averaging commutes with adjoining the centre's field on
the second tensor factor. -/
theorem tensorBaseChange_average_tmul
    (ρ : Representation R G B) (b : B) (a : F) :
    (tensorBaseChangeRepresentation (F := F) ρ).averageMap (b ⊗ₜ[R] a) =
      ρ.averageMap b ⊗ₜ[R] a := by
  let f : B →ₗ[R] B ⊗[R] F := (TensorProduct.mk R B F).flip a
  have hf (g : G) (x : B) :
      f (ρ g x) = tensorBaseChangeRepresentation (F := F) ρ g (f x) := by
    simp [f]
  simpa only [f, LinearMap.flip_apply, TensorProduct.mk_apply] using
    (map_reynolds_of_intertwining ρ
      (tensorBaseChangeRepresentation (F := F) ρ) f hf b).symm

/-- If the invariants of `B` are exactly `R`, the invariants of the
actual fibre algebra `B⊗[R]F` lie in the scalar copy of `F`.
No flatness assumption is used. -/
theorem tensorBaseChange_invariant_is_scalar
    (ρ : Representation R G B)
    (hfixed : ∀ b : B, b ∈ ρ.invariants →
      ∃ r : R, algebraMap R B r = b)
    (c : B ⊗[R] F)
    (hc : c ∈ (tensorBaseChangeRepresentation (F := F) ρ).invariants) :
    ∃ a : F, (Algebra.TensorProduct.includeRight : F →ₐ[R] B ⊗[R] F) a = c := by
  let σ : F →ₐ[R] B ⊗[R] F := Algebra.TensorProduct.includeRight
  let τ := tensorBaseChangeRepresentation (F := F) ρ
  have havg : ∀ z : B ⊗[R] F, ∃ a : F, σ a = τ.averageMap z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b a =>
      obtain ⟨r, hr⟩ := hfixed (ρ.averageMap b) (ρ.averageMap_invariant b)
      refine ⟨r • a, ?_⟩
      rw [tensorBaseChange_average_tmul, ← hr]
      simpa only [σ, Algebra.TensorProduct.includeRight_apply, Algebra.smul_def, mul_one]
        using (TensorProduct.smul_tmul r (1 : B) a).symm
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨a₁, ha₁⟩ := h₁
      obtain ⟨a₂, ha₂⟩ := h₂
      refine ⟨a₁ + a₂, ?_⟩
      rw [map_add, ha₁, ha₂, map_add]
  obtain ⟨a, ha⟩ := havg c
  exact ⟨a, ha.trans ((τ.averageMap_id c hc))⟩

/-- Equality of the invariant subset with the image of the scalar
inclusion, provided the action fixes the unit of `B`. -/
theorem tensorBaseChange_invariants_eq_scalar_range
    (ρ : Representation R G B)
    (hfixed : ∀ b : B, b ∈ ρ.invariants →
      ∃ r : R, algebraMap R B r = b)
    (hone : ∀ g : G, ρ g (1 : B) = 1) :
    ((tensorBaseChangeRepresentation (F := F) ρ).invariants :
      Set (B ⊗[R] F)) =
      Set.range (Algebra.TensorProduct.includeRight : F →ₐ[R] B ⊗[R] F) := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha⟩ := tensorBaseChange_invariant_is_scalar
      (F := F) ρ hfixed c hc
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    intro g
    simp only [Algebra.TensorProduct.includeRight_apply,
      tensorBaseChangeRepresentation_tmul, hone]

end InvertibleOrder

/-- A semiring action fixing the base ring gives a linear
representation on the integral closure. -/
def ringActionRepresentation
    [MulSemiringAction G B] [SMulCommClass G R B] :
    Representation R G B where
  toFun g := {
    toFun := fun b => g • b
    map_add' := smul_add g
    map_smul' := fun r b => smul_comm g r b
  }
  map_one' := by ext b; exact one_smul G b
  map_mul' g h := by ext b; exact mul_smul g h b

omit [Fintype G] in
@[simp] theorem ringActionRepresentation_apply
    [MulSemiringAction G B] [SMulCommClass G R B]
    (g : G) (b : B) :
    ringActionRepresentation (R := R) g b = g • b := rfl

/-- The actual tensor fibre has no new invariant classes when the
group order is invertible and the original invariant ring is `R`.
This is the base-change assertion `(B⊗_R F)^G=F` in the proof of
`lem:allcodim-monodromy`, stated as equality with the image of
`F→B⊗_R F` so no nonemptiness of the fibre is hidden. -/
theorem tensorBaseChange_invariants_eq_scalar_range_of_isInvariant
    [MulSemiringAction G B] [SMulCommClass G R B]
    [Algebra.IsInvariant R B G]
    [Invertible (Fintype.card G : R)] :
    ((tensorBaseChangeRepresentation (F := F)
      (ringActionRepresentation (R := R) (B := B) (G := G))).invariants :
      Set (B ⊗[R] F)) =
      Set.range (Algebra.TensorProduct.includeRight : F →ₐ[R] B ⊗[R] F) := by
  apply tensorBaseChange_invariants_eq_scalar_range
  · intro b hb
    exact Algebra.IsInvariant.isInvariant (G := G) b
      (fun g => hb g)
  · intro g
    exact smul_one g

/-- Prime-to-characteristic form of invariant base change, with the
invertibility of the group order derived from `char(R)=p`. -/
theorem tensorBaseChange_invariants_eq_scalar_range_charP
    (p : ℕ) (hp : p.Prime) [CharP R p]
    [MulSemiringAction G B] [SMulCommClass G R B]
    [Algebra.IsInvariant R B G]
    (horder : (Fintype.card G).Coprime p) :
    ((tensorBaseChangeRepresentation (F := F)
      (ringActionRepresentation (R := R) (B := B) (G := G))).invariants :
      Set (B ⊗[R] F)) =
      Set.range (Algebra.TensorProduct.includeRight : F →ₐ[R] B ⊗[R] F) := by
  letI : Invertible (Fintype.card G : R) :=
    ((nonempty_invertible_iff_isUnit _).mpr
      ((CharP.isUnit_natCast_iff hp).mpr
        (hp.coprime_iff_not_dvd.mp horder.symm))).some
  exact tensorBaseChange_invariants_eq_scalar_range_of_isInvariant

/-- For a nonempty fibre, the scalar copy of its function field is
faithfully embedded in the tensor algebra. -/
theorem tensorBaseChange_scalar_injective
    [Nontrivial (B ⊗[R] F)] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : F →ₐ[R] B ⊗[R] F) := by
  exact (Algebra.TensorProduct.includeRight : F →ₐ[R] B ⊗[R] F).injective

#print axioms tensorBaseChange_invariant_is_scalar
#print axioms tensorBaseChange_invariants_eq_scalar_range_of_isInvariant
#print axioms tensorBaseChange_invariants_eq_scalar_range_charP
#print axioms tensorBaseChange_scalar_injective

end Pcf
