/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Integral closure after smooth base change

This file gives the affine algebra statement behind Stacks Project Tag `03GV`, in the
`IsIntegralClosure` form consumed by the normalization step of Tag `0EYH`.

If `N` is the integral closure of `R` in `B` and `R → R'` is smooth, then
`R' ⊗[R] N` is the integral closure of `R'` in `R' ⊗[R] B`.  The algebra structure on the
two tensor products is the canonical base change of `N → B`.
-/

@[expose] public section

universe u

open TensorProduct

namespace Pcf.Stacks

variable {R R' N B : Type u}
variable [CommRing R] [CommRing R'] [CommRing N] [CommRing B]
variable [Algebra R R'] [Algebra R N] [Algebra R B]
variable [Algebra N B] [IsScalarTower R N B]
variable [IsIntegralClosure N R B]

/-- The canonical algebra structure
`R' ⊗[R] N → R' ⊗[R] B` obtained by base changing `N → B`. -/
@[instance_reducible]
noncomputable def normalizationBaseChangeAlgebra :
    Algebra (R' ⊗[R] N) (R' ⊗[R] B) :=
  (Algebra.TensorProduct.map (AlgHom.id R' R')
    (IsScalarTower.toAlgHom R N B)).toRingHom.toAlgebra

attribute [local instance] normalizationBaseChangeAlgebra

/-- Affine form of the normalization comparison in Stacks Tag `03GV`: smooth base change
of an arbitrary integral closure is canonically equivalent to the integral closure after
base change. -/
noncomputable def smoothBaseChangeIntegralClosureEquiv [Algebra.Smooth R R'] :
    R' ⊗[R] N ≃ₐ[R'] integralClosure R' (R' ⊗[R] B) :=
  (Algebra.TensorProduct.congr (.refl (R := R') (A₁ := R'))
    (IsIntegralClosure.equiv R N B (integralClosure R B))).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R R' B)
      TensorProduct.toIntegralClosure_bijective_of_smooth)

/-- The comparison equivalence commutes with the canonical embeddings into
`R' ⊗[R] B`. -/
theorem smoothBaseChangeIntegralClosureEquiv_val [Algebra.Smooth R R']
    (x : R' ⊗[R] N) :
    ((smoothBaseChangeIntegralClosureEquiv
        (R := R) (R' := R') (N := N) (B := B) x :
      integralClosure R' (R' ⊗[R] B)) : R' ⊗[R] B) =
      algebraMap (R' ⊗[R] N) (R' ⊗[R] B) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul x y =>
      change x ⊗ₜ[R] ((IsIntegralClosure.equiv R N B (integralClosure R B) y :
          integralClosure R B) : B) =
        (Algebra.TensorProduct.map (AlgHom.id R' R')
          (IsScalarTower.toAlgHom R N B)) (x ⊗ₜ[R] y)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun z : B => x ⊗ₜ[R] z)
        (IsIntegralClosure.algebraMap_equiv R N B (integralClosure R B) y)

/-- The exact `IsIntegralClosure` input needed after the étale base change in Tag `0EYH`.

The conclusion uses `normalizationBaseChangeAlgebra`, the base change of the original
embedding `N → B`; no normality or integral-closure conclusion is assumed. -/
theorem smoothBaseChange_isIntegralClosure [Algebra.Smooth R R'] :
    IsIntegralClosure (R' ⊗[R] N) R' (R' ⊗[R] B) := by
  let e := smoothBaseChangeIntegralClosureEquiv
    (R := R) (R' := R') (N := N) (B := B)
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    rw [smoothBaseChangeIntegralClosureEquiv_val,
      smoothBaseChangeIntegralClosureEquiv_val, hxy]
  · intro x
    constructor
    · intro hx
      let z : integralClosure R' (R' ⊗[R] B) := ⟨x, hx⟩
      refine ⟨e.symm z, ?_⟩
      rw [← smoothBaseChangeIntegralClosureEquiv_val]
      simp [e, z]
    · rintro ⟨y, rfl⟩
      rw [← smoothBaseChangeIntegralClosureEquiv_val]
      exact (e y).2

/-- The localization form used literally in Tag `0EYH`: if `N` is the normalization of
`R` in `N[1/a]`, then after smooth base change `R → R'`, the tensor product `R' ⊗[R] N`
is the normalization of `R'` in its localization away from the image of `a`.

The proof first applies the tensor-product form of Tag `03GV`, then uses the canonical
base-change equivalence between `R' ⊗[R] N[1/a]` and `(R' ⊗[R] N)[1/a]`. -/
theorem smoothBaseChange_isIntegralClosure_localizationAway
    {S : Type u} [CommRing S] [Algebra R S]
    [Algebra.Smooth R R'] (a : R)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))] :
    IsIntegralClosure (R' ⊗[R] S) R'
      (Localization.Away
        (algebraMap R' (R' ⊗[R] S) (algebraMap R R' a))) := by
  let B := Localization.Away (algebraMap R S a)
  let T := R' ⊗[R] S
  let _ : Algebra T (R' ⊗[R] B) :=
    normalizationBaseChangeAlgebra (R := R) (R' := R') (N := S) (B := B)
  have hIC : IsIntegralClosure T R' (R' ⊗[R] B) :=
    smoothBaseChange_isIntegralClosure (R := R) (R' := R') (N := S) (B := B)
  let _ : IsIntegralClosure T R' (R' ⊗[R] B) := hIC
  let F : R' ⊗[R] B ≃ₐ[R']
      Localization.Away ((1 : R') ⊗ₜ[R] algebraMap R S a) :=
    IsLocalization.Away.tensorProductEquivTMulRight R R'
      (algebraMap R S a) B
  have hbase : (1 : R') ⊗ₜ[R] algebraMap R S a =
      algebraMap R' T (algebraMap R R' a) := by
    change (1 : R') ⊗ₜ[R] algebraMap R S a =
      algebraMap R R' a ⊗ₜ[R] (1 : S)
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm
  rw [← hbase]
  apply IsIntegralClosure.of_algEquiv T F
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      change algebraMap T (Localization.Away
          ((1 : R') ⊗ₜ[R] algebraMap R S a)) (x ⊗ₜ[R] y) =
        F ((Algebra.TensorProduct.map (AlgHom.id R' R')
          (IsScalarTower.toAlgHom R S B)) (x ⊗ₜ[R] y))
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact (IsLocalization.Away.tensorProductEquivTMulRight_tmul
        (R := R) (S := R') S (algebraMap R S a) B x y).symm

#print axioms smoothBaseChangeIntegralClosureEquiv_val
#print axioms smoothBaseChange_isIntegralClosure
#print axioms smoothBaseChange_isIntegralClosure_localizationAway

end Pcf.Stacks
