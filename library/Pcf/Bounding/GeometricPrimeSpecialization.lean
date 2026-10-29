/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricFibreSelection

/-!
# A factor above a prescribed prime

The prime of the Galois normalization lying over a centre gives a
compatible specialization into its residue fraction field. The
preceding fibre selection theorem then locates a field factor whose
contraction to an intermediate algebra is the prescribed prime.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

universe u v w

variable {R : Type u} {S : Type v} {B : Type w}
  [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Module.Finite R B]

/-- A prime `q` of `B` over `P` selects a reduced tensor-fibre factor
whose contraction to `S` is `q ∩ S`. -/
theorem exists_tensorFibre_factor_over_prime
    (ι : S →ₐ[R] B) (P : Ideal R) (q : Ideal B)
    [P.IsPrime] [q.IsPrime] [q.LiesOver P] :
    ∃ m : MaximalSpectrum
      ((B ⊗[R] FractionRing (R ⧸ P)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ P))),
      RingHom.ker
        (tensorFibreComponentMap (F := FractionRing (R ⧸ P)) ι m) =
        q.comap ι.toRingHom := by
  letI : Algebra (R ⧸ P) (B ⧸ q) := inferInstance
  let F := FractionRing (R ⧸ P)
  let K := FractionRing (B ⧸ q)
  letI : Algebra (R ⧸ P) K := Algebra.compHom K (algebraMap (R ⧸ P) (B ⧸ q))
  letI : SMul (R ⧸ P) K := Algebra.toSMul
  have hinj : Function.Injective (algebraMap (R ⧸ P) K) := by
    change Function.Injective
      ((algebraMap (B ⧸ q) K).comp (algebraMap (R ⧸ P) (B ⧸ q)))
    exact (IsFractionRing.injective (B ⧸ q) K).comp
      (FaithfulSMul.algebraMap_injective (R ⧸ P) (B ⧸ q))
  letI : FaithfulSMul (R ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective (R ⧸ P) K).mpr hinj
  letI : Algebra F K := FractionRing.liftAlgebra (R ⧸ P) K
  letI : Algebra R K := Algebra.compHom K (algebraMap R (R ⧸ P))
  letI : SMul R K := Algebra.toSMul
  letI : IsScalarTower R (R ⧸ P) K :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let β : B →ₐ[R] K := {
    toRingHom := (algebraMap (B ⧸ q) K).comp (algebraMap B (B ⧸ q))
    commutes' := by
      intro r
      rfl }
  letI : IsScalarTower R F K := inferInstance
  refine ⟨tensorFibreSelectedFactor (F := F) β, ?_⟩
  rw [tensorFibreSelectedFactor_ker_eq (F := F) ι β]
  ext s
  simp [β, RingHom.mem_ker, Ideal.mem_comap,
    Ideal.Quotient.eq_zero_iff_mem]

#print axioms exists_tensorFibre_factor_over_prime

end Pcf
