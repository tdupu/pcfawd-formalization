/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricFibreEmbedding

/-!
# Selecting a reduced fibre component by a field specialization

A compatible map from the normalization `B` to a field `K` determines
a maximal ideal of its finite tensor fibre. Passing through the
nilradical gives an actual field factor of the reduced fibre.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

universe u v w x y

variable {R : Type u} {S : Type v} {B : Type w} {F : Type x} {K : Type y}
  [CommRing R] [CommRing S] [CommRing B] [Field F] [Field K]
  [Algebra R S] [Algebra R B] [Algebra R F] [Algebra R K]
  [Algebra F K] [IsScalarTower R F K] [Module.Finite R B]

/-- The actual field factor selected by a compatible specialization
of the Galois normalization. -/
noncomputable def tensorFibreSelectedFactor (β : B →ₐ[R] K) :
    MaximalSpectrum ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) := by
  let C := B ⊗[R] F
  let ψ := tensorFibreEvaluation (F := F) β
  let I := RingHom.ker ψ.toRingHom
  let q : C →+* C ⧸ nilradical C := Ideal.Quotient.mk (nilradical C)
  have hI : I.IsMaximal := tensorFibreEvaluation_ker_isMaximal (F := F) β
  letI : I.IsMaximal := hI
  have hnil : nilradical C ≤ I := nilradical_le_prime I
  have hker : RingHom.ker q ≤ I := by simpa [q] using hnil
  have hJ : (I.map q).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      (show Function.Surjective q from Ideal.Quotient.mk_surjective) hker
  exact ⟨I.map q, hJ⟩

/-- The selected factor has exactly the prime of `S` cut out by the
field specialization of `B`. In the geometric application this prime
is the generic point of the prescribed subvariety `W`. -/
theorem tensorFibreSelectedFactor_ker_eq
    (ι : S →ₐ[R] B) (β : B →ₐ[R] K) :
    RingHom.ker
      (tensorFibreComponentMap (F := F) ι
        (tensorFibreSelectedFactor (F := F) β)) =
      RingHom.ker (β.toRingHom.comp ι.toRingHom) := by
  let C := B ⊗[R] F
  let ψ := tensorFibreEvaluation (F := F) β
  let I := RingHom.ker ψ.toRingHom
  let q : C →+* C ⧸ nilradical C := Ideal.Quotient.mk (nilradical C)
  have hI : I.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  letI : I.IsPrime := hI
  have hnil : RingHom.ker q ≤ I := by
    simpa [q] using (nilradical_le_prime I)
  have hmem (x : C) : q x ∈ I.map q ↔ x ∈ I := by
    change x ∈ (I.map q).comap q ↔ x ∈ I
    rw [Ideal.comap_map_of_surjective q
      (show Function.Surjective q from Ideal.Quotient.mk_surjective) I,
      ← RingHom.ker_eq_comap_bot, sup_of_le_left hnil]
  ext s
  simp only [RingHom.mem_ker]
  change (Ideal.Quotient.mk (I.map q)
      (q ((Algebra.TensorProduct.includeLeft : B →ₐ[R] C) (ι s)))) = 0 ↔
    β (ι s) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [hmem]
  change ψ ((Algebra.TensorProduct.includeLeft : B →ₐ[R] C) (ι s)) = 0 ↔
    β (ι s) = 0
  change tensorFibreEvaluation (F := F) β ((ι s) ⊗ₜ[R] (1 : F)) = 0 ↔
    β (ι s) = 0
  rw [tensorFibreEvaluation_tmul]
  simp

#print axioms tensorFibreSelectedFactor
#print axioms tensorFibreSelectedFactor_ker_eq

end Pcf
