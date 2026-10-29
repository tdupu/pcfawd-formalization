/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GeometricPrimeLyingOver

/-!
# The centre function field inside an intermediate component

For `Q` a prime of an intermediate coordinate algebra `S/R`, the
fraction field of `S/Q` is naturally an algebra over the fraction
field of `R/(Q ∩ R)`. This is the field structure needed to state the
last embedding step of `lem:allcodim-monodromy` over its correct base.
-/

@[expose] public section

namespace Pcf

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
set_option linter.style.haveILetI false

universe u v

variable {R : Type u} {S : Type v}
  [CommRing R] [CommRing S] [Algebra R S]

/-- The function field of a prime centre of `S` is an algebra over
the function field of its image in `R`. -/
@[instance_reducible] noncomputable def centreFieldAlgebra (Q : Ideal S) [Q.IsPrime] :
    Algebra (FractionRing (R ⧸ Q.under R)) (FractionRing (S ⧸ Q)) := by
  let P := Q.under R
  letI : Q.LiesOver P := ⟨rfl⟩
  letI : Algebra (R ⧸ P) (S ⧸ Q) := inferInstance
  let E := FractionRing (S ⧸ Q)
  letI : Algebra (R ⧸ P) E := Algebra.compHom E (algebraMap (R ⧸ P) (S ⧸ Q))
  have hinj : Function.Injective (algebraMap (R ⧸ P) E) := by
    change Function.Injective
      ((algebraMap (S ⧸ Q) E).comp (algebraMap (R ⧸ P) (S ⧸ Q)))
    exact (IsFractionRing.injective (S ⧸ Q) E).comp
      (FaithfulSMul.algebraMap_injective (R ⧸ P) (S ⧸ Q))
  exact (IsFractionRing.lift hinj).toAlgebra

/-- The field map extends the quotient map on the base coordinate
ring, so its scalars agree with the original `R → S` map. -/
theorem centreFieldAlgebra_algebraMap_quotient
    (Q : Ideal S) [Q.IsPrime]
    (a : R ⧸ Q.under R) :
    letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
    algebraMap (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q))
        (algebraMap (R ⧸ Q.under R) (FractionRing (R ⧸ Q.under R)) a) =
      algebraMap (S ⧸ Q) (FractionRing (S ⧸ Q))
        (algebraMap (R ⧸ Q.under R) (S ⧸ Q) a) := by
  let P := Q.under R
  letI : Q.LiesOver P := ⟨rfl⟩
  letI : Algebra (R ⧸ P) (S ⧸ Q) := inferInstance
  let E := FractionRing (S ⧸ Q)
  let F := FractionRing (R ⧸ P)
  letI : Algebra (R ⧸ P) E :=
    Algebra.compHom E (algebraMap (R ⧸ P) (S ⧸ Q))
  letI : Algebra F E := centreFieldAlgebra Q
  have hinj : Function.Injective (algebraMap (R ⧸ P) E) := by
    change Function.Injective
      ((algebraMap (S ⧸ Q) E).comp (algebraMap (R ⧸ P) (S ⧸ Q)))
    exact (IsFractionRing.injective (S ⧸ Q) E).comp
      (FaithfulSMul.algebraMap_injective (R ⧸ P) (S ⧸ Q))
  change IsFractionRing.lift hinj (algebraMap (R ⧸ P) F a) =
    algebraMap (R ⧸ P) E a
  exact IsFractionRing.lift_algebraMap hinj a

section Component

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The field embedding of the prescribed centre into a selected
component, initially as a ring homomorphism. -/
noncomputable def centreFieldComponentRingHom
    (ι : S →ₐ[R] B) (Q : Ideal S) [Q.IsPrime]
    (m : MaximalSpectrum
      ((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))))
    (hker : RingHom.ker
      (tensorFibreComponentMap
        (F := FractionRing (R ⧸ Q.under R)) ι m) = Q) :
    letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    FractionRing (S ⧸ Q) →+*
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) := by
  letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  let φ := tensorFibreComponentMap
    (F := FractionRing (R ⧸ Q.under R)) ι m
  have hQ : ∀ s : S, s ∈ Q → φ s = 0 := by
    intro s hs
    exact RingHom.mem_ker.mp (hker.symm ▸ hs)
  let φQ : S ⧸ Q →+* _ := Ideal.Quotient.lift Q φ hQ
  have hφQ : Function.Injective φQ :=
    (Ideal.injective_lift_iff hQ).mpr hker
  exact IsFractionRing.lift hφQ

@[simp] theorem centreFieldComponentRingHom_algebraMap_quotient
    (ι : S →ₐ[R] B) (Q : Ideal S) [Q.IsPrime]
    (m : MaximalSpectrum
      ((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))))
    (hker : RingHom.ker
      (tensorFibreComponentMap
        (F := FractionRing (R ⧸ Q.under R)) ι m) = Q)
    (s : S) :
    letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    centreFieldComponentRingHom ι Q m hker
      (algebraMap (S ⧸ Q) (FractionRing (S ⧸ Q))
        (Ideal.Quotient.mk Q s)) =
      tensorFibreComponentMap
        (F := FractionRing (R ⧸ Q.under R)) ι m s := by
  letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  simp [centreFieldComponentRingHom, IsFractionRing.lift_algebraMap]

/-- The field embedding into a selected component respects the
function field of the image centre. -/
theorem centreFieldComponentRingHom_commutes
    (ι : S →ₐ[R] B) (Q : Ideal S) [Q.IsPrime]
    (m : MaximalSpectrum
      ((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))))
    (hker : RingHom.ker
      (tensorFibreComponentMap
        (F := FractionRing (R ⧸ Q.under R)) ι m) = Q)
    (a : FractionRing (R ⧸ Q.under R)) :
    letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
    letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    centreFieldComponentRingHom ι Q m hker
      (algebraMap (FractionRing (R ⧸ Q.under R))
        (FractionRing (S ⧸ Q)) a) =
      algebraMap (FractionRing (R ⧸ Q.under R))
        (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
          nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) a := by
  let P := Q.under R
  let F := FractionRing (R ⧸ P)
  let E := FractionRing (S ⧸ Q)
  let L := ((B ⊗[R] F) ⧸ nilradical (B ⊗[R] F)) ⧸ m.asIdeal
  letI : Algebra F E := centreFieldAlgebra Q
  letI : Field L := Ideal.Quotient.field m.asIdeal
  let e : E →+* L := centreFieldComponentRingHom ι Q m hker
  have hEq : e.comp (algebraMap F E) = algebraMap F L := by
    apply IsFractionRing.ringHom_ext (A := R ⧸ P)
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change e (algebraMap F E
      (algebraMap (R ⧸ P) F (Ideal.Quotient.mk P r))) =
        algebraMap F L (algebraMap (R ⧸ P) F (Ideal.Quotient.mk P r))
    rw [centreFieldAlgebra_algebraMap_quotient (Q := Q)]
    letI : Q.LiesOver P := ⟨rfl⟩
    letI : Algebra (R ⧸ P) (S ⧸ Q) := inferInstance
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [centreFieldComponentRingHom_algebraMap_quotient]
    exact tensorFibreComponentMap_algebraMap
      (F := F) ι m r
  exact congrArg (fun f : F →+* L => f a) hEq

/-- The source-faithful embedding `k(W) → L_i` over `k(V)` for a
selected field factor with contraction `Q`. -/
noncomputable def centreFieldComponentAlgHom
    (ι : S →ₐ[R] B) (Q : Ideal S) [Q.IsPrime]
    (m : MaximalSpectrum
      ((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))))
    (hker : RingHom.ker
      (tensorFibreComponentMap
        (F := FractionRing (R ⧸ Q.under R)) ι m) = Q) :
    letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
    letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
      Ideal.Quotient.field m.asIdeal
    FractionRing (S ⧸ Q) →ₐ[FractionRing (R ⧸ Q.under R)]
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) := by
  letI : Algebra (FractionRing (R ⧸ Q.under R))
      (FractionRing (S ⧸ Q)) := centreFieldAlgebra Q
  letI : Field
      (((B ⊗[R] FractionRing (R ⧸ Q.under R)) ⧸
        nilradical (B ⊗[R] FractionRing (R ⧸ Q.under R))) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  exact {
    toRingHom := centreFieldComponentRingHom ι Q m hker
    commutes' := centreFieldComponentRingHom_commutes ι Q m hker }

end Component

#print axioms centreFieldAlgebra
#print axioms centreFieldAlgebra_algebraMap_quotient
#print axioms centreFieldComponentRingHom
#print axioms centreFieldComponentRingHom_algebraMap_quotient
#print axioms centreFieldComponentRingHom_commutes
#print axioms centreFieldComponentAlgHom

end Pcf
