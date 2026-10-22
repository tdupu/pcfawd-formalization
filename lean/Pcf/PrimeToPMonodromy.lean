/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime-to-characteristic monodromy of a finite field extension

This is the field-theoretic condition in `latex/paper-p.tex`, Definition
`def:prime-to-p`. The extension must be separable, and a finite normal closure
must have degree coprime to `p`. The explicit normal-closure certificate
records the algebraic embedding of the given extension into its closure.
-/

@[expose] public section

universe u v w x

namespace Pcf

set_option linter.style.haveILetI false

/-- A chosen finite Galois closure of `L/F` whose degree is prime to `p`.
The `IsNormalClosure` field enforces minimality, while `embedding` identifies
the original extension with a subextension of this chosen closure. -/
structure PrimeToPMonodromyCertificate (p : ℕ)
    (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L] where
  Closure : Type w
  [field : Field Closure]
  [algebra : Algebra F Closure]
  [normalClosure : IsNormalClosure F L Closure]
  [finiteClosure : FiniteDimensional F Closure]
  embedding : L →ₐ[F] Closure
  separable : Algebra.IsSeparable F L
  coprimeDegree : (Module.finrank F Closure).Coprime p

attribute [instance] PrimeToPMonodromyCertificate.field
  PrimeToPMonodromyCertificate.algebra
  PrimeToPMonodromyCertificate.normalClosure
  PrimeToPMonodromyCertificate.finiteClosure

/-- A separable normal closure is Galois. -/
theorem PrimeToPMonodromyCertificate.isGaloisClosure
    {p : ℕ} {F : Type u} {L : Type v}
    [Field F] [Field L] [Algebra F L]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p F L) :
    IsGalois F C.Closure := by
  letI := C.field
  letI := C.algebra
  letI := C.normalClosure
  letI : Algebra.IsSeparable F L := C.separable
  have htop : IntermediateField.normalClosure F L C.Closure = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff).mp inferInstance |>.2
  have hsep : Algebra.IsSeparable F C.Closure := by
    have hsep' : Algebra.IsSeparable F
        (IntermediateField.normalClosure F L C.Closure) := inferInstance
    rw [htop] at hsep'
    exact Algebra.IsSeparable.of_algHom F
      (⊤ : IntermediateField F C.Closure)
      (IntermediateField.topEquiv :
        (⊤ : IntermediateField F C.Closure) ≃ₐ[F] C.Closure).symm.toAlgHom
  exact isGalois_iff.mpr ⟨hsep,
    IsNormalClosure.normal (F := F) (K := L) (L := C.Closure)⟩

/-- Prime-to-`p` monodromy of a field extension: existence of a finite
normal closure of degree prime to `p`, together with separability of the
original extension. -/
def IsPrimeToPMonodromy (p : ℕ)
    (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L] : Prop :=
  Nonempty (PrimeToPMonodromyCertificate.{u, v, w} p F L)

/-- A field embedding into a finite extension makes the source extension
finite, and its degree divides the larger degree. -/
theorem finrank_dvd_finrank_of_algHom
    (F : Type u) (L : Type v) (N : Type w)
    [Field F] [Field L] [Field N] [Algebra F L] [Algebra F N]
    (ι : L →ₐ[F] N) :
    Module.finrank F L ∣ Module.finrank F N := by
  letI : Algebra L N := ι.toRingHom.toAlgebra
  letI : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (ι.commutes x).symm)
  exact Module.finrank_dvd_finrank_right F L N

/-- The extension represented by a finite normal-closure certificate is finite. -/
theorem PrimeToPMonodromyCertificate.finite_extension
    {p : ℕ} {F : Type u} {L : Type v}
    [Field F] [Field L] [Algebra F L]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p F L) :
    FiniteDimensional F L := by
  letI := C.field
  letI := C.algebra
  exact FiniteDimensional.of_injective C.embedding.toLinearMap C.embedding.injective

/-- A subextension of a finite Galois extension of degree prime to `p`
has prime-to-`p` monodromy. Its normal closure is taken inside the given
Galois extension. -/
theorem isPrimeToPMonodromy_of_embedding_into_galois
    (p : ℕ) (F : Type u) (L : Type v) (N : Type w)
    [Field F] [Field L] [Field N] [Algebra F L] [Algebra F N]
    [IsGalois F N] [FiniteDimensional F N]
    (ι : L →ₐ[F] N) (hdegree : (Module.finrank F N).Coprime p) :
    IsPrimeToPMonodromy.{u, v, w} p F L := by
  letI : FiniteDimensional F L :=
    FiniteDimensional.of_injective ι.toLinearMap ι.injective
  letI : Nonempty (L →ₐ[F] N) := ⟨ι⟩
  let C := IntermediateField.normalClosure F L N
  letI : IsNormalClosure F L C := inferInstance
  letI : FiniteDimensional F C := inferInstance
  let ιC : L →ₐ[F] C := (normalClosure.algHomEquiv F L N).symm ι
  have hdiv : Module.finrank F C ∣ Module.finrank F N :=
    finrank_dvd_finrank_of_algHom F C N C.val
  exact ⟨{
    Closure := C
    embedding := ιC
    separable := Algebra.IsSeparable.of_algHom F N ι
    coprimeDegree := Nat.Coprime.of_dvd_left hdiv hdegree
  }⟩

/-- Prime-to-`p` monodromy descends to every intermediate field of the
original extension. -/
theorem isPrimeToPMonodromy_of_algHom
    (p : ℕ) (F : Type u) (E : Type x) (L : Type v)
    [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    (hmono : IsPrimeToPMonodromy.{u, v, w} p F L)
    (ι : E →ₐ[F] L) :
    IsPrimeToPMonodromy.{u, x, w} p F E := by
  obtain ⟨C⟩ := hmono
  letI := C.field
  letI := C.algebra
  letI := C.finiteClosure
  letI : IsGalois F C.Closure := C.isGaloisClosure
  exact isPrimeToPMonodromy_of_embedding_into_galois p F E C.Closure
    (C.embedding.comp ι) C.coprimeDegree

/-- The degree of the original extension is prime to `p` whenever its
Galois closure has prime-to-`p` degree. -/
theorem PrimeToPMonodromyCertificate.coprime_extension_degree
    {p : ℕ} {F : Type u} {L : Type v}
    [Field F] [Field L] [Algebra F L]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p F L) :
    (Module.finrank F L).Coprime p := by
  letI := C.field
  letI := C.algebra
  exact Nat.Coprime.of_dvd_left
    (finrank_dvd_finrank_of_algHom F L C.Closure C.embedding)
    C.coprimeDegree

/-- For prime `p`, the original extension degree is not divisible by `p`. -/
theorem PrimeToPMonodromyCertificate.prime_not_dvd_extension_degree
    {p : ℕ} (hp : p.Prime) {F : Type u} {L : Type v}
    [Field F] [Field L] [Algebra F L]
    (C : PrimeToPMonodromyCertificate.{u, v, w} p F L) :
    ¬ p ∣ Module.finrank F L :=
  hp.coprime_iff_not_dvd.mp C.coprime_extension_degree.symm

/-- The normal-closure degree in the certificate is independent of the
chosen finite normal closure. This is the invariance needed to match the
manuscript's phrase “its Galois closure has degree prime to `p`.” -/
theorem isPrimeToPMonodromy_iff_fixedClosure
    (p : ℕ) (F : Type u) (L : Type v) (N : Type w)
    [Field F] [Field L] [Field N] [Algebra F L] [Algebra F N]
    [IsNormalClosure F L N] [FiniteDimensional F N]
    (ι : L →ₐ[F] N) :
    IsPrimeToPMonodromy.{u, v, w} p F L ↔
      Algebra.IsSeparable F L ∧ (Module.finrank F N).Coprime p := by
  constructor
  · rintro ⟨C⟩
    letI := C.field
    letI := C.algebra
    letI := C.normalClosure
    letI := C.finiteClosure
    have hdegree : Module.finrank F C.Closure = Module.finrank F N :=
      (IsNormalClosure.equiv (F := F) (K := L) (L := C.Closure)
        (L' := N)).toLinearEquiv.finrank_eq
    exact ⟨C.separable, hdegree ▸ C.coprimeDegree⟩
  · rintro ⟨hsep, hcoprime⟩
    exact ⟨{
      Closure := N
      embedding := ι
      separable := hsep
      coprimeDegree := hcoprime
    }⟩

#print axioms PrimeToPMonodromyCertificate
#print axioms PrimeToPMonodromyCertificate.isGaloisClosure
#print axioms IsPrimeToPMonodromy
#print axioms finrank_dvd_finrank_of_algHom
#print axioms PrimeToPMonodromyCertificate.finite_extension
#print axioms isPrimeToPMonodromy_of_embedding_into_galois
#print axioms isPrimeToPMonodromy_of_algHom
#print axioms PrimeToPMonodromyCertificate.coprime_extension_degree
#print axioms PrimeToPMonodromyCertificate.prime_not_dvd_extension_degree
#print axioms isPrimeToPMonodromy_iff_fixedClosure

end Pcf
