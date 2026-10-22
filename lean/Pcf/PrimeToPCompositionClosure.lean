/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPComposition
public import Mathlib.FieldTheory.Relrank

/-!
# Normal closures in the prime-to-characteristic composition argument

The `E/L` certificate in `latex/paper-p.tex`, Lemma `lem:prime-to-p-compose`,
can be realized inside any ambient Galois extension containing `E`.  Its
normal closure there still has prime-to-`p` degree.  Compositum with a finite
base extension preserves that property.  These are the first two closure
steps of the paper's composition proof; the remaining step takes all
`K`-conjugates and proves their compositum is normal over `K`.
-/

@[expose] public section

universe u v w x y

namespace Pcf

set_option linter.style.haveILetI false

/-- In a finite Galois ambient extension, the normal closure of an
intermediate field is the finite compositum of all its bottom-field
conjugates.  This is the finite-conjugate construction used in the last
paragraph of `paper-p.tex`, Lemma `lem:prime-to-p-compose`. -/
theorem normalClosure_eq_finset_sup_galois_conjugates
    (K : Type u) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [FiniteDimensional K Ω]
    (B : IntermediateField K Ω) :
    IntermediateField.normalClosure K B Ω =
      (Finset.univ : Finset Gal(Ω/K)).sup
        (fun σ => B.map (σ : Ω →ₐ[K] Ω)) := by
  classical
  rw [IntermediateField.normalClosure_def'', Finset.sup_univ_eq_iSup]

/-- When `A/K` is normal, a `K`-conjugate of `B` has the same relative
degree over `A`. This is the degree-invariance input for the conjugates
in the composition lemma. -/
theorem galoisConjugate_relfinrank_of_normal_base
    (K : Type u) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (σ : Gal(Ω/K)) :
    IntermediateField.relfinrank A
        (B.map (σ : Ω →ₐ[K] Ω)) =
      IntermediateField.relfinrank A B := by
  have hmapA : A.map (σ : Ω →ₐ[K] Ω) = A :=
    (IntermediateField.normal_iff_forall_map_eq' (K := A)).mp inferInstance σ
  calc
    A.relfinrank (B.map (σ : Ω →ₐ[K] Ω)) =
        (A.map (σ : Ω →ₐ[K] Ω)).relfinrank
          (B.map (σ : Ω →ₐ[K] Ω)) := by rw [hmapA]
    _ = A.relfinrank B :=
      IntermediateField.relfinrank_map_map A B (σ : Ω →ₐ[K] Ω)

/-- Prime-to-`p` relative degree survives every `K`-conjugate when the
base intermediate field is normal over `K`. -/
theorem galoisConjugate_coprime_relfinrank_of_normal_base
    (p : ℕ) (K : Type u) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hdegree : (IntermediateField.relfinrank A B).Coprime p)
    (σ : Gal(Ω/K)) :
    (IntermediateField.relfinrank A
      (B.map (σ : Ω →ₐ[K] Ω))).Coprime p := by
  rw [galoisConjugate_relfinrank_of_normal_base K Ω A B σ]
  exact hdegree

/-- A prime-to-`p` Galois-closure certificate for `E/L` realizes the normal
closure inside any Galois ambient field containing `E`.  Its degree remains
prime to `p` because finite normal closures are unique up to equivalence. -/
theorem primeToPMonodromy_normalClosure_in_galoisAmbient
    (p : ℕ) (L : Type u) (E : Type v) (Ω : Type w)
    [Field L] [Field E] [Field Ω]
    [Algebra L E] [Algebra L Ω] [IsGalois L Ω]
    (hmono : IsPrimeToPMonodromy.{u, v, x} p L E)
    (ι : E →ₐ[L] Ω) :
    let B := IntermediateField.normalClosure L E Ω
    IsGalois L B ∧ FiniteDimensional L B ∧
      (Module.finrank L B).Coprime p := by
  obtain ⟨C⟩ := hmono
  letI : FiniteDimensional L E := C.finite_extension
  letI : Nonempty (E →ₐ[L] Ω) := ⟨ι⟩
  let B := IntermediateField.normalClosure L E Ω
  letI : IsNormalClosure L E B := inferInstance
  letI : FiniteDimensional L B := inferInstance
  letI : Algebra.IsSeparable L E := C.separable
  letI : IsGalois L B := IsGalois.normalClosure L E Ω
  letI := C.field
  letI := C.algebra
  letI := C.normalClosure
  letI := C.finiteClosure
  have hdegreeEq : Module.finrank L C.Closure = Module.finrank L B :=
    (IsNormalClosure.equiv (F := L) (K := E) (L := C.Closure)
      (L' := B)).toLinearEquiv.finrank_eq
  have hdegree : (Module.finrank L B).Coprime p := by
    simpa only [← hdegreeEq] using C.coprimeDegree
  exact ⟨inferInstance, inferInstance, hdegree⟩

/-- Base changing the actual Galois closure of `E/L` to a finite extension
`A/L` gives a finite Galois extension of `A` with prime-to-`p` degree.
In the manuscript, `A` is the Galois closure of `L/K`. -/
theorem primeToPMonodromy_galoisClosure_baseChange
    (p : ℕ) (L : Type u) (E : Type v) (Ω : Type w)
    [Field L] [Field E] [Field Ω]
    [Algebra L E] [Algebra L Ω] [IsGalois L Ω]
    (hmono : IsPrimeToPMonodromy.{u, v, x} p L E)
    (ι : E →ₐ[L] Ω)
    (A : IntermediateField L Ω) [FiniteDimensional L A] :
    let B := IntermediateField.normalClosure L E Ω
    let C := B ⊔ A
    let A' := A.restrict (show A ≤ C from le_sup_right)
    IsGalois A' C ∧ FiniteDimensional A' C ∧
      (Module.finrank A' C).Coprime p ∧ Nonempty (E →ₐ[L] C) := by
  obtain ⟨CE⟩ := hmono
  letI : FiniteDimensional L E := CE.finite_extension
  letI : Nonempty (E →ₐ[L] Ω) := ⟨ι⟩
  let B := IntermediateField.normalClosure L E Ω
  obtain ⟨hgalB, hfiniteB, hdegreeB⟩ :=
    primeToPMonodromy_normalClosure_in_galoisAmbient p L E Ω ⟨CE⟩ ι
  letI : IsGalois L B := hgalB
  letI : FiniteDimensional L B := hfiniteB
  let C := B ⊔ A
  let A' := A.restrict (show A ≤ C from le_sup_right)
  obtain ⟨hgal, hdegree⟩ := primeToP_galois_base_change p L Ω B A hdegreeB
  have hfinite : FiniteDimensional A' C := by
    letI : FiniteDimensional L C := inferInstance
    exact Module.Finite.of_restrictScalars_finite L A' C
  let ιB : E →ₐ[L] B := (normalClosure.algHomEquiv L E Ω).symm ι
  let ιC : E →ₐ[L] C :=
    (IntermediateField.inclusion (show B ≤ C from le_sup_left)).comp ιB
  exact ⟨hgal, hfinite, hdegree, ⟨ιC⟩⟩

/-- The base-changed closure itself has prime-to-`p` monodromy over the
new base.  The Galois extension produced above serves as its own closure. -/
theorem isPrimeToPMonodromy_galoisClosure_baseChange
    (p : ℕ) (L : Type u) (E : Type v) (Ω : Type w)
    [Field L] [Field E] [Field Ω]
    [Algebra L E] [Algebra L Ω] [IsGalois L Ω]
    (hmono : IsPrimeToPMonodromy.{u, v, x} p L E)
    (ι : E →ₐ[L] Ω)
    (A : IntermediateField L Ω) [FiniteDimensional L A] :
    let B := IntermediateField.normalClosure L E Ω
    let C := B ⊔ A
    let A' := A.restrict (show A ≤ C from le_sup_right)
    IsPrimeToPMonodromy.{w, w, w} p A' C := by
  let B := IntermediateField.normalClosure L E Ω
  let C := B ⊔ A
  let A' := A.restrict (show A ≤ C from le_sup_right)
  obtain ⟨hgal, hfinite, hdegree, _⟩ :=
    primeToPMonodromy_galoisClosure_baseChange p L E Ω hmono ι A
  letI : IsGalois A' C := hgal
  letI : FiniteDimensional A' C := hfinite
  exact isPrimeToPMonodromy_of_embedding_into_galois p A' C C
    (AlgHom.id A' C) hdegree

/-- The final degree deduction in the composition lemma: a finite compositum
of `A`-Galois conjugate closures of prime-to-`p` degree has prime-to-`p`
degree over `K` when `A/K` does.  If that compositum is normal over `K` and
contains `E`, it is a valid Galois ambient field for the closure of `E/K`.
The construction and `K`-normality of the conjugate family remain the
unformalized step of the unrestricted composition lemma. -/
theorem primeToPMonodromy_of_finiteConjugateCompositum
    {ι : Type y} (p : ℕ)
    (K : Type u) (A : Type v) (Ω : Type w) (E : Type x)
    [Field K] [Field A] [Field Ω] [Field E]
    [Algebra K A] [Algebra A Ω] [Algebra K E]
    [FiniteDimensional K A]
    (hA : (Module.finrank K A).Coprime p)
    (s : Finset ι) (t : ι → IntermediateField A Ω)
    (hgal : ∀ i ∈ s, IsGalois A (t i))
    (hfinite : ∀ i ∈ s, FiniteDimensional A (t i))
    (hdegree : ∀ i ∈ s, (Module.finrank A (t i)).Coprime p)
    [Algebra K (s.sup t : IntermediateField A Ω)]
    [IsScalarTower K A (s.sup t : IntermediateField A Ω)]
    [IsGalois K (s.sup t : IntermediateField A Ω)]
    (ιE : E →ₐ[K] (s.sup t : IntermediateField A Ω)) :
    IsPrimeToPMonodromy.{u, x, w} p K E := by
  let N := (s.sup t : IntermediateField A Ω)
  obtain ⟨_, hfiniteAN, hdegreeAN⟩ :=
    primeToP_galois_finset_compositum p A Ω s t hgal hfinite hdegree
  letI : FiniteDimensional A N := hfiniteAN
  letI : FiniteDimensional K N := FiniteDimensional.trans K A N
  have hdegreeKN : (Module.finrank K N).Coprime p := by
    rw [← Module.finrank_mul_finrank K A N]
    exact (Nat.coprime_mul_iff_left).2 ⟨hA, hdegreeAN⟩
  exact isPrimeToPMonodromy_of_embedding_into_galois p K E N ιE hdegreeKN

#print axioms normalClosure_eq_finset_sup_galois_conjugates
#print axioms galoisConjugate_relfinrank_of_normal_base
#print axioms galoisConjugate_coprime_relfinrank_of_normal_base
#print axioms primeToPMonodromy_normalClosure_in_galoisAmbient
#print axioms primeToPMonodromy_galoisClosure_baseChange
#print axioms isPrimeToPMonodromy_galoisClosure_baseChange
#print axioms primeToPMonodromy_of_finiteConjugateCompositum

end Pcf
