/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPCompositionClosure
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Conjugates over the normal base in the composition argument

This file constructs the actual family of `K`-conjugates of a finite
`A`-extension inside a common Galois field, where `A/K` is normal. The
construction is the conjugate-compositum step of `paper-p.tex`, Lemma
`lem:prime-to-p-compose`.
-/

@[expose] public section

universe u v w x y z

namespace Pcf

set_option linter.style.haveILetI false

/-- Every `K`-conjugate of an intermediate field `B` containing a normal
intermediate field `A` still contains `A`. -/
theorem normalBase_le_galoisConjugate
    (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B) (σ : Gal(Ω/K)) :
    A ≤ B.map (σ : Ω →ₐ[K] Ω) := by
  have hmapA : A.map (σ : Ω →ₐ[K] Ω) = A :=
    (IntermediateField.normal_iff_forall_map_eq' (K := A)).mp inferInstance σ
  rw [← hmapA]
  exact IntermediateField.map_mono (σ : Ω →ₐ[K] Ω) hAB

/-- The `K`-conjugate of `B`, viewed as an `A`-extension. The normality of
`A/K` ensures that this is defined for every `K`-automorphism. -/
def galoisConjugateOverNormalBase
    (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B) (σ : Gal(Ω/K)) : IntermediateField A Ω :=
  IntermediateField.extendScalars
    (normalBase_le_galoisConjugate K Ω A B hAB σ)

@[simp]
theorem galoisConjugateOverNormalBase_restrictScalars
    (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B) (σ : Gal(Ω/K)) :
    (galoisConjugateOverNormalBase K Ω A B hAB σ).restrictScalars K =
      B.map (σ : Ω →ₐ[K] Ω) :=
  IntermediateField.extendScalars_restrictScalars _

/-- Relative degrees of the `A`-extensions in the conjugate family are
identical to the relative degree of `B/A`. -/
theorem galoisConjugateOverNormalBase_finrank
    (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B) (σ : Gal(Ω/K)) :
    Module.finrank A (galoisConjugateOverNormalBase K Ω A B hAB σ) =
      IntermediateField.relfinrank A B := by
  have h := IntermediateField.relfinrank_eq_finrank_of_le
    (normalBase_le_galoisConjugate K Ω A B hAB σ)
  change IntermediateField.relfinrank A
      (B.map (σ : Ω →ₐ[K] Ω)) =
    Module.finrank A (galoisConjugateOverNormalBase K Ω A B hAB σ) at h
  rw [← h, galoisConjugate_relfinrank_of_normal_base K Ω A B σ]

/-- Every field in the conjugate family has prime-to-`p` degree over `A`
when `B/A` does. -/
theorem galoisConjugateOverNormalBase_coprime_finrank
    (p : ℕ) (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B)
    (hdegree : (IntermediateField.relfinrank A B).Coprime p)
    (σ : Gal(Ω/K)) :
    (Module.finrank A
      (galoisConjugateOverNormalBase K Ω A B hAB σ)).Coprime p := by
  rw [galoisConjugateOverNormalBase_finrank K Ω A B hAB σ]
  exact hdegree

/-- Galoisness over the normal base is preserved by every automorphism of
the common Galois ambient field over `K`. The automorphism may act
nontrivially on `A`, so the proof transports both base and extension. -/
theorem isGalois_galoisConjugateOverNormalBase
    (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [Normal K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B) [IsGalois A (IntermediateField.extendScalars hAB)]
    (σ : Gal(Ω/K)) :
    IsGalois A (galoisConjugateOverNormalBase K Ω A B hAB σ) := by
  let C := galoisConjugateOverNormalBase K Ω A B hAB σ
  have hmapA : A.map (σ : Ω →ₐ[K] Ω) = A :=
    (IntermediateField.normal_iff_forall_map_eq' (K := A)).mp inferInstance σ
  let f : A ≃+* A :=
    ((IntermediateField.equivMap A (σ : Ω →ₐ[K] Ω)).trans
      (IntermediateField.equivOfEq hmapA)).toRingEquiv
  let g : IntermediateField.extendScalars hAB ≃+* C := {
    toFun := fun x => ⟨σ x.1, by
      change σ x.1 ∈ B.map (σ : Ω →ₐ[K] Ω)
      exact ⟨x.1, x.2, rfl⟩⟩
    invFun := fun y => ⟨σ.symm y.1, by
      have hy : y.1 ∈ B.map (σ : Ω →ₐ[K] Ω) := y.2
      obtain ⟨z, hz, hzy⟩ := hy
      change σ.symm y.1 ∈ B
      rw [← hzy]
      simpa using hz⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact σ.symm_apply_apply x.1
    right_inv := by
      intro y
      apply Subtype.ext
      exact σ.apply_symm_apply y.1
    map_mul' := by intros; apply Subtype.ext; exact map_mul σ _ _
    map_add' := by intros; apply Subtype.ext; exact map_add σ _ _
  }
  exact IsGalois.of_equiv_equiv (f := f) (g := g) (by
    ext x
    rfl)

/-- The normal closure of `B/K` is the finite compositum of the explicit
family, after forgetting the intermediate base `A`. -/
theorem normalClosure_eq_finset_sup_conjugates_over_normalBase
    (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [FiniteDimensional K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B) :
    IntermediateField.normalClosure K B Ω =
      (Finset.univ : Finset Gal(Ω/K)).sup
        (fun σ => (galoisConjugateOverNormalBase K Ω A B hAB σ).restrictScalars K) := by
  rw [normalClosure_eq_finset_sup_galois_conjugates]
  simp only [galoisConjugateOverNormalBase_restrictScalars]

/-- Restricting scalars in a finite compositum adds the base field `A` to
the compositum viewed over `K`. -/
theorem restrictScalars_finset_sup
    {ι : Type*} (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] (A : IntermediateField K Ω)
    (s : Finset ι) (t : ι → IntermediateField A Ω) :
    ((s.sup t : IntermediateField A Ω).restrictScalars K) =
      A ⊔ s.sup (fun i => (t i).restrictScalars K) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sup_empty, IntermediateField.restrictScalars_bot_eq_self]
      simp
  | @insert i s hi ih =>
      rw [Finset.sup_insert,
        ← IntermediateField.restrictScalars_sup K (t i) (s.sup t), ih,
        Finset.sup_insert]
      ac_rfl

/-- Transport Galoisness from a restricted base inside `B` back to the
same base as an intermediate field of the ambient extension. -/
theorem isGalois_extendScalars_of_restrict
    (F : Type u) (Ω : Type v) [Field F] [Field Ω]
    [Algebra F Ω] (A B : IntermediateField F Ω) (hAB : A ≤ B)
    [IsGalois (A.restrict hAB) B] :
    IsGalois A (IntermediateField.extendScalars hAB) := by
  let f : A.restrict hAB ≃+* A := {
    toFun := fun x => ⟨x.1.1, (IntermediateField.mem_restrict hAB x.1).mp x.2⟩
    invFun := fun x => ⟨⟨x.1, hAB x.2⟩,
      (IntermediateField.mem_restrict hAB ⟨x.1, hAB x.2⟩).mpr x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
  }
  let g : B ≃+* IntermediateField.extendScalars hAB := {
    toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
  }
  exact IsGalois.of_equiv_equiv (f := f) (g := g) (by
    ext x
    rfl)

/-- The corresponding relative field degrees agree under the base and
extension identifications above. -/
theorem finrank_extendScalars_eq_restrict
    (F : Type u) (Ω : Type v) [Field F] [Field Ω]
    [Algebra F Ω] (A B : IntermediateField F Ω) (hAB : A ≤ B) :
    Module.finrank A (IntermediateField.extendScalars hAB) =
      Module.finrank (A.restrict hAB) B := by
  let f : A.restrict hAB ≃+* A := {
    toFun := fun x => ⟨x.1.1, (IntermediateField.mem_restrict hAB x.1).mp x.2⟩
    invFun := fun x => ⟨⟨x.1, hAB x.2⟩,
      (IntermediateField.mem_restrict hAB ⟨x.1, hAB x.2⟩).mpr x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
  }
  let g : B ≃+* IntermediateField.extendScalars hAB := {
    toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
  }
  exact (Algebra.finrank_eq_of_equiv_equiv f g (by ext x; rfl)).symm

/-- An `L`-intermediate Galois extension remains the same extension when
both intermediate fields are viewed over a smaller field `K`. The
underlying subfields and their relative scalar actions coincide. -/
theorem relativeGalois_restrictScalars
    (p : ℕ) (K : Type u) (L : Type w) (Ω : Type v)
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A B : IntermediateField L Ω) (hAB : A ≤ B)
    [IsGalois A (IntermediateField.extendScalars hAB)]
    (hdegree : (Module.finrank A (IntermediateField.extendScalars hAB)).Coprime p) :
    let A₀ := A.restrictScalars K
    let B₀ := B.restrictScalars K
    let hAB₀ : A₀ ≤ B₀ := hAB
    IsGalois A₀ (IntermediateField.extendScalars hAB₀) ∧
      (Module.finrank A₀ (IntermediateField.extendScalars hAB₀)).Coprime p := by
  constructor
  · change IsGalois A (IntermediateField.extendScalars hAB)
    infer_instance
  · change (Module.finrank A (IntermediateField.extendScalars hAB)).Coprime p
    exact hdegree

/-- The normal closure of `B/K` has prime-to-`p` degree if `A/K` has
prime-to-`p` degree and `B/A` is Galois of prime-to-`p` degree. This is the
group-theoretic heart of `paper-p.tex`, Lemma `lem:prime-to-p-compose`:
all `K`-conjugates of `B` remain Galois over the normal base `A`, so their
finite compositum has prime-to-`p` degree over `A`. -/
theorem primeToP_normalClosure_of_relativeGalois
    (p : ℕ) (K : Type u) (Ω : Type v) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [FiniteDimensional K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B)
    (hA : (Module.finrank K A).Coprime p)
    [IsGalois A (IntermediateField.extendScalars hAB)]
    (hB : (IntermediateField.relfinrank A B).Coprime p) :
    (Module.finrank K (IntermediateField.normalClosure K B Ω)).Coprime p := by
  let t : Gal(Ω/K) → IntermediateField A Ω :=
    galoisConjugateOverNormalBase K Ω A B hAB
  let N : IntermediateField A Ω := Finset.univ.sup t
  have hgal : ∀ σ ∈ (Finset.univ : Finset Gal(Ω/K)), IsGalois A (t σ) := by
    intro σ _
    exact isGalois_galoisConjugateOverNormalBase K Ω A B hAB σ
  letI : FiniteDimensional A Ω := Module.Finite.of_restrictScalars_finite K A Ω
  have hfinite : ∀ σ ∈ (Finset.univ : Finset Gal(Ω/K)),
      FiniteDimensional A (t σ) := by
    intro σ _
    infer_instance
  have hdegree : ∀ σ ∈ (Finset.univ : Finset Gal(Ω/K)),
      (Module.finrank A (t σ)).Coprime p := by
    intro σ _
    exact galoisConjugateOverNormalBase_coprime_finrank p K Ω A B hAB hB σ
  obtain ⟨_, hfiniteN, hdegreeN⟩ :=
    primeToP_galois_finset_compositum p A Ω Finset.univ t
      hgal hfinite hdegree
  letI : FiniteDimensional A N := hfiniteN
  have hN : N.restrictScalars K = IntermediateField.normalClosure K B Ω := by
    rw [restrictScalars_finset_sup]
    have hclosure := normalClosure_eq_finset_sup_conjugates_over_normalBase
      K Ω A B hAB
    rw [← hclosure]
    exact sup_eq_right.mpr (hAB.trans (IntermediateField.le_normalClosure B))
  letI : FiniteDimensional K A := inferInstance
  letI : FiniteDimensional K N := FiniteDimensional.trans K A N
  have hdegreeKN : (Module.finrank K N).Coprime p := by
    rw [← Module.finrank_mul_finrank K A N]
    exact (Nat.coprime_mul_iff_left).2 ⟨hA, hdegreeN⟩
  rw [← hN]
  exact hdegreeKN

/-- Any `K`-subextension of `B` has prime-to-`p` monodromy under the
relative-Galois hypotheses above.  The certificate is the normal closure
of `B/K` inside the finite Galois ambient field. -/
theorem isPrimeToPMonodromy_of_relativeGaloisContaining
    (p : ℕ) (K : Type u) (E : Type w) (Ω : Type v)
    [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω]
    [IsGalois K Ω] [FiniteDimensional K Ω]
    (A B : IntermediateField K Ω) [Normal K A]
    (hAB : A ≤ B)
    (hA : (Module.finrank K A).Coprime p)
    [IsGalois A (IntermediateField.extendScalars hAB)]
    (hB : (IntermediateField.relfinrank A B).Coprime p)
    (ι : E →ₐ[K] B) :
    IsPrimeToPMonodromy.{u, w, v} p K E := by
  let C := IntermediateField.normalClosure K B Ω
  letI : IsGalois K C := IsGalois.normalClosure K B Ω
  letI : FiniteDimensional K C := inferInstance
  let ιC : E →ₐ[K] C :=
    (IntermediateField.inclusion (IntermediateField.le_normalClosure B)).comp ι
  exact isPrimeToPMonodromy_of_embedding_into_galois p K E C ιC
    (primeToP_normalClosure_of_relativeGalois p K Ω A B hAB hA hB)

/-- The composition lemma in any finite Galois ambient extension that
contains the top field of the tower. -/
theorem isPrimeToPMonodromy_tower_in_finiteGaloisAmbient
    (p : ℕ) (K : Type u) (L : Type w) (E : Type x) (Ω : Type v)
    [Field K] [Field L] [Field E] [Field Ω]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [Algebra K Ω] [IsGalois K Ω] [FiniteDimensional K Ω]
    (ιE : E →ₐ[K] Ω)
    (hKL : IsPrimeToPMonodromy.{u, w, y} p K L)
    (hLE : IsPrimeToPMonodromy.{w, x, z} p L E) :
    IsPrimeToPMonodromy.{u, x, v} p K E := by
  let ιL : L →ₐ[K] Ω := ιE.comp (IsScalarTower.toAlgHom K L E)
  letI : Algebra L Ω := ιL.toRingHom.toAlgebra
  letI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (ιL.commutes a).symm)
  let ιLE : E →ₐ[L] Ω := {
    toRingHom := ιE.toRingHom
    commutes' := fun a => by
      change ιE (algebraMap L E a) = ιL a
      rfl
  }
  letI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  letI : FiniteDimensional L Ω := Module.Finite.of_restrictScalars_finite K L Ω
  obtain ⟨C₀⟩ := hKL
  letI : FiniteDimensional K L := C₀.finite_extension
  let A : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  obtain ⟨hgalA, hfiniteA, hdegreeA⟩ :=
    primeToPMonodromy_normalClosure_in_galoisAmbient p K L Ω ⟨C₀⟩ ιL
  letI : IsGalois K A := hgalA
  letI : FiniteDimensional K A := hfiniteA
  have hιL_A : ιL.fieldRange ≤ A := ιL.fieldRange_le_normalClosure
  let A₁ : IntermediateField L Ω :=
    A.toSubfield.toIntermediateField (fun a => hιL_A ⟨a, rfl⟩)
  letI : FiniteDimensional L A₁ := inferInstance
  let D : IntermediateField L Ω := IntermediateField.normalClosure L E Ω
  let B₁ : IntermediateField L Ω := D ⊔ A₁
  have hA₁B₁ : A₁ ≤ B₁ := le_sup_right
  obtain ⟨hgalB, _, hdegreeB, ⟨ιB⟩⟩ :=
    primeToPMonodromy_galoisClosure_baseChange p L E Ω hLE ιLE A₁
  letI : IsGalois (A₁.restrict hA₁B₁) B₁ := hgalB
  letI : IsGalois A₁ (IntermediateField.extendScalars hA₁B₁) :=
    isGalois_extendScalars_of_restrict L Ω A₁ B₁ hA₁B₁
  have hdegreeB₁ :
      (Module.finrank A₁ (IntermediateField.extendScalars hA₁B₁)).Coprime p := by
    rw [finrank_extendScalars_eq_restrict L Ω A₁ B₁ hA₁B₁]
    exact hdegreeB
  let A₀ : IntermediateField K Ω := A₁.restrictScalars K
  let B₀ : IntermediateField K Ω := B₁.restrictScalars K
  have hA₀B₀ : A₀ ≤ B₀ := hA₁B₁
  obtain ⟨hgalB₀, hdegreeB₀⟩ :=
    relativeGalois_restrictScalars p K L Ω A₁ B₁ hA₁B₁ hdegreeB₁
  have hA₀_eq_A : A₀ = A := rfl
  letI : Normal K A₀ := hA₀_eq_A ▸ inferInstance
  letI : IsGalois A₀ (IntermediateField.extendScalars hA₀B₀) := hgalB₀
  have hdegreeA₀ : (Module.finrank K A₀).Coprime p := by
    rw [hA₀_eq_A]
    exact hdegreeA
  have hdegreeB₀' : (IntermediateField.relfinrank A₀ B₀).Coprime p := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hA₀B₀]
    exact hdegreeB₀
  let ιB₀ : E →ₐ[K] B₀ := ιB.restrictScalars K
  exact isPrimeToPMonodromy_of_relativeGaloisContaining p K E Ω A₀ B₀
    hA₀B₀ hdegreeA₀ hdegreeB₀' ιB₀

/-- Unrestricted prime-to-`p` monodromy is closed under finite separable
field towers. This is the full field-theoretic composition lemma in
`paper-p.tex`, Lemma `lem:prime-to-p-compose`. -/
theorem isPrimeToPMonodromy_tower
    (p : ℕ) (K : Type u) (L : Type w) (E : Type x)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    (hKL : IsPrimeToPMonodromy.{u, w, y} p K L)
    (hLE : IsPrimeToPMonodromy.{w, x, z} p L E) :
    IsPrimeToPMonodromy.{u, x, u} p K E := by
  obtain ⟨hfinite, hsep, _⟩ :=
    primeToPMonodromy_tower_degree p K L E hKL hLE
  letI : FiniteDimensional K E := hfinite
  letI : Algebra.IsSeparable K E := hsep
  let Ω := SeparableClosure K
  let ιΩ : E →ₐ[K] Ω := IsSepClosed.lift
  letI : Algebra E Ω := ιΩ.toRingHom.toAlgebra
  letI : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    simp)
  let N : IntermediateField K Ω := IntermediateField.normalClosure K E Ω
  letI : IsGalois K N := inferInstance
  letI : FiniteDimensional K N := inferInstance
  let ιN : E →ₐ[K] N := (normalClosure.algHomEquiv K E Ω).symm ιΩ
  exact isPrimeToPMonodromy_tower_in_finiteGaloisAmbient
    p K L E N ιN hKL hLE

#print axioms normalBase_le_galoisConjugate
#print axioms galoisConjugateOverNormalBase_restrictScalars
#print axioms galoisConjugateOverNormalBase_finrank
#print axioms galoisConjugateOverNormalBase_coprime_finrank
#print axioms isGalois_galoisConjugateOverNormalBase
#print axioms normalClosure_eq_finset_sup_conjugates_over_normalBase
#print axioms restrictScalars_finset_sup
#print axioms isGalois_extendScalars_of_restrict
#print axioms finrank_extendScalars_eq_restrict
#print axioms relativeGalois_restrictScalars
#print axioms primeToP_normalClosure_of_relativeGalois
#print axioms isPrimeToPMonodromy_of_relativeGaloisContaining
#print axioms isPrimeToPMonodromy_tower_in_finiteGaloisAmbient
#print axioms isPrimeToPMonodromy_tower

end Pcf
