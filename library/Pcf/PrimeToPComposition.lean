/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPMonodromy
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Coset.Card

/-!
# Prime-to-characteristic field towers

This file develops the degree and separability consequences of the tower in
`latex/paper-p.tex`, Lemma `lem:prime-to-p-compose` (Composition). The further
normal-closure assertion needs a Galois compositum construction over the bottom
field; the degree of the composite alone does not imply it.
-/

@[expose] public section

universe u v w x y

namespace Pcf

set_option linter.style.haveILetI false

/-- Finite separable field extensions with prime-to-`p` monodromy in two
successive steps give a finite separable composite of degree prime to `p`.
This is the tower calculation in `paper-p.tex`, Lemma
`lem:prime-to-p-compose`; it does not claim the stronger normal-closure bound. -/
theorem primeToPMonodromy_tower_degree
    (p : ℕ) (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    (hKL : IsPrimeToPMonodromy.{u, v, x} p K L)
    (hLE : IsPrimeToPMonodromy.{v, w, y} p L E) :
    FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
      (Module.finrank K E).Coprime p := by
  obtain ⟨CKL⟩ := hKL
  obtain ⟨CLE⟩ := hLE
  letI : FiniteDimensional K L := CKL.finite_extension
  letI : FiniteDimensional L E := CLE.finite_extension
  have hfinite : FiniteDimensional K E := FiniteDimensional.trans K L E
  letI : Algebra.IsSeparable K L := CKL.separable
  letI : Algebra.IsSeparable L E := CLE.separable
  have hsep : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K L E
  have hdegree : (Module.finrank K E).Coprime p := by
    rw [← Module.finrank_mul_finrank K L E]
    exact (Nat.coprime_mul_iff_left).2
      ⟨CKL.coprime_extension_degree, CLE.coprime_extension_degree⟩
  exact ⟨hfinite, hsep, hdegree⟩

/-- The compositum of two finite Galois extensions of prime-to-`p` degree
again has prime-to-`p` degree. The proof embeds its Galois group into the
product of the two factor Galois groups; this is the degree calculation used
for the finitely many conjugates in `paper-p.tex`, Lemma
`lem:prime-to-p-compose`. -/
theorem primeToP_galois_compositum
    (p : ℕ) (F : Type u) (N : Type v)
    [Field F] [Field N] [Algebra F N]
    (A B : IntermediateField F N)
    [IsGalois F A] [IsGalois F B]
    [FiniteDimensional F A] [FiniteDimensional F B]
    (hA : (Module.finrank F A).Coprime p)
    (hB : (Module.finrank F B).Coprime p) :
    IsGalois F (A ⊔ B : IntermediateField F N) ∧
      (Module.finrank F (A ⊔ B : IntermediateField F N)).Coprime p := by
  have hgal : IsGalois F (A ⊔ B : IntermediateField F N) :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  letI : IsGalois F (A ⊔ B : IntermediateField F N) := hgal
  have hdiv : Nat.card Gal((A ⊔ B : IntermediateField F N)/F) ∣
      Nat.card (Gal(A/F) × Gal(B/F)) :=
    Subgroup.card_dvd_of_injective (IntermediateField.restrictNormalHomSupProd A B)
      (IntermediateField.restrictNormalHomSupProd_injective A B)
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank F A,
    IsGalois.card_aut_eq_finrank F B,
    IsGalois.card_aut_eq_finrank F (A ⊔ B : IntermediateField F N)] at hdiv
  exact ⟨hgal, Nat.Coprime.of_dvd_left hdiv
    ((Nat.coprime_mul_iff_left).2 ⟨hA, hB⟩)⟩

/-- A finite compositum of finite Galois extensions of degree prime to `p`
has the same properties. This is the numerical part of the conjugate
compositum in `paper-p.tex`, Lemma `lem:prime-to-p-compose`. -/
theorem primeToP_galois_finset_compositum
    {ι : Type x} (p : ℕ) (F : Type u) (N : Type v)
    [Field F] [Field N] [Algebra F N]
    (s : Finset ι) (t : ι → IntermediateField F N)
    (hgal : ∀ i ∈ s, IsGalois F (t i))
    (hfinite : ∀ i ∈ s, FiniteDimensional F (t i))
    (hdegree : ∀ i ∈ s, (Module.finrank F (t i)).Coprime p) :
    IsGalois F (s.sup t : IntermediateField F N) ∧
      FiniteDimensional F (s.sup t : IntermediateField F N) ∧
      (Module.finrank F (s.sup t : IntermediateField F N)).Coprime p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change IsGalois F (⊥ : IntermediateField F N) ∧
        FiniteDimensional F (⊥ : IntermediateField F N) ∧
        (Module.finrank F (⊥ : IntermediateField F N)).Coprime p
      exact ⟨inferInstance,
        FiniteDimensional.of_finrank_pos (by simp), by simp⟩
  | @insert i s hi ih =>
      have hgis : IsGalois F (t i) := hgal i (Finset.mem_insert_self ..)
      have hfis : FiniteDimensional F (t i) := hfinite i (Finset.mem_insert_self ..)
      have hdis : (Module.finrank F (t i)).Coprime p :=
        hdegree i (Finset.mem_insert_self ..)
      obtain ⟨hgs, hfs, hds⟩ := ih
        (fun j hj => hgal j (Finset.mem_insert_of_mem hj))
        (fun j hj => hfinite j (Finset.mem_insert_of_mem hj))
        (fun j hj => hdegree j (Finset.mem_insert_of_mem hj))
      letI : IsGalois F (t i) := hgis
      letI : FiniteDimensional F (t i) := hfis
      letI : IsGalois F (s.sup t : IntermediateField F N) := hgs
      letI : FiniteDimensional F (s.sup t : IntermediateField F N) := hfs
      obtain ⟨hgc, hdc⟩ :=
        primeToP_galois_compositum p F N (t i) (s.sup t) hdis hds
      rw [Finset.sup_insert]
      exact ⟨hgc, inferInstance, hdc⟩

/-- Base changing a finite Galois extension along a finite field extension
preserves prime-to-`p` degree. This is the first base-change step in the
composition proof of `paper-p.tex`, Lemma `lem:prime-to-p-compose`. -/
theorem primeToP_galois_base_change
    (p : ℕ) (F : Type u) (N : Type v)
    [Field F] [Field N] [Algebra F N]
    (A B : IntermediateField F N)
    [IsGalois F A] [FiniteDimensional F A] [FiniteDimensional F B]
    (hA : (Module.finrank F A).Coprime p) :
    let C : IntermediateField F N := A ⊔ B
    let B' : IntermediateField F C := B.restrict le_sup_right
    IsGalois B' C ∧ (Module.finrank B' C).Coprime p := by
  let C : IntermediateField F N := A ⊔ B
  let A' : IntermediateField F C := A.restrict le_sup_left
  let B' : IntermediateField F C := B.restrict le_sup_right
  have htop : A' ⊔ B' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
      IntermediateField.lift_sup, IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right]
  letI : IsGalois F A' := IsGalois.of_algEquiv
    (IntermediateField.restrictAlgEquiv le_sup_left)
  letI : FiniteDimensional F A' :=
    FiniteDimensional.of_injective
      (IntermediateField.restrictAlgEquiv le_sup_left).symm.toLinearMap
      (IntermediateField.restrictAlgEquiv le_sup_left).symm.injective
  letI : FiniteDimensional F C := inferInstance
  letI : FiniteDimensional B' C := Module.Finite.of_restrictScalars_finite F B' C
  have hgal' : IsGalois B' C := IsGalois.sup_right A' B' htop
  letI : IsGalois B' C := hgal'
  have hdiv : Nat.card Gal(C/B') ∣ Nat.card Gal(A'/F) :=
    Subgroup.card_dvd_of_injective
      (IntermediateField.restrictRestrictAlgEquivMapHom F A' B' C)
      (IntermediateField.restrictRestrictAlgEquivMapHom_injective
        (F := F) (E := C) A' B' htop)
  have hdegree' : (Module.finrank B' C).Coprime p := by
    rw [IsGalois.card_aut_eq_finrank F A',
      ← (IntermediateField.restrictAlgEquiv le_sup_left).toLinearEquiv.finrank_eq,
      IsGalois.card_aut_eq_finrank B' C] at hdiv
    exact Nat.Coprime.of_dvd_left hdiv hA
  exact ⟨hgal', hdegree'⟩

/-- The composition lemma holds when the composite extension is already
Galois over the bottom field. The general case requires proving that the
normal closure has prime-to-`p` degree. -/
theorem isPrimeToPMonodromy_tower_of_isGalois
    (p : ℕ) (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [IsGalois K E]
    (hKL : IsPrimeToPMonodromy.{u, v, x} p K L)
    (hLE : IsPrimeToPMonodromy.{v, w, y} p L E) :
    IsPrimeToPMonodromy.{u, w, w} p K E := by
  obtain ⟨hfinite, _, hdegree⟩ :=
    primeToPMonodromy_tower_degree p K L E hKL hLE
  letI : FiniteDimensional K E := hfinite
  exact isPrimeToPMonodromy_of_embedding_into_galois p K E E
    (AlgHom.id K E) hdegree

#print axioms primeToPMonodromy_tower_degree
#print axioms primeToP_galois_compositum
#print axioms primeToP_galois_finset_compositum
#print axioms primeToP_galois_base_change
#print axioms isPrimeToPMonodromy_tower_of_isGalois

end Pcf
