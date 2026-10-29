/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsSurjective
public import Pcf.Bounding.Divisors
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Hyperplane divisors and their images under projective forms

A nonzero linear form `ℓ` defines the integral effective divisor `V(ℓ)` of
`Proj K[x_0, …, x_N]`, represented by its generic point, the homogeneous prime
`(ℓ)`. This point has codimension one, and its closure is the zero locus of `ℓ`.

When substitution of the defining forms is injective and integral, the actual
projective morphism sends `(ℓ)` to `(ℓ')` as soon as `ℓ'(F)` is divisible by
`ℓ`. The proof uses going down for the integral extension of the integrally
closed polynomial ring and Krull's principal ideal theorem. This is the
image computation used in `paper.tex`, Examples `ex:squaring-PN`, `ex:koch`
and `ex:dupont`; it is an equality of actual scheme points, not only of sets
of field-valued coordinate vectors.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- For an injective integral ring map from an integrally closed domain to a
Noetherian domain, the contraction of a principal prime is the unique nonzero
prime it contains. -/
theorem comap_span_singleton_eq_of_isIntegral
    {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (f : A →+* B) (hinj : Function.Injective f) (hint : f.IsIntegral)
    (ℓ : B) [hq : (Ideal.span {ℓ}).IsPrime]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (hle : p ≤ (Ideal.span {ℓ}).comap f) :
    (Ideal.span {ℓ}).comap f = p := by
  let : Algebra A B := f.toAlgebra
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have : Algebra.IsIntegral A B := ⟨hint⟩
  set Q : Ideal B := Ideal.span {ℓ}
  by_contra hne
  have : Q.LiesOver (Q.under A) := ⟨rfl⟩
  obtain ⟨P, hPQ, hP, hPl⟩ := Q.exists_ideal_lt_liesOver_of_lt (p := p) (q := Q.under A)
    (lt_of_le_of_ne hle (Ne.symm hne))
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply hp
    rw [hPl.over]
    change Ideal.comap (algebraMap A B) ⊥ = ⊥
    refine eq_bot_iff.mpr fun a ha => ?_
    rw [Ideal.mem_comap, Ideal.mem_bot] at ha
    exact (Ideal.mem_bot).mpr (hinj (ha.trans (map_zero f).symm))
  have hQ1 : Q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes Q Q
      ⟨⟨hq, le_rfl⟩, fun _ h _ => h.2⟩
  have hP1 : 1 ≤ P.height := by
    have h0 := Ideal.height_add_one_le_of_lt_of_isPrime (I := (⊥ : Ideal B)) (J := P)
      (bot_lt_iff_ne_bot.mpr hPbot)
    simpa [Ideal.height_bot] using h0
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hPQ
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ P.height + 1 := by gcongr
      _ ≤ Q.height := h2
      _ ≤ 1 := hQ1
  exact absurd this (by norm_num)

variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- A nonzero linear form is prime. -/
theorem prime_of_isHomogeneous_one {σ : Type*} {ℓ : MvPolynomial σ K}
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) : Prime ℓ := by
  refine (irreducible_of_totalDegree_eq_one (hℓ.totalDegree h0) ?_).prime
  intro x hx
  obtain ⟨i, hi⟩ := MvPolynomial.ne_zero_iff.mp h0
  exact isUnit_of_dvd_unit (hx i) (Ne.isUnit hi)

/-- A polynomial vanishing nowhere on the zero set of `ℓ` at one vector is not
divisible by `ℓ`. -/
theorem not_mem_span_of_eval {σ : Type*} {ℓ P : MvPolynomial σ K} (v : σ → K)
    (hv : eval v ℓ = 0) (hP : eval v P ≠ 0) : P ∉ Ideal.span {ℓ} := by
  intro h
  obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp h
  simp [hv] at hP

/-- The generic point of the hyperplane `V(ℓ)`: the homogeneous prime `(ℓ)`.
Relevance is witnessed by a coordinate not divisible by `ℓ`. -/
noncomputable def projLinePoint (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ}) :
    ProjectiveSpectrum polyGrade where
  asHomogeneousIdeal := ⟨Ideal.span {ℓ}, Ideal.homogeneous_span polyGrade _ (by
    rintro x rfl
    exact ⟨1, hℓ⟩)⟩
  isPrime := (Ideal.span_singleton_prime h0).mpr (prime_of_isHomogeneous_one hℓ h0)
  not_irrelevant_le h := hj (h (HomogeneousIdeal.mem_irrelevant_of_mem polyGrade
    Nat.zero_lt_one (isHomogeneous_X K j)))

@[simp] theorem projLinePoint_toIdeal (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ}) :
    (projLinePoint ℓ hℓ h0 j hj).asHomogeneousIdeal.toIdeal = Ideal.span {ℓ} := rfl

/-- Two hyperplane points agree exactly when their principal ideals agree. -/
theorem projLinePoint_eq_iff (ℓ ℓ' : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ})
    (hℓ' : ℓ'.IsHomogeneous 1) (h0' : ℓ' ≠ 0) (j' : Fin n ⊕ Unit)
    (hj' : (X j' : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ'}) :
    projLinePoint ℓ hℓ h0 j hj = projLinePoint ℓ' hℓ' h0' j' hj' ↔
      Ideal.span {ℓ} = Ideal.span {ℓ'} := by
  constructor
  · intro h
    exact congrArg (fun x : ProjectiveSpectrum polyGrade => x.asHomogeneousIdeal.toIdeal) h
  · intro h
    apply ProjectiveSpectrum.ext
    exact HomogeneousIdeal.toIdeal_injective h

/-- Distinct hyperplanes, detected by a vector on the first but not the second. -/
theorem projLinePoint_ne_of_eval (ℓ ℓ' : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ})
    (hℓ' : ℓ'.IsHomogeneous 1) (h0' : ℓ' ≠ 0) (j' : Fin n ⊕ Unit)
    (hj' : (X j' : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ'})
    (v : Fin n ⊕ Unit → K) (hv : eval v ℓ = 0) (hv' : eval v ℓ' ≠ 0) :
    projLinePoint ℓ hℓ h0 j hj ≠ projLinePoint ℓ' hℓ' h0' j' hj' := by
  rw [Ne, projLinePoint_eq_iff]
  intro h
  exact not_mem_span_of_eval v hv hv' (h ▸ Ideal.mem_span_singleton_self ℓ')

/-- The closure of the hyperplane point is the zero locus `V(ℓ)`. -/
theorem projLinePoint_closure (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ}) :
    closure ({projLinePoint ℓ hℓ h0 j hj} : Set (ProjectiveSpectrum polyGrade)) =
      ProjectiveSpectrum.zeroLocus polyGrade {ℓ} := by
  ext y
  rw [← ProjectiveSpectrum.le_iff_mem_closure, ProjectiveSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff]
  change Ideal.span {ℓ} ≤ y.asHomogeneousIdeal.toIdeal ↔ _
  rw [Ideal.span_singleton_le_iff_mem]
  rfl

/-- The hyperplane point has codimension one in projective space. -/
theorem projLinePoint_coheight (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ}) :
    Order.coheight (show AlgebraicGeometry.Proj polyGrade from projLinePoint ℓ hℓ h0 j hj) = 1 := by
  apply le_antisymm
  · have h := Order.coheight_le_coheight_apply_of_strictMono _
      (projPrimeOrderEmbedding (K := K) (n := n)).strictMono
      (show AlgebraicGeometry.Proj polyGrade from projLinePoint ℓ hℓ h0 j hj)
    refine h.trans ?_
    have hprime : (Ideal.span {ℓ}).IsPrime :=
      (Ideal.span_singleton_prime h0).mpr (prime_of_isHomogeneous_one hℓ h0)
    change Order.height (⟨Ideal.span {ℓ}, hprime⟩ :
      PrimeSpectrum (MvPolynomial (Fin n ⊕ Unit) K)) ≤ 1
    rw [← PrimeSpectrum.height_eq_orderHeight]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _
      ⟨⟨hprime, le_rfl⟩, fun _ h _ => h.2⟩
  · rw [Order.one_le_iff_pos, Order.coheight_pos]
    intro hmax
    have hle : (show AlgebraicGeometry.Proj polyGrade from projLinePoint ℓ hℓ h0 j hj) ≤
        (show AlgebraicGeometry.Proj polyGrade from projGenericPoint) := by
      change (projGenericPoint : ProjectiveSpectrum polyGrade) ⤳ projLinePoint ℓ hℓ h0 j hj
      rw [specializes_iff_mem_closure, ← ProjectiveSpectrum.le_iff_mem_closure]
      change (⊥ : HomogeneousIdeal polyGrade) ≤ _
      exact bot_le
    have hge := hmax hle
    change projLinePoint ℓ hℓ h0 j hj ⤳ (projGenericPoint : ProjectiveSpectrum polyGrade) at hge
    rw [specializes_iff_mem_closure, ← ProjectiveSpectrum.le_iff_mem_closure] at hge
    have hge' : Ideal.span {ℓ} ≤ (⊥ : Ideal (MvPolynomial (Fin n ⊕ Unit) K)) := hge
    exact h0 ((Ideal.mem_bot).mp (hge' (Ideal.mem_span_singleton_self ℓ)))

/-- The hyperplane as an integral effective divisor of projective space,
i.e. a codimension-one point. -/
noncomputable def projLineDivisor (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ}) :
    Pcf.SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade) :=
  ⟨projLinePoint ℓ hℓ h0 j hj, projLinePoint_coheight ℓ hℓ h0 j hj⟩

/-- Integrality of substitution follows from integrality of the coordinates. -/
theorem aeval_isIntegral_of_X (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (h : ∀ i, (aeval (R := K) F).toRingHom.IsIntegralElem (X i)) :
    (aeval (R := K) F).toRingHom.IsIntegral := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (C a : MvPolynomial (Fin n ⊕ Unit) K) = (aeval (R := K) F).toRingHom (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  | add P Q hP hQ => exact hP.add _ hQ
  | mul_X P i hP => exact hP.mul _ (h i)

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : FormsCoverProjective F)

/-- The underlying point map of the projective morphism is contraction of
homogeneous primes along substitution. -/
theorem projFormsProjectiveSchemeMap_apply_toIdeal (x : AlgebraicGeometry.Proj polyGrade) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover x : AlgebraicGeometry.Proj polyGrade) :
        ProjectiveSpectrum polyGrade).asHomogeneousIdeal.toIdeal =
      (x : ProjectiveSpectrum polyGrade).asHomogeneousIdeal.toIdeal.comap
        (aeval (R := K) F).toRingHom := rfl

/-- The actual morphism maps the hyperplane `(ℓ)` to the hyperplane `(ℓ')`
whenever `ℓ'(F)` is divisible by `ℓ`, provided substitution is injective and
integral. -/
theorem projFormsProjectiveSchemeMap_projLinePoint
    (hinj : Function.Injective (aeval (R := K) F)) (hint : (aeval (R := K) F).toRingHom.IsIntegral)
    (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ})
    (ℓ' : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ' : ℓ'.IsHomogeneous 1) (h0' : ℓ' ≠ 0) (j' : Fin n ⊕ Unit)
    (hj' : (X j' : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ'})
    (hdiv : aeval F ℓ' ∈ Ideal.span {ℓ}) :
    projFormsProjectiveSchemeMap F d hd hF hcover (projLinePoint ℓ hℓ h0 j hj) =
      projLinePoint ℓ' hℓ' h0' j' hj' := by
  have hq : (Ideal.span {ℓ}).IsPrime :=
    (Ideal.span_singleton_prime h0).mpr (prime_of_isHomogeneous_one hℓ h0)
  have hp : (Ideal.span {ℓ'}).IsPrime :=
    (Ideal.span_singleton_prime h0').mpr (prime_of_isHomogeneous_one hℓ' h0')
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [projFormsProjectiveSchemeMap_apply_toIdeal]
  exact comap_span_singleton_eq_of_isIntegral (aeval (R := K) F).toRingHom hinj hint ℓ
    (Ideal.span {ℓ'}) (by simpa [Ideal.span_singleton_eq_bot] using h0')
    ((Ideal.span_singleton_le_iff_mem _).mpr hdiv)

/-- Image of the whole hyperplane `V(ℓ)` as a closed set. -/
theorem projFormsProjectiveSchemeMap_image_zeroLocus
    (hinj : Function.Injective (aeval (R := K) F)) (hint : (aeval (R := K) F).toRingHom.IsIntegral)
    (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ})
    (ℓ' : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ' : ℓ'.IsHomogeneous 1) (h0' : ℓ' ≠ 0) (j' : Fin n ⊕ Unit)
    (hj' : (X j' : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ'})
    (hdiv : aeval F ℓ' ∈ Ideal.span {ℓ}) :
    (projFormsProjectiveSchemeMap F d hd hF hcover) ''
        ProjectiveSpectrum.zeroLocus polyGrade {ℓ} =
      ProjectiveSpectrum.zeroLocus polyGrade {ℓ'} := by
  rw [← projLinePoint_closure ℓ hℓ h0 j hj, ← projLinePoint_closure ℓ' hℓ' h0' j' hj']
  let ψ := projFormsProjectiveSchemeMap F d hd hF hcover
  change ψ '' closure ({projLinePoint ℓ hℓ h0 j hj} : Set (AlgebraicGeometry.Proj polyGrade)) =
    closure ({projLinePoint ℓ' hℓ' h0' j' hj'} : Set (AlgebraicGeometry.Proj polyGrade))
  rw [(ψ.isClosedMap.closure_image_eq_of_continuous ψ.continuous _).symm,
    Set.image_singleton, projFormsProjectiveSchemeMap_projLinePoint F d hd hF hcover hinj hint
      ℓ hℓ h0 j hj ℓ' hℓ' h0' j' hj' hdiv]

/-- Inverse images of zero loci are zero loci of the substituted equations. -/
theorem projFormsProjectiveSchemeMap_preimage_zeroLocus
    (s : Set (MvPolynomial (Fin n ⊕ Unit) K)) :
    (projFormsProjectiveSchemeMap F d hd hF hcover) ⁻¹'
        ProjectiveSpectrum.zeroLocus polyGrade s =
      ProjectiveSpectrum.zeroLocus polyGrade ((aeval F) '' s) := by
  ext x
  change s ⊆ (aeval F) ⁻¹' (x.asHomogeneousIdeal : Set _) ↔
    (aeval F) '' s ⊆ (x.asHomogeneousIdeal : Set _)
  exact Set.image_subset_iff.symm

#print axioms comap_span_singleton_eq_of_isIntegral
#print axioms prime_of_isHomogeneous_one
#print axioms projLinePoint
#print axioms projLinePoint_eq_iff
#print axioms projLinePoint_ne_of_eval
#print axioms projLinePoint_closure
#print axioms projLinePoint_coheight
#print axioms projLineDivisor
#print axioms aeval_isIntegral_of_X
#print axioms projFormsProjectiveSchemeMap_apply_toIdeal
#print axioms projFormsProjectiveSchemeMap_projLinePoint
#print axioms projFormsProjectiveSchemeMap_image_zeroLocus
#print axioms projFormsProjectiveSchemeMap_preimage_zeroLocus
end Pcf.PaperCharZero
