/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Pcf.Stacks.Purity.DiscriminantFiber

/-!
# The disconnected finite-free discriminant criterion

This file supplies the form of the discriminant argument needed in the dimension-two case of
Stacks Tag `0BMA`.  The finite normal algebra in that argument need not be local or connected.
Consequently the local-target criterion in `DiscriminantFiber` is not enough: one must allow the
closed fibre to be a finite product of separable fields.

The proof follows the usual trace-pairing argument.  A nonzero discriminant makes the trace
pairing nondegenerate.  A finite reduced algebra over a field is a finite product of fields, and
nondegeneracy of the product trace pairing forces each field factor to be separable.  Applied to
the closed fibre of a finite-free algebra over a local ring, this proves formal unramifiedness at
every maximal point, with no connectedness or locality hypothesis on the target.
-/

@[expose] public section

open scoped TensorProduct

namespace Pcf.Stacks

universe u v w z

/-- Nondegeneracy of the trace pairing on a product forces nondegeneracy on both factors. -/
theorem Algebra.traceForm_prod_nondegenerate_factors
    {K : Type u} {S : Type v} {T : Type w}
    [CommRing K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    [Module.Free K S] [Module.Finite K S]
    [Module.Free K T] [Module.Finite K T]
    (h : (Algebra.traceForm K (S × T)).Nondegenerate) :
    (Algebra.traceForm K S).Nondegenerate ∧
      (Algebra.traceForm K T).Nondegenerate := by
  constructor
  · constructor
    · intro x hx
      have hzero : (x, (0 : T)) = 0 := h.1 (x, 0) (fun y ↦ by
        simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
          zero_mul, Algebra.trace_prod_apply, map_zero, add_zero] using hx y.1)
      exact congrArg Prod.fst hzero
    · intro y hy
      have hzero : (y, (0 : T)) = 0 := h.2 (y, 0) (fun x ↦ by
        simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
          mul_zero, Algebra.trace_prod_apply, map_zero, add_zero] using hy x.1)
      exact congrArg Prod.fst hzero
  · constructor
    · intro x hx
      have hzero : ((0 : S), x) = 0 := h.1 (0, x) (fun y ↦ by
        simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
          zero_mul, Algebra.trace_prod_apply, map_zero, zero_add] using hx y.2)
      exact congrArg Prod.snd hzero
    · intro y hy
      have hzero : ((0 : S), y) = 0 := h.2 (0, y) (fun x ↦ by
        simpa only [Algebra.traceForm_apply, Prod.fst_mul, Prod.snd_mul,
          mul_zero, Algebra.trace_prod_apply, map_zero, zero_add] using hy x.2)
      exact congrArg Prod.snd hzero

/-- If the trace pairing of a finite product of finite algebras is nondegenerate, the trace
pairing of every factor is nondegenerate. -/
theorem Algebra.traceForm_pi_nondegenerate_factors
    (K : Type u) [Field K]
    (I : Type v) [Finite I]
    (A : I → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Free K (A i)] [∀ i, Module.Finite K (A i)]
    (hA : (Algebra.traceForm K (∀ i, A i)).Nondegenerate) :
    ∀ i, (Algebra.traceForm K (A i)).Nondegenerate := by
  classical
  let P : Type v → Prop := fun J ↦
    ∀ (B : J → Type w)
      [∀ j, CommRing (B j)] [∀ j, Algebra K (B j)]
      [∀ j, Module.Free K (B j)] [∀ j, Module.Finite K (B j)],
      (Algebra.traceForm K (∀ j, B j)).Nondegenerate →
        ∀ j, (Algebra.traceForm K (B j)).Nondegenerate
  apply Finite.induction_empty_option (P := P)
      (fun {J J'} e hJ B _ _ _ _ hB ↦ ?_)
      (fun B _ _ _ _ _ j ↦ ?_)
      (fun {J} _ hJ B _ _ _ _ hB j ↦ ?_)
      I A hA
  · let ePi : (∀ j : J, B (e j)) ≃ₐ[K] (∀ j : J', B j) :=
      AlgEquiv.piCongrLeft K B e
    intro j
    rw [← e.apply_symm_apply j]
    exact hJ (fun j ↦ B (e j))
      (Algebra.traceForm_nondegenerate_of_algEquiv ePi hB) (e.symm j)
  · exact isEmptyElim j
  · let ePi : (∀ j : Option J, B j) ≃ₐ[K]
        B none × (∀ j : J, B (some j)) :=
      { __ := RingEquiv.piOptionEquivProd
        commutes' := fun _ ↦ rfl }
    have hprod : (Algebra.traceForm K
        (B none × (∀ j : J, B (some j)))).Nondegenerate :=
      Algebra.traceForm_nondegenerate_of_algEquiv ePi.symm hB
    obtain ⟨hnone, hsome⟩ :=
      Algebra.traceForm_prod_nondegenerate_factors hprod
    cases j with
    | none => exact hnone
    | some j => exact hJ (fun j ↦ B (some j)) hsome j

/-- A finite-free algebra over a field with nonzero discriminant is formally etale, without any
locality or connectedness hypothesis on the algebra.

This is the disconnected field-fibre input in the discriminant proof of Stacks Tag `0BJF` used
inside the dimension-two case of Tag `0BMA`. -/
theorem Algebra.formallyEtale_of_discr_ne_zero_of_basis_global
    {K : Type u} {T : Type v} {ι : Type z}
    [Field K] [CommRing T] [Algebra K T]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K T) (hdisc : Algebra.discr K b ≠ 0) :
    Algebra.FormallyEtale K T := by
  classical
  letI : Module.Free K T := Module.Free.of_basis b
  letI : Module.Finite K T := Module.Finite.of_basis b
  letI : IsReduced T := Algebra.isReduced_of_discr_ne_zero_of_basis b hdisc
  letI : IsArtinianRing T := isArtinian_of_tower K inferInstance
  have htrace : (Algebra.traceForm K T).Nondegenerate :=
    (Algebra.traceForm K T).nondegenerate_of_det_ne_zero b (by
      simpa only [← Algebra.traceMatrix_of_basis, ← Algebra.discr_def] using hdisc)
  let e : T ≃ₐ[K] (∀ m : MaximalSpectrum T, T ⧸ m.asIdeal) :=
    (IsArtinianRing.equivPi T).restrictScalars K
  letI (m : MaximalSpectrum T) : Field (T ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  letI : Module.Finite K (∀ m : MaximalSpectrum T, T ⧸ m.asIdeal) :=
    Module.Finite.equiv e.toLinearEquiv
  letI (m : MaximalSpectrum T) : Module.Finite K (T ⧸ m.asIdeal) :=
    Module.Finite.of_surjective
      (Pi.evalAlgHom K (fun n : MaximalSpectrum T ↦ T ⧸ n.asIdeal) m).toLinearMap
      (Function.surjective_eval m)
  have hPi : (Algebra.traceForm K
      (∀ m : MaximalSpectrum T, T ⧸ m.asIdeal)).Nondegenerate :=
    Algebra.traceForm_nondegenerate_of_algEquiv e.symm htrace
  have hfactor (m : MaximalSpectrum T) :
      (Algebra.traceForm K (T ⧸ m.asIdeal)).Nondegenerate :=
    Algebra.traceForm_pi_nondegenerate_factors K (MaximalSpectrum T)
      (fun m ↦ T ⧸ m.asIdeal) hPi m
  apply (Algebra.FormallyEtale.iff_exists_algEquiv_prod K T).mpr
  refine ⟨MaximalSpectrum T, inferInstance, (fun m ↦ T ⧸ m.asIdeal),
    (fun _ ↦ Ideal.Quotient.field _), inferInstance, e, ?_⟩
  intro m
  exact ((traceForm_nondegenerate_tfae K (T ⧸ m.asIdeal)).out 3 1).mp (hfactor m)

/-- Formal etaleness of a whole fibre forces unramifiedness at each prime above that fibre for a
finite algebra.  This packages the two pointwise ingredients of the local criterion: the local
fibre is a field, and the residue-field extension is separable. -/
theorem Algebra.isUnramifiedAt_of_formallyEtale_fiber
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.FormallyEtale p.ResidueField (p.Fiber S)] :
    Algebra.IsUnramifiedAt R q := by
  classical
  letI : Algebra.QuasiFiniteAt R q := inferInstance
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  letI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    inferInstance
  let qF : Ideal (p.Fiber S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, inferInstance, inferInstance⟩).asIdeal
  letI : qF.IsPrime := inferInstance
  have hq : q = qF.comap Algebra.TensorProduct.includeRight.toRingHom := by
    exact congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply
      ⟨q, inferInstance, inferInstance⟩).1).symm
  letI : (qF.comap Algebra.TensorProduct.includeRight.toRingHom).IsPrime :=
    inferInstance
  letI : (qF.comap Algebra.TensorProduct.includeRight.toRingHom).LiesOver p := ⟨by
    rw [← hq]
    exact q.over_def p⟩
  let hAlg : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (qF.comap Algebra.TensorProduct.includeRight.toRingHom)) :=
    Localization.AtPrime.algebraOfLiesOver p
      (qF.comap Algebra.TensorProduct.includeRight.toRingHom)
  letI := hAlg
  let hTower : IsScalarTower R (Localization.AtPrime p)
      (Localization.AtPrime (qF.comap Algebra.TensorProduct.includeRight.toRingHom)) :=
    inferInstance
  letI := hTower
  let r : Ideal S := qF.comap Algebra.TensorProduct.includeRight.toRingHom
  letI : Algebra.QuasiFiniteAt R r := inferInstance
  have hr : Algebra.IsUnramifiedAt R r := by
    letI : IsReduced (p.Fiber S) :=
      Algebra.FormallyUnramified.isReduced_of_field p.ResidueField (p.Fiber S)
    letI : IsArtinianRing (p.Fiber S) :=
      isArtinian_of_tower p.ResidueField inferInstance
    letI : IsReduced (Localization.AtPrime qF) := inferInstance
    letI : IsArtinianRing (Localization.AtPrime qF) := inferInstance
    have hlocalField : IsField (Localization.AtPrime qF) :=
      IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime qF)
    have hquotField : IsField
        (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) := by
      convert
        (Ideal.Fiber.localizationAlgEquivQuotient p qF).symm.toRingEquiv.isField hlocalField
      all_goals first | rfl | exact hTower | exact hAlg
    have hmap : p.map (algebraMap R (Localization.AtPrime r)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime r) := by
      apply IsLocalRing.eq_maximalIdeal
      rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
      exact hquotField
    let phi : p.Fiber S →ₐ[p.ResidueField] r.ResidueField :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ ↦ .all _ _)
    have hphi : Function.Surjective phi :=
      Ideal.Fiber.lift_residueField_surjective p r
    letI : (RingHom.ker phi.toRingHom).IsPrime :=
      RingHom.ker_isPrime phi.toRingHom
    letI : Field ((p.Fiber S) ⧸ RingHom.ker phi.toRingHom) :=
      Ideal.Quotient.field (RingHom.ker phi.toRingHom)
    letI : Algebra.IsSeparable p.ResidueField
        ((p.Fiber S) ⧸ RingHom.ker phi.toRingHom) := inferInstance
    let equot : ((p.Fiber S) ⧸ RingHom.ker phi.toRingHom) ≃ₐ[p.ResidueField]
        r.ResidueField := Ideal.quotientKerAlgEquivOfSurjective hphi
    letI : Algebra.IsSeparable p.ResidueField r.ResidueField :=
      Algebra.IsSeparable.of_algHom p.ResidueField
        ((p.Fiber S) ⧸ RingHom.ker phi.toRingHom) equot.symm.toAlgHom
    exact (Algebra.isUnramifiedAt_iff_map_eq R p r).mpr ⟨inferInstance, hmap⟩
  simpa only [hq] using hr

/-- A finite-presentation flat algebra over a local ring with a finite basis and unit
discriminant is etale, with no locality or connectedness assumption on the target algebra.

The closed fibre is a product of separable fields by the global field discriminant criterion.
Every maximal point is therefore etale; openness and stability under generization give the whole
etale locus. -/
theorem Algebra.etale_of_isUnit_discr_of_basis_global
    {R : Type u} {S : Type v} {ι : Type z}
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    Algebra.Etale R S := by
  classical
  letI : Module.Free R S := Module.Free.of_basis b
  letI : Module.Finite R S := Module.Finite.of_basis b
  let m := IsLocalRing.maximalIdeal R
  let bm : Module.Basis ι m.ResidueField (m.Fiber S) :=
    Algebra.TensorProduct.basis m.ResidueField b
  have hdiscm : Algebra.discr m.ResidueField bm ≠ 0 := by
    change Algebra.discr m.ResidueField
      (Algebra.TensorProduct.basis m.ResidueField b) ≠ 0
    rw [Algebra.discr_baseChange]
    exact (hdisc.map (algebraMap R m.ResidueField)).ne_zero
  letI : Algebra.FormallyEtale m.ResidueField (m.Fiber S) :=
    Algebra.formallyEtale_of_discr_ne_zero_of_basis_global bm hdiscm
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro q
  obtain ⟨Q, hQmax, hqQ⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  letI : Q.IsMaximal := hQmax
  letI : Q.IsPrime := hQmax.isPrime
  have hQunderMax : (Q.under R).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hQunder : Q.under R = m :=
    IsLocalRing.eq_maximalIdeal hQunderMax
  letI : Q.LiesOver m := ⟨hQunder.symm⟩
  letI : Algebra.IsUnramifiedAt R Q :=
    Algebra.isUnramifiedAt_of_formallyEtale_fiber m Q
  letI : Algebra.IsEtaleAt R Q :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat Q
  obtain ⟨f, hfQ, hf⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) Q
  have hfq : f ∉ q.asIdeal := fun hfq ↦ hfQ (hqQ hfq)
  exact (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := R) (f := f)).mpr hf hfq

end Pcf.Stacks

#print axioms Pcf.Stacks.Algebra.traceForm_prod_nondegenerate_factors
#print axioms Pcf.Stacks.Algebra.traceForm_pi_nondegenerate_factors
#print axioms Pcf.Stacks.Algebra.formallyEtale_of_discr_ne_zero_of_basis_global
#print axioms Pcf.Stacks.Algebra.isUnramifiedAt_of_formallyEtale_fiber
#print axioms Pcf.Stacks.Algebra.etale_of_isUnit_discr_of_basis_global
