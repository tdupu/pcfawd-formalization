/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Pcf.Stacks.Purity.HypersurfaceLifting
public import Pcf.Stacks.Purity.Tag0BMAClauses
public import Pcf.Stacks.Abhyankar.StrictHenselizationQuotient
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Pcf.Stacks.Purity.LocalEtaleSectionLifting
public import Pcf.Stacks.Purity.IntegralIdempotentPolynomial
public import Pcf.Stacks.Purity.FiniteAlgebraIdempotents

/-!
# Lifting finite etale algebras over a henselian local ring

This file proves the essential-surjectivity half of Stacks Tag `09ZL` (Lemma 15.13.2) in the
case of a henselian local ring `A` and an ideal `I ⊆ m_A`: every finite etale `A/I`-algebra is
`A/I ⊗_A B` for a finite etale `A`-algebra `B`.  For the hypersurface `I = (x)` it is repackaged
as essential surjectivity of the scheme-theoretic restriction functor
`restrictFiniteEtaleToHypersurface`, which is the first input of
`hypersurfaceFiniteEtaleLifting_of_essSurj_of_fullyFaithful` (Stacks Tags `0BLS`/`0BLM`).

## Main results

* `exists_monic_factorization_lift_of_henselian`: coprime monic factorizations lift over a local
  ring henselian along `I` (the factorization condition of Stacks Tag `09XE`).  The proof applies
  the local section lifting of Tag `09XI` (`exists_algHom_lift_of_etale_of_isLocalRing`) to
  Mathlib's etale universal coprime factorization ring.
* `exists_isIdempotentElem_sub_mem_of_isIntegral_of_henselian`: idempotents lift in integral
  algebras over such a pair (existence half of Tag `09XI`, condition (4), local base ring).
* `exists_finite_etale_lift_of_henselianLocalRing`: Tag `09ZL`, essential surjectivity, for a
  henselian local ring `A` and `I ⊆ m_A`.
* `restrictFiniteEtaleToHypersurface_essSurj`: the scheme-theoretic form (essential
  surjectivity of restriction to the hypersurface), the input of the `0BLM` categorical assembly.

## Proof route (divergence from the Stacks proof)

Stacks proves essential surjectivity by lifting `C` to an etale `A`-algebra (Algebra, Lemma
10.143.10) and cutting out a finite etale direct factor of its integral closure (Lemma 15.11.5).
We instead use that `A/I` is again henselian local and induct on the rank of `C`: the closed
fibre of `C` is a finite product of finite separable field extensions (Mathlib); a nontrivial
idempotent of the closed fibre lifts to `C` and splits it; if the closed fibre is a field `K`,
the characteristic polynomial `χ` of a lift of a primitive element of `K` reduces to its
separable minimal polynomial, Nakayama gives `C ≅ (A/I)[X]/(χ)`, and a monic lift of `χ` to `A`
gives the finite etale lift `A[X]/(χ̃)`.  Full faithfulness of Tag `09ZL` is not proved here.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open Polynomial IsLocalRing
open scoped TensorProduct

universe u v

namespace Pcf.Stacks

section HenselFactorization

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Hensel factorization over a local ring that is henselian along `I`: a factorization of the
reduction of a monic polynomial into coprime monic factors lifts to a factorization into coprime
monic factors.

This is the factorization condition in the definition of a henselian pair (Stacks Tag `09XE`),
deduced from Mathlib's simple-root formulation `HenselianRing` when the base ring is local.  The
proof lifts the residual point of the etale universal coprime factorization ring with the local
case of Stacks Tag `09XI`, condition (2).

Tag `09XE` is a definition (henselian pair); for a local ring, its agreement with Mathlib's
simple-root formulation is Stacks Lemma 10.153.3 (`04GG`, (1) ⇔ (3)).  That proof is not
followed: the factorization is obtained from a section of the étale universal
coprime-factorization ring, lifted by the local case of `09XI`, condition (2). -/
@[stacks 09XE "factorization condition, for a local ring henselian in Mathlib's sense"]
theorem exists_monic_factorization_lift_of_henselian
    (I : Ideal R) [HenselianRing R I]
    (p : R[X]) (hp : p.Monic) (f₀ g₀ : (R ⧸ I)[X]) (hf₀ : f₀.Monic) (hg₀ : g₀.Monic)
    (hfac : p.map (Ideal.Quotient.mk I) = f₀ * g₀) (hcop : IsCoprime f₀ g₀) :
    ∃ f g : R[X], f.Monic ∧ g.Monic ∧ p = f * g ∧ IsCoprime f g ∧
      f.map (Ideal.Quotient.mk I) = f₀ ∧ g.map (Ideal.Quotient.mk I) = g₀ := by
  have hn : p.natDegree = f₀.natDegree + g₀.natDegree := by
    by_cases hI : I = ⊤
    · subst hI
      have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      have h1 : (1 : R) = 0 := by
        have := HenselianRing.jac (R := R) (I := ⊤)
        exfalso
        have hj : (⊤ : Ideal R) ≤ maximalIdeal R := by
          simpa [jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top] using this
        exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hj)
      exact absurd h1 one_ne_zero
    have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    rw [← hf₀.natDegree_mul hg₀, ← hfac, hp.natDegree_map]
  let P : MonicDegreeEq R p.natDegree := .mk p hp rfl
  let F : MonicDegreeEq (R ⧸ I) f₀.natDegree := .mk f₀ hf₀ rfl
  let G : MonicDegreeEq (R ⧸ I) g₀.natDegree := .mk g₀ hg₀ rfl
  let σ :=
    (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) f₀.natDegree g₀.natDegree hn P).symm
    ⟨(F, G), by simpa [F, G, P, Ideal.Quotient.algebraMap_eq] using hfac.symm, hcop⟩
  obtain ⟨τ, hτ⟩ := exists_algHom_lift_of_etale_of_isLocalRing I σ
  let q := UniversalCoprimeFactorizationRing.homEquiv R f₀.natDegree g₀.natDegree hn P τ
  have h₁ := UniversalCoprimeFactorizationRing.homEquiv_comp_fst R f₀.natDegree
    g₀.natDegree hn P τ (Ideal.Quotient.mkₐ R I)
  have h₂ := UniversalCoprimeFactorizationRing.homEquiv_comp_snd R f₀.natDegree
    g₀.natDegree hn P τ (Ideal.Quotient.mkₐ R I)
  rw [hτ] at h₁ h₂
  simp only [σ, Equiv.apply_symm_apply] at h₁ h₂
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, q.2.2, ?_, ?_⟩
  · simpa [P] using q.2.1.symm
  · have := (congrArg Subtype.val h₁).symm
    simp only [F, MonicDegreeEq.map_coe] at this
    exact this
  · have := (congrArg Subtype.val h₂).symm
    simp only [G, MonicDegreeEq.map_coe] at this
    exact this

end HenselFactorization

section IdempotentLifting

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- Over a local ring henselian along `I`, every idempotent of `B / IB` lifts to an idempotent
of `B`, for `B` integral over the base.

This is the existence half of condition (4) of Stacks Tag `09XI` for a local base ring; the
uniqueness half is `injective_idempotentQuotientMap_of_isIntegral`.  Proof route differs from
Stacks, which proves `(2) ⇒ (4)` by lifting along an étale map (More on Algebra, Lemma 15.9.10).
Here `(1) ⇒ (4)` is proved directly: Tag `09XG` gives a monic annihilating polynomial reducing to
`X ^ d (X - 1) ^ d`, the henselian factorization (`exists_monic_factorization_lift_of_henselian`)
splits it, and a Bezout combination of the factors is the idempotent. -/
@[stacks 09XI "(4), existence of idempotent lifts, local base ring"]
theorem exists_isIdempotentElem_sub_mem_of_isIntegral_of_henselian
    [Algebra.IsIntegral R B] (I : Ideal R) [HenselianRing R I] (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b)) :
    ∃ e : B, IsIdempotentElem e ∧ e - b ∈ I.map (algebraMap R B) := by
  obtain ⟨f, hfm, hfb, d, hd, hred⟩ :=
    exists_monic_aeval_eq_zero_map_eq_X_pow_mul_X_sub_one_pow I b hb
  have hcop0 : IsCoprime ((X : (R ⧸ I)[X]) ^ d) ((X - 1) ^ d) := by
    have : IsCoprime (X : (R ⧸ I)[X]) (X - 1) := ⟨1, -1, by ring⟩
    exact this.pow
  have hm1 : ((X : (R ⧸ I)[X]) - 1).Monic := by
    simpa using monic_X_sub_C (1 : R ⧸ I)
  obtain ⟨g, h, -, -, hfgh, ⟨u, v, huv⟩, hgred, hhred⟩ :=
    exists_monic_factorization_lift_of_henselian I f hfm (X ^ d) ((X - 1) ^ d)
      (monic_X_pow d) (hm1.pow d) hred hcop0
  let J := I.map (algebraMap R B)
  let β : B ⧸ J := Ideal.Quotient.mk J b
  refine ⟨aeval b (u * g), ?_, ?_⟩
  · have h1 : aeval b (u * g) + aeval b (v * h) = 1 := by
      rw [← map_add, huv, map_one]
    have h0 : aeval b (u * g) * aeval b (v * h) = 0 := by
      rw [← map_mul, show u * g * (v * h) = u * v * (g * h) by ring, ← hfgh, map_mul, hfb,
        mul_zero]
    have : aeval b (v * h) = 1 - aeval b (u * g) := by rw [← h1]; ring
    rw [this, mul_sub, mul_one, sub_eq_zero] at h0
    exact h0.symm
  · rw [← Ideal.Quotient.eq]
    have hmk : ∀ p : R[X], Ideal.Quotient.mk J (aeval b p) = aeval β p := fun p ↦ by
      simpa using (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R J) b p).symm
    have hmap : ∀ p : R[X], aeval β p = aeval β (p.map (Ideal.Quotient.mk I)) := fun p ↦ by
      rw [← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_map_algebraMap]
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hg : aeval β g = β := by
      rw [hmap, hgred]
      simpa using hb.pow_succ_eq d'
    have hh : aeval β h = (β - 1) ^ (d' + 1) := by
      rw [hmap, hhred]
      simp
    have hβ0 : β * (β - 1) ^ (d' + 1) = 0 := by
      have h' : β * (β - 1) = 0 := by rw [mul_sub, mul_one, hb.eq, sub_self]
      rw [pow_succ', ← mul_assoc, h', zero_mul]
    have huv' := congrArg (aeval β) huv
    rw [map_add, map_mul, map_mul, hg, hh, map_one] at huv'
    have key : aeval β u * β = β := by
      linear_combination β * huv' - (aeval β u) * hb.eq - (aeval β v) * hβ0
    rw [hmk, map_mul, hg, key]

end IdempotentLifting

section CoprimeLift

variable {R : Type u} [CommRing R]

/-- Coprimality of a monic polynomial with another polynomial lifts along an ideal contained in
the Jacobson radical. -/
theorem isCoprime_of_isCoprime_map_of_le_jacobson (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (f g : R[X]) (hf : f.Monic)
    (h : IsCoprime (f.map (Ideal.Quotient.mk J)) (g.map (Ideal.Quotient.mk J))) :
    IsCoprime f g := by
  obtain ⟨a₀, b₀, hab⟩ := h
  obtain ⟨a, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective a₀
  obtain ⟨b, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective b₀
  have ht : a * f + b * g - 1 ∈ J.map (C : R →+* R[X]) := by
    rw [← Ideal.mk_ker (I := J), ← Polynomial.ker_mapRingHom, RingHom.mem_ker]
    simp only [coe_mapRingHom, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_one, hab, sub_self]
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  let M := AdjoinRoot.mk f
  have hjac : J.map (algebraMap R (AdjoinRoot f)) ≤ Ideal.jacobson ⊥ :=
    map_le_jacobson_bot_of_le_jacobson_of_isIntegral _
      (fun x ↦ Algebra.IsIntegral.isIntegral x) J hJ
  have hMt : M (a * f + b * g - 1) ∈ Ideal.jacobson ⊥ := by
    apply hjac
    have : (J.map (C : R →+* R[X])).map M = J.map (algebraMap R (AdjoinRoot f)) := by
      rw [Ideal.map_map]
      rfl
    rw [← this]
    exact Ideal.mem_map_of_mem _ ht
  have hu : IsUnit (M b * M g) := by
    have := (Ideal.mem_jacobson_bot.mp hMt) 1
    have hMf : M f = 0 := AdjoinRoot.mk_self
    simpa [M, map_sub, map_add, map_mul, hMf] using this
  obtain ⟨w₀, hw₀⟩ := (isUnit_of_mul_isUnit_right hu).exists_right_inv
  obtain ⟨w, rfl⟩ := AdjoinRoot.mk_surjective w₀
  have hdvd : f ∣ g * w - 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, map_one]
    simpa [M, sub_eq_zero] using hw₀
  obtain ⟨q, hq⟩ := hdvd
  exact ⟨-q, w, by linear_combination hq⟩

end CoprimeLift

section AdjoinRoot

variable {R : Type u} [CommRing R]

/-- A monic polynomial coprime to its derivative defines a finite etale algebra. -/
theorem etale_adjoinRoot_of_isCoprime_derivative (f : R[X]) (hf : f.Monic)
    (hcop : IsCoprime f (derivative f)) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hcop
  let P : StandardEtalePair R :=
    { f := f, monic_f := hf, g := 1, cond := ⟨b, a, 0, by linear_combination hab⟩ }
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by simp [P]
  letI : IsLocalization.Away (AdjoinRoot.mk P.f P.g) (AdjoinRoot f) :=
    IsLocalization.away_of_isUnit_of_bijective _ hunit Function.bijective_id
  let e₁ : Localization.Away (AdjoinRoot.mk P.f P.g) ≃ₐ[AdjoinRoot f] AdjoinRoot f :=
    IsLocalization.algEquiv (Submonoid.powers (AdjoinRoot.mk P.f P.g)) _ _
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans (e₁.restrictScalars R))

variable {S : Type v} [CommRing S] [Algebra R S]

/-- Adjoining a root commutes with base change. -/
def tensorAdjoinRootEquiv (f : R[X]) :
    S ⊗[R] AdjoinRoot f ≃ₐ[S] AdjoinRoot (f.map (algebraMap R S)) := by
  let Q := AdjoinRoot (f.map (algebraMap R S))
  have hQ : aeval (AdjoinRoot.root (f.map (algebraMap R S))) f = 0 := by
    rw [← aeval_map_algebraMap S, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hT : aeval ((1 : S) ⊗ₜ[R] AdjoinRoot.root f) (f.map (algebraMap R S)) = 0 := by
    rw [aeval_map_algebraMap]
    have := Polynomial.aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : AdjoinRoot f →ₐ[R] S ⊗[R] AdjoinRoot f)
      (AdjoinRoot.root f) f
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] at this
    simpa using this
  let fwdR : AdjoinRoot f →ₐ[R] Q :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R Q) (AdjoinRoot.root _) (by
      simpa [aeval_def] using hQ)
  let fwd : S ⊗[R] AdjoinRoot f →ₐ[S] Q :=
    Algebra.TensorProduct.lift (Algebra.ofId S Q) fwdR fun _ _ ↦ .all _ _
  let bwd : Q →ₐ[S] S ⊗[R] AdjoinRoot f :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId S _) ((1 : S) ⊗ₜ AdjoinRoot.root f) (by
      simpa [aeval_def] using hT)
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · apply AdjoinRoot.algHom_ext
    simp [fwd, bwd, fwdR]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AdjoinRoot.algHom_ext
      simp [fwd, bwd, fwdR]

end AdjoinRoot

section Fiber

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C]

/-- The fibre `C / IC` of an etale algebra is etale over `R / I`. -/
theorem etale_quotient_map [Algebra.Etale R C] (I : Ideal R) :
    Algebra.Etale (R ⧸ I) (C ⧸ (I.map (algebraMap R C) : Ideal C)) := by
  let e₀ : (C ⧸ (I.map (algebraMap R C) : Ideal C)) ≃ₐ[R] (R ⧸ I) ⊗[R] C :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).restrictScalars R).trans
      (Algebra.TensorProduct.comm R C (R ⧸ I))
  let e : (R ⧸ I) ⊗[R] C ≃ₐ[R ⧸ I] (C ⧸ (I.map (algebraMap R C) : Ideal C)) :=
    AlgEquiv.ofRingEquiv (f := e₀.symm.toRingEquiv) (fun x ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [← Ideal.Quotient.algebraMap_eq]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact e₀.symm.commutes r)
  exact Algebra.Etale.of_equiv e

end Fiber

section Monogenic

attribute [local instance] Ideal.Quotient.field

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C] [Module.Free R C]

/-- If the closed fibre of a finite free algebra over a local ring is a finite separable field
extension of the residue field, the algebra is `R[X]/(χ)` for a monic `χ` coprime to its
derivative.  No henselian hypothesis is needed. -/
theorem exists_adjoinRoot_algEquiv_of_closedFiber_field
    {K : Type*} [Field K] [Algebra (R ⧸ maximalIdeal R) K]
    [Module.Finite (R ⧸ maximalIdeal R) K] [Algebra.IsSeparable (R ⧸ maximalIdeal R) K]
    (ψ : (C ⧸ ((maximalIdeal R).map (algebraMap R C) : Ideal C)) ≃ₐ[R ⧸ maximalIdeal R]
      K) :
    ∃ χ : R[X], χ.Monic ∧ IsCoprime χ (derivative χ) ∧
      Nonempty (AdjoinRoot χ ≃ₐ[R] C) := by
  let m := maximalIdeal R
  let k := R ⧸ m
  let mC := m.map (algebraMap R C)
  let pb := Field.powerBasisOfFiniteOfSeparable k K
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (I := mC) (ψ.symm pb.gen)
  let χ : R[X] := (Algebra.lmul R C c).charpoly
  have hχm : χ.Monic := LinearMap.charpoly_monic _
  have hχdeg : χ.natDegree = Module.finrank R C := LinearMap.charpoly_natDegree _
  have hχc : aeval c χ = 0 := by
    have h := LinearMap.aeval_self_charpoly (Algebra.lmul R C c)
    rw [show (Algebra.lmul R C c) = (Algebra.lmul R C : C →ₐ[R] Module.End R C) c from rfl,
      Polynomial.aeval_algHom_apply] at h
    simpa [χ] using congrArg (fun f : Module.End R C ↦ f 1) h
  have hroot : aeval pb.gen (χ.map (Ideal.Quotient.mk m)) = 0 := by
    have h1 : aeval (Ideal.Quotient.mk mC c) (χ.map (Ideal.Quotient.mk m)) = 0 := by
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R mC) c χ
      rw [hχc, map_zero] at this
      rw [show (Ideal.Quotient.mk m) = algebraMap R k from rfl, Polynomial.aeval_map_algebraMap]
      simpa using this
    have hg : pb.gen = ψ (Ideal.Quotient.mk mC c) := by rw [hc]; simp
    rw [hg, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h1, map_zero]
  have hrank : Module.finrank k K = Module.finrank R C := by
    rw [← ψ.toLinearEquiv.finrank_eq]
    exact IsLocalRing.finrank_quotient_map
  have hχbar : χ.map (Ideal.Quotient.mk m) = minpoly k pb.gen := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic pb.isIntegral_gen)
      (hχm.map _) (minpoly.dvd k pb.gen hroot)
    rw [hχm.natDegree_map, pb.natDegree_minpoly, ← pb.finrank, hrank, hχdeg]
  have hsep : (minpoly k pb.gen).Separable := Algebra.IsSeparable.isSeparable k pb.gen
  have hcop : IsCoprime χ (derivative χ) := by
    apply isCoprime_of_isCoprime_map_of_le_jacobson m
      (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]) χ _ hχm
    rw [← Polynomial.derivative_map, hχbar]
    exact hsep
  let φ : AdjoinRoot χ →ₐ[R] C :=
    AdjoinRoot.liftAlgHom χ (Algebra.ofId R C) c (by simpa [aeval_def] using hχc)
  have hφroot : φ (AdjoinRoot.root χ) = c := by simp [φ]
  -- every element of the closed fibre comes from the image of `φ`
  have himage : ∀ y : C ⧸ mC, ∃ x, Ideal.Quotient.mk mC (φ x) = y := by
    intro y
    have hy : ψ y ∈ Algebra.adjoin k {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
    have hall : ∀ z ∈ Algebra.adjoin k {pb.gen},
        ∃ x, Ideal.Quotient.mk mC (φ x) = ψ.symm z := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        exact ⟨AdjoinRoot.root χ, by rw [hφroot, hc, hz]⟩
      | algebraMap z =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
        refine ⟨algebraMap R _ r, ?_⟩
        rw [AlgEquiv.commutes, φ.commutes, Ideal.Quotient.algebraMap_quotient_map_quotient]
      | add z w _ _ hz hw =>
        obtain ⟨a, ha⟩ := hz
        obtain ⟨b, hb⟩ := hw
        exact ⟨a + b, by rw [map_add, map_add, ha, hb, map_add]⟩
      | mul z w _ _ hz hw =>
        obtain ⟨a, ha⟩ := hz
        obtain ⟨b, hb⟩ := hw
        exact ⟨a * b, by rw [map_mul, map_mul, ha, hb, map_mul]⟩
    obtain ⟨x, hx⟩ := hall _ hy
    exact ⟨x, by simpa using hx⟩
  have hsurj : Function.Surjective φ := by
    have hspan : Submodule.span R (Set.range φ) = ⊤ := by
      apply (IsLocalRing.quotient_span_eq_top_iff_span_eq_top _).mp
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := himage y
      exact Submodule.subset_span ⟨φ x, ⟨x, rfl⟩, rfl⟩
    have hle : Submodule.span R (Set.range φ) ≤ LinearMap.range φ.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    rw [hspan, top_le_iff, LinearMap.range_eq_top] at hle
    exact hle
  let b₁ := (AdjoinRoot.powerBasis' hχm).basis
  let b₂ : Module.Basis (Fin χ.natDegree) R C := Module.finBasisOfFinrankEq R C hχdeg.symm
  let i : AdjoinRoot χ ≃ₗ[R] C := b₁.equiv b₂ (Equiv.refl _)
  have hbij : Function.Bijective φ :=
    OrzechProperty.bijective_of_surjective_of_injective i.toLinearMap φ.toLinearMap
      i.injective hsurj
  exact ⟨χ, hχm, hcop, ⟨AlgEquiv.ofBijective φ hbij⟩⟩

end Monogenic

section Product

/-- The two-factor family used to express a binary product as a `Bool`-indexed product. -/
def BoolFamily (B₁ B₂ : Type v) (b : Bool) : Type v := cond b B₁ B₂

instance BoolFamily.instCommRing (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂] (b : Bool) :
    CommRing (BoolFamily B₁ B₂ b) :=
  match b with
  | true => inferInstanceAs (CommRing B₁)
  | false => inferInstanceAs (CommRing B₂)

instance BoolFamily.instAlgebra (A : Type u) [CommRing A] (B₁ B₂ : Type v) [CommRing B₁]
    [CommRing B₂] [Algebra A B₁] [Algebra A B₂] (b : Bool) :
    Algebra A (BoolFamily B₁ B₂ b) :=
  match b with
  | true => inferInstanceAs (Algebra A B₁)
  | false => inferInstanceAs (Algebra A B₂)

theorem BoolFamily.etale (A : Type u) [CommRing A] (B₁ B₂ : Type v) [CommRing B₁]
    [CommRing B₂] [Algebra A B₁] [Algebra A B₂] [Algebra.Etale A B₁] [Algebra.Etale A B₂]
    (b : Bool) : Algebra.Etale A (BoolFamily B₁ B₂ b) :=
  match b with
  | true => inferInstanceAs (Algebra.Etale A B₁)
  | false => inferInstanceAs (Algebra.Etale A B₂)

/-- The `Bool`-indexed product is the binary product. -/
def BoolFamily.piAlgEquiv (A : Type u) [CommRing A] (B₁ B₂ : Type v) [CommRing B₁]
    [CommRing B₂] [Algebra A B₁] [Algebra A B₂] :
    (Π b, BoolFamily B₁ B₂ b) ≃ₐ[A] B₁ × B₂ where
  toFun f := (f true, f false)
  invFun p b := match b with
    | true => p.1
    | false => p.2
  left_inv f := by funext b; cases b <;> rfl
  right_inv p := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A product of two etale algebras is etale. -/
theorem etale_prod {A : Type u} [CommRing A] (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂] [Algebra.Etale A B₁] [Algebra.Etale A B₂] :
    Algebra.Etale A (B₁ × B₂) := by
  haveI := BoolFamily.etale A B₁ B₂
  exact Algebra.Etale.of_equiv (BoolFamily.piAlgEquiv A B₁ B₂)

end Product

section Lift

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The finite etale `A`-algebras whose reduction modulo `I` is isomorphic to `C`. -/
def HasFiniteEtaleLift (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] : Prop :=
  ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
    Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] C)

variable {A I}

theorem HasFiniteEtaleLift.of_algEquiv {C C' : Type u} [CommRing C] [Algebra (A ⧸ I) C]
    [CommRing C'] [Algebra (A ⧸ I) C'] (h : HasFiniteEtaleLift A I C) (e : C ≃ₐ[A ⧸ I] C') :
    HasFiniteEtaleLift A I C' := by
  obtain ⟨B, _, _, hf, he, ⟨φ⟩⟩ := h
  exact ⟨B, _, _, hf, he, ⟨φ.trans e⟩⟩

theorem HasFiniteEtaleLift.prod {C₁ C₂ : Type u} [CommRing C₁] [Algebra (A ⧸ I) C₁]
    [CommRing C₂] [Algebra (A ⧸ I) C₂] (h₁ : HasFiniteEtaleLift A I C₁)
    (h₂ : HasFiniteEtaleLift A I C₂) : HasFiniteEtaleLift A I (C₁ × C₂) := by
  obtain ⟨B₁, _, _, hf₁, he₁, ⟨φ₁⟩⟩ := h₁
  obtain ⟨B₂, _, _, hf₂, he₂, ⟨φ₂⟩⟩ := h₂
  exact ⟨B₁ × B₂, inferInstance, inferInstance, inferInstance, etale_prod B₁ B₂,
    ⟨(Algebra.TensorProduct.prodRight A (A ⧸ I) (A ⧸ I) B₁ B₂).trans
      (φ₁.prodCongr φ₂)⟩⟩

theorem HasFiniteEtaleLift.of_adjoinRoot [IsLocalRing A] (hI : I ≤ maximalIdeal A)
    {C : Type u} [CommRing C] [Algebra (A ⧸ I) C] (χ₀ : (A ⧸ I)[X]) (hm : χ₀.Monic)
    (hc : IsCoprime χ₀ (derivative χ₀)) (e : AdjoinRoot χ₀ ≃ₐ[A ⧸ I] C) :
    HasFiniteEtaleLift A I C := by
  have hlifts : χ₀ ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
    (Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective χ₀)
  obtain ⟨χ, hχmap, -, hχm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hm
  have hjac : I ≤ Ideal.jacobson ⊥ := by
    rwa [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hcop : IsCoprime χ (derivative χ) := by
    apply isCoprime_of_isCoprime_map_of_le_jacobson I hjac χ _ hχm
    rw [← Polynomial.derivative_map, hχmap]
    exact hc
  haveI : Module.Finite A (AdjoinRoot χ) := hχm.finite_adjoinRoot
  haveI : Algebra.Etale A (AdjoinRoot χ) := etale_adjoinRoot_of_isCoprime_derivative χ hχm hcop
  refine ⟨AdjoinRoot χ, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (tensorAdjoinRootEquiv χ).trans
    ((AdjoinRoot.algEquivOfEq (R := A ⧸ I) (χ.map (algebraMap A (A ⧸ I))) χ₀
      (by rw [Ideal.Quotient.algebraMap_eq]; exact hχmap)).trans e)

/-- A finite algebra over a local ring with zero closed fibre is zero (Nakayama). -/
theorem subsingleton_of_subsingleton_closedFiber {R C : Type*} [CommRing R] [IsLocalRing R]
    [CommRing C] [Algebra R C] [Module.Finite R C]
    (h : Subsingleton (C ⧸ ((maximalIdeal R).map (algebraMap R C) : Ideal C))) :
    Subsingleton C := by
  have htop : (maximalIdeal R).map (algebraMap R C) = ⊤ :=
    Ideal.Quotient.subsingleton_iff.mp h
  have hjac : (maximalIdeal R).map (algebraMap R C) ≤ Ideal.jacobson ⊥ :=
    map_le_jacobson_bot_of_le_jacobson_of_isIntegral _
      (fun x ↦ Algebra.IsIntegral.isIntegral x) _
      (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  rw [htop, top_le_iff, Ideal.jacobson_eq_top_iff] at hjac
  have h1 : (1 : C) ∈ (⊥ : Ideal C) := hjac ▸ Submodule.mem_top
  exact subsingleton_of_zero_eq_one (by simpa using h1.symm)

variable [HenselianLocalRing A]

/-- The induction on the rank behind the essential surjectivity in Stacks Tag `09ZL`. -/
theorem hasFiniteEtaleLift_of_finrank_eq (hI : I ≤ maximalIdeal A) (n : ℕ) :
    ∀ (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] [Module.Finite (A ⧸ I) C]
      [Algebra.Etale (A ⧸ I) C], Module.finrank (A ⧸ I) C = n → HasFiniteEtaleLift A I C := by
  haveI : HenselianLocalRing (A ⧸ I) := HenselianLocalRing.quotient_of_le_maximalIdeal I hI
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C _ _ _ _ hn
  let R₀ := A ⧸ I
  haveI : Module.Free R₀ C := Module.free_of_flat_of_isLocalRing
  let m₀ := maximalIdeal R₀
  let k := R₀ ⧸ m₀
  let mC : Ideal C := m₀.map (algebraMap R₀ C)
  haveI : Algebra.Etale k (C ⧸ mC) := etale_quotient_map m₀
  obtain ⟨J, _, K, _, _, eK, hK⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k (C ⧸ mC)).mp inferInstance
  by_cases hJ : ∃ i j : J, i ≠ j
  · -- split off a nontrivial idempotent
    obtain ⟨i, j, hij⟩ := hJ
    classical
    let ebar : C ⧸ mC := eK.symm (Pi.single i 1)
    have hebar : IsIdempotentElem ebar := by
      simp only [IsIdempotentElem, ebar, ← map_mul, ← Pi.single_mul, mul_one]
    have hebar0 : ebar ≠ 0 := by
      intro h0
      have := congrArg (fun z ↦ eK z i) h0
      simp [ebar] at this
    have hebar1 : ebar ≠ 1 := by
      intro h1
      have := congrArg (fun z ↦ eK z j) h1
      simp [ebar, hij.symm] at this
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ebar
    obtain ⟨e, he, heb⟩ := exists_isIdempotentElem_sub_mem_of_isIntegral_of_henselian m₀ b
      (by rw [hb]; exact hebar)
    have hmk : Ideal.Quotient.mk mC e = ebar := by
      rw [← hb, Ideal.Quotient.eq]
      exact heb
    have hunit : ∀ u : C, IsIdempotentElem u → IsUnit u → u = 1 := fun u hu hU ↦
      hU.mul_left_cancel (by rw [hu.eq, mul_one])
    let C₁ := C ⧸ Ideal.span {1 - e}
    let C₂ := C ⧸ Ideal.span {1 - (1 - e)}
    let eC : C ≃ₐ[R₀] C₁ × C₂ :=
      AlgEquiv.prodQuotientOfIsIdempotentElem R₀ he.one_sub he.one_sub.one_sub (by ring)
        (by rw [sub_sub_cancel, sub_mul, one_mul, he.eq, sub_self])
    haveI : IsLocalization.Away e C₁ := IsLocalization.Away.quotient_of_isIdempotentElem he
    haveI : IsLocalization.Away (1 - e) C₂ :=
      IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
    haveI : Algebra.Etale C C₁ := Algebra.Etale.of_isLocalizationAway e
    haveI : Algebra.Etale C C₂ := Algebra.Etale.of_isLocalizationAway (1 - e)
    haveI : Algebra.Etale R₀ C₁ := Algebra.Etale.comp R₀ C C₁
    haveI : Algebra.Etale R₀ C₂ := Algebra.Etale.comp R₀ C C₂
    haveI : Module.Finite R₀ C₁ :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ R₀ _).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Finite R₀ C₂ :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ R₀ _).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Free R₀ C₁ := Module.free_of_flat_of_isLocalRing
    haveI : Module.Free R₀ C₂ := Module.free_of_flat_of_isLocalRing
    haveI : Nontrivial C₁ := by
      apply Ideal.Quotient.nontrivial_iff.mpr
      rw [Ne, Ideal.span_singleton_eq_top]
      intro hU
      apply hebar0
      have h1 := hunit _ he.one_sub hU
      have he0 : e = 0 := by linear_combination -h1
      rw [← hmk, he0, map_zero]
    haveI : Nontrivial C₂ := by
      apply Ideal.Quotient.nontrivial_iff.mpr
      rw [Ne, Ideal.span_singleton_eq_top]
      intro hU
      apply hebar1
      have h1 := hunit _ he.one_sub.one_sub hU
      have he1 : e = 1 := by linear_combination h1
      rw [← hmk, he1, map_one]
    have hrank : Module.finrank R₀ C = Module.finrank R₀ C₁ + Module.finrank R₀ C₂ := by
      rw [eC.toLinearEquiv.finrank_eq, Module.finrank_prod]
    have h₁pos : 0 < Module.finrank R₀ C₁ :=
      (Module.finrank_pos_iff_of_free R₀ C₁).mpr ‹_›
    have h₂pos : 0 < Module.finrank R₀ C₂ :=
      (Module.finrank_pos_iff_of_free R₀ C₂).mpr ‹_›
    have hn' : Module.finrank R₀ C = n := hn
    have hl₁ := ih (Module.finrank R₀ C₁) (by omega) C₁ rfl
    have hl₂ := ih (Module.finrank R₀ C₂) (by omega) C₂ rfl
    exact (hl₁.prod hl₂).of_algEquiv eC.symm
  · push Not at hJ
    haveI : Subsingleton J := ⟨hJ⟩
    rcases isEmpty_or_nonempty J with hJe | hJn
    · -- the closed fibre is zero
      haveI : Subsingleton (C ⧸ mC) := eK.toEquiv.subsingleton
      haveI : Subsingleton C := subsingleton_of_subsingleton_closedFiber (R := R₀) ‹_›
      haveI : Subsingleton (AdjoinRoot (1 : R₀[X])) := by
        change Subsingleton (R₀[X] ⧸ Ideal.span {(1 : R₀[X])})
        exact Ideal.Quotient.subsingleton_iff.mpr (by simp)
      let φ : AdjoinRoot (1 : R₀[X]) →ₐ[R₀] C :=
        AdjoinRoot.liftAlgHom 1 (Algebra.ofId R₀ C) 0 (Subsingleton.elim _ _)
      have hφ : Function.Bijective φ :=
        ⟨Function.injective_of_subsingleton _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
      exact HasFiniteEtaleLift.of_adjoinRoot hI 1 monic_one isCoprime_one_left
        (AlgEquiv.ofBijective φ hφ)
    · -- the closed fibre is a field
      haveI : Unique J := uniqueOfSubsingleton (Classical.arbitrary J)
      obtain ⟨hKf, hKs⟩ := hK default
      let ψ : (C ⧸ mC) ≃ₐ[k] K default :=
        AlgEquiv.ofRingEquiv (f := eK.toRingEquiv.trans (RingEquiv.piUnique K)) (by
          intro x
          simp)
      obtain ⟨χ, hχm, hχc, ⟨φ⟩⟩ := exists_adjoinRoot_algEquiv_of_closedFiber_field ψ
      exact HasFiniteEtaleLift.of_adjoinRoot hI χ hχm hχc φ

/-- **Stacks Tag `09ZL`, essential surjectivity, henselian local case.**  For a henselian local
ring `A` and an ideal `I ⊆ m_A` (so that `(A, I)` is a henselian pair), every finite etale
`A/I`-algebra `C` is isomorphic to `A/I ⊗_A B` for a finite etale `A`-algebra `B`.

Divergence from Stacks: only the essential-surjectivity half of the equivalence, and only for
a henselian local `A` with `I ⊆ m_A` rather than an arbitrary henselian pair.  The proof route
differs from Stacks; see the module docstring. -/
@[stacks 09ZL "essential surjectivity, for a henselian local ring and an ideal in its maximal
ideal"]
theorem exists_finite_etale_lift_of_henselianLocalRing (hI : I ≤ maximalIdeal A)
    (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] [Module.Finite (A ⧸ I) C]
    [Algebra.Etale (A ⧸ I) C] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧
      Algebra.Etale A B ∧ Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] C) :=
  hasFiniteEtaleLift_of_finrank_eq hI _ C rfl

end Lift

section Scheme

open AlgebraicGeometry CategoryTheory Limits

variable (R : Type u) [CommRing R] [HenselianLocalRing R] (x : R)

local notation "Rbar" => R ⧸ Ideal.span (Set.singleton x)

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks Tag `09ZL`, essential surjectivity, for the hypersurface of a henselian local
ring.**  Every finite etale cover of `Spec(R/(x))` is the restriction of a finite etale cover of
`Spec R`.  This is the hypothesis `hLift` of
`hypersurfaceFiniteEtaleLifting_of_essSurj_of_fullyFaithful`.

The hypothesis `[IsLocalRing (R ⧸ (x))]` (as in `HypersurfaceLifting.lean`) forces `x ∈ m_R`.
The algebraic input is `exists_finite_etale_lift_of_henselianLocalRing`; the translation uses
the affine `Γ ⊣ Spec` unit isomorphism for finite etale covers and `pullbackSpecIso`. -/
@[stacks 09ZL "essential surjectivity, for `A` henselian local and `I = (x)`, as covers"]
theorem restrictFiniteEtaleToHypersurface_essSurj [IsLocalRing Rbar] :
    (restrictFiniteEtaleToHypersurface R x).EssSurj := by
  have hI : Ideal.span (Set.singleton x) ≤ maximalIdeal R := by
    intro y hy
    by_contra hym
    have hunit : IsUnit y := (IsLocalRing.notMem_maximalIdeal.mp hym)
    have htop : Ideal.span (Set.singleton x) = ⊤ := Ideal.eq_top_of_isUnit_mem _ hy hunit
    have : Nontrivial Rbar := inferInstance
    exact (Ideal.Quotient.nontrivial_iff.mp this) htop
  constructor
  intro Y₀
  let Cop := (algΓ (.of Rbar)).obj ((FiniteEtaleCover.forget _).obj Y₀)
  let C := Cop.unop
  obtain ⟨hCf, hCe⟩ := finiteEtaleCover_sections_finite_etale Rbar Y₀
  obtain ⟨B, _, _, hBf, hBe, ⟨φ⟩⟩ :=
    exists_finite_etale_lift_of_henselianLocalRing hI C
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have het : Etale (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let Y : FiniteEtaleCover (Spec (.of R)) :=
    MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨hfin, het⟩
  refine ⟨Y, ⟨?_⟩⟩
  let τ : B ⊗[R] Rbar ≃+* C :=
    (Algebra.TensorProduct.comm R B Rbar).toRingEquiv.trans φ.toRingEquiv
  have hτ : ∀ r : Rbar, τ.symm (algebraMap Rbar C r) = (1 : B) ⊗ₜ r := by
    intro r
    apply τ.injective
    rw [RingEquiv.apply_symm_apply]
    change algebraMap Rbar C r = φ (r ⊗ₜ (1 : B))
    rw [show r ⊗ₜ[R] (1 : B) = algebraMap Rbar (Rbar ⊗[R] B) r from rfl, AlgEquiv.commutes]
  let u := (algΓAlgSpecAdjunction (.of Rbar)).unit.app ((FiniteEtaleCover.forget _).obj Y₀)
  haveI : IsIso u := finiteEtaleCover_algGamma_unit_isIso Rbar Y₀
  haveI : IsIso u.left := inferInstance
  let L : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R Rbar))) ≅ Y₀.left :=
    pullbackSpecIso R B Rbar ≪≫
      Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ).op.symm ≪≫
      (asIso u.left).symm
  refine MorphismProperty.Over.isoMk L ?_
  have hu : inv u.left ≫ Y₀.hom = Spec.map (CommRingCat.ofHom (algebraMap Rbar C)) := by
    rw [IsIso.inv_comp_eq]
    exact (Over.w u).symm
  have hring : CommRingCat.ofHom (algebraMap Rbar C) ≫
      (RingEquiv.toCommRingCatIso τ).inv =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Rbar →ₐ[R] B ⊗[R] Rbar).toRingHom := by
    ext r
    exact hτ r
  change (pullbackSpecIso R B Rbar).hom ≫ Spec.map (RingEquiv.toCommRingCatIso τ).inv ≫
      inv u.left ≫ Y₀.hom = pullback.snd _ _
  rw [hu, ← Spec.map_comp, hring]
  exact pullbackSpecIso_hom_snd R B Rbar

end Scheme

#print axioms exists_monic_factorization_lift_of_henselian
#print axioms exists_isIdempotentElem_sub_mem_of_isIntegral_of_henselian
#print axioms isCoprime_of_isCoprime_map_of_le_jacobson
#print axioms etale_adjoinRoot_of_isCoprime_derivative
#print axioms tensorAdjoinRootEquiv
#print axioms etale_quotient_map
#print axioms exists_adjoinRoot_algEquiv_of_closedFiber_field
#print axioms BoolFamily.etale
#print axioms BoolFamily.piAlgEquiv
#print axioms etale_prod
#print axioms HasFiniteEtaleLift.of_algEquiv
#print axioms HasFiniteEtaleLift.prod
#print axioms HasFiniteEtaleLift.of_adjoinRoot
#print axioms subsingleton_of_subsingleton_closedFiber
#print axioms hasFiniteEtaleLift_of_finrank_eq
#print axioms exists_finite_etale_lift_of_henselianLocalRing
#print axioms restrictFiniteEtaleToHypersurface_essSurj

end Pcf.Stacks
