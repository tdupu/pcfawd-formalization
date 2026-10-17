/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Finite
public import Pcf.Stacks.Purity.NormalRing

/-!
# Etale algebras over normal rings

This file proves the etale case of Stacks Tag `033C` (Lemma 10.163.9: a smooth algebra over a
normal ring is normal), in the forms used by the purity and Abhyankar packages:

* `isDomain_isIntegrallyClosed_atPrime_of_etale`: for `A → B` etale and a prime `q` of `B` over
  `p`, if `A_p` is a normal domain then so is `B_q` (pointwise form, for the `0BMB` local models);
* `IsStacksNormalRing.of_etale`: an etale algebra over a normal ring (Stacks `00GV`) is normal;
* `isStacksNormalRing_of_etale_of_isDomain` and `isIntegrallyClosed_of_etale`: the versions over a
  normal domain, the second for an etale domain (Mathlib's `IsIntegrallyClosed`).

It also proves that etale maps preserve heights of primes (`height_eq_height_under_of_etale`),
from the flat quasi-finite statement `height_eq_height_under_of_flat_of_quasiFiniteAt`.

## Proof route

The Stacks proof uses Serre's criterion in the Noetherian case and an absolute Noetherian
approximation in general. Here we instead use Mathlib's theorem that smooth base change commutes
with integral closure (Stacks `03GV`, `TensorProduct.toIntegralClosure_bijective_of_smooth`):
for `R` a normal domain with fraction field `K` and `S` etale over `R`, the ring `S` is integrally
closed in its generic fibre `S ⊗[R] K`, which is Artinian and reduced. Localizing at a prime `Q` of
`S`, the generic fibre becomes a field, since a separating idempotent would be integral over `S`,
hence would come from an idempotent of `S` lying in `Q` together with its complement. So `S_Q`
is integrally closed in a field containing it, hence a normal domain. The smooth case of `033C`
is not formalized here.
-/

@[expose] public section

open scoped TensorProduct

namespace Pcf.Stacks

section Localization

variable {R S Rf Sf : Type*} [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
  [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
  [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]

/-- Being integrally closed in an algebra is preserved by localizing both rings at the same
submonoid of the base. -/
theorem isIntegrallyClosedIn_of_isLocalization (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf] [IsIntegrallyClosedIn R S] :
    IsIntegrallyClosedIn Rf Sf := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨?_, fun {x} hx ↦ ?_⟩
  · have : IsLocalization (M.map (algebraMap R S)) Sf :=
      ‹IsLocalization (Algebra.algebraMapSubmonoid S M) Sf›
    rw [IsLocalization.algebraMap_eq_map_map_submonoid M S Rf Sf]
    exact IsLocalization.map_injective_of_injective (M := M) (g := algebraMap R S) Rf Sf
      (isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn R S›).1
  · obtain ⟨⟨y, _, m₁, hm₁, rfl⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S M) x
    obtain ⟨⟨m₂, hm₂⟩, hm₂x⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hx
    simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂x
    obtain ⟨m₃, hm₃, hm₃y⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Sf)
      M (x := m₂ • y) <| by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e,
          ← mul_assoc]
        exact hm₂x.mul (.algebraMap (Algebra.IsIntegral.isIntegral _))
    obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hm₃y
    refine ⟨IsLocalization.mk' Rf r ⟨m₃ * m₂ * m₁, mul_mem (mul_mem hm₃ hm₂) hm₁⟩, ?_⟩
    rw [IsLocalization.algebraMap_mk' (S := S), hr, IsLocalization.mk'_eq_iff_eq_mul]
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at e ⊢
    rw [← e]
    ring

end Localization

section SmoothBaseChange

variable (R S K : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- A smooth algebra over a normal domain is integrally closed in its generic fibre. This is the
form in which Mathlib's theorem that smooth base change commutes with integral closure (Stacks
`03GV`) enters the proof of Stacks `033C`. -/
theorem isIntegrallyClosedIn_tensor_fractionRing_of_smooth [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] K) := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨?_, fun {x} hx ↦ ?_⟩
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
      (Algebra.linearMap R K) (IsFractionRing.injective R K)
    have : ⇑(algebraMap S (S ⊗[R] K)) =
        (LinearMap.lTensor S (Algebra.linearMap R K)) ∘ (TensorProduct.rid R S).symm := by
      ext s
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [this]
    exact hinj.comp (TensorProduct.rid R S).symm.injective
  · obtain ⟨w, hw⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := K)).2 ⟨x, hx⟩
    have hx' : x = Algebra.TensorProduct.map (AlgHom.id R S) (integralClosure R K).val w := by
      exact (congrArg Subtype.val hw).symm
    rw [hx']
    clear hw hx'
    induction w with
    | tmul a b =>
      obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp b.2
      refine ⟨r • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
        Algebra.algebraMap_eq_smul_one r, ← TensorProduct.smul_tmul]
      rfl
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨s₁, hs₁⟩ := h₁
      obtain ⟨s₂, hs₂⟩ := h₂
      exact ⟨s₁ + s₂, by rw [map_add, hs₁, hs₂, map_add]⟩

end SmoothBaseChange

section Core

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsIntegrallyClosed R] [Algebra.Etale R S]

omit [IsIntegrallyClosed R] in
/-- The generic fibre of an etale algebra over a domain is an Artinian reduced ring. -/
theorem isArtinianRing_isReduced_tensor_fractionRing_of_etale :
    IsArtinianRing (S ⊗[R] FractionRing R) ∧ IsReduced (S ⊗[R] FractionRing R) := by
  let K := FractionRing R
  have : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K _
  have : IsArtinianRing (K ⊗[R] S) := IsArtinianRing.of_finite K _
  have : IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K _
  let e : S ⊗[R] K ≃+* K ⊗[R] S := (Algebra.TensorProduct.comm R S K).toRingEquiv
  exact ⟨e.symm.isArtinianRing, isReduced_of_injective e.toRingHom e.injective⟩

/-- Two primes of the generic fibre of an etale algebra over a normal domain whose contractions
lie in a common prime `Q` coincide.  The separating idempotent of the Artinian generic fibre is
integral, hence comes from an idempotent of `S` lying in `Q` together with its complement. -/
theorem eq_of_comap_le_of_etale (Q : Ideal S) [Q.IsPrime]
    (P₁ P₂ : Ideal (S ⊗[R] FractionRing R)) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : P₁.comap (algebraMap S _) ≤ Q) (h₂ : P₂.comap (algebraMap S _) ≤ Q) : P₁ = P₂ := by
  obtain ⟨hart, -⟩ := isArtinianRing_isReduced_tensor_fractionRing_of_etale (R := R) (S := S)
  have hcl := isIntegrallyClosedIn_tensor_fractionRing_of_smooth R S (FractionRing R)
  by_contra hne
  obtain ⟨e, he₂, hidem, hall⟩ := IsArtinianRing.exists_notMem_forall_mem_of_ne P₂
  have he₁ : e ∈ P₁ := hall P₁ inferInstance hne
  have : Nontrivial S := nontrivial_of_ne 0 1 fun h ↦
    ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).mpr (h ▸ Q.zero_mem))
  have hint : IsIntegral S e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; decide)
    · simp [pow_two, hidem.eq]
  obtain ⟨s, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  have hs₁ : s ∈ Q := h₁ he₁
  have hcompl : algebraMap S (S ⊗[R] FractionRing R) (1 - s) ∈ P₂ := by
    have hzero : algebraMap S (S ⊗[R] FractionRing R) s *
        algebraMap S (S ⊗[R] FractionRing R) (1 - s) = 0 := by
      rw [map_sub, map_one, mul_sub, mul_one, hidem.eq, sub_self]
    exact ((‹P₂.IsPrime›.mem_or_mem (hzero ▸ P₂.zero_mem)).resolve_left he₂)
  have hs₂ : 1 - s ∈ Q := h₂ hcompl
  exact ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).mpr (by simpa using Q.add_mem hs₁ hs₂))

variable (R) in
include R in
/-- The localization at `S \ Q` of the generic fibre of an etale algebra over a normal domain is a
field as soon as it is nonzero. -/
theorem isField_localization_tensor_fractionRing_of_etale (Q : Ideal S) [Q.IsPrime]
    (Lq : Type*) [CommRing Lq] [Algebra (S ⊗[R] FractionRing R) Lq]
    [IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq]
    [Nontrivial Lq] : IsField Lq := by
  obtain ⟨hart, hred⟩ := isArtinianRing_isReduced_tensor_fractionRing_of_etale (R := R) (S := S)
  have : IsArtinianRing Lq := IsArtinianRing.localization_artinian
    (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq
  have : IsReduced Lq := by
    let e := IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl))
    exact isReduced_of_injective e.toRingHom e.injective
  have hcomap : ∀ m : Ideal Lq, m.IsMaximal →
      (m.under (S ⊗[R] FractionRing R)).under S ≤ Q := by
    intro m hm s hs
    by_contra hsQ
    have hunit : IsUnit (algebraMap (S ⊗[R] FractionRing R) Lq
        (algebraMap S (S ⊗[R] FractionRing R) s)) :=
      IsLocalization.map_units Lq (⟨algebraMap S (S ⊗[R] FractionRing R) s,
        Algebra.mem_algebraMapSubmonoid_of_mem (⟨s, hsQ⟩ : Q.primeCompl)⟩ :
          Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl)
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hunit)
  have : IsLocalRing Lq := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Lq
    refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun m' hm' ↦ ?_⟩
    have := hm.isPrime
    have := hm'.isPrime
    have heq : m'.under (S ⊗[R] FractionRing R) = m.under (S ⊗[R] FractionRing R) :=
      eq_of_comap_le_of_etale (R := R) Q _ _ (hcomap m' hm') (hcomap m hm)
    rw [← IsLocalization.map_under
        (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq m', heq,
      IsLocalization.map_under
        (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl) Lq m]
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing Lq

variable (R) in
include R in
/-- **Stacks `033C`, etale case, over a normal domain, at one prime.** The local ring at any prime
of an etale algebra over a normal domain is a normal domain.

The proof differs from the Stacks proof (which reduces to Serre's criterion in the Noetherian case
and to a limit argument in general): the localization `S_Q` is integrally closed in the
localization of the generic fibre `S ⊗[R] K` (smooth base change commutes with integral closure,
Stacks `03GV`), and the latter localization is a field because the separating idempotents of the
Artinian generic fibre are integral over `S`. -/
@[stacks 033C "etale case, base a normal domain, local form"]
theorem isDomain_isIntegrallyClosed_atPrime_of_etale_of_isDomain (Q : Ideal S) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  have hcl : IsIntegrallyClosedIn S (S ⊗[R] FractionRing R) :=
    isIntegrallyClosedIn_tensor_fractionRing_of_smooth R S (FractionRing R)
  have hclq : IsIntegrallyClosedIn (Localization.AtPrime Q)
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl)) :=
    isIntegrallyClosedIn_of_isLocalization (R := S) (S := S ⊗[R] FractionRing R) Q.primeCompl
  have hinj := (isIntegrallyClosedIn_iff.mp hclq).1
  have : Nontrivial
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl)) :=
    hinj.nontrivial
  let : Field
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl)) :=
    (isField_localization_tensor_fractionRing_of_etale R Q _).toField
  have : FaithfulSMul (Localization.AtPrime Q)
      (Localization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact ⟨hinj.isDomain _, IsIntegrallyClosed.of_isIntegrallyClosedIn _
    (Localization (Algebra.algebraMapSubmonoid (S ⊗[R] FractionRing R) Q.primeCompl))⟩

end Core

section Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]

variable (A) in
/-- **Stacks `033C`, etale case, local form.** Let `A → B` be etale and `q` a prime of `B` over
`p`. If `A_p` is a normal domain, then `B_q` is a normal domain.

Divergence from Stacks: Stacks `033C` assumes `A` normal everywhere; this pointwise form only
assumes it at `p`. Since normality is defined by the local rings (Stacks `00GV`), it implies the
etale case of the tag (`IsStacksNormalRing.of_etale`). It is deduced from the normal-domain case
by the etale base change `A_p ⊗[A] B` and the identification of `B_q` with a localization of that
base change. -/
@[stacks 033C "etale case, local form"]
theorem isDomain_isIntegrallyClosed_atPrime_of_etale (q : Ideal B) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under A))]
    [IsIntegrallyClosed (Localization.AtPrime (q.under A))] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let p := q.under A
  let Ap := Localization.AtPrime p
  let C := Ap ⊗[A] B
  let : Algebra B C := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B p.primeCompl
  have hloc : IsLocalization M C := IsLocalization.tensorRight (S := B) Ap p.primeCompl
  have hd : Disjoint (M : Set B) (q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hq
    exact ha hq
  let Q : Ideal C := q.map (algebraMap B C)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M C q inferInstance hd
  have hQq : Q.comap (algebraMap B C) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M C inferInstance hd
  have hT : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (S := C) (Localization.AtPrime Q) Q
    have hc : (Q.comap (algebraMap B C)).primeCompl = q.primeCompl :=
      Submonoid.ext fun x ↦ by simp only [Ideal.mem_primeCompl_iff, hQq]
    unfold IsLocalization.AtPrime at this ⊢
    rwa [hc] at this
  obtain ⟨hdom, hic⟩ := isDomain_isIntegrallyClosed_atPrime_of_etale_of_isDomain Ap Q
  let e : Localization.AtPrime q ≃ₐ[B] Localization.AtPrime Q :=
    IsLocalization.algEquiv q.primeCompl _ _
  exact ⟨e.toMulEquiv.isDomain _,
    IsIntegrallyClosed.of_equiv (R := Localization.AtPrime Q) e.symm.toRingEquiv⟩

variable (B) in
/-- **Stacks `033C`, etale case.** An etale algebra over a normal ring (Stacks `00GV`: all local
rings at primes are normal domains) is a normal ring. -/
@[stacks 033C "etale case"]
theorem IsStacksNormalRing.of_etale (hA : IsStacksNormalRing A) : IsStacksNormalRing B := by
  intro q
  have := hA.isDomain_atPrime ⟨q.asIdeal.under A, inferInstance⟩
  have := hA.isIntegrallyClosed_atPrime ⟨q.asIdeal.under A, inferInstance⟩
  exact isDomain_isIntegrallyClosed_atPrime_of_etale A q.asIdeal

variable (A B) in
/-- **Stacks `033C`, etale case, base a normal domain.** An etale algebra over a normal domain is a
normal ring in the Stacks sense (it need not be a domain). -/
@[stacks 033C "etale case, base a normal domain"]
theorem isStacksNormalRing_of_etale_of_isDomain [IsDomain A] [IsIntegrallyClosed A] :
    IsStacksNormalRing B :=
  IsStacksNormalRing.of_etale B (IsStacksNormalRing.of_isDomain (R := A))

variable (A B) in
/-- **Stacks `033C`, etale case, domains.** An etale domain over a normal domain is integrally
closed. -/
@[stacks 033C "etale case, both rings domains"]
theorem isIntegrallyClosed_of_etale [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] :
    IsIntegrallyClosed B :=
  IsStacksNormalRing.iff_isIntegrallyClosed.mp (isStacksNormalRing_of_etale_of_isDomain A B)

end Pointwise

section Height

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A flat map of Noetherian rings that is quasi-finite at a prime `P` preserves the height
of `P`: the fibre through `P` is zero-dimensional at `P`, so the going-down dimension formula
(Stacks `00ON`) has no fibre contribution. -/
theorem height_eq_height_under_of_flat_of_quasiFiniteAt [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    P.height = (P.under R).height := by
  let p := P.under R
  have : P.LiesOver p := ⟨rfl⟩
  let I := p.map (algebraMap R S)
  have hIP : I ≤ P := Ideal.map_comap_le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ P := by rwa [Ideal.mk_ker]
  have hq : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIP]
  have hmin : P.map (Ideal.Quotient.mk I) ∈ minimalPrimes (S ⧸ I) := by
    refine ⟨⟨hq, bot_le⟩, fun r ⟨hr, _⟩ hrq ↦ ?_⟩
    let r' := r.comap (Ideal.Quotient.mk I)
    have hr'P : r' ≤ P := hcomap ▸ Ideal.comap_mono hrq
    have hIr' : I ≤ r' := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ r
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact r.zero_mem
    have hunder : r'.under R = P.under R := by
      refine le_antisymm (Ideal.comap_mono hr'P) ?_
      exact (Ideal.le_comap_of_map_le hIr' : p ≤ r'.under R)
    have heq : r' = P := Algebra.QuasiFiniteAt.eq_of_le_of_under_eq hr'P hunder
    rw [← heq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P,
    Ideal.height_eq_zero_iff.mpr hmin, add_zero]

/-- **Etale maps preserve heights.** For an etale algebra over a Noetherian ring, every prime has
the same height as its contraction. -/
theorem height_eq_height_under_of_etale [IsNoetherianRing R] [Algebra.Etale R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height :=
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  height_eq_height_under_of_flat_of_quasiFiniteAt P

end Height

end Pcf.Stacks
