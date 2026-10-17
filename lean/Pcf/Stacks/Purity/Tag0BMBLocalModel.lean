/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Pcf.Stacks.Common.EtaleNormal
public import Pcf.Stacks.Common.EtaleRegular
public import Pcf.Stacks.Common.RegularLocalization
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Stacks.Purity.LocalEtale
public import Pcf.Stacks.Purity.LocalFlatness
public import Pcf.Stacks.Purity.PuncturedEtaleOfPointwise
public import Pcf.Stacks.Purity.Tag0BMBAssembly

/-!
# The étale-local finite model in Stacks Tag `0BMB`

This file proves the inductive step of Zariski--Nagata purity (Stacks Tag `0BMB`) at a point
`w` of height at least two, following the second and third paragraphs of the Stacks proof.

Let `R → S` be of finite type between Noetherian rings and let `w = q` satisfy the pointwise
hypotheses `ZariskiNagataPurityHypothesesAt R S w`, with `p = q ∩ R`.

1. Tag `00UJ` (`exists_etale_finiteComponent_of_zariskiNagataPurityHypothesesAt`) gives an étale
   `R → R'`, a prime `P` of `R'`
   over `p` and a prime `P'` of `T = R' ⊗[R] S` over `P` and `q`, cut out by an idempotent `e`
   with `T_e` finite over `R'` and `P'` the only prime of `T_e` over `P`.
2. The local model is `A = R'_P → B = T_{P'}`.  It is finite (uniqueness of `P'`), `A` is
   regular (`isRegularLocalRing_of_flat_of_formallyUnramified`), hence normal (Stacks `0567`),
   `B` is a normal domain (the étale case of Stacks `033C`, an explicit hypothesis), and the
   heights of `P`, `P'`, `p`, `q` agree, because flat quasi-finite maps preserve heights.
   Equal dimensions make `A → B` injective, hence `B` torsion-free.
3. Every non-closed point of `Spec B` has smaller height, so the induction hypothesis on the
   height gives étaleness there; the inputs at such a point are regularity of `A_Q`
   (Stacks `0AFS`), going down for the finite normal extension, and unramifiedness in
   codimension one transported from `S` along the étale map `S → T`.
4. Clause (2) of Stacks `0BMA` (an explicit hypothesis) makes `A → B` étale.
5. Unramifiedness and flatness descend along the faithfully flat local map `S_q → B`, so
   `R → S_q` is formally étale.

Stacks proves the final descent with Tag `02VN` on schemes; here the descent is done directly
on local rings with Kähler differentials and Tor-free tensor products.
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped TensorProduct

set_option linter.style.haveILetI false

universe u v

namespace Pcf.Stacks

/-! ### Heights along maps with zero-dimensional fibres -/

section Height

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- If `P` is minimal over the extension of its contraction, then its image in the fibre ring
`S ⧸ (P ∩ R) S` has height zero. -/
theorem height_map_fiber_eq_zero_of_mem_minimalPrimes
    (P : Ideal S) [P.IsPrime]
    (hmin : P ∈ ((P.under R).map (algebraMap R S)).minimalPrimes) :
    (P.map (Ideal.Quotient.mk ((P.under R).map (algebraMap R S)))).height = 0 := by
  let p : Ideal R := P.under R
  let q : Ideal (S ⧸ p.map (algebraMap R S)) :=
    P.map (Ideal.Quotient.mk (p.map (algebraMap R S)))
  have hq : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa [p] using Ideal.map_comap_le)
  rw [Ideal.minimalPrimes_eq_comap] at hmin
  obtain ⟨q', hq'min, hq'⟩ := hmin
  have hqq' : q = q' := by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [show q.comap (Ideal.Quotient.mk _) = P by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      apply sup_eq_left.mpr
      change (P.under R).map (algebraMap R S) ≤ P
      exact Ideal.map_comap_le]
    exact hq'.symm
  haveI := hq
  have hqmin : q ∈ minimalPrimes (S ⧸ p.map (algebraMap R S)) := hqq' ▸ hq'min
  exact Ideal.height_eq_zero_iff.mpr hqmin

/-- A prime minimal over the extension of its contraction has height at most that of its
contraction (Stacks Tag `00OM` with a zero-dimensional fibre). -/
theorem height_le_height_under_of_mem_minimalPrimes
    [IsNoetherianRing R] [IsNoetherianRing S] (P : Ideal S) [P.IsPrime]
    (hmin : P ∈ ((P.under R).map (algebraMap R S)).minimalPrimes) :
    P.height ≤ (P.under R).height := by
  letI : (P.under R).IsPrime := Ideal.IsPrime.under R P
  letI : P.LiesOver (P.under R) := ⟨rfl⟩
  have h := Ideal.height_le_height_add_of_liesOver (P.under R) P
  rwa [height_map_fiber_eq_zero_of_mem_minimalPrimes P hmin, add_zero] at h

/-- With going down, a prime minimal over the extension of its contraction has the same height
as its contraction. -/
theorem height_eq_height_under_of_mem_minimalPrimes
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime]
    (hmin : P ∈ ((P.under R).map (algebraMap R S)).minimalPrimes) :
    P.height = (P.under R).height := by
  letI : (P.under R).IsPrime := Ideal.IsPrime.under R P
  letI : P.LiesOver (P.under R) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P
  rwa [height_map_fiber_eq_zero_of_mem_minimalPrimes P hmin, add_zero] at h

/-- A prime at which the algebra is quasi-finite is minimal over the extension of its
contraction. -/
theorem mem_minimalPrimes_of_quasiFiniteAt
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    P ∈ ((P.under R).map (algebraMap R S)).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.map_comap_le⟩, fun Q ⟨hQ, hpQ⟩ hQP ↦ ?_⟩
  have hunder : Q.under R = P.under R :=
    le_antisymm (Ideal.comap_mono hQP) (Ideal.map_le_iff_le_comap.mp hpQ)
  exact (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq hQP hunder).symm.le

/-- A finite extension of Noetherian domains with normal base preserves heights. -/
theorem height_eq_height_under_of_finite_of_isIntegrallyClosed
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite R S] [FaithfulSMul R S]
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height :=
  height_eq_height_under_of_mem_minimalPrimes P (Ideal.IsIntegral.mem_minimalPrimes_map_under P)

end Height

/-! ### Local rings of an étale algebra -/

section EtaleLocal

variable {S : Type u} {T : Type v} [CommRing S] [CommRing T] [Algebra S T]

/-- The local ring of a formally étale algebra at a prime is formally étale over the local ring
of the base at the contracted prime. -/
theorem formallyEtale_localization_atPrime
    [Algebra.FormallyEtale S T] (w : Ideal S) [w.IsPrime] (Q : Ideal T) [Q.IsPrime]
    [Q.LiesOver w] :
    letI := Localization.AtPrime.algebraOfLiesOver w Q
    Algebra.FormallyEtale (Localization.AtPrime w) (Localization.AtPrime Q) := by
  letI := Localization.AtPrime.algebraOfLiesOver w Q
  have : Algebra.FormallyEtale T (Localization.AtPrime Q) :=
    .of_isLocalization Q.primeCompl
  have : Algebra.FormallyEtale S (Localization.AtPrime Q) :=
    .comp S T (Localization.AtPrime Q)
  exact .localization_base w.primeCompl

/-- The local ring of a flat algebra at a prime is faithfully flat over the local ring of the
base at the contracted prime. -/
theorem faithfullyFlat_localization_atPrime
    [Module.Flat S T] (w : Ideal S) [w.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver w] :
    letI := Localization.AtPrime.algebraOfLiesOver w Q
    Module.FaithfullyFlat (Localization.AtPrime w) (Localization.AtPrime Q) := by
  letI := Localization.AtPrime.algebraOfLiesOver w Q
  have hflat : (Localization.localRingHom (Q.under S) Q (algebraMap S T) rfl).Flat :=
    (RingHom.flat_algebraMap_iff.mpr inferInstance).localRingHom Q (Q.under S) rfl
  have hw : w = Q.under S := Q.over_def w
  subst hw
  have : Module.Flat (Localization.AtPrime (Q.under S)) (Localization.AtPrime Q) := by
    rw [← RingHom.flat_algebraMap_iff, Localization.AtPrime.algebraMap_eq]
    exact hflat
  exact .of_flat_of_isLocalHom

end EtaleLocal

/-! ### Faithfully flat descent of flatness and unramifiedness -/

section Descent

variable (R₀ : Type*) (S₀ : Type*) (T₀ : Type*) [CommRing R₀] [CommRing S₀] [CommRing T₀]
  [Algebra R₀ S₀] [Algebra S₀ T₀] [Algebra R₀ T₀] [IsScalarTower R₀ S₀ T₀]

/-- Flatness descends along a faithfully flat algebra: if `T₀` is faithfully flat over `S₀`
and flat over `R₀`, then `S₀` is flat over `R₀`. -/
theorem flat_of_faithfullyFlat_of_flat [Module.FaithfullyFlat S₀ T₀] [Module.Flat R₀ T₀] :
    Module.Flat R₀ S₀ := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  change Function.Injective (f.baseChange S₀)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective S₀ T₀ (f.baseChange S₀)]
  have hcomm : (f.baseChange S₀).lTensor T₀ =
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ S₀ T₀ T₀ N').symm.toLinearMap
          |>.restrictScalars S₀) ∘ₗ
        (f.baseChange T₀).restrictScalars S₀ ∘ₗ
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ S₀ T₀ T₀ N).toLinearMap
          |>.restrictScalars S₀) := by
    ext t n
    simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul]
  rw [hcomm]
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    EquivLike.comp_injective, EquivLike.injective_comp]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := T₀) f hf

/-- Unramifiedness descends along a faithfully flat formally étale algebra. -/
theorem formallyUnramified_of_faithfullyFlat_of_formallyEtale
    [Module.FaithfullyFlat S₀ T₀] [Algebra.FormallyEtale S₀ T₀]
    [Algebra.FormallyUnramified R₀ T₀] :
    Algebra.FormallyUnramified R₀ S₀ := by
  rw [Algebra.formallyUnramified_iff]
  have : Subsingleton (T₀ ⊗[S₀] Ω[S₀⁄R₀]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R₀ S₀ T₀).subsingleton
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right S₀ T₀).mp this

end Descent

/-! ### Generization of étaleness -/

/-- The étale locus is stable under generization. -/
theorem isEtaleAt_of_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (Q Q₁ : Ideal B) [Q.IsPrime] [Q₁.IsPrime] (hle : Q ≤ Q₁)
    (h : Algebra.IsEtaleAt A Q₁) : Algebra.IsEtaleAt A Q := by
  let M := Q₁.primeCompl
  let L := Localization.AtPrime Q₁
  let Q' : Ideal L := Q.map (algebraMap B L)
  have hdisj : Disjoint (M : Set B) Q := by
    rw [Set.disjoint_left]
    intro x hxM hxQ
    exact hxM (hle hxQ)
  have hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M L Q inferInstance hdisj
  have hcomap : Q'.comap (algebraMap B L) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M L inferInstance hdisj
  have : Algebra.FormallyEtale A L := h
  have : Algebra.FormallyEtale L (Localization.AtPrime Q') := .of_isLocalization Q'.primeCompl
  have : Algebra.FormallyEtale A (Localization.AtPrime Q') := .comp A L _
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M Q'
  have hsub : Q.primeCompl = (Q'.comap (algebraMap B L)).primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  haveI : IsLocalization Q.primeCompl (Localization.AtPrime (Q'.comap (algebraMap B L))) := by
    rw [hsub]
    infer_instance
  let e' : Localization.AtPrime Q ≃ₐ[B] Localization.AtPrime (Q'.comap (algebraMap B L)) :=
    IsLocalization.algEquiv Q.primeCompl _ _
  exact .of_equiv ((e'.trans e).symm.restrictScalars A)

/-! ### Normality of étale local rings -/

/-- The étale case of Stacks Tag `033C` (Lemma 10.163.9): an étale algebra over a Stacks-normal
ring is Stacks-normal.  It is used here as an explicit hypothesis. -/
def EtaleNormalAscent : Prop :=
  ∀ (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C],
    IsStacksNormalRing A → IsStacksNormalRing C

/-- If the base local ring is a normal domain, so is every local ring of an étale algebra lying
over it.  The étale algebra `S_w ⊗_S T` is normal by `033C`, and `T_Q` is one of its local
rings. -/
theorem isDomain_isIntegrallyClosed_localization_of_etale
    (h033C : EtaleNormalAscent.{u})
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Algebra.Etale S T]
    (w : Ideal S) [w.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver w]
    [IsDomain (Localization.AtPrime w)] [IsIntegrallyClosed (Localization.AtPrime w)] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let M := w.primeCompl
  let M' := Algebra.algebraMapSubmonoid T M
  let C := Localization M'
  have : Algebra.FormallyEtale T C := .of_isLocalization M'
  have : Algebra.FormallyEtale S C := .comp S T C
  have : Algebra.FormallyEtale (Localization M) C := .localization_base M
  have : Algebra.IsPushout S (Localization M) T C :=
    .symm <| Algebra.isPushout_of_isLocalization M _ _ _
  have : Algebra.FinitePresentation (Localization M) C :=
    .equiv (Algebra.IsPushout.equiv S (Localization M) T C)
  have : Algebra.Etale (Localization M) C := ⟨inferInstance, inferInstance⟩
  have hC : IsStacksNormalRing C :=
    h033C (Localization M) C (IsStacksNormalRing.of_isDomain (R := Localization M))
  have hdisj : Disjoint (M' : Set T) Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    apply hs
    rw [Q.over_def w]
    exact hsQ
  let Q' : Ideal C := Q.map (algebraMap T C)
  have hQ' : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M' C Q inferInstance hdisj
  have hcomap : Q'.comap (algebraMap T C) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M' C inferInstance hdisj
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M' Q'
  have hsub : Q.primeCompl = (Q'.comap (algebraMap T C)).primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  haveI : IsLocalization Q.primeCompl (Localization.AtPrime (Q'.comap (algebraMap T C))) := by
    rw [hsub]
    infer_instance
  let e' : Localization.AtPrime Q ≃ₐ[T] Localization.AtPrime (Q'.comap (algebraMap T C)) :=
    IsLocalization.algEquiv Q.primeCompl _ _
  let f : Localization.AtPrime Q ≃+* Localization.AtPrime Q' := (e'.trans e).toRingEquiv
  have hD : IsDomain (Localization.AtPrime Q') := hC.isDomain_atPrime ⟨Q', hQ'⟩
  have hI : IsIntegrallyClosed (Localization.AtPrime Q') := hC.isIntegrallyClosed_atPrime ⟨Q', hQ'⟩
  exact ⟨f.toMulEquiv.isDomain _,
    @IsIntegrallyClosed.of_equiv (Localization.AtPrime Q') (Localization.AtPrime Q) _ _ f.symm hI⟩

/-! ### The finite local model -/

/-- The finite component produced by Tag `00UJ` has a finite local ring at the selected point:
if `T_e` is finite over `R'` and `P'` is the only prime of `T` over `P` avoiding `e`, then
`T_{P'}` is finite over `R'_P`. -/
theorem module_finite_localization_atPrime_of_unique
    {R' : Type u} {T : Type v} [CommRing R'] [CommRing T] [Algebra R' T]
    (P : Ideal R') [P.IsPrime] (P' : Ideal T) [P'.IsPrime] [P'.LiesOver P]
    (e : T) (he : e ∉ P') [Module.Finite R' (Localization.Away e)]
    (huniq : ∀ P'' : Ideal T, P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    letI := Localization.AtPrime.algebraOfLiesOver P P'
    Module.Finite (Localization.AtPrime P) (Localization.AtPrime P') := by
  letI := Localization.AtPrime.algebraOfLiesOver P P'
  let A := Localization.AtPrime P
  let Te := Localization.Away e
  let N0 := Algebra.algebraMapSubmonoid Te P.primeCompl
  let D := Localization N0
  have hfinD : Module.Finite A D := inferInstance
  have hintD : Algebra.IsIntegral A D := inferInstance
  -- every maximal ideal of `D` contracts to `P'`
  have hmax : ∀ Mx : Ideal D, Mx.IsMaximal → Mx.comap (algebraMap T D) = P' := by
    intro Mx hMx
    have hMA : (Mx.comap (algebraMap A D)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Mx
    have hMA' : Mx.comap (algebraMap A D) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal hMA
    apply huniq
    · exact Ideal.IsPrime.comap _
    · constructor
      rw [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq R' A D, ← Ideal.comap_comap, hMA']
      exact (Localization.AtPrime.under_maximalIdeal (I := P)).symm
    · intro heM
      have hunit : IsUnit (algebraMap T D e) := by
        rw [IsScalarTower.algebraMap_eq T Te D, RingHom.comp_apply]
        exact (IsLocalization.Away.algebraMap_isUnit e).map _
      exact hMx.ne_top (Ideal.eq_top_of_isUnit_mem _ heM hunit)
  -- `D` is nontrivial: `P'` survives in it
  have hP'Te : (P'.map (algebraMap T Te)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers e) Te P' inferInstance
      (by
        rw [Set.disjoint_left]
        rintro _ ⟨n, rfl⟩ hn
        exact he (Ideal.IsPrime.mem_of_pow_mem inferInstance n hn))
  have hP'Tecomap : (P'.map (algebraMap T Te)).comap (algebraMap T Te) = P' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers e) Te inferInstance
      (by
        rw [Set.disjoint_left]
        rintro _ ⟨n, rfl⟩ hn
        exact he (Ideal.IsPrime.mem_of_pow_mem inferInstance n hn))
  have hPD : ((P'.map (algebraMap T Te)).map (algebraMap Te D)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint N0 D _ hP'Te (by
      rw [Set.disjoint_left]
      rintro _ ⟨r, hr, rfl⟩ hrP
      apply hr
      have : algebraMap R' T r ∈ P' := by
        rw [← hP'Tecomap, Ideal.mem_comap, ← RingHom.comp_apply,
          ← IsScalarTower.algebraMap_eq]
        exact hrP
      rw [P'.over_def P]
      exact this)
  have : Nontrivial D := ⟨⟨0, 1, fun h ↦ hPD.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ Ideal.zero_mem _))⟩⟩
  -- every element outside `P'` becomes a unit in `D`
  have hunits : ∀ t ∈ P'.primeCompl, IsUnit (algebraMap T D t) := by
    intro t ht
    by_contra hnu
    obtain ⟨Mx, hMx, htMx⟩ := exists_max_ideal_of_mem_nonunits hnu
    apply ht
    rw [← hmax Mx hMx]
    exact htMx
  -- `D` is the localization of `T` at `P'`
  have hDloc0 : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule (Submonoid.powers e) N0) D :=
    IsLocalization.localization_localization_isLocalization (Submonoid.powers e) N0 D
  have hle : IsLocalization.localizationLocalizationSubmodule (Submonoid.powers e) N0 ≤
      P'.primeCompl := by
    intro x hx hxP
    obtain ⟨Mx, hMx⟩ := Ideal.exists_maximal D
    have hxu : IsUnit (algebraMap T D x) := IsLocalization.map_units D ⟨x, hx⟩
    have : algebraMap T D x ∈ Mx := by
      rw [← Ideal.mem_comap, hmax Mx hMx]
      exact hxP
    exact hMx.ne_top (Ideal.eq_top_of_isUnit_mem _ this hxu)
  have hDloc : IsLocalization.AtPrime D P' :=
    IsLocalization.of_le _ P'.primeCompl hle hunits
  let eDB : D ≃ₐ[T] Localization.AtPrime P' := IsLocalization.algEquiv P'.primeCompl D _
  let f : D →ₗ[A] Localization.AtPrime P' :=
    LinearMap.extendScalarsOfIsLocalization P.primeCompl A
      ((eDB.toLinearEquiv.toLinearMap).restrictScalars R')
  exact Module.Finite.of_surjective f eDB.surjective

/-! ### Injectivity from equal dimensions -/

/-- A finite local algebra over a Noetherian local domain of the same finite dimension is
injective.  Otherwise it would be finite over a proper quotient, which has smaller dimension. -/
theorem injective_algebraMap_of_finite_of_ringKrullDim_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B]
    [Module.Finite A B]
    (hdim : ringKrullDim A ≤ ringKrullDim B) (hfin : ringKrullDim A < ⊤) :
    Function.Injective (algebraMap A B) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  let I : Ideal A := Ideal.span {r}
  have hI : I ≤ RingHom.ker (algebraMap A B) := by
    rw [Ideal.span_le]
    simpa using hr
  letI : Algebra (A ⧸ I) B := (Ideal.Quotient.lift I (algebraMap A B) hI).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) B := .of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.Finite (A ⧸ I) B := .of_restrictScalars_finite A _ B
  let mB := maximalIdeal B
  have hmin : mB ∈ ((mB.under (A ⧸ I)).map (algebraMap (A ⧸ I) B)).minimalPrimes :=
    Ideal.IsIntegral.mem_minimalPrimes_map_under mB
  have h1 : (mB.height : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ I) := by
    letI : (mB.under (A ⧸ I)).IsPrime := Ideal.IsPrime.under _ mB
    exact (WithBot.coe_le_coe.mpr (height_le_height_under_of_mem_minimalPrimes mB hmin)).trans
      Ideal.height_le_ringKrullDim_of_isPrime
  have h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h1
  have h3 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim (A ⧸ I) :=
    h2.trans (hdim.trans h1)
  have hne : ringKrullDim (A ⧸ I) ≠ ⊤ :=
    ((ringKrullDim_quotient_le I).trans_lt hfin).ne
  have hnebot : ringKrullDim (A ⧸ I) ≠ ⊥ := by
    have : Nontrivial (A ⧸ I) := by
      rw [Ideal.Quotient.nontrivial_iff]
      intro htop
      have : IsUnit r := by
        rw [← Ideal.span_singleton_eq_top]
        exact htop
      have h01 : (1 : B) = 0 := by
        obtain ⟨u, rfl⟩ := this
        have := congrArg (algebraMap A B) u.mul_inv
        rw [map_mul, hr, zero_mul, map_one] at this
        exact this.symm
      exact one_ne_zero h01
    exact ringKrullDim_ne_bot
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (A ⧸ I) = n := by
    induction h : ringKrullDim (A ⧸ I) with
    | bot => exact absurd h hnebot
    | coe m =>
      induction m with
      | top => exact absurd h hne
      | coe n => exact ⟨n, rfl⟩
  rw [hn] at h3
  exact absurd (by exact_mod_cast h3 : n + 1 ≤ n) (by omega)

/-! ### Formal étaleness at a point from flatness and unramifiedness -/

/-- If the local ring `S_q` of a finitely presented algebra is flat and formally unramified over
the base, then `S` is étale at `q`. -/
theorem isEtaleAt_of_flat_of_formallyUnramified
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)]
    [Algebra.FormallyUnramified R (Localization.AtPrime q)] :
    Algebra.IsEtaleAt R q := by
  let p : Ideal R := q.under R
  letI : q.LiesOver p := ⟨rfl⟩
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl)
      (f := Algebra.ofId _ _) (by
    rintro ⟨_, x, hx, rfl⟩
    simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
      by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Algebra.FormallyUnramified Rp Sq := .localization_base p.primeCompl
  have : Module.Flat Rp Sq :=
    haveI := isLocalizedModule_id p.primeCompl Sq Rp
    Module.Flat.of_isLocalizedModule Rp p.primeCompl (LinearMap.id : Sq →ₗ[R] Sq)
  have : Algebra.FormallyEtale Rp Sq :=
    formallyEtale_of_flat_of_formallyUnramified_of_isLocalization Rp Sq Sp
      (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  exact Algebra.FormallyEtale.comp R Rp Sq

/-! ### The inductive step of Tag `0BMB` -/

/-- **The inductive step of Stacks Tag `0BMB` at a point of height at least two.**

Let `R → S` be of finite type between Noetherian rings and let `w` be a point of `Spec S` of
height at least two.  Assume purity at all points of smaller height of all such pairs (`IH`),
the étale case of Stacks `033C` (`h033C`), and clause (2) of Stacks `0BMA` for regular local
rings of dimension at least two (`h0BMA`).  Then purity holds at `w`.

The proof is the second and third paragraphs of the Stacks proof of `0BMB`: pass to the étale
local finite component of Tag `00UJ`, check that the local model `R'_P → T_{P'}` is finite,
torsion-free and normal over a regular base, get étaleness on its punctured spectrum from `IH`,
apply `0BMA`, and descend.  The descent is done on local rings with faithfully flat descent of
flatness and of Kähler differentials, rather than with Tag `02VN` on schemes. -/
theorem hasZariskiNagataPurityAt_of_lowerHeight
    (h033C : EtaleNormalAscent.{u})
    (h0BMA : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
      2 ≤ ringKrullDim A → FiniteNormalPuncturedEtalePurity A)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    (w : PrimeSpectrum S) (hw : 2 ≤ w.asIdeal.height)
    (IH : ∀ (R₁ S₁ : Type u) [CommRing R₁] [CommRing S₁] [Algebra R₁ S₁],
      IsNoetherianRing R₁ → IsNoetherianRing S₁ → Algebra.FiniteType R₁ S₁ →
      ∀ w₁ : PrimeSpectrum S₁, w₁.asIdeal.height < w.asIdeal.height →
        HasZariskiNagataPurityAt R₁ S₁ w₁) :
    HasZariskiNagataPurityAt R S w := by
  intro h
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hcomapq, heP', -, hfin, huniq⟩ :=
    exists_etale_finiteComponent_of_zariskiNagataPurityHypothesesAt w h
  let q := w.asIdeal
  let p := q.under R
  let T := R' ⊗[R] S
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.Etale S T := by
    let eT : S ⊗[R] R' ≃ₐ[S] T :=
      .ofRingEquiv (f := (Algebra.TensorProduct.comm R S R').toRingEquiv) fun _ ↦ rfl
    exact Algebra.Etale.of_equiv eT
  haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing S T
  haveI : P'.LiesOver q := ⟨hcomapq.symm⟩
  -- heights
  have hPp : P.height = p.height := by
    rw [height_eq_height_under_of_flat_of_quasiFiniteAt (R := R) P, ← P.over_def p]
  have hP'q : P'.height = q.height := by
    rw [height_eq_height_under_of_flat_of_quasiFiniteAt (R := S) P', ← P'.over_def q]
  have hqp : q.height = p.height := h.equalDimension
  -- the local model
  let A := Localization.AtPrime P
  let B := Localization.AtPrime P'
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver P P'
  haveI : Module.Finite A B := module_finite_localization_atPrime_of_unique P P' e heP' huniq
  -- `A` is regular local, hence a normal domain
  have : Algebra.FormallyEtale R' A := .of_isLocalization P.primeCompl
  have : Algebra.FormallyEtale R A := .comp R R' A
  letI : Algebra (Localization.AtPrime p) A := Localization.AtPrime.algebraOfLiesOver p P
  haveI : IsRegularLocalRing (Localization.AtPrime p) := h.target_isRegular
  have : Algebra.FormallyEtale (Localization.AtPrime p) A := .localization_base p.primeCompl
  have : Module.FaithfullyFlat (Localization.AtPrime p) A := faithfullyFlat_localization_atPrime p P
  have : Algebra.EssFiniteType R A := .comp R R' A
  have : Algebra.EssFiniteType (Localization.AtPrime p) A := .of_comp R _ A
  haveI : IsRegularLocalRing A :=
    isRegularLocalRing_of_flat_of_formallyUnramified (Localization.AtPrime p) A
  haveI : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  haveI : IsRegularRing A := Pcf.Vendor.isRegularRing_of_isRegularLocalRing A
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularRing A
  -- `B` is a normal domain
  haveI : IsDomain (Localization.AtPrime q) := h.source_isDomain
  haveI : IsIntegrallyClosed (Localization.AtPrime q) := h.source_isIntegrallyClosed
  obtain ⟨hBdom, hBic⟩ := isDomain_isIntegrallyClosed_localization_of_etale h033C q P'
  haveI : IsDomain B := hBdom
  haveI : IsIntegrallyClosed B := hBic
  -- dimensions
  have hdimA : ringKrullDim A = q.height := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P A, hPp, hqp]
  have hdimB : ringKrullDim B = q.height := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P' B, hP'q]
  have hmaxB : (maximalIdeal B).height = q.height := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B)
    rw [hdimB] at this
    exact_mod_cast this
  have hqfin : q.height < ⊤ := Ideal.height_lt_top_of_isPrime
  -- `A → B` is injective, so `B` is torsion-free
  have hinj : Function.Injective (algebraMap A B) :=
    injective_algebraMap_of_finite_of_ringKrullDim_le (by rw [hdimA, hdimB])
      (by rw [hdimA]; exact WithBot.coe_lt_coe.mpr hqfin)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  -- unramifiedness of `A → B` in codimension one
  have hunr : ∀ (Q₁ : Ideal B) [Q₁.IsPrime], Q₁.height = 1 → Algebra.IsUnramifiedAt A Q₁ := by
    intro Q₁ _ hQ₁
    let Q₁T : Ideal T := Q₁.under T
    have hQ₁T : Q₁T.height = 1 := (IsLocalization.height_under P'.primeCompl Q₁).trans hQ₁
    have hle : Q₁T ≤ P' := by
      have := Ideal.comap_mono (f := algebraMap T B) (IsLocalRing.le_maximalIdeal
        (Ideal.IsPrime.ne_top (inferInstance : Q₁.IsPrime)))
      exact this.trans (Localization.AtPrime.under_maximalIdeal (I := P')).le
    let w₁ : Ideal S := Q₁T.under S
    haveI : Q₁T.LiesOver w₁ := ⟨rfl⟩
    have hw₁ : w₁.height = 1 := by
      rw [← height_eq_height_under_of_flat_of_quasiFiniteAt (R := S) Q₁T]
      exact hQ₁T
    have hw₁q : w₁ ≤ q := by
      rw [P'.over_def q]
      exact Ideal.comap_mono hle
    have hU : Algebra.IsUnramifiedAt R w₁ :=
      h.unramifiedCodimensionOne ⟨w₁, inferInstance⟩
        ((PrimeSpectrum.le_iff_specializes ⟨w₁, inferInstance⟩ w).mp hw₁q) hw₁
    letI := Localization.AtPrime.algebraOfLiesOver w₁ Q₁T
    have : Algebra.FormallyEtale (Localization.AtPrime w₁) (Localization.AtPrime Q₁T) :=
      formallyEtale_localization_atPrime w₁ Q₁T
    have : Algebra.FormallyUnramified R (Localization.AtPrime w₁) := hU
    have : Algebra.FormallyUnramified R (Localization.AtPrime Q₁T) :=
      .comp R (Localization.AtPrime w₁) _
    have : Algebra.FormallyUnramified R' (Localization.AtPrime Q₁T) :=
      .of_restrictScalars R R' _
    let eQ := IsLocalization.localizationLocalizationAtPrimeIsoLocalization P'.primeCompl Q₁
    have : Algebra.FormallyUnramified R' (Localization.AtPrime Q₁) :=
      .of_equiv (eQ.restrictScalars R')
    exact Algebra.FormallyUnramified.of_restrictScalars R' A (Localization.AtPrime Q₁)
  -- étaleness at non-closed points of positive height, from the induction hypothesis
  have hetaleIH : ∀ (Q : Ideal B) [Q.IsPrime], 1 ≤ Q.height → Q ≠ maximalIdeal B →
      Algebra.IsEtaleAt A Q := by
    intro Q _ hQ1 hQm
    have hlt : Q.height < q.height := by
      rw [← hmaxB]
      exact Ideal.height_strict_mono_of_isPrime
        (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal
          (Ideal.IsPrime.ne_top (inferInstance : Q.IsPrime))) hQm)
    have hBn : IsStacksNormalRing B := IsStacksNormalRing.of_isDomain
    refine IH A B inferInstance inferInstance inferInstance ⟨Q, inferInstance⟩ hlt
      { source_isDomain := hBn.isDomain_atPrime ⟨Q, inferInstance⟩
        source_isIntegrallyClosed := hBn.isIntegrallyClosed_atPrime ⟨Q, inferInstance⟩
        target_isRegular := Pcf.Vendor.isRegularLocalRing_localization A (Q.under A)
        quasiFinite := inferInstance
        equalDimension := height_eq_height_under_of_finite_of_isIntegrallyClosed Q
        positiveDimension := hQ1
        unramifiedCodimensionOne := fun Q₁ _ h1 ↦ hunr Q₁.asIdeal h1 }
  -- étaleness on the punctured spectrum
  have hmaxunder : (maximalIdeal B).under A = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) _)
  have hpunct : ∀ (Q : Ideal B) [Q.IsPrime], Q.under A ≠ maximalIdeal A →
      Algebra.IsEtaleAt A Q := by
    intro Q _ hQ
    have hQm : Q ≠ maximalIdeal B := by
      rintro rfl
      exact hQ hmaxunder
    by_cases h1 : 1 ≤ Q.height
    · exact hetaleIH Q h1 hQm
    · have hQ0 : Q.height = 0 := Order.lt_one_iff.mp (not_le.mp h1)
      have hQbot : Q = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hQ0
      have hnot : ¬ (maximalIdeal B).height ≤ ((1 : ℕ) : ℕ∞) := by
        rw [hmaxB]
        intro h'
        have := hw.trans h'
        norm_num at this
      rw [Ideal.height_le_iff] at hnot
      push Not at hnot
      obtain ⟨Q₁, hQ₁p, hQ₁lt, hQ₁h⟩ := hnot
      haveI := hQ₁p
      have hQ₁ : Algebra.IsEtaleAt A Q₁ := hetaleIH Q₁ (by exact_mod_cast hQ₁h) hQ₁lt.ne
      exact isEtaleAt_of_le Q Q₁ (by rw [hQbot]; exact bot_le) hQ₁
  -- clause (2) of `0BMA`
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hpunctScheme := etale_puncturedSpectrum_pullback_of_forall_isEtaleAt (R := A) (S := B) hpunct
  have hBnormal : IsStacksNormalRing B := IsStacksNormalRing.of_isDomain
  let Bop : (CommAlgCat A)ᵒᵖ := Opposite.op (.of A B)
  have hB : finiteNormalPuncturedEtaleAlgebraProperty A Bop :=
    ⟨inferInstance, inferInstance, hBnormal, hpunctScheme⟩
  have hdim2 : 2 ≤ ringKrullDim A := by
    rw [hdimA]
    exact WithBot.coe_le_coe.mpr hw
  haveI : Algebra.Etale A B := h0BMA A hdim2 Bop hB
  -- descent from `T_{P'}` to `S_q`
  letI : Algebra (Localization.AtPrime q) B := Localization.AtPrime.algebraOfLiesOver q P'
  have : Algebra.FormallyEtale (Localization.AtPrime q) B := formallyEtale_localization_atPrime q P'
  have : Module.FaithfullyFlat (Localization.AtPrime q) B :=
    faithfullyFlat_localization_atPrime q P'
  have : Algebra.FormallyEtale R' B := .comp R' A B
  have : Algebra.FormallyEtale R B := .comp R R' B
  have : Module.Flat R' A := IsLocalization.flat A P.primeCompl
  have : Module.Flat R' B := .trans R' A B
  have : Module.Flat R B := .trans R R' B
  have : Module.Flat R (Localization.AtPrime q) :=
    flat_of_faithfullyFlat_of_flat R (Localization.AtPrime q) B
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    formallyUnramified_of_faithfullyFlat_of_formallyEtale R (Localization.AtPrime q) B
  haveI : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact isEtaleAt_of_flat_of_formallyUnramified q

#print axioms height_map_fiber_eq_zero_of_mem_minimalPrimes
#print axioms height_le_height_under_of_mem_minimalPrimes
#print axioms height_eq_height_under_of_mem_minimalPrimes
#print axioms mem_minimalPrimes_of_quasiFiniteAt
#print axioms height_eq_height_under_of_finite_of_isIntegrallyClosed
#print axioms formallyEtale_localization_atPrime
#print axioms faithfullyFlat_localization_atPrime
#print axioms flat_of_faithfullyFlat_of_flat
#print axioms formallyUnramified_of_faithfullyFlat_of_formallyEtale
#print axioms isEtaleAt_of_le
#print axioms EtaleNormalAscent
#print axioms isDomain_isIntegrallyClosed_localization_of_etale
#print axioms module_finite_localization_atPrime_of_unique
#print axioms injective_algebraMap_of_finite_of_ringKrullDim_le
#print axioms isEtaleAt_of_flat_of_formallyUnramified
#print axioms hasZariskiNagataPurityAt_of_lowerHeight

end Pcf.Stacks
