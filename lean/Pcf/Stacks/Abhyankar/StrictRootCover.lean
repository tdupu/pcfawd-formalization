/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Idempotents
public import Pcf.Stacks.Abhyankar.KummerIntermediate
public import Pcf.Stacks.Abhyankar.StandardCoverAddendum
public import Pcf.Stacks.Abhyankar.StandardCoverNormalization
public import Pcf.Stacks.Abhyankar.StrictHenselization
public import Pcf.Stacks.Common.RegularDimensionOne
public import Pcf.Stacks.Common.RegularLocalization
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Stacks.Purity.HenselianFiniteEtaleLift

/-!
# The strict root cover in the proof of Abhyankar's lemma (Stacks Tag `0EYG`)

In the strictly henselian paragraph of the proof
of Stacks Tag `0EYG`, `A` is a regular local ring, `f ∈ 𝔪_A` is a nonzerodivisor with `A ⧸ (f)`
regular, and the proof forms the finite free `A`-algebra

  `A' = A[x] ⧸ (x^e − f)`.

Stacks records the following facts about this situation and we prove each of them here:

* `f` is a prime element of `A` generating a height-one prime `𝔭 = fA`, and `A_𝔭` is a discrete
  valuation ring with uniformizer `f` (`divisorPrime_isPrime`, `divisorPrime_height_eq_one`,
  `divisorLocalization_isDiscreteValuationRing`, `divisorLocalization_irreducible`);
* `A'` is a local ring, finite over `A`, with the same residue field (`rootCover_isLocalRing`,
  `rootCover_residueField_bijective`); in particular its residue field is separably closed when
  that of `A` is;
* `f' = x` is a nonzerodivisor of `A'`, `A' ⧸ (x) ≅ A ⧸ (f)` is regular, so `A'` is regular
  (Stacks `00NU`), hence a normal domain (`rootCover_isRegularLocalRing`, `rootCover_isDomain`,
  `rootCover_isIntegrallyClosed`), and `(x)` is again a height-one prime whose localization is a
  DVR (`rootCover_span_root_isPrime`, `rootCover_localization_span_root_isDiscreteValuationRing`).

Stacks also says that `A'` is strictly henselian ("a local finite extension of a strictly henselian
local ring").  We do not formalize henselianity of `A'`.  The only consequence of strict
henselianity of `A'` used later in `0EYG` is that a finite étale *local* `A'`-algebra is trivial,
and that a finite normal domain over `A'` is local.  Both are proved here from the henselianity of
`A` and the separable closedness of the common residue field:

* `isLocalRing_of_isDomain_of_finite_of_henselian`: a finite domain over a henselian local ring is
  local (idempotents of the closed fibre lift, Stacks `09XI`);
* `bijective_algebraMap_of_finite_etale_local_of_isSepClosed`: a finite étale local algebra over a
  local ring with separably closed residue field is the base ring.

Divergence from Stacks: henselianity of the root cover is replaced by these two consequences.
The statements are otherwise the ones in the proof of `0EYG`.
-/

@[expose] public section

universe u v

open IsLocalRing Polynomial

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Divisor

variable {A : Type u} [CommRing A]

/-- If `A ⧸ (a)` is a domain, then `(a)` is a prime ideal. -/
theorem span_singleton_isPrime_of_quotient_isDomain (a : A)
    [IsDomain (A ⧸ Ideal.span ({a} : Set A))] : (Ideal.span ({a} : Set A)).IsPrime :=
  Ideal.Quotient.isDomain_iff_prime _ |>.mp inferInstance

variable [IsRegularLocalRing A]

omit [IsRegularLocalRing A] in
/-- In a regular local ring, a divisor with regular quotient is a prime element: `A ⧸ (a)` is a
regular local ring, hence a domain (Stacks `00NP`). -/
theorem divisorPrime_isPrime (a : A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    (Ideal.span ({a} : Set A)).IsPrime := by
  have : IsDomain (A ⧸ Ideal.span ({a} : Set A)) := isDomain_of_isRegularLocalRing _
  exact span_singleton_isPrime_of_quotient_isDomain a

/-- A nonzero element of the maximal ideal of a regular local ring generates a height-one ideal
(Krull's principal ideal theorem). -/
theorem divisorPrime_height_eq_one (a : A) (ha : a ∈ maximalIdeal A) (ha0 : a ≠ 0) :
    (Ideal.span ({a} : Set A)).height = 1 := by
  have : IsDomain A := isDomain_of_isRegularLocalRing A
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha0) ((IsLocalRing.mem_maximalIdeal a).mp ha)

/-- The localization of a regular local ring at a prime is regular local (Stacks `0AFS`). -/
theorem divisorLocalization_isRegularLocalRing (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_localization_atPrime A p

/-- The localization of a regular local ring at a height-one prime is a discrete valuation
ring. -/
theorem isDiscreteValuationRing_localization_atPrime_of_height_eq_one
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have := divisorLocalization_isRegularLocalRing p
  apply isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
  rfl

/-- `A_(a)` is a discrete valuation ring when `a` is a nonzero element of the maximal ideal of
the regular local ring `A` generating a prime ideal. -/
theorem divisorLocalization_isDiscreteValuationRing (a : A) (ha : a ∈ maximalIdeal A)
    (ha0 : a ≠ 0) [(Ideal.span ({a} : Set A)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span ({a} : Set A))) :=
  isDiscreteValuationRing_localization_atPrime_of_height_eq_one _
    (divisorPrime_height_eq_one a ha ha0)

/-- The image of `a` is a uniformizer of the discrete valuation ring `A_(a)`. -/
theorem divisorLocalization_irreducible (a : A) (ha : a ∈ maximalIdeal A) (ha0 : a ≠ 0)
    [(Ideal.span ({a} : Set A)).IsPrime] :
    Irreducible (algebraMap A (Localization.AtPrime (Ideal.span ({a} : Set A))) a) := by
  have : IsDomain A := isDomain_of_isRegularLocalRing A
  have := divisorLocalization_isDiscreteValuationRing a ha ha0
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]

end Divisor

section Jacobson

variable {B : Type u} [CommRing B]

/-- A ring whose quotient by an ideal contained in the Jacobson radical is local is itself
local. -/
theorem isLocalRing_of_quotient_of_le_jacobson (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥)
    [IsLocalRing (B ⧸ J)] : IsLocalRing B := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨(maximalIdeal (B ⧸ J)).comap (Ideal.Quotient.mk J),
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  intro I hI
  haveI := hI
  have hJI : J ≤ I := by
    refine hJ.trans ?_
    rw [Ideal.jacobson]
    exact sInf_le ⟨bot_le, hI⟩
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ I := by rwa [Ideal.mk_ker]
  have hmax : (I.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  rw [← IsLocalRing.eq_maximalIdeal hmax,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJI]

end Jacobson

section HenselianFinite

variable (A : Type u) (N : Type v) [CommRing A] [CommRing N] [Algebra A N]

/-- Every maximal ideal of an integral extension of a local ring contains the extension of the
maximal ideal. -/
theorem map_maximalIdeal_le_of_isMaximal_of_isIntegral [IsLocalRing A] [Algebra.IsIntegral A N]
    (I : Ideal N) [I.IsMaximal] : (maximalIdeal A).map (algebraMap A N) ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  have : (I.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal I
  exact (IsLocalRing.eq_maximalIdeal this).ge

/-- The extension of the maximal ideal to an integral extension lies in the Jacobson radical. -/
theorem map_maximalIdeal_le_jacobson_of_isIntegral [IsLocalRing A] [Algebra.IsIntegral A N] :
    (maximalIdeal A).map (algebraMap A N) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro I ⟨-, hI⟩
  exact map_maximalIdeal_le_of_isMaximal_of_isIntegral A N I

/-- An idempotent of a domain is `0` or `1`. -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_isDomain {D : Type*} [CommRing D] [IsDomain D]
    {e : D} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

/-- **A finite domain over a henselian local ring is local.**  This is the only consequence of
"a finite local extension of a strictly henselian ring is strictly henselian" (proof of Stacks
`0EYG`) that is used for the components of the normalization.

Proof.  All maximal ideals of `N` lie over the maximal ideal `𝔪` of `A`, so the closed fibre
`N ⧸ 𝔪N` is a finite `κ`-algebra, hence Artinian; modulo its (nilpotent) Jacobson radical it is a
product of fields indexed by the maximal ideals of `N`.  If `N` had two maximal ideals, this
product would contain a nontrivial idempotent, which lifts to `N ⧸ 𝔪N` along the nilpotent ideal
and then to `N` by henselianity (Stacks `09XI`); a domain has no nontrivial idempotent. -/
theorem isLocalRing_of_isDomain_of_finite_of_henselian [HenselianLocalRing A]
    [Module.Finite A N] [IsDomain N] : IsLocalRing N := by
  classical
  have hint : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  let J : Ideal N := (maximalIdeal A).map (algebraMap A N)
  have hJ : J ≤ Ideal.jacobson ⊥ := map_maximalIdeal_le_jacobson_of_isIntegral A N
  -- it suffices to show that the closed fibre is local
  suffices IsLocalRing (N ⧸ J) from isLocalRing_of_quotient_of_le_jacobson J hJ
  letI : Algebra (ResidueField A) (N ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := maximalIdeal A) Ideal.le_comap_map
  haveI : IsScalarTower A (ResidueField A) (N ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have : Module.Finite A (N ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A J).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (ResidueField A) (N ⧸ J) :=
    Module.Finite.of_restrictScalars_finite A (ResidueField A) (N ⧸ J)
  have : IsArtinianRing (N ⧸ J) := IsArtinianRing.of_finite (ResidueField A) (N ⧸ J)
  have hnt : Nontrivial (N ⧸ J) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    intro htop
    have h1 : (1 : N) ∈ Ideal.jacobson (⊥ : Ideal N) := hJ (htop ▸ Submodule.mem_top)
    have hbot : (⊥ : Ideal N) = ⊤ :=
      Ideal.jacobson_eq_top_iff.mp ((Ideal.eq_top_iff_one _).mpr h1)
    exact one_ne_zero (Ideal.mem_bot.mp (hbot ▸ Submodule.mem_top : (1 : N) ∈ (⊥ : Ideal N)))
  -- reduce to the reduced quotient, a finite product of fields
  let Jac : Ideal (N ⧸ J) := Ideal.jacobson ⊥
  have hnil : IsNilpotent Jac := IsArtinianRing.isNilpotent_jacobson_bot
  have hred : IsReduced ((N ⧸ J) ⧸ Jac) :=
    (Ideal.isRadical_iff_quotient_reduced Jac).mp (Ideal.isRadical_jacobson _)
  let e := IsArtinianRing.equivPi ((N ⧸ J) ⧸ Jac)
  have hJacle : ∀ I : Ideal (N ⧸ J), I.IsMaximal → Jac ≤ I := fun I hI ↦ by
    change Ideal.jacobson ⊥ ≤ I
    rw [Ideal.jacobson]
    exact sInf_le ⟨bot_le, hI⟩
  -- two maximal ideals of `N ⧸ J` would give a nontrivial idempotent
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal (N ⧸ J)
  refine ⟨m₁, hm₁, fun m₂ hm₂ ↦ ?_⟩
  by_contra hne
  haveI := hm₁
  haveI := hm₂
  let M₁ : MaximalSpectrum ((N ⧸ J) ⧸ Jac) :=
    ⟨m₁.map (Ideal.Quotient.mk Jac), Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJacle m₁ hm₁)⟩
  let M₂ : MaximalSpectrum ((N ⧸ J) ⧸ Jac) :=
    ⟨m₂.map (Ideal.Quotient.mk Jac), Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJacle m₂ hm₂)⟩
  have hM : M₁ ≠ M₂ := by
    intro h
    apply hne
    have h' : m₁.map (Ideal.Quotient.mk Jac) = m₂.map (Ideal.Quotient.mk Jac) :=
      congrArg MaximalSpectrum.asIdeal h
    have := congrArg (Ideal.comap (Ideal.Quotient.mk Jac)) h'
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (hJacle m₁ hm₁), sup_eq_left.mpr (hJacle m₂ hm₂)] at this
    exact this.symm
  -- the idempotent `(1, 0, …)` in the product of fields
  let ε : ∀ I : MaximalSpectrum ((N ⧸ J) ⧸ Jac), ((N ⧸ J) ⧸ Jac) ⧸ I.asIdeal :=
    Pi.single M₁ 1
  have hε : IsIdempotentElem ε := by
    change ε * ε = ε
    ext I
    by_cases h : I = M₁
    · subst h; simp [ε]
    · simp [ε, h]
  let εC : (N ⧸ J) ⧸ Jac := e.symm ε
  have hεC : IsIdempotentElem εC := by
    change εC * εC = εC
    simp only [εC, ← map_mul, hε.eq]
  -- lift along the nilpotent Jacobson radical
  have hker : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk Jac), IsNilpotent x := by
    intro x hx
    rw [Ideal.mk_ker] at hx
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    have : x ^ n ∈ Jac ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact Ideal.mem_bot.mp this
  obtain ⟨εB, hεB, hεBmk⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk Jac) hker εC (RingHom.mem_range.mpr (Ideal.Quotient.mk_surjective εC)) hεC
  -- lift to `N` by henselianity
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective εB
  obtain ⟨eN, heN, heNb⟩ :=
    exists_isIdempotentElem_sub_mem_of_isIntegral_of_henselian (maximalIdeal A) b hεB
  have heNmk : Ideal.Quotient.mk J eN = Ideal.Quotient.mk J b := Ideal.Quotient.eq.mpr heNb
  -- a domain has no nontrivial idempotents
  have hε0 : ε ≠ 0 := by
    intro h
    have h1 := congrFun h M₁
    simp only [ε, Pi.single_eq_same, Pi.zero_apply] at h1
    haveI : Nontrivial (((N ⧸ J) ⧸ Jac) ⧸ M₁.asIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr M₁.isMaximal.ne_top
    exact one_ne_zero h1
  have hε1 : ε ≠ 1 := by
    intro h
    have h1 := congrFun h M₂
    simp only [ε, Pi.single_eq_of_ne hM.symm, Pi.one_apply] at h1
    haveI : Nontrivial (((N ⧸ J) ⧸ Jac) ⧸ M₂.asIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr M₂.isMaximal.ne_top
    exact zero_ne_one h1
  rcases IsIdempotentElem.eq_zero_or_eq_one_of_isDomain heN with h0 | h1
  · apply hε0
    have hC : εC = 0 := by
      rw [← hεBmk, ← heNmk, h0, map_zero, map_zero]
    have := congrArg e hC
    simpa [εC] using this
  · apply hε1
    have hC : εC = 1 := by
      rw [← hεBmk, ← heNmk, h1, map_one, map_one]
    have := congrArg e hC
    simpa [εC] using this

end HenselianFinite

section SepClosedSplitting

/-- Separable closedness transfers along a ring equivalence of fields. -/
theorem IsSepClosed.of_ringEquiv {K K' : Type*} [Field K] [Field K'] [IsSepClosed K]
    (e : K ≃+* K') : IsSepClosed K' := by
  constructor
  intro p hp
  have hq : (p.map e.symm.toRingHom).Separable := hp.map
  have hsplit := IsSepClosed.splits_of_separable _ hq
  have := hsplit.map e.toRingHom
  rwa [Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id] at this

/-- A finite étale local algebra over a local ring with separably closed residue field is the
base ring: its closed fibre is a finite separable field extension of a separably closed field,
hence trivial, and Nakayama gives rank one.

This is `StrictlyHenselianLocalRing.bijective_algebraMap_of_finite_etale_local` with the
henselian hypothesis removed; the proof never used it. -/
theorem bijective_algebraMap_of_finite_etale_local_of_isSepClosed
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsSepClosed (ResidueField R)] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Algebra.Etale R S] :
    Function.Bijective (algebraMap R S) := by
  let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hresidue : Function.Bijective
      (algebraMap (ResidueField R) (ResidueField S)) :=
    IsSepClosed.algebraMap_bijective _ _
  have hresidueRank : Module.finrank (ResidueField R) (ResidueField S) = 1 :=
    Module.finrank_of_bijective_algebraMap hresidue
  have hRank : Module.finrank R S = 1 := by
    rw [IsLocalRing.finrank_eq_finrank_residueField]
    exact hresidueRank
  let _ : Module.Free R S := Module.free_of_flat_of_isLocalRing
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hRank

/-- The algebra equivalence form of `bijective_algebraMap_of_finite_etale_local_of_isSepClosed`. -/
noncomputable def finiteEtaleLocalAlgEquivOfIsSepClosed
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsSepClosed (ResidueField R)] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S] [Algebra.Etale R S] :
    S ≃ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R S)
    (bijective_algebraMap_of_finite_etale_local_of_isSepClosed R S)).symm

end SepClosedSplitting

section Faithful

/-- A nontrivial flat algebra over a domain is faithful: a nonzero scalar acts injectively, so it
cannot kill `1`. -/
theorem faithfulSMul_of_flat_of_isDomain (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Nontrivial B] [Algebra A B] [Module.Flat A B] : FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hreg : IsSMulRegular B r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_iff_ne_zero.mpr hr0)
  have : r • (1 : B) = r • (0 : B) := by
    rw [smul_zero, Algebra.smul_def, mul_one]
    exact hr
  exact one_ne_zero (hreg this)

end Faithful

section RootCover

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (a : A) {E : ℕ}

/-- The root cover `A' = A[x] ⧸ (x^E − a)` of the proof of Stacks `0EYG`, written with the unit
`1` of `Pcf.LocalModel.localPoly`. -/
abbrev StrictRootCover (a : A) (E : ℕ) : Type u :=
  AdjoinRoot (Pcf.LocalModel.localPoly (1 : Aˣ) a E)

/-- The distinguished root `x` of the root cover. -/
noncomputable abbrev strictRoot (a : A) (E : ℕ) : StrictRootCover a E :=
  AdjoinRoot.root (Pcf.LocalModel.localPoly (1 : Aˣ) a E)

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem strictRoot_pow :
    strictRoot a E ^ E = algebraMap A (StrictRootCover a E) a := by
  rw [strictRoot, Pcf.LocalModel.root_pow_eq]
  simp

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem strictRootCover_finite (hE : 1 ≤ E) : Module.Finite A (StrictRootCover a E) :=
  Pcf.LocalModel.finite_adjoinRoot 1 a hE

omit [IsLocalRing A] in
theorem strictRootCover_isNoetherianRing (hE : 1 ≤ E) : IsNoetherianRing (StrictRootCover a E) :=
  have := strictRootCover_finite a hE
  IsNoetherianRing.of_finite A _

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem strictRootCover_isIntegral (hE : 1 ≤ E) : Algebra.IsIntegral A (StrictRootCover a E) :=
  AdjoinRoot.isIntegral_of_monic (Pcf.LocalModel.localPoly_monic 1 a hE)

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem strictRootCover_degree_pos [Nontrivial A] (hE : 1 ≤ E) :
    0 < (Pcf.LocalModel.localPoly (1 : Aˣ) a E).degree := by
  rw [Polynomial.degree_eq_natDegree (Pcf.LocalModel.localPoly_monic 1 a hE).ne_zero,
    Pcf.LocalModel.localPoly_natDegree]
  exact_mod_cast hE

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem strictRootCover_faithfulSMul [Nontrivial A] (hE : 1 ≤ E) :
    FaithfulSMul A (StrictRootCover a E) :=
  AdjoinRoot.faithfulSMul_of_monic_of_degree_pos (Pcf.LocalModel.localPoly_monic 1 a hE)
    (strictRootCover_degree_pos a hE)

omit [IsNoetherianRing A] [IsLocalRing A] in
theorem strictRootCover_isLocalHom [Nontrivial A] (hE : 1 ≤ E) :
    IsLocalHom (algebraMap A (StrictRootCover a E)) :=
  AdjoinRoot.isLocalHom_of_monic_of_degree_pos (Pcf.LocalModel.localPoly_monic 1 a hE)
    (strictRootCover_degree_pos a hE)

omit [IsNoetherianRing A] in
/-- The root lies in every maximal ideal of the root cover when `a` lies in the maximal ideal of
`A`. -/
theorem strictRoot_mem_of_isMaximal (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E)
    (I : Ideal (StrictRootCover a E)) [I.IsMaximal] : strictRoot a E ∈ I := by
  have := strictRootCover_isIntegral a hE
  apply Ideal.IsPrime.mem_of_pow_mem (I := I) inferInstance E
  rw [strictRoot_pow a]
  exact map_maximalIdeal_le_of_isMaximal_of_isIntegral A (StrictRootCover a E) I
    (Ideal.mem_map_of_mem _ ha)

omit [IsNoetherianRing A] in
theorem strictRoot_mem_jacobson (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E) :
    Ideal.span ({strictRoot a E} : Set (StrictRootCover a E)) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.jacobson, Ideal.mem_sInf]
  rintro I ⟨-, hI⟩
  exact strictRoot_mem_of_isMaximal a ha hE I

omit [IsNoetherianRing A] in
/-- `A' ⧸ (x) ≅ A ⧸ (a)` is local, so the root cover is local. -/
theorem strictRootCover_isLocalRing (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E) :
    IsLocalRing (StrictRootCover a E) := by
  have hne : Ideal.span ({a} : Set A) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal a).mp ha
  have : Nontrivial (A ⧸ Ideal.span ({a} : Set A)) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (A ⧸ Ideal.span ({a} : Set A)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Nontrivial (StrictRootCover a E ⧸ Ideal.span ({strictRoot a E} :
      Set (StrictRootCover a E))) :=
    (Pcf.LocalModel.quotientRootEquiv 1 a hE).toEquiv.nontrivial
  have : IsLocalRing (StrictRootCover a E ⧸ Ideal.span ({strictRoot a E} :
      Set (StrictRootCover a E))) :=
    IsLocalRing.of_surjective' (Pcf.LocalModel.quotientRootEquiv 1 a hE).symm.toRingHom
      (Pcf.LocalModel.quotientRootEquiv 1 a hE).symm.surjective
  exact isLocalRing_of_quotient_of_le_jacobson _ (strictRoot_mem_jacobson a ha hE)

omit [IsNoetherianRing A] in
theorem strictRoot_mem_maximalIdeal (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E) :
    letI := strictRootCover_isLocalRing a ha hE
    strictRoot a E ∈ maximalIdeal (StrictRootCover a E) := by
  letI := strictRootCover_isLocalRing a ha hE
  exact strictRoot_mem_of_isMaximal a ha hE _

omit [IsNoetherianRing A] in
/-- The root cover has the same residue field as the base: every element of `A[x] ⧸ (x^E − a)`
is congruent to a constant modulo the maximal ideal, which contains `x`. -/
theorem strictRootCover_residueField_bijective (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E) :
    letI := strictRootCover_isLocalRing a ha hE
    letI := strictRootCover_isLocalHom a hE
    Function.Bijective (ResidueField.map (algebraMap A (StrictRootCover a E))) := by
  letI := strictRootCover_isLocalRing a ha hE
  letI := strictRootCover_isLocalHom a hE
  refine ⟨(ResidueField.map _).injective, fun y ↦ ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨IsLocalRing.residue A (p.coeff 0), ?_⟩
  rw [ResidueField.map_residue]
  apply Ideal.Quotient.eq.mpr
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have : AdjoinRoot.mk (Pcf.LocalModel.localPoly (1 : Aˣ) a E) p -
      algebraMap A (StrictRootCover a E) (p.coeff 0) =
      strictRoot a E * AdjoinRoot.mk (Pcf.LocalModel.localPoly (1 : Aˣ) a E) q := by
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← map_sub, hq, map_mul, AdjoinRoot.mk_X]
  rw [← neg_mem_iff, neg_sub, this]
  exact Ideal.mul_mem_right _ _ (strictRoot_mem_maximalIdeal a ha hE)

omit [IsNoetherianRing A] in
/-- The residue field of the root cover is separably closed when that of the base is. -/
theorem strictRootCover_residueField_isSepClosed (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E)
    [IsSepClosed (ResidueField A)] :
    letI := strictRootCover_isLocalRing a ha hE
    IsSepClosed (ResidueField (StrictRootCover a E)) := by
  letI := strictRootCover_isLocalRing a ha hE
  letI := strictRootCover_isLocalHom a hE
  exact IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective _ (strictRootCover_residueField_bijective a ha hE))

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The root is a nonzerodivisor of the root cover when `a` is one in `A`. -/
theorem strictRoot_mem_nonZeroDivisors (hE : 1 ≤ E) (ha0 : a ∈ nonZeroDivisors A) :
    strictRoot a E ∈ nonZeroDivisors (StrictRootCover a E) :=
  Pcf.LocalModel.root_mem_nonZeroDivisors 1 a hE ha0

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- `A' ⧸ (x) ≅ A ⧸ (a)` is regular local when `A ⧸ (a)` is. -/
theorem strictRootCover_quotient_isRegularLocalRing (hE : 1 ≤ E)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    IsRegularLocalRing (StrictRootCover a E ⧸
      Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))) :=
  IsRegularLocalRing.of_ringEquiv (Pcf.LocalModel.quotientRootEquiv 1 a hE).symm.toRingEquiv

/-- **The root cover is regular local** (Stacks `00NU` applied to `x`). -/
theorem strictRootCover_isRegularLocalRing (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E)
    (ha0 : a ∈ nonZeroDivisors A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    IsRegularLocalRing (StrictRootCover a E) := by
  letI := strictRootCover_isLocalRing a ha hE
  letI := strictRootCover_isNoetherianRing a hE
  letI := strictRootCover_quotient_isRegularLocalRing a hE
  exact Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor (strictRoot a E)
    (strictRoot_mem_maximalIdeal a ha hE) (strictRoot_mem_nonZeroDivisors a hE ha0)

theorem strictRootCover_isDomain (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E)
    (ha0 : a ∈ nonZeroDivisors A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    IsDomain (StrictRootCover a E) :=
  have := strictRootCover_isRegularLocalRing a ha hE ha0
  isDomain_of_isRegularLocalRing _

theorem strictRootCover_isIntegrallyClosed (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E)
    (ha0 : a ∈ nonZeroDivisors A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    IsIntegrallyClosed (StrictRootCover a E) :=
  have := strictRootCover_isRegularLocalRing a ha hE ha0
  have := isRegularRing_of_isRegularLocalRing (StrictRootCover a E)
  have := strictRootCover_isDomain a ha hE ha0
  isIntegrallyClosed_of_isRegularRing (StrictRootCover a E)

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The root generates a prime ideal of the root cover. -/
theorem strictRootCover_span_root_isPrime (hE : 1 ≤ E)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    (Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))).IsPrime := by
  have := strictRootCover_quotient_isRegularLocalRing a hE
  have : IsDomain (StrictRootCover a E ⧸
      Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))) :=
    isDomain_of_isRegularLocalRing _
  exact Ideal.Quotient.isDomain_iff_prime _ |>.mp inferInstance

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The prime `(x)` of the root cover lies over the prime `(a)` of the base. -/
theorem strictRootCover_span_root_under (hE : 1 ≤ E) :
    (Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))).under A =
      Ideal.span ({a} : Set A) := by
  ext r
  rw [Ideal.mem_under, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem,
    ← (Pcf.LocalModel.quotientRootEquiv 1 a hE).map_eq_zero_iff]
  change (Pcf.LocalModel.quotientRootEquiv 1 a hE)
    (algebraMap A (StrictRootCover a E ⧸ _) r) = 0 ↔ _
  rw [AlgEquiv.commutes]
  rfl

/-- The prime `(x)` of the root cover has height one. -/
theorem strictRootCover_span_root_height_eq_one (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E)
    (ha0 : a ∈ nonZeroDivisors A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    (Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))).height = 1 := by
  letI := strictRootCover_isNoetherianRing a hE
  letI := strictRootCover_isLocalRing a ha hE
  letI := strictRootCover_isRegularLocalRing a ha hE ha0
  apply divisorPrime_height_eq_one _ (strictRoot_mem_maximalIdeal a ha hE)
  exact nonZeroDivisors.ne_zero (strictRoot_mem_nonZeroDivisors a hE ha0)

/-- The localization of the root cover at the prime `(x)` is a discrete valuation ring. -/
theorem strictRootCover_localization_span_root_isDiscreteValuationRing
    (ha : a ∈ maximalIdeal A) (hE : 1 ≤ E) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] :
    letI := strictRootCover_span_root_isPrime a hE
    letI := strictRootCover_isDomain a ha hE ha0
    IsDiscreteValuationRing (Localization.AtPrime
      (Ideal.span ({strictRoot a E} : Set (StrictRootCover a E)))) := by
  letI := strictRootCover_isNoetherianRing a hE
  letI := strictRootCover_isLocalRing a ha hE
  letI := strictRootCover_isRegularLocalRing a ha hE ha0
  letI := strictRootCover_span_root_isPrime a hE
  letI := strictRootCover_isDomain a ha hE ha0
  exact divisorLocalization_isDiscreteValuationRing _ (strictRoot_mem_maximalIdeal a ha hE)
    (nonZeroDivisors.ne_zero (strictRoot_mem_nonZeroDivisors a hE ha0))

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- The quotient of the root cover by `(x)` is a regular ring; this is the
`[IsRegularRing (A' ⧸ (x))]` input of Tag `0EYE` over the root cover. -/
theorem strictRootCover_quotient_isRegularRing (hE : 1 ≤ E)
    [IsRegularRing (A ⧸ Ideal.span ({a} : Set A))] :
    IsRegularRing (StrictRootCover a E ⧸
      Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))) :=
  standardCover_rootQuotient_isRegularRing 1 a hE

end RootCover

#print axioms divisorLocalization_irreducible
#print axioms isLocalRing_of_quotient_of_le_jacobson
#print axioms isLocalRing_of_isDomain_of_finite_of_henselian
#print axioms bijective_algebraMap_of_finite_etale_local_of_isSepClosed
#print axioms faithfulSMul_of_flat_of_isDomain
#print axioms strictRootCover_isLocalRing
#print axioms strictRootCover_residueField_bijective
#print axioms strictRootCover_residueField_isSepClosed
#print axioms strictRootCover_isRegularLocalRing
#print axioms strictRootCover_span_root_under
#print axioms strictRootCover_localization_span_root_isDiscreteValuationRing

end Pcf.Stacks
