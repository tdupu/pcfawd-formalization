/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingPCF

/-!
# `ex:frobenius-pinching`: the restriction `f|_B : u ↦ u²` is PCF

The pinched axis `B = Spec k[x^p]` has coordinate `u = x^p`, and `f|_B` is
`pinchedAxisSquare : u ↦ u²` (`FrobeniusPinchingGenerators.pinchedAxisSquare_u`).
When `2 ≠ 0` in `k`, it is generically separable, étale off `u = 0`, and its only weighted
branch point is the fixed point `u = 0`, so it is PCF in the paper's sense.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingAxisPCF

open AlgebraicGeometry CategoryTheory MvPolynomial
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators
open Pcf.Examples.PaperP.CoordinateSquareEtale (sq sqScheme sqScheme_stalk_formallyEtale)
open Pcf.Examples.PaperP.FrobeniusPinchingPCF (iso_stalk_formallyEtale)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]

abbrev Q := MvPolynomial PUnit.{u+1} k

/-- The coordinate identification `k[X] ≃ k[x^p]`, `X ↦ u = x^p`. -/
noncomputable def ψ : Q k ≃ₐ[k] axisPowers k p :=
  (MvPolynomial.uniqueAlgEquiv k PUnit.{u+1}).trans (axisPowerEquiv k p (Fact.out : p.Prime).pos)

/-- The coordinate `u = x^p` on `B`. -/
noncomputable def uB : axisPowers k p := axisPowerMap k p Polynomial.X

theorem ψ_X : ψ k p (X PUnit.unit) = uB k p := by
  simp [ψ, uB, axisPowerEquiv]

theorem uB_ne_zero : uB k p ≠ 0 := by
  rw [← ψ_X]
  exact (map_ne_zero_iff _ (ψ k p).injective).mpr (X_ne_zero _)

theorem pinchedAxisSquare_ψ :
    (pinchedAxisSquare k p).comp (ψ k p).toAlgHom = (ψ k p).toAlgHom.comp (sq k PUnit.{u+1} PUnit.unit) := by
  apply MvPolynomial.algHom_ext
  intro i
  change pinchedAxisSquare k p (ψ k p (X i)) = ψ k p (sq k PUnit.{u+1} PUnit.unit (X i))
  rw [show i = PUnit.unit from rfl, CoordinateSquareEtale.sq_X_self, map_pow, ψ_X]
  exact pinchedAxisSquare_u k p

/-- `B = Spec k[x^p]` and `g = f|_B`. -/
noncomputable abbrev Bs := Spec (.of (axisPowers k p))

noncomputable def g : Bs k p ⟶ Bs k p :=
  Spec.map (CommRingCat.ofHom (pinchedAxisSquare k p).toRingHom)

noncomputable def eS : Bs k p ⟶ Spec (.of (Q k)) :=
  Spec.map (CommRingCat.ofHom (ψ k p).toRingHom)

noncomputable def eS' : Spec (.of (Q k)) ⟶ Bs k p :=
  Spec.map (CommRingCat.ofHom (ψ k p).symm.toRingHom)

theorem eS_eS' : eS k p ≫ eS' k p = 𝟙 _ := by
  unfold eS eS'
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun x => (ψ k p).apply_symm_apply x

theorem eS'_eS : eS' k p ≫ eS k p = 𝟙 _ := by
  unfold eS eS'
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun x => (ψ k p).symm_apply_apply x

instance eS_isIso : IsIso (eS k p) := ⟨eS' k p, eS_eS' k p, eS'_eS k p⟩
instance eS'_isIso : IsIso (eS' k p) := ⟨eS k p, eS'_eS k p, eS_eS' k p⟩

theorem g_eq : g k p = eS k p ≫ sqScheme k PUnit.{u+1} PUnit.unit ≫ eS' k p := by
  unfold g eS sqScheme eS'
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun a => ?_
  change pinchedAxisSquare k p a = ψ k p (sq k PUnit.{u+1} PUnit.unit ((ψ k p).symm a))
  have h := congrArg (fun φ : Q k →ₐ[k] axisPowers k p => φ ((ψ k p).symm a))
    (pinchedAxisSquare_ψ k p)
  simp only [AlgHom.comp_apply] at h
  have ha : ((ψ k p).toAlgHom : Q k → axisPowers k p) ((ψ k p).symm a) = a :=
    (ψ k p).apply_symm_apply a
  rw [ha] at h
  exact h

/-- `g` is formally étale at every point with `u ∉ q`. -/
theorem g_stalk_formallyEtale (h2 : (2 : k) ≠ 0) (q : Bs k p) (hq : uB k p ∉ q.asIdeal) :
    ((g k p).stalkMap q).hom.FormallyEtale := by
  rw [g_eq, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
  refine RingHom.FormallyEtale.comp ?_ (iso_stalk_formallyEtale _ _)
  refine RingHom.FormallyEtale.comp (iso_stalk_formallyEtale _ _) ?_
  apply sqScheme_stalk_formallyEtale k PUnit.{u+1} PUnit.unit h2
  change (X PUnit.unit : Q k) ∉ (q.asIdeal).comap (ψ k p).toRingHom
  rw [Ideal.mem_comap]
  change ψ k p (X PUnit.unit) ∉ q.asIdeal
  rw [ψ_X]
  exact hq


/-- The point `u = 0` of `Spec k[X]`. -/
noncomputable def zeroQ : Spec (.of (Q k)) :=
  ⟨Ideal.span {(X PUnit.unit : Q k)},
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr MvPolynomial.X_prime⟩

theorem zeroQ_coheight : Order.coheight (zeroQ k) = 1 := by
  rw [← AlgebraicGeometry.idealHeight_eq_coheight]
  let P : Ideal (Q k) := Ideal.span {(X PUnit.unit : Q k)}
  haveI : P.IsPrime := (zeroQ k).2
  change P.height = 1
  apply le_antisymm
  · apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · have hbot : (⊥ : Ideal (Q k)) < P := by
      rw [bot_lt_iff_ne_bot]
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact X_ne_zero _ h
    have h0 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rwa [Ideal.height_bot, zero_add] at h0

theorem eq_zeroQ (q : Spec (.of (Q k))) (hq : Order.coheight q = 1)
    (hi : (X PUnit.unit : Q k) ∈ q.asIdeal) : q = zeroQ k := by
  have hh : q.asIdeal.height = 1 := by
    rw [AlgebraicGeometry.idealHeight_eq_coheight]
    exact hq
  let P : Ideal (Q k) := Ideal.span {(X PUnit.unit : Q k)}
  haveI : P.IsPrime := (zeroQ k).2
  have hPq : P ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hi
  by_contra hne
  have hlt : P < q.asIdeal := lt_of_le_of_ne hPq (fun h => hne (PrimeSpectrum.ext h.symm))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hP : P.height = 1 := by
    have := zeroQ_coheight k
    rw [← AlgebraicGeometry.idealHeight_eq_coheight] at this
    exact this
  rw [hh, hP] at h1
  exact absurd h1 (by norm_num)

/-- The point `u = 0` of `B`. -/
noncomputable def zeroB : Bs k p := eS' k p (zeroQ k)

theorem eS_zeroB : eS k p (zeroB k p) = zeroQ k := by
  unfold zeroB
  rw [← Scheme.Hom.comp_apply, eS'_eS]
  rfl

theorem zeroB_coheight : Order.coheight (zeroB k p) = 1 :=
  (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (eS' k p)).trans (zeroQ_coheight k)

theorem uB_mem_iff (q : Bs k p) : uB k p ∈ q.asIdeal ↔ (X PUnit.unit : Q k) ∈ (eS k p q).asIdeal := by
  change _ ↔ (X PUnit.unit : Q k) ∈ (q.asIdeal).comap (ψ k p).toRingHom
  rw [Ideal.mem_comap]
  change _ ↔ ψ k p (X PUnit.unit) ∈ q.asIdeal
  rw [ψ_X]

/-- The only codimension-one point of `B` containing `u` is `u = 0`. -/
theorem eq_zeroB (q : Bs k p) (hq : Order.coheight q = 1) (hu : uB k p ∈ q.asIdeal) :
    q = zeroB k p := by
  have h1 : Order.coheight (eS k p q) = 1 :=
    (AlgebraicGeometry.coheight_eq_of_isOpenImmersion (eS k p)).trans hq
  have h2 := eq_zeroQ k (eS k p q) h1 ((uB_mem_iff k p q).mp hu)
  have : eS' k p (eS k p q) = eS' k p (zeroQ k) := by rw [h2]
  rwa [← Scheme.Hom.comp_apply, eS_eS'] at this

instance B_isIntegrallyClosed : IsIntegrallyClosed (axisPowers k p) :=
  IsIntegrallyClosed.of_equiv (ψ k p).toRingEquiv

instance B_isNormal : Pcf.IsNormalScheme (Bs k p) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro q
  haveI : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of (axisPowers k p)) q).symm.commRingCatIsoToRingEquiv


instance B_noetherian : IsNoetherianRing (axisPowers k p) :=
  isNoetherianRing_of_ringEquiv (Q k) (ψ k p).toRingEquiv

theorem sqQ_eq_expand : sq k PUnit.{u+1} PUnit.unit = MvPolynomial.expand 2 := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [show i = PUnit.unit from rfl, CoordinateSquareEtale.sq_X_self, MvPolynomial.expand_X]

theorem sqQ_injective : Function.Injective (sq k PUnit.{u+1} PUnit.unit) := by
  rw [sqQ_eq_expand]
  exact MvPolynomial.expand_injective (by decide : 0 < 2)

theorem sqQ_finite : (sq k PUnit.{u+1} PUnit.unit).toRingHom.Finite := by
  let φ := sq k PUnit.{u+1} PUnit.unit
  have hft : φ.toRingHom.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (Q k))
    have heq : φ.toRingHom.comp (algebraMap k (Q k)) = algebraMap k (Q k) :=
      RingHom.ext fun a => φ.commutes a
    rw [heq]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hint : φ.toRingHom.IsIntegral := by
    letI : Algebra (Q k) (Q k) := φ.toRingHom.toAlgebra
    have hX : IsIntegral (Q k) (X PUnit.unit : Q k) := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (X PUnit.unit),
        Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      change X PUnit.unit ^ 2 - φ (X PUnit.unit) = 0
      rw [CoordinateSquareEtale.sq_X_self, sub_self]
    have htop : ∀ z : Q k, IsIntegral (Q k) z := by
      intro z
      have hz : z ∈ Algebra.adjoin k (Set.range (X : PUnit.{u+1} → Q k)) := by
        rw [MvPolynomial.adjoin_range_X]; trivial
      induction hz using Algebra.adjoin_induction with
      | mem w hw =>
          obtain ⟨j, rfl⟩ := hw
          exact hX
      | algebraMap r =>
          have : algebraMap k (Q k) r = algebraMap (Q k) (Q k) (algebraMap k (Q k) r) := by
            change _ = φ (algebraMap k (Q k) r)
            rw [φ.commutes]
          rw [this]
          exact isIntegral_algebraMap
      | add a b _ _ ha hb => exact ha.add hb
      | mul a b _ _ ha hb => exact ha.mul hb
    exact htop
  exact hint.to_finite hft

theorem sqSchemeQ_finite : IsFinite (sqScheme k PUnit.{u+1} PUnit.unit) :=
  (IsFinite.SpecMap_iff _).mpr (sqQ_finite k)

theorem sqSchemeQ_surjective : Surjective (sqScheme k PUnit.{u+1} PUnit.unit) := by
  rw [surjective_iff]
  exact (sqQ_finite k).to_isIntegral.comap_surjective (sqQ_injective k)

instance g_finite : IsFinite (g k p) := by
  haveI := sqSchemeQ_finite k
  rw [g_eq]
  infer_instance

instance g_surjective : Surjective (g k p) := by
  haveI := sqSchemeQ_surjective k
  rw [g_eq]
  infer_instance

instance g_dominant : IsDominant (g k p) := inferInstance

/-- `g` fixes `u = 0`. -/
theorem g_zeroB : g k p (zeroB k p) = zeroB k p := by
  let A : Pcf.SchemeDivisorPoint (Bs k p) := ⟨zeroB k p, zeroB_coheight k p⟩
  apply eq_zeroB k p _ (Pcf.coheight_apply_eq_one (g k p) A)
  change uB k p ∈ ((zeroB k p).asIdeal).comap (pinchedAxisSquare k p).toRingHom
  rw [Ideal.mem_comap]
  change pinchedAxisSquare k p (uB k p) ∈ _
  rw [uB, pinchedAxisSquare_u, pow_two]
  apply Ideal.mul_mem_left
  exact (uB_mem_iff k p _).mpr (by rw [eS_zeroB]; exact Ideal.mem_span_singleton_self _)

instance B_normalization_isIso : IsIso (Pcf.Palomar.normalizationMap (Bs k p)) :=
  Pcf.normalScheme_normalizationMap_isIso _

/-- The weighted branch points of `g` are just `u = 0`. -/
theorem g_weightedBranchPointSet_subset (h2 : (2 : k) ≠ 0) :
    Pcf.weightedBranchPointSet (g k p) ⊆ {zeroB k p} := by
  rw [Pcf.weightedBranchPointSet_eq_schemeDelta_image_of_normal]
  rintro _ ⟨d, hd, rfl⟩
  have hu : uB k p ∈ d.1.asIdeal := by
    by_contra hu
    have := Pcf.schemeDivisorDelta_eq_one_of_formallyEtale (g k p) d
      (g_stalk_formallyEtale k p h2 d.1 hu)
    change 1 < Pcf.schemeDivisorDelta (g k p) d at hd
    omega
  have := eq_zeroB k p d.1 d.2 hu
  change g k p d.1 = zeroB k p
  rw [this, g_zeroB]

/-- The structure morphism `B → Spec k`. -/
noncomputable def structureMapB : Bs k p ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (axisPowers k p)))

instance structureMapB_finiteType : LocallyOfFiniteType (structureMapB k p) := by
  haveI : Algebra.FiniteType k (axisPowers k p) :=
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType k (Q k)) (ψ k p)
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **`f|_B : u ↦ u²` is PCF** (when `2 ≠ 0` in `k`).

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem g_isSeparableNormalizedPCF (h2 : (2 : k) ≠ 0) :
    Pcf.IsSeparableNormalizedPCF k (structureMapB k p) (g k p) := by
  apply (Pcf.isSeparableNormalizedPCF_iff_downstairs k (structureMapB k p) _).2
  refine ⟨?_, ?_⟩
  · apply Pcf.isGenericallySeparable_of_formallyEtale_generic
    apply g_stalk_formallyEtale k p h2
    rw [genericPoint_eq_bot_of_affine]
    exact uB_ne_zero k p
  · apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite k
      (structureMapB k p) _).2
    apply (Set.finite_singleton (zeroB k p)).subset
    intro q hq
    simp only [Pcf.weightedPostcriticalPointSet, Set.mem_iUnion] at hq
    obtain ⟨n, z, hz, rfl⟩ := hq
    have hz' := g_weightedBranchPointSet_subset k p h2 hz
    rw [Set.mem_singleton_iff] at hz' ⊢
    subst hz'
    induction n with
    | zero => rfl
    | succ n ih =>
        change (g k p : _ → _)^[n + 1] (zeroB k p) = _
        rw [Function.iterate_succ_apply']
        rw [show (g k p : _ → _)^[n] (zeroB k p) = zeroB k p from ih, g_zeroB]

/-- `g` is the restriction `u ↦ u²` of the descended map. -/
theorem g_is_square : pinchedAxisSquare k p (uB k p) = uB k p ^ 2 := pinchedAxisSquare_u k p

#print axioms g_stalk_formallyEtale
#print axioms g_weightedBranchPointSet_subset
#print axioms g_isSeparableNormalizedPCF

end Pcf.Examples.PaperP.FrobeniusPinchingAxisPCF
