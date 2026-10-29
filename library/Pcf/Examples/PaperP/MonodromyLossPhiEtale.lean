/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiFinite
public import Pcf.Examples.PaperP.MonodromyLossCurveRegular
public import Mathlib.RingTheory.Unramified.Dedekind
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# `φ = 1 + ι` is flat and étale (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "`F(P, z) = (φ(P), 1/z)` is an étale
degree-2 self-map".

* `phi1_injective`, **`phi_isDominant`**: `x₃ = i(x² - 1)/x` is transcendental over `k`
  (`x` is a root of `i X² - x₃ X - i`), so `phi1` is injective (`A` is integral over `k[x]`).
* `A_finite_y`, **`A_isDedekindDomain`**: `A` is finite and standard étale over `k[y]`, hence
  Dedekind (Mathlib's `IsDedekindDomain.of_formallyUnramified`).
* **`isBezout_stalk`**: every local ring of `E` is a Bézout domain (a DVR or a field).
* `phi_stalkMap_injective`, **`phi_flat`**: the stalk maps of `φ` are injective, so
  torsion-free over Bézout domains, hence flat (Stacks 0539, through Mathlib).
* **`phi_etale`**: flat, formally unramified and locally of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section Dominant
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

include hi in
theorem i_ne_zero : i ≠ 0 := by
  rintro rfl
  have h3 : (3 : k) = 0 := CharP.cast_eq_zero k 3
  have : (1 : k) = 0 := by linear_combination hi
  exact one_ne_zero this

omit [CharP k 3] in
theorem Ax_X_transcendental : Transcendental k (algebraMap (A k) (Ax k) (xA k)) := by
  rw [transcendental_iff_injective]
  have h1 : Function.Injective (algebraMap (A k) (Ax k)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (xA_ne_zero k))
  have h2 : (Polynomial.aeval (algebraMap (A k) (Ax k) (xA k)) : k[X] →ₐ[k] Ax k) =
      (IsScalarTower.toAlgHom k (A k) (Ax k)).comp
        ((Polynomial.aeval (xA k) : k[X] →ₐ[k] A k)) := by
    ext; simp
  rw [h2]
  refine h1.comp ?_
  have h3 : (Polynomial.aeval (xA k) : k[X] →ₐ[k] A k).toRingHom =
      AdjoinRoot.of (W k).polynomial := by
    apply Polynomial.ringHom_ext
    · intro a; simp [A_algebraMap_eq]
    · simp [xA]
  intro p q hpq
  have := congrArg (fun f => f p) h3
  have := congrArg (fun f => f q) h3
  exact A_of_injective k (by simp_all)

include hi in
/-- `x₃ = i(x² - 1)/x` is transcendental over `k`. -/
theorem x3_transcendental :
    Transcendental k (phi1 k i hi (xA k)) := by
  haveI : IsDomain (Ax k) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (xA_ne_zero k))
  set xx := algebraMap (A k) (Ax k) (xA k)
  set U := invX k
  set c := algebraMap k (Ax k) i
  have hx3 : phi1 k i hi (xA k) = c * (xx ^ 2 - 1) * U := liftA_x k _ _ _
  rw [hx3]
  intro halg
  set z := c * (xx ^ 2 - 1) * U
  have hXU : xx * U = 1 := IsLocalization.Away.mul_invSelf (xA k)
  let S := Algebra.adjoin k {z}
  haveI : Algebra.IsAlgebraic k S :=
    (Subalgebra.isAlgebraic_iff S).mp (Algebra.isAlgebraic_adjoin_singleton_iff.mpr halg)
  have hzS : z ∈ S := Algebra.subset_adjoin rfl
  have hc0 : c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap k (Ax k)).injective]; exact i_ne_zero k i hi
  -- `x` is a root of `c T² - z T - c` over `S`
  have halgX : IsAlgebraic S xx := by
    refine ⟨C (algebraMap k S i) * X ^ 2 - C ⟨z, hzS⟩ * X - C (algebraMap k S i), ?_, ?_⟩
    · intro h
      have := congrArg (fun p => p.coeff 2) h
      simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, ite_true,
        mul_one, coeff_zero] at this
      norm_num at this
      exact i_ne_zero k i hi this
    · simp only [map_sub, map_mul, aeval_C, aeval_X_pow, aeval_X]
      change algebraMap k (Ax k) i * xx ^ 2 - z * xx - algebraMap k (Ax k) i = 0
      simp only [z]
      linear_combination (c - c * xx ^ 2) * hXU
  exact (Ax_X_transcendental k) (halgX.restrictScalars k)

include hi in
/-- **`phi1` is injective.** -/
theorem phi1_injective : Function.Injective (phi1 k i hi) := by
  have hint : Algebra.IsIntegral k[X] (A k) :=
    AdjoinRoot.isIntegral_of_monic (WeierstrassCurve.Affine.monic_polynomial)
  have hcomp : (phi1 k i hi).comp (algebraMap k[X] (A k)) =
      (Polynomial.aeval (phi1 k i hi (xA k)) : k[X] →ₐ[k] Ax k).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rw [show algebraMap k[X] (A k) (C a) = algebraMap k (A k) a from A_algebraMap_eq k a,
        phi1_algebraMap]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_under_eq_bot (R := k[X])
  rw [eq_bot_iff]
  intro p hp
  rw [Ideal.mem_comap, RingHom.mem_ker] at hp
  have ht := x3_transcendental k i hi
  rw [transcendental_iff_injective] at ht
  have : (Polynomial.aeval (phi1 k i hi (xA k)) : k[X] →ₐ[k] Ax k) p = 0 := by
    rw [← hp]
    exact (congrArg (fun f => f p) hcomp).symm
  exact (Ideal.mem_bot).mpr (ht (this.trans (map_zero _).symm))

include hi in
instance SpecMap_phi1_isDominant : IsDominant (Spec.map (CommRingCat.ofHom (phi1 k i hi))) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (phi1 k i hi))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro r hr
  have : r = 0 := phi1_injective k i hi (by simpa using hr)
  simp [this]

instance ιA_isDominant : IsDominant (ιA k) := by
  constructor
  have hne : (Set.range (ιA k)).Nonempty := ⟨_, ⟨⊥, Ideal.isPrime_bot⟩, rfl⟩
  exact ((ιA k).isOpenEmbedding.isOpenMap.isOpen_range).dense hne

/-- **`φ` is dominant.** -/
instance phi_isDominant : IsDominant (phi k i hi) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ ιA k ≫
      phi k i hi) := by
    rw [pieceA_phi1]; infer_instance
  have : IsDominant ((Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ ιA k) ≫
      phi k i hi) := by rwa [Category.assoc]
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ax k))) ≫ ιA k)
    (phi k i hi)

end Dominant

section Flat
variable (k : Type u) [Field k] [CharP k 3]

omit [CharP k 3] in
/-- `A` is finite over `k[y]` (`x` is a root of `X³ - X - y²`). -/
theorem A_finite_y : @Module.Finite k[X] (A k) _ _ (algY k).toModule := by
  letI := algY k
  have hxint : IsIntegral k[X] (xA k) := by
    refine ⟨fA k, fA_monic k, ?_⟩
    rw [← aeval_def]
    simp only [fA, map_sub, map_pow, aeval_X, aeval_C, algY_apply]
    rw [A_rel]; ring
  have hadj : Algebra.adjoin k[X] {xA k} = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    have ha : a ∈ Algebra.adjoin k {xA k, yA k} := by rw [A_adjoin]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact Algebra.subset_adjoin rfl
      · have : yA k = algebraMap k[X] (A k) X := by rw [algY_apply, aeval_X]
        rw [this]; exact Subalgebra.algebraMap_mem _ _
    | algebraMap c =>
      have : algebraMap k (A k) c = algebraMap k[X] (A k) (C c) := by rw [algY_apply, aeval_C]
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine ⟨?_⟩
  rw [← Algebra.top_toSubmodule, ← hadj]
  exact hxint.fg_adjoin_singleton

/-- **`A` is a Dedekind domain** (finite and étale over the PID `k[y]`). -/
instance A_isDedekindDomain : IsDedekindDomain (A k) := by
  letI := algY k
  haveI : Algebra.IsStandardEtale k[X] (A k) := A_isStandardEtale k
  haveI : Module.Finite k[X] (A k) := A_finite_y k
  exact IsDedekindDomain.of_formallyUnramified k[X] (A k)

omit [CharP k 3] in
theorem isFractionRing_atPrime_bot {R : Type u} [CommRing R] [IsDomain R] :
    IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
  have h : (⊥ : Ideal R).primeCompl = nonZeroDivisors R := by
    ext r
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsFractionRing
  rw [← h]
  infer_instance

omit [CharP k 3] in
/-- The localization of a Dedekind domain at a prime is Bézout (a DVR or a field). -/
theorem isBezout_localization_of_dedekind {R : Type u} [CommRing R] [IsDedekindDomain R]
    (p : Ideal R) [p.IsPrime] : IsBezout (Localization.AtPrime p) := by
  by_cases hp : p = ⊥
  · subst hp
    haveI := isFractionRing_atPrime_bot (R := R)
    let e := IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R)
      (Localization.AtPrime (⊥ : Ideal R))
    exact Function.Surjective.isBezout e.toRingEquiv.toRingHom e.surjective
  · haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp
      (Localization.AtPrime p)
    infer_instance

omit [CharP k 3] in
theorem isBezout_stalk_of_isOpenImmersion {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (u : Spec R ⟶ Y) [IsOpenImmersion u] (p : Spec R)
    (h : IsBezout (Localization.AtPrime p.asIdeal)) :
    IsBezout (Y.presheaf.stalk (u p)) := by
  have : IsIso (u.stalkMap p) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 p
  let e := (asIso (u.stalkMap p) ≪≫ Spec.stalkIso R p).commRingCatIsoToRingEquiv
  exact Function.Surjective.isBezout e.symm.toRingHom e.symm.surjective

/-- **Every local ring of `E` is a Bézout domain.** -/
theorem isBezout_stalk (x : E k) : IsBezout ((E k).presheaf.stalk x) := by
  rcases chart_cover k x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact isBezout_stalk_of_isOpenImmersion (ιA k) p
      (isBezout_localization_of_dedekind p.asIdeal)
  · by_cases hw : wB k ∈ p.asIdeal
    · haveI := B_localization_isDVR k p.asIdeal hw
      exact isBezout_stalk_of_isOpenImmersion (ιB k) p inferInstance
    · obtain ⟨q, hq⟩ := ιB_mem_range_ιA k p hw
      rw [← hq]
      exact isBezout_stalk_of_isOpenImmersion (ιA k) q
        (isBezout_localization_of_dedekind q.asIdeal)

omit [CharP k 3] in
/-- On an integral scheme, specialization maps of stalks are injective. -/
theorem stalkSpecializes_injective {X : Scheme.{u}} [IsIntegral X] {y x : X} (h : y ⤳ x) :
    Function.Injective (X.presheaf.stalkSpecializes h) := by
  intro s₁ s₂ hs
  obtain ⟨U, hxU, t₁, rfl⟩ := X.presheaf.exists_germ_eq s₁
  obtain ⟨V, hxV, t₂, rfl⟩ := X.presheaf.exists_germ_eq s₂
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply,
    TopCat.Presheaf.germ_stalkSpecializes_apply] at hs
  -- compare on `U ⊓ V`
  have e1 := X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) x ⟨hxU, hxV⟩ t₁
  have e2 := X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) x ⟨hxU, hxV⟩ t₂
  have f1 := X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) y
    ⟨h.mem_open U.isOpen hxU, h.mem_open V.isOpen hxV⟩ t₁
  have f2 := X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) y
    ⟨h.mem_open U.isOpen hxU, h.mem_open V.isOpen hxV⟩ t₂
  rw [← e1, ← e2]
  rw [← f1, ← f2] at hs
  rw [germ_injective_of_isIntegral (X := X) y _ hs]

/-- A ring hom out of a ring that is a field is injective. -/
theorem injective_of_isField {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (hR : IsField R) (f : R →+* S) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h0
  obtain ⟨r', hr'⟩ := hR.mul_inv_cancel h0
  have := congrArg f hr'
  rw [map_mul, hr, zero_mul, map_one] at this
  exact zero_ne_one this

variable (i : k) (hi : i ^ 2 = -1)

/-- **The stalk maps of `φ` are injective.** -/
theorem phi_stalkMap_injective (x : E k) : Function.Injective ((phi k i hi).stalkMap x) := by
  have h := genericPoint_specializes x
  have key := (phi k i hi).stalkSpecializes_stalkMap (genericPoint (E k)) x h
  have hgp : phi k i hi (genericPoint (E k)) = genericPoint (E k) := by
    apply ((genericPoint_spec (E k)).eq _).symm
    convert! (genericPoint_spec (E k)).image (phi k i hi).continuous
    rw [Set.image_univ, (phi k i hi).denseRange.closure_range]
  let e := ((E k).presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hF : IsField ((E k).presheaf.stalk (phi k i hi (genericPoint (E k)))) :=
    e.toMulEquiv.isField (Field.toIsField ((E k).functionField))
  have h1 : Function.Injective
      ((E k).presheaf.stalkSpecializes ((phi k i hi).base.hom.map_specializes h) ≫
        (phi k i hi).stalkMap (genericPoint (E k))) := by
    intro a b hab
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hab
    exact stalkSpecializes_injective _
      (injective_of_isField hF ((phi k i hi).stalkMap (genericPoint (E k))).hom hab)
  rw [key] at h1
  intro a b hab
  exact h1 (by rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hab])

/-- **`φ` is flat**: its stalk maps are injective maps out of Bézout domains. -/
instance phi_flat : Flat (phi k i hi) := by
  refine Flat.of_stalkMap _ fun x => ?_
  haveI := isBezout_stalk k (phi k i hi x)
  have hinj := phi_stalkMap_injective k i hi x
  set f := ((phi k i hi).stalkMap x).hom
  letI := f.toAlgebra
  change Module.Flat _ _
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro s hs
  obtain ⟨⟨a, ha⟩, has⟩ := (Submodule.mem_torsion_iff s).mp hs
  rw [Submodule.mem_bot]
  change f a * s = 0 at has
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hfa : f a ≠ 0 := fun h => ha0 (hinj (h.trans (map_zero f).symm))
  exact (mul_eq_zero.mp has).resolve_left hfa

instance phi_locallyOfFinitePresentation : LocallyOfFinitePresentation (phi k i hi) := by
  haveI : IsNoetherianRing (A k) := Algebra.FiniteType.isNoetherianRing k (A k)
  haveI : IsNoetherianRing (B k) := Algebra.FiniteType.isNoetherianRing k (B k)
  refine phi_prop_of_pieces k i hi @LocallyOfFinitePresentation (fun f _ => inferInstance)
    ?_ ?_ ?_
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      (piece_finiteType k i hi _ (ιA k) _ (ιA k) (pieceA_phi1 k i hi).symm)
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      (piece_finiteType k i hi _ (ιB k) _ (ιA k) (pieceA_phi2 k i hi).symm)
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      (piece_finiteType k i hi _ (ιB k) _ (ιB k) (pieceB_phi3 k i hi).symm)

/-- **`φ = 1 + ι : E ⟶ E` is étale.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
instance phi_etale : Etale (phi k i hi) :=
  Etale.of_formallyUnramified_of_flat _

end Flat

#print axioms phi1_injective
#print axioms phi_isDominant
#print axioms A_isDedekindDomain
#print axioms phi_flat
#print axioms phi_etale

end Pcf.Examples.PaperP.MonodromyLossCurve
