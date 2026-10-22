/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NormalizationSchemeBridge
public import Pcf.Bounding.AllCodimBlowupNormalizedExceptionalChart

/-!
# The normalized blow-up is an isomorphism off the centre

At a point of the normalized Rees blow-up whose image in the affine base
avoids the centre, the stalk map of the structural morphism is an
isomorphism. The Rees `Proj` is a localization of the base on a standard
chart there, and the absolute normalization does not change a normal stalk.
This is used in `latex/paper-p.tex`, proof of Theorem `thm:allcodim-normal`,
where away from the exceptional divisor the blow-ups are isomorphisms and the
local ramification of `F_m` agrees with that of `f^{ms}`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- An integral birational morphism is an isomorphism on stalks at points
whose image stalk is integrally closed. -/
theorem stalkMap_bijective_of_isIntegralHom_of_integrallyClosed
    {N X : Scheme.{u}} [IsIntegral N] [IsIntegral X]
    (f : N ⟶ X) [IsIntegralHom f] [IsDominant f] (w : N)
    (hbir : IsStalkBirationalAt f w)
    (hint : IsIntegrallyClosed (X.presheaf.stalk (f w))) :
    Function.Bijective (f.stalkMap w).hom := by
  refine ⟨stalkMap_injective_of_dominant_integral f w, ?_⟩
  let B := X.presheaf.stalk (f w)
  let L := N.presheaf.stalk w
  let K := N.functionField
  let φ := (f.stalkMap w).hom
  letI : Algebra B K := ((algebraMap L K).comp φ).toAlgebra
  letI : IsFractionRing B K := hbir
  obtain ⟨U, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f w ∈ (⊤ : X.Opens) from trivial)
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let wV : V := ⟨w, hwU⟩
  letI : Algebra Γ(N, V) L := TopCat.Presheaf.algebra_section_stalk _ wV
  letI : IsLocalization.AtPrime L (hV.primeIdealOf wV).asIdeal := hV.isLocalization_stalk wV
  -- germs of sections lie in the image of the stalk map
  have hgerm (c : Γ(N, V)) : ∃ y : B, φ y = algebraMap Γ(N, V) L c := by
    obtain ⟨p, hpm, hp⟩ := f.isIntegral_app U hU c
    have hcomm : (N.presheaf.germ V w hwU).hom.comp (f.app U).hom =
        φ.comp (X.presheaf.germ U (f w) hwU).hom := by
      ext a
      exact (f.germ_stalkMap_apply U w hwU a).symm
    have hint' : IsIntegral B (algebraMap L K (algebraMap Γ(N, V) L c)) := by
      refine ⟨p.map (X.presheaf.germ U (f w) hwU).hom, hpm.map _, ?_⟩
      have h0 := Polynomial.hom_eval₂ p (f.app U).hom
        ((algebraMap L K).comp (N.presheaf.germ V w hwU).hom) c
      rw [hp, map_zero, RingHom.comp_assoc, hcomm] at h0
      rw [Polynomial.eval₂_map]
      exact h0.symm
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := K)).mp hint'
    exact ⟨y, IsFractionRing.injective L K hy⟩
  intro z
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hV.primeIdealOf wV).asIdeal.primeCompl z
  obtain ⟨u, hu⟩ := hgerm c
  obtain ⟨v, hv⟩ := hgerm s
  have hsunit : IsUnit (φ v) := by
    rw [hv]
    exact IsLocalization.map_units L s
  have hvunit : IsUnit v := isUnit_of_map_unit φ v hsunit
  refine ⟨u * ↑hvunit.unit⁻¹, ?_⟩
  refine (IsLocalization.eq_mk'_iff_mul_eq).mpr ?_
  rw [← hv, ← hu, ← map_mul, mul_assoc, hvunit.val_inv_mul, mul_one]

#print axioms stalkMap_bijective_of_isIntegralHom_of_integrallyClosed

/-- A ring map that becomes surjective after inverting one element `c`
(every element of the target times a power of `c` comes from the source)
induces an isomorphism of localizations at any prime not containing `c`. -/
theorem localization_map_bijective_of_away_surjective
    {A₀ A : Type*} [CommRing A₀] [CommRing A] [IsDomain A]
    (θ : A₀ →+* A) (hinj : Function.Injective θ) (c : A₀)
    (hc : ∀ z : A, ∃ (n : ℕ) (r : A₀), θ c ^ n * z = θ r)
    (𝔓 : Ideal A) [𝔓.IsPrime] (hc𝔓 : θ c ∉ 𝔓)
    (𝔭 : Ideal A₀) [𝔭.IsPrime] (h𝔭 : 𝔭 = 𝔓.comap θ)
    {Rp Ap : Type*} [CommRing Rp] [CommRing Ap] [Algebra A₀ Rp] [Algebra A Ap]
    [IsLocalization.AtPrime Rp 𝔭] [IsLocalization.AtPrime Ap 𝔓]
    (ψ : Rp →+* Ap) (hψ : ψ.comp (algebraMap A₀ Rp) = (algebraMap A Ap).comp θ) :
    Function.Bijective ψ := by
  subst h𝔭
  have hψa (r : A₀) : ψ (algebraMap A₀ Rp r) = algebraMap A Ap (θ r) :=
    congrArg (fun g : A₀ →+* Ap => g r) hψ
  have hAinj : Function.Injective (algebraMap A Ap) :=
    IsLocalization.injective Ap 𝔓.primeCompl_le_nonZeroDivisors
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝔓.comap θ).primeCompl z
    have h1 : ψ (algebraMap A₀ Rp r) = 0 := by
      have hspec : ψ (IsLocalization.mk' Rp r s) * ψ (algebraMap A₀ Rp s) =
          ψ (algebraMap A₀ Rp r) := by
        rw [← map_mul, IsLocalization.mk'_spec]
      rw [← hspec, hz, zero_mul]
    rw [hψa, ← map_zero (algebraMap A Ap)] at h1
    have hr : r = 0 := hinj ((hAinj h1).trans (map_zero θ).symm)
    change IsLocalization.mk' Rp r s = 0
    rw [hr, IsLocalization.mk'_zero]
  · intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl z
    obtain ⟨n, r, hr⟩ := hc a
    obtain ⟨m, r', hr'⟩ := hc t
    have hcn (k : ℕ) : θ c ^ k ∉ 𝔓 := fun h => hc𝔓 (Ideal.IsPrime.mem_of_pow_mem ‹_› k h)
    have hden : r' * c ^ n ∈ (𝔓.comap θ).primeCompl := by
      change θ (r' * c ^ n) ∉ 𝔓
      rw [map_mul, ← hr', map_pow]
      intro h
      rcases Ideal.IsPrime.mem_or_mem ‹_› h with h | h
      · rcases Ideal.IsPrime.mem_or_mem ‹_› h with h | h
        · exact hcn m h
        · exact t.2 h
      · exact hcn n h
    refine ⟨IsLocalization.mk' Rp (r * c ^ m) ⟨r' * c ^ n, hden⟩, ?_⟩
    change _ = IsLocalization.mk' Ap a t
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    have hunit : IsUnit (algebraMap A Ap (θ c)) :=
      IsLocalization.map_units Ap (⟨θ c, hc𝔓⟩ : 𝔓.primeCompl)
    apply (hunit.pow (n + m)).mul_left_cancel
    have key := congrArg ψ (IsLocalization.mk'_spec Rp (r * c ^ m) ⟨r' * c ^ n, hden⟩)
    rw [map_mul, hψa, hψa] at key
    simp only [map_mul, map_pow] at key ⊢
    rw [← hr, ← hr'] at key
    simp only [map_mul, map_pow] at key
    linear_combination key

#print axioms localization_map_bijective_of_away_surjective

/-- On the spectrum of a ring, the prime of a point in the global affine
chart is the point itself, read through `Γ(Spec R, ⊤) ≅ R`. -/
theorem mem_primeIdealOf_top_Spec_iff (R : Type u) [CommRing R] (x : Spec (.of R)) (r : R) :
    (Scheme.ΓSpecIso (.of R)).inv.hom r ∈
        ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨x, trivial⟩).asIdeal ↔
      r ∈ x.asIdeal := by
  have h := (isAffineOpen_top (Spec (.of R))).fromSpec_primeIdealOf ⟨x, trivial⟩
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have h' : (Spec.map (Scheme.ΓSpecIso (.of R)).inv)
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨x, trivial⟩) = x := h
  have key : r ∈ x.asIdeal ↔ r ∈ ((Spec.map (Scheme.ΓSpecIso (.of R)).inv)
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨x, trivial⟩)).asIdeal := by
    rw [h']
  rw [key]
  rfl

/-- A bijective stalk map preserves the codimension of the point. -/
theorem coheight_eq_of_stalkMap_bijective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : Function.Bijective (f.stalkMap x).hom) :
    Order.coheight x = Order.coheight (f x) := by
  have h := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hf)
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact (WithBot.coe_inj.mp h).symm

/-- A bijective ring map is formally étale. -/
theorem RingHom.formallyEtale_of_bijective' {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) : f.FormallyEtale := by
  letI := f.toAlgebra
  change Algebra.FormallyEtale A B
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hf)

/-- Formal étaleness of stalk maps transfers through a commuting square whose
vertical stalk maps are bijective. -/
theorem formallyEtale_stalkMap_iff_of_square {X' Y X₀ Y₀ : Scheme.{u}}
    (F : X' ⟶ Y) (α : X' ⟶ X₀) (β : Y ⟶ Y₀) (g : X₀ ⟶ Y₀) (h : F ≫ β = α ≫ g)
    (w : X') (hα : Function.Bijective (α.stalkMap w).hom)
    (hβ : Function.Bijective (β.stalkMap (F w)).hom) :
    (F.stalkMap w).hom.FormallyEtale ↔ (g.stalkMap (α w)).hom.FormallyEtale := by
  have hsq := Scheme.Hom.stalkMap_congr_hom (F ≫ β) (α ≫ g) h w
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hsq
  let c := (Y₀.presheaf.stalkCongr (.of_eq <| h ▸ rfl :
    Inseparable ((F ≫ β) w) ((α ≫ g) w)))
  have hc : Function.Bijective c.hom.hom := ConcreteCategory.bijective_of_isIso c.hom
  have hcinv : Function.Bijective c.inv.hom := ConcreteCategory.bijective_of_isIso c.inv
  have hring : (F.stalkMap w).hom.comp (β.stalkMap (F w)).hom =
      (α.stalkMap w).hom.comp ((g.stalkMap (α w)).hom.comp c.hom.hom) := by
    rw [← CommRingCat.hom_comp, hsq]
    rfl
  let eα := RingEquiv.ofBijective _ hα
  let eβ := RingEquiv.ofBijective _ hβ
  constructor
  · intro hF
    have h1 : ((F.stalkMap w).hom.comp (β.stalkMap (F w)).hom).FormallyEtale :=
      RingHom.FormallyEtale.comp (RingHom.formallyEtale_of_bijective' _ hβ) hF
    rw [hring] at h1
    have h2 := RingHom.FormallyEtale.comp
      (RingHom.FormallyEtale.comp (RingHom.formallyEtale_of_bijective' _ hcinv) h1)
      (RingHom.formallyEtale_of_bijective' eα.symm.toRingHom eα.symm.bijective)
    have key : eα.symm.toRingHom.comp
        (((α.stalkMap w).hom.comp ((g.stalkMap (α w)).hom.comp c.hom.hom)).comp c.inv.hom) =
        (g.stalkMap (α w)).hom := by
      apply RingHom.ext
      intro z
      change eα.symm ((α.stalkMap w).hom ((g.stalkMap (α w)).hom
        (c.hom.hom (c.inv.hom z)))) = _
      have hci : c.hom.hom (c.inv.hom z) = z := by
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
      rw [hci]
      exact eα.symm_apply_apply _
    rw [key] at h2
    exact h2
  · intro hg
    have h1 : ((α.stalkMap w).hom.comp ((g.stalkMap (α w)).hom.comp c.hom.hom)).FormallyEtale :=
      RingHom.FormallyEtale.comp
        (RingHom.FormallyEtale.comp (RingHom.formallyEtale_of_bijective' _ hc) hg)
        (RingHom.formallyEtale_of_bijective' _ hα)
    rw [← hring] at h1
    have h2 := RingHom.FormallyEtale.comp
      (RingHom.formallyEtale_of_bijective' eβ.symm.toRingHom eβ.symm.bijective) h1
    convert h2 using 1
    ext z
    simp only [RingHom.comp_apply]
    change _ = (F.stalkMap w).hom (eβ (eβ.symm z))
    rw [RingEquiv.apply_symm_apply]

#print axioms coheight_eq_of_stalkMap_bijective
#print axioms formallyEtale_stalkMap_iff_of_square

end
end Pcf

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {R : Type u} [CommRing R] [IsDomain R]

attribute [local instance] reesProjChartAlgebra

/-- On a standard chart, every chart element times a power of the chart
coordinate comes from the base. -/
theorem reesProjChart_exists_pow_mul (I : Ideal R) (c : I) (z : reesProjChart I c) :
    ∃ (n : ℕ) (r : R), reesProjChartBaseMap I c ((c : R) ^ n) * z =
      reesProjChartBaseMap I c r := by
  let e := reesProjChartAlgEquiv I c
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers c.1) (e z : Localization.Away c.1)
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, r, e.injective ?_⟩
  apply Subtype.ext
  change ((e (algebraMap R (reesProjChart I c) ((c : R) ^ n) * z) :
      affineBlowupChart I c) : Localization.Away c.1) =
    ((e (algebraMap R (reesProjChart I c) r) : affineBlowupChart I c) : Localization.Away c.1)
  rw [map_mul, e.commutes, e.commutes]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  rw [mul_comm]
  have hn' : (c : R) ^ n = s := hn
  rw [hn']
  exact hrs

/-- The base map into a nonzero standard chart is injective. -/
theorem reesProjChart_algebraMap_injective (I : Ideal R) (c : I) (hc : (c : R) ≠ 0) :
    Function.Injective (reesProjChartBaseMap I c) := by
  let e := reesProjChartAlgEquiv I c
  intro x y hxy
  have h1 : (e (algebraMap R (reesProjChart I c) x) : Localization.Away c.1) =
      (e (algebraMap R (reesProjChart I c) y) : Localization.Away c.1) :=
    congrArg (fun t => ((e t : affineBlowupChart I c) : Localization.Away c.1)) hxy
  rw [e.commutes, e.commutes] at h1
  simp only [Subalgebra.coe_algebraMap] at h1
  exact IsLocalization.injective (Localization.Away c.1)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hc) h1

/-- Every centre element factors through the chart coordinate on its chart. -/
theorem reesProjChart_algebraMap_mem_center (I : Ideal R) (c b : I) :
    ∃ t : reesProjChart I c, reesProjChartBaseMap I c b =
      reesProjChartBaseMap I c c * t := by
  let e := reesProjChartAlgEquiv I c
  refine ⟨e.symm (chartRatio I c b), e.injective ?_⟩
  apply Subtype.ext
  change ((e (algebraMap R (reesProjChart I c) b) : affineBlowupChart I c) :
      Localization.Away c.1) =
    ((e (algebraMap R (reesProjChart I c) c * e.symm (chartRatio I c b)) :
      affineBlowupChart I c) : Localization.Away c.1)
  rw [map_mul, e.commutes, e.commutes, AlgEquiv.apply_symm_apply]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, chartRatio_val]
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]

/-- **The Rees blow-up is an isomorphism off the centre, on stalks.** -/
theorem reesProjToSpec_stalkMap_bijective (I : Ideal R) (P : reesProj I)
    (hP : ¬ I ≤ (reesProjToSpec I P).asIdeal) :
    Function.Bijective ((reesProjToSpec I).stalkMap P).hom := by
  classical
  obtain ⟨b, hbI, hbx⟩ := Set.not_subset.mp hP
  have hPtop : P ∈ (⨆ c : I, reesProjStandardOpen I c) := by
    rw [iSup_reesProjStandardOpen_eq_top]
    trivial
  obtain ⟨c, hPc⟩ := TopologicalSpace.Opens.mem_iSup.mp hPtop
  have hc0 : (c : R) ≠ 0 := by
    intro h
    have hc : c = 0 := Subtype.ext h
    subst hc
    rw [reesProjStandardOpen_zero] at hPc
    exact hPc
  let ρ := reesProjToSpec I
  let U := reesProjStandardOpen I c
  have hU : IsAffineOpen U := reesProjStandardOpen_isAffine I c
  have hUle : U ≤ ρ ⁻¹ᵁ ⊤ := le_preimage_top _ _
  let θ := (ρ.appLE ⊤ U hUle).hom
  let eS := reesProjStandardOpen_sectionsIso I c
  let Γi := (Scheme.ΓSpecIso (.of R)).inv.hom
  have hθ (r : R) : θ (Γi r) = eS.inv.hom (reesProjChartBaseMap I c r) := by
    have h := congrArg (fun φ => φ.hom r) (reesProjToSpec_appLE_standardOpen I c)
    exact h
  have hΓsurj : Function.Surjective Γi :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2
  have heSinj : Function.Injective eS.inv.hom :=
    (ConcreteCategory.bijective_of_isIso eS.inv).1
  letI : IsDomain (reesProjChart I c) := reesProjChart_isDomain_of_nonzero I c hc0
  letI : IsDomain Γ(reesProj I, U) :=
    Function.Injective.isDomain eS.hom.hom (ConcreteCategory.bijective_of_isIso eS.hom).1
  let 𝔓 := (hU.primeIdealOf ⟨P, hPc⟩).asIdeal
  let c0 := Γi c
  have hinj : Function.Injective θ := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hΓsurj x
    obtain ⟨y', rfl⟩ := hΓsurj y
    rw [hθ, hθ] at hxy
    rw [reesProjChart_algebraMap_injective I c hc0 (heSinj hxy)]
  have hc : ∀ z, ∃ (n : ℕ) (r : Γ(Spec (.of R), ⊤)), θ c0 ^ n * z = θ r := by
    intro z
    obtain ⟨n, r, h⟩ := reesProjChart_exists_pow_mul I c (eS.hom.hom z)
    refine ⟨n, Γi r, ?_⟩
    rw [hθ, hθ]
    apply (ConcreteCategory.bijective_of_isIso eS.hom).1
    rw [map_mul, map_pow, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, ← map_pow]
    exact h
  have hcomap := IsAffineOpen.comap_primeIdealOf_appLE (f := ρ) ⊤ (isAffineOpen_top _) U hU
    hUle hPc
  have hc𝔓 : θ c0 ∉ 𝔓 := by
    intro hmem
    obtain ⟨t, ht⟩ := reesProjChart_algebraMap_mem_center I c ⟨b, hbI⟩
    have hb𝔓 : θ (Γi b) ∈ 𝔓 := by
      rw [hθ]
      change eS.inv.hom (reesProjChartBaseMap I c b) ∈ 𝔓
      rw [ht, map_mul, ← hθ]
      exact Ideal.mul_mem_right _ _ hmem
    have hb' : Γi b ∈
        ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨ρ P, hUle hPc⟩).asIdeal := by
      rw [← hcomap]
      exact hb𝔓
    exact hbx ((Pcf.mem_primeIdealOf_top_Spec_iff R (ρ P) b).mp hb')
  have hIJ : ((isAffineOpen_top (Spec (.of R))).primeIdealOf ⟨ρ P, hUle hPc⟩).asIdeal =
      𝔓.comap θ := congr($(hcomap).1).symm
  let ψ := Localization.localRingHom _ 𝔓 θ hIJ
  have hψ : ψ.comp (algebraMap _ _) = (algebraMap _ (Localization.AtPrime 𝔓)).comp θ := by
    ext x
    simp [ψ, Localization.localRingHom_to_map]
  have hbij := Pcf.localization_map_bijective_of_away_surjective θ hinj c0 hc 𝔓 hc𝔓 _ hIJ ψ hψ
  let e := IsAffineOpen.arrowStalkMapIso ρ ⊤ (isAffineOpen_top _) U hU hUle hPc
  have hiso : IsIso (CommRingCat.ofHom ψ) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have h := ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff e).mpr hiso
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- **The normalized blow-up is an isomorphism off the centre, on stalks.**
At a point of the absolute normalization of the Rees blow-up whose image in
`Spec R` avoids `V(I)`, the stalk map of the structural morphism is
bijective. -/
theorem normalizedReesToSpec_stalkMap_bijective [IsIntegrallyClosed R]
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (w : (letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      Palomar.normalization (reesProj I)))
    (hw : ¬ I ≤ ((letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) w).asIdeal) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    Function.Bijective
      ((Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I).stalkMap w).hom := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let ν := Palomar.normalizationMap (reesProj I)
  let ρ := reesProjToSpec I
  have hρ := reesProjToSpec_stalkMap_bijective I (ν w) hw
  letI : IsDomain Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  letI : IsIntegrallyClosed Γ(Spec (.of R), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let x : (⊤ : (Spec (.of R)).Opens) := ⟨ρ (ν w), trivial⟩
  letI : Algebra Γ(Spec (.of R), ⊤) ((Spec (.of R)).presheaf.stalk (ρ (ν w))) :=
    TopCat.Presheaf.algebra_section_stalk _ x
  letI : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk (ρ (ν w)))
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf x).asIdeal :=
    (isAffineOpen_top _).isLocalization_stalk x
  have hSpec : IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk (ρ (ν w))) :=
    isIntegrallyClosed_of_isLocalization _
      ((isAffineOpen_top (Spec (.of R))).primeIdealOf x).asIdeal.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hrees : IsIntegrallyClosed ((reesProj I).presheaf.stalk (ν w)) :=
    IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective _ hρ)
  have hν := Pcf.stalkMap_bijective_of_isIntegralHom_of_integrallyClosed ν w
    (schemeGlobalNormalizationMap_stalkBirationalAt (reesProj I) w) hrees
  rw [Scheme.Hom.stalkMap_comp]
  exact hν.comp hρ

#print axioms reesProjToSpec_stalkMap_bijective
#print axioms normalizedReesToSpec_stalkMap_bijective

end
end Pcf.Bounding.AllCodimBlowup
