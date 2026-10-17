/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.AffineTameLocal

/-!
# Transfer of codimension-one tameness to the chart at `y`

`isTamelyRamifiedInCodimensionOneAlong_localizedNormalization`: if `Spec B → Spec R_a` is tame in
codimension one along `V(a)` in the chart form `IsTamelyRamifiedAlongDivisor a B` (the form in which
the scheme-level definition of Stacks Section 58.31, Tag `0BSE`, reads on an affine open), then the
normalization `N_y` of the local ring `R_y` in `R_y ⊗_R B` satisfies pcf's affine predicate
`IsTamelyRamifiedInCodimensionOneAlong (R_y) (N_y) a`, the tameness hypothesis of the affine
statement `AbhyankarLemmaTameOfFinite`.

For a prime `q` of `N_y` over a height-one prime `𝔭' ∋ a` of `R_y` with `𝔭 = 𝔭' ∩ R`:
`R_𝔭` is a discrete valuation ring (`00NU` with `00PD`), `K_𝔭 = R_𝔭[1/a]`
(`isLocalization_away_fractionRing`), so `K_𝔭 ⊗_R B` is the localization of `B_y` at `𝔭'ᶜ`
(`isLocalization_genericFiberAtContraction`), the integral closure `C_𝔭` of `R_𝔭` in it is the
localization of `N_y` (Mathlib's `IsLocalization.integralClosure`;
`isLocalization_normalizationAtContraction`), `q C_𝔭` is a maximal ideal
(`isMaximal_map_normalizationAtContraction`), and tameness at `q C_𝔭` (given by
`IsTamelyRamifiedAlongDivisor`) is tameness at `q` (`isTamelyRamifiedAt_of_isLocalization`).
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing Algebra

set_option linter.style.haveILetI false

namespace Pcf.Stacks.SchemeLevel.AffineTame

/-- In a discrete valuation ring, the fraction field is obtained by inverting any nonzero
non-unit. -/
theorem isLocalization_away_fractionRing {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (x : A) (hx0 : x ≠ 0) (hxu : ¬IsUnit x) :
    IsLocalization.Away x (FractionRing A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hx0)).isUnit
  · intro k
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) k
    have hs0 : (s : A) ≠ 0 := nonZeroDivisors.ne_zero s.2
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hϖ
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hxu (hk.isUnit_iff.mpr (by simp))
    -- `s ∣ x ^ m`
    have hdvd : (s : A) ∣ x ^ m := by
      have h1 : (s : A) ∣ ϖ ^ m := hm.dvd
      have h2 : ϖ ^ m ∣ x ^ m := by
        have : ϖ ^ m ∣ (ϖ ^ k) ^ m := by
          rw [← pow_mul]; exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk0))
        exact this.trans (hk.symm.pow_pow (n := m)).dvd
      exact h1.trans h2
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨m, r * t, ?_⟩
    rw [map_mul, ← map_pow, ht, map_mul, ← mul_assoc, IsLocalization.mk'_spec_mk]
  · intro u v huv
    exact ⟨0, by simpa using IsFractionRing.injective A (FractionRing A) huv⟩

section Transfer

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
  (y : Ideal R) [y.IsPrime]

include Ra in
/-- The image of `a_y` in `B_y` is a unit (`a` is already inverted in `B`). -/
theorem isUnit_localizedEquation_localizedCover : IsUnit
    (algebraMap (Localization.AtPrime y) (LocalizedCover B y) (localizedEquation a y)) := by
  have h : IsUnit (algebraMap R B a) := by
    rw [IsScalarTower.algebraMap_apply R Ra B]
    exact (IsLocalization.Away.algebraMap_isUnit a).map _
  have : algebraMap (Localization.AtPrime y) (LocalizedCover B y) (localizedEquation a y) =
      toLocalizedCover B y (algebraMap R B a) := by
    change (algebraMap R (Localization.AtPrime y) a) ⊗ₜ[R] (1 : B) =
      (1 : Localization.AtPrime y) ⊗ₜ[R] algebraMap R B a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [this]
  exact h.map _

/-- The prime `p = p' ∩ R` lies in `y`. -/
theorem comap_le_localizationAtPrime (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime] :
    p'.comap (algebraMap R (Localization.AtPrime y)) ≤ y := by
  intro r hr
  by_contra hry
  have : IsUnit (algebraMap R (Localization.AtPrime y) r) :=
    IsLocalization.map_units (Localization.AtPrime y) (⟨r, hry⟩ : y.primeCompl)
  exact (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.eq_top_of_isUnit_mem p' (Ideal.mem_comap.mp hr) this)

/-- The algebra `R_y → R_𝔭` for `𝔭 = 𝔭' ∩ R`, `𝔭'` a prime of `R_y`. -/
@[instance_reducible]
noncomputable def algebraLocalizationAtContraction (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] :
    Algebra (Localization.AtPrime y)
      (Localization.AtPrime (p'.comap (algebraMap R (Localization.AtPrime y)))) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ y.primeCompl
    (p'.comap (algebraMap R (Localization.AtPrime y))).primeCompl
    (fun _ hx hxp ↦ hx (comap_le_localizationAtPrime y p' hxp))

/-- The scalar tower `R → R_y → R_𝔭` for `𝔭 = 𝔭' ∩ R`. -/
theorem isScalarTower_localizationAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime] :
    letI := algebraLocalizationAtContraction y p'
    IsScalarTower R (Localization.AtPrime y)
      (Localization.AtPrime (p'.comap (algebraMap R (Localization.AtPrime y)))) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime y)
    (Localization.AtPrime (p'.comap (algebraMap R (Localization.AtPrime y)))) y.primeCompl
    (p'.comap (algebraMap R (Localization.AtPrime y))).primeCompl
    (fun _ hx hxp ↦ hx (comap_le_localizationAtPrime y p' hxp))

/-- `R_𝔭` is the localization of `R_y` at `𝔭'`, for `𝔭 = 𝔭' ∩ R`. -/
theorem isLocalization_localizationAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    :
    letI := algebraLocalizationAtContraction y p'
    IsLocalization.AtPrime
      (Localization.AtPrime (p'.comap (algebraMap R (Localization.AtPrime y)))) p' := by
  letI := algebraLocalizationAtContraction y p'
  haveI := isScalarTower_localizationAtContraction y p'
  set p := p'.comap (algebraMap R (Localization.AtPrime y))
  have h1 := IsLocalization.isLocalization_of_submonoid_le (Localization.AtPrime y)
    (Localization.AtPrime p) y.primeCompl p.primeCompl
    (fun _ hx hxp ↦ hx (comap_le_localizationAtPrime y p' hxp))
  refine (IsLocalization.iff_of_le_of_exists_dvd _ p'.primeCompl ?_ ?_).mp h1
  · rintro _ ⟨r, hr, rfl⟩
    exact hr
  · intro n hn
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.primeCompl n
    dsimp only at hn ⊢
    refine ⟨algebraMap R _ r, ⟨r, ?_, rfl⟩, ?_⟩
    · intro hr
      apply hn
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ hr
    · exact ⟨algebraMap R _ s, by rw [IsLocalization.mk'_spec]⟩

attribute [local instance] algebraLocalizationAtContraction

/-- The prime `𝔭 = 𝔭' ∩ R` of `R` below a prime `𝔭'` of `R_y`. -/
abbrev contraction (p' : Ideal (Localization.AtPrime y)) : Ideal R :=
  p'.comap (algebraMap R (Localization.AtPrime y))

/-- `K_𝔭 = Frac(R_𝔭)`. -/
abbrev FractionFieldAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime] : Type u :=
  FractionRing (Localization.AtPrime (contraction y p'))

/-- `K_𝔭 ⊗_R B`. -/
abbrev GenericFiberAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime] : Type u :=
    FractionFieldAtContraction y p' ⊗[R] B

instance isScalarTower_fractionFieldAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    :
    IsScalarTower R (Localization.AtPrime y) (FractionFieldAtContraction y p') := by
  haveI := isScalarTower_localizationAtContraction y p'
  exact IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply (Localization.AtPrime y)
        (Localization.AtPrime (contraction y p'))
      (FractionFieldAtContraction y p'), ← IsScalarTower.algebraMap_apply R (Localization.AtPrime y)
      (Localization.AtPrime (contraction y p')), ← IsScalarTower.algebraMap_apply R
      (Localization.AtPrime (contraction y p')) (FractionFieldAtContraction y p')]

/-- The algebra structure `B_y = R_y ⊗_R B → K_𝔭 ⊗_R B`. -/
@[instance_reducible]
noncomputable def genericFiberAtContractionAlgebra (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] :
    Algebra (LocalizedCover B y) (GenericFiberAtContraction B y p') :=
  (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R (Localization.AtPrime y) (FractionFieldAtContraction y p'))
    (AlgHom.id R B) : Localization.AtPrime y ⊗[R] B →ₐ[R] GenericFiberAtContraction B y
        p').toRingHom.toAlgebra

attribute [local instance] genericFiberAtContractionAlgebra

/-- The algebra map `B_y → K_𝔭 ⊗_R B` on pure tensors. -/
theorem genericFiberAtContraction_algebraMap_tmul (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    (r : Localization.AtPrime y) (b : B) :
    algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p')
        (show LocalizedCover B y from r ⊗ₜ[R] b) =
      algebraMap (Localization.AtPrime y) (FractionFieldAtContraction y p') r ⊗ₜ[R] b :=
  Algebra.TensorProduct.map_tmul _ _ r b

instance isScalarTower_genericFiberAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    :
    IsScalarTower (Localization.AtPrime y) (LocalizedCover B y)
        (GenericFiberAtContraction B y p') :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap (Localization.AtPrime y) (FractionFieldAtContraction y p') r ⊗ₜ[R] (1 : B) =
      algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p') (r ⊗ₜ[R] (1 : B))
    rw [genericFiberAtContraction_algebraMap_tmul]

include Ra in
/-- If `R_𝔭` is a DVR and `a ∈ 𝔭`, then `K_𝔭 ⊗_R B` is the localization of `B_y` at `𝔭'ᶜ`
(inverting `a` is already done in `B`, and `K_𝔭 = R_𝔭[1/a]`). -/
theorem isLocalization_genericFiberAtContraction (ha : a ∈ nonZeroDivisors R)
    (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] (hap : a ∈ contraction y p') [IsDomain (Localization.AtPrime (contraction y p'))]
    [IsDiscreteValuationRing (Localization.AtPrime (contraction y p'))] :
    IsLocalization (algebraMapSubmonoid (LocalizedCover B y) p'.primeCompl)
        (GenericFiberAtContraction B y p') := by
  set Ry := Localization.AtPrime y
  haveI := isScalarTower_localizationAtContraction y p'
  haveI := isLocalization_localizationAtContraction y p'
  set Rp := Localization.AtPrime (contraction y p')
  set K := FractionFieldAtContraction y p'
  have hapRp : algebraMap Ry Rp (localizedEquation a y) = algebraMap R Rp a :=
    (IsScalarTower.algebraMap_apply R Ry Rp a).symm
  have hne : algebraMap Ry Rp (localizedEquation a y) ≠ 0 := by
    rw [hapRp]
    exact nonZeroDivisors.ne_zero
      (IsLocalization.map_nonZeroDivisors_le (contraction y p').primeCompl Rp ⟨a, ha, rfl⟩)
  have hnu : ¬IsUnit (algebraMap Ry Rp (localizedEquation a y)) := by
    rw [hapRp]
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Rp (contraction y p') a).mpr hap))
  haveI : IsLocalization.Away (algebraMap Ry Rp (localizedEquation a y)) K :=
    isLocalization_away_fractionRing _ hne hnu
  haveI hN : IsLocalization (IsLocalization.localizationLocalizationSubmodule p'.primeCompl
      (Submonoid.powers (algebraMap Ry Rp (localizedEquation a y)))) K :=
    IsLocalization.localization_localization_isLocalization p'.primeCompl
      (Submonoid.powers (algebraMap Ry Rp (localizedEquation a y))) K
  set N := IsLocalization.localizationLocalizationSubmodule p'.primeCompl
      (Submonoid.powers (algebraMap Ry Rp (localizedEquation a y)))
  have hloc1 : IsLocalization (algebraMapSubmonoid (LocalizedCover B y) N)
      (LocalizedCover B y ⊗[Ry] K) :=
    IsLocalization.tensor (S := LocalizedCover B y) K N
  have hloc2 : IsLocalization (algebraMapSubmonoid (LocalizedCover B y) p'.primeCompl)
      (LocalizedCover B y ⊗[Ry] K) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd _ (algebraMapSubmonoid (LocalizedCover B y) N) ?_
        ?_).mpr
      hloc1
    · rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, IsLocalization.mem_localizationLocalizationSubmodule.mpr
        ⟨1, ⟨m, hm⟩, by simp⟩, rfl⟩
    · rintro _ ⟨n, hn, rfl⟩
      obtain ⟨⟨_, k, rfl⟩, ⟨z, hz⟩, hnz⟩ :=
        IsLocalization.mem_localizationLocalizationSubmodule.mp hn
      simp only at hnz
      rw [← map_pow] at hnz
      obtain ⟨⟨t, ht⟩, htn⟩ :=
        (IsLocalization.eq_iff_exists p'.primeCompl Rp).mp (hnz.trans (map_mul _ _ _).symm)
      refine ⟨algebraMap Ry (LocalizedCover B y) (t * z), ⟨t * z, mul_mem ht hz, rfl⟩, ?_⟩
      obtain ⟨u, hu⟩ := (isUnit_localizedEquation_localizedCover a Ra B y).pow k
      refine ⟨algebraMap Ry (LocalizedCover B y) t * ↑u⁻¹, ?_⟩
      have := congrArg (algebraMap Ry (LocalizedCover B y)) htn
      simp only [map_mul, map_pow] at this
      rw [← hu] at this
      calc algebraMap Ry (LocalizedCover B y) (t * z)
          = algebraMap Ry (LocalizedCover B y) (t * z) * (↑u * ↑u⁻¹) := by simp
        _ = algebraMap Ry (LocalizedCover B y) n * (algebraMap Ry (LocalizedCover B y) t * ↑u⁻¹) :=
            by
          rw [map_mul]
          linear_combination (↑u⁻¹ : LocalizedCover B y) * this.symm
  let E0 : (LocalizedCover B y ⊗[Ry] K) ≃+* GenericFiberAtContraction B y p' :=
    (Algebra.TensorProduct.comm Ry (LocalizedCover B y) K).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange R Ry K K B).toRingEquiv
  have hE0 : ∀ x : LocalizedCover B y, E0
      (algebraMap (LocalizedCover B y) (LocalizedCover B y ⊗[Ry] K) x) =
      algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p') x := by
    intro x
    change Localization.AtPrime y ⊗[R] B at x
    induction x using TensorProduct.inductionOn with
    | add x z hx hz =>
      change E0
          (algebraMap (LocalizedCover B y) _
              ((show LocalizedCover B y from x) + (show LocalizedCover B y from z))) =
        algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p')
            ((show LocalizedCover B y from x) + (show LocalizedCover B y from z))
      rw [map_add, map_add, hx, hz, map_add]
    | tmul r b =>
      rw [genericFiberAtContraction_algebraMap_tmul]
      change Algebra.TensorProduct.cancelBaseChange R Ry K K B
        ((1 : K) ⊗ₜ[Ry] (show LocalizedCover B y from r ⊗ₜ[R] b)) = _
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
  let E : (LocalizedCover B y ⊗[Ry] K) ≃ₐ[LocalizedCover B y] GenericFiberAtContraction B y p' :=
      AlgEquiv.ofRingEquiv (f := E0) hE0
  exact IsLocalization.isLocalization_of_algEquiv _ E

/-- `C_𝔭`, the integral closure of `R_𝔭` in `K_𝔭 ⊗_R B`. -/
abbrev NormalizationAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime] : Type u :=
  integralClosure (Localization.AtPrime (contraction y p')) (GenericFiberAtContraction B y p')

instance isScalarTower_localizationAtContraction_fractionField (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] :
    IsScalarTower (Localization.AtPrime y) (Localization.AtPrime (contraction y p'))
        (FractionFieldAtContraction y p') := by
  exact IsScalarTower.of_algebraMap_eq (R := Localization.AtPrime y)
    (S := Localization.AtPrime (contraction y p')) (A := FractionFieldAtContraction y p') fun _ ↦
        rfl

/-- The map `N_y → C_𝔭` induced by `B_y → K_𝔭 ⊗_R B`. -/
noncomputable def localizedNormalizationToNormalizationAtContraction
    (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime] :
    LocalizedNormalization B y →+* NormalizationAtContraction B y p' where
  toFun x := ⟨algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p') x.1, by
    have hx : IsIntegral (Localization.AtPrime y) x.1 := x.2
    exact (hx.map (IsScalarTower.toAlgHom (Localization.AtPrime y) (LocalizedCover B y)
      (GenericFiberAtContraction B y p'))).tower_top⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x z := Subtype.ext
      (map_mul (algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p')) x.1 z.1)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x z := Subtype.ext
      (map_add (algebraMap (LocalizedCover B y) (GenericFiberAtContraction B y p')) x.1 z.1)

/-- `C_𝔭` as an `N_y`-algebra, via `localizedNormalizationToNormalizationAtContraction`. -/
@[instance_reducible]
noncomputable def normalizationAtContractionAlgebra (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] :
    Algebra (LocalizedNormalization B y) (NormalizationAtContraction B y p') :=
  (localizedNormalizationToNormalizationAtContraction B y p').toAlgebra

attribute [local instance] normalizationAtContractionAlgebra

/-- `localizedNormalizationToNormalizationAtContraction` is the restriction of the algebra map
`B_y → K_𝔭 ⊗_R B`. -/
theorem localizedNormalizationToNormalizationAtContraction_val (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] (x : LocalizedNormalization B y) :
    ((localizedNormalizationToNormalizationAtContraction B y p' x : NormalizationAtContraction B y
        p') : GenericFiberAtContraction B y p') = algebraMap (LocalizedCover B y)
            (GenericFiberAtContraction B y p') x.1 := rfl

instance isScalarTower_normalizationAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    :
    IsScalarTower (LocalizedNormalization B y) (NormalizationAtContraction B y p')
        (GenericFiberAtContraction B y p') := by
  refine ⟨fun x c s ↦ ?_⟩
  change ((localizedNormalizationToNormalizationAtContraction B y p' x * c :
      NormalizationAtContraction B y p') : GenericFiberAtContraction B y p') * s =
          (x : LocalizedCover B y) • (c * s)
  rw [Subalgebra.coe_mul, localizedNormalizationToNormalizationAtContraction_val, Algebra.smul_def,
      mul_assoc]

instance isScalarTower_normalizationAtContraction_genericFiber (p' : Ideal (Localization.AtPrime y))
    [p'.IsPrime] :
    IsScalarTower (Localization.AtPrime y) (LocalizedNormalization B y)
        (NormalizationAtContraction B y p') :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    apply Subtype.ext
    rw [RingHom.algebraMap_toAlgebra, localizedNormalizationToNormalizationAtContraction_val]
    exact IsScalarTower.algebraMap_apply (Localization.AtPrime y) (LocalizedCover B y)
        (GenericFiberAtContraction B y p') r

/-- If `K_𝔭 ⊗_R B` is the localization of `B_y` at `𝔭'`, then `C_𝔭` is the localization of
`N_y` at `𝔭'` (integral closure commutes with localization). -/
theorem isLocalization_normalizationAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    [IsLocalization (algebraMapSubmonoid (LocalizedCover B y) p'.primeCompl)
        (GenericFiberAtContraction B y p')] :
    IsLocalization (algebraMapSubmonoid (LocalizedNormalization B y) p'.primeCompl)
        (NormalizationAtContraction B y p') := by
  haveI := isScalarTower_localizationAtContraction y p'
  haveI := isLocalization_localizationAtContraction y p'
  exact IsLocalization.integralClosure (R := Localization.AtPrime y) (S := LocalizedCover B y)
    (Rf := Localization.AtPrime (contraction y p')) (Sf := GenericFiberAtContraction B y p')
        p'.primeCompl

/-- For `𝔭'` minimal over `(a_y)` in `R_y` (`a` a nonzerodivisor), `R_𝔭` has dimension one
(Krull's principal ideal theorem). -/
theorem ringKrullDim_localizationAtContraction [IsNoetherianRing R] (ha : a ∈ nonZeroDivisors R)
    (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    (hq : p' ∈ (Ideal.span {localizedEquation a y}).minimalPrimes) :
    ringKrullDim (Localization.AtPrime (contraction y p')) = 1 := by
  haveI := isScalarTower_localizationAtContraction y p'
  haveI := isLocalization_localizationAtContraction y p'
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p' (Localization.AtPrime (contraction y p'))]
  have hle : p'.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p' hq
  have hnzd : localizedEquation a y ∈ nonZeroDivisors (Localization.AtPrime y) :=
    IsLocalization.map_nonZeroDivisors_le y.primeCompl _ ⟨a, ha, rfl⟩
  have hge : 1 ≤ p'.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hnzd).trans
      (Ideal.height_mono hq.1.2)
  rw [le_antisymm hle hge]
  rfl

/-- A prime `q` of `N_y` over `𝔭'` extends to a maximal ideal of `C_𝔭`. -/
theorem isMaximal_map_normalizationAtContraction (p' : Ideal (Localization.AtPrime y)) [p'.IsPrime]
    [IsLocalization (algebraMapSubmonoid (LocalizedCover B y) p'.primeCompl)
        (GenericFiberAtContraction B y p')]
    (q : Ideal (LocalizedNormalization B y)) [q.IsPrime]
        (hq : q.under (Localization.AtPrime y) = p') :
    haveI := isLocalization_normalizationAtContraction B y p'
    haveI := isPrime_map_localizationAtPrime p' (NormalizationAtContraction B y p') q hq
    (q.map (algebraMap (LocalizedNormalization B y)
        (NormalizationAtContraction B y p'))).IsMaximal := by
  haveI := isScalarTower_localizationAtContraction y p'
  haveI := isLocalization_localizationAtContraction y p'
  haveI := isLocalization_normalizationAtContraction B y p'
  haveI := isPrime_map_localizationAtPrime p' (NormalizationAtContraction B y p') q hq
  set Rp := Localization.AtPrime (contraction y p')
  set m := q.map (algebraMap (LocalizedNormalization B y) (NormalizationAtContraction B y p'))
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (S := NormalizationAtContraction B y p')
    (algebraMap Rp (NormalizationAtContraction B y p')) (fun x ↦ ?_) m ?_
  · exact integralClosure.isIntegral x
  set J := m.comap (algebraMap Rp (NormalizationAtContraction B y p'))
  have hJ : J.under (Localization.AtPrime y) = p' := by
    change (m.comap (algebraMap Rp (NormalizationAtContraction B y p'))).comap
        (algebraMap (Localization.AtPrime y) Rp) = p'
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq (Localization.AtPrime y) (LocalizedNormalization B y)
          (NormalizationAtContraction B y p'),
      ← Ideal.comap_comap, comap_map_localizationAtPrime p' (NormalizationAtContraction B y p') q
          hq]
    exact hq
  have : J = IsLocalRing.maximalIdeal Rp := by
    rw [← IsLocalization.map_under p'.primeCompl Rp J, hJ,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
  rw [this]
  infer_instance

include Ra in
/-- **Tameness transfers to the chart at `y`.**  If `Spec B → Spec R_a` is tame in codimension one
along `V(a)` (`IsTamelyRamifiedAlongDivisor`), then the normalization `N_y` of `R_y` in `R_y ⊗_R B`
is tamely ramified in codimension one along `V(a_y)` in the sense of
`IsTamelyRamifiedInCodimensionOneAlong`. -/
theorem isTamelyRamifiedInCodimensionOneAlong_localizedNormalization [IsNoetherianRing R]
    (ha : a ∈ nonZeroDivisors R) [IsRegularRing (R ⧸ Ideal.span {a})]
    (htame : IsTamelyRamifiedAlongDivisor a B) :
    IsTamelyRamifiedInCodimensionOneAlong (Localization.AtPrime y) (LocalizedNormalization B y)
        (localizedEquation a y) := by
  intro q hq _
  set p' : Ideal (Localization.AtPrime y) := q.asIdeal.under (Localization.AtPrime y)
  have hap : a ∈ contraction y p' := hq.1.2 (Ideal.subset_span rfl)
  haveI : IsRegularLocalRing (Localization.AtPrime (contraction y p')) :=
    Pcf.Stacks.isRegularLocalRing_atPrime_of_regular_principal_quotient a ha (contraction y p') hap
  haveI : IsDomain (Localization.AtPrime (contraction y p')) :=
    Pcf.Stacks.isDomain_of_isRegularLocalRing _
  have hdim := ringKrullDim_localizationAtContraction a y ha p' hq
  haveI : IsDiscreteValuationRing (Localization.AtPrime (contraction y p')) :=
    Pcf.Stacks.isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one _ hdim
  have ht := htame (contraction y p') inferInstance hap hdim
  haveI := isLocalization_genericFiberAtContraction a Ra B y ha p' hap
  haveI := isScalarTower_localizationAtContraction y p'
  haveI := isLocalization_localizationAtContraction y p'
  haveI := isLocalization_normalizationAtContraction B y p'
  have hqp : q.asIdeal.under (Localization.AtPrime y) = p' := rfl
  exact isTamelyRamifiedAt_of_isLocalization p' (Localization.AtPrime (contraction y p'))
      (NormalizationAtContraction B y p') q hqp
    (ht _ (isMaximal_map_normalizationAtContraction B y p' q.asIdeal hqp))

end Transfer

section Apply

variable {R : Type u} [CommRing R] (a : R) (Ra : Type u) [CommRing Ra] [Algebra R Ra]
  [IsLocalization.Away a Ra]
  (B : Type u) [CommRing B] [Algebra Ra B] [Algebra R B] [IsScalarTower R Ra B]
  (y : Ideal R) [y.IsPrime]

include Ra in
/-- **The affine hypothesis applied at `R_y`.** -/
theorem hasAbhyankarStandardCoverAt_localizedNormalization [IsNoetherianRing R]
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span {a})] [Module.Finite Ra B] [Algebra.Etale Ra B]
    (htame : IsTamelyRamifiedAlongDivisor a B) (hy : a ∈ y)
    (hA : ∀ (S : Type u) [CommRing S] [Algebra (Localization.AtPrime y) S]
      (b : Localization.AtPrime y), AbhyankarLemmaTameOfFinite (Localization.AtPrime y) S b) :
    HasAbhyankarStandardCoverAt (Localization.AtPrime y) (LocalizedNormalization B y)
        (localizedEquation a y)
      ⟨maximalIdeal (Localization.AtPrime y), inferInstance⟩ := by
  haveI : IsRegularLocalRing (Localization.AtPrime y) :=
    Pcf.Stacks.isRegularLocalRing_atPrime_of_regular_principal_quotient a ha y hy
  haveI : IsDomain (Localization.AtPrime y) := Pcf.Stacks.isDomain_of_isRegularLocalRing _
  haveI : IsIntegrallyClosed (Localization.AtPrime y) :=
    Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _
  have hnzd : localizedEquation a y ∈ nonZeroDivisors (Localization.AtPrime y) :=
    IsLocalization.map_nonZeroDivisors_le y.primeCompl _ ⟨a, ha, rfl⟩
  have hreg : IsRegularRing (Localization.AtPrime y ⧸ Ideal.span {localizedEquation a y}) := by
    have hle : Ideal.span ({a} : Set R) ≤ y := (Ideal.span_singleton_le_iff_mem y).mpr hy
    haveI := Pcf.Stacks.isRegularLocalRing_quotient_localization (Ideal.span {a}) y hle
    have hJ : (Ideal.span ({a} : Set R)).map (algebraMap R (Localization.AtPrime y)) =
        Ideal.span {localizedEquation a y} := by
      rw [Ideal.map_span, Set.image_singleton]
    haveI : IsRegularLocalRing (Localization.AtPrime y ⧸ Ideal.span {localizedEquation a y}) :=
      IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquivAlgOfEq ℤ hJ).toRingEquiv
    exact Pcf.Stacks.isRegularRing_of_isRegularLocalRing _
  have hmem : localizedEquation a y ∈ maximalIdeal (Localization.AtPrime y) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ y a).mpr hy
  exact hA (LocalizedNormalization B y) (localizedEquation a y) inferInstance hnzd hreg
    (finite_localizedNormalization a Ra B y (nonZeroDivisors.ne_zero hnzd))
    (isEtaleAt_localizedNormalization a Ra B y) (isIntegralClosure_localizedNormalization a Ra B y)
    (isTamelyRamifiedInCodimensionOneAlong_localizedNormalization a Ra B y ha htame) _ hmem

end Apply

end Pcf.Stacks.SchemeLevel.AffineTame
